module

public import PakPrimes.QuasipolynomialEulerParity
public import PakPrimes.QuasipolynomialIFF
public import PakPrimes.HigherOrderStokes
public import PakPrimes.HigherOrderStrongDTrans
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! # Compact Rank-1 Symmetric Space (CROSS) Odd-Sphere Uniqueness & ADE Spherical 3-Manifold Parity

This module formalizes Module 2 of Theory 2 (the Geometry–Compression Trichotomy):

## Part A — Complete Cartan CROSS Bosonic Euler-Product Parity Classification
- Exact Weyl multiplicity polynomials and `Quasipoly` instances for every compact rank-1
  symmetric space (CROSS) of real dimension `d ≥ 2`:
  - `cpnQP n hn` (`ℂℙⁿ`, real dim `2n`, `M = 2`, supported on `s % 2 = n % 2`),
  - `hpnQP n hn` (`ℍℙⁿ`, real dim `4n`, `M = 2`, supported on odd `s`),
  - `op2QP` (`𝕆ℙ² = F₄ / Spin(9)`, real dim `16`, `M = 2`, supported on odd `s`,
    with exact dimensions `m(11) = 1, m(13) = 26, m(15) = 324, m(17) = 2652` and exact
    sub-ground vanishing `m(1) = m(3) = m(5) = m(7) = m(9) = 0`),
  - `rpsQP s hs` (`ℝℙˢ = Sˢ / {±1}`, real dim `s`, `M = 4`, supported on `m % 4 = (s - 1) % 4`).
- Exact isomorphism cross-checks (`ℂℙ¹ ≅ S²`, `ℍℙ¹ ≅ S⁴`), sub-ground root vanishing, and
  parity theorems (`cpnQP_oddPart_ne_zero`, `hpnQP_oddPart_ne_zero`, `op2QP_oddPart_ne_zero`,
  `rpsQP_oddPart_eq_zero_iff`).
- Master unconditional bosonic Euler-product classification theorems over `ℂ(q)`:
  - `cpn_eulerProduct_dTrans`, `hpn_eulerProduct_dTrans`, `op2_eulerProduct_dTrans`,
    `rps_eulerProduct_dAlg_iff`,
  - **Headline Cartan Uniqueness Theorem (`cross_simplyConnected_dAlg_iff`)**: among all simply
    connected CROSS (`Sˢ, ℂℙⁿ, ℍℙⁿ, 𝕆ℙ²`), the conformal bosonic Euler product is D-algebraic
    over `ℂ(q)` if and only if the space is an **odd sphere** `S^{2r+1}`!

## Part B — Exact Leading Borel Pole Combinatorics & Strong `ℂ({t})` Wave-EGF D-Transcendence
- Exact integer leading Borel pole coefficients:
  - `cpn_leading_pole_coeff`: `Nat.choose (2 * n) n` (central binomials),
  - `hpn_leading_pole_coeff`: `Nat.choose (4 * n) (2 * n) / (2 * n + 1) = catalan (2 * n)`
    (even Catalan numbers),
  - `op2_leading_pole_coeff`: `78`,
  - `evenSphere_leading_pole_coeff`: `2`.
- Unified `HigherOrderBorelData` engine along `θ₀ = π / 2` for regularized wave EGFs
  built from `psi0Reg y = (exp y - 1)⁻¹ - y⁻¹` and `psiHalfReg y = (2 sinh (y/2))⁻¹ - y⁻¹`,
  yielding unconditional **strong differential transcendence over convergent meromorphic germs
  `ℂ({t})`** (`StronglyDTransOverMeromorphicGerms`) for `ogfOfEGF` of every even-dimensional
  simply connected CROSS (`ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`, `S^{2r}`).

## Part C — Poincaré Homology Sphere `S³ / I*` & ADE Spherical 3-Manifold Even-Parity Theorem
- General palindromic Gorenstein Molien quasipolynomial engine (`adeSphere3QP`), proving
  exact `PowerSeries` Molien identities and strict even parity (`eval (-m) = eval m`,
  `oddPart m = 0`, `cOdd = 0`, `borelAmp = 0`) universally for all ADE binary polyhedral
  quotients `S³ / Γ`:
  - **Poincaré homology sphere** `S³ / I*` (`poincareSphereQP`, period `M = 60`,
    `(1 - X¹²)(1 - X²⁰) M_{I*}(X) = 1 + X³⁰`, exact values verified on `0..60`),
  - **Octahedral spherical 3-manifold** `S³ / O*` (`octahedralSphereQP`, period `M = 24`,
    `(1 - X⁸)(1 - X¹²) M_{O*}(X) = 1 + X¹⁸`),
  - **Tetrahedral spherical 3-manifold** `S³ / T*` (`tetrahedralSphereQP`, period `M = 12`,
    `(1 - X⁶)(1 - X⁸) M_{T*}(X) = 1 + X¹²`),
  - **Binary dihedral prism manifolds** `S³ / D_m*` (`binaryDihedralSphereQP`, period `M = 4m`,
    `(1 - X⁴)(1 - X^{2m}) M_{D_m*}(X) = 1 + X^{2m + 2}`).
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.RankOneSymmetricParity

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.HigherOrderStokes
open PakPrimes.FishburnStrongDTrans
open PakPrimes.PakYeliussizovEGF
open PakPrimes.HigherOrderStrongDTrans
open PakPrimes.HolderGamma
open PakPrimes.PrimeNome
open PakPrimes.DivisorAndMacMahon
open PakPrimes.QuasipolynomialEulerParity
open PakPrimes.QuasipolynomialIFF
open scoped Topology Interval BigOperators

noncomputable section

/-! ### Part A: Complete Cartan CROSS Bosonic Euler-Product Parity Classification -/

/-! #### A.1 Helper Product Identities -/

private lemma prod_Icc_natCast (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, (k : ℂ) = (Nat.factorial n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul]

private lemma eval_finset_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (z : ℂ) :
    (∏ i ∈ s, f i).eval z = ∏ i ∈ s, (f i).eval z := by
  change Polynomial.evalRingHom z (∏ i ∈ s, f i) = ∏ i ∈ s, Polynomial.evalRingHom z (f i)
  exact map_prod (Polynomial.evalRingHom z) f s

private lemma monic_X_sq_sub_C (a : ℂ) :
    (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℂ).Monic := by
  have h1 : (Polynomial.X ^ 2 : Polynomial ℂ).Monic := Polynomial.monic_X_pow 2
  have hdeg : (Polynomial.C a : Polynomial ℂ).degree < (Polynomial.X ^ 2 : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_cast)
  simpa [sub_eq_add_neg] using h1.add_of_left (by simpa [Polynomial.degree_neg] using hdeg)

private lemma natDegree_X_sq_sub_C (a : ℂ) :
    (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℂ).natDegree = 2 := by
  have hlt : (Polynomial.C a : Polynomial ℂ).natDegree < (Polynomial.X ^ 2 : Polynomial ℂ).natDegree := by
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]; norm_num
  rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt
    (by rwa [Polynomial.natDegree_neg]), Polynomial.natDegree_X_pow]

private lemma poly_finset_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff ℂ m) f s

private lemma coeff_comp_C_mul_X' (P : Polynomial ℂ) (a : ℂ) (k : ℕ) :
    (P.comp (Polynomial.C a * Polynomial.X)).coeff k = a ^ k * P.coeff k := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, mul_add]
  | monomial i c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hik
    · subst hik; ring
    · simp

/-! #### A.2 Complex Projective Spaces `ℂℙⁿ` (`n ≥ 1`, real dimension `2n`) -/

/-- Exact Weyl multiplicity polynomial of `ℂℙⁿ` (`n ≥ 1`) in the doubled spectral variable
`j = 2 u_k = 2 k + n`:
`P_{ℂℙⁿ}(j) = (2^(2(n-1)) · n · ((n-1)!)²)⁻¹ · j · ∏_{r=1}^{n-1} (j + 2r - n)²`. -/
@[expose] def cpnPoly (n : ℕ) : Polynomial ℂ :=
  Polynomial.C (((2 : ℂ) ^ (2 * (n - 1)) * (n : ℂ) * ((Nat.factorial (n - 1) : ℂ) ^ 2))⁻¹) *
    (Polynomial.X * ∏ r ∈ Finset.Icc 1 (n - 1),
      (Polynomial.X + Polynomial.C (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2)

private lemma cpnPoly_monicPart (n : ℕ) :
    (Polynomial.X * ∏ r ∈ Finset.Icc 1 (n - 1),
      (Polynomial.X + Polynomial.C (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2).Monic := by
  refine Polynomial.monic_X.mul (Polynomial.monic_prod_of_monic _ _ fun r _ => ?_)
  exact (Polynomial.monic_X_add_C _).pow 2

private lemma cpnPoly_monicPart_natDegree {n : ℕ} (hn : 1 ≤ n) :
    (Polynomial.X * ∏ r ∈ Finset.Icc 1 (n - 1),
      (Polynomial.X + Polynomial.C (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2).natDegree =
      2 * n - 1 := by
  have hprod_monic : (∏ r ∈ Finset.Icc 1 (n - 1),
      (Polynomial.X + Polynomial.C (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun r _ => (Polynomial.monic_X_add_C _).pow 2
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hprod_monic.ne_zero, Polynomial.natDegree_X,
    Polynomial.natDegree_prod_of_monic _ _ (fun r _ => (Polynomial.monic_X_add_C _).pow 2)]
  have hdeg : ∀ r ∈ Finset.Icc 1 (n - 1),
      ((Polynomial.X + Polynomial.C (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2).natDegree = 2 := by
    intro r _
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, show (Finset.Icc 1 (n - 1)).card = n - 1 by simp,
    smul_eq_mul]
  omega

lemma natDegree_cpnPoly_le {n : ℕ} (hn : 1 ≤ n) : (cpnPoly n).natDegree ≤ 2 * n - 1 := by
  unfold cpnPoly
  exact (Polynomial.natDegree_C_mul_le _ _).trans (cpnPoly_monicPart_natDegree hn).le

lemma cpnPoly_coeff_top {n : ℕ} (hn : 1 ≤ n) :
    (cpnPoly n).coeff (2 * n - 1) =
      ((2 : ℂ) ^ (2 * (n - 1)) * (n : ℂ) * ((Nat.factorial (n - 1) : ℂ) ^ 2))⁻¹ := by
  unfold cpnPoly
  rw [Polynomial.coeff_C_mul, ← cpnPoly_monicPart_natDegree hn,
    ← Polynomial.leadingCoeff, (cpnPoly_monicPart n).leadingCoeff, mul_one]

lemma cpnPoly_eval_neg (n : ℕ) (z : ℂ) :
    (cpnPoly n).eval (-z) = -(cpnPoly n).eval z := by
  unfold cpnPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_finset_prod]
  have hprod : (∏ r ∈ Finset.Icc 1 (n - 1),
      ((-z + (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2)) =
      ∏ r ∈ Finset.Icc 1 (n - 1), ((z + (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2) := by
    refine Finset.prod_bij (fun r _ => n - r) ?_ ?_ ?_ ?_
    · intro r hr; have := Finset.mem_Icc.mp hr; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb hab
      have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega
    · intro b hb; have := Finset.mem_Icc.mp hb
      exact ⟨n - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro r hr
      have := Finset.mem_Icc.mp hr
      have hcast : ((n - r : ℕ) : ℤ) = (n : ℤ) - (r : ℤ) := by omega
      have hint : 2 * ((n - r : ℕ) : ℤ) - (n : ℤ) = -(2 * (r : ℤ) - (n : ℤ)) := by
        rw [hcast]; ring
      rw [hint, Int.cast_neg]
      ring
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [hprod]
  ring

lemma cpnPoly_eval_ground {n : ℕ} (hn : 1 ≤ n) :
    (cpnPoly n).eval (n : ℂ) = 1 := by
  unfold cpnPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_finset_prod,
    Polynomial.eval_pow, Polynomial.eval_add]
  have hprod : (∏ r ∈ Finset.Icc 1 (n - 1),
      ((n : ℂ) + (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2) =
      (2 : ℂ) ^ (2 * (n - 1)) * (Nat.factorial (n - 1) : ℂ) ^ 2 := by
    have hterm : ∀ r ∈ Finset.Icc 1 (n - 1),
        ((n : ℂ) + (((2 * (r : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2 = (2 : ℂ) ^ 2 * (r : ℂ) ^ 2 := by
      intro r _; push_cast; ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
      show (Finset.Icc 1 (n - 1)).card = n - 1 by simp, ← pow_mul, Finset.prod_pow,
      prod_Icc_natCast]
  rw [hprod]
  have hne : (2 : ℂ) ^ (2 * (n - 1)) * (n : ℂ) * ((Nat.factorial (n - 1) : ℂ) ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) ?_
    · exact Nat.cast_ne_zero.mpr (by omega)
    · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hcomm : (n : ℂ) * ((2 : ℂ) ^ (2 * (n - 1)) * (Nat.factorial (n - 1) : ℂ) ^ 2) =
      (2 : ℂ) ^ (2 * (n - 1)) * (n : ℂ) * (Nat.factorial (n - 1) : ℂ) ^ 2 := by ring
  rw [hcomm, inv_mul_cancel₀ hne]

/-- Exact sub-ground root vanishing for `ℂℙⁿ`: for every lattice point `0 ≤ s < n` with
`s ≡ n (mod 2)`, `P_{ℂℙⁿ}(s) = 0`. -/
lemma cpnPoly_subground_eq_zero {n s : ℕ} (hs_lt : s < n) (hpar : s % 2 = n % 2) :
    (cpnPoly n).eval (s : ℂ) = 0 := by
  unfold cpnPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_finset_prod,
    Polynomial.eval_pow, Polynomial.eval_add]
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  · have hmem : (n - s) / 2 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfac : ((s : ℂ) + (((2 * (((n - s) / 2 : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℂ))) ^ 2 = 0 := by
      have hint : (s : ℤ) + (2 * (((n - s) / 2 : ℕ) : ℤ) - (n : ℤ)) = 0 := by omega
      have hC : (s : ℂ) + (((2 * (((n - s) / 2 : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℂ)) = 0 := by
        exact_mod_cast hint
      rw [hC, zero_pow two_ne_zero]
    rw [Finset.prod_eq_zero hmem hfac, mul_zero, mul_zero]

/-- Isomorphism cross-check `ℂℙ¹ ≅ S²`: exact polynomial equality `cpnPoly 1 = conformalScalarPoly 2`. -/
lemma cpnPoly_one_eq_sphereTwo : cpnPoly 1 = conformalScalarPoly 2 := by
  unfold cpnPoly conformalScalarPoly
  simp

/-- Period-2 quasipolynomial encoding the exact spherical harmonic multiplicities of `ℂℙⁿ` (`n ≥ 1`),
supported on `s % 2 = n % 2` with `eval (2k + n) = m_{ℂℙⁿ}(k + n/2)`. -/
@[expose] def cpnQP (n : ℕ) (_hn : 1 ≤ n) : Quasipoly where
  M := 2
  hM := by norm_num
  «D» := 2 * n - 1
  c d s := if s % 2 = n % 2 then (cpnPoly n).coeff d.1 else 0
  periodic _ _ := by simp

lemma cpnQP_eval {n : ℕ} (hn : 1 ≤ n) (s : ℤ) :
    (cpnQP n hn).eval s =
      if (s % 2).toNat = n % 2 then (cpnPoly n).eval (s : ℂ) else 0 := by
  unfold Quasipoly.eval cpnQP
  simp only [Nat.cast_ofNat]
  have hmod2 : (s % 2).toNat % 2 = (s % 2).toNat := Nat.mod_eq_of_lt (by omega)
  simp_rw [hmod2]
  split_ifs with h
  · rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_cpnPoly_le hn) (Nat.lt_succ_self _)),
      Fin.sum_univ_eq_sum_range (fun d => (cpnPoly n).coeff d * (s : ℂ) ^ d)]
  · exact Finset.sum_eq_zero fun d _ => by simp

lemma cpnQP_eval_neg {n : ℕ} (hn : 1 ≤ n) (s : ℤ) :
    (cpnQP n hn).eval (-s) = -(cpnQP n hn).eval s := by
  rw [cpnQP_eval hn (-s), cpnQP_eval hn s]
  have hmod : ((-s) % 2).toNat = (s % 2).toNat := by omega
  rw [hmod]
  split_ifs
  · rw [Int.cast_neg, cpnPoly_eval_neg]
  · simp

lemma cpnQP_eval_ground {n : ℕ} (hn : 1 ≤ n) :
    (cpnQP n hn).eval (n : ℤ) = 1 := by
  rw [cpnQP_eval hn (n : ℤ)]
  have hmod : ((n : ℤ) % 2).toNat = n % 2 := by omega
  rw [ite_eq_left_iff.mpr (fun h => (h hmod).elim), Int.cast_natCast]
  exact cpnPoly_eval_ground hn

lemma cpnQP_oddPart_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : ℤ, (cpnQP n hn).oddPart s ≠ 0 := by
  refine ⟨(n : ℤ), ?_⟩
  unfold Quasipoly.oddPart
  rw [cpnQP_eval_neg hn, cpnQP_eval_ground hn]
  norm_num

/-! #### A.3 Quaternionic Projective Spaces `ℍℙⁿ` (`n ≥ 1`, real dimension `4n`) -/

/-- Exact Weyl multiplicity polynomial of `ℍℙⁿ` (`n ≥ 1`) in the doubled spectral variable
`j = 2 u_k = 2 k + (2n + 1)`:
`P_{ℍℙⁿ}(j) = (2^(4n-2) (2n+1)(2n)((2n-1)!)²)⁻¹ · j · (j² - (2n-1)²) · ∏_{m=1}^{n-1} (j² - (2m-1)²)²`. -/
@[expose] def hpnPoly (n : ℕ) : Polynomial ℂ :=
  Polynomial.C (((2 : ℂ) ^ (4 * n - 2) * ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) *
      ((Nat.factorial (2 * n - 1) : ℂ) ^ 2))⁻¹) *
    (Polynomial.X * (Polynomial.X ^ 2 - Polynomial.C ((((2 * n - 1 : ℕ) : ℂ)) ^ 2)) *
      ∏ m ∈ Finset.Icc 1 (n - 1),
        (Polynomial.X ^ 2 - Polynomial.C ((((2 * m - 1 : ℕ) : ℂ)) ^ 2)) ^ 2)

private lemma hpnPoly_monicPart (n : ℕ) :
    (Polynomial.X * (Polynomial.X ^ 2 - Polynomial.C ((((2 * n - 1 : ℕ) : ℂ)) ^ 2)) *
      ∏ m ∈ Finset.Icc 1 (n - 1),
        (Polynomial.X ^ 2 - Polynomial.C ((((2 * m - 1 : ℕ) : ℂ)) ^ 2)) ^ 2).Monic := by
  refine (Polynomial.monic_X.mul (monic_X_sq_sub_C _)).mul ?_
  exact Polynomial.monic_prod_of_monic _ _ fun m _ => (monic_X_sq_sub_C _).pow 2

private lemma hpnPoly_monicPart_natDegree {n : ℕ} (hn : 1 ≤ n) :
    (Polynomial.X * (Polynomial.X ^ 2 - Polynomial.C ((((2 * n - 1 : ℕ) : ℂ)) ^ 2)) *
      ∏ m ∈ Finset.Icc 1 (n - 1),
        (Polynomial.X ^ 2 - Polynomial.C ((((2 * m - 1 : ℕ) : ℂ)) ^ 2)) ^ 2).natDegree =
      4 * n - 1 := by
  have hm1 : (Polynomial.X * (Polynomial.X ^ 2 - Polynomial.C ((((2 * n - 1 : ℕ) : ℂ)) ^ 2))).Monic :=
    Polynomial.monic_X.mul (monic_X_sq_sub_C _)
  have hm2 : (∏ m ∈ Finset.Icc 1 (n - 1),
      (Polynomial.X ^ 2 - Polynomial.C ((((2 * m - 1 : ℕ) : ℂ)) ^ 2)) ^ 2).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun m _ => (monic_X_sq_sub_C _).pow 2
  rw [Polynomial.natDegree_mul hm1.ne_zero hm2.ne_zero,
    Polynomial.natDegree_mul Polynomial.X_ne_zero (monic_X_sq_sub_C _).ne_zero,
    Polynomial.natDegree_X, natDegree_X_sq_sub_C,
    Polynomial.natDegree_prod_of_monic _ _ (fun m _ => (monic_X_sq_sub_C _).pow 2)]
  have hdeg : ∀ m ∈ Finset.Icc 1 (n - 1),
      ((Polynomial.X ^ 2 - Polynomial.C ((((2 * m - 1 : ℕ) : ℂ)) ^ 2)) ^ 2).natDegree = 4 := by
    intro m _
    rw [Polynomial.natDegree_pow, natDegree_X_sq_sub_C]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, show (Finset.Icc 1 (n - 1)).card = n - 1 by simp,
    smul_eq_mul]
  omega

lemma natDegree_hpnPoly_le {n : ℕ} (hn : 1 ≤ n) : (hpnPoly n).natDegree ≤ 4 * n - 1 := by
  unfold hpnPoly
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hpnPoly_monicPart_natDegree hn).le

lemma hpnPoly_coeff_top {n : ℕ} (hn : 1 ≤ n) :
    (hpnPoly n).coeff (4 * n - 1) =
      ((2 : ℂ) ^ (4 * n - 2) * ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) *
        ((Nat.factorial (2 * n - 1) : ℂ) ^ 2))⁻¹ := by
  unfold hpnPoly
  rw [Polynomial.coeff_C_mul, ← hpnPoly_monicPart_natDegree hn,
    ← Polynomial.leadingCoeff, (hpnPoly_monicPart n).leadingCoeff, mul_one]

lemma hpnPoly_eval_neg (n : ℕ) (z : ℂ) :
    (hpnPoly n).eval (-z) = -(hpnPoly n).eval z := by
  unfold hpnPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_pow, eval_finset_prod, neg_sq]
  ring

private lemma hpn_ground_prod {n : ℕ} (hn : 1 ≤ n) :
    (∏ m ∈ Finset.Icc 1 (n - 1),
      (((2 * n + 1 : ℕ) : ℂ) ^ 2 - (((2 * m - 1 : ℕ) : ℂ)) ^ 2) ^ 2) =
      (2 : ℂ) ^ (4 * (n - 1)) * (Nat.factorial (2 * n - 1) : ℂ) ^ 2 := by
  have hfac : ∀ m ∈ Finset.Icc 1 (n - 1),
      (((2 * n + 1 : ℕ) : ℂ) ^ 2 - (((2 * m - 1 : ℕ) : ℂ)) ^ 2) ^ 2 =
        (2 : ℂ) ^ 4 * (((n + 1 - m : ℕ) : ℂ) * ((n + m : ℕ) : ℂ)) ^ 2 := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have h1 : ((2 * m - 1 : ℕ) : ℂ) = 2 * (m : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have h2 : ((n + 1 - m : ℕ) : ℂ) = (n : ℂ) + 1 - (m : ℂ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    rw [h1, h2]; push_cast; ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    show (Finset.Icc 1 (n - 1)).card = n - 1 by simp, ← pow_mul, Finset.prod_pow,
    Finset.prod_mul_distrib]
  have hlow : ∏ m ∈ Finset.Icc 1 (n - 1), ((n + 1 - m : ℕ) : ℂ) =
      ∏ k ∈ Finset.Icc 2 n, (k : ℂ) := by
    refine Finset.prod_bij (fun m _ => n + 1 - m) ?_ ?_ ?_ ?_
    · intro m hm; have := Finset.mem_Icc.mp hm; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb hab
      have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega
    · intro k hk; have := Finset.mem_Icc.mp hk
      exact ⟨n + 1 - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro _ _; rfl
  have hhigh : ∏ m ∈ Finset.Icc 1 (n - 1), ((n + m : ℕ) : ℂ) =
      ∏ k ∈ Finset.Icc (n + 1) (2 * n - 1), (k : ℂ) := by
    refine Finset.prod_bij (fun m _ => n + m) ?_ ?_ ?_ ?_
    · intro m hm; have := Finset.mem_Icc.mp hm; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ hab; omega
    · intro k hk; have := Finset.mem_Icc.mp hk
      exact ⟨k - n, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro _ _; rfl
  have hmerge : (∏ k ∈ Finset.Icc 2 n, (k : ℂ)) * (∏ k ∈ Finset.Icc (n + 1) (2 * n - 1), (k : ℂ)) =
      (Nat.factorial (2 * n - 1) : ℂ) := by
    have hdisj : Disjoint (Finset.Icc 2 n) (Finset.Icc (n + 1) (2 * n - 1)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      have := Finset.mem_Icc.mp hk1; have := Finset.mem_Icc.mp hk2; omega
    rw [← Finset.prod_union hdisj]
    have hunion : Finset.Icc 2 n ∪ Finset.Icc (n + 1) (2 * n - 1) = Finset.Icc 2 (2 * n - 1) := by
      ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    rw [hunion]
    have hIcc1 : Finset.Icc 1 (2 * n - 1) = insert 1 (Finset.Icc 2 (2 * n - 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hprod1 := prod_Icc_natCast (2 * n - 1)
    rw [hIcc1, Finset.prod_insert (by simp)] at hprod1
    simpa using hprod1
  rw [hlow, hhigh, hmerge]

lemma hpnPoly_eval_ground {n : ℕ} (hn : 1 ≤ n) :
    (hpnPoly n).eval ((2 * n + 1 : ℕ) : ℂ) = 1 := by
  unfold hpnPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_pow, eval_finset_prod]
  rw [hpn_ground_prod hn]
  have hmid : (((2 * n + 1 : ℕ) : ℂ) ^ 2 - (((2 * n - 1 : ℕ) : ℂ)) ^ 2) =
      (2 : ℂ) ^ 2 * ((2 * n : ℕ) : ℂ) := by
    have hsub : ((2 * n - 1 : ℕ) : ℂ) = 2 * (n : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    rw [hsub]; push_cast; ring
  rw [hmid]
  have hpow : (2 : ℂ) ^ 2 * (2 : ℂ) ^ (4 * (n - 1)) = (2 : ℂ) ^ (4 * n - 2) := by
    rw [← pow_add]; congr 1; omega
  have hnum : ((2 * n + 1 : ℕ) : ℂ) * ((2 : ℂ) ^ 2 * ((2 * n : ℕ) : ℂ)) *
      ((2 : ℂ) ^ (4 * (n - 1)) * (Nat.factorial (2 * n - 1) : ℂ) ^ 2) =
      (2 : ℂ) ^ (4 * n - 2) * ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) *
        (Nat.factorial (2 * n - 1) : ℂ) ^ 2 := by
    rw [← hpow]; ring
  rw [hnum]
  have hne : (2 : ℂ) ^ (4 * n - 2) * ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) *
      (Nat.factorial (2 * n - 1) : ℂ) ^ 2 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) ?_) ?_
    · exact Nat.cast_ne_zero.mpr (by omega)
    · exact Nat.cast_ne_zero.mpr (by omega)
    · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  exact inv_mul_cancel₀ hne

/-- Exact sub-ground root vanishing for `ℍℙⁿ`: for every odd lattice point `0 < s < 2n + 1`,
`P_{ℍℙⁿ}(s) = 0`. -/
lemma hpnPoly_subground_eq_zero {n s : ℕ} (hs_lt : s < 2 * n + 1) (hodd : s % 2 = 1) :
    (hpnPoly n).eval (s : ℂ) = 0 := by
  unfold hpnPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_pow, eval_finset_prod]
  by_cases htop : s = 2 * n - 1
  · subst htop; simp
  · have hmem : (s + 1) / 2 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfac : ((s : ℂ) ^ 2 - (((2 * ((s + 1) / 2) - 1 : ℕ) : ℂ)) ^ 2) ^ 2 = 0 := by
      have heq : 2 * ((s + 1) / 2) - 1 = s := by omega
      rw [heq, sub_self, zero_pow two_ne_zero]
    rw [Finset.prod_eq_zero hmem hfac, mul_zero, mul_zero]

/-- Isomorphism cross-check `ℍℙ¹ ≅ S⁴`: exact polynomial equality `hpnPoly 1 = conformalScalarPoly 4`. -/
lemma hpnPoly_one_eq_sphereFour : hpnPoly 1 = conformalScalarPoly 4 := by
  apply Polynomial.funext
  intro z
  unfold hpnPoly conformalScalarPoly
  have hIcc : Finset.Icc 1 (4 - 2) = {1, 2} := by decide
  rw [hIcc]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_pow, Finset.prod_pair (by decide : (1 : ℕ) ≠ 2),
    Polynomial.eval_add, Nat.sub_self, Finset.Icc_eq_empty (by decide : ¬ 1 ≤ 0),
    Finset.prod_empty, mul_one,
    show 4 * 1 - 2 = 2 by rfl, show 2 * 1 + 1 = 3 by rfl, show 2 * 1 - 1 = 1 by rfl,
    show 2 * 1 = 2 by rfl, show 4 - 1 = 3 by rfl, Nat.factorial]
  push_cast
  ring

/-- Period-2 quasipolynomial encoding the exact spherical harmonic multiplicities of `ℍℙⁿ` (`n ≥ 1`),
supported on odd `s` with `eval (2k + 2n + 1) = m_{ℍℙⁿ}(k + n + 1/2)`. -/
@[expose] def hpnQP (n : ℕ) (_hn : 1 ≤ n) : Quasipoly where
  M := 2
  hM := by norm_num
  «D» := 4 * n - 1
  c d s := if s % 2 = 1 then (hpnPoly n).coeff d.1 else 0
  periodic _ _ := by simp

lemma hpnQP_eval {n : ℕ} (hn : 1 ≤ n) (s : ℤ) :
    (hpnQP n hn).eval s =
      if (s % 2).toNat = 1 then (hpnPoly n).eval (s : ℂ) else 0 := by
  unfold Quasipoly.eval hpnQP
  simp only [Nat.cast_ofNat]
  have hmod2 : (s % 2).toNat % 2 = (s % 2).toNat := Nat.mod_eq_of_lt (by omega)
  simp_rw [hmod2]
  split_ifs with h
  · rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_hpnPoly_le hn) (Nat.lt_succ_self _)),
      Fin.sum_univ_eq_sum_range (fun d => (hpnPoly n).coeff d * (s : ℂ) ^ d)]
  · exact Finset.sum_eq_zero fun d _ => by simp

lemma hpnQP_eval_neg {n : ℕ} (hn : 1 ≤ n) (s : ℤ) :
    (hpnQP n hn).eval (-s) = -(hpnQP n hn).eval s := by
  rw [hpnQP_eval hn (-s), hpnQP_eval hn s]
  have hmod : ((-s) % 2).toNat = (s % 2).toNat := by omega
  rw [hmod]
  split_ifs
  · rw [Int.cast_neg, hpnPoly_eval_neg]
  · simp

lemma hpnQP_eval_ground {n : ℕ} (hn : 1 ≤ n) :
    (hpnQP n hn).eval ((2 * n + 1 : ℕ) : ℤ) = 1 := by
  rw [hpnQP_eval hn ((2 * n + 1 : ℕ) : ℤ)]
  have hmod : (((2 * n + 1 : ℕ) : ℤ) % 2).toNat = 1 := by omega
  rw [ite_eq_left_iff.mpr (fun h => (h hmod).elim), Int.cast_natCast]
  exact hpnPoly_eval_ground hn

lemma hpnQP_oddPart_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : ℤ, (hpnQP n hn).oddPart s ≠ 0 := by
  refine ⟨((2 * n + 1 : ℕ) : ℤ), ?_⟩
  unfold Quasipoly.oddPart
  rw [hpnQP_eval_neg hn, hpnQP_eval_ground hn]
  norm_num

/-! #### A.4 Cayley Projective Plane `𝕆ℙ² = F₄ / Spin(9)` (real dimension `16`) -/

/-- Exact Weyl multiplicity polynomial of the 16-dimensional Cayley projective plane
`𝕆ℙ² = F₄ / Spin(9)` in the doubled spectral variable `j = 2 u_k = 2 k + 11`:
`P_{𝕆ℙ²}(j) = (6 / (2¹⁴ · 11! · 7!)) · j · (j² - 1)² (j² - 9)² (j² - 25)(j² - 49)(j² - 81)`. -/
@[expose] def op2Poly : Polynomial ℂ :=
  Polynomial.C ((6 : ℂ) / ((2 : ℂ) ^ 14 * (Nat.factorial 11 : ℂ) * (Nat.factorial 7 : ℂ))) *
    (Polynomial.X *
      (Polynomial.X ^ 2 - Polynomial.C 1) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 9) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 25) *
      (Polynomial.X ^ 2 - Polynomial.C 49) *
      (Polynomial.X ^ 2 - Polynomial.C 81))

private lemma op2Poly_monicPart :
    ((Polynomial.X : Polynomial ℂ) *
      (Polynomial.X ^ 2 - Polynomial.C 1) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 9) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 25) *
      (Polynomial.X ^ 2 - Polynomial.C 49) *
      (Polynomial.X ^ 2 - Polynomial.C 81)).Monic :=
  (((((Polynomial.monic_X.mul ((monic_X_sq_sub_C 1).pow 2)).mul
    ((monic_X_sq_sub_C 9).pow 2)).mul (monic_X_sq_sub_C 25)).mul
    (monic_X_sq_sub_C 49)).mul (monic_X_sq_sub_C 81))

private lemma op2Poly_monicPart_natDegree :
    ((Polynomial.X : Polynomial ℂ) *
      (Polynomial.X ^ 2 - Polynomial.C 1) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 9) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 25) *
      (Polynomial.X ^ 2 - Polynomial.C 49) *
      (Polynomial.X ^ 2 - Polynomial.C 81)).natDegree = 15 := by
  have h1 : ((Polynomial.X : Polynomial ℂ) * (Polynomial.X ^ 2 - Polynomial.C 1) ^ 2).Monic :=
    Polynomial.monic_X.mul ((monic_X_sq_sub_C 1).pow 2)
  have h2 : ((Polynomial.X : Polynomial ℂ) * (Polynomial.X ^ 2 - Polynomial.C 1) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 9) ^ 2).Monic :=
    h1.mul ((monic_X_sq_sub_C 9).pow 2)
  have h3 : ((Polynomial.X : Polynomial ℂ) * (Polynomial.X ^ 2 - Polynomial.C 1) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 9) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 25)).Monic :=
    h2.mul (monic_X_sq_sub_C 25)
  have h4 : ((Polynomial.X : Polynomial ℂ) * (Polynomial.X ^ 2 - Polynomial.C 1) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 9) ^ 2 *
      (Polynomial.X ^ 2 - Polynomial.C 25) *
      (Polynomial.X ^ 2 - Polynomial.C 49)).Monic :=
    h3.mul (monic_X_sq_sub_C 49)
  rw [Polynomial.natDegree_mul h4.ne_zero (monic_X_sq_sub_C 81).ne_zero,
    Polynomial.natDegree_mul h3.ne_zero (monic_X_sq_sub_C 49).ne_zero,
    Polynomial.natDegree_mul h2.ne_zero (monic_X_sq_sub_C 25).ne_zero,
    Polynomial.natDegree_mul h1.ne_zero ((monic_X_sq_sub_C 9).pow 2).ne_zero,
    Polynomial.natDegree_mul Polynomial.X_ne_zero ((monic_X_sq_sub_C 1).pow 2).ne_zero,
    Polynomial.natDegree_X, Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    natDegree_X_sq_sub_C, natDegree_X_sq_sub_C, natDegree_X_sq_sub_C,
    natDegree_X_sq_sub_C, natDegree_X_sq_sub_C]

lemma natDegree_op2Poly_le : op2Poly.natDegree ≤ 15 := by
  unfold op2Poly
  exact (Polynomial.natDegree_C_mul_le _ _).trans op2Poly_monicPart_natDegree.le

lemma op2Poly_coeff_15 :
    op2Poly.coeff 15 =
      (6 : ℂ) / ((2 : ℂ) ^ 14 * (Nat.factorial 11 : ℂ) * (Nat.factorial 7 : ℂ)) := by
  unfold op2Poly
  rw [Polynomial.coeff_C_mul, ← op2Poly_monicPart_natDegree,
    ← Polynomial.leadingCoeff, op2Poly_monicPart.leadingCoeff, mul_one]

lemma op2Poly_eval_neg (z : ℂ) : op2Poly.eval (-z) = -op2Poly.eval z := by
  unfold op2Poly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_pow, neg_sq]
  ring

/-- Period-2 quasipolynomial encoding the exact spherical harmonic multiplicities of
`𝕆ℙ² = F₄ / Spin(9)`, supported on odd `s` with `eval (2k + 11) = m_{𝕆ℙ²}(k + 11/2)`. -/
@[expose] def op2QP : Quasipoly where
  M := 2
  hM := by norm_num
  «D» := 15
  c d s := if s % 2 = 1 then op2Poly.coeff d.1 else 0
  periodic _ _ := by simp

lemma op2QP_eval (s : ℤ) :
    op2QP.eval s = if (s % 2).toNat = 1 then op2Poly.eval (s : ℂ) else 0 := by
  unfold Quasipoly.eval op2QP
  simp only [Nat.cast_ofNat]
  have hmod2 : (s % 2).toNat % 2 = (s % 2).toNat := Nat.mod_eq_of_lt (by omega)
  simp_rw [hmod2]
  split_ifs with h
  · rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt natDegree_op2Poly_le (Nat.lt_succ_self _)),
      Fin.sum_univ_eq_sum_range (fun d => op2Poly.coeff d * (s : ℂ) ^ d)]
  · exact Finset.sum_eq_zero fun d _ => by simp

lemma op2QP_eval_neg (s : ℤ) : op2QP.eval (-s) = -op2QP.eval s := by
  rw [op2QP_eval (-s), op2QP_eval s]
  have hmod : ((-s) % 2).toNat = (s % 2).toNat := by omega
  rw [hmod]
  split_ifs
  · rw [Int.cast_neg, op2Poly_eval_neg]
  · simp

/-- Exact sub-ground root vanishing `m_{𝕆ℙ²}(1) = m(3) = m(5) = m(7) = m(9) = 0`. -/
lemma op2QP_subground_vanishing :
    op2QP.eval 1 = 0 ∧ op2QP.eval 3 = 0 ∧ op2QP.eval 5 = 0 ∧
      op2QP.eval 7 = 0 ∧ op2QP.eval 9 = 0 := by
  refine ⟨by rw [op2QP_eval]; simp [op2Poly], ?_, ?_, ?_, ?_⟩ <;>
    (rw [op2QP_eval]; simp [op2Poly]; norm_num)

/-- Exact ground and first three excited `F₄` spherical harmonic dimensions on `𝕆ℙ²`:
`m(11) = 1`, `m(13) = 26`, `m(15) = 324`, `m(17) = 2652`. -/
lemma op2QP_exact_dimensions :
    op2QP.eval 11 = 1 ∧ op2QP.eval 13 = 26 ∧ op2QP.eval 15 = 324 ∧ op2QP.eval 17 = 2652 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [op2QP_eval]; simp [op2Poly]; norm_num [Nat.factorial])

lemma op2QP_oddPart_ne_zero : ∃ s : ℤ, op2QP.oddPart s ≠ 0 := by
  refine ⟨11, ?_⟩
  unfold Quasipoly.oddPart
  rw [op2QP_eval_neg, op2QP_exact_dimensions.1]
  norm_num

/-! #### A.5 Real Projective Spaces `ℝℙˢ = Sˢ / {±1}` (`s ≥ 2`, real dimension `s`) -/

private lemma conformalScalarPoly_monicPart (s : ℕ) :
    (Polynomial.X * ∏ k ∈ Finset.Icc 1 (s - 2),
      (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))).Monic :=
  Polynomial.monic_X.mul (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_add_C _)

private lemma conformalScalarPoly_monicPart_natDegree {s : ℕ} (hs : 2 ≤ s) :
    (Polynomial.X * ∏ k ∈ Finset.Icc 1 (s - 2),
      (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))).natDegree =
      s - 1 := by
  have hm : (∏ k ∈ Finset.Icc 1 (s - 2),
      (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_add_C _
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hm.ne_zero, Polynomial.natDegree_X,
    Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  have hdeg : ∀ k ∈ Finset.Icc 1 (s - 2),
      (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))).natDegree = 1 :=
    fun _ _ => Polynomial.natDegree_X_add_C _
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, show (Finset.Icc 1 (s - 2)).card = s - 2 by simp,
    smul_eq_mul]
  omega

lemma natDegree_conformalScalarPoly_le' {s : ℕ} (hs : 2 ≤ s) :
    (conformalScalarPoly s).natDegree ≤ s - 1 := by
  unfold conformalScalarPoly
  exact (Polynomial.natDegree_C_mul_le _ _).trans (conformalScalarPoly_monicPart_natDegree hs).le

lemma conformalScalarPoly_coeff_top {s : ℕ} (hs : 2 ≤ s) :
    (conformalScalarPoly s).coeff (s - 1) =
      ((2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 1) : ℂ))⁻¹ := by
  unfold conformalScalarPoly
  rw [Polynomial.coeff_C_mul, ← conformalScalarPoly_monicPart_natDegree hs,
    ← Polynomial.leadingCoeff, (conformalScalarPoly_monicPart s).leadingCoeff, mul_one]

lemma conformalScalarPoly_eval_neg' {s : ℕ} (hs : 2 ≤ s) (z : ℂ) :
    (conformalScalarPoly s).eval (-z) = (-1 : ℂ) ^ (s - 1) * (conformalScalarPoly s).eval z := by
  unfold conformalScalarPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_finset_prod,
    Polynomial.eval_add]
  have hprod : (∏ k ∈ Finset.Icc 1 (s - 2), (-z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))) =
      (-1 : ℂ) ^ (s - 2) *
        ∏ k ∈ Finset.Icc 1 (s - 2), (z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))) := by
    have hbij : (∏ k ∈ Finset.Icc 1 (s - 2), (-z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))) =
        ∏ k ∈ Finset.Icc 1 (s - 2), (-(z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))) := by
      refine Finset.prod_bij (fun k _ => s - 1 - k) ?_ ?_ ?_ ?_
      · intro k hk; have := Finset.mem_Icc.mp hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a ha b hb hab
        have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega
      · intro b hb; have := Finset.mem_Icc.mp hb
        exact ⟨s - 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        have := Finset.mem_Icc.mp hk
        have hcast : ((s - 1 - k : ℕ) : ℤ) = (s : ℤ) - 1 - (k : ℤ) := by omega
        have hint : 2 * ((s - 1 - k : ℕ) : ℤ) - ((s : ℤ) - 1) = -(2 * (k : ℤ) - ((s : ℤ) - 1)) := by
          rw [hcast]; ring
        rw [hint, Int.cast_neg]; ring
    rw [hbij, Finset.prod_neg, show (Finset.Icc 1 (s - 2)).card = s - 2 by simp]
  rw [hprod, show s - 1 = (s - 2) + 1 by omega, pow_succ]
  ring

lemma conformalScalarPoly_eval_ground' {s : ℕ} (hs : 2 ≤ s) :
    (conformalScalarPoly s).eval ((s - 1 : ℕ) : ℂ) = 1 := by
  unfold conformalScalarPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_finset_prod,
    Polynomial.eval_add]
  have hprod : (∏ k ∈ Finset.Icc 1 (s - 2),
      (((s - 1 : ℕ) : ℂ) + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))) =
      (2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 2) : ℂ) := by
    have hterm : ∀ k ∈ Finset.Icc 1 (s - 2),
        ((s - 1 : ℕ) : ℂ) + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)) = (2 : ℂ) * (k : ℂ) := by
      intro k _
      have hsub : ((s - 1 : ℕ) : ℂ) = (s : ℂ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hsub]; push_cast; ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
      show (Finset.Icc 1 (s - 2)).card = s - 2 by simp, prod_Icc_natCast]
  rw [hprod]
  have hfact : ((s - 1 : ℕ) : ℂ) * ((2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 2) : ℂ)) =
      (2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 1) : ℂ) := by
    have hsucc : s - 1 = (s - 2) + 1 := by omega
    conv_rhs => rw [hsucc, Nat.factorial_succ, Nat.cast_mul]
    rw [← hsucc]; ring
  rw [hfact]
  exact inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))

/-- Exact sub-ground root vanishing for `Sˢ` and `ℝℙˢ`: for every `0 ≤ m < s - 1` with
`m ≡ s - 1 (mod 2)`, `conformalScalarPoly s` vanishes at `m`. -/
lemma conformalScalarPoly_subground_eq_zero {s m : ℕ} (hs : 2 ≤ s)
    (hm_lt : m < s - 1) (hpar : m % 2 = (s - 1) % 2) :
    (conformalScalarPoly s).eval (m : ℂ) = 0 := by
  unfold conformalScalarPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_finset_prod,
    Polynomial.eval_add]
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  · have hmem : (s - 1 - m) / 2 ∈ Finset.Icc 1 (s - 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfac : (m : ℂ) + (((2 * (((s - 1 - m) / 2 : ℕ) : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)) = 0 := by
      have hint : (m : ℤ) + (2 * (((s - 1 - m) / 2 : ℕ) : ℤ) - ((s : ℤ) - 1)) = 0 := by omega
      exact_mod_cast hint
    rw [Finset.prod_eq_zero hmem hfac, mul_zero, mul_zero]

/-- Period-4 quasipolynomial encoding the exact spherical harmonic multiplicities of
`ℝℙˢ = Sˢ / {±1}` (`s ≥ 2`) in the doubled spectral variable `2 u_{2j} = 4j + (s - 1)`
(the surviving even-degree harmonics `k = 2j`). -/
@[expose] def rpsQP (s : ℕ) (_hs : 2 ≤ s) : Quasipoly where
  M := 4
  hM := by norm_num
  «D» := s - 1
  c d n := if n % 4 = (s - 1) % 4 then (conformalScalarPoly s).coeff d.1 else 0
  periodic _ _ := by simp

lemma rpsQP_eval {s : ℕ} (hs : 2 ≤ s) (m : ℤ) :
    (rpsQP s hs).eval m =
      if (m % 4).toNat = (s - 1) % 4 then (conformalScalarPoly s).eval (m : ℂ) else 0 := by
  unfold Quasipoly.eval rpsQP
  simp only [Nat.cast_ofNat]
  have hmod4 : (m % 4).toNat % 4 = (m % 4).toNat := Nat.mod_eq_of_lt (by omega)
  simp_rw [hmod4]
  split_ifs with h
  · rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_conformalScalarPoly_le' hs)
      (Nat.lt_succ_self _)),
      Fin.sum_univ_eq_sum_range (fun d => (conformalScalarPoly s).coeff d * (m : ℂ) ^ d)]
  · exact Finset.sum_eq_zero fun d _ => by simp

/-- **Exact Parity Characterization of `ℝℙˢ`**:
The quasipolynomial `rpsQP s hs` has identically vanishing odd part **if and only if `s` is odd**.
For odd `s`, `(s - 1) % 4 ∈ {0, 2}` is negation-invariant mod 4 and `conformalScalarPoly s` is even;
for even `s`, both the congruence class `(s - 1) % 4 ∈ {1, 3}` and the polynomial break symmetry,
yielding `oddPart (s - 1) = 1 / 2 ≠ 0`. -/
theorem rpsQP_oddPart_eq_zero_iff {s : ℕ} (hs : 2 ≤ s) :
    (∀ m : ℤ, (rpsQP s hs).oddPart m = 0) ↔ Odd s := by
  constructor
  · intro hall
    by_contra hnot
    have heven : Even s := Nat.not_odd_iff_even.mp hnot
    have h0 := hall ((s - 1 : ℕ) : ℤ)
    unfold Quasipoly.oddPart at h0
    rw [rpsQP_eval hs ((s - 1 : ℕ) : ℤ), rpsQP_eval hs (-((s - 1 : ℕ) : ℤ))] at h0
    have hmod_pos : (((s - 1 : ℕ) : ℤ) % 4).toNat = (s - 1) % 4 := by omega
    have hmod_neg : ((-((s - 1 : ℕ) : ℤ)) % 4).toNat ≠ (s - 1) % 4 := by
      rcases heven with ⟨k, rfl⟩; omega
    rw [ite_eq_left_iff.mpr (fun h => (h hmod_pos).elim),
      ite_eq_right_iff.mpr (fun h => (hmod_neg h).elim),
      Int.cast_natCast, conformalScalarPoly_eval_ground' hs] at h0
    norm_num at h0
  · intro hodd m
    unfold Quasipoly.oddPart
    rw [rpsQP_eval hs m, rpsQP_eval hs (-m)]
    have heven_sub : Even (s - 1) := by rcases hodd with ⟨k, rfl⟩; exact ⟨k, by omega⟩
    have hmod_symm : ((-m) % 4).toNat = (s - 1) % 4 ↔ (m % 4).toNat = (s - 1) % 4 := by
      rcases heven_sub with ⟨k, hk⟩; omega
    by_cases h : (m % 4).toNat = (s - 1) % 4
    · have hneg : ((-m) % 4).toNat = (s - 1) % 4 := hmod_symm.mpr h
      rw [ite_eq_left_iff.mpr (fun hn => (hn h).elim),
        ite_eq_left_iff.mpr (fun hn => (hn hneg).elim),
        Int.cast_neg, conformalScalarPoly_eval_neg' hs, heven_sub.neg_one_pow]
      ring
    · have hneg : ((-m) % 4).toNat ≠ (s - 1) % 4 := fun h' => h (hmod_symm.mp h')
      rw [ite_eq_right_iff.mpr (fun h' => (h h').elim),
        ite_eq_right_iff.mpr (fun h' => (hneg h').elim)]
      ring

/-! #### A.6 Master Unconditional Bosonic Euler-Product Classification Theorems -/

private lemma lambertSeries_mul_dvd' {m : ℕ} (hm : 0 < m) (d : ℕ) :
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
        refine Finset.sum_congr rfl fun e _ => by split_ifs <;> simp [pow_succ']
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
      · intro a _; push_cast; rw [mul_pow]
    · rw [mul_zero]
      refine Finset.sum_eq_zero fun e he => ?_
      have hndvd : ¬ m ∣ e := fun hme => hmn (dvd_trans hme (Nat.dvd_of_mem_divisors he))
      simp only [hndvd, ↓reduceIte, mul_zero]

private lemma lambertSeries_const_mul' (c : ℂ) (w : ℕ → ℂ) :
    lambertSeries (fun n => c * w n) = PowerSeries.C c * lambertSeries w := by
  ext n
  rw [coeff_lambertSeries, PowerSeries.coeff_C_mul, coeff_lambertSeries]
  split_ifs with hn
  · simp
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring

private lemma lambertSeries_finset_sum' {ι : Type*} (s : Finset ι) (w : ι → ℕ → ℂ) :
    lambertSeries (fun n => ∑ i ∈ s, w i n) = ∑ i ∈ s, lambertSeries (w i) := by
  ext n
  rw [coeff_lambertSeries, map_sum]
  simp_rw [coeff_lambertSeries]
  split_ifs with hn
  · simp
  · simp_rw [Finset.mul_sum]; exact Finset.sum_comm

private lemma conformalScalarPoly_coeff_odd_eq_zero {s : ℕ} (hs : 2 ≤ s) (hodd : Odd s)
    {d : ℕ} (hd : Odd d) : (conformalScalarPoly s).coeff d = 0 := by
  have heven_sub : Even (s - 1) := by rcases hodd with ⟨k, rfl⟩; exact ⟨k, by omega⟩
  have hcomp : (conformalScalarPoly s).comp (Polynomial.C (-1 : ℂ) * Polynomial.X) =
      conformalScalarPoly s := by
    apply Polynomial.funext
    intro z
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      neg_one_mul, conformalScalarPoly_eval_neg' hs, heven_sub.neg_one_pow, one_mul]
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff d) hcomp
  rw [coeff_comp_C_mul_X', hd.neg_one_pow, neg_one_mul] at hc
  linear_combination -(1 / 2 : ℂ) * hc

/-- **Unconditional Bosonic Euler-Product D-Transcendence for ALL `ℂℙⁿ` (`n ≥ 1`)**:
Every complex projective space `ℂℙⁿ` has unconditionally D-transcendental conformal bosonic
Euler product over `ℂ(q)`. -/
theorem cpn_eulerProduct_dTrans (n : ℕ) (hn : 1 ≤ n) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (eulerProduct (fun s => (cpnQP n hn).eval (s : ℤ)))) :=
  quasipoly_eulerProduct_algebraicIndependent (cpnQP n hn) (cpnQP_oddPart_ne_zero hn)
    (Eventually.of_forall fun _ => rfl)

/-- **Unconditional Bosonic Euler-Product D-Transcendence for ALL `ℍℙⁿ` (`n ≥ 1`)**:
Every quaternionic projective space `ℍℙⁿ` has unconditionally D-transcendental conformal bosonic
Euler product over `ℂ(q)`. -/
theorem hpn_eulerProduct_dTrans (n : ℕ) (hn : 1 ≤ n) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (eulerProduct (fun s => (hpnQP n hn).eval (s : ℤ)))) :=
  quasipoly_eulerProduct_algebraicIndependent (hpnQP n hn) (hpnQP_oddPart_ne_zero hn)
    (Eventually.of_forall fun _ => rfl)

/-- **Unconditional Bosonic Euler-Product D-Transcendence for `𝕆ℙ² = F₄ / Spin(9)`**:
The 16-dimensional Cayley projective plane `𝕆ℙ²` has unconditionally D-transcendental conformal
bosonic Euler product over `ℂ(q)`. -/
theorem op2_eulerProduct_dTrans :
    AlgebraicIndependent ℂ
      (seriesCoordinates (eulerProduct (fun s => op2QP.eval (s : ℤ)))) :=
  quasipoly_eulerProduct_algebraicIndependent op2QP op2QP_oddPart_ne_zero
    (Eventually.of_forall fun _ => rfl)

/-- **Complete Real Projective Space `ℝℙˢ` Parity Dichotomy (`∀ s ≥ 2`)**:
The conformal bosonic Euler product on `ℝℙˢ = Sˢ / {±1}` is D-algebraic over `ℂ(q)`
**if and only if `s` is odd** (D-algebraic for `ℝℙ³, ℝℙ⁵, …` via quasi-modular forms of levels
`2, 4`; unconditionally D-transcendental for `ℝℙ², ℝℙ⁴, …`). -/
theorem rps_eulerProduct_dAlg_iff (s : ℕ) (hs : 2 ≤ s) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun m => (rpsQP s hs).eval (m : ℤ)))) ↔
      Odd s := by
  constructor
  · intro hdep
    refine (rpsQP_oddPart_eq_zero_iff hs).mp fun m => ?_
    by_contra hne
    exact hdep (quasipoly_eulerProduct_algebraicIndependent (rpsQP s hs) ⟨m, hne⟩
      (Eventually.of_forall fun _ => rfl))
  · intro hodd
    have hhalf : (s - 1) % 4 = 0 ∨ (s - 1) % 4 = 2 := by
      rcases hodd with ⟨k, rfl⟩; omega
    let R := Finset.range ((s - 1) / 2 + 1)
    have heval_even_sum : ∀ m : ℕ,
        (conformalScalarPoly s).eval (m : ℂ) =
          ∑ k ∈ R, (conformalScalarPoly s).coeff (2 * k) * (m : ℂ) ^ (2 * k) := by
      intro m
      rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_conformalScalarPoly_le' hs)
        (Nat.lt_succ_self _)), show (s - 1).succ = s by omega]
      have hsplit : Finset.range s =
          (Finset.range s).filter Even ∪ (Finset.range s).filter (fun d => ¬ Even d) :=
        (Finset.filter_union_filter_not_eq Even (Finset.range s)).symm
      rw [hsplit, Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _)]
      have hodd_zero : ∑ d ∈ (Finset.range s).filter (fun d => ¬ Even d),
          (conformalScalarPoly s).coeff d * (m : ℂ) ^ d = 0 := by
        refine Finset.sum_eq_zero fun d hd => ?_
        have hdo : Odd d := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hd).2
        rw [conformalScalarPoly_coeff_odd_eq_zero hs hodd hdo, zero_mul]
      rw [hodd_zero, add_zero]
      refine Finset.sum_bij (fun d _ => d / 2) ?_ ?_ ?_ ?_
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hlt : d < s := Finset.mem_range.mp hd'.1
        exact Finset.mem_range.mpr (by omega)
      · intro a ha b hb hab
        obtain ⟨k₁, hk₁⟩ := (Finset.mem_filter.mp ha).2
        obtain ⟨k₂, hk₂⟩ := (Finset.mem_filter.mp hb).2
        omega
      · intro k hk
        have hk' : k < (s - 1) / 2 + 1 := Finset.mem_range.mp hk
        rcases hodd with ⟨r, rfl⟩
        refine ⟨2 * k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨k, by omega⟩⟩,
          by omega⟩
      · intro d hd
        obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hd).2
        have h2 : 2 * (d / 2) = d := by omega
        rw [h2]
    rcases hhalf with hmod0 | hmod2
    · -- Case `(s - 1) % 4 = 0`: weight supported on `4 ∣ m`
      let S : Finset ℕ+ := {4}
      have hH_eq : lambertSeries (fun m => (rpsQP s hs).eval (m : ℤ)) =
          ∑ k ∈ R, PowerSeries.C ((conformalScalarPoly s).coeff (2 * k) * (4 : ℂ) ^ (2 * k + 1)) *
            PowerSeries.expand (4 : ℕ+).1 (4 : ℕ+).2.ne' (sigmaSeries (2 * k + 1)) := by
        have hfun : (fun m : ℕ => (rpsQP s hs).eval (m : ℤ)) =
            fun m : ℕ => ∑ k ∈ R, (conformalScalarPoly s).coeff (2 * k) *
              (if 4 ∣ m then (m : ℂ) ^ (2 * k) else 0) := by
          funext m
          rw [rpsQP_eval hs (m : ℤ), hmod0, Int.cast_natCast, heval_even_sum m]
          have hcond : ((m : ℤ) % 4).toNat = 0 ↔ 4 ∣ m := by omega
          by_cases h4 : 4 ∣ m
          · rw [ite_eq_left_iff.mpr (fun hn => (hn (hcond.mpr h4)).elim)]
            refine Finset.sum_congr rfl fun k _ => by simp [h4]
          · rw [ite_eq_right_iff.mpr (fun h => (h4 (hcond.mp h)).elim)]
            symm; exact Finset.sum_eq_zero fun k _ => by simp [h4]
        rw [hfun, lambertSeries_finset_sum']
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lambertSeries_const_mul', lambertSeries_mul_dvd' (by norm_num : 0 < 4) (2 * k),
          ← mul_assoc, ← map_mul]
        rfl
      have hspan := (evenDivisorSpan_dAlgebraic (S := S) R
        (fun k => (conformalScalarPoly s).coeff (2 * k) * (4 : ℂ) ^ (2 * k + 1))
        (fun _ => (4 : ℕ+)) (fun _ _ => Finset.mem_singleton_self _) (fun k => k)).2
      exact hspan _ (hH_eq ▸ eulerProduct_ode _)
    · -- Case `(s - 1) % 4 = 2`: `1_{m ≡ 2 (4)} = 1_{2 ∣ m} - 1_{4 ∣ m}`
      let S : Finset ℕ+ := {2, 4}
      let idx : Finset (ℕ × Fin 2) := R ×ˢ (Finset.univ : Finset (Fin 2))
      let cFn : ℕ × Fin 2 → ℂ := fun p =>
        if p.2 = 0 then (conformalScalarPoly s).coeff (2 * p.1) * (2 : ℂ) ^ (2 * p.1 + 1)
        else -((conformalScalarPoly s).coeff (2 * p.1) * (4 : ℂ) ^ (2 * p.1 + 1))
      let mFn : ℕ × Fin 2 → ℕ+ := fun p => if p.2 = 0 then (2 : ℕ+) else (4 : ℕ+)
      have hmS : ∀ p ∈ idx, mFn p ∈ S := fun p _ => by
        dsimp only [mFn, S]; split_ifs <;> simp
      have hH_eq : lambertSeries (fun m => (rpsQP s hs).eval (m : ℤ)) =
          ∑ p ∈ idx, PowerSeries.C (cFn p) *
            PowerSeries.expand (mFn p).1 (mFn p).2.ne' (sigmaSeries (2 * p.1 + 1)) := by
        have hfun : (fun m : ℕ => (rpsQP s hs).eval (m : ℤ)) =
            fun m : ℕ => ∑ p ∈ idx,
              (if p.2 = 0 then (conformalScalarPoly s).coeff (2 * p.1) *
                  (if 2 ∣ m then (m : ℂ) ^ (2 * p.1) else 0)
               else -((conformalScalarPoly s).coeff (2 * p.1)) *
                  (if 4 ∣ m then (m : ℂ) ^ (2 * p.1) else 0)) := by
          funext m
          rw [rpsQP_eval hs (m : ℤ), hmod2, Int.cast_natCast, heval_even_sum m,
            Finset.sum_product]
          have hpair : ∀ k ∈ R,
              (∑ j : Fin 2,
                if j = 0 then (conformalScalarPoly s).coeff (2 * k) *
                    (if 2 ∣ m then (m : ℂ) ^ (2 * k) else 0)
                else -(conformalScalarPoly s).coeff (2 * k) *
                    (if 4 ∣ m then (m : ℂ) ^ (2 * k) else 0)) =
              if ((m : ℤ) % 4).toNat = 2 then (conformalScalarPoly s).coeff (2 * k) * (m : ℂ) ^ (2 * k)
              else 0 := by
            intro k _
            rw [Fin.sum_univ_two]
            simp only [↓reduceIte, Fin.one_eq_zero_iff]
            by_cases h4 : 4 ∣ m
            · have h2 : 2 ∣ m := dvd_trans (by norm_num : 2 ∣ 4) h4
              have hne2 : ((m : ℤ) % 4).toNat ≠ 2 := by omega
              simp [h2, h4, hne2]
            · by_cases h2 : 2 ∣ m
              · have heq2 : ((m : ℤ) % 4).toNat = 2 := by omega
                simp [h2, h4, heq2]
              · have hne2 : ((m : ℤ) % 4).toNat ≠ 2 := by omega
                simp [h2, h4, hne2]
          rw [Finset.sum_congr rfl hpair]
          split_ifs with h
          · rfl
          · simp
        rw [hfun, lambertSeries_finset_sum']
        refine Finset.sum_congr rfl fun p _ => ?_
        rcases p with ⟨k, j⟩
        by_cases hj : j = 0
        · subst hj
          simp only [cFn, mFn, ↓reduceIte]
          rw [lambertSeries_const_mul', lambertSeries_mul_dvd' (by norm_num : 0 < 2) (2 * k),
            ← mul_assoc, ← map_mul]
          rfl
        · simp only [cFn, mFn, hj, ↓reduceIte]
          rw [lambertSeries_const_mul', lambertSeries_mul_dvd' (by norm_num : 0 < 4) (2 * k),
            ← mul_assoc, ← map_mul]
          congr 2; ring
      have hspan := (evenDivisorSpan_dAlgebraic (S := S) idx cFn mFn hmS (fun p => p.1)).2
      exact hspan _ (hH_eq ▸ eulerProduct_ode _)

/-! #### A.7 Headline Cartan Classification Uniqueness Packaging Theorems -/

/-- Exhaustive Élie Cartan classification of simply connected compact rank-1 symmetric spaces
(CROSS) of real dimension `≥ 2`. -/
inductive SimplyConnectedCROSS where
  | sphere (s : ℕ) (hs : 2 ≤ s)
  | cp (n : ℕ) (hn : 1 ≤ n)
  | hp (n : ℕ) (hn : 1 ≤ n)
  | op2

namespace SimplyConnectedCROSS

/-- Real dimension of a simply connected compact rank-1 symmetric space. -/
@[expose] def realDim : SimplyConnectedCROSS → ℕ
  | .sphere s _ => s
  | .cp n _ => 2 * n
  | .hp n _ => 4 * n
  | .op2 => 16

/-- Exact period-2 conformal bosonic multiplicity quasipolynomial of a simply connected CROSS. -/
@[expose] def qp : SimplyConnectedCROSS → Quasipoly
  | .sphere s _ => conformalScalarSphereQP s
  | .cp n hn => cpnQP n hn
  | .hp n hn => hpnQP n hn
  | .op2 => op2QP

/-- Predicate characterizing odd-dimensional spheres `S^{2r+1}` inside Cartan's classification. -/
@[expose] def isOddSphere : SimplyConnectedCROSS → Prop
  | .sphere s _ => Odd s
  | .cp _ _ => False
  | .hp _ _ => False
  | .op2 => False

lemma isOddSphere_iff_odd_realDim (M : SimplyConnectedCROSS) :
    M.isOddSphere ↔ Odd M.realDim := by
  cases M with
  | sphere s _ => rfl
  | cp n _ => simp [isOddSphere, realDim, Nat.not_odd_iff_even]
  | hp n _ =>
    simp only [isOddSphere, realDim, false_iff, Nat.not_odd_iff_even]
    exact ⟨2 * n, by ring⟩
  | op2 =>
    simp only [isOddSphere, realDim, false_iff, Nat.not_odd_iff_even]
    exact ⟨8, by norm_num⟩

end SimplyConnectedCROSS

/-- **Headline Cartan Odd-Sphere Uniqueness Theorem**:
Across the entire Élie Cartan classification of simply connected compact rank-1 symmetric spaces
(`Sˢ`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`), the conformal bosonic Euler product
`Z_M^{bose}(q) = ∏_{k ≥ 0} (1 - q^{2 u_k})^{-m_k}` is D-algebraic over `ℂ(q)`
**if and only if `M` is an odd-dimensional sphere `S^{2r+1}`**! -/
theorem cross_simplyConnected_dAlg_iff (M : SimplyConnectedCROSS) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun s => M.qp.eval (s : ℤ)))) ↔
      M.isOddSphere := by
  cases M with
  | sphere s hs => exact conformalScalar_sphere_allDim_eulerProduct_iff hs
  | cp n hn =>
    simp only [SimplyConnectedCROSS.qp, SimplyConnectedCROSS.isOddSphere, iff_false, not_not]
    exact cpn_eulerProduct_dTrans n hn
  | hp n hn =>
    simp only [SimplyConnectedCROSS.qp, SimplyConnectedCROSS.isOddSphere, iff_false, not_not]
    exact hpn_eulerProduct_dTrans n hn
  | op2 =>
    simp only [SimplyConnectedCROSS.qp, SimplyConnectedCROSS.isOddSphere, iff_false, not_not]
    exact op2_eulerProduct_dTrans

/-- Complete Cartan classification of ALL compact rank-1 symmetric spaces (simply connected
and non-simply-connected `ℝℙˢ`) of real dimension `≥ 2`. -/
inductive CompactRankOneSymmetric where
  | sphere (s : ℕ) (hs : 2 ≤ s)
  | rp (s : ℕ) (hs : 2 ≤ s)
  | cp (n : ℕ) (hn : 1 ≤ n)
  | hp (n : ℕ) (hn : 1 ≤ n)
  | op2

namespace CompactRankOneSymmetric

/-- Real dimension of any compact rank-1 symmetric space. -/
@[expose] def realDim : CompactRankOneSymmetric → ℕ
  | .sphere s _ => s
  | .rp s _ => s
  | .cp n _ => 2 * n
  | .hp n _ => 4 * n
  | .op2 => 16

/-- Exact conformal bosonic multiplicity quasipolynomial of any compact rank-1 symmetric space. -/
@[expose] def qp : CompactRankOneSymmetric → Quasipoly
  | .sphere s _ => conformalScalarSphereQP s
  | .rp s hs => rpsQP s hs
  | .cp n hn => cpnQP n hn
  | .hp n hn => hpnQP n hn
  | .op2 => op2QP

end CompactRankOneSymmetric

/-- **Complete Cartan CROSS Dimensional-Parity Theorem (All Simply & Non-Simply Connected CROSS)**:
Across EVERY compact rank-1 symmetric space (`Sˢ`, `ℝℙˢ`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`), the conformal
bosonic Euler product is D-algebraic over `ℂ(q)` **if and only if `dim_ℝ M` is odd** (uniquely
`S^{2r+1}` and `ℝℙ^{2r+1}`). -/
theorem cross_all_dAlg_iff (M : CompactRankOneSymmetric) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun s => M.qp.eval (s : ℤ)))) ↔
      Odd M.realDim := by
  cases M with
  | sphere s hs => exact conformalScalar_sphere_allDim_eulerProduct_iff hs
  | rp s hs => exact rps_eulerProduct_dAlg_iff s hs
  | cp n hn =>
    have hnot : ¬ Odd (2 * n) := Nat.not_odd_iff_even.mpr ⟨n, by ring⟩
    simp only [CompactRankOneSymmetric.qp, CompactRankOneSymmetric.realDim, hnot, iff_false, not_not]
    exact cpn_eulerProduct_dTrans n hn
  | hp n hn =>
    have hnot : ¬ Odd (4 * n) := Nat.not_odd_iff_even.mpr ⟨2 * n, by ring⟩
    simp only [CompactRankOneSymmetric.qp, CompactRankOneSymmetric.realDim, hnot, iff_false, not_not]
    exact hpn_eulerProduct_dTrans n hn
  | op2 =>
    have hnot : ¬ Odd 16 := Nat.not_odd_iff_even.mpr ⟨8, by norm_num⟩
    simp only [CompactRankOneSymmetric.qp, CompactRankOneSymmetric.realDim, hnot, iff_false, not_not]
    exact op2_eulerProduct_dTrans

/-! ### Part B: Leading Borel Pole Combinatorics & Strong `ℂ({t})` Wave-EGF D-Transcendence -/

/-! #### B.1 Exact `u`-Variable Multiplicity Polynomials & Integer Leading Pole Coefficients -/

/-- Convert a doubled-variable polynomial `P(j)` (`j = 2u`) to the `u`-variable Weyl multiplicity
polynomial `m(u) = P(2u)`. -/
@[expose] def multPolyOfDoubled (P : Polynomial ℂ) : Polynomial ℂ :=
  P.comp (Polynomial.C 2 * Polynomial.X)

lemma multPolyOfDoubled_eval (P : Polynomial ℂ) (u : ℂ) :
    (multPolyOfDoubled P).eval u = P.eval (2 * u) := by
  simp [multPolyOfDoubled, Polynomial.eval_comp]

lemma multPolyOfDoubled_coeff (P : Polynomial ℂ) (k : ℕ) :
    (multPolyOfDoubled P).coeff k = (2 : ℂ) ^ k * P.coeff k := by
  unfold multPolyOfDoubled
  induction P using Polynomial.induction_on' with
  | add a b ha hb => simp only [Polynomial.add_comp, Polynomial.coeff_add, ha, hb, mul_add]
  | monomial i c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hik
    · subst hik; ring
    · simp

/-- Exact `u`-variable Weyl multiplicity polynomials `m_M(u)` for `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`, `Sˢ`. -/
@[expose] def cpnMultPoly (n : ℕ) : Polynomial ℂ := multPolyOfDoubled (cpnPoly n)
@[expose] def hpnMultPoly (n : ℕ) : Polynomial ℂ := multPolyOfDoubled (hpnPoly n)
@[expose] def op2MultPoly : Polynomial ℂ := multPolyOfDoubled op2Poly
@[expose] def sphereMultPoly (s : ℕ) : Polynomial ℂ := multPolyOfDoubled (conformalScalarPoly s)

/-- **Exact Leading Borel Pole Coefficient for `ℂℙⁿ` (Central Binomials `C(2n, n)`)**:
`L_{ℂℙⁿ} · (2n - 1)! = Nat.choose (2 * n) n` (`2, 6, 20, 70, …`). -/
theorem cpn_leading_pole_coeff (n : ℕ) (hn : 1 ≤ n) :
    (cpnMultPoly n).coeff (2 * n - 1) * ((2 * n - 1).factorial : ℂ) =
      (Nat.choose (2 * n) n : ℂ) := by
  rw [cpnMultPoly, multPolyOfDoubled_coeff, cpnPoly_coeff_top hn]
  have hpow : (2 : ℂ) ^ (2 * n - 1) = (2 : ℂ) * (2 : ℂ) ^ (2 * (n - 1)) := by
    rw [← pow_succ']; congr 1; omega
  have hnat : Nat.choose (2 * n) n * n * (Nat.factorial (n - 1)) ^ 2 =
      2 * Nat.factorial (2 * n - 1) := by
    have hch := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at hch
    have h2n : Nat.factorial (2 * n) = (2 * n) * Nat.factorial (2 * n - 1) := by
      conv_lhs => rw [show 2 * n = (2 * n - 1) + 1 by omega, Nat.factorial_succ]
      congr 1; omega
    have hnfac : Nat.factorial n = n * Nat.factorial (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
      congr 1; omega
    rw [h2n, hnfac] at hch
    have hmul : n * (Nat.choose (2 * n) n * n * (Nat.factorial (n - 1)) ^ 2) =
        n * (2 * Nat.factorial (2 * n - 1)) := by
      nlinarith [hch]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) hmul
  have hC : (Nat.choose (2 * n) n : ℂ) * (n : ℂ) * (Nat.factorial (n - 1) : ℂ) ^ 2 =
      2 * (Nat.factorial (2 * n - 1) : ℂ) := by exact_mod_cast hnat
  have h2ne : (2 : ℂ) ^ (2 * (n - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hf1 : (Nat.factorial (n - 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hden : (2 : ℂ) ^ (2 * (n - 1)) * (n : ℂ) * (Nat.factorial (n - 1) : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2ne hnne) (pow_ne_zero 2 hf1)
  rw [hpow, mul_assoc, ← div_eq_inv_mul, mul_div_assoc', div_eq_iff hden]
  calc (2 : ℂ) * (2 : ℂ) ^ (2 * (n - 1)) * (Nat.factorial (2 * n - 1) : ℂ)
      = (2 : ℂ) ^ (2 * (n - 1)) * (2 * (Nat.factorial (2 * n - 1) : ℂ)) := by ring
    _ = (2 : ℂ) ^ (2 * (n - 1)) *
        ((Nat.choose (2 * n) n : ℂ) * (n : ℂ) * (Nat.factorial (n - 1) : ℂ) ^ 2) := by rw [← hC]
    _ = (Nat.choose (2 * n) n : ℂ) * ((2 : ℂ) ^ (2 * (n - 1)) * (n : ℂ) *
        (Nat.factorial (n - 1) : ℂ) ^ 2) := by ring

/-- **Exact Leading Borel Pole Coefficient for `ℍℙⁿ` (Even Catalan Numbers `C_{2n}`)**:
`L_{ℍℙⁿ} · (4n - 1)! = Nat.choose (4 * n) (2 * n) / (2 * n + 1)` (`2, 14, 132, 1430, …`). -/
theorem hpn_leading_pole_coeff (n : ℕ) (hn : 1 ≤ n) :
    (hpnMultPoly n).coeff (4 * n - 1) * ((4 * n - 1).factorial : ℂ) =
      ((Nat.choose (4 * n) (2 * n) / (2 * n + 1) : ℕ) : ℂ) := by
  rw [hpnMultPoly, multPolyOfDoubled_coeff, hpnPoly_coeff_top hn]
  have hpow : (2 : ℂ) ^ (4 * n - 1) = (2 : ℂ) * (2 : ℂ) ^ (4 * n - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hdvd : (2 * n + 1) ∣ Nat.choose (4 * n) (2 * n) := by
    simpa [Nat.centralBinom, show 2 * (2 * n) = 4 * n by omega] using
      Nat.succ_dvd_centralBinom (2 * n)
  have hdiv : (2 * n + 1) * (Nat.choose (4 * n) (2 * n) / (2 * n + 1)) =
      Nat.choose (4 * n) (2 * n) := Nat.mul_div_cancel' hdvd
  have hnat : (Nat.choose (4 * n) (2 * n) / (2 * n + 1)) * (2 * n + 1) * (2 * n) *
      (Nat.factorial (2 * n - 1)) ^ 2 = 2 * Nat.factorial (4 * n - 1) := by
    have hch := Nat.choose_mul_factorial_mul_factorial (show 2 * n ≤ 4 * n by omega)
    rw [show 4 * n - 2 * n = 2 * n by omega] at hch
    have h4n : Nat.factorial (4 * n) = (4 * n) * Nat.factorial (4 * n - 1) := by
      conv_lhs => rw [show 4 * n = (4 * n - 1) + 1 by omega, Nat.factorial_succ]
      congr 1; omega
    have h2n : Nat.factorial (2 * n) = (2 * n) * Nat.factorial (2 * n - 1) := by
      conv_lhs => rw [show 2 * n = (2 * n - 1) + 1 by omega, Nat.factorial_succ]
      congr 1; omega
    rw [h4n, h2n] at hch
    have hmul : (2 * n) * (Nat.choose (4 * n) (2 * n) * (2 * n) * (Nat.factorial (2 * n - 1)) ^ 2) =
        (2 * n) * (2 * Nat.factorial (4 * n - 1)) := by
      nlinarith [hch]
    have hstep := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n) hmul
    rw [← hdiv] at hstep
    nlinarith [hstep]
  have hC : ((Nat.choose (4 * n) (2 * n) / (2 * n + 1) : ℕ) : ℂ) *
      ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) * (Nat.factorial (2 * n - 1) : ℂ) ^ 2 =
      2 * (Nat.factorial (4 * n - 1) : ℂ) := by exact_mod_cast hnat
  have h2ne : (2 : ℂ) ^ (4 * n - 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2n1 : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2n0 : ((2 * n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hf1 : (Nat.factorial (2 * n - 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hden : (2 : ℂ) ^ (4 * n - 2) * ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) *
      (Nat.factorial (2 * n - 1) : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2ne h2n1) h2n0) (pow_ne_zero 2 hf1)
  rw [hpow, mul_assoc, ← div_eq_inv_mul, mul_div_assoc', div_eq_iff hden]
  calc (2 : ℂ) * (2 : ℂ) ^ (4 * n - 2) * (Nat.factorial (4 * n - 1) : ℂ)
      = (2 : ℂ) ^ (4 * n - 2) * (2 * (Nat.factorial (4 * n - 1) : ℂ)) := by ring
    _ = (2 : ℂ) ^ (4 * n - 2) *
        (((Nat.choose (4 * n) (2 * n) / (2 * n + 1) : ℕ) : ℂ) *
          ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) * (Nat.factorial (2 * n - 1) : ℂ) ^ 2) := by
        rw [← hC]
    _ = ((Nat.choose (4 * n) (2 * n) / (2 * n + 1) : ℕ) : ℂ) *
        ((2 : ℂ) ^ (4 * n - 2) * ((2 * n + 1 : ℕ) : ℂ) * ((2 * n : ℕ) : ℂ) *
          (Nat.factorial (2 * n - 1) : ℂ) ^ 2) := by ring

/-- Explicit Catalan-number form of `hpn_leading_pole_coeff`: `L_{ℍℙⁿ} · (4n - 1)! = catalan (2n)`. -/
theorem hpn_leading_pole_coeff_catalan (n : ℕ) (hn : 1 ≤ n) :
    (hpnMultPoly n).coeff (4 * n - 1) * ((4 * n - 1).factorial : ℂ) = (catalan (2 * n) : ℂ) := by
  rw [hpn_leading_pole_coeff n hn, catalan_eq_centralBinom_div (2 * n), Nat.centralBinom,
    show 2 * (2 * n) = 4 * n by omega]

/-- **Exact Leading Borel Pole Coefficient for `𝕆ℙ²`**: `L_{𝕆ℙ²} · 15! = 78`. -/
theorem op2_leading_pole_coeff :
    op2MultPoly.coeff 15 * ((15 : ℕ).factorial : ℂ) = 78 := by
  rw [op2MultPoly, multPolyOfDoubled_coeff, op2Poly_coeff_15]
  norm_num [Nat.factorial]

/-- **Exact Leading Borel Pole Coefficient for Even Spheres `S^{2r}`**: `L_{S^{2r}} · (2r - 1)! = 2`. -/
theorem evenSphere_leading_pole_coeff (r : ℕ) (hr : 1 ≤ r) :
    (sphereMultPoly (2 * r)).coeff (2 * r - 1) * ((2 * r - 1).factorial : ℂ) = 2 := by
  rw [sphereMultPoly, multPolyOfDoubled_coeff, conformalScalarPoly_coeff_top (by omega)]
  have hpow : (2 : ℂ) ^ (2 * r - 1) = (2 : ℂ) * (2 : ℂ) ^ (2 * r - 2) := by
    rw [← pow_succ']; congr 1; omega
  have h2ne : (2 : ℂ) ^ (2 * r - 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfne : ((2 * r - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hpow]
  field_simp [h2ne, hfne]

/-! #### B.2 Regularized Wave-EGF Kernels (`psi0Reg`, `psiHalfReg`) & General `HigherOrderBorelData` -/

/-- Regularized integer-lattice wave kernel `ψ₀^{reg}(y) = (e^y - 1)⁻¹ - y⁻¹` with removable
singularity at `y = 0`, defined cleanly via `dslope bernEGF 0`. -/
@[expose] def psi0Reg (y : ℂ) : ℂ :=
  dslope bernEGF 0 y

/-- Regularized half-integer-lattice core `y / (2 sinh (y / 2))` with removable singularity `1`
at `y = 0`. -/
@[expose] def cschCore (y : ℂ) : ℂ :=
  (dslope (fun w : ℂ => 2 * Complex.sinh (w / 2)) 0 y)⁻¹

/-- Regularized half-integer-lattice wave kernel `ψ_{1/2}^{reg}(y) = (2 sinh (y / 2))⁻¹ - y⁻¹`
with removable singularity at `y = 0`. -/
@[expose] def psiHalfReg (y : ℂ) : ℂ :=
  dslope cschCore 0 y

/-- Regularized wave EGF `W_P^{reg}(y) = ∑_{j=0}^{d-1} c_j (-1)^j ψ^{(j)}(y)` associated to a
multiplicity polynomial `P(u) = ∑ c_j u^j` of degree `< d` and base kernel `ψ ∈ {psi0Reg, psiHalfReg}`. -/
@[expose] def waveEGFReg (ψ : ℂ → ℂ) (P : Polynomial ℂ) (d : ℕ) (y : ℂ) : ℂ :=
  ∑ j ∈ Finset.range d, P.coeff j * (-1 : ℂ) ^ j * iteratedDeriv j ψ y

/-- Imaginary-axis pole lattice `ω_m = 2π (m + 1)` for all even-dimensional CROSS wave EGFs. -/
@[expose] def crossWavePole (m : ℕ) : ℝ :=
  2 * Real.pi * ((m : ℝ) + 1)

private lemma crossWavePole_pos : 0 < crossWavePole 0 := by
  unfold crossWavePole; positivity

private lemma crossWavePole_mono : StrictMono crossWavePole := fun a b hab => by
  unfold crossWavePole
  have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  nlinarith [Real.pi_pos]

private lemma exp_I_pi_div_two : Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ)) = I := by
  rw [show I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I by ring,
    Complex.exp_mul_I]
  simp

private lemma exp_neg_I_pi_div_two : Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ)) = -I := by
  rw [show -I * ((Real.pi / 2 : ℝ) : ℂ) = ((-(Real.pi / 2) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I]
  simp

private lemma not_pole_of_mem_crossWedge {z : ℂ}
    (hz : z ∈ rotatedPuncturedWedge (Real.pi / 2) (Real.pi / 3) Real.pi crossWavePole) :
    ∀ k : ℤ, k ≠ 0 → z ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ) := by
  intro k hk0 heq
  let w : ℂ := Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ)) * z
  have hw_eq : w = ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) := by
    dsimp only [w]
    rw [exp_neg_I_pi_div_two, heq]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rcases lt_trichotomy k 0 with hk_neg | rfl | hk_pos
  · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
    have hw_re : w.re ≤ -(2 * Real.pi) := by rw [hw_eq, Complex.ofReal_re]; nlinarith [Real.pi_pos]
    rcases hz.1 with hball | hsec
    · rw [Metric.mem_ball, dist_zero_right] at hball
      have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
      have h2 : 2 * Real.pi ≤ |w.re| := by rw [abs_of_nonpos (by linarith [Real.pi_pos])]; linarith
      change ‖w‖ < Real.pi at hball
      linarith [Real.pi_pos]
    · have hre_pos : 0 < w.re := hsec.1
      linarith [Real.pi_pos]
  · exact hk0 rfl
  · apply hz.2
    refine ⟨(k - 1).toNat, ?_⟩
    change (crossWavePole (k - 1).toNat : ℂ) = w
    rw [hw_eq]
    have hk_nat : ((k - 1).toNat : ℂ) + 1 = (k : ℂ) := by
      have : ((k - 1).toNat : ℤ) + 1 = k := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      exact_mod_cast this
    unfold crossWavePole
    push_cast
    rw [hk_nat]

private lemma psi0Reg_eq_of_ne_zero {y : ℂ} (hy : y ≠ 0) :
    psi0Reg y = (Complex.exp y - 1)⁻¹ - y⁻¹ := by
  unfold psi0Reg
  rw [dslope_of_ne _ hy, slope_def_field, bernEGF_zero, bernEGF_eq_of_ne_zero hy, sub_zero]
  field_simp [hy]

private lemma psi0Reg_analyticAt {y : ℂ}
    (h : y = 0 ∨ ∀ k : ℤ, k ≠ 0 → y ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ)) :
    AnalyticAt ℂ psi0Reg y := by
  have hbern : AnalyticAt ℂ bernEGF y := by
    have hphi := phiBern_analyticAt h
    have heq : bernEGF = fun z => phiBern z + (1 - z / 2) := funext bernEGF_eq_phiBern_add
    rw [heq]
    exact hphi.add (analyticAt_const.sub (analyticAt_id.mul analyticAt_const))
  by_cases hy : y = 0
  · subst hy
    exact hbern.hasFPowerSeriesAt.dslope_fslope.analyticAt
  · have hev : psi0Reg =ᶠ[𝓝 y] fun z : ℂ => (bernEGF z - 1) / z := by
      filter_upwards [isOpen_ne.mem_nhds hy] with z hz
      unfold psi0Reg
      rw [dslope_of_ne _ hz, slope_def_field, bernEGF_zero, sub_zero]
    exact ((hbern.sub analyticAt_const).div analyticAt_id hy).congr hev.symm

private lemma two_sinh_half_eq_zero_iff (y : ℂ) :
    2 * Complex.sinh (y / 2) = 0 ↔ ∃ k : ℤ, y = 2 * (Real.pi : ℂ) * I * (k : ℂ) := by
  have h2sinh : 2 * Complex.sinh (y / 2) = Complex.exp (y / 2) - Complex.exp (-(y / 2)) := by
    rw [Complex.sinh]; ring
  rw [h2sinh, sub_eq_zero]
  constructor
  · intro h
    have hmul : Complex.exp y = 1 := by
      calc Complex.exp y = Complex.exp (y / 2 + y / 2) := by congr 1; ring
        _ = Complex.exp (y / 2) * Complex.exp (y / 2) := Complex.exp_add _ _
        _ = Complex.exp (-(y / 2)) * Complex.exp (y / 2) := by rw [h]
        _ = Complex.exp (-(y / 2) + y / 2) := (Complex.exp_add _ _).symm
        _ = 1 := by simp
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hmul
    exact ⟨k, by rw [hk]; ring⟩
  · rintro ⟨k, rfl⟩
    have harg : 2 * (Real.pi : ℂ) * I * (k : ℂ) / 2 = (k : ℂ) * ((Real.pi : ℂ) * I) := by ring
    rw [harg]
    have hneg : -((k : ℂ) * ((Real.pi : ℂ) * I)) =
        (k : ℂ) * ((Real.pi : ℂ) * I) + (-(k : ℤ) : ℤ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast; ring
    rw [hneg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma hasDerivAt_two_sinh_half (y : ℂ) :
    HasDerivAt (fun w : ℂ => 2 * Complex.sinh (w / 2)) (Complex.cosh (y / 2)) y := by
  have hfn : (fun w : ℂ => 2 * Complex.sinh (w / 2)) =
      fun w : ℂ => Complex.exp (w / 2) - Complex.exp (-(w / 2)) := by
    funext w; rw [Complex.sinh]; ring
  rw [hfn]
  have hhalf : HasDerivAt (fun w : ℂ => w / 2) (1 / 2 : ℂ) y := by
    simpa using (hasDerivAt_id y).div_const (2 : ℂ)
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (w / 2)) (Complex.exp (y / 2) * (1 / 2)) y :=
    (Complex.hasDerivAt_exp (y / 2)).comp y hhalf
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (-(w / 2)))
      (Complex.exp (-(y / 2)) * (-(1 / 2))) y :=
    (Complex.hasDerivAt_exp (-(y / 2))).comp y hhalf.neg
  refine (h1.sub h2).congr_deriv ?_
  rw [Complex.cosh]; ring

private lemma cschCore_zero : cschCore 0 = 1 := by
  unfold cschCore
  rw [dslope_same, (hasDerivAt_two_sinh_half 0).deriv]
  simp

private lemma cschCore_eq_of_ne_zero {y : ℂ} (hy : y ≠ 0) :
    cschCore y = y / (2 * Complex.sinh (y / 2)) := by
  unfold cschCore
  rw [dslope_of_ne _ hy, slope_def_field, show (0 : ℂ) / 2 = 0 by ring, Complex.sinh_zero,
    mul_zero, sub_zero, sub_zero, inv_div]

private lemma psiHalfReg_eq_of_ne_zero {y : ℂ} (hy : y ≠ 0) :
    psiHalfReg y = (2 * Complex.sinh (y / 2))⁻¹ - y⁻¹ := by
  unfold psiHalfReg
  rw [dslope_of_ne _ hy, slope_def_field, cschCore_zero, cschCore_eq_of_ne_zero hy, sub_zero]
  field_simp [hy]

private lemma dslope_two_sinh_half_analyticOn :
    AnalyticOnNhd ℂ (dslope (fun w : ℂ => 2 * Complex.sinh (w / 2)) 0) Set.univ := by
  have hent : Differentiable ℂ (fun w : ℂ => 2 * Complex.sinh (w / 2)) := fun w =>
    (hasDerivAt_two_sinh_half w).differentiableAt
  intro z _
  by_cases hz : z = 0
  · subst hz
    exact (hent.analyticAt 0).hasFPowerSeriesAt.dslope_fslope.analyticAt
  · have hev : dslope (fun w : ℂ => 2 * Complex.sinh (w / 2)) 0 =ᶠ[𝓝 z]
        fun w : ℂ => (2 * Complex.sinh (w / 2)) / w := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      rw [dslope_of_ne _ hw, slope_def_field, show (0 : ℂ) / 2 = 0 by ring, Complex.sinh_zero,
        mul_zero, sub_zero, sub_zero]
    exact ((hent.analyticAt z).div analyticAt_id hz).congr hev.symm

private lemma cschCore_analyticAt {y : ℂ}
    (h : y = 0 ∨ ∀ k : ℤ, k ≠ 0 → y ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ)) :
    AnalyticAt ℂ cschCore y := by
  have hd := dslope_two_sinh_half_analyticOn y (Set.mem_univ _)
  have hne : dslope (fun w : ℂ => 2 * Complex.sinh (w / 2)) 0 y ≠ 0 := by
    rcases eq_or_ne y 0 with rfl | hy
    · rw [dslope_same, (hasDerivAt_two_sinh_half 0).deriv]; simp
    · rw [dslope_of_ne _ hy, slope_def_field, show (0 : ℂ) / 2 = 0 by ring, Complex.sinh_zero,
        mul_zero, sub_zero, sub_zero]
      refine div_ne_zero (fun h0 => ?_) hy
      obtain ⟨k, hk⟩ := (two_sinh_half_eq_zero_iff y).mp h0
      rcases eq_or_ne k 0 with rfl | hk0
      · simp at hk; exact hy hk
      · rcases h with rfl | hfor
        · exact hy rfl
        · exact hfor k hk0 hk
  exact hd.inv hne

private lemma psiHalfReg_analyticAt {y : ℂ}
    (h : y = 0 ∨ ∀ k : ℤ, k ≠ 0 → y ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ)) :
    AnalyticAt ℂ psiHalfReg y := by
  have hcore := cschCore_analyticAt h
  by_cases hy : y = 0
  · subst hy
    exact hcore.hasFPowerSeriesAt.dslope_fslope.analyticAt
  · have hev : psiHalfReg =ᶠ[𝓝 y] fun z : ℂ => (cschCore z - 1) / z := by
      filter_upwards [isOpen_ne.mem_nhds hy] with z hz
      unfold psiHalfReg
      rw [dslope_of_ne _ hz, slope_def_field, cschCore_zero, sub_zero]
    exact ((hcore.sub analyticAt_const).div analyticAt_id hy).congr hev.symm

private lemma analyticAt_iteratedDeriv {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (j : ℕ) :
    AnalyticAt ℂ (iteratedDeriv j f) z := by
  induction j generalizing f with
  | zero => simpa using hf
  | succ j ih =>
    rw [iteratedDeriv_succ']
    exact ih hf.deriv

private lemma iteratedDeriv_inv_sub (c : ℂ) (j : ℕ) :
    ∀ z : ℂ, z ≠ c →
      iteratedDeriv j (fun w : ℂ => (w - c)⁻¹) z =
        (-1 : ℂ) ^ j * (j.factorial : ℂ) / (z - c) ^ (j + 1) := by
  induction j with
  | zero =>
    intro z _; simp [one_div]
  | succ j ih =>
    intro z hzc
    have hev : iteratedDeriv j (fun w : ℂ => (w - c)⁻¹) =ᶠ[𝓝 z]
        fun w : ℂ => (-1 : ℂ) ^ j * (j.factorial : ℂ) * ((w - c)⁻¹) ^ (j + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hzc] with w hw
      rw [ih w hw, div_eq_mul_inv, inv_pow]
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hsub : z - c ≠ 0 := sub_ne_zero.mpr hzc
    have hinv : HasDerivAt (fun w : ℂ => (w - c)⁻¹) (-1 / (z - c) ^ 2) z :=
      ((hasDerivAt_id z).sub_const c).inv hsub
    have hpow := (hinv.pow (j + 1)).const_mul ((-1 : ℂ) ^ j * (j.factorial : ℂ))
    change HasDerivAt (fun w : ℂ => (-1 : ℂ) ^ j * (j.factorial : ℂ) * ((w - c)⁻¹) ^ (j + 1)) _ z at hpow
    rw [hpow.deriv]
    simp only [Nat.add_sub_cancel, inv_pow, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp [hsub]

/-- Unified simple-pole decomposition: if `f` is analytic at `z₀ ≠ 0` with `f z₀ = 0` and
`deriv f z₀ = κ` (`κ ^ 2 = 1`), and `ψ w = (f w)⁻¹ - w⁻¹` on `w ≠ 0`, then on a punctured
neighborhood of `z₀`, `ψ w = κ / (w - z₀) + R w` with `AnalyticAt ℂ R z₀`. -/
private lemma simple_pole_decomp {ψ f : ℂ → ℂ} {z₀ κ : ℂ}
    (hz₀ : z₀ ≠ 0) (hf : AnalyticAt ℂ f z₀) (hf0 : f z₀ = 0)
    (hf' : deriv f z₀ = κ) (hκ2 : κ ^ 2 = 1)
    (hψ : ∀ w : ℂ, w ≠ 0 → ψ w = (f w)⁻¹ - w⁻¹) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R z₀ ∧
      ∀ᶠ w in 𝓝[≠] z₀, ψ w = κ / (w - z₀) + R w := by
  have hκ_ne : κ ≠ 0 := fun h => by rw [h, zero_pow two_ne_zero] at hκ2; norm_num at hκ2
  let h : ℂ → ℂ := dslope f z₀
  have hh : AnalyticAt ℂ h z₀ := hf.hasFPowerSeriesAt.dslope_fslope.analyticAt
  have hh0 : h z₀ = κ := by simp [h, dslope_same, hf']
  let R : ℂ → ℂ := fun w => -(κ * dslope h z₀ w) / h w - w⁻¹
  have hR : AnalyticAt ℂ R z₀ := by
    have hd : AnalyticAt ℂ (dslope h z₀) z₀ := hh.hasFPowerSeriesAt.dslope_fslope.analyticAt
    exact (((analyticAt_const.mul hd).neg).div hh (hh0.symm ▸ hκ_ne)).sub (analyticAt_id.inv hz₀)
  refine ⟨R, hR, ?_⟩
  have hne0 : ∀ᶠ w in 𝓝 z₀, w ≠ 0 := isOpen_ne.mem_nhds hz₀
  have hh_ne : ∀ᶠ w in 𝓝 z₀, h w ≠ 0 :=
    hh.continuousAt.eventually_ne (hh0.symm ▸ hκ_ne)
  filter_upwards [nhdsWithin_le_nhds hne0, nhdsWithin_le_nhds hh_ne,
    self_mem_nhdsWithin] with w hw0 hhw hwz
  have hsub : w - z₀ ≠ 0 := sub_ne_zero.mpr hwz
  have hfw : f w = (w - z₀) * h w := by
    dsimp only [h]
    rw [dslope_of_ne _ hwz, slope_def_field, hf0, sub_zero, mul_div_cancel₀ _ hsub]
  have hdh : dslope h z₀ w = (h w - κ) / (w - z₀) := by
    rw [dslope_of_ne _ hwz, slope_def_field, hh0]
  rw [hψ w hw0, hfw]
  dsimp only [R]
  rw [hdh]
  field_simp [hsub, hhw, hw0]
  linear_combination -w * hκ2

private lemma waveEGFReg_pole_principalPart {ψ : ℂ → ℂ} {z₀ κ : ℂ} {R : ℂ → ℂ}
    (hR : AnalyticAt ℂ R z₀)
    (hdecomp : ∀ᶠ w in 𝓝[≠] z₀, ψ w = κ / (w - z₀) + R w)
    (P : Polynomial ℂ) (d : ℕ) :
    ∃ L : ℂ, Filter.Tendsto
      (fun z : ℂ => waveEGFReg ψ P d z -
        ∑ s ∈ Finset.Icc 1 d, (κ * P.coeff (s - 1) * ((s - 1).factorial : ℂ)) / (z - z₀) ^ s)
      (𝓝[≠] z₀) (𝓝 L) := by
  let Rsum : ℂ → ℂ := fun z => ∑ j ∈ Finset.range d, P.coeff j * (-1 : ℂ) ^ j * iteratedDeriv j R z
  have hRsum_ana : AnalyticAt ℂ Rsum z₀ := by
    refine Finset.analyticAt_fun_sum (Finset.range d) fun j _ => ?_
    exact analyticAt_const.mul (analyticAt_iteratedDeriv hR j)
  refine ⟨Rsum z₀, ?_⟩
  have hRsum_tend : Filter.Tendsto Rsum (𝓝[≠] z₀) (𝓝 (Rsum z₀)) :=
    hRsum_ana.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- Extract an open neighborhood `U` of `z₀` on which `ψ w = κ / (w - z₀) + R w` for `w ∈ U \ {z₀}`
  -- and `R` is analytic on `U`.
  rw [eventually_nhdsWithin_iff] at hdecomp
  obtain ⟨U₁, hU₁_sub, hU₁_open, hz₀_U₁⟩ := mem_nhds_iff.mp hdecomp
  obtain ⟨U₂, hU₂_sub, hU₂_open, hz₀_U₂⟩ := mem_nhds_iff.mp hR.eventually_analyticAt
  refine hRsum_tend.congr' ?_
  change ∀ᶠ z in 𝓝[≠] z₀, Rsum z =
    waveEGFReg ψ P d z -
      ∑ s ∈ Finset.Icc 1 d, (κ * P.coeff (s - 1) * ((s - 1).factorial : ℂ)) / (z - z₀) ^ s
  rw [eventually_nhdsWithin_iff]
  filter_upwards [(hU₁_open.inter hU₂_open).mem_nhds ⟨hz₀_U₁, hz₀_U₂⟩] with z hz hzz₀
  have hψ_loc : ψ =ᶠ[𝓝 z] fun w => κ * (w - z₀)⁻¹ + R w := by
    filter_upwards [((hU₁_open.inter hU₂_open).inter isOpen_ne).mem_nhds ⟨hz, hzz₀⟩] with w hw
    have h1 := hU₁_sub hw.1.1 hw.2
    rw [div_eq_mul_inv] at h1
    exact h1
  have hinv_ana : AnalyticAt ℂ (fun w : ℂ => κ * (w - z₀)⁻¹) z :=
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzz₀))
  have hRz_ana : AnalyticAt ℂ R z := hU₂_sub hz.2
  have hterm : ∀ j ∈ Finset.range d,
      P.coeff j * (-1 : ℂ) ^ j * iteratedDeriv j ψ z =
        (κ * P.coeff j * (j.factorial : ℂ)) / (z - z₀) ^ (j + 1) +
        P.coeff j * (-1 : ℂ) ^ j * iteratedDeriv j R z := by
    intro j _
    rw [hψ_loc.iteratedDeriv_eq j]
    have hadd : iteratedDeriv j (fun w => κ * (w - z₀)⁻¹ + R w) z =
        iteratedDeriv j (fun w => κ * (w - z₀)⁻¹) z + iteratedDeriv j R z :=
      iteratedDeriv_add (hinv_ana.contDiffAt.of_le le_top) (hRz_ana.contDiffAt.of_le le_top)
    rw [hadd, iteratedDeriv_const_mul_field, iteratedDeriv_inv_sub z₀ j z hzz₀]
    have hsq : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    calc P.coeff j * (-1 : ℂ) ^ j *
          (κ * ((-1 : ℂ) ^ j * (j.factorial : ℂ) / (z - z₀) ^ (j + 1)) + iteratedDeriv j R z)
        = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * (κ * P.coeff j * (j.factorial : ℂ) / (z - z₀) ^ (j + 1)) +
          P.coeff j * (-1 : ℂ) ^ j * iteratedDeriv j R z := by ring
      _ = (κ * P.coeff j * (j.factorial : ℂ)) / (z - z₀) ^ (j + 1) +
          P.coeff j * (-1 : ℂ) ^ j * iteratedDeriv j R z := by rw [hsq, one_mul]
  have hsum_Icc : ∑ s ∈ Finset.Icc 1 d,
        (κ * P.coeff (s - 1) * ((s - 1).factorial : ℂ)) / (z - z₀) ^ s =
      ∑ j ∈ Finset.range d, (κ * P.coeff j * (j.factorial : ℂ)) / (z - z₀) ^ (j + 1) := by
    refine Finset.sum_bij (fun s _ => s - 1) ?_ ?_ ?_ ?_
    · intro s hs; have := Finset.mem_Icc.mp hs; exact Finset.mem_range.mpr (by omega)
    · intro a ha b hb hab
      have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega
    · intro j hj; have := Finset.mem_range.mp hj
      exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro s hs
      have := Finset.mem_Icc.mp hs
      rw [show s - 1 + 1 = s by omega]
  dsimp only [waveEGFReg, Rsum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hsum_Icc]
  ring

/-- Universal Cauchy-estimate `ExpType` lemma for all derivatives `iteratedDeriv j ψ` along any
flanking ray `μ = e^{i σ}` with `1 / 2 ≤ |cos σ|`, whenever `ψ` is analytic off `i ℝ \ {0}` and
uniformly bounded on `{w | 1 / 2 ≤ |w.re| ∧ 1 ≤ ‖w‖}`. -/
private lemma expType_iteratedDeriv_flanking_ray {ψ : ℂ → ℂ} {M : ℝ} (_hM : 0 ≤ M)
    (hana : ∀ w : ℂ, (w = 0 ∨ ∀ k : ℤ, k ≠ 0 → w ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ)) →
      AnalyticAt ℂ ψ w)
    (hbd : ∀ w : ℂ, 1 / 2 ≤ |w.re| → 1 ≤ ‖w‖ → ‖ψ w‖ ≤ M)
    {σ : ℝ} (hcos : 1 / 2 < |Real.cos σ|) (j : ℕ) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (iteratedDeriv j ψ)) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I σ
  have hμ_re : μ.re = Real.cos σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re σ
  have hcos_ne : Real.cos σ ≠ 0 := fun h => by rw [h, abs_zero] at hcos; linarith
  have hray_ana : ∀ v : ℝ, AnalyticAt ℂ (iteratedDeriv j ψ) (μ * (v : ℂ)) := fun v => by
    refine analyticAt_iteratedDeriv (hana _ (Or.inr fun k hk0 heq => ?_)) j
    have hre : (μ * (v : ℂ)).re = Real.cos σ * v := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
    have hpole : (2 * (Real.pi : ℂ) * I * (k : ℂ)).re = 0 := by simp
    rw [heq, hpole] at hre
    have hv0 : v = 0 := (mul_eq_zero.mp hre.symm).resolve_left hcos_ne
    subst hv0
    simp only [Complex.ofReal_zero, mul_zero] at heq
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Int.cast_ne_zero.mpr hk0) heq.symm
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ (iteratedDeriv j ψ) v) (Icc 0 2) := by
    intro v _
    have hc : ContinuousAt (fun x : ℝ => μ * iteratedDeriv j ψ (μ * (x : ℂ))) v :=
      continuousAt_const.mul (ContinuousAt.comp (g := iteratedDeriv j ψ)
        (f := fun x : ℝ => μ * (x : ℂ)) (hray_ana v).continuousAt
        (continuousAt_const.mul Complex.continuous_ofReal.continuousAt))
    exact hc.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let C₁ : ℝ := (j.factorial : ℝ) * M / (1 / 2 : ℝ) ^ j
  let C : ℝ := max (max M₀ 0) (max C₁ 0)
  have hC : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 0, hC, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hv2 : v ≤ 2
  · exact (hM₀ v ⟨hv, hv2⟩).trans ((le_max_left M₀ 0).trans (le_max_left _ _))
  · push Not at hv2
    -- On `closedBall (μ * v) (1/2)`, every `w` has `|w.re| ≥ 1/2` and `‖w‖ ≥ 1`!
    have hball_props : ∀ w ∈ Metric.closedBall (μ * (v : ℂ)) (1 / 2),
        1 / 2 ≤ |w.re| ∧ 1 ≤ ‖w‖ := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have hre_diff : |(w - μ * (v : ℂ)).re| ≤ 1 / 2 :=
        (Complex.abs_re_le_norm _).trans hw
      have hre_muv : |(μ * (v : ℂ)).re| = |Real.cos σ| * v := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re,
          abs_mul, abs_of_pos (show (0 : ℝ) < v by linarith)]
      have hre_w : 1 / 2 ≤ |w.re| := by
        have htri := abs_sub_abs_le_abs_sub (μ * (v : ℂ)).re w.re
        rw [abs_sub_comm] at htri
        have hsub : (w - μ * (v : ℂ)).re = w.re - (μ * (v : ℂ)).re := rfl
        rw [← hsub] at htri
        have hmul : 1 < |Real.cos σ| * v := by nlinarith
        linarith
      have hnorm_muv : ‖μ * (v : ℂ)‖ = v := by
        rw [norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have hnorm_w : 1 ≤ ‖w‖ := by
        have htri := norm_sub_norm_le (μ * (v : ℂ)) w
        rw [norm_sub_rev, hnorm_muv] at htri
        linarith
      exact ⟨hre_w, hnorm_w⟩
    have hdiff : DiffContOnCl ℂ ψ (Metric.ball (μ * (v : ℂ)) (1 / 2)) := by
      have hana_cl : ∀ w ∈ Metric.closedBall (μ * (v : ℂ)) (1 / 2), AnalyticAt ℂ ψ w := by
        intro w hw
        have hre_ge := (hball_props w hw).1
        refine hana w (Or.inr fun k _ heq => ?_)
        have hre0 : w.re = 0 := by rw [heq]; simp
        rw [hre0, abs_zero] at hre_ge; linarith
      refine ⟨fun w hw => (hana_cl w (Metric.ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt,
        fun w hw => (hana_cl w (Metric.closure_ball_subset_closedBall hw)).continuousAt.continuousWithinAt⟩
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j
      (by norm_num : (0 : ℝ) < 1 / 2) hdiff fun w hw => by
        have hprops := hball_props w (Metric.sphere_subset_closedBall hw)
        exact hbd w hprops.1 hprops.2
    rw [Minor.pull, norm_mul, hμ_norm, one_mul]
    exact hcauchy.trans ((le_max_left C₁ 0).trans (le_max_right _ _))

private lemma expType_zero : ExpType (fun _ : ℝ => (0 : ℂ)) :=
  ⟨0, 0, le_rfl, le_rfl, fun _ _ => by simp⟩

private lemma expType_const_mul {f : ℝ → ℂ} (c : ℂ) (hf : ExpType f) :
    ExpType (fun v => c * f v) := by
  obtain ⟨C, D, hC, hD, hbd⟩ := hf
  refine ⟨‖c‖ * C, D, mul_nonneg (norm_nonneg c) hC, hD, fun v hv => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbd v hv) (norm_nonneg c)

private lemma expType_add {f g : ℝ → ℂ} (hf : ExpType f) (hg : ExpType g) :
    ExpType (fun v => f v + g v) := by
  obtain ⟨Cf, Df, hCf, hDf, hbdf⟩ := hf
  obtain ⟨Cg, Dg, hCg, hDg, hbdg⟩ := hg
  refine ⟨Cf + Cg, max Df Dg, add_nonneg hCf hCg, le_trans hDf (le_max_left _ _), fun v hv => ?_⟩
  have he1 : Real.exp (Df * v) ≤ Real.exp (max Df Dg * v) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
  have he2 : Real.exp (Dg * v) ≤ Real.exp (max Df Dg * v) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hv)
  calc ‖f v + g v‖ ≤ ‖f v‖ + ‖g v‖ := norm_add_le _ _
    _ ≤ Cf * Real.exp (Df * v) + Cg * Real.exp (Dg * v) := add_le_add (hbdf v hv) (hbdg v hv)
    _ ≤ Cf * Real.exp (max Df Dg * v) + Cg * Real.exp (max Df Dg * v) :=
        add_le_add (mul_le_mul_of_nonneg_left he1 hCf) (mul_le_mul_of_nonneg_left he2 hCg)
    _ = (Cf + Cg) * Real.exp (max Df Dg * v) := by ring

private lemma expType_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, ExpType (f i)) :
    ExpType (fun v => ∑ i ∈ s, f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expType_zero
  | @insert i s hi ih =>
    have h1 := hf i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have heq : (fun v => ∑ j ∈ insert i s, f j v) = fun v => f i v + ∑ j ∈ s, f j v := by
      funext v; rw [Finset.sum_insert hi]
    rw [heq]
    exact expType_add h1 h2

private lemma expType_waveEGFReg {ψ : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hana : ∀ w : ℂ, (w = 0 ∨ ∀ k : ℤ, k ≠ 0 → w ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ)) →
      AnalyticAt ℂ ψ w)
    (hbd : ∀ w : ℂ, 1 / 2 ≤ |w.re| → 1 ≤ ‖w‖ → ‖ψ w‖ ≤ M)
    {σ : ℝ} (hcos : 1 / 2 < |Real.cos σ|) (P : Polynomial ℂ) (d : ℕ) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (waveEGFReg ψ P d)) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have heq : Minor.pull μ (waveEGFReg ψ P d) =
      fun v => ∑ j ∈ Finset.range d,
        (P.coeff j * (-1 : ℂ) ^ j) * Minor.pull μ (iteratedDeriv j ψ) v := by
    funext v
    simp only [Minor.pull, waveEGFReg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  exact expType_finset_sum (Finset.range d) _ fun j _ =>
    expType_const_mul _ (expType_iteratedDeriv_flanking_ray hM hana hbd hcos j)

private lemma abs_cos_pi_div_two_add_pi_div_four :
    (1 / 2 : ℝ) < |Real.cos (Real.pi / 2 + Real.pi / 4)| := by
  rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub,
    abs_neg, Real.sin_pi_div_four, abs_of_pos (by positivity)]
  have h1 : (1 : ℝ) < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
  linarith

private lemma abs_cos_pi_div_two_sub_pi_div_four :
    (1 / 2 : ℝ) < |Real.cos (Real.pi / 2 - Real.pi / 4)| := by
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_four, abs_of_pos (by positivity)]
  have h1 : (1 : ℝ) < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
  linarith

private lemma psi0Reg_strip_bound {w : ℂ} (hre : 1 / 2 ≤ |w.re|) (hnorm : 1 ≤ ‖w‖) :
    ‖psi0Reg w‖ ≤ (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ + 1 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
  rw [psi0Reg_eq_of_ne_zero hw0]
  have hδ_pos : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by
    linarith [Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)]
  have hden : 1 - Real.exp (-(1 / 2 : ℝ)) ≤ ‖Complex.exp w - 1‖ := by
    rcases le_or_gt 0 w.re with hpos | hneg
    · have hge : (1 / 2 : ℝ) ≤ w.re := by rwa [abs_of_nonneg hpos] at hre
      have hexp_ge : Real.exp (1 / 2 : ℝ) ≤ ‖Complex.exp w‖ := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hge
      have htri := norm_sub_norm_le (Complex.exp w) (1 : ℂ)
      rw [norm_one] at htri
      have hcomp : 1 - Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (1 / 2 : ℝ) - 1 := by
        have hp : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
        rw [Real.exp_neg]
        have hsq : (Real.exp (1 / 2 : ℝ) - 1) - (1 - (Real.exp (1 / 2 : ℝ))⁻¹) =
            (Real.exp (1 / 2 : ℝ) - 1) ^ 2 / Real.exp (1 / 2 : ℝ) := by
          field_simp [hp.ne']
        linarith [div_nonneg (sq_nonneg (Real.exp (1 / 2 : ℝ) - 1)) hp.le]
      linarith
    · have hle : w.re ≤ -(1 / 2 : ℝ) := by rw [abs_of_neg hneg] at hre; linarith
      have hexp_le : ‖Complex.exp w‖ ≤ Real.exp (-(1 / 2 : ℝ)) := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hle
      have htri := norm_sub_norm_le (1 : ℂ) (Complex.exp w)
      rw [norm_one, norm_sub_rev] at htri
      linarith
  calc ‖(Complex.exp w - 1)⁻¹ - w⁻¹‖
      ≤ ‖(Complex.exp w - 1)⁻¹‖ + ‖w⁻¹‖ := norm_sub_le _ _
    _ = ‖Complex.exp w - 1‖⁻¹ + ‖w‖⁻¹ := by rw [norm_inv, norm_inv]
    _ ≤ (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ + 1 :=
        add_le_add (inv_anti₀ hδ_pos hden) (by simpa using inv_anti₀ zero_lt_one hnorm)

private lemma psiHalfReg_strip_bound {w : ℂ} (hre : 1 / 2 ≤ |w.re|) (hnorm : 1 ≤ ‖w‖) :
    ‖psiHalfReg w‖ ≤ (Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)))⁻¹ + 1 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
  rw [psiHalfReg_eq_of_ne_zero hw0]
  have hδ_pos : 0 < Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)) := by
    linarith [Real.exp_lt_exp.mpr (by norm_num : -(1 / 4 : ℝ) < 1 / 4)]
  have h2sinh : 2 * Complex.sinh (w / 2) = Complex.exp (w / 2) - Complex.exp (-(w / 2)) := by
    rw [Complex.sinh]; ring
  have hw2_re : (w / 2).re = w.re / 2 := by simp
  have h1 : ‖Complex.exp (w / 2)‖ = Real.exp (w.re / 2) := by
    rw [Complex.norm_exp, hw2_re]
  have h2 : ‖Complex.exp (-(w / 2))‖ = Real.exp (-(w.re / 2)) := by
    rw [Complex.norm_exp, Complex.neg_re, hw2_re]
  have hden : Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)) ≤ ‖2 * Complex.sinh (w / 2)‖ := by
    rw [h2sinh]
    rcases le_or_gt 0 w.re with hpos | hneg
    · have hge : (1 / 4 : ℝ) ≤ w.re / 2 := by rw [abs_of_nonneg hpos] at hre; linarith
      have htri := norm_sub_norm_le (Complex.exp (w / 2)) (Complex.exp (-(w / 2)))
      rw [h1, h2] at htri
      have ha : Real.exp (1 / 4 : ℝ) ≤ Real.exp (w.re / 2) := Real.exp_le_exp.mpr hge
      have hb : Real.exp (-(w.re / 2)) ≤ Real.exp (-(1 / 4 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      linarith
    · have hle : w.re / 2 ≤ -(1 / 4 : ℝ) := by rw [abs_of_neg hneg] at hre; linarith
      have htri := norm_sub_norm_le (Complex.exp (-(w / 2))) (Complex.exp (w / 2))
      rw [norm_sub_rev, h1, h2] at htri
      have ha : Real.exp (1 / 4 : ℝ) ≤ Real.exp (-(w.re / 2)) := Real.exp_le_exp.mpr (by linarith)
      have hb : Real.exp (w.re / 2) ≤ Real.exp (-(1 / 4 : ℝ)) := Real.exp_le_exp.mpr hle
      linarith
  calc ‖(2 * Complex.sinh (w / 2))⁻¹ - w⁻¹‖
      ≤ ‖(2 * Complex.sinh (w / 2))⁻¹‖ + ‖w⁻¹‖ := norm_sub_le _ _
    _ = ‖2 * Complex.sinh (w / 2)‖⁻¹ + ‖w‖⁻¹ := by rw [norm_inv, norm_inv]
    _ ≤ (Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)))⁻¹ + 1 :=
        add_le_add (inv_anti₀ hδ_pos hden) (by simpa using inv_anti₀ zero_lt_one hnorm)

/-- **General Integer-Lattice Wave-EGF `HigherOrderBorelData` Constructor (`θ₀ = π / 2`)**:
For any polynomial `P` of degree `d - 1` (`1 ≤ d`, `P.coeff (d - 1) ≠ 0`), `waveEGFReg psi0Reg P d`
satisfies `HigherOrderBorelData` along `θ₀ = π / 2` with poles at `2π i (m + 1)` of exact order `d`
and explicit principal-part coefficients `P.coeff (s - 1) * (s - 1)!`. -/
def waveEGFReg_psi0_borelData (P : Polynomial ℂ) (d : ℕ) (hd : 1 ≤ d)
    (hlead : P.coeff (d - 1) ≠ 0) :
    HigherOrderBorelData (waveEGFReg psi0Reg P d) (Real.pi / 2) crossWavePole (fun _ => d)
      (fun _ s => P.coeff (s - 1) * ((s - 1).factorial : ℂ)) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := Real.pi
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := Real.pi_pos
  ω_pos := crossWavePole_pos
  ω_mono := crossWavePole_mono
  ord_pos := fun _ => hd
  pp_lead_ne_zero := fun _ =>
    mul_ne_zero hlead (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  analyticOn := fun z hz => by
    have hnot := not_pole_of_mem_crossWedge hz
    refine Finset.analyticAt_fun_sum (Finset.range d) fun j _ => ?_
    exact analyticAt_const.mul (analyticAt_iteratedDeriv (psi0Reg_analyticAt (Or.inr hnot)) j)
  pole_principalPart := fun m => by
    let z_m : ℂ := Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ)) * (crossWavePole m : ℂ)
    have hz_eq : z_m = ((m + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      dsimp only [z_m, crossWavePole]; rw [exp_I_pi_div_two]; push_cast; ring
    have hz_ne : z_m ≠ 0 := by
      rw [hz_eq]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
        (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero)
    have hf0 : Complex.exp z_m - 1 = 0 := by
      rw [hz_eq, Complex.exp_nat_mul_two_pi_mul_I, sub_self]
    have hf' : deriv (fun w : ℂ => Complex.exp w - 1) z_m = 1 := by
      rw [show (fun w : ℂ => Complex.exp w - 1) = fun w => Complex.exp w - (1 : ℂ) from rfl]
      have hd1 : HasDerivAt (fun w : ℂ => Complex.exp w - 1) (Complex.exp z_m) z_m := by
        simpa using (Complex.hasDerivAt_exp z_m).sub_const (1 : ℂ)
      rw [hd1.deriv, hz_eq, Complex.exp_nat_mul_two_pi_mul_I]
    obtain ⟨R, hR, hdecomp⟩ := simple_pole_decomp hz_ne
      (analyticAt_cexp.sub analyticAt_const) hf0 hf' (one_pow 2)
      (fun w hw => psi0Reg_eq_of_ne_zero hw)
    simpa only [one_mul] using waveEGFReg_pole_principalPart hR hdecomp P d
  expType_plus := by
    have hM : 0 ≤ (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ + 1 := by
      have : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by
        linarith [Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)]
      positivity
    exact expType_waveEGFReg hM (fun _ h => psi0Reg_analyticAt h) (fun _ h1 h2 => psi0Reg_strip_bound h1 h2)
      abs_cos_pi_div_two_add_pi_div_four P d
  expType_minus := by
    have hM : 0 ≤ (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ + 1 := by
      have : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by
        linarith [Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)]
      positivity
    exact expType_waveEGFReg hM (fun _ h => psi0Reg_analyticAt h) (fun _ h1 h2 => psi0Reg_strip_bound h1 h2)
      abs_cos_pi_div_two_sub_pi_div_four P d

/-- **General Half-Integer-Lattice Wave-EGF `HigherOrderBorelData` Constructor (`θ₀ = π / 2`)**:
For any polynomial `P` of degree `d - 1` (`1 ≤ d`, `P.coeff (d - 1) ≠ 0`), `waveEGFReg psiHalfReg P d`
satisfies `HigherOrderBorelData` along `θ₀ = π / 2` with poles at `2π i (m + 1)` of exact order `d`
and explicit principal-part coefficients `(-1)^(m + 1) * P.coeff (s - 1) * (s - 1)!`. -/
def waveEGFReg_psiHalf_borelData (P : Polynomial ℂ) (d : ℕ) (hd : 1 ≤ d)
    (hlead : P.coeff (d - 1) ≠ 0) :
    HigherOrderBorelData (waveEGFReg psiHalfReg P d) (Real.pi / 2) crossWavePole (fun _ => d)
      (fun m s => (-1 : ℂ) ^ (m + 1) * P.coeff (s - 1) * ((s - 1).factorial : ℂ)) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := Real.pi
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := Real.pi_pos
  ω_pos := crossWavePole_pos
  ω_mono := crossWavePole_mono
  ord_pos := fun _ => hd
  pp_lead_ne_zero := fun m =>
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hlead)
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  analyticOn := fun z hz => by
    have hnot := not_pole_of_mem_crossWedge hz
    refine Finset.analyticAt_fun_sum (Finset.range d) fun j _ => ?_
    exact analyticAt_const.mul (analyticAt_iteratedDeriv (psiHalfReg_analyticAt (Or.inr hnot)) j)
  pole_principalPart := fun m => by
    let z_m : ℂ := Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ)) * (crossWavePole m : ℂ)
    have hz_eq : z_m = 2 * (Real.pi : ℂ) * I * ((m + 1 : ℕ) : ℂ) := by
      dsimp only [z_m, crossWavePole]; rw [exp_I_pi_div_two]; push_cast; ring
    have hz_ne : z_m ≠ 0 := by
      rw [hz_eq]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
    have hf0 : 2 * Complex.sinh (z_m / 2) = 0 :=
      (two_sinh_half_eq_zero_iff z_m).mpr ⟨(m + 1 : ℕ), by simpa using hz_eq⟩
    have hf' : deriv (fun w : ℂ => 2 * Complex.sinh (w / 2)) z_m = (-1 : ℂ) ^ (m + 1) := by
      rw [(hasDerivAt_two_sinh_half z_m).deriv, hz_eq]
      have harg : 2 * (Real.pi : ℂ) * I * ((m + 1 : ℕ) : ℂ) / 2 =
          ((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * I) := by ring
      rw [harg, Complex.cosh]
      have hexp1 : Complex.exp (((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * I)) = (-1 : ℂ) ^ (m + 1) := by
        rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      have hexp2 : Complex.exp (-(((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * I))) = (-1 : ℂ) ^ (m + 1) := by
        rw [Complex.exp_neg, hexp1, ← inv_pow]; norm_num
      rw [hexp1, hexp2]; ring
    have hκ2 : ((-1 : ℂ) ^ (m + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm (m + 1) 2, pow_mul]; norm_num
    have hent : Differentiable ℂ (fun w : ℂ => 2 * Complex.sinh (w / 2)) := fun w =>
      (hasDerivAt_two_sinh_half w).differentiableAt
    obtain ⟨R, hR, hdecomp⟩ := simple_pole_decomp hz_ne (hent.analyticAt z_m) hf0 hf' hκ2
      (fun w hw => psiHalfReg_eq_of_ne_zero hw)
    exact waveEGFReg_pole_principalPart hR hdecomp P d
  expType_plus := by
    have hM : 0 ≤ (Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)))⁻¹ + 1 := by
      have : 0 < Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)) := by
        linarith [Real.exp_lt_exp.mpr (by norm_num : -(1 / 4 : ℝ) < 1 / 4)]
      positivity
    exact expType_waveEGFReg hM (fun _ h => psiHalfReg_analyticAt h) (fun _ h1 h2 => psiHalfReg_strip_bound h1 h2)
      abs_cos_pi_div_two_add_pi_div_four P d
  expType_minus := by
    have hM : 0 ≤ (Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)))⁻¹ + 1 := by
      have : 0 < Real.exp (1 / 4 : ℝ) - Real.exp (-(1 / 4 : ℝ)) := by
        linarith [Real.exp_lt_exp.mpr (by norm_num : -(1 / 4 : ℝ) < 1 / 4)]
      positivity
    exact expType_waveEGFReg hM (fun _ h => psiHalfReg_analyticAt h) (fun _ h1 h2 => psiHalfReg_strip_bound h1 h2)
      abs_cos_pi_div_two_sub_pi_div_four P d

/-! #### B.3 Concrete Even-Dimensional CROSS Wave-EGFs & Strong `ℂ({t})` D-Transcendence -/

/-- Regularized wave EGF `W_{ℂℙⁿ}^{reg}(y)` (`n ≥ 1`): uses `psi0Reg` for even `n` (`ρ ∈ ℤ`)
and `psiHalfReg` for odd `n` (`ρ ∈ ℤ + 1/2`). -/
@[expose] def cpnWaveEGFReg (n : ℕ) (y : ℂ) : ℂ :=
  if Even n then waveEGFReg psi0Reg (cpnMultPoly n) (2 * n) y
  else waveEGFReg psiHalfReg (cpnMultPoly n) (2 * n) y

/-- Regularized wave EGF `W_{ℍℙⁿ}^{reg}(y)` (`n ≥ 1`, `ρ = n + 1/2`). -/
@[expose] def hpnWaveEGFReg (n : ℕ) (y : ℂ) : ℂ :=
  waveEGFReg psiHalfReg (hpnMultPoly n) (4 * n) y

/-- Regularized wave EGF `W_{𝕆ℙ²}^{reg}(y)` (`dim = 16`, `ρ = 11/2`). -/
@[expose] def op2WaveEGFReg (y : ℂ) : ℂ :=
  waveEGFReg psiHalfReg op2MultPoly 16 y

/-- Regularized wave EGF `W_{S^{2r}}^{reg}(y)` (`r ≥ 1`, `ρ = r - 1/2`). -/
@[expose] def evenSphereWaveEGFReg (r : ℕ) (y : ℂ) : ℂ :=
  waveEGFReg psiHalfReg (sphereMultPoly (2 * r)) (2 * r) y

private lemma cpnMultPoly_lead_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    (cpnMultPoly n).coeff (2 * n - 1) ≠ 0 := by
  intro h0
  have h := cpn_leading_pole_coeff n hn
  rw [h0, zero_mul] at h
  have hpos : 0 < Nat.choose (2 * n) n := Nat.choose_pos (by omega)
  exact (Nat.cast_ne_zero.mpr hpos.ne') h.symm

private lemma hpnMultPoly_lead_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    (hpnMultPoly n).coeff (4 * n - 1) ≠ 0 := by
  intro h0
  have h := hpn_leading_pole_coeff_catalan n hn
  rw [h0, zero_mul] at h
  have hpos : 0 < catalan (2 * n) := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom, show 2 * (2 * n) = 4 * n by omega]
    exact Nat.div_pos (by
      have hle : 2 * n + 1 ≤ Nat.choose (4 * n) (2 * n) := by
        have h1 := Nat.choose_le_choose (2 * n) (show 2 * n + 1 ≤ 4 * n by omega)
        -- Actually `Nat.succ_dvd_centralBinom` + `centralBinom > 0` immediately gives `≤`!
        exact Nat.le_of_dvd (Nat.choose_pos (by omega))
          (by simpa [Nat.centralBinom, show 2 * (2 * n) = 4 * n by omega] using
            Nat.succ_dvd_centralBinom (2 * n))
      exact hle) (by omega)
  exact (Nat.cast_ne_zero.mpr hpos.ne') h.symm

private lemma op2MultPoly_lead_ne_zero : op2MultPoly.coeff 15 ≠ 0 := by
  intro h0
  have h := op2_leading_pole_coeff
  rw [h0, zero_mul] at h
  norm_num at h

private lemma evenSphereMultPoly_lead_ne_zero {r : ℕ} (hr : 1 ≤ r) :
    (sphereMultPoly (2 * r)).coeff (2 * r - 1) ≠ 0 := by
  intro h0
  have h := evenSphere_leading_pole_coeff r hr
  rw [h0, zero_mul] at h
  norm_num at h

/-- Genuine `HigherOrderBorelData` witness along `θ₀ = π / 2` for `W_{ℂℙⁿ}^{reg}(y)` (`n ≥ 1`)
with poles of exact order `2n` at `2π i (m + 1)` and exact leading principal part
`(-1)^((m + 1) * n) * Nat.choose (2 * n) n ≠ 0`. -/
def cpnWaveEGFReg_borelData (n : ℕ) (hn : 1 ≤ n) :
    HigherOrderBorelData (cpnWaveEGFReg n) (Real.pi / 2) crossWavePole (fun _ => 2 * n)
      (fun m s => (-1 : ℂ) ^ ((m + 1) * n) * (cpnMultPoly n).coeff (s - 1) *
        ((s - 1).factorial : ℂ)) := by
  by_cases hev : Even n
  · have hfn : cpnWaveEGFReg n = waveEGFReg psi0Reg (cpnMultPoly n) (2 * n) := by
      ext y; simp [cpnWaveEGFReg, hev]
    have hpp : (fun m s => (-1 : ℂ) ^ ((m + 1) * n) * (cpnMultPoly n).coeff (s - 1) *
        ((s - 1).factorial : ℂ)) =
        fun _ s => (cpnMultPoly n).coeff (s - 1) * ((s - 1).factorial : ℂ) := by
      funext m s
      have hev' : Even ((m + 1) * n) := Even.mul_left hev (m + 1)
      rw [hev'.neg_one_pow, one_mul]
    rw [hfn, hpp]
    exact waveEGFReg_psi0_borelData (cpnMultPoly n) (2 * n) (by omega) (cpnMultPoly_lead_ne_zero hn)
  · have hodd : Odd n := Nat.not_even_iff_odd.mp hev
    have hfn : cpnWaveEGFReg n = waveEGFReg psiHalfReg (cpnMultPoly n) (2 * n) := by
      ext y; simp [cpnWaveEGFReg, hev]
    have hpp : (fun m s => (-1 : ℂ) ^ ((m + 1) * n) * (cpnMultPoly n).coeff (s - 1) *
        ((s - 1).factorial : ℂ)) =
        fun m s => (-1 : ℂ) ^ (m + 1) * (cpnMultPoly n).coeff (s - 1) * ((s - 1).factorial : ℂ) := by
      funext m s
      have hpow : (-1 : ℂ) ^ ((m + 1) * n) = (-1 : ℂ) ^ (m + 1) := by
        rw [mul_comm, pow_mul, hodd.neg_one_pow]
      rw [hpow]
    rw [hfn, hpp]
    exact waveEGFReg_psiHalf_borelData (cpnMultPoly n) (2 * n) (by omega) (cpnMultPoly_lead_ne_zero hn)

/-- Genuine `HigherOrderBorelData` witness along `θ₀ = π / 2` for `W_{ℍℙⁿ}^{reg}(y)` (`n ≥ 1`)
with poles of exact order `4n` at `2π i (m + 1)` and exact leading principal part
`(-1)^(m + 1) * C_{2n} ≠ 0`. -/
def hpnWaveEGFReg_borelData (n : ℕ) (hn : 1 ≤ n) :
    HigherOrderBorelData (hpnWaveEGFReg n) (Real.pi / 2) crossWavePole (fun _ => 4 * n)
      (fun m s => (-1 : ℂ) ^ (m + 1) * (hpnMultPoly n).coeff (s - 1) * ((s - 1).factorial : ℂ)) :=
  waveEGFReg_psiHalf_borelData (hpnMultPoly n) (4 * n) (by omega) (hpnMultPoly_lead_ne_zero hn)

/-- Genuine `HigherOrderBorelData` witness along `θ₀ = π / 2` for `W_{𝕆ℙ²}^{reg}(y)`
with poles of exact order `16` at `2π i (m + 1)` and exact leading principal part
`(-1)^(m + 1) * 78 ≠ 0`. -/
def op2WaveEGFReg_borelData :
    HigherOrderBorelData op2WaveEGFReg (Real.pi / 2) crossWavePole (fun _ => 16)
      (fun m s => (-1 : ℂ) ^ (m + 1) * op2MultPoly.coeff (s - 1) * ((s - 1).factorial : ℂ)) :=
  waveEGFReg_psiHalf_borelData op2MultPoly 16 (by omega) op2MultPoly_lead_ne_zero

/-- Genuine `HigherOrderBorelData` witness along `θ₀ = π / 2` for `W_{S^{2r}}^{reg}(y)` (`r ≥ 1`)
with poles of exact order `2r` at `2π i (m + 1)` and exact leading principal part
`(-1)^(m + 1) * 2 ≠ 0`. -/
def evenSphereWaveEGFReg_borelData (r : ℕ) (hr : 1 ≤ r) :
    HigherOrderBorelData (evenSphereWaveEGFReg r) (Real.pi / 2) crossWavePole (fun _ => 2 * r)
      (fun m s => (-1 : ℂ) ^ (m + 1) * (sphereMultPoly (2 * r)).coeff (s - 1) *
        ((s - 1).factorial : ℂ)) :=
  waveEGFReg_psiHalf_borelData (sphereMultPoly (2 * r)) (2 * r) (by omega)
    (evenSphereMultPoly_lead_ne_zero hr)

/-- **Unconditional Strong `ℂ({t})` Wave-EGF D-Transcendence for ALL `ℂℙⁿ` (`n ≥ 1`)**:
`ogfOfEGF (cpnWaveEGFReg n)` is strongly differentially transcendental over convergent
meromorphic germs `ℂ({t})`. -/
theorem cpn_waveEGF_ogf_stronglyDTrans (n : ℕ) (hn : 1 ≤ n) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (cpnWaveEGFReg n)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (cpnWaveEGFReg_borelData n hn)

/-- **Unconditional Strong `ℂ({t})` Wave-EGF D-Transcendence for ALL `ℍℙⁿ` (`n ≥ 1`)**:
`ogfOfEGF (hpnWaveEGFReg n)` is strongly differentially transcendental over convergent
meromorphic germs `ℂ({t})`. -/
theorem hpn_waveEGF_ogf_stronglyDTrans (n : ℕ) (hn : 1 ≤ n) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (hpnWaveEGFReg n)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (hpnWaveEGFReg_borelData n hn)

/-- **Unconditional Strong `ℂ({t})` Wave-EGF D-Transcendence for `𝕆ℙ² = F₄ / Spin(9)`**:
`ogfOfEGF op2WaveEGFReg` is strongly differentially transcendental over convergent
meromorphic germs `ℂ({t})`. -/
theorem op2_waveEGF_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF op2WaveEGFReg) :=
  ogf_stronglyDTrans_of_higherOrderBorel op2WaveEGFReg_borelData

/-- **Unconditional Strong `ℂ({t})` Wave-EGF D-Transcendence for ALL Even Spheres `S^{2r}` (`r ≥ 1`)**:
`ogfOfEGF (evenSphereWaveEGFReg r)` is strongly differentially transcendental over convergent
meromorphic germs `ℂ({t})`. -/
theorem evenSphere_waveEGF_ogf_stronglyDTrans (r : ℕ) (hr : 1 ≤ r) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (evenSphereWaveEGFReg r)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (evenSphereWaveEGFReg_borelData r hr)

/-! ### Part C: Poincaré Homology Sphere `S³ / I*` & ADE Spherical 3-Manifold Even-Parity Theorem -/

/-! #### C.1 General Palindromic Gorenstein Molien Quasipolynomial Engine -/

/-- Palindromicity of a polynomial `P` at degree `d`: `P.coeff j = 0` for `j > d` and
`P.coeff (d - j) = P.coeff j` for all `j ≤ d`. -/
@[expose] def IsPalindromic (d : ℕ) (P : Polynomial ℂ) : Prop :=
  (∀ j : ℕ, d < j → P.coeff j = 0) ∧ (∀ j : ℕ, j ≤ d → P.coeff (d - j) = P.coeff j)

private lemma isPalindromic_mul {d₁ d₂ : ℕ} {P Q : Polynomial ℂ}
    (hP : IsPalindromic d₁ P) (hQ : IsPalindromic d₂ Q) :
    IsPalindromic (d₁ + d₂) (P * Q) := by
  have hcoeff_rect : ∀ n : ℕ, (P * Q).coeff n =
      ∑ ab ∈ Finset.range (d₁ + 1) ×ˢ Finset.range (d₂ + 1),
        if ab.1 + ab.2 = n then P.coeff ab.1 * Q.coeff ab.2 else 0 := fun n => by
    rw [Polynomial.coeff_mul]
    let R := (Finset.range (d₁ + 1) ×ˢ Finset.range (d₂ + 1)).filter (fun ab => ab.1 + ab.2 = n)
    rw [← Finset.sum_filter]
    have hsub : R ⊆ Finset.HasAntidiagonal.antidiagonal n := fun ab hab => by
      simpa using (Finset.mem_filter.mp hab).2
    symm
    refine Finset.sum_subset hsub fun ab hab hnot => ?_
    have hsum : ab.1 + ab.2 = n := by simpa using hab
    by_cases h1 : d₁ < ab.1
    · rw [hP.1 ab.1 h1, zero_mul]
    · by_cases h2 : d₂ < ab.2
      · rw [hQ.1 ab.2 h2, mul_zero]
      · exfalso
        apply hnot
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, hsum⟩
  constructor
  · intro j hj
    rw [hcoeff_rect j]
    refine Finset.sum_eq_zero fun ab hab => ?_
    have h1 := Finset.mem_range.mp (Finset.mem_product.mp hab).1
    have h2 := Finset.mem_range.mp (Finset.mem_product.mp hab).2
    have hne : ab.1 + ab.2 ≠ j := by omega
    simp [hne]
  · intro j hj
    rw [hcoeff_rect (d₁ + d₂ - j), hcoeff_rect j]
    refine Finset.sum_bij (fun ab _ => (d₁ - ab.1, d₂ - ab.2)) ?_ ?_ ?_ ?_
    · intro ab hab
      have h1 := Finset.mem_range.mp (Finset.mem_product.mp hab).1
      have h2 := Finset.mem_range.mp (Finset.mem_product.mp hab).2
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    · intro a ha b hb hab
      have ha1 := Finset.mem_range.mp (Finset.mem_product.mp ha).1
      have ha2 := Finset.mem_range.mp (Finset.mem_product.mp ha).2
      have hb1 := Finset.mem_range.mp (Finset.mem_product.mp hb).1
      have hb2 := Finset.mem_range.mp (Finset.mem_product.mp hb).2
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (by omega) (by omega)
    · intro ab hab
      have h1 := Finset.mem_range.mp (Finset.mem_product.mp hab).1
      have h2 := Finset.mem_range.mp (Finset.mem_product.mp hab).2
      refine ⟨(d₁ - ab.1, d₂ - ab.2), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_⟩
      exact Prod.ext (by omega) (by omega)
    · intro ab hab
      have h1 : ab.1 ≤ d₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hab).1)
      have h2 : ab.2 ≤ d₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hab).2)
      have hiff : ab.1 + ab.2 = d₁ + d₂ - j ↔ (d₁ - ab.1) + (d₂ - ab.2) = j := by omega
      by_cases h : ab.1 + ab.2 = d₁ + d₂ - j
      · rw [ite_eq_left_iff.mpr (fun hn => (hn h).elim),
          ite_eq_left_iff.mpr (fun hn => (hn (hiff.mp h)).elim),
          hP.2 ab.1 h1, hQ.2 ab.2 h2]
      · rw [ite_eq_right_iff.mpr (fun h' => (h h').elim),
          ite_eq_right_iff.mpr (fun h' => (h (hiff.mpr h')).elim)]

/-- Geometric-sum polynomial `∑_{i=0}^{q-1} X^{i d} = (1 - X^{q d}) / (1 - X^d)`. -/
@[expose] def geomPoly (d q : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range q, Polynomial.X ^ (i * d)

private lemma coeff_geomPoly {d : ℕ} (hd : 0 < d) (q j : ℕ) :
    (geomPoly d q).coeff j = if d ∣ j ∧ j / d < q then 1 else 0 := by
  unfold geomPoly
  rw [poly_finset_sum_coeff]
  simp_rw [Polynomial.coeff_X_pow]
  by_cases h : d ∣ j ∧ j / d < q
  · rw [ite_eq_left_iff.mpr (fun hn => (hn h).elim)]
    rw [Finset.sum_eq_single (j / d)]
    · have hmul : j / d * d = j := Nat.div_mul_cancel h.1
      simp [hmul]
    · intro i _ hne
      have hne' : j ≠ i * d := fun heq => by
        apply hne; rw [heq, Nat.mul_div_cancel i hd]
      simp [hne']
    · intro hnot; exact absurd (Finset.mem_range.mpr h.2) hnot
  · rw [ite_eq_right_iff.mpr (fun h' => (h h').elim)]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_lt : i < q := Finset.mem_range.mp hi
    have hne : j ≠ i * d := fun heq => h ⟨⟨i, by rw [heq, mul_comm]⟩, by rw [heq, Nat.mul_div_cancel i hd]; exact hi_lt⟩
    simp [hne]

private lemma isPalindromic_geomPoly {d q : ℕ} (hd : 0 < d) (hq : 1 ≤ q) :
    IsPalindromic ((q - 1) * d) (geomPoly d q) := by
  constructor
  · intro j hj
    rw [coeff_geomPoly hd]
    have hnot : ¬ (d ∣ j ∧ j / d < q) := by
      rintro ⟨hdvd, hlt⟩
      have hmul : j / d * d = j := Nat.div_mul_cancel hdvd
      have hle : j / d ≤ q - 1 := by omega
      have : j / d * d ≤ (q - 1) * d := Nat.mul_le_mul_right d hle
      omega
    simp [hnot]
  · intro j hj
    rw [coeff_geomPoly hd, coeff_geomPoly hd]
    have hiff : (d ∣ (q - 1) * d - j ∧ ((q - 1) * d - j) / d < q) ↔ (d ∣ j ∧ j / d < q) := by
      constructor
      · rintro ⟨⟨a, ha⟩, hlt⟩
        have hle : j ≤ (q - 1) * d := hj
        have ha_le : a ≤ q - 1 := by
          by_contra hgt; push Not at hgt
          have : (q - 1) * d < d * a := by nlinarith
          omega
        have hsum_d : (q - 1 - a) * d + d * a = (q - 1) * d := by
          rw [mul_comm d a, ← Nat.add_mul, Nat.sub_add_cancel ha_le]
        have hmul : j = (q - 1 - a) * d := by omega
        refine ⟨⟨q - 1 - a, by rw [hmul, mul_comm]⟩, ?_⟩
        rw [hmul, Nat.mul_div_cancel _ hd]; omega
      · rintro ⟨⟨a, ha⟩, hlt⟩
        have ha_le : a ≤ q - 1 := by
          have : d * a ≤ (q - 1) * d := by rw [← ha]; exact hj
          nlinarith
        have hsum_d : (q - 1 - a) * d + d * a = (q - 1) * d := by
          rw [mul_comm d a, ← Nat.add_mul, Nat.sub_add_cancel ha_le]
        have hsub : (q - 1) * d - j = (q - 1 - a) * d := by omega
        refine ⟨⟨q - 1 - a, by rw [hsub, mul_comm]⟩, ?_⟩
        rw [hsub, Nat.mul_div_cancel _ hd]; omega
    by_cases hc : d ∣ j ∧ j / d < q
    · rw [ite_eq_left_iff.mpr (fun hn => (hn (hiff.mpr hc)).elim),
        ite_eq_left_iff.mpr (fun hn => (hn hc).elim)]
    · rw [ite_eq_right_iff.mpr (fun h => (hc (hiff.mp h)).elim),
        ite_eq_right_iff.mpr (fun h => (hc h).elim)]

private lemma one_sub_X_pow_mul_geomPoly (d q : ℕ) :
    (1 - Polynomial.X ^ d : Polynomial ℂ) * geomPoly d q = 1 - Polynomial.X ^ (q * d) := by
  unfold geomPoly
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, ← pow_add,
      show d + q * d = (q + 1) * d by ring]
    ring

private lemma isPalindromic_one_add_X_pow (d : ℕ) :
    IsPalindromic d (1 + Polynomial.X ^ d : Polynomial ℂ) := by
  constructor
  · intro j hj
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow]
    have h0 : j ≠ 0 := by omega
    have hd : j ≠ d := by omega
    simp [h0, hd]
  · intro j hj
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_one,
      Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
    by_cases h0 : j = 0
    · subst h0
      by_cases hd0 : d = 0
      · subst hd0; simp
      · simp [hd0, Ne.symm hd0]
    · by_cases hd : j = d
      · subst hd
        simp [h0, Ne.symm h0]
      · have h1 : d - j ≠ 0 := by omega
        have h2 : d - j ≠ d := by omega
        simp [h0, hd, h1, h2]

/-- Slope coefficient `α(r)` of the period-`M` Molien quasipolynomial derived from numerator `A`
of `A(t) / (1 - t^M)²`. -/
@[expose] def adeAlpha (M : ℕ) (A : Polynomial ℂ) (r : ℕ) : ℂ :=
  if r % M = 0 then A.coeff (M - 1) / (M : ℂ)
  else (A.coeff (r % M - 1) + A.coeff (r % M - 1 + M)) / (M : ℂ)

/-- Intercept coefficient `β(r)` of the period-`M` Molien quasipolynomial `c(u - 1) = α(u) u + β(u)`. -/
@[expose] def adeBeta (M : ℕ) (A : Polynomial ℂ) (r : ℕ) : ℂ :=
  if r % M = 0 then 0
  else A.coeff (r % M - 1) - ((r % M : ℕ) : ℂ) / (M : ℂ) *
    (A.coeff (r % M - 1) + A.coeff (r % M - 1 + M))

/-- Period-`M` quasipolynomial encoding `m_{S³/Γ}(u) = u · c_Γ(u - 1) = α(u) u² + β(u) u`
from any Gorenstein palindromic numerator `A` of `∑ c_Γ(k) t^k = A(t) / (1 - t^M)²`. -/
@[expose] def adeSphere3QP (M : ℕ) (hM : 0 < M) (A : Polynomial ℂ) : Quasipoly where
  M := M
  hM := hM
  «D» := 2
  c d n := if d.1 = 2 then adeAlpha M A n else if d.1 = 1 then adeBeta M A n else 0
  periodic d n := by
    simp only [adeAlpha, adeBeta, Nat.add_mod_right]

/-- Exact Molien series coefficient `c(k) = α(k + 1) (k + 1) + β(k + 1)`. -/
@[expose] def adeMolienCoeff (M : ℕ) (A : Polynomial ℂ) (k : ℕ) : ℂ :=
  adeAlpha M A (k + 1) * ((k + 1 : ℕ) : ℂ) + adeBeta M A (k + 1)

/-- Formal Molien power series `∑_{k ≥ 0} c(k) X^k`. -/
@[expose] def adeMolienSeries (M : ℕ) (A : Polynomial ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (adeMolienCoeff M A)

lemma adeSphere3QP_eval (M : ℕ) (hM : 0 < M) (A : Polynomial ℂ) (u : ℤ) :
    (adeSphere3QP M hM A).eval u =
      adeAlpha M A ((u % (M : ℤ)).toNat) * (u : ℂ) ^ 2 +
        adeBeta M A ((u % (M : ℤ)).toNat) * (u : ℂ) := by
  unfold Quasipoly.eval adeSphere3QP
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, OfNat.zero_ne_ofNat, Nat.zero_ne_one,
    ↓reduceIte, zero_mul, zero_add, OfNat.one_ne_ofNat, pow_one]
  ring

lemma adeSphere3QP_eval_succ (M : ℕ) (hM : 0 < M) (A : Polynomial ℂ) (k : ℕ) :
    (adeSphere3QP M hM A).eval ((k + 1 : ℕ) : ℤ) =
      ((k + 1 : ℕ) : ℂ) * adeMolienCoeff M A k := by
  rw [adeSphere3QP_eval]
  have hmod : (((k + 1 : ℕ) : ℤ) % (M : ℤ)).toNat = (k + 1) % M := by
    rw [← Int.natCast_emod, Int.toNat_natCast]
  rw [hmod]
  simp only [adeMolienCoeff, adeAlpha, adeBeta, Nat.mod_mod, Int.cast_natCast]
  ring

private lemma adeMolienCoeff_eq_quot {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hdeg : ∀ j : ℕ, 2 * M - 2 < j → A.coeff j = 0) (k : ℕ) :
    adeMolienCoeff M A k =
      ((k / M + 1 : ℕ) : ℂ) * A.coeff (k % M) + ((k / M : ℕ) : ℂ) * A.coeff (k % M + M) := by
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hk_div : k = M * (k / M) + k % M := (Nat.div_add_mod k M).symm
  have hlt : k % M < M := Nat.mod_lt k hM
  unfold adeMolienCoeff adeAlpha adeBeta
  by_cases hlast : k % M = M - 1
  · have hk1_nat : k + 1 = M * (k / M + 1) := by
      rw [Nat.mul_add, mul_one]; omega
    have hmod0 : (k + 1) % M = 0 := by rw [hk1_nat, Nat.mul_mod_right]
    have hk1 : ((k + 1 : ℕ) : ℂ) = (M : ℂ) * ((k / M + 1 : ℕ) : ℂ) := by
      exact_mod_cast hk1_nat
    have hAhi : A.coeff (M - 1 + M) = 0 := hdeg (M - 1 + M) (by omega)
    simp only [hmod0, ↓reduceIte, hk1, hlast, hAhi, mul_zero, add_zero]
    field_simp [hMne]
  · have hk1_nat : k + 1 = M * (k / M) + (k % M + 1) := by omega
    have hmod_pos : (k + 1) % M = k % M + 1 := by
      rw [hk1_nat, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hmod_ne0 : (k + 1) % M ≠ 0 := by omega
    have hk1 : ((k + 1 : ℕ) : ℂ) = (M : ℂ) * ((k / M : ℕ) : ℂ) + ((k % M + 1 : ℕ) : ℂ) := by
      exact_mod_cast hk1_nat
    rw [ite_eq_right_iff.mpr (fun h => (hmod_ne0 h).elim),
      ite_eq_right_iff.mpr (fun h => (hmod_ne0 h).elim),
      hmod_pos, Nat.add_sub_cancel, hk1]
    push_cast
    field_simp [hMne]
    ring

/-- **Exact Rational Generating-Function Identity (`(1 - X^M)² * M_A(X) = A(X)`)** in `PowerSeries ℂ`. -/
theorem adeMolienSeries_mul_one_sub_pow_two {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hdeg : ∀ j : ℕ, 2 * M - 2 < j → A.coeff j = 0) :
    ((1 - PowerSeries.X ^ M : PowerSeries ℂ) ^ 2) * adeMolienSeries M A =
      (A : PowerSeries ℂ) := by
  have hsq : (1 - PowerSeries.X ^ M : PowerSeries ℂ) ^ 2 =
      1 - PowerSeries.C (2 : ℂ) * PowerSeries.X ^ M + PowerSeries.X ^ (2 * M) := by
    have h2 : (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) := (map_ofNat PowerSeries.C 2).symm
    rw [sub_sq, one_pow, ← pow_mul, mul_comm M 2, h2]; ring
  rw [hsq, add_mul, sub_mul, one_mul, mul_assoc]
  ext k
  rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul', Polynomial.coeff_coe]
  simp only [adeMolienSeries, PowerSeries.coeff_mk]
  by_cases hk1 : k < M
  · have hge1 : ¬ M ≤ k := by omega
    have hge2 : ¬ 2 * M ≤ k := by omega
    simp only [hge1, hge2, ↓reduceIte, mul_zero, sub_zero, add_zero]
    rw [adeMolienCoeff_eq_quot hM hdeg k, Nat.div_eq_of_lt hk1, Nat.mod_eq_of_lt hk1]
    simp
  · by_cases hk2 : k < 2 * M
    · have hge1 : M ≤ k := by omega
      have hge2 : ¬ 2 * M ≤ k := by omega
      simp only [hge1, hge2, ↓reduceIte, add_zero]
      rw [adeMolienCoeff_eq_quot hM hdeg k, adeMolienCoeff_eq_quot hM hdeg (k - M)]
      have hdiv1 : k / M = 1 := by
        have : k = M * 1 + (k - M) := by omega
        rw [this, Nat.mul_add_div hM, Nat.div_eq_of_lt (by omega : k - M < M)]
      have hmod1 : k % M = k - M := by
        have : k = M * 1 + (k - M) := by omega
        conv_lhs => rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : k - M < M)]
      have hdiv0 : (k - M) / M = 0 := Nat.div_eq_of_lt (by omega)
      have hmod0 : (k - M) % M = k - M := Nat.mod_eq_of_lt (by omega)
      rw [hdiv1, hmod1, hdiv0, hmod0, show k - M + M = k by omega]
      push_cast; ring
    · have hge1 : M ≤ k := by omega
      have hge2 : 2 * M ≤ k := by omega
      simp only [hge1, hge2, ↓reduceIte]
      rw [adeMolienCoeff_eq_quot hM hdeg k, adeMolienCoeff_eq_quot hM hdeg (k - M),
        adeMolienCoeff_eq_quot hM hdeg (k - 2 * M)]
      have hmod1 : (k - M) % M = k % M := by
        have : k = (k - M) + 1 * M := by omega
        conv_rhs => rw [this, Nat.add_mul_mod_self_right]
      have hmod2 : (k - 2 * M) % M = k % M := by
        have : k = (k - 2 * M) + 2 * M := by omega
        conv_rhs => rw [this, Nat.add_mul_mod_self_right]
      have hdiv1 : (k - M) / M + 1 = k / M := by
        have h1 : k = (k - M) + M := by omega
        conv_rhs => rw [h1, Nat.add_div_right _ hM]
      have hdiv2 : (k - 2 * M) / M + 2 = k / M := by
        have h1 : k = (k - 2 * M) + 2 * M := by omega
        conv_rhs => rw [h1, Nat.add_mul_div_right _ _ hM]
      have hd1C : (((k - M) / M : ℕ) : ℂ) = ((k / M : ℕ) : ℂ) - 1 := by
        have h1 : (((k - M) / M : ℕ) : ℂ) + 1 = ((k / M : ℕ) : ℂ) := by exact_mod_cast hdiv1
        linear_combination h1
      have hd2C : (((k - 2 * M) / M : ℕ) : ℂ) = ((k / M : ℕ) : ℂ) - 2 := by
        have h2 : (((k - 2 * M) / M : ℕ) : ℂ) + 2 = ((k / M : ℕ) : ℂ) := by exact_mod_cast hdiv2
        linear_combination h2
      rw [hmod1, hmod2, hdeg k (by omega)]
      push_cast
      rw [hd1C, hd2C]
      ring

/-- **Factoring Helper**: If `A = N * geomPoly d₁ (M / d₁) * geomPoly d₂ (M / d₂)` with
`d₁ ∣ M`, `d₂ ∣ M`, then `(1 - X^{d₁})(1 - X^{d₂}) * adeMolienSeries M A = N` in `PowerSeries ℂ`. -/
theorem adeMolienSeries_factor_identity {M d₁ d₂ : ℕ} (hM : 0 < M) (hd₁ : d₁ ∣ M) (hd₂ : d₂ ∣ M)
    (N : Polynomial ℂ)
    (hdeg : ∀ j : ℕ, 2 * M - 2 < j →
      (N * geomPoly d₁ (M / d₁) * geomPoly d₂ (M / d₂)).coeff j = 0) :
    (1 - PowerSeries.X ^ d₁ : PowerSeries ℂ) * (1 - PowerSeries.X ^ d₂ : PowerSeries ℂ) *
        adeMolienSeries M (N * geomPoly d₁ (M / d₁) * geomPoly d₂ (M / d₂)) =
      (N : PowerSeries ℂ) := by
  let P₁ : Polynomial ℂ := geomPoly d₁ (M / d₁)
  let P₂ : Polynomial ℂ := geomPoly d₂ (M / d₂)
  let A : Polynomial ℂ := N * P₁ * P₂
  have h1 : (1 - Polynomial.X ^ d₁ : Polynomial ℂ) * P₁ = 1 - Polynomial.X ^ M := by
    dsimp only [P₁]
    rw [one_sub_X_pow_mul_geomPoly, Nat.div_mul_cancel hd₁]
  have h2 : (1 - Polynomial.X ^ d₂ : Polynomial ℂ) * P₂ = 1 - Polynomial.X ^ M := by
    dsimp only [P₂]
    rw [one_sub_X_pow_mul_geomPoly, Nat.div_mul_cancel hd₂]
  have hps1 : (1 - PowerSeries.X ^ d₁ : PowerSeries ℂ) * (P₁ : PowerSeries ℂ) =
      1 - PowerSeries.X ^ M := by
    have := congrArg (fun p : Polynomial ℂ => (p : PowerSeries ℂ)) h1
    simpa [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.coe_mul] using this
  have hps2 : (1 - PowerSeries.X ^ d₂ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ) =
      1 - PowerSeries.X ^ M := by
    have := congrArg (fun p : Polynomial ℂ => (p : PowerSeries ℂ)) h2
    simpa [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.coe_mul] using this
  have hmain := adeMolienSeries_mul_one_sub_pow_two hM (A := A) hdeg
  have hAcoe : (A : PowerSeries ℂ) = (N : PowerSeries ℂ) * ((P₁ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ)) := by
    dsimp only [A]
    simp only [Polynomial.coe_mul, mul_assoc]
  have hprod : ((P₁ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ)) *
      ((1 - PowerSeries.X ^ d₁ : PowerSeries ℂ) * (1 - PowerSeries.X ^ d₂ : PowerSeries ℂ) *
        adeMolienSeries M A) =
      ((P₁ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ)) * (N : PowerSeries ℂ) := by
    calc ((P₁ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ)) *
          ((1 - PowerSeries.X ^ d₁ : PowerSeries ℂ) * (1 - PowerSeries.X ^ d₂ : PowerSeries ℂ) *
            adeMolienSeries M A)
        = (((1 - PowerSeries.X ^ d₁ : PowerSeries ℂ) * (P₁ : PowerSeries ℂ)) *
            ((1 - PowerSeries.X ^ d₂ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ))) *
            adeMolienSeries M A := by ring
      _ = ((1 - PowerSeries.X ^ M : PowerSeries ℂ) ^ 2) * adeMolienSeries M A := by
            rw [hps1, hps2, sq]
      _ = (A : PowerSeries ℂ) := hmain
      _ = ((P₁ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ)) * (N : PowerSeries ℂ) := by
            rw [hAcoe]; ring
  have hPne : ∀ {d q : ℕ}, 0 < d → 1 ≤ q → (geomPoly d q : PowerSeries ℂ) ≠ 0 := by
    intro d q hd hq h0
    have hc := congrArg (PowerSeries.coeff 0) h0
    rw [Polynomial.coeff_coe, coeff_geomPoly hd, map_zero] at hc
    simp [Nat.zero_div] at hc
    omega
  have hd₁_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hd₁ hM
  have hd₂_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos hd₂ hM
  have hq₁ : 1 ≤ M / d₁ := Nat.div_pos (Nat.le_of_dvd hM hd₁) hd₁_pos
  have hq₂ : 1 ≤ M / d₂ := Nat.div_pos (Nat.le_of_dvd hM hd₂) hd₂_pos
  have hP12_ne : (P₁ : PowerSeries ℂ) * (P₂ : PowerSeries ℂ) ≠ 0 :=
    mul_ne_zero (hPne hd₁_pos hq₁) (hPne hd₂_pos hq₂)
  exact mul_left_cancel₀ hP12_ne hprod

/-- **Master Gorenstein Palindromic Even-Parity Theorem**:
Whenever `A` is palindromic of degree `2M - 2`, the spherical 3-manifold multiplicity
quasipolynomial `adeSphere3QP M hM A` is **strictly even on all of `ℤ`**:
`eval (-u) = eval u` and `oddPart u = 0` for every `u : ℤ`! -/
theorem adeSphere3QP_even {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hpal : IsPalindromic (2 * M - 2) A) (u : ℤ) :
    (adeSphere3QP M hM A).eval (-u) = (adeSphere3QP M hM A).eval u := by
  rw [adeSphere3QP_eval, adeSphere3QP_eval]
  have hMpos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hlt : (u % (M : ℤ)).toNat < M := by
    have h1 := Int.emod_lt_of_pos u hMpos
    have h2 := Int.emod_nonneg u (ne_of_gt hMpos)
    omega
  set r : ℕ := (u % (M : ℤ)).toNat
  have hneg_mod : ((-u) % (M : ℤ)).toNat = if r = 0 then 0 else M - r := by
    have h1 := Int.emod_lt_of_pos (-u) hMpos
    have h2 := Int.emod_nonneg (-u) (ne_of_gt hMpos)
    have h3 := Int.emod_lt_of_pos u hMpos
    have h4 := Int.emod_nonneg u (ne_of_gt hMpos)
    have hsum : (M : ℤ) ∣ (u % (M : ℤ)) + ((-u) % (M : ℤ)) := by
      have ha : u % (M : ℤ) ≡ u [ZMOD (M : ℤ)] := Int.mod_modEq u (M : ℤ)
      have hb : (-u) % (M : ℤ) ≡ -u [ZMOD (M : ℤ)] := Int.mod_modEq (-u) (M : ℤ)
      have hc := ha.add hb
      rw [add_neg_cancel] at hc
      exact Int.dvd_of_emod_eq_zero hc
    split_ifs with hr0
    · have hu0 : u % (M : ℤ) = 0 := by omega
      rw [hu0, zero_add] at hsum
      rcases hsum with ⟨k, hk⟩
      have hk0 : k = 0 := by nlinarith
      subst hk0; omega
    · have hu_pos : 0 < u % (M : ℤ) := by omega
      rcases hsum with ⟨k, hk⟩
      have hk1 : k = 1 := by nlinarith
      subst hk1; omega
  rw [hneg_mod, Int.cast_neg, neg_sq]
  split_ifs with hr0
  · rw [hr0]
    simp only [adeBeta, Nat.zero_mod, ↓reduceIte, zero_mul, add_zero]
  · have hMr_lt : M - r < M := by omega
    have hMr_ne0 : M - r ≠ 0 := by omega
    have hpal1 : A.coeff (M - r - 1) = A.coeff (r - 1 + M) := by
      have := hpal.2 (r - 1 + M) (by omega)
      rw [show 2 * M - 2 - (r - 1 + M) = M - r - 1 by omega] at this
      exact this
    have hpal2 : A.coeff (M - r - 1 + M) = A.coeff (r - 1) := by
      have := hpal.2 (r - 1) (by omega)
      rw [show 2 * M - 2 - (r - 1) = M - r - 1 + M by omega] at this
      exact this
    have halpha : adeAlpha M A (M - r) = adeAlpha M A r := by
      unfold adeAlpha
      rw [Nat.mod_eq_of_lt hMr_lt, Nat.mod_eq_of_lt hlt,
        ite_eq_right_iff.mpr (fun h => (hMr_ne0 h).elim),
        ite_eq_right_iff.mpr (fun h => (hr0 h).elim),
        hpal1, hpal2, add_comm]
    have hbeta : adeBeta M A (M - r) = -adeBeta M A r := by
      unfold adeBeta
      rw [Nat.mod_eq_of_lt hMr_lt, Nat.mod_eq_of_lt hlt,
        ite_eq_right_iff.mpr (fun h => (hMr_ne0 h).elim),
        ite_eq_right_iff.mpr (fun h => (hr0 h).elim),
        hpal1, hpal2]
      have hcast : ((M - r : ℕ) : ℂ) = (M : ℂ) - (r : ℂ) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
      rw [hcast]
      field_simp [hMne]
      ring
    rw [halpha, hbeta]
    ring

theorem adeSphere3QP_oddPart_eq_zero {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hpal : IsPalindromic (2 * M - 2) A) (u : ℤ) :
    (adeSphere3QP M hM A).oddPart u = 0 := by
  unfold Quasipoly.oddPart
  rw [adeSphere3QP_even hM hpal u, sub_self, zero_div]

/-- Vanishing of every odd-part quasipolynomial coefficient and every odd-parity Borel Stokes
amplitude for any palindromic ADE spherical 3-manifold `S³ / Γ`. -/
theorem adeSphere3QP_cOdd_eq_zero {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hpal : IsPalindromic (2 * M - 2) A) (d : Fin 3) (n : ℕ) :
    (adeSphere3QP M hM A).cOdd d n = 0 := by
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hlt : n % M < M := Nat.mod_lt n hM
  unfold Quasipoly.cOdd adeSphere3QP
  dsimp only
  by_cases hd2 : d.1 = 2
  · simp only [hd2, ↓reduceIte, show (-1 : ℂ) ^ 2 = 1 by norm_num, one_mul]
    have halpha : adeAlpha M A (M - n % M) = adeAlpha M A n := by
      unfold adeAlpha
      by_cases hr0 : n % M = 0
      · rw [hr0, Nat.sub_zero, Nat.mod_self]
      · have hMr_lt : M - n % M < M := by omega
        have hMr_ne0 : M - n % M ≠ 0 := by omega
        rw [Nat.mod_eq_of_lt hMr_lt,
          ite_eq_right_iff.mpr (fun h => (hMr_ne0 h).elim),
          ite_eq_right_iff.mpr (fun h => (hr0 h).elim)]
        have h1 : A.coeff (M - n % M - 1) = A.coeff (n % M - 1 + M) := by
          have := hpal.2 (n % M - 1 + M) (by omega)
          rwa [show 2 * M - 2 - (n % M - 1 + M) = M - n % M - 1 by omega] at this
        have h2 : A.coeff (M - n % M - 1 + M) = A.coeff (n % M - 1) := by
          have := hpal.2 (n % M - 1) (by omega)
          rwa [show 2 * M - 2 - (n % M - 1) = M - n % M - 1 + M by omega] at this
        rw [h1, h2, add_comm]
    rw [halpha]; ring
  · rw [ite_eq_right_iff.mpr (fun h => (hd2 h).elim),
      ite_eq_right_iff.mpr (fun h => (hd2 h).elim)]
    by_cases hd1 : d.1 = 1
    · simp only [hd1, ↓reduceIte, pow_one]
      have hbeta : adeBeta M A (M - n % M) = -adeBeta M A n := by
        unfold adeBeta
        by_cases hr0 : n % M = 0
        · rw [hr0, Nat.sub_zero, Nat.mod_self]; simp
        · have hMr_lt : M - n % M < M := by omega
          have hMr_ne0 : M - n % M ≠ 0 := by omega
          rw [Nat.mod_eq_of_lt hMr_lt,
            ite_eq_right_iff.mpr (fun h => (hMr_ne0 h).elim),
            ite_eq_right_iff.mpr (fun h => (hr0 h).elim)]
          have h1 : A.coeff (M - n % M - 1) = A.coeff (n % M - 1 + M) := by
            have := hpal.2 (n % M - 1 + M) (by omega)
            rwa [show 2 * M - 2 - (n % M - 1 + M) = M - n % M - 1 by omega] at this
          have h2 : A.coeff (M - n % M - 1 + M) = A.coeff (n % M - 1) := by
            have := hpal.2 (n % M - 1) (by omega)
            rwa [show 2 * M - 2 - (n % M - 1) = M - n % M - 1 + M by omega] at this
          have hcast : ((M - n % M : ℕ) : ℂ) = (M : ℂ) - ((n % M : ℕ) : ℂ) := by
            rw [Nat.cast_sub (le_of_lt hlt)]
          rw [h1, h2, hcast]
          field_simp [hMne]; ring
      rw [hbeta]; ring
    · rw [ite_eq_right_iff.mpr (fun h => (hd1 h).elim),
        ite_eq_right_iff.mpr (fun h => (hd1 h).elim)]; ring

theorem adeSphere3QP_borelAmp_eq_zero {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hpal : IsPalindromic (2 * M - 2) A) (d : Fin 3) (m : ℕ) :
    (adeSphere3QP M hM A).borelAmp d m = 0 := by
  unfold Quasipoly.borelAmp Quasipoly.cDft
  refine Finset.sum_eq_zero fun k _ => ?_
  have hsum : ∑ r ∈ Finset.Icc 1 (adeSphere3QP M hM A).M,
      (adeSphere3QP M hM A).cOdd d r *
        Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / ((adeSphere3QP M hM A).M : ℝ) : ℝ) : ℂ) * I) = 0 :=
    Finset.sum_eq_zero fun r _ => by rw [adeSphere3QP_cOdd_eq_zero hM hpal d r, zero_mul]
  rw [hsum, mul_zero, mul_zero]

/-! #### C.2 Poincaré Homology Sphere `S³ / I*` (`E₈`, Period `M = 60`) -/

/-- Palindromic degree-118 numerator of `M_{I*}(t) = (1 + t³⁰) / ((1 - t¹²)(1 - t²⁰)) = A_{I*}(t) / (1 - t⁶⁰)²`. -/
@[expose] def poincareMolienNum : Polynomial ℂ :=
  (1 + Polynomial.X ^ 30) * geomPoly 12 5 * geomPoly 20 3

lemma poincareMolienNum_palindromic : IsPalindromic 118 poincareMolienNum := by
  have h1 : IsPalindromic 30 (1 + Polynomial.X ^ 30 : Polynomial ℂ) :=
    isPalindromic_one_add_X_pow 30
  have h2 : IsPalindromic 48 (geomPoly 12 5) :=
    isPalindromic_geomPoly (by norm_num : 0 < 12) (by norm_num : 1 ≤ 5)
  have h3 : IsPalindromic 40 (geomPoly 20 3) :=
    isPalindromic_geomPoly (by norm_num : 0 < 20) (by norm_num : 1 ≤ 3)
  simpa [poincareMolienNum] using isPalindromic_mul (isPalindromic_mul h1 h2) h3

/-- Exact period-60 quasipolynomial for the **Poincaré homology sphere `S³ / I*`** (`|I*| = 120`):
`m_{S³/I*}(u) = u · c_{I*}(u - 1)` where `∑ c_{I*}(k) t^k = (1 + t³⁰) / ((1 - t¹²)(1 - t²⁰))`. -/
@[expose] def poincareSphereQP : Quasipoly :=
  adeSphere3QP 60 (by norm_num) poincareMolienNum

/-- Exact Molien power series identity for the Poincaré homology sphere `S³ / I*`:
`(1 - X¹²)(1 - X²⁰) * M_{I*}(X) = 1 + X³⁰` in `PowerSeries ℂ`. -/
theorem poincareSphere_molien_identity :
    (1 - PowerSeries.X ^ 12 : PowerSeries ℂ) * (1 - PowerSeries.X ^ 20 : PowerSeries ℂ) *
        adeMolienSeries 60 poincareMolienNum =
      1 + PowerSeries.X ^ 30 := by
  have h := adeMolienSeries_factor_identity (M := 60) (d₁ := 12) (d₂ := 20)
    (by norm_num) (by norm_num) (by norm_num) (1 + Polynomial.X ^ 30)
    poincareMolienNum_palindromic.1
  simpa [poincareMolienNum, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_pow,
    Polynomial.coe_X] using h

/-- **Poincaré Homology Sphere `S³ / I*` Even-Parity Theorem**:
`m_{S³/I*}(-u) = m_{S³/I*}(u)` for all `u : ℤ`! -/
theorem poincareSphereQP_even (m : ℤ) :
    poincareSphereQP.eval (-m) = poincareSphereQP.eval m :=
  adeSphere3QP_even (by norm_num) poincareMolienNum_palindromic m

/-- **Poincaré Homology Sphere `S³ / I*` Vanishing Odd Part**:
`poincareSphereQP.oddPart m = 0` for all `m : ℤ` (and all odd-parity Borel Stokes amplitudes
vanish identically). -/
theorem poincareSphereQP_oddPart_eq_zero (m : ℤ) :
    poincareSphereQP.oddPart m = 0 :=
  adeSphere3QP_oddPart_eq_zero (by norm_num) poincareMolienNum_palindromic m

theorem poincareSphereQP_borelAmp_eq_zero (d : Fin 3) (m : ℕ) :
    poincareSphereQP.borelAmp d m = 0 :=
  adeSphere3QP_borelAmp_eq_zero (by norm_num) poincareMolienNum_palindromic d m

/-- Exact computable `ℕ`-level Molien coefficient `c_{I*}(k)` for `0 ≤ k < 60` from
`(1 + t³⁰)(1 + t¹² + t²⁴ + t³⁶ + t⁴⁸)(1 + t²⁰ + t⁴⁰)`. -/
@[expose] def poincareMolienNat (k : ℕ) : ℕ :=
  (Finset.range 5).sum fun i =>
    (Finset.range 3).sum fun j =>
      (if 12 * i + 20 * j = k then 1 else 0) +
      (if 30 + 12 * i + 20 * j = k then 1 else 0)

private lemma poincareMolienNum_coeff_eq (k : ℕ) :
    poincareMolienNum.coeff k = (poincareMolienNat k : ℂ) := by
  unfold poincareMolienNum geomPoly poincareMolienNat
  have hexp : ((1 + Polynomial.X ^ 30 : Polynomial ℂ) *
      (∑ i ∈ Finset.range 5, Polynomial.X ^ (i * 12)) *
      (∑ j ∈ Finset.range 3, Polynomial.X ^ (j * 20))) =
      ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 3,
        (Polynomial.X ^ (12 * i + 20 * j) + Polynomial.X ^ (30 + 12 * i + 20 * j)) := by
    rw [Finset.mul_sum (s := Finset.range 5), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_mul, one_mul, add_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    · congr 1; ring
    · congr 1; ring
  rw [hexp, poly_finset_sum_coeff]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [poly_finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
  simp only [eq_comm (a := k)]

/-- **Exact Values of `poincareSphereQP` on the Entire Fundamental Period `0 ≤ u ≤ 60`**:
For `u = 0`, `eval 0 = 0`; for every `1 ≤ u ≤ 60`, `eval u = u * poincareMolienNat (u - 1)`! -/
theorem poincareSphereQP_eval_period (u : ℕ) (hu : u ≤ 60) :
    poincareSphereQP.eval (u : ℤ) =
      if u = 0 then 0 else (u : ℂ) * (poincareMolienNat (u - 1) : ℂ) := by
  cases u with
  | zero =>
    simp [poincareSphereQP, adeSphere3QP_eval]
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [poincareSphereQP, adeSphere3QP_eval_succ,
      adeMolienCoeff_eq_quot (by norm_num : 0 < 60) poincareMolienNum_palindromic.1 k,
      Nat.div_eq_of_lt (by omega : k < 60), Nat.mod_eq_of_lt (by omega : k < 60),
      poincareMolienNum_coeff_eq k]
    simp

/-- Concrete benchmark multiplicities on the Poincaré homology sphere `S³ / I*`:
ground state `u = 1 → 1`, first excited `u = 13 → 13` (`λ₁ = 168`), `u = 21 → 21`,
`u = 25 → 25`, `u = 31 → 31`, `u = 37 → 37`, `u = 41 → 41`, `u = 45 → 45`, `u = 49 → 49`,
`u = 51 → 51`, `u = 55 → 55`, and `u = 61 → 122` (`c_{I*}(60) = 2`), with exact spectral gap
`m(u) = 0` for `2 ≤ u ≤ 12`! -/
theorem poincareSphereQP_key_values :
    poincareSphereQP.eval 1 = 1 ∧
    (∀ u : ℕ, 2 ≤ u → u ≤ 12 → poincareSphereQP.eval (u : ℤ) = 0) ∧
    poincareSphereQP.eval 13 = 13 ∧
    poincareSphereQP.eval 21 = 21 ∧
    poincareSphereQP.eval 25 = 25 ∧
    poincareSphereQP.eval 31 = 31 ∧
    poincareSphereQP.eval 37 = 37 ∧
    poincareSphereQP.eval 41 = 41 ∧
    poincareSphereQP.eval 45 = 45 ∧
    poincareSphereQP.eval 49 = 49 ∧
    poincareSphereQP.eval 51 = 51 ∧
    poincareSphereQP.eval 55 = 55 ∧
    poincareSphereQP.eval 61 = 122 := by
  have hval : ∀ u : ℕ, 1 ≤ u → u ≤ 60 →
      poincareSphereQP.eval (u : ℤ) = (u : ℂ) * (poincareMolienNat (u - 1) : ℂ) := fun u h1 h2 => by
    rw [poincareSphereQP_eval_period u h2]
    simp [show u ≠ 0 by omega]
  have hnat_eval : ∀ k n : ℕ, poincareMolienNat k = n → (poincareMolienNat k : ℂ) = (n : ℂ) :=
    fun _ _ h => by exact_mod_cast h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, hval 1 (by omega) (by omega),
      hnat_eval 0 1 (by decide)]; norm_num
  · intro u hu1 hu2
    rw [hval u (by omega) (by omega)]
    have h0 : poincareMolienNat (u - 1) = 0 := by
      interval_cases u <;> decide
    rw [h0]; simp
  · rw [show (13 : ℤ) = ((13 : ℕ) : ℤ) from rfl, hval 13 (by omega) (by omega),
      hnat_eval 12 1 (by decide)]; norm_num
  · rw [show (21 : ℤ) = ((21 : ℕ) : ℤ) from rfl, hval 21 (by omega) (by omega),
      hnat_eval 20 1 (by decide)]; norm_num
  · rw [show (25 : ℤ) = ((25 : ℕ) : ℤ) from rfl, hval 25 (by omega) (by omega),
      hnat_eval 24 1 (by decide)]; norm_num
  · rw [show (31 : ℤ) = ((31 : ℕ) : ℤ) from rfl, hval 31 (by omega) (by omega),
      hnat_eval 30 1 (by decide)]; norm_num
  · rw [show (37 : ℤ) = ((37 : ℕ) : ℤ) from rfl, hval 37 (by omega) (by omega),
      hnat_eval 36 1 (by decide)]; norm_num
  · rw [show (41 : ℤ) = ((41 : ℕ) : ℤ) from rfl, hval 41 (by omega) (by omega),
      hnat_eval 40 1 (by decide)]; norm_num
  · rw [show (45 : ℤ) = ((45 : ℕ) : ℤ) from rfl, hval 45 (by omega) (by omega),
      hnat_eval 44 1 (by decide)]; norm_num
  · rw [show (49 : ℤ) = ((49 : ℕ) : ℤ) from rfl, hval 49 (by omega) (by omega),
      hnat_eval 48 1 (by decide)]; norm_num
  · rw [show (51 : ℤ) = ((51 : ℕ) : ℤ) from rfl, hval 51 (by omega) (by omega),
      hnat_eval 50 1 (by decide)]; norm_num
  · rw [show (55 : ℤ) = ((55 : ℕ) : ℤ) from rfl, hval 55 (by omega) (by omega),
      hnat_eval 54 1 (by decide)]; norm_num
  · rw [show (61 : ℤ) = ((60 + 1 : ℕ) : ℤ) from rfl, poincareSphereQP, adeSphere3QP_eval_succ,
      adeMolienCoeff_eq_quot (by norm_num : 0 < 60) poincareMolienNum_palindromic.1 60]
    have h0 := poincareMolienNum_coeff_eq 0
    have h60 := poincareMolienNum_coeff_eq 60
    rw [show 60 / 60 = 1 by decide, show 60 % 60 = 0 by decide, zero_add, h0, h60,
      hnat_eval 0 1 (by decide), hnat_eval 60 0 (by decide)]
    norm_num

/-! #### C.3 Octahedral `S³ / O*` (`E₇`, `M = 24`), Tetrahedral `S³ / T*` (`E₆`, `M = 12`), and Binary Dihedral `S³ / D_m*` (`D_{m+2}`, `M = 4m`) -/

/-- Palindromic degree-46 numerator of `M_{O*}(t) = (1 + t¹⁸) / ((1 - t⁸)(1 - t¹²)) = A_{O*}(t) / (1 - t²⁴)²`. -/
@[expose] def octahedralMolienNum : Polynomial ℂ :=
  (1 + Polynomial.X ^ 18) * geomPoly 8 3 * geomPoly 12 2

lemma octahedralMolienNum_palindromic : IsPalindromic 46 octahedralMolienNum := by
  have h1 : IsPalindromic 18 (1 + Polynomial.X ^ 18 : Polynomial ℂ) :=
    isPalindromic_one_add_X_pow 18
  have h2 : IsPalindromic 16 (geomPoly 8 3) :=
    isPalindromic_geomPoly (by norm_num : 0 < 8) (by norm_num : 1 ≤ 3)
  have h3 : IsPalindromic 12 (geomPoly 12 2) :=
    isPalindromic_geomPoly (by norm_num : 0 < 12) (by norm_num : 1 ≤ 2)
  simpa [octahedralMolienNum] using isPalindromic_mul (isPalindromic_mul h1 h2) h3

/-- Exact period-24 quasipolynomial for the **octahedral spherical 3-manifold `S³ / O*`** (`|O*| = 48`). -/
@[expose] def octahedralSphereQP : Quasipoly :=
  adeSphere3QP 24 (by norm_num) octahedralMolienNum

theorem octahedralSphere_molien_identity :
    (1 - PowerSeries.X ^ 8 : PowerSeries ℂ) * (1 - PowerSeries.X ^ 12 : PowerSeries ℂ) *
        adeMolienSeries 24 octahedralMolienNum =
      1 + PowerSeries.X ^ 18 := by
  have h := adeMolienSeries_factor_identity (M := 24) (d₁ := 8) (d₂ := 12)
    (by norm_num) (by norm_num) (by norm_num) (1 + Polynomial.X ^ 18)
    octahedralMolienNum_palindromic.1
  simpa [octahedralMolienNum, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_pow,
    Polynomial.coe_X] using h

theorem octahedralSphereQP_even (m : ℤ) :
    octahedralSphereQP.eval (-m) = octahedralSphereQP.eval m :=
  adeSphere3QP_even (by norm_num) octahedralMolienNum_palindromic m

theorem octahedralSphereQP_oddPart_eq_zero (m : ℤ) :
    octahedralSphereQP.oddPart m = 0 :=
  adeSphere3QP_oddPart_eq_zero (by norm_num) octahedralMolienNum_palindromic m

/-- Palindromic degree-22 numerator of
`M_{T*}(t) = (1 + t¹²) / ((1 - t⁶)(1 - t⁸)) = (1 - t⁴ + t⁸) / ((1 - t⁶)(1 - t⁴)) = A_{T*}(t) / (1 - t¹²)²`. -/
@[expose] def tetrahedralMolienNum : Polynomial ℂ :=
  (1 - Polynomial.X ^ 4 + Polynomial.X ^ 8) * geomPoly 6 2 * geomPoly 4 3

private lemma isPalindromic_tetra_num :
    IsPalindromic 8 (1 - Polynomial.X ^ 4 + Polynomial.X ^ 8 : Polynomial ℂ) := by
  constructor
  · intro j hj
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
    have h0 : j ≠ 0 := by omega
    have h4 : j ≠ 4 := by omega
    have h8 : j ≠ 8 := by omega
    simp [h0, h4, h8]
  · intro j hj
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_X_pow, Polynomial.coeff_X_pow,
      Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
    interval_cases j <;> simp

lemma tetrahedralMolienNum_palindromic : IsPalindromic 22 tetrahedralMolienNum := by
  have h2 : IsPalindromic 6 (geomPoly 6 2) :=
    isPalindromic_geomPoly (by norm_num : 0 < 6) (by norm_num : 1 ≤ 2)
  have h3 : IsPalindromic 8 (geomPoly 4 3) :=
    isPalindromic_geomPoly (by norm_num : 0 < 4) (by norm_num : 1 ≤ 3)
  simpa [tetrahedralMolienNum] using isPalindromic_mul (isPalindromic_mul isPalindromic_tetra_num h2) h3

/-- Exact period-12 quasipolynomial for the **tetrahedral spherical 3-manifold `S³ / T*`** (`|T*| = 24`). -/
@[expose] def tetrahedralSphereQP : Quasipoly :=
  adeSphere3QP 12 (by norm_num) tetrahedralMolienNum

theorem tetrahedralSphere_molien_identity :
    (1 - PowerSeries.X ^ 6 : PowerSeries ℂ) * (1 - PowerSeries.X ^ 8 : PowerSeries ℂ) *
        adeMolienSeries 12 tetrahedralMolienNum =
      1 + PowerSeries.X ^ 12 := by
  have hbase := adeMolienSeries_factor_identity (M := 12) (d₁ := 6) (d₂ := 4)
    (by norm_num) (by norm_num) (by norm_num) (1 - Polynomial.X ^ 4 + Polynomial.X ^ 8)
    tetrahedralMolienNum_palindromic.1
  have hbase' : (1 - PowerSeries.X ^ 6 : PowerSeries ℂ) * (1 - PowerSeries.X ^ 4 : PowerSeries ℂ) *
      adeMolienSeries 12 tetrahedralMolienNum =
      1 - PowerSeries.X ^ 4 + PowerSeries.X ^ 8 := by
    simpa [tetrahedralMolienNum, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_pow, Polynomial.coe_X] using hbase
  have hmul := congrArg (fun S : PowerSeries ℂ => (1 + PowerSeries.X ^ 4) * S) hbase'
  have hL : (1 + PowerSeries.X ^ 4 : PowerSeries ℂ) *
      ((1 - PowerSeries.X ^ 6) * (1 - PowerSeries.X ^ 4) * adeMolienSeries 12 tetrahedralMolienNum) =
      (1 - PowerSeries.X ^ 6) * (1 - PowerSeries.X ^ 8) * adeMolienSeries 12 tetrahedralMolienNum := by
    have h48 : (PowerSeries.X ^ 4 : PowerSeries ℂ) * PowerSeries.X ^ 4 = PowerSeries.X ^ 8 := by
      rw [← pow_add]
    linear_combination -h48 * (1 - PowerSeries.X ^ 6) * adeMolienSeries 12 tetrahedralMolienNum
  have hR : (1 + PowerSeries.X ^ 4 : PowerSeries ℂ) *
      (1 - PowerSeries.X ^ 4 + PowerSeries.X ^ 8) = 1 + PowerSeries.X ^ 12 := by
    have h48 : (PowerSeries.X ^ 4 : PowerSeries ℂ) * PowerSeries.X ^ 4 = PowerSeries.X ^ 8 := by
      rw [← pow_add]
    have h412 : (PowerSeries.X ^ 4 : PowerSeries ℂ) * PowerSeries.X ^ 8 = PowerSeries.X ^ 12 := by
      rw [← pow_add]
    linear_combination h412 - h48
  rw [hL, hR] at hmul
  exact hmul

theorem tetrahedralSphereQP_even (m : ℤ) :
    tetrahedralSphereQP.eval (-m) = tetrahedralSphereQP.eval m :=
  adeSphere3QP_even (by norm_num) tetrahedralMolienNum_palindromic m

theorem tetrahedralSphereQP_oddPart_eq_zero (m : ℤ) :
    tetrahedralSphereQP.oddPart m = 0 :=
  adeSphere3QP_oddPart_eq_zero (by norm_num) tetrahedralMolienNum_palindromic m

/-- Palindromic degree-`8m - 2` numerator of the **binary dihedral prism manifold `S³ / D_m*`**
(`|D_m*| = 4m`, `m ≥ 2`): `M_{D_m*}(t) = (1 + t^{2m + 2}) / ((1 - t⁴)(1 - t^{2m}))`. -/
@[expose] def binaryDihedralMolienNum (m : ℕ) : Polynomial ℂ :=
  (1 + Polynomial.X ^ (2 * m + 2)) * geomPoly 4 m * geomPoly (2 * m) 2

lemma binaryDihedralMolienNum_palindromic {m : ℕ} (hm : 2 ≤ m) :
    IsPalindromic (2 * (4 * m) - 2) (binaryDihedralMolienNum m) := by
  have h1 : IsPalindromic (2 * m + 2) (1 + Polynomial.X ^ (2 * m + 2) : Polynomial ℂ) :=
    isPalindromic_one_add_X_pow (2 * m + 2)
  have h2 : IsPalindromic ((m - 1) * 4) (geomPoly 4 m) :=
    isPalindromic_geomPoly (by norm_num : 0 < 4) (by omega)
  have h3 : IsPalindromic ((2 - 1) * (2 * m)) (geomPoly (2 * m) 2) :=
    isPalindromic_geomPoly (by omega : 0 < 2 * m) (by norm_num : 1 ≤ 2)
  have hdeg : (2 * m + 2) + (m - 1) * 4 + (2 - 1) * (2 * m) = 2 * (4 * m) - 2 := by omega
  rw [← hdeg]
  exact isPalindromic_mul (isPalindromic_mul h1 h2) h3

/-- Exact period-`4m` quasipolynomial for the binary dihedral prism manifold `S³ / D_m*` (`m ≥ 2`). -/
@[expose] def binaryDihedralSphereQP (m : ℕ) (hm : 2 ≤ m) : Quasipoly :=
  adeSphere3QP (4 * m) (by omega) (binaryDihedralMolienNum m)

theorem binaryDihedralSphere_molien_identity {m : ℕ} (hm : 2 ≤ m) :
    (1 - PowerSeries.X ^ 4 : PowerSeries ℂ) * (1 - PowerSeries.X ^ (2 * m) : PowerSeries ℂ) *
        adeMolienSeries (4 * m) (binaryDihedralMolienNum m) =
      1 + PowerSeries.X ^ (2 * m + 2) := by
  have hd1 : 4 ∣ 4 * m := dvd_mul_right 4 m
  have hd2 : 2 * m ∣ 4 * m := ⟨2, by ring⟩
  have hq1 : 4 * m / 4 = m := Nat.mul_div_cancel_left m (by norm_num)
  have hq2 : 4 * m / (2 * m) = 2 := by
    rw [show 4 * m = 2 * (2 * m) by ring, Nat.mul_div_cancel _ (by omega)]
  have hdeg : ∀ j : ℕ, 2 * (4 * m) - 2 < j →
      ((1 + Polynomial.X ^ (2 * m + 2)) * geomPoly 4 (4 * m / 4) *
        geomPoly (2 * m) (4 * m / (2 * m))).coeff j = 0 := by
    rw [hq1, hq2]
    exact (binaryDihedralMolienNum_palindromic hm).1
  have h := adeMolienSeries_factor_identity (M := 4 * m) (d₁ := 4) (d₂ := 2 * m)
    (by omega) hd1 hd2 (1 + Polynomial.X ^ (2 * m + 2)) hdeg
  rw [hq1, hq2] at h
  simpa [binaryDihedralMolienNum, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_pow,
    Polynomial.coe_X] using h

theorem binaryDihedralSphereQP_even {m : ℕ} (hm : 2 ≤ m) (u : ℤ) :
    (binaryDihedralSphereQP m hm).eval (-u) = (binaryDihedralSphereQP m hm).eval u :=
  adeSphere3QP_even (by omega) (binaryDihedralMolienNum_palindromic hm) u

theorem binaryDihedralSphereQP_oddPart_eq_zero {m : ℕ} (hm : 2 ≤ m) (u : ℤ) :
    (binaryDihedralSphereQP m hm).oddPart u = 0 :=
  adeSphere3QP_oddPart_eq_zero (by omega) (binaryDihedralMolienNum_palindromic hm) u

/-! ### Part D: All-CROSS Heat-Trace Dimension-Reduction & Unconditional `ℂ(t)` D-Transcendence -/

section HeatTraceClosure

open PakPrimes.BranchPointStokes PakPrimes.FalseThetaDichotomy PakPrimes.FishburnTorusKnots

/-! #### D.1 Constant-Coefficient Linear Differential Operator Preservation & `ℂ(t)`-ADE Transfer -/

/-- Constant-coefficient linear differential operator
`L_P(f)(t) = ∑_{j=0}^{deg P} P_j · f^{(j)}(t)`. -/
@[expose] def constCoeffLinDiffOp (P : Polynomial ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * iteratedDeriv j f t

private lemma analyticOnNhd_iteratedDeriv_Ioi' {g : ℝ → ℂ} (hg : AnalyticOnNhd ℝ g (Set.Ioi 0))
    (k : ℕ) : AnalyticOnNhd ℝ (iteratedDeriv k g) (Set.Ioi 0) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    exact (ih x hx).deriv

lemma constCoeffLinDiffOp_analyticOn {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f (Set.Ioi 0))
    (P : Polynomial ℂ) : AnalyticOnNhd ℝ (constCoeffLinDiffOp P f) (Set.Ioi 0) := by
  intro t ht
  refine Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) fun j _ => ?_
  exact analyticAt_const.mul (analyticOnNhd_iteratedDeriv_Ioi' hf j t ht)

private lemma poly_eval_eventually_ne_zero_nhdsGT {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), q.eval (t : ℂ) ≠ 0 := by
  classical
  let S : Finset ℂ := q.roots.toFinset.erase 0
  by_cases hS : S.Nonempty
  · let δ : ℝ := S.inf' hS fun z => ‖z‖
    have hδ_pos : 0 < δ := by
      rw [Finset.lt_inf'_iff]
      intro z hz
      exact norm_pos_iff.mpr (Finset.mem_erase.mp hz).1
    have hmem : Set.Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ_pos
    filter_upwards [hmem] with t ht h0
    have hroot : (t : ℂ) ∈ q.roots := (Polynomial.mem_roots hq).mpr h0
    have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have ht_mem : (t : ℂ) ∈ S := Finset.mem_erase.mpr ⟨ht_ne, Multiset.mem_toFinset.mpr hroot⟩
    have hle : δ ≤ ‖(t : ℂ)‖ := Finset.inf'_le (f := fun z : ℂ => ‖z‖) ht_mem
    rw [Complex.norm_real, Real.norm_of_nonneg ht.1.le] at hle
    linarith [ht.2]
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    filter_upwards [self_mem_nhdsWithin] with t ht h0
    have hroot : (t : ℂ) ∈ q.roots := (Polynomial.mem_roots hq).mpr h0
    have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp ht).ne'
    have ht_mem : (t : ℂ) ∈ S := Finset.mem_erase.mpr ⟨ht_ne, Multiset.mem_toFinset.mpr hroot⟩
    rw [hS] at ht_mem
    exact Finset.notMem_empty _ ht_mem

private noncomputable def clearDenomPoly' {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) : Polynomial ℂ :=
  ∏ α ∈ P.support, (P.coeff α).denom

private noncomputable def clearDenomMvPoly' {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := by
  classical
  exact ∑ α ∈ P.support, MvPolynomial.monomial α
    ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)

private lemma clearDenomMvPoly'_coeff {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) (α : Fin (r + 1) →₀ ℕ) :
    (clearDenomMvPoly' P).coeff α =
      if α ∈ P.support then (P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom else 0 := by
  classical
  unfold clearDenomMvPoly'
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [ite_eq_left_iff.mpr (fun h => (h hα).elim), Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [ite_eq_right_iff.mpr (fun h => (hα h).elim)]
    refine Finset.sum_eq_zero fun β hβ => ?_
    rw [ite_eq_right_iff]
    intro hβα; subst hβα; exact absurd hβ hα

private lemma clearDenomMvPoly'_ne_zero {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)} (hP : P ≠ 0) :
    clearDenomMvPoly' P ≠ 0 := by
  have hne : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨α, hα⟩ := hne
  intro h0
  have hc := congrArg (fun Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) => Q.coeff α) h0
  rw [clearDenomMvPoly'_coeff, ite_eq_left_iff.mpr (fun h => (h hα).elim)] at hc
  change (P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom = 0 at hc
  have hnum_ne : (P.coeff α).num ≠ 0 := by
    intro hnum0
    have hcoeff0 : P.coeff α = 0 := by
      rw [← RatFunc.num_div_denom (P.coeff α), hnum0, map_zero, zero_div]
    exact MvPolynomial.mem_support_iff.mp hα hcoeff0
  have hprod_ne : (∏ β ∈ P.support.erase α, (P.coeff β).denom) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun β _ => RatFunc.denom_ne_zero (P.coeff β)
  exact mul_ne_zero hnum_ne hprod_ne hc

private lemma evalU_clearDenomMvPoly' {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) {u : ℂ}
    (hu : ∀ β ∈ P.support, (P.coeff β).denom.eval u ≠ 0) :
    evalU (clearDenomMvPoly' P) u = (clearDenomPoly' P).eval u • evalRatU P u := by
  classical
  ext α
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, clearDenomMvPoly'_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul, evalRatU, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [ite_eq_left_iff.mpr (fun h => (h hα).elim), Finset.sum_eq_single α]
    · simp only [↓reduceIte, ratEval, clearDenomPoly', Polynomial.eval_prod]
      rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval u) hα,
        Polynomial.eval_mul, Polynomial.eval_prod]
      field_simp [hu α hα]
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [ite_eq_right_iff.mpr (fun h => (hα h).elim), Polynomial.eval_zero, Finset.sum_eq_zero]
    · simp
    · intro β hβ
      rw [ite_eq_right_iff]
      intro hβα; subst hβα; exact absurd hβ hα

private lemma poly_eval_real_analyticAt (p : Polynomial ℂ) (t : ℝ) :
    AnalyticAt ℝ (fun x : ℝ => p.eval (x : ℂ)) t := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
    simpa only [Polynomial.eval_add] using ha.fun_add hb
  | monomial k c =>
    have hfun : (fun x : ℝ => (Polynomial.monomial k c).eval (x : ℂ)) =
        fun x : ℝ => c * (x : ℂ) ^ k := funext fun x => Polynomial.eval_monomial
    rw [hfun]
    exact analyticAt_const.fun_mul ((Complex.ofRealCLM.analyticAt t).pow k)

private lemma evalU_analyticOn_Ioi {r : ℕ} {g : ℝ → ℂ} (hg : AnalyticOnNhd ℝ g (Set.Ioi 0))
    (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    AnalyticOnNhd ℝ
      (fun t : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalU Q (t : ℂ)))
      (Set.Ioi 0) := by
  induction Q using MvPolynomial.induction_on with
  | C p =>
    intro t _
    have hfun : (fun x : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g x)
        (evalU (MvPolynomial.C p) (x : ℂ))) = fun x : ℝ => p.eval (x : ℂ) := by
      funext x; simp [evalU]
    rw [hfun]
    exact poly_eval_real_analyticAt p t
  | add A B hA hB =>
    intro t ht
    have hfun : (fun x : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g x)
        (evalU (A + B) (x : ℂ))) =
        fun x : ℝ =>
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g x) (evalU A (x : ℂ)) +
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g x) (evalU B (x : ℂ)) := by
      funext x; simp [evalU]
    rw [hfun]
    exact (hA t ht).fun_add (hB t ht)
  | mul_X A i hA =>
    intro t ht
    have hfun : (fun x : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g x)
        (evalU (A * MvPolynomial.X i) (x : ℂ))) =
        fun x : ℝ =>
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g x) (evalU A (x : ℂ)) *
          iteratedDeriv i.val g x := by
      funext x; simp [evalU]
    rw [hfun]
    exact (hA t ht).fun_mul (analyticOnNhd_iteratedDeriv_Ioi' hg i.val t ht)

private lemma mvPoly_eval_iteratedDeriv_analyticOn {N : ℕ} {f : ℝ → ℂ}
    (hf : AnalyticOnNhd ℝ f (Set.Ioi 0)) (R : MvPolynomial (Fin (N + 1)) ℂ) :
    AnalyticOnNhd ℝ
      (fun t : ℝ => MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f t) R)
      (Set.Ioi 0) := by
  induction R using MvPolynomial.induction_on with
  | C a => intro t _; simpa using analyticAt_const
  | add a b ha hb =>
    intro t ht
    have hfun : (fun x : ℝ => MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f x) (a + b)) =
        fun x => MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f x) a +
          MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f x) b := by
      funext x; simp
    rw [hfun]; exact (ha t ht).fun_add (hb t ht)
  | mul_X a j ha =>
    intro t ht
    have hfun : (fun x : ℝ => MvPolynomial.eval (fun i : Fin (N + 1) => iteratedDeriv i.val f x) (a * MvPolynomial.X j)) =
        fun x => MvPolynomial.eval (fun i : Fin (N + 1) => iteratedDeriv i.val f x) a *
          iteratedDeriv j.val f x := by
      funext x; simp
    rw [hfun]; exact (ha t ht).fun_mul (analyticOnNhd_iteratedDeriv_Ioi' hf j.val t ht)

/-- Clearing rational denominators near `0+` and extending by real-analyticity to all of `(0, ∞)`. -/
theorem ratADE_nhdsGT_to_polyADE_Ioi {g : ℝ → ℂ} (hg : AnalyticOnNhd ℝ g (Set.Ioi 0))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) (hP_ne : P ≠ 0)
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalRatU P (t : ℂ)) = 0) :
    ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q ≠ 0 ∧
      ∀ t : ℝ, 0 < t →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalU Q (t : ℂ)) = 0 := by
  let Q := clearDenomMvPoly' P
  refine ⟨Q, clearDenomMvPoly'_ne_zero hP_ne, ?_⟩
  have hden : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ β ∈ P.support, (P.coeff β).denom.eval (t : ℂ) ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro β _
    exact poly_eval_eventually_ne_zero_nhdsGT (RatFunc.denom_ne_zero (P.coeff β))
  have hzero_ev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalU Q (t : ℂ)) = 0 := by
    filter_upwards [hP, hden] with t ht hdt
    rw [evalU_clearDenomMvPoly' P hdt, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      ht, mul_zero]
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hzero_ev
  obtain ⟨δ, hδ_pos, hδ⟩ := hzero_ev
  let t₀ : ℝ := δ / 2
  have ht₀_pos : 0 < t₀ := half_pos hδ_pos
  have ht₀_lt : t₀ < δ := by dsimp only [t₀]; linarith
  have hana : AnalyticOnNhd ℝ
      (fun t : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalU Q (t : ℂ)))
      (Set.Ioi 0) := evalU_analyticOn_Ioi hg Q
  have hloc : (fun t : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalU Q (t : ℂ))) =ᶠ[𝓝 t₀]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioo_mem_nhds ht₀_pos ht₀_lt] with t ht
    refine hδ ?_ ht.1
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2
  have hfreq : ∃ᶠ t in 𝓝[≠] t₀,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalU Q (t : ℂ)) = 0 :=
    (hloc.filter_mono nhdsWithin_le_nhds).frequently
  have heq := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_Ioi (0 : ℝ)).isPreconnected ht₀_pos hfreq
  intro t ht
  exact heq ht

private noncomputable def liftPolyToMv {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) : MvPolynomial ℕ ℂ :=
  MvPolynomial.eval₂ (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (fun j : Fin (r + 1) => MvPolynomial.X (j.val + 1)) Q

private lemma eval_liftPolyToMv {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (u : ℂ) (v : Fin (r + 1) → ℂ) :
    MvPolynomial.eval (fun i : ℕ => match i with | 0 => u | j + 1 => if h : j < r + 1 then v ⟨j, h⟩ else 0)
        (liftPolyToMv Q) =
      MvPolynomial.eval v (evalU Q u) := by
  let env : ℕ → ℂ := fun i => match i with | 0 => u | j + 1 => if h : j < r + 1 then v ⟨j, h⟩ else 0
  change MvPolynomial.eval env (liftPolyToMv Q) = MvPolynomial.eval v (evalU Q u)
  induction Q using MvPolynomial.induction_on with
  | C p =>
    simp only [liftPolyToMv, MvPolynomial.eval₂_C, evalU, MvPolynomial.map_C, MvPolynomial.eval_C,
      Polynomial.coe_evalRingHom]
    induction p using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Polynomial.eval_add, ha, hb]
    | monomial k c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
  | add A B hA hB =>
    rw [liftPolyToMv, MvPolynomial.eval₂_add, map_add, evalU, map_add, map_add]
    exact congrArg₂ (· + ·) hA hB
  | mul_X A j hA =>
    rw [liftPolyToMv, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, MvPolynomial.eval_X,
      evalU, map_mul, MvPolynomial.map_X, map_mul, MvPolynomial.eval_X]
    refine congrArg₂ (· * ·) hA ?_
    dsimp only [env]
    split_ifs with h
    · rfl
    · exact (h j.isLt).elim

private lemma liftPolyToMv_ne_zero {r : ℕ} {Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)}
    (hQ : Q ≠ 0) : liftPolyToMv Q ≠ 0 := by
  intro h0
  apply hQ
  refine MvPolynomial.ext _ _ fun α => ?_
  change Q.coeff α = 0
  apply Polynomial.funext
  intro u
  rw [Polynomial.eval_zero]
  have hev_all : evalU Q u = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_zero, ← eval_liftPolyToMv Q u v, h0, map_zero]
  have hc := congrArg (fun M : MvPolynomial (Fin (r + 1)) ℂ => M.coeff α) hev_all
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom] at hc
  exact hc

private lemma eval_congr_vars' {σ : Type*} (P : MvPolynomial σ ℂ) {f g : σ → ℂ}
    (h : ∀ i ∈ P.vars, f i = g i) : MvPolynomial.eval f P = MvPolynomial.eval g P := by
  classical
  rw [MvPolynomial.eval, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩)]

private lemma vars_poly_eval₂_C_X0 (q : Polynomial ℂ) :
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) q : MvPolynomial ℕ ℂ).vars ⊆ {0} := by
  classical
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add]
    exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset ha hb)
  | monomial k c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
    refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ?_ ?_)
    · rw [MvPolynomial.vars_C]; exact Finset.empty_subset _
    · exact (MvPolynomial.vars_pow _ _).trans (by rw [MvPolynomial.vars_X])

private lemma vars_liftPolyToMv_subset {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    (liftPolyToMv Q).vars ⊆ insert 0 (Finset.image (fun m : Fin (r + 1) => m.val + 1) Finset.univ) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C p =>
    intro x hx
    rw [liftPolyToMv, MvPolynomial.eval₂_C] at hx
    have hx0 := Finset.mem_singleton.mp (vars_poly_eval₂_C_X0 p hx)
    subst hx0
    exact Finset.mem_insert_self 0 _
  | add A B hA hB =>
    intro x hx
    rw [liftPolyToMv, MvPolynomial.eval₂_add] at hx
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hx) with h1 | h2
    · exact hA h1
    · exact hB h2
  | mul_X A m hA =>
    intro x hx
    rw [liftPolyToMv, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at hx
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hx) with h1 | h2
    · exact hA h1
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at h2
      subst h2
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩)

private lemma evalRatU_map_algebraMap {N : ℕ} (R : MvPolynomial (Fin (N + 1)) ℂ) (u : ℂ) :
    evalRatU (MvPolynomial.map (algebraMap ℂ (RatFunc ℂ)) R) u = R := by
  classical
  let Rrat : MvPolynomial (Fin (N + 1)) (RatFunc ℂ) := MvPolynomial.map (algebraMap ℂ (RatFunc ℂ)) R
  change evalRatU Rrat u = R
  ext α
  rw [evalRatU, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  have hcoeff : ∀ β, Rrat.coeff β = algebraMap ℂ (RatFunc ℂ) (R.coeff β) := fun β =>
    MvPolynomial.coeff_map (algebraMap ℂ (RatFunc ℂ)) R β
  have hratC : ∀ c : ℂ, ratEval (algebraMap ℂ (RatFunc ℂ) c) u = c := fun c => by
    have h1 : algebraMap ℂ (RatFunc ℂ) c = RatFunc.C c := rfl
    rw [h1, ratEval, RatFunc.num_C, RatFunc.denom_C, Polynomial.eval_C, Polynomial.eval_one, div_one]
  by_cases hα : α ∈ Rrat.support
  · rw [Finset.sum_eq_single α]
    · simp only [↓reduceIte]; rw [hcoeff α, hratC]
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have h0 : Rrat.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hcoeff α] at h0
    have hR0 : R.coeff α = 0 := (algebraMap ℂ (RatFunc ℂ)).injective (h0.trans (map_zero _).symm)
    rw [hR0]
    refine Finset.sum_eq_zero fun β hβ => ?_
    rw [ite_eq_right_iff]; intro hβα; subst hβα; exact absurd hβ hα

/-- **General Constant-Coefficient Linear Differential Operator Preservation Theorem**:
If `f : ℝ → ℂ` is real-analytic on `(0, ∞)`, `P ∈ ℂ[X]` is any nonzero polynomial, and
`g = constCoeffLinDiffOp P f = ∑_{j=0}^d P_j f^{(j)}` satisfies a nonzero `ℂ[t]`-ADE on `(0, ∞)`,
then `f` itself satisfies a nonzero autonomous polynomial differential equation over `ℂ` on `(0, ∞)`! -/
theorem constCoeffLinDiffOp_ade_transfer {f : ℝ → ℂ}
    (hf : AnalyticOnNhd ℝ f (Set.Ioi 0))
    (P : Polynomial ℂ) (hP_ne : P ≠ 0)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hQ_ne : Q ≠ 0)
    (hQ : ∀ t : ℝ, 0 < t →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (constCoeffLinDiffOp P f) t)
        (evalU Q (t : ℂ)) = 0) :
    ∃ (N : ℕ) (R : MvPolynomial (Fin (N + 1)) ℂ), R ≠ 0 ∧
      ∀ t : ℝ, 0 < t →
        MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f t) R = 0 := by
  classical
  let g : ℝ → ℂ := constCoeffLinDiffOp P f
  have hg_an : AnalyticOnNhd ℝ g (Set.Ioi 0) := constCoeffLinDiffOp_analyticOn hf P
  let y : ℕ → ℝ → ℂ := fun i t =>
    match i with
    | 0 => (t : ℂ)
    | k + 1 => iteratedDeriv k g t
  have hQ_mv_zero : ∀ t ∈ Set.Ioi (0 : ℝ), MvPolynomial.eval (fun i => y i t) (liftPolyToMv Q) = 0 := by
    intro t ht
    have hev := eval_liftPolyToMv Q (t : ℂ) (fun j : Fin (r + 1) => iteratedDeriv j.val g t)
    have hcongr : MvPolynomial.eval (fun i => y i t) (liftPolyToMv Q) =
        MvPolynomial.eval (fun i : ℕ => match i with | 0 => (t : ℂ) | j + 1 => if h : j < r + 1 then iteratedDeriv j g t else 0)
          (liftPolyToMv Q) := by
      refine eval_congr_vars' (liftPolyToMv Q) fun i hi => ?_
      cases i with
      | zero => rfl
      | succ j =>
        have hmem := vars_liftPolyToMv_subset Q hi
        simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hmem
        have hj : j < r + 1 := by
          rcases hmem with h0 | ⟨m, hm⟩
          · omega
          · have : m.val = j := by omega
            rw [← this]; exact m.isLt
        simp [y, hj]
    rw [hcongr, hev]
    exact hQ t ht
  obtain ⟨n, Q₀, t₀, ht₀, hord, hident⟩ :=
    ordinary_relation (Set.Ioi (0 : ℝ)) ⟨1, zero_lt_one⟩ y ⟨liftPolyToMv Q, liftPolyToMv_ne_zero hQ_ne, hQ_mv_zero⟩
  let v : Fin (n + 1) → ℝ → ℂ := fun i t => y i.val t
  let gv : Fin (n + 1) → ℝ → ℂ := fun i t => MvPolynomial.eval (fun j => v j t) (MvPolynomial.pderiv i Q₀)
  let top : Fin (n + 1) := Fin.last n
  let S : ℝ → ℂ := gv top
  have hv_an : ∀ (i : Fin (n + 1)) (t : ℝ), 0 < t → AnalyticAt ℝ (v i) t := by
    intro i t ht
    rcases i with ⟨iv, hiv⟩
    cases iv with
    | zero => exact Complex.ofRealCLM.analyticAt t
    | succ k => exact analyticOnNhd_iteratedDeriv_Ioi' hg_an k t ht
  have hv0_deriv : ∀ t : ℝ, HasDerivAt (v ⟨0, Nat.succ_pos n⟩) (1 : ℂ) t := fun t => by
    change HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) t
    simpa using (hasDerivAt_id t).ofReal_comp
  have hv_succ_deriv : ∀ (k : ℕ) (hk : k + 1 < n + 1) (t : ℝ), 0 < t →
      HasDerivAt (v ⟨k + 1, hk⟩) (y (k + 2) t) t := fun k _ t ht => by
    change HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g t) t
    rw [iteratedDeriv_succ]
    exact (analyticOnNhd_iteratedDeriv_Ioi' hg_an k t ht).differentiableAt.hasDerivAt
  have hchain : ∀ (A : MvPolynomial (Fin (n + 1)) ℂ) (t : ℝ), 0 < t →
      HasDerivAt (fun x => MvPolynomial.eval (fun i => v i x) A)
        (∑ i : Fin (n + 1), MvPolynomial.eval (fun j => v j t) (MvPolynomial.pderiv i A) *
          _root_.deriv (v i) t) t := fun A t ht =>
    polynomial_chain A v (fun i => _root_.deriv (v i)) t fun i =>
      (hv_an i t ht).differentiableAt.hasDerivAt
  have hvanish : ∀ t : ℝ, 0 < t → ∑ i : Fin (n + 1), gv i t * _root_.deriv (v i) t = 0 := by
    intro t ht
    have hnear : (fun x => MvPolynomial.eval (fun i => v i x) Q₀) =ᶠ[𝓝 t] (fun _ => 0) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) fun x hx => hident x hx
    exact (hchain Q₀ t ht).deriv.symm.trans (hnear.deriv_eq.trans (deriv_const _ _))
  have hn_pos : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have he := hvanish t₀ ht₀
    change ∑ i : Fin 1, gv i t₀ * _root_.deriv (v i) t₀ = 0 at he
    rw [Fin.sum_univ_one, (hv0_deriv t₀).deriv, mul_one] at he
    exact hord he
  have hS_an : AnalyticAt ℝ S t₀ := by
    have heval : ∀ (A : MvPolynomial (Fin (n + 1)) ℂ), AnalyticAt ℝ (fun x => MvPolynomial.eval (fun j => v j x) A) t₀ := by
      intro A
      induction A using MvPolynomial.induction_on with
      | C a => simpa using analyticAt_const
      | add a b ha hb => simpa only [map_add] using ha.fun_add hb
      | mul_X a j ha => simpa only [map_mul, MvPolynomial.eval_X] using ha.fun_mul (hv_an j t₀ ht₀)
    exact heval (MvPolynomial.pderiv top Q₀)
  have hS_ne : ∀ᶠ t in 𝓝 t₀, S t ≠ 0 := hS_an.continuousAt.eventually_ne hord
  let d : ℕ := P.natDegree
  have hPd_ne : P.coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
  let ι := Fin (n + 1) ⊕ Unit ⊕ Fin d
  let U : ι → ℝ → ℂ := fun idx t =>
    match idx with
    | Sum.inl i => v i t
    | Sum.inr (Sum.inl ()) => (S t)⁻¹
    | Sum.inr (Sum.inr k) => iteratedDeriv k.val f t
  have hgen_v : ∀ i : Fin (n + 1), Generated U t₀ (v i) := fun i => Generated.coord (Sum.inl i)
  have hgen_Sinv : Generated U t₀ (fun t => (S t)⁻¹) := Generated.coord (Sum.inr (Sum.inl ()))
  have hgen_f : ∀ k : Fin d, Generated U t₀ (iteratedDeriv k.val f) := fun k =>
    Generated.coord (Sum.inr (Sum.inr k))
  have hgen_gv : ∀ i : Fin (n + 1), Generated U t₀ (gv i) := fun i =>
    Generated.evalPoly v hgen_v (MvPolynomial.pderiv i Q₀)
  have hgen_dv_lt : ∀ (i : Fin (n + 1)), i ≠ top → Generated U t₀ (_root_.deriv (v i)) := by
    intro i hi
    rcases i with ⟨iv, hiv⟩
    cases iv with
    | zero =>
      refine (Generated.const (u := U) (x := t₀) (1 : ℂ)).congr ?_
      filter_upwards with t
      exact (hv0_deriv t).deriv.symm
    | succ k =>
      have hk_lt : k + 2 < n + 1 := by
        have hne : k + 1 ≠ n := fun h => hi (Fin.ext h)
        omega
      refine (hgen_v ⟨k + 2, hk_lt⟩).congr ?_
      filter_upwards [Ioi_mem_nhds ht₀] with t ht
      exact (hv_succ_deriv k hiv t ht).deriv.symm
  have hgen_dv_top : Generated U t₀ (_root_.deriv (v top)) := by
    have hsum_gen : Generated U t₀ (fun t =>
        -(S t)⁻¹ * ∑ i ∈ Finset.univ.erase top, gv i t * _root_.deriv (v i) t) := by
      have h1 : Generated U t₀ (fun t => -(S t)⁻¹) := by
        have := (Generated.const (u := U) (x := t₀) (-1 : ℂ)).mul hgen_Sinv
        exact this.congr (Filter.Eventually.of_forall fun t => by simp)
      have h2 : Generated U t₀ (fun t => ∑ i ∈ Finset.univ.erase top, gv i t * _root_.deriv (v i) t) :=
        (Generated.finsetSum (Finset.univ.erase top) (fun i t => gv i t * _root_.deriv (v i) t)
          fun i hi => (hgen_gv i).mul (hgen_dv_lt i (Finset.mem_erase.mp hi).1)).congr
          (Filter.Eventually.of_forall fun t => Finset.sum_apply t _ _)
      exact h1.mul h2
    refine hsum_gen.congr ?_
    filter_upwards [Ioi_mem_nhds ht₀, hS_ne] with t ht hSt
    have hv0 := hvanish t ht
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at hv0
    change S t * _root_.deriv (v top) t + ∑ i ∈ Finset.univ.erase top, gv i t * _root_.deriv (v i) t = 0 at hv0
    have heq : _root_.deriv (v top) t = -(S t)⁻¹ * ∑ i ∈ Finset.univ.erase top, gv i t * _root_.deriv (v i) t := by
      field_simp [hSt]
      linear_combination hv0
    exact heq.symm
  have hgen_dv_all : ∀ i : Fin (n + 1), Generated U t₀ (_root_.deriv (v i)) := fun i => by
    by_cases hi : i = top
    · subst hi; exact hgen_dv_top
    · exact hgen_dv_lt i hi
  have hsmooth : ∀ᶠ t in 𝓝 t₀, ∀ idx : ι, DifferentiableAt ℝ (U idx) t := by
    filter_upwards [Ioi_mem_nhds ht₀, hS_ne, hS_an.eventually_analyticAt] with t ht hSt hSan
    rintro (i | ⟨⟨⟩⟩ | k)
    · exact (hv_an i t ht).differentiableAt
    · exact hSan.differentiableAt.fun_inv hSt
    · exact (analyticOnNhd_iteratedDeriv_Ioi' hf k.val t ht).differentiableAt
  have hclosed : ∀ idx : ι, Generated U t₀ (_root_.deriv (U idx)) := by
    rintro (i | ⟨⟨⟩⟩ | k)
    · exact hgen_dv_all i
    · have hS_deriv_gen : Generated U t₀ (_root_.deriv S) := by
        have hsum := Generated.finsetSum Finset.univ
          (fun i t => MvPolynomial.eval (fun j => v j t) (MvPolynomial.pderiv i (MvPolynomial.pderiv top Q₀)) *
            _root_.deriv (v i) t)
          fun i _ => (Generated.evalPoly v hgen_v _).mul (hgen_dv_all i)
        refine hsum.congr ?_
        filter_upwards [Ioi_mem_nhds ht₀] with t ht
        simpa only [Finset.sum_apply] using (hchain (MvPolynomial.pderiv top Q₀) t ht).deriv.symm
      have hgen_inv_d : Generated U t₀ (fun t => -((S t)⁻¹ ^ 2) * _root_.deriv S t) := by
        have hneg : Generated U t₀ (fun t => -((S t)⁻¹ ^ 2)) := by
          have := (Generated.const (u := U) (x := t₀) (-1 : ℂ)).mul (hgen_Sinv.pow 2)
          exact this.congr (Filter.Eventually.of_forall fun t => by simp)
        exact hneg.mul hS_deriv_gen
      refine hgen_inv_d.congr ?_
      filter_upwards [hS_ne, hS_an.eventually_analyticAt] with t hSt hSan
      change -((S t)⁻¹ ^ 2) * _root_.deriv S t = _root_.deriv (fun w => (S w)⁻¹) t
      have hd := hSan.differentiableAt.hasDerivAt.fun_inv hSt
      rw [hd.deriv]
      field_simp [hSt]
    · by_cases hk : k.val + 1 < d
      · refine (hgen_f ⟨k.val + 1, hk⟩).congr ?_
        filter_upwards with t
        change iteratedDeriv (k.val + 1) f t = _root_.deriv (iteratedDeriv k.val f) t
        rw [iteratedDeriv_succ]
      · have hkd : k.val + 1 = d := by omega
        have htop_gen : Generated U t₀ (fun t =>
            (P.coeff d)⁻¹ * (v ⟨1, by omega⟩ t - ∑ j : Fin d, P.coeff j.val * iteratedDeriv j.val f t)) := by
          have hsum : Generated U t₀ (fun t => ∑ j : Fin d, P.coeff j.val * iteratedDeriv j.val f t) :=
            (Generated.finsetSum Finset.univ (fun j : Fin d => fun t => P.coeff j.val * iteratedDeriv j.val f t)
              fun j _ => (Generated.const (P.coeff j.val)).mul (hgen_f j)).congr
              (Filter.Eventually.of_forall fun t => Finset.sum_apply t _ _)
          exact (Generated.const (P.coeff d)⁻¹).mul ((hgen_v ⟨1, by omega⟩).sub hsum)
        refine htop_gen.congr ?_
        filter_upwards with t
        change (P.coeff d)⁻¹ * (g t - ∑ j : Fin d, P.coeff j.val * iteratedDeriv j.val f t) =
          _root_.deriv (iteratedDeriv k.val f) t
        rw [← iteratedDeriv_succ, hkd]
        have hg_eq : g t = (∑ j : Fin d, P.coeff j.val * iteratedDeriv j.val f t) +
            P.coeff d * iteratedDeriv d f t := by
          dsimp only [g, constCoeffLinDiffOp, d]
          rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
        rw [hg_eq]
        field_simp [hPd_ne]
        ring
  have hreadout : Generated U t₀ f := by
    by_cases hd0 : d = 0
    · have hf_gen : Generated U t₀ (fun t => (P.coeff 0)⁻¹ * v ⟨1, by omega⟩ t) :=
        (Generated.const (P.coeff 0)⁻¹).mul (hgen_v ⟨1, by omega⟩)
      refine hf_gen.congr ?_
      filter_upwards with t
      change (P.coeff 0)⁻¹ * g t = f t
      have hg_eq : g t = P.coeff 0 * f t := by
        dsimp only [g, constCoeffLinDiffOp]
        have : P.natDegree = 0 := hd0
        rw [this]; simp
      rw [hg_eq, inv_mul_cancel_left₀ (hd0 ▸ hPd_ne)]
    · have h0lt : 0 < d := Nat.pos_of_ne_zero hd0
      exact (hgen_f ⟨0, h0lt⟩).congr (Filter.Eventually.of_forall fun _ => by simp)
  obtain ⟨R, hR_ne, hR_loc⟩ := autonomous_readout U t₀ f hreadout hsmooth hclosed
  refine ⟨Fintype.card ι, R, hR_ne, ?_⟩
  have hana_R := mvPoly_eval_iteratedDeriv_analyticOn hf R
  have heq := hana_R.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_Ioi (0 : ℝ)).isPreconnected ht₀ (hR_loc.filter_mono nhdsWithin_le_nhds).frequently
  intro t ht
  exact heq ht

/-- **Contrapositive Constant-Coefficient Linear Differential Operator D-Transcendence Preservation (`ℂ(t)`-ADE)**:
If `f` is real-analytic on `(0, ∞)` and satisfies NO nonzero `ℂ(t)`-ADE on `𝓝[>] 0`, then for ANY
nonzero constant-coefficient differential polynomial `P`, `constCoeffLinDiffOp P f` also satisfies
NO nonzero `ℂ(t)`-ADE on `𝓝[>] 0`! -/
theorem dTrans_of_constCoeffLinDiffOp {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f (Set.Ioi 0))
    (hf_no_ade : ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f t) (evalRatU P (t : ℂ)) = 0) →
      P = 0)
    (L : Polynomial ℂ) (hL : L ≠ 0)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (constCoeffLinDiffOp L f) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 := by
  by_contra hP_ne
  obtain ⟨Q, hQ_ne, hQ_zero⟩ :=
    ratADE_nhdsGT_to_polyADE_Ioi (constCoeffLinDiffOp_analyticOn hf L) P hP_ne hP
  obtain ⟨N, R, hR_ne, hR_zero⟩ := constCoeffLinDiffOp_ade_transfer hf L hL Q hQ_ne hQ_zero
  let Rrat : MvPolynomial (Fin (N + 1)) (RatFunc ℂ) := MvPolynomial.map (algebraMap ℂ (RatFunc ℂ)) R
  have hRrat_ne : Rrat ≠ 0 := by
    intro h0
    apply hR_ne
    exact (MvPolynomial.map_injective (algebraMap ℂ (RatFunc ℂ))
      (algebraMap ℂ (RatFunc ℂ)).injective) (h0.trans (map_zero _).symm)
  exact hRrat_ne (hf_no_ade Rrat (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => by
    rw [evalRatU_map_algebraMap]; exact hR_zero t ht))

/-- **Variable-Inversion Transfer (`t = 1 / u`, `M(u) = (2 / u²) (f(1/u) - u/2)`)**:
If `f : ℝ → ℂ` is real-analytic on `(0, ∞)` and satisfies a nonzero `ℂ(t)`-ADE on `𝓝[>] 0`, then
`M u = (2 : ℂ) / (u : ℂ) ^ 2 * (f (1 / u) - (u : ℂ) / 2)` satisfies a nonzero `ℂ(u)`-ADE
eventually as `u → +∞`! -/
theorem invVar_ade_transfer {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f (Set.Ioi 0))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) (hP_ne : P ≠ 0)
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f t) (evalRatU P (t : ℂ)) = 0) :
    ∃ (N : ℕ) (R : MvPolynomial (Fin (N + 1)) (RatFunc ℂ)), R ≠ 0 ∧
      ∀ᶠ u : ℝ in Filter.atTop,
        MvPolynomial.eval
          (fun j : Fin (N + 1) =>
            iteratedDeriv j.val (fun x : ℝ => (2 : ℂ) / (x : ℂ) ^ 2 * (f (1 / x) - (x : ℂ) / 2)) u)
          (evalRatU R (u : ℂ)) = 0 := by
  classical
  obtain ⟨Q, hQ_ne, hQ⟩ := ratADE_nhdsGT_to_polyADE_Ioi hf P hP_ne hP
  let y : ℕ → ℝ → ℂ := fun i t =>
    match i with
    | 0 => (t : ℂ)
    | k + 1 => iteratedDeriv k f t
  have hQ_mv_zero : ∀ t ∈ Set.Ioi (0 : ℝ), MvPolynomial.eval (fun i => y i t) (liftPolyToMv Q) = 0 := by
    intro t ht
    have hev := eval_liftPolyToMv Q (t : ℂ) (fun j : Fin (r + 1) => iteratedDeriv j.val f t)
    have hcongr : MvPolynomial.eval (fun i => y i t) (liftPolyToMv Q) =
        MvPolynomial.eval (fun i : ℕ => match i with | 0 => (t : ℂ) | j + 1 => if h : j < r + 1 then iteratedDeriv j f t else 0)
          (liftPolyToMv Q) := by
      refine eval_congr_vars' (liftPolyToMv Q) fun i hi => ?_
      cases i with
      | zero => rfl
      | succ j =>
        have hmem := vars_liftPolyToMv_subset Q hi
        simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hmem
        have hj : j < r + 1 := by
          rcases hmem with h0 | ⟨m, hm⟩
          · omega
          · have : m.val = j := by omega
            rw [← this]; exact m.isLt
        simp [y, hj]
    rw [hcongr, hev]
    exact hQ t ht
  obtain ⟨n, Q₀, t₀, ht₀, hord, hident⟩ :=
    ordinary_relation (Set.Ioi (0 : ℝ)) ⟨1, zero_lt_one⟩ y ⟨liftPolyToMv Q, liftPolyToMv_ne_zero hQ_ne, hQ_mv_zero⟩
  let v : Fin (n + 1) → ℝ → ℂ := fun i t => y i.val t
  let gv : Fin (n + 1) → ℝ → ℂ := fun i t => MvPolynomial.eval (fun j => v j t) (MvPolynomial.pderiv i Q₀)
  let top : Fin (n + 1) := Fin.last n
  let S : ℝ → ℂ := gv top
  have hv_an : ∀ (i : Fin (n + 1)) (t : ℝ), 0 < t → AnalyticAt ℝ (v i) t := by
    intro i t ht
    rcases i with ⟨iv, hiv⟩
    cases iv with
    | zero => exact Complex.ofRealCLM.analyticAt t
    | succ k => exact analyticOnNhd_iteratedDeriv_Ioi' hf k t ht
  have hv0_deriv : ∀ t : ℝ, HasDerivAt (v ⟨0, Nat.succ_pos n⟩) (1 : ℂ) t := fun t => by
    change HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) t
    simpa using (hasDerivAt_id t).ofReal_comp
  have hv_succ_deriv : ∀ (k : ℕ) (hk : k + 1 < n + 1) (t : ℝ), 0 < t →
      HasDerivAt (v ⟨k + 1, hk⟩) (y (k + 2) t) t := fun k _ t ht => by
    change HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t
    rw [iteratedDeriv_succ]
    exact (analyticOnNhd_iteratedDeriv_Ioi' hf k t ht).differentiableAt.hasDerivAt
  have hchain : ∀ (A : MvPolynomial (Fin (n + 1)) ℂ) (t : ℝ), 0 < t →
      HasDerivAt (fun x => MvPolynomial.eval (fun i => v i x) A)
        (∑ i : Fin (n + 1), MvPolynomial.eval (fun j => v j t) (MvPolynomial.pderiv i A) *
          _root_.deriv (v i) t) t := fun A t ht =>
    polynomial_chain A v (fun i => _root_.deriv (v i)) t fun i =>
      (hv_an i t ht).differentiableAt.hasDerivAt
  have hvanish : ∀ t : ℝ, 0 < t → ∑ i : Fin (n + 1), gv i t * _root_.deriv (v i) t = 0 := by
    intro t ht
    have hnear : (fun x => MvPolynomial.eval (fun i => v i x) Q₀) =ᶠ[𝓝 t] (fun _ => 0) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) fun x hx => hident x hx
    exact (hchain Q₀ t ht).deriv.symm.trans (hnear.deriv_eq.trans (deriv_const _ _))
  have hn_pos : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have he := hvanish t₀ ht₀
    change ∑ i : Fin 1, gv i t₀ * _root_.deriv (v i) t₀ = 0 at he
    rw [Fin.sum_univ_one, (hv0_deriv t₀).deriv, mul_one] at he
    exact hord he
  let u₀ : ℝ := 1 / t₀
  have hu₀_pos : 0 < u₀ := div_pos one_pos ht₀
  have hinv_u₀ : 1 / u₀ = t₀ := one_div_one_div t₀
  have hinv_an : ∀ x : ℝ, 0 < x → AnalyticAt ℝ (fun w : ℝ => 1 / w) x := fun x hx =>
    analyticAt_const.div analyticAt_id hx.ne'
  have hinv_deriv : ∀ x : ℝ, 0 < x → HasDerivAt (fun w : ℝ => 1 / w) (-(1 / x ^ 2)) x := fun x hx => by
    have := hasDerivAt_inv hx.ne'
    convert this using 1
    · funext w; rw [one_div]
    · ring
  have hS_an : ∀ t : ℝ, 0 < t → AnalyticAt ℝ S t := fun t ht => by
    have heval : ∀ (A : MvPolynomial (Fin (n + 1)) ℂ), AnalyticAt ℝ (fun x => MvPolynomial.eval (fun j => v j x) A) t := by
      intro A
      induction A using MvPolynomial.induction_on with
      | C a => simpa using analyticAt_const
      | add a b ha hb => simpa only [map_add] using ha.fun_add hb
      | mul_X a j ha => simpa only [map_mul, MvPolynomial.eval_X] using ha.fun_mul (hv_an j t ht)
    exact heval (MvPolynomial.pderiv top Q₀)
  have hS_comp_an : AnalyticAt ℝ (fun x : ℝ => S (1 / x)) u₀ :=
    (hinv_u₀.symm ▸ hS_an t₀ ht₀).comp (hinv_an u₀ hu₀_pos)
  have hS_comp_ne : ∀ᶠ x in 𝓝 u₀, S (1 / x) ≠ 0 :=
    hS_comp_an.continuousAt.eventually_ne (by rwa [hinv_u₀])
  let ι := Fin (n + 1) ⊕ Unit
  let U : ι → ℝ → ℂ := fun idx x =>
    match idx with
    | Sum.inl i => v i (1 / x)
    | Sum.inr () => (S (1 / x))⁻¹
  have hgen_v : ∀ i : Fin (n + 1), Generated U u₀ (fun x => v i (1 / x)) := fun i =>
    Generated.coord (Sum.inl i)
  have hgen_Sinv : Generated U u₀ (fun x => (S (1 / x))⁻¹) := Generated.coord (Sum.inr ())
  have hgen_xinv : Generated U u₀ (fun x : ℝ => (x : ℂ)⁻¹) := by
    refine (hgen_v ⟨0, Nat.succ_pos n⟩).congr ?_
    filter_upwards with x
    simp [v, y]
  have hgen_gv : ∀ i : Fin (n + 1), Generated U u₀ (fun x => gv i (1 / x)) := fun i =>
    Generated.evalPoly (fun j x => v j (1 / x)) hgen_v (MvPolynomial.pderiv i Q₀)
  have hgen_dv_lt : ∀ (i : Fin (n + 1)), i ≠ top → Generated U u₀ (fun x => _root_.deriv (v i) (1 / x)) := by
    intro i hi
    rcases i with ⟨iv, hiv⟩
    cases iv with
    | zero =>
      refine (Generated.const (u := U) (x := u₀) (1 : ℂ)).congr ?_
      filter_upwards with x
      exact (hv0_deriv (1 / x)).deriv.symm
    | succ k =>
      have hk_lt : k + 2 < n + 1 := by
        have hne : k + 1 ≠ n := fun h => hi (Fin.ext h)
        omega
      refine (hgen_v ⟨k + 2, hk_lt⟩).congr ?_
      filter_upwards [Ioi_mem_nhds hu₀_pos] with x hx
      exact (hv_succ_deriv k hiv (1 / x) (div_pos one_pos hx)).deriv.symm
  have hgen_dv_top : Generated U u₀ (fun x => _root_.deriv (v top) (1 / x)) := by
    have hsum_gen : Generated U u₀ (fun x =>
        -(S (1 / x))⁻¹ * ∑ i ∈ Finset.univ.erase top, gv i (1 / x) * _root_.deriv (v i) (1 / x)) := by
      have h1 : Generated U u₀ (fun x => -(S (1 / x))⁻¹) := by
        have := (Generated.const (u := U) (x := u₀) (-1 : ℂ)).mul hgen_Sinv
        exact this.congr (Filter.Eventually.of_forall fun x => by simp)
      have h2 : Generated U u₀ (fun x => ∑ i ∈ Finset.univ.erase top, gv i (1 / x) * _root_.deriv (v i) (1 / x)) :=
        (Generated.finsetSum (Finset.univ.erase top) (fun i x => gv i (1 / x) * _root_.deriv (v i) (1 / x))
          fun i hi => (hgen_gv i).mul (hgen_dv_lt i (Finset.mem_erase.mp hi).1)).congr
          (Filter.Eventually.of_forall fun x => Finset.sum_apply x _ _)
      exact h1.mul h2
    refine hsum_gen.congr ?_
    filter_upwards [Ioi_mem_nhds hu₀_pos, hS_comp_ne] with x hx hSx
    have hv0 := hvanish (1 / x) (div_pos one_pos hx)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at hv0
    change S (1 / x) * _root_.deriv (v top) (1 / x) +
      ∑ i ∈ Finset.univ.erase top, gv i (1 / x) * _root_.deriv (v i) (1 / x) = 0 at hv0
    have heq : _root_.deriv (v top) (1 / x) =
        -(S (1 / x))⁻¹ * ∑ i ∈ Finset.univ.erase top, gv i (1 / x) * _root_.deriv (v i) (1 / x) := by
      field_simp [hSx]
      linear_combination hv0
    exact heq.symm
  have hgen_dv_all : ∀ i : Fin (n + 1), Generated U u₀ (fun x => _root_.deriv (v i) (1 / x)) := fun i => by
    by_cases hi : i = top
    · subst hi; exact hgen_dv_top
    · exact hgen_dv_lt i hi
  have hgen_neg_sq : Generated U u₀ (fun x : ℝ => -((x : ℂ)⁻¹ ^ 2)) := by
    have := (Generated.const (u := U) (x := u₀) (-1 : ℂ)).mul (hgen_xinv.pow 2)
    exact this.congr (Filter.Eventually.of_forall fun x => by simp)
  have hsmooth : ∀ᶠ x in 𝓝 u₀, ∀ idx : ι, DifferentiableAt ℝ (U idx) x := by
    filter_upwards [Ioi_mem_nhds hu₀_pos, hS_comp_ne, hS_comp_an.eventually_analyticAt] with x hx hSx hSan
    rintro (i | ⟨⟩)
    · exact ((hv_an i (1 / x) (div_pos one_pos hx)).comp (hinv_an x hx)).differentiableAt
    · exact hSan.differentiableAt.fun_inv hSx
  have hclosed : ∀ idx : ι, Generated U u₀ (_root_.deriv (U idx)) := by
    rintro (i | ⟨⟩)
    · refine (hgen_neg_sq.mul (hgen_dv_all i)).congr ?_
      filter_upwards [Ioi_mem_nhds hu₀_pos] with x hx
      change -((x : ℂ)⁻¹ ^ 2) * _root_.deriv (v i) (1 / x) = _root_.deriv (fun w => v i (1 / w)) x
      have hd1 := (hv_an i (1 / x) (div_pos one_pos hx)).differentiableAt.hasDerivAt
      have hd : HasDerivAt (fun w : ℝ => v i (1 / w))
          ((-(1 / x ^ 2) : ℝ) • _root_.deriv (v i) (1 / x)) x :=
        hd1.scomp x (hinv_deriv x hx)
      rw [hd.deriv, Complex.real_smul]
      push_cast; simp only [inv_pow, one_div]
    · have hS_deriv_gen : Generated U u₀ (fun x => _root_.deriv S (1 / x)) := by
        have hsum := Generated.finsetSum Finset.univ
          (fun i x => MvPolynomial.eval (fun j => v j (1 / x))
            (MvPolynomial.pderiv i (MvPolynomial.pderiv top Q₀)) * _root_.deriv (v i) (1 / x))
          fun i _ => (Generated.evalPoly (fun j x => v j (1 / x)) hgen_v _).mul (hgen_dv_all i)
        refine hsum.congr ?_
        filter_upwards [Ioi_mem_nhds hu₀_pos] with x hx
        simpa only [Finset.sum_apply] using (hchain (MvPolynomial.pderiv top Q₀) (1 / x) (div_pos one_pos hx)).deriv.symm
      have hgen_inv_d : Generated U u₀ (fun x =>
          -((S (1 / x))⁻¹ ^ 2) * (-((x : ℂ)⁻¹ ^ 2) * _root_.deriv S (1 / x))) := by
        have hneg : Generated U u₀ (fun x => -((S (1 / x))⁻¹ ^ 2)) := by
          have := (Generated.const (u := U) (x := u₀) (-1 : ℂ)).mul (hgen_Sinv.pow 2)
          exact this.congr (Filter.Eventually.of_forall fun x => by simp)
        exact hneg.mul (hgen_neg_sq.mul hS_deriv_gen)
      refine hgen_inv_d.congr ?_
      filter_upwards [Ioi_mem_nhds hu₀_pos, hS_comp_ne] with x hx hSx
      change -((S (1 / x))⁻¹ ^ 2) * (-((x : ℂ)⁻¹ ^ 2) * _root_.deriv S (1 / x)) =
        _root_.deriv (fun w => (S (1 / w))⁻¹) x
      have hdS : HasDerivAt (fun w : ℝ => S (1 / w))
          ((-(1 / x ^ 2) : ℝ) • _root_.deriv S (1 / x)) x :=
        (hS_an (1 / x) (div_pos one_pos hx)).differentiableAt.hasDerivAt.scomp x (hinv_deriv x hx)
      have hd := hdS.fun_inv hSx
      rw [hd.deriv, Complex.real_smul]
      push_cast; simp only [inv_pow, one_div]
      field_simp [hSx]
  let M : ℝ → ℂ := fun x => (2 : ℂ) / (x : ℂ) ^ 2 * (f (1 / x) - (x : ℂ) / 2)
  have hreadout : Generated U u₀ M := by
    have hgen_M : Generated U u₀ (fun x =>
        (2 : ℂ) * ((x : ℂ)⁻¹ ^ 2) * v ⟨1, by omega⟩ (1 / x) - (x : ℂ)⁻¹) :=
      ((Generated.const (2 : ℂ)).mul (hgen_xinv.pow 2)).mul (hgen_v ⟨1, by omega⟩) |>.sub hgen_xinv
    refine hgen_M.congr ?_
    filter_upwards [Ioi_mem_nhds hu₀_pos] with x hx
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    dsimp only [M, v, y]
    simp only [iteratedDeriv_zero]
    field_simp [hxC]
  obtain ⟨R, hR_ne, hR_loc⟩ := autonomous_readout U u₀ M hreadout hsmooth hclosed
  have hM_an : AnalyticOnNhd ℝ M (Set.Ioi 0) := fun x hx => by
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have h1 : AnalyticAt ℝ (fun w : ℝ => (2 : ℂ) / (w : ℂ) ^ 2) x :=
      analyticAt_const.div ((Complex.ofRealCLM.analyticAt x).pow 2) (pow_ne_zero 2 hxC)
    have h2 : AnalyticAt ℝ (fun w : ℝ => f (1 / w) - (w : ℂ) / 2) x :=
      ((hf (1 / x) (div_pos one_pos hx)).comp (hinv_an x hx)).sub
        ((Complex.ofRealCLM.analyticAt x).div analyticAt_const (by norm_num))
    exact h1.mul h2
  have hana_R := mvPoly_eval_iteratedDeriv_analyticOn hM_an R
  have hR_all : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (Fintype.card ι + 1) => iteratedDeriv j.val M x) R = 0 := by
    have heq := hana_R.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected hu₀_pos (hR_loc.filter_mono nhdsWithin_le_nhds).frequently
    intro x hx; exact heq hx
  let Rrat : MvPolynomial (Fin (Fintype.card ι + 1)) (RatFunc ℂ) :=
    MvPolynomial.map (algebraMap ℂ (RatFunc ℂ)) R
  have hRrat_ne : Rrat ≠ 0 := by
    intro h0
    apply hR_ne
    exact (MvPolynomial.map_injective (algebraMap ℂ (RatFunc ℂ))
      (algebraMap ℂ (RatFunc ℂ)).injective) (h0.trans (map_zero _).symm)
  refine ⟨Fintype.card ι, Rrat, hRrat_ne, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [evalRatU_map_algebraMap]
  exact hR_all u hu

/-! #### D.2 Canonical Base Heat Traces (`baseHeatInt`, `baseHeatHalf`) & Exact Scaling Identity -/

/-- Canonical integer-lattice base heat trace `H_{int}(t) = ∑_{u ≥ 1} u e^{-t u²}`. -/
@[expose] def baseHeatInt (t : ℝ) : ℂ :=
  ∑' u : ℕ, ((u + 1 : ℕ) : ℂ) * Complex.exp (-(t : ℂ) * ((u + 1 : ℕ) : ℂ) ^ 2)

/-- Canonical half-integer-lattice base heat trace `H_{1/2}(t) = ∑_{k ≥ 0} (k + 1/2) e^{-t (k + 1/2)²}`. -/
@[expose] def baseHeatHalf (t : ℝ) : ℂ :=
  ∑' k : ℕ, ((k : ℂ) + 1 / 2) * Complex.exp (-(t : ℂ) * ((k : ℂ) + 1 / 2) ^ 2)

private lemma summable_poly_mul_exp_sq {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (p : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + c) ^ p * Real.exp (-a * ((k : ℝ) + c) ^ 2)) := by
  have hr_pos : 0 < Real.exp (-(a * c)) := Real.exp_pos _
  have hr_lt : Real.exp (-(a * c)) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos ha hc))
  have hgeom : Summable (fun k : ℕ =>
      ((p.factorial : ℝ) / ((a * c / 2) ^ p) + 1) * (Real.exp (-(a * c / 2))) ^ k) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (half_pos (mul_pos ha hc))))).mul_left _
  refine hgeom.of_nonneg_of_le (fun k => by positivity) fun k => ?_
  have hkc : 0 < (k : ℝ) + c := by positivity
  have hsq : c * ((k : ℝ) + c) ≤ ((k : ℝ) + c) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hpow := Real.pow_div_factorial_le_exp ((a * c / 2) * ((k : ℝ) + c)) (by positivity) p
  have hfac_pos : (0 : ℝ) < (p.factorial : ℝ) := by positivity
  have hden_pos : (0 : ℝ) < (a * c / 2) ^ p := pow_pos (by positivity) p
  rw [mul_pow, div_le_iff₀ hfac_pos] at hpow
  have hterm : ((k : ℝ) + c) ^ p ≤ ((p.factorial : ℝ) / (a * c / 2) ^ p) *
      Real.exp ((a * c / 2) * ((k : ℝ) + c)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden_pos]
    nlinarith
  have hexp_split : Real.exp ((a * c / 2) * ((k : ℝ) + c)) * Real.exp (-a * ((k : ℝ) + c) ^ 2) ≤
      (Real.exp (-(a * c / 2))) ^ k := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hk_le : (k : ℝ) ≤ (k : ℝ) + c := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le, mul_le_mul_of_nonneg_left hk_le (half_pos (mul_pos ha hc)).le]
  calc ((k : ℝ) + c) ^ p * Real.exp (-a * ((k : ℝ) + c) ^ 2)
      ≤ ((p.factorial : ℝ) / (a * c / 2) ^ p) * Real.exp ((a * c / 2) * ((k : ℝ) + c)) *
          Real.exp (-a * ((k : ℝ) + c) ^ 2) :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_pos _).le
    _ = ((p.factorial : ℝ) / (a * c / 2) ^ p) *
          (Real.exp ((a * c / 2) * ((k : ℝ) + c)) * Real.exp (-a * ((k : ℝ) + c) ^ 2)) := by ring
    _ ≤ ((p.factorial : ℝ) / (a * c / 2) ^ p) * (Real.exp (-(a * c / 2))) ^ k :=
        mul_le_mul_of_nonneg_left hexp_split (by positivity)
    _ ≤ ((p.factorial : ℝ) / (a * c / 2) ^ p + 1) * (Real.exp (-(a * c / 2))) ^ k :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private lemma summable_heat_term {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (p : ℕ) :
    Summable (fun k : ℕ => (((k : ℝ) + c : ℝ) : ℂ) ^ p *
      Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) := by
  refine Summable.of_norm ?_
  refine (summable_poly_mul_exp_sq hc ht p).congr fun k => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp]
  congr 2
  have hsq : (((k : ℝ) + c : ℝ) : ℂ) ^ 2 = ((((k : ℝ) + c) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hsq, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Exact Scaling Identity Connecting the Two Canonical Base Heat Traces**:
For every `t > 0`, `baseHeatHalf t = (1 / 2) * baseHeatInt (t / 4) - baseHeatInt t`! -/
theorem baseHeatHalf_eq (t : ℝ) (ht : 0 < t) :
    baseHeatHalf t = (1 / 2 : ℂ) * baseHeatInt (t / 4) - baseHeatInt t := by
  let f : ℕ → ℂ := fun n =>
    ((n + 1 : ℕ) : ℂ) * Complex.exp (-((t / 4 : ℝ) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 2)
  have hf_sum : Summable f := by
    have h := summable_heat_term (c := (1 : ℝ)) (t := t / 4) one_pos (by positivity) 1
    refine h.congr fun n => ?_
    dsimp only [f]; push_cast; rw [pow_one]
  have heven : Summable (fun k : ℕ => f (2 * k)) :=
    hf_sum.comp_injective (fun a b h => by omega)
  have hodd : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hf_sum.comp_injective (fun a b h => by omega)
  have hsplit : baseHeatInt (t / 4) = (∑' k : ℕ, f (2 * k)) + (∑' k : ℕ, f (2 * k + 1)) :=
    (heven.hasSum.even_add_odd hodd.hasSum).tsum_eq
  have heven_eq : ∑' k : ℕ, f (2 * k) = 2 * baseHeatHalf t := by
    rw [baseHeatHalf, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    dsimp only [f]
    have h1 : ((2 * k + 1 : ℕ) : ℂ) = 2 * ((k : ℂ) + 1 / 2) := by push_cast; ring
    have h2 : -((t / 4 : ℝ) : ℂ) * ((2 * k + 1 : ℕ) : ℂ) ^ 2 = -(t : ℂ) * ((k : ℂ) + 1 / 2) ^ 2 := by
      rw [h1]; push_cast; ring
    rw [h2, h1]; ring
  have hodd_eq : ∑' k : ℕ, f (2 * k + 1) = 2 * baseHeatInt t := by
    rw [baseHeatInt, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    dsimp only [f]
    have h1 : ((2 * k + 1 + 1 : ℕ) : ℂ) = 2 * ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    have h2 : -((t / 4 : ℝ) : ℂ) * ((2 * k + 1 + 1 : ℕ) : ℂ) ^ 2 = -(t : ℂ) * ((k + 1 : ℕ) : ℂ) ^ 2 := by
      rw [h1]; push_cast; ring
    rw [h2, h1]; ring
  rw [hsplit, heven_eq, hodd_eq]
  ring

private lemma heatSum_holo {c : ℝ} (hc : 0 < c) (p : ℕ) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) ^ p *
        Complex.exp (-z * (((k : ℝ) + c : ℝ) : ℂ) ^ 2))
      {z : ℂ | 0 < z.re} := by
  intro z₀ hz₀
  change 0 < z₀.re at hz₀
  let r : ℝ := z₀.re / 2
  have hr_pos : 0 < r := half_pos hz₀
  have hball_re : ∀ z ∈ Metric.ball z₀ r, r < z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h1 := (abs_lt.mp (hre.trans_lt hz)).1
    dsimp only [r] at *; linarith
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) ^ p *
        Complex.exp (-z * (((k : ℝ) + c : ℝ) : ℂ) ^ 2))
      (Metric.ball z₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_poly_mul_exp_sq hc hr_pos p)
      (fun k => (differentiableOn_const _).mul
        ((differentiableOn_id.neg.mul (differentiableOn_const _)).cexp))
      Metric.isOpen_ball (fun k z hz => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp]
    have hre_eq : (-z * (((k : ℝ) + c : ℝ) : ℂ) ^ 2).re = -z.re * ((k : ℝ) + c) ^ 2 := by
      have hsq : (((k : ℝ) + c : ℝ) : ℂ) ^ 2 = ((((k : ℝ) + c) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hsq, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hre_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    nlinarith [hball_re z hz, sq_nonneg ((k : ℝ) + c)]
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))).differentiableWithinAt

private lemma heatSum_real_analyticOn {c : ℝ} (hc : 0 < c) (p : ℕ) :
    AnalyticOnNhd ℝ
      (fun t : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) ^ p *
        Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2))
      (Set.Ioi 0) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hC := (heatSum_holo hc p).analyticOnNhd hopen
  intro t ht
  exact ((hC (t : ℂ) (by simpa using ht)).restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)

private lemma hasDerivAt_heatSum {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (p : ℕ) :
    HasDerivAt
      (fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) ^ p *
        Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2))
      (∑' k : ℕ, -((((k : ℝ) + c : ℝ) : ℂ) ^ (p + 2) *
        Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2))) t := by
  let a : ℝ := t / 2
  have ha_pos : 0 < a := half_pos ht
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (k : ℕ) (x : ℝ) => (((k : ℝ) + c : ℝ) : ℂ) ^ p *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2))
    (g' := fun (k : ℕ) (x : ℝ) => -((((k : ℝ) + c : ℝ) : ℂ) ^ (p + 2) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)))
    (u := fun k : ℕ => ((k : ℝ) + c) ^ (p + 2) * Real.exp (-a * ((k : ℝ) + c) ^ 2))
    (t := Set.Ioi a) (y₀ := t) (y := t)
    (summable_poly_mul_exp_sq hc ha_pos (p + 2)) isOpen_Ioi (convex_Ioi a).isPreconnected
    (fun k x _ => ?_) (fun k x hx => ?_)
    (by change a < t; dsimp only [a]; linarith) (summable_heat_term hc ht p)
    (by change a < t; dsimp only [a]; linarith)
  · have hd1 : HasDerivAt (fun w : ℝ => -(w : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)
        (-((((k : ℝ) + c : ℝ) : ℂ) ^ 2)) x := by
      have h0 : HasDerivAt (fun w : ℝ => -(w : ℂ)) (-1 : ℂ) x :=
        (Complex.ofRealCLM.hasDerivAt (x := x)).neg
      simpa using h0.mul_const ((((k : ℝ) + c : ℝ) : ℂ) ^ 2)
    refine (hd1.cexp.const_mul ((((k : ℝ) + c : ℝ) : ℂ) ^ p)).congr_deriv ?_
    rw [pow_add]; ring
  · rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Complex.norm_exp]
    have hre_eq : (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2).re = -x * ((k : ℝ) + c) ^ 2 := by
      have hsq : (((k : ℝ) + c : ℝ) : ℂ) ^ 2 = ((((k : ℝ) + c) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hsq, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hax : a < x := hx
    nlinarith [sq_nonneg ((k : ℝ) + c)]

private lemma iteratedDeriv_heatSum {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∀ t : ℝ, 0 < t →
      iteratedDeriv m
        (fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) *
          Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) t =
      (-1 : ℂ) ^ m * ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1) *
        Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2) := by
  induction m with
  | zero => intro t _; simp
  | succ m ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m
        (fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) *
          Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) =ᶠ[𝓝 t]
        fun x : ℝ => (-1 : ℂ) ^ m * ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1) *
          Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact ih x hx
    rw [hev.deriv_eq, ((hasDerivAt_heatSum hc ht (2 * m + 1)).const_mul ((-1 : ℂ) ^ m)).deriv,
      tsum_neg, show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega, pow_succ]
    ring

lemma baseHeatInt_analyticOn : AnalyticOnNhd ℝ baseHeatInt (Set.Ioi 0) := by
  have heq : baseHeatInt = fun t : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 : ℝ) : ℂ) ^ 1 *
      Complex.exp (-(t : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) ^ 2) := by
    funext t; unfold baseHeatInt; refine tsum_congr fun k => ?_; push_cast; rw [pow_one]
  rw [heq]; exact heatSum_real_analyticOn one_pos 1

lemma baseHeatHalf_analyticOn : AnalyticOnNhd ℝ baseHeatHalf (Set.Ioi 0) := by
  have heq : baseHeatHalf = fun t : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 1 *
      Complex.exp (-(t : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2) := by
    funext t; unfold baseHeatHalf; refine tsum_congr fun k => ?_; push_cast; rw [pow_one]
  rw [heq]; exact heatSum_real_analyticOn (by norm_num) 1

lemma iteratedDeriv_baseHeatInt (m : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv m baseHeatInt t =
      (-1 : ℂ) ^ m * ∑' u : ℕ, ((u + 1 : ℕ) : ℂ) ^ (2 * m + 1) *
        Complex.exp (-(t : ℂ) * ((u + 1 : ℕ) : ℂ) ^ 2) := by
  have heq : baseHeatInt = fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 : ℝ) : ℂ) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) ^ 2) := by
    funext x; unfold baseHeatInt; refine tsum_congr fun k => ?_; push_cast; rfl
  rw [heq, iteratedDeriv_heatSum one_pos m t ht]
  congr 1; refine tsum_congr fun k => ?_; push_cast; rfl

lemma iteratedDeriv_baseHeatHalf (m : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv m baseHeatHalf t =
      (-1 : ℂ) ^ m * ∑' k : ℕ, ((k : ℂ) + 1 / 2) ^ (2 * m + 1) *
        Complex.exp (-(t : ℂ) * ((k : ℂ) + 1 / 2) ^ 2) := by
  have heq : baseHeatHalf = fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 / 2 : ℝ) : ℂ) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2) := by
    funext x; unfold baseHeatHalf; refine tsum_congr fun k => ?_; push_cast; rfl
  rw [heq, iteratedDeriv_heatSum (by norm_num) m t ht]
  congr 1; refine tsum_congr fun k => ?_; push_cast; rfl

/-! #### D.3 Exact Even-Dimensional CROSS Heat Traces & Dimension-Reduction Closure -/

/-- Constant-coefficient differential polynomial `∑_{m=0}^{deg Q / 2} (-1)^m Q_{2m+1} X^m`
encoding an odd multiplicity polynomial `Q(u) = ∑ Q_{2m+1} u^{2m+1}` in `(-∂_t)`. -/
@[expose] def heatDiffPoly (Q : Polynomial ℂ) : Polynomial ℂ :=
  ∑ m ∈ Finset.range (Q.natDegree / 2 + 1),
    Polynomial.C ((-1 : ℂ) ^ m * Q.coeff (2 * m + 1)) * Polynomial.X ^ m

private lemma coeff_heatDiffPoly (Q : Polynomial ℂ) (m : ℕ) :
    (heatDiffPoly Q).coeff m =
      if m ≤ Q.natDegree / 2 then (-1 : ℂ) ^ m * Q.coeff (2 * m + 1) else 0 := by
  unfold heatDiffPoly
  rw [poly_finset_sum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hm : m ≤ Q.natDegree / 2
  · rw [ite_eq_left_iff.mpr (fun h => (h hm).elim), Finset.sum_eq_single m]
    · simp
    · intro k _ hkm; simp [Ne.symm hkm]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [ite_eq_right_iff.mpr (fun h => (hm h).elim)]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk_lt : k < Q.natDegree / 2 + 1 := Finset.mem_range.mp hk
    have hne : m ≠ k := by omega
    simp [hne]

private lemma heatDiffPoly_ne_zero {Q : Polynomial ℂ} {d : ℕ} (hlead : Q.coeff (2 * d + 1) ≠ 0) :
    heatDiffPoly Q ≠ 0 := by
  intro h0
  have hdeg : 2 * d + 1 ≤ Q.natDegree := Polynomial.le_natDegree_of_ne_zero hlead
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff d) h0
  rw [coeff_heatDiffPoly, ite_eq_left_iff.mpr (fun h => (h (by omega)).elim),
    Polynomial.coeff_zero] at hc
  exact mul_ne_zero (pow_ne_zero d (by norm_num)) hlead hc

private lemma odd_poly_eval_eq_sum {Q : Polynomial ℂ} (hodd : ∀ z : ℂ, Q.eval (-z) = -Q.eval z) (u : ℂ) :
    Q.eval u = ∑ m ∈ Finset.range (Q.natDegree / 2 + 1), Q.coeff (2 * m + 1) * u ^ (2 * m + 1) := by
  have heven_zero : ∀ k : ℕ, Even k → Q.coeff k = 0 := by
    intro k hk
    have hcomp : Q.comp (Polynomial.C (-1 : ℂ) * Polynomial.X) = -Q := by
      apply Polynomial.funext; intro z
      simp [Polynomial.eval_comp, hodd z]
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff k) hcomp
    rw [coeff_comp_C_mul_X', hk.neg_one_pow, one_mul, Polynomial.coeff_neg] at hc
    linear_combination (1 / 2 : ℂ) * hc
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self Q.natDegree)]
  have hsplit : Finset.range (Q.natDegree + 1) =
      (Finset.range (Q.natDegree + 1)).filter Odd ∪ (Finset.range (Q.natDegree + 1)).filter (fun k => ¬ Odd k) :=
    (Finset.filter_union_filter_not_eq Odd _).symm
  rw [hsplit, Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _)]
  have hzero : ∑ k ∈ (Finset.range (Q.natDegree + 1)).filter (fun k => ¬ Odd k), Q.coeff k * u ^ k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [heven_zero k (Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hk).2), zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_bij_ne_zero (fun k _ _ => k / 2) ?_ ?_ ?_ ?_
  · intro k hk _
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)
  · intro a ha _ b hb _ hab
    obtain ⟨m₁, hm₁⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨m₂, hm₂⟩ := (Finset.mem_filter.mp hb).2
    omega
  · intro m hm hne
    have hmlt := Finset.mem_range.mp hm
    by_cases hle : 2 * m + 1 < Q.natDegree + 1
    · refine ⟨2 * m + 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hle, ⟨m, rfl⟩⟩, hne, by omega⟩
    · exfalso
      have hgt : Q.natDegree < 2 * m + 1 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul] at hne
      exact hne rfl
  · intro k hk _
    obtain ⟨m, rfl⟩ := (Finset.mem_filter.mp hk).2
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]

private lemma tsum_finset_sum_complex {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℂ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    ∑ i ∈ s, ∑' k : ℕ, f i k = ∑' k : ℕ, ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    have h1 : Summable (f a) := hf a (Finset.mem_insert_self a s)
    have h2 : Summable (fun k => ∑ i ∈ s, f i k) :=
      summable_sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [← h1.tsum_add h2]
    refine tsum_congr fun k => ?_
    rw [Finset.sum_insert ha]

private lemma constCoeffLinDiffOp_heatSum {Q : Polynomial ℂ} (hodd : ∀ z : ℂ, Q.eval (-z) = -Q.eval z)
    {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    constCoeffLinDiffOp (heatDiffPoly Q)
      (fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) *
        Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) t =
      ∑' k : ℕ, Q.eval (((k : ℝ) + c : ℝ) : ℂ) *
        Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2) := by
  have hdeg_le : (heatDiffPoly Q).natDegree ≤ Q.natDegree / 2 := by
    unfold heatDiffPoly
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun m hm => ?_)
    have hmlt : m < Q.natDegree / 2 + 1 := Finset.mem_range.mp hm
    refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_X_pow_le m).trans (by omega))
  unfold constCoeffLinDiffOp
  have hsum_ext : ∑ m ∈ Finset.range ((heatDiffPoly Q).natDegree + 1),
        (heatDiffPoly Q).coeff m * iteratedDeriv m
          (fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) *
            Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) t =
      ∑ m ∈ Finset.range (Q.natDegree / 2 + 1),
        (heatDiffPoly Q).coeff m * iteratedDeriv m
          (fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) *
            Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) t := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hnot => ?_
    have hgt : (heatDiffPoly Q).natDegree < m := by
      rw [Finset.mem_range] at hnot; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
  rw [hsum_ext]
  have hterm : ∀ m ∈ Finset.range (Q.natDegree / 2 + 1),
      (heatDiffPoly Q).coeff m * iteratedDeriv m
        (fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + c : ℝ) : ℂ) *
          Complex.exp (-(x : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) t =
      ∑' k : ℕ, (Q.coeff (2 * m + 1) * (((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1)) *
        Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2) := by
    intro m hm
    have hm_le : m ≤ Q.natDegree / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [coeff_heatDiffPoly, ite_eq_left_iff.mpr (fun h => (h hm_le).elim),
      iteratedDeriv_heatSum hc m t ht, ← mul_assoc, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hsq : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by rw [← mul_pow]; norm_num
    calc ((-1 : ℂ) ^ m * Q.coeff (2 * m + 1) * (-1 : ℂ) ^ m) *
          ((((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1) *
            Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2))
        = ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) * ((Q.coeff (2 * m + 1) * (((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1)) *
            Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) := by ring
      _ = _ := by rw [hsq, one_mul]
  rw [Finset.sum_congr rfl hterm]
  have hswap :
      (∑ m ∈ Finset.range (Q.natDegree / 2 + 1),
        ∑' k : ℕ, (Q.coeff (2 * m + 1) * (((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1)) *
          Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) =
      ∑' k : ℕ, ∑ m ∈ Finset.range (Q.natDegree / 2 + 1),
        (Q.coeff (2 * m + 1) * (((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1)) *
          Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2) :=
    tsum_finset_sum_complex (Finset.range (Q.natDegree / 2 + 1))
      (fun (m k : ℕ) => (Q.coeff (2 * m + 1) * (((k : ℝ) + c : ℝ) : ℂ) ^ (2 * m + 1)) *
        Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) fun m _ =>
        ((summable_heat_term hc ht (2 * m + 1)).mul_left (Q.coeff (2 * m + 1))).congr fun k => by ring
  rw [hswap]
  refine tsum_congr fun k => ?_
  rw [odd_poly_eval_eq_sum hodd, Finset.sum_mul]

private lemma tsum_shift_of_subground_zero {g : ℕ → ℂ} {s : ℕ}
    (hg : Summable g) (hsub : ∀ j < s, g j = 0) :
    ∑' k : ℕ, g (k + s) = ∑' k : ℕ, g k := by
  have h := hg.sum_add_tsum_nat_add s
  have hfin : ∑ j ∈ Finset.range s, g j = 0 :=
    Finset.sum_eq_zero fun j hj => hsub j (Finset.mem_range.mp hj)
  rw [hfin, zero_add] at h
  exact h

/-- Literal shifted heat trace of `ℂℙⁿ` (`n ≥ 1`, `u_k = k + n / 2`):
`H_{ℂℙⁿ}(t) = ∑_{k ≥ 0} m_{ℂℙⁿ}(k + n/2) e^{-t (k + n/2)²}`. -/
@[expose] def cpnHeatTrace (n : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, (cpnMultPoly n).eval ((k : ℂ) + (n : ℂ) / 2) *
    Complex.exp (-(t : ℂ) * ((k : ℂ) + (n : ℂ) / 2) ^ 2)

/-- Literal shifted heat trace of `ℍℙⁿ` (`n ≥ 1`, `u_k = k + n + 1/2`):
`H_{ℍℙⁿ}(t) = ∑_{k ≥ 0} m_{ℍℙⁿ}(k + n + 1/2) e^{-t (k + n + 1/2)²}`. -/
@[expose] def hpnHeatTrace (n : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, (hpnMultPoly n).eval ((k : ℂ) + (n : ℂ) + 1 / 2) *
    Complex.exp (-(t : ℂ) * ((k : ℂ) + (n : ℂ) + 1 / 2) ^ 2)

/-- Literal shifted heat trace of the Cayley projective plane `𝕆ℙ²` (`u_k = k + 11/2`):
`H_{𝕆ℙ²}(t) = ∑_{k ≥ 0} m_{𝕆ℙ²}(k + 11/2) e^{-t (k + 11/2)²}`. -/
@[expose] def op2HeatTrace (t : ℝ) : ℂ :=
  ∑' k : ℕ, op2MultPoly.eval ((k : ℂ) + 11 / 2) *
    Complex.exp (-(t : ℂ) * ((k : ℂ) + 11 / 2) ^ 2)

/-- Literal shifted heat trace of the even sphere `S^{2r}` (`r ≥ 1`, `u_k = k + r - 1/2`):
`H_{S^{2r}}(t) = ∑_{k ≥ 0} m_{S^{2r}}(k + r - 1/2) e^{-t (k + r - 1/2)²}`. -/
@[expose] def evenSphereHeatTrace (r : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, (sphereMultPoly (2 * r)).eval ((k : ℂ) + (r : ℂ) - 1 / 2) *
    Complex.exp (-(t : ℂ) * ((k : ℂ) + (r : ℂ) - 1 / 2) ^ 2)

private lemma summable_polyEval_heat {Q : Polynomial ℂ} {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    Summable (fun k : ℕ => Q.eval (((k : ℝ) + c : ℝ) : ℂ) *
      Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) := by
  have heq : (fun k : ℕ => Q.eval (((k : ℝ) + c : ℝ) : ℂ) *
      Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) =
      fun k : ℕ => ∑ j ∈ Finset.range (Q.natDegree + 1),
        Q.coeff j * ((((k : ℝ) + c : ℝ) : ℂ) ^ j *
          Complex.exp (-(t : ℂ) * (((k : ℝ) + c : ℝ) : ℂ) ^ 2)) := by
    funext k
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self Q.natDegree), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  exact summable_sum fun j _ => (summable_heat_term hc ht j).mul_left _

/-- Exact differential-operator reduction for `ℂℙⁿ` (`n` even): `H_{ℂℙⁿ}(t) = L_{ℂℙⁿ}(baseHeatInt)(t)`. -/
theorem cpnHeatTrace_eq_diffOp_even {n : ℕ} (hn : 1 ≤ n) (heven : Even n) {t : ℝ} (ht : 0 < t) :
    cpnHeatTrace n t = constCoeffLinDiffOp (heatDiffPoly (cpnMultPoly n)) baseHeatInt t := by
  rcases heven with ⟨r, rfl⟩
  have hr : 1 ≤ r := by omega
  have hodd : ∀ z : ℂ, (cpnMultPoly (r + r)).eval (-z) = -(cpnMultPoly (r + r)).eval z := fun z => by
    rw [cpnMultPoly, multPolyOfDoubled_eval, multPolyOfDoubled_eval,
      show 2 * -z = -(2 * z) by ring, cpnPoly_eval_neg]
  have hbase : baseHeatInt = fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 : ℝ) : ℂ) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) ^ 2) := by
    funext x; unfold baseHeatInt; refine tsum_congr fun k => ?_; push_cast; rfl
  rw [hbase, constCoeffLinDiffOp_heatSum hodd (c := (1 : ℝ)) one_pos ht]
  have hshift := tsum_shift_of_subground_zero (s := r - 1)
    (summable_polyEval_heat (Q := cpnMultPoly (r + r)) (c := (1 : ℝ)) one_pos ht) fun j hj => by
      rw [cpnMultPoly, multPolyOfDoubled_eval]
      have harg : (2 : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) = ((2 * (j + 1) : ℕ) : ℂ) := by push_cast; ring
      rw [harg, cpnPoly_subground_eq_zero (by omega) (by omega), zero_mul]
  rw [← hshift, cpnHeatTrace]
  refine tsum_congr fun k => ?_
  have harg : ((((k + (r - 1) : ℕ) : ℝ) + 1 : ℝ) : ℂ) = (k : ℂ) + ((r + r : ℕ) : ℂ) / 2 := by
    have hnat : (k + (r - 1) : ℕ) + 1 = k + r := by omega
    have hC : (((k + (r - 1) : ℕ) : ℂ) + 1) = (k : ℂ) + (r : ℂ) := by exact_mod_cast hnat
    push_cast at hC ⊢; linear_combination hC
  rw [harg]

/-- Exact differential-operator reduction for `ℂℙⁿ` (`n` odd): `H_{ℂℙⁿ}(t) = L_{ℂℙⁿ}(baseHeatHalf)(t)`. -/
theorem cpnHeatTrace_eq_diffOp_odd {n : ℕ} (_hn : 1 ≤ n) (hodd_n : Odd n) {t : ℝ} (ht : 0 < t) :
    cpnHeatTrace n t = constCoeffLinDiffOp (heatDiffPoly (cpnMultPoly n)) baseHeatHalf t := by
  rcases hodd_n with ⟨r, rfl⟩
  have hodd : ∀ z : ℂ, (cpnMultPoly (2 * r + 1)).eval (-z) = -(cpnMultPoly (2 * r + 1)).eval z := fun z => by
    rw [cpnMultPoly, multPolyOfDoubled_eval, multPolyOfDoubled_eval,
      show 2 * -z = -(2 * z) by ring, cpnPoly_eval_neg]
  have hbase : baseHeatHalf = fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 / 2 : ℝ) : ℂ) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2) := by
    funext x; unfold baseHeatHalf; refine tsum_congr fun k => ?_; push_cast; rfl
  rw [hbase, constCoeffLinDiffOp_heatSum hodd (c := (1 / 2 : ℝ)) (by norm_num) ht]
  have hshift := tsum_shift_of_subground_zero (s := r)
    (summable_polyEval_heat (Q := cpnMultPoly (2 * r + 1)) (c := (1 / 2 : ℝ)) (by norm_num) ht) fun j hj => by
      rw [cpnMultPoly, multPolyOfDoubled_eval]
      have harg : (2 : ℂ) * (((j : ℝ) + 1 / 2 : ℝ) : ℂ) = ((2 * j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [harg, cpnPoly_subground_eq_zero (by omega) (by omega), zero_mul]
  rw [← hshift, cpnHeatTrace]
  refine tsum_congr fun k => ?_
  have harg : ((((k + r : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ) + ((2 * r + 1 : ℕ) : ℂ) / 2 := by
    push_cast; ring
  rw [harg]

/-- Exact differential-operator reduction for `ℍℙⁿ` (`n ≥ 1`): `H_{ℍℙⁿ}(t) = L_{ℍℙⁿ}(baseHeatHalf)(t)`. -/
theorem hpnHeatTrace_eq_diffOp {n : ℕ} (_hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    hpnHeatTrace n t = constCoeffLinDiffOp (heatDiffPoly (hpnMultPoly n)) baseHeatHalf t := by
  have hodd : ∀ z : ℂ, (hpnMultPoly n).eval (-z) = -(hpnMultPoly n).eval z := fun z => by
    rw [hpnMultPoly, multPolyOfDoubled_eval, multPolyOfDoubled_eval,
      show 2 * -z = -(2 * z) by ring, hpnPoly_eval_neg]
  have hbase : baseHeatHalf = fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 / 2 : ℝ) : ℂ) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2) := by
    funext x; unfold baseHeatHalf; refine tsum_congr fun k => ?_; push_cast; rfl
  rw [hbase, constCoeffLinDiffOp_heatSum hodd (c := (1 / 2 : ℝ)) (by norm_num) ht]
  have hshift := tsum_shift_of_subground_zero (s := n)
    (summable_polyEval_heat (Q := hpnMultPoly n) (c := (1 / 2 : ℝ)) (by norm_num) ht) fun j hj => by
      rw [hpnMultPoly, multPolyOfDoubled_eval]
      have harg : (2 : ℂ) * (((j : ℝ) + 1 / 2 : ℝ) : ℂ) = ((2 * j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [harg, hpnPoly_subground_eq_zero (by omega) (by omega), zero_mul]
  rw [← hshift, hpnHeatTrace]
  refine tsum_congr fun k => ?_
  have harg : ((((k + n : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ) + (n : ℂ) + 1 / 2 := by
    push_cast; ring
  rw [harg]

/-- Exact differential-operator reduction for `𝕆ℙ²`: `H_{𝕆ℙ²}(t) = L_{𝕆ℙ²}(baseHeatHalf)(t)`. -/
theorem op2HeatTrace_eq_diffOp {t : ℝ} (ht : 0 < t) :
    op2HeatTrace t = constCoeffLinDiffOp (heatDiffPoly op2MultPoly) baseHeatHalf t := by
  have hodd : ∀ z : ℂ, op2MultPoly.eval (-z) = -op2MultPoly.eval z := fun z => by
    rw [op2MultPoly, multPolyOfDoubled_eval, multPolyOfDoubled_eval,
      show 2 * -z = -(2 * z) by ring, op2Poly_eval_neg]
  have hbase : baseHeatHalf = fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 / 2 : ℝ) : ℂ) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2) := by
    funext x; unfold baseHeatHalf; refine tsum_congr fun k => ?_; push_cast; rfl
  rw [hbase, constCoeffLinDiffOp_heatSum hodd (c := (1 / 2 : ℝ)) (by norm_num) ht]
  have hshift := tsum_shift_of_subground_zero (s := 5)
    (summable_polyEval_heat (Q := op2MultPoly) (c := (1 / 2 : ℝ)) (by norm_num) ht) fun j hj => by
      rw [op2MultPoly, multPolyOfDoubled_eval]
      have harg : (2 : ℂ) * (((j : ℝ) + 1 / 2 : ℝ) : ℂ) = ((2 * j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [harg]
      have hsub := op2QP_subground_vanishing
      have hev : ∀ s : ℕ, s % 2 = 1 → op2Poly.eval (s : ℂ) = op2QP.eval (s : ℤ) := fun s hs => by
        rw [op2QP_eval, show ((s : ℤ) % 2).toNat = 1 by omega]; simp
      rw [hev (2 * j + 1) (by omega)]
      interval_cases j
      · rw [show ((2 * 0 + 1 : ℕ) : ℤ) = 1 by rfl, hsub.1, zero_mul]
      · rw [show ((2 * 1 + 1 : ℕ) : ℤ) = 3 by rfl, hsub.2.1, zero_mul]
      · rw [show ((2 * 2 + 1 : ℕ) : ℤ) = 5 by rfl, hsub.2.2.1, zero_mul]
      · rw [show ((2 * 3 + 1 : ℕ) : ℤ) = 7 by rfl, hsub.2.2.2.1, zero_mul]
      · rw [show ((2 * 4 + 1 : ℕ) : ℤ) = 9 by rfl, hsub.2.2.2.2, zero_mul]
  rw [← hshift, op2HeatTrace]
  refine tsum_congr fun k => ?_
  have harg : ((((k + 5 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ) + 11 / 2 := by push_cast; ring
  rw [harg]

/-- Exact differential-operator reduction for every even sphere `S^{2r}` (`r ≥ 1`):
`H_{S^{2r}}(t) = L_{S^{2r}}(baseHeatHalf)(t)`. -/
theorem evenSphereHeatTrace_eq_diffOp {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : 0 < t) :
    evenSphereHeatTrace r t = constCoeffLinDiffOp (heatDiffPoly (sphereMultPoly (2 * r))) baseHeatHalf t := by
  have hodd : ∀ z : ℂ, (sphereMultPoly (2 * r)).eval (-z) = -(sphereMultPoly (2 * r)).eval z := fun z => by
    rw [sphereMultPoly, multPolyOfDoubled_eval, multPolyOfDoubled_eval,
      show 2 * -z = -(2 * z) by ring, conformalScalarPoly_eval_neg' (by omega),
      (show Odd (2 * r - 1) from ⟨r - 1, by omega⟩).neg_one_pow, neg_one_mul]
  have hbase : baseHeatHalf = fun x : ℝ => ∑' k : ℕ, (((k : ℝ) + 1 / 2 : ℝ) : ℂ) *
      Complex.exp (-(x : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2) := by
    funext x; unfold baseHeatHalf; refine tsum_congr fun k => ?_; push_cast; rfl
  rw [hbase, constCoeffLinDiffOp_heatSum hodd (c := (1 / 2 : ℝ)) (by norm_num) ht]
  have hshift := tsum_shift_of_subground_zero (s := r - 1)
    (summable_polyEval_heat (Q := sphereMultPoly (2 * r)) (c := (1 / 2 : ℝ)) (by norm_num) ht) fun j hj => by
      rw [sphereMultPoly, multPolyOfDoubled_eval]
      have harg : (2 : ℂ) * (((j : ℝ) + 1 / 2 : ℝ) : ℂ) = ((2 * j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [harg, conformalScalarPoly_subground_eq_zero (by omega) (by omega) (by omega), zero_mul]
  rw [← hshift, evenSphereHeatTrace]
  refine tsum_congr fun k => ?_
  have harg : ((((k + (r - 1) : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ) + (r : ℂ) - 1 / 2 := by
    have hnat : ((k + (r - 1) : ℕ) : ℂ) = (k : ℂ) + (r : ℂ) - 1 := by
      have h1 : (r - 1 : ℕ) + 1 = r := by omega
      have hC : ((r - 1 : ℕ) : ℂ) + 1 = (r : ℂ) := by exact_mod_cast h1
      push_cast; linear_combination hC
    push_cast at hnat ⊢; linear_combination hnat
  rw [harg]

/-- Unified shifted heat trace of any even-dimensional simply connected CROSS (`S^{2r}`, `ℂℙⁿ`,
`ℍℙⁿ`, `𝕆ℙ²`). -/
@[expose] def evenCROSSHeatTrace (M : SimplyConnectedCROSS) (t : ℝ) : ℂ :=
  match M with
  | .sphere s _ => evenSphereHeatTrace (s / 2) t
  | .cp n _ => cpnHeatTrace n t
  | .hp n _ => hpnHeatTrace n t
  | .op2 => op2HeatTrace t

/-- **All-CROSS Heat-Trace Dimension-Reduction Closure (Conditional Form)**:
If both canonical base heat traces `baseHeatInt` and `baseHeatHalf` satisfy no nonzero `ℂ(t)`-ADE
as `t → 0+`, then EVERY even-dimensional simply connected compact rank-1 symmetric space
(`S^{2r}`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`) has a shifted heat trace satisfying NO nonzero `ℂ(t)`-ADE as `t → 0+`! -/
theorem evenCROSS_heatTrace_no_rat_ade_of_baseHeat
    (hInt : ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val baseHeatInt t) (evalRatU P (t : ℂ)) = 0) →
      P = 0)
    (hHalf : ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val baseHeatHalf t) (evalRatU P (t : ℂ)) = 0) →
      P = 0)
    (M : SimplyConnectedCROSS) (hEven : Even M.realDim)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (evenCROSSHeatTrace M) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 := by
  have hcongr_op : ∀ {f g : ℝ → ℂ}, (∀ t : ℝ, 0 < t → f t = g t) →
      (∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f t) (evalRatU P (t : ℂ)) = 0) →
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g t) (evalRatU P (t : ℂ)) = 0 := by
    intro f g hfg hPf
    filter_upwards [hPf, self_mem_nhdsWithin] with t ht ht_pos
    have hloc : f =ᶠ[𝓝 t] g := Filter.eventually_of_mem (Ioi_mem_nhds ht_pos) hfg
    have hj : (fun j : Fin (r + 1) => iteratedDeriv j.val f t) =
        fun j : Fin (r + 1) => iteratedDeriv j.val g t := funext fun j => hloc.iteratedDeriv_eq j.val
    rwa [← hj]
  cases M with
  | sphere s hs =>
    rcases hEven with ⟨k, hk⟩
    change s = k + k at hk
    have hk_ge : 1 ≤ k := by omega
    have hs2 : s / 2 = k := by omega
    have hL : heatDiffPoly (sphereMultPoly (2 * k)) ≠ 0 :=
      heatDiffPoly_ne_zero (d := k - 1) (by
        rw [show 2 * (k - 1) + 1 = 2 * k - 1 by omega]
        exact evenSphereMultPoly_lead_ne_zero hk_ge)
    refine dTrans_of_constCoeffLinDiffOp baseHeatHalf_analyticOn hHalf _ hL P ?_
    exact hcongr_op (fun t ht => by
      simp only [evenCROSSHeatTrace, hs2]; exact evenSphereHeatTrace_eq_diffOp hk_ge ht) hP
  | cp n hn =>
    have hL : heatDiffPoly (cpnMultPoly n) ≠ 0 :=
      heatDiffPoly_ne_zero (d := n - 1) (by
        rw [show 2 * (n - 1) + 1 = 2 * n - 1 by omega]
        exact cpnMultPoly_lead_ne_zero hn)
    by_cases hev : Even n
    · refine dTrans_of_constCoeffLinDiffOp baseHeatInt_analyticOn hInt _ hL P ?_
      exact hcongr_op (fun t ht => cpnHeatTrace_eq_diffOp_even hn hev ht) hP
    · have hodd : Odd n := Nat.not_even_iff_odd.mp hev
      refine dTrans_of_constCoeffLinDiffOp baseHeatHalf_analyticOn hHalf _ hL P ?_
      exact hcongr_op (fun t ht => cpnHeatTrace_eq_diffOp_odd hn hodd ht) hP
  | hp n hn =>
    have hL : heatDiffPoly (hpnMultPoly n) ≠ 0 :=
      heatDiffPoly_ne_zero (d := 2 * n - 1) (by
        rw [show 2 * (2 * n - 1) + 1 = 4 * n - 1 by omega]
        exact hpnMultPoly_lead_ne_zero hn)
    refine dTrans_of_constCoeffLinDiffOp baseHeatHalf_analyticOn hHalf _ hL P ?_
    exact hcongr_op (fun t ht => hpnHeatTrace_eq_diffOp hn ht) hP
  | op2 =>
    have hL : heatDiffPoly op2MultPoly ≠ 0 :=
      heatDiffPoly_ne_zero (d := 7) (by
        rw [show 2 * 7 + 1 = 15 by rfl]
        exact op2MultPoly_lead_ne_zero)
    refine dTrans_of_constCoeffLinDiffOp baseHeatHalf_analyticOn hHalf _ hL P ?_
    exact hcongr_op (fun t ht => op2HeatTrace_eq_diffOp ht) hP

/-! ### Part D.4: Unconditional `ℂ(t)`-D-Transcendence of `baseHeatInt`, `baseHeatHalf`, and All Even-Dimensional CROSS Heat Traces -/

section UnconditionalBaseHeatDTrans

open Filter Topology MeasureTheory
open PakPrimes.GeneralTheorem2
open PakPrimes.BorelStokesVandermonde
open PakPrimes.BranchPointStokes
open PakPrimes.FishburnTorusKnots
open PakPrimes.FalseThetaDichotomy

/-! #### D.4a. Meromorphic Borel Kernels for `baseHeatInt` (`(z cot z - 1) / z²`) and `baseHeatHalf` (`(z / sin z - 1) / z²`) -/

/-- Simple-pole sequence `ω_m = (π (m + 1))²` shared by both canonical heat-trace Borel kernels. -/
@[expose] def heatPole (m : ℕ) : ℝ := (Real.pi * ((m : ℝ) + 1)) ^ 2

/-- Analytic even kernel `K_int(z²) = z cot z - 1`. -/
@[expose] def heatIntKernel (w : ℂ) : ℂ := cosSqrt w / sinSqrt w - 1

/-- Analytic even kernel `K_half(z²) = z / sin z - 1`. -/
@[expose] def heatHalfKernel (w : ℂ) : ℂ := (sinSqrt w)⁻¹ - 1

/-- Divided-difference Borel kernel `ψ_int(w) = (cosSqrt w / sinSqrt w - 1) / w` (`w ≠ 0`). -/
@[expose] def heatIntBorel (w : ℂ) : ℂ := dslope heatIntKernel 0 w

/-- Divided-difference Borel kernel `ψ_half(w) = ((sinSqrt w)⁻¹ - 1) / w` (`w ≠ 0`). -/
@[expose] def heatHalfBorel (w : ℂ) : ℂ := dslope heatHalfKernel 0 w

private lemma cosSqrt_eq_deriv_sinSqrt (w : ℂ) :
    cosSqrt w = 2 * w * deriv sinSqrt w + sinSqrt w := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w := by
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    · refine ⟨Complex.exp (Complex.log w / 2), ?_⟩
      rw [sq, ← Complex.exp_add, add_halves, Complex.exp_log hw]
  subst hs
  rw [cosSqrt_sq, deriv_sinSqrt_sq]

private lemma cosSqrt_analyticAt' (z : ℂ) : AnalyticAt ℂ cosSqrt z := by
  have heq : cosSqrt = fun w : ℂ => 2 * w * deriv sinSqrt w + sinSqrt w :=
    funext cosSqrt_eq_deriv_sinSqrt
  rw [heq]
  exact (((analyticAt_const.mul analyticAt_id).mul (sinSqrt_analyticAt z).deriv).add (sinSqrt_analyticAt z))

private lemma cosSqrt_zero' : cosSqrt 0 = 1 := by
  have h := cosSqrt_sq 0
  simpa using h

private lemma heatIntKernel_zero : heatIntKernel 0 = 0 := by
  simp [heatIntKernel, cosSqrt_zero', sinSqrt_zero]

private lemma heatHalfKernel_zero : heatHalfKernel 0 = 0 := by
  simp [heatHalfKernel, sinSqrt_zero]

private lemma heatPole_pos (m : ℕ) : 0 < heatPole m := by
  unfold heatPole; positivity

private lemma heatPole_strictMono : StrictMono heatPole := fun a b hab => by
  unfold heatPole
  have hlt : (a : ℝ) < b := by exact_mod_cast hab
  have h1 : Real.pi * ((a : ℝ) + 1) < Real.pi * ((b : ℝ) + 1) :=
    mul_lt_mul_of_pos_left (by linarith) Real.pi_pos
  have hpos : 0 < Real.pi * ((a : ℝ) + 1) := by positivity
  nlinarith

private lemma sinSqrt_ne_zero_of_not_heatPole {z : ℂ}
    (hz : z ∉ Set.range (fun m : ℕ => (heatPole m : ℂ))) : sinSqrt z ≠ 0 := by
  intro h0
  obtain ⟨n, hn, rfl⟩ := (sinSqrt_eq_zero_iff z).mp h0
  refine hz ⟨n - 1, ?_⟩
  dsimp only; unfold heatPole
  have hn1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast Nat.sub_add_cancel hn
  rw [hn1]

private lemma heatIntKernel_analyticAt {z : ℂ}
    (hz : z ∉ Set.range (fun m : ℕ => (heatPole m : ℂ))) :
    AnalyticAt ℂ heatIntKernel z :=
  ((cosSqrt_analyticAt' z).div (sinSqrt_analyticAt z) (sinSqrt_ne_zero_of_not_heatPole hz)).sub
    analyticAt_const

private lemma heatHalfKernel_analyticAt {z : ℂ}
    (hz : z ∉ Set.range (fun m : ℕ => (heatPole m : ℂ))) :
    AnalyticAt ℂ heatHalfKernel z :=
  ((sinSqrt_analyticAt z).inv (sinSqrt_ne_zero_of_not_heatPole hz)).sub analyticAt_const

private lemma heatIntBorel_analyticAt {z : ℂ}
    (hz : z ∉ Set.range (fun m : ℕ => (heatPole m : ℂ))) :
    AnalyticAt ℂ heatIntBorel z :=
  (heatIntKernel_analyticAt hz).dslope 0

private lemma heatHalfBorel_analyticAt {z : ℂ}
    (hz : z ∉ Set.range (fun m : ℕ => (heatPole m : ℂ))) :
    AnalyticAt ℂ heatHalfBorel z :=
  (heatHalfKernel_analyticAt hz).dslope 0

private lemma norm_csin_ge_quarter_exp {w : ℂ} (hw : 1 ≤ |w.im|) :
    (1 / 4 : ℝ) * Real.exp |w.im| ≤ ‖Complex.sin w‖ := by
  have hsin : Complex.sin w = (Complex.exp (w * I) - Complex.exp (-(w * I))) / (2 * I) := by
    rw [Complex.sin]
    field_simp [Complex.I_ne_zero]
    ring_nf; rw [Complex.I_sq]; ring
  have h1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have h2 : ‖Complex.exp (-(w * I))‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hdiff : Real.exp |w.im| - Real.exp (-|w.im|) ≤ ‖Complex.exp (w * I) - Complex.exp (-(w * I))‖ := by
    by_cases him : 0 ≤ w.im
    · rw [abs_of_nonneg him]
      have htri := norm_sub_norm_le (Complex.exp (-(w * I))) (Complex.exp (w * I))
      rw [norm_sub_rev, h1, h2] at htri
      exact htri
    · push Not at him
      rw [abs_of_neg him, neg_neg]
      have htri := norm_sub_norm_le (Complex.exp (w * I)) (Complex.exp (-(w * I)))
      rw [h1, h2] at htri
      exact htri
  have hexp_ratio : Real.exp (-|w.im|) ≤ (1 / 2 : ℝ) * Real.exp |w.im| := by
    have hmul : Real.exp (2 * |w.im|) ≥ 2 := by
      have hge := Real.add_one_le_exp (2 * |w.im|)
      linarith
    have hpos : 0 < Real.exp |w.im| := Real.exp_pos _
    have hsq : Real.exp (-|w.im|) * Real.exp (2 * |w.im|) = Real.exp |w.im| := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith
  rw [hsin, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  linarith

private lemma norm_ccos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have hcos : Complex.cos w = (Complex.exp (w * I) + Complex.exp (-(w * I))) / 2 := by
    rw [Complex.cos]; ring_nf
  have h1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have h2 : ‖Complex.exp (-(w * I))‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  rw [hcos, norm_div, Complex.norm_ofNat]
  have htri : ‖Complex.exp (w * I) + Complex.exp (-(w * I))‖ ≤ Real.exp (-w.im) + Real.exp w.im := by
    calc ‖Complex.exp (w * I) + Complex.exp (-(w * I))‖
        ≤ ‖Complex.exp (w * I)‖ + ‖Complex.exp (-(w * I))‖ := norm_add_le _ _
      _ = Real.exp (-w.im) + Real.exp w.im := by rw [h1, h2]
  have hle1 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs w.im)
  have hle2 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self w.im)
  linarith

private lemma heatBorel_expType_ray {ψ : ℂ → ℂ} {s : ℝ}
    (hcont : ContinuousOn (fun v : ℝ => ψ (Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ)))
      (Set.Icc 0 16))
    (hfar : ∀ v : ℝ, 16 ≤ v →
      ‖ψ (Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ))‖ ≤ 2) :
    ExpType (Minor.pull (Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ))) ψ) := by
  let d : ℂ := Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ))
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max (max M 0) 2, 0, by positivity, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  unfold Minor.pull
  change ‖d * ψ (d * (v : ℂ))‖ ≤ max (max M 0) 2
  rw [norm_mul, hd_norm, one_mul]
  by_cases hv16 : v ≤ 16
  · exact (hM v ⟨hv, hv16⟩).trans ((le_max_left M 0).trans (le_max_left _ _))
  · push Not at hv16
    exact (hfar v hv16.le).trans (le_max_right _ _)

private lemma ray_point_not_heatPole {s v : ℝ} (hs : s = 1 ∨ s = -1) (hv : 0 ≤ v) :
    Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ) ∉
      Set.range (fun m : ℕ => (heatPole m : ℂ)) := by
  rintro ⟨m, hm⟩
  have him := congrArg Complex.im hm
  have hre_pos : 0 < heatPole m := heatPole_pos m
  have hv_ne : v ≠ 0 := by
    intro hv0; subst hv0
    simp at hm
    exact hre_pos.ne' hm
  have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
  rw [Complex.ofReal_im, show I * ((s * (Real.pi / 3) : ℝ) : ℂ) = ((s * (Real.pi / 3) : ℝ) : ℂ) * I by ring,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, mul_zero, zero_add] at him
  have hsin_ne : Real.sin (s * (Real.pi / 3)) ≠ 0 := by
    rcases hs with rfl | rfl
    · simp [Real.sin_pi_div_three]
    · simp [Real.sin_neg, Real.sin_pi_div_three]
  exact mul_ne_zero hsin_ne hv_pos.ne' him.symm

private lemma ray_sqrt_point {s v : ℝ} (hs : s = 1 ∨ s = -1) (hv : 16 ≤ v) :
    ∃ z : ℂ, z ^ 2 = Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ) ∧
      ‖z‖ = Real.sqrt v ∧ |z.im| = Real.sqrt v / 2 ∧ 2 ≤ |z.im| := by
  let z : ℂ := ((Real.sqrt v : ℝ) : ℂ) * Complex.exp (I * ((s * (Real.pi / 6) : ℝ) : ℂ))
  have hv0 : 0 ≤ v := by linarith
  have hsr_ge4 : 4 ≤ Real.sqrt v := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · dsimp only [z]
    rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, Real.sq_sqrt hv0]
    have hexp : (2 : ℕ) * (I * ((s * (Real.pi / 6) : ℝ) : ℂ)) = I * ((s * (Real.pi / 3) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hexp]; ring
  · dsimp only [z]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v),
      show I * ((s * (Real.pi / 6) : ℝ) : ℂ) = ((s * (Real.pi / 6) : ℝ) : ℂ) * I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  · have him : z.im = Real.sqrt v * Real.sin (s * (Real.pi / 6)) := by
      dsimp only [z]
      rw [show I * ((s * (Real.pi / 6) : ℝ) : ℂ) = ((s * (Real.pi / 6) : ℝ) : ℂ) * I by ring,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im]
      ring
    rw [him, abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]
    have hsin : |Real.sin (s * (Real.pi / 6))| = 1 / 2 := by
      rcases hs with rfl | rfl
      · simp [Real.sin_pi_div_six]
      · simp [Real.sin_neg, Real.sin_pi_div_six]
    rw [hsin]; ring
  · have him : |z.im| = Real.sqrt v / 2 := by
      have h1 : z.im = Real.sqrt v * Real.sin (s * (Real.pi / 6)) := by
        dsimp only [z]
        rw [show I * ((s * (Real.pi / 6) : ℝ) : ℂ) = ((s * (Real.pi / 6) : ℝ) : ℂ) * I by ring,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im]
        ring
      rw [h1, abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]
      rcases hs with rfl | rfl
      · simp [Real.sin_pi_div_six]; ring
      · simp [Real.sin_neg, Real.sin_pi_div_six]; ring
    linarith

private lemma heatIntBorel_far_bound {s v : ℝ} (hs : s = 1 ∨ s = -1) (hv : 16 ≤ v) :
    ‖heatIntBorel (Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ))‖ ≤ 2 := by
  obtain ⟨z, hz_sq, hz_norm, _, hz_im2⟩ := ray_sqrt_point hs hv
  set w : ℂ := Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ)
  have hw_norm : ‖w‖ = v := by
    dsimp only [w]
    rw [norm_mul, show I * ((s * (Real.pi / 3) : ℝ) : ℂ) = ((s * (Real.pi / 3) : ℝ) : ℂ) * I by ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hw_ne : w ≠ 0 := norm_pos_iff.mp (by rw [hw_norm]; linarith)
  have hz_ne : z ≠ 0 := by intro h0; apply hw_ne; rw [← hz_sq, h0]; simp
  have hsin_ge : (1 / 4 : ℝ) * Real.exp |z.im| ≤ ‖Complex.sin z‖ :=
    norm_csin_ge_quarter_exp (by linarith)
  have hsin_ne : Complex.sin z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsin_ge
    linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 4) (Real.exp_pos |z.im|)]
  have hsinSqrt_ne : sinSqrt w ≠ 0 := by
    rw [← hz_sq]; intro h0; apply hsin_ne; rw [← mul_sinSqrt_sq, h0, mul_zero]
  have hval : heatIntBorel w = (z * Complex.cos z / Complex.sin z - 1) / w := by
    unfold heatIntBorel
    rw [dslope_of_ne _ hw_ne, slope_def_field, heatIntKernel_zero, sub_zero, sub_zero]
    congr 1; unfold heatIntKernel; congr 1
    rw [← hz_sq, cosSqrt_sq]
    have hmul := mul_sinSqrt_sq z
    rw [← hmul]; field_simp [hz_ne, hsinSqrt_ne]
  rw [hval, norm_div, hw_norm]
  have hcot : ‖z * Complex.cos z / Complex.sin z‖ ≤ 4 * Real.sqrt v := by
    rw [norm_div, norm_mul, hz_norm]
    have hnum : Real.sqrt v * ‖Complex.cos z‖ ≤ Real.sqrt v * Real.exp |z.im| :=
      mul_le_mul_of_nonneg_left (norm_ccos_le_exp z) (Real.sqrt_nonneg v)
    have hpos_den : 0 < (1 / 4 : ℝ) * Real.exp |z.im| := by positivity
    calc Real.sqrt v * ‖Complex.cos z‖ / ‖Complex.sin z‖
        ≤ (Real.sqrt v * Real.exp |z.im|) / ((1 / 4 : ℝ) * Real.exp |z.im|) :=
          div_le_div₀ (by positivity) hnum hpos_den hsin_ge
      _ = 4 * Real.sqrt v := by
          have he : Real.exp |z.im| ≠ 0 := (Real.exp_pos _).ne'
          field_simp [he]
  have htri : ‖z * Complex.cos z / Complex.sin z - 1‖ ≤ 4 * Real.sqrt v + 1 :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hsr_le : 4 * Real.sqrt v + 1 ≤ 2 * v := by
    have h4 : 4 ≤ Real.sqrt v := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
      exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
    have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt (by linarith)
    nlinarith
  exact (div_le_iff₀ (by linarith : (0 : ℝ) < v)).mpr (by linarith)

private lemma heatHalfBorel_far_bound {s v : ℝ} (hs : s = 1 ∨ s = -1) (hv : 16 ≤ v) :
    ‖heatHalfBorel (Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ))‖ ≤ 2 := by
  obtain ⟨z, hz_sq, hz_norm, _, hz_im2⟩ := ray_sqrt_point hs hv
  set w : ℂ := Complex.exp (I * ((s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ)
  have hw_norm : ‖w‖ = v := by
    dsimp only [w]
    rw [norm_mul, show I * ((s * (Real.pi / 3) : ℝ) : ℂ) = ((s * (Real.pi / 3) : ℝ) : ℂ) * I by ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hw_ne : w ≠ 0 := norm_pos_iff.mp (by rw [hw_norm]; linarith)
  have hz_ne : z ≠ 0 := by intro h0; apply hw_ne; rw [← hz_sq, h0]; simp
  have hsin_ge : (1 / 4 : ℝ) * Real.exp |z.im| ≤ ‖Complex.sin z‖ :=
    norm_csin_ge_quarter_exp (by linarith)
  have hsin_ne : Complex.sin z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsin_ge
    linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 4) (Real.exp_pos |z.im|)]
  have hsinSqrt_ne : sinSqrt w ≠ 0 := by
    rw [← hz_sq]; intro h0; apply hsin_ne; rw [← mul_sinSqrt_sq, h0, mul_zero]
  have hval : heatHalfBorel w = (z / Complex.sin z - 1) / w := by
    unfold heatHalfBorel
    rw [dslope_of_ne _ hw_ne, slope_def_field, heatHalfKernel_zero, sub_zero, sub_zero]
    congr 1; unfold heatHalfKernel; congr 1
    rw [← hz_sq]
    have hmul := mul_sinSqrt_sq z
    rw [← hmul]; field_simp [hz_ne, hsinSqrt_ne]
  rw [hval, norm_div, hw_norm]
  have hcsc : ‖z / Complex.sin z‖ ≤ 4 * Real.sqrt v := by
    rw [norm_div, hz_norm]
    have hexp_ge1 : (1 : ℝ) ≤ Real.exp |z.im| := Real.one_le_exp (abs_nonneg _)
    have hden_ge : (1 / 4 : ℝ) ≤ ‖Complex.sin z‖ := by linarith
    calc Real.sqrt v / ‖Complex.sin z‖
        ≤ Real.sqrt v / (1 / 4 : ℝ) := div_le_div_of_nonneg_left (Real.sqrt_nonneg v) (by norm_num) hden_ge
      _ = 4 * Real.sqrt v := by ring
  have htri : ‖z / Complex.sin z - 1‖ ≤ 4 * Real.sqrt v + 1 :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hsr_le : 4 * Real.sqrt v + 1 ≤ 2 * v := by
    have h4 : 4 ≤ Real.sqrt v := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
      exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
    have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt (by linarith)
    nlinarith
  exact (div_le_iff₀ (by linarith : (0 : ℝ) < v)).mpr (by linarith)

/-- Complete `MeromorphicBorelData` for the integer-lattice heat-trace Borel kernel
`ψ_int(w) = (cosSqrt w / sinSqrt w - 1) / w`, with simple poles at `ω_m = (π (m + 1))²`
and constant residue `+2`. -/
def heatIntBorel_meromorphicBorelData :
    MeromorphicBorelData heatIntBorel heatPole (fun _ => (2 : ℂ)) where
  θ₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := Real.pi ^ 2 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hθ₀_lt := by linarith [Real.pi_pos]
  hε_pos := by positivity
  ω_pos := heatPole_pos 0
  ω_mono := heatPole_strictMono
  res_ne_zero := fun _ => two_ne_zero
  analyticOn := fun z hz => heatIntBorel_analyticAt hz.2
  simple_pole := fun m => by
    let ωm : ℂ := (heatPole m : ℂ)
    have hωm_pos : 0 < heatPole m := heatPole_pos m
    have hωm_ne : ωm ≠ 0 := Complex.ofReal_ne_zero.mpr hωm_pos.ne'
    have hm1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have hωm_eq : ωm = (((Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      dsimp only [ωm]; unfold heatPole; push_cast; rfl
    have hsin0 : sinSqrt ωm = 0 := by
      rw [hωm_eq]; exact (sinSqrt_eq_zero_iff _).mpr ⟨m + 1, hm1, rfl⟩
    have hd_val : deriv sinSqrt ωm = (-1 : ℂ) ^ (m + 1) / (2 * ωm) := by
      rw [hωm_eq, deriv_sinSqrt_at_zero_val hm1]
      push_cast; ring
    have hd_ne : deriv sinSqrt ωm ≠ 0 := by
      rw [hωm_eq]; exact deriv_sinSqrt_at_zero_ne_zero hm1
    have hcos_val : cosSqrt ωm = (-1 : ℂ) ^ (m + 1) := by
      have hr : (((Real.pi * ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) ^ 2 = ωm := by
        rw [hωm_eq]; push_cast; ring
      rw [← hr, cosSqrt_sq, ← Complex.ofReal_cos,
        show Real.pi * ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * Real.pi by ring,
        Real.cos_nat_mul_pi]
      push_cast; rfl
    have hslope : Tendsto (fun z : ℂ => sinSqrt z / (z - ωm)) (𝓝[≠] ωm) (𝓝 (deriv sinSqrt ωm)) := by
      have h := hasDerivAt_iff_tendsto_slope.mp ((sinSqrt_differentiable ωm).hasDerivAt)
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z _
      rw [slope_def_field, hsin0, sub_zero]
    have hnum : Tendsto (fun z : ℂ => cosSqrt z / z) (𝓝[≠] ωm) (𝓝 (cosSqrt ωm / ωm)) :=
      (((cosSqrt_analyticAt' ωm).continuousAt.div continuousAt_id hωm_ne).continuousWithinAt).tendsto
    have htail : Tendsto (fun z : ℂ => (z - ωm) / z) (𝓝[≠] ωm) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℂ => (z - ωm) / z) ωm :=
        (continuousAt_id.sub continuousAt_const).div continuousAt_id hωm_ne
      have ht : Tendsto (fun z : ℂ => (z - ωm) / z) (𝓝[≠] ωm) (𝓝 ((ωm - ωm) / ωm)) :=
        hc.continuousWithinAt.tendsto
      simpa using ht
    have hcomb := (hnum.div hslope hd_ne).sub htail
    have hlim : cosSqrt ωm / ωm / deriv sinSqrt ωm - 0 = 2 := by
      rw [sub_zero, hcos_val, hd_val]
      have hpow : (-1 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hωm_ne, hpow]
    rw [hlim] at hcomb
    have hsin_ne : ∀ᶠ z in 𝓝[≠] ωm, sinSqrt z ≠ 0 := by
      have h := hslope.eventually_ne hd_ne
      filter_upwards [h] with z hz h0
      rw [h0, zero_div] at hz; exact hz rfl
    have hz_ne : ∀ᶠ z in 𝓝[≠] ωm, z ≠ 0 :=
      (continuousAt_id.continuousWithinAt.tendsto).eventually_ne hωm_ne
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hsin_ne, hz_ne] with z hzw hsz hz0
    have hsub : z - ωm ≠ 0 := sub_ne_zero.mpr hzw
    unfold heatIntBorel
    rw [dslope_of_ne _ hz0, slope_def_field, heatIntKernel_zero, sub_zero, sub_zero]
    unfold heatIntKernel
    simp only [Pi.div_apply]
    dsimp only [ωm] at hsub ⊢
    field_simp [hsub, hsz, hz0]
  expType_plus := by
    have heq : Complex.exp (I * ((Real.pi / 3 : ℝ) : ℂ)) =
        Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) := by simp
    rw [heq]
    refine heatBorel_expType_ray (fun v hv => ?_) (fun v hv => heatIntBorel_far_bound (Or.inl rfl) hv)
    have h1 : ContinuousAt heatIntBorel (Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ)) :=
      (heatIntBorel_analyticAt (ray_point_not_heatPole (Or.inl rfl) hv.1)).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) v :=
      continuousAt_const.mul Complex.continuous_ofReal.continuousAt
    exact (ContinuousAt.comp (g := heatIntBorel)
      (f := fun t : ℝ => Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) h1 h2).continuousWithinAt
  expType_minus := by
    have heq : Complex.exp (-I * ((Real.pi / 3 : ℝ) : ℂ)) =
        Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) := by congr 1; push_cast; ring
    rw [heq]
    refine heatBorel_expType_ray (fun v hv => ?_) (fun v hv => heatIntBorel_far_bound (Or.inr rfl) hv)
    have h1 : ContinuousAt heatIntBorel (Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ)) :=
      (heatIntBorel_analyticAt (ray_point_not_heatPole (Or.inr rfl) hv.1)).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) v :=
      continuousAt_const.mul Complex.continuous_ofReal.continuousAt
    exact (ContinuousAt.comp (g := heatIntBorel)
      (f := fun t : ℝ => Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) h1 h2).continuousWithinAt

/-- Complete `MeromorphicBorelData` for the half-integer heat-trace Borel kernel
`ψ_half(w) = ((sinSqrt w)⁻¹ - 1) / w`, with simple poles at `ω_m = (π (m + 1))²`
and alternating residues `2 (-1)^{m+1}`. -/
def heatHalfBorel_meromorphicBorelData :
    MeromorphicBorelData heatHalfBorel heatPole (fun m => 2 * (-1 : ℂ) ^ (m + 1)) where
  θ₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := Real.pi ^ 2 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hθ₀_lt := by linarith [Real.pi_pos]
  hε_pos := by positivity
  ω_pos := heatPole_pos 0
  ω_mono := heatPole_strictMono
  res_ne_zero := fun m => mul_ne_zero two_ne_zero (pow_ne_zero _ (by norm_num))
  analyticOn := fun z hz => heatHalfBorel_analyticAt hz.2
  simple_pole := fun m => by
    let ωm : ℂ := (heatPole m : ℂ)
    have hωm_pos : 0 < heatPole m := heatPole_pos m
    have hωm_ne : ωm ≠ 0 := Complex.ofReal_ne_zero.mpr hωm_pos.ne'
    have hm1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have hωm_eq : ωm = (((Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      dsimp only [ωm]; unfold heatPole; push_cast; rfl
    have hsin0 : sinSqrt ωm = 0 := by
      rw [hωm_eq]; exact (sinSqrt_eq_zero_iff _).mpr ⟨m + 1, hm1, rfl⟩
    have hd_val : deriv sinSqrt ωm = (-1 : ℂ) ^ (m + 1) / (2 * ωm) := by
      rw [hωm_eq, deriv_sinSqrt_at_zero_val hm1]
      push_cast; ring
    have hd_ne : deriv sinSqrt ωm ≠ 0 := by
      rw [hωm_eq]; exact deriv_sinSqrt_at_zero_ne_zero hm1
    have hslope : Tendsto (fun z : ℂ => sinSqrt z / (z - ωm)) (𝓝[≠] ωm) (𝓝 (deriv sinSqrt ωm)) := by
      have h := hasDerivAt_iff_tendsto_slope.mp ((sinSqrt_differentiable ωm).hasDerivAt)
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z _
      rw [slope_def_field, hsin0, sub_zero]
    have hnum : Tendsto (fun z : ℂ => (1 : ℂ) / z) (𝓝[≠] ωm) (𝓝 ((1 : ℂ) / ωm)) :=
      ((continuousAt_const.div continuousAt_id hωm_ne).continuousWithinAt).tendsto
    have htail : Tendsto (fun z : ℂ => (z - ωm) / z) (𝓝[≠] ωm) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℂ => (z - ωm) / z) ωm :=
        (continuousAt_id.sub continuousAt_const).div continuousAt_id hωm_ne
      have ht : Tendsto (fun z : ℂ => (z - ωm) / z) (𝓝[≠] ωm) (𝓝 ((ωm - ωm) / ωm)) :=
        hc.continuousWithinAt.tendsto
      simpa using ht
    have hcomb := (hnum.div hslope hd_ne).sub htail
    have hlim : (1 : ℂ) / ωm / deriv sinSqrt ωm - 0 = 2 * (-1 : ℂ) ^ (m + 1) := by
      rw [sub_zero, hd_val]
      have hpow : (-1 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hωm_ne, hpow]
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hlim] at hcomb
    have hsin_ne : ∀ᶠ z in 𝓝[≠] ωm, sinSqrt z ≠ 0 := by
      have h := hslope.eventually_ne hd_ne
      filter_upwards [h] with z hz h0
      rw [h0, zero_div] at hz; exact hz rfl
    have hz_ne : ∀ᶠ z in 𝓝[≠] ωm, z ≠ 0 :=
      (continuousAt_id.continuousWithinAt.tendsto).eventually_ne hωm_ne
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hsin_ne, hz_ne] with z hzw hsz hz0
    have hsub : z - ωm ≠ 0 := sub_ne_zero.mpr hzw
    unfold heatHalfBorel
    rw [dslope_of_ne _ hz0, slope_def_field, heatHalfKernel_zero, sub_zero, sub_zero]
    unfold heatHalfKernel
    simp only [Pi.div_apply]
    dsimp only [ωm] at hsub ⊢
    field_simp [hsub, hsz, hz0]
  expType_plus := by
    have heq : Complex.exp (I * ((Real.pi / 3 : ℝ) : ℂ)) =
        Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) := by simp
    rw [heq]
    refine heatBorel_expType_ray (fun v hv => ?_) (fun v hv => heatHalfBorel_far_bound (Or.inl rfl) hv)
    have h1 : ContinuousAt heatHalfBorel (Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ)) :=
      (heatHalfBorel_analyticAt (ray_point_not_heatPole (Or.inl rfl) hv.1)).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) v :=
      continuousAt_const.mul Complex.continuous_ofReal.continuousAt
    exact (ContinuousAt.comp (g := heatHalfBorel)
      (f := fun t : ℝ => Complex.exp (I * (((1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) h1 h2).continuousWithinAt
  expType_minus := by
    have heq : Complex.exp (-I * ((Real.pi / 3 : ℝ) : ℂ)) =
        Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) := by congr 1; push_cast; ring
    rw [heq]
    refine heatBorel_expType_ray (fun v hv => ?_) (fun v hv => heatHalfBorel_far_bound (Or.inr rfl) hv)
    have h1 : ContinuousAt heatHalfBorel (Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ)) :=
      (heatHalfBorel_analyticAt (ray_point_not_heatPole (Or.inr rfl) hv.1)).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) v :=
      continuousAt_const.mul Complex.continuous_ofReal.continuousAt
    exact (ContinuousAt.comp (g := heatHalfBorel)
      (f := fun t : ℝ => Complex.exp (I * (((-1 : ℝ) * (Real.pi / 3) : ℝ) : ℂ)) * (t : ℂ)) h1 h2).continuousWithinAt

/-! #### D.4b. Parametric Exponential Integrals, Leibniz Rule, Exponential Tails, and Real Gaussian Moments -/

private lemma iteratedDeriv_mul_Ioi {u₀ : ℝ} {f g : ℝ → ℂ} (n : ℕ)
    (hf : ∀ k ≤ n, ∀ u : ℝ, u₀ < u → DifferentiableAt ℝ (iteratedDeriv k f) u)
    (hg : ∀ k ≤ n, ∀ u : ℝ, u₀ < u → DifferentiableAt ℝ (iteratedDeriv k g) u) :
    ∀ u : ℝ, u₀ < u →
      iteratedDeriv n (fun t => f t * g t) u =
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i f u * iteratedDeriv (n - i) g u := by
  induction n with
  | zero => intro u _; simp
  | succ n ih =>
    intro u hu
    have hloc : iteratedDeriv n (fun t => f t * g t) =ᶠ[𝓝 u]
        fun t => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i f t * iteratedDeriv (n - i) g t := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      exact ih (fun k hk => hf k (by omega)) (fun k hk => hg k (by omega)) t ht
    rw [iteratedDeriv_succ, hloc.deriv_eq]
    have hderiv_term : ∀ i ∈ Finset.range (n + 1),
        HasDerivAt (fun t => (n.choose i : ℂ) * iteratedDeriv i f t * iteratedDeriv (n - i) g t)
          ((n.choose i : ℂ) * (iteratedDeriv (i + 1) f u * iteratedDeriv (n - i) g u +
            iteratedDeriv i f u * iteratedDeriv (n - i + 1) g u)) u := by
      intro i hi
      have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hdf : HasDerivAt (iteratedDeriv i f) (iteratedDeriv (i + 1) f u) u := by
        rw [iteratedDeriv_succ]; exact (hf i (by omega) u hu).hasDerivAt
      have hdg : HasDerivAt (iteratedDeriv (n - i) g) (iteratedDeriv (n - i + 1) g u) u := by
        rw [iteratedDeriv_succ]; exact (hg (n - i) (by omega) u hu).hasDerivAt
      have hmul := (hdf.mul hdg).const_mul (n.choose i : ℂ)
      refine hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      change (n.choose i : ℂ) * iteratedDeriv i f t * iteratedDeriv (n - i) g t =
        (n.choose i : ℂ) * (iteratedDeriv i f t * iteratedDeriv (n - i) g t)
      ring
    have hsum_d := HasDerivAt.fun_sum hderiv_term
    rw [hsum_d.deriv]
    have hsplit :
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) * (iteratedDeriv (i + 1) f u * iteratedDeriv (n - i) g u +
            iteratedDeriv i f u * iteratedDeriv (n - i + 1) g u) =
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv (i + 1) f u * iteratedDeriv (n - i) g u) +
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i f u * iteratedDeriv (n - i + 1) g u) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    have hS1 :
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv (i + 1) f u * iteratedDeriv (n - i) g u =
        ∑ j ∈ Finset.range (n + 2),
          (if j = 0 then (0 : ℂ) else (n.choose (j - 1) : ℂ)) * iteratedDeriv j f u * iteratedDeriv (n + 1 - j) g u := by
      symm
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ite_eq_right_iff.mpr (fun h => (Nat.succ_ne_zero i h).elim), Nat.add_sub_cancel, Nat.succ_sub_succ_eq_sub]
    have hS2 :
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i f u * iteratedDeriv (n - i + 1) g u =
        ∑ j ∈ Finset.range (n + 2),
          (if j = n + 1 then (0 : ℂ) else (n.choose j : ℂ)) * iteratedDeriv j f u * iteratedDeriv (n + 1 - j) g u := by
      symm
      rw [Finset.sum_range_succ]
      simp only [↓reduceIte, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hilt : i < n + 1 := Finset.mem_range.mp hi
      have hne : i ≠ n + 1 := by omega
      have hsub : n + 1 - i = n - i + 1 := by omega
      rw [ite_eq_right_iff.mpr (fun h => (hne h).elim), hsub]
    rw [hS1, hS2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases eq_or_ne j 0 with rfl | hj0
    · have h0n : (0 : ℕ) ≠ n + 1 := (Nat.succ_ne_zero n).symm
      rw [ite_eq_left_iff.mpr (fun h => (h rfl).elim), ite_eq_right_iff.mpr (fun h => (h0n h).elim)]
      simp
    · rcases eq_or_ne j (n + 1) with rfl | hjn
      · rw [ite_eq_right_iff.mpr (fun h => (Nat.succ_ne_zero n h).elim),
          ite_eq_left_iff.mpr (fun h => (h rfl).elim), Nat.add_sub_cancel]
        simp
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hk_ne : k + 1 ≠ n + 1 := hjn
        have hch : ((n + 1).choose (k + 1) : ℂ) = (n.choose k : ℂ) + (n.choose (k + 1) : ℂ) := by
          exact_mod_cast Nat.choose_succ_succ n k
        rw [ite_eq_right_iff.mpr (fun h => (Nat.succ_ne_zero k h).elim),
          ite_eq_right_iff.mpr (fun h => (hk_ne h).elim), Nat.succ_sub_one, Nat.succ_eq_add_one, hch]
        ring

private noncomputable def invSqrtPi (u : ℝ) : ℂ := ((Real.sqrt (Real.pi * u) : ℝ) : ℂ)⁻¹

private noncomputable def invSqrtPiCoeff : ℕ → ℝ
  | 0 => 1
  | j + 1 => -((j : ℝ) + 1 / 2) * invSqrtPiCoeff j

private lemma iteratedDeriv_invSqrtPi (j : ℕ) :
    ∀ u : ℝ, 0 < u →
      iteratedDeriv j invSqrtPi u =
        (invSqrtPiCoeff j : ℂ) * invSqrtPi u * ((u : ℂ)⁻¹ ^ j) := by
  induction j with
  | zero => intro u _; simp [invSqrtPiCoeff]
  | succ j ih =>
    intro u hu
    have hloc : iteratedDeriv j invSqrtPi =ᶠ[𝓝 u]
        fun t : ℝ => (invSqrtPiCoeff j : ℂ) * invSqrtPi t * ((t : ℂ)⁻¹ ^ j) := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ, hloc.deriv_eq]
    have hpow_eq : (fun t : ℝ => (invSqrtPiCoeff j : ℂ) * invSqrtPi t * ((t : ℂ)⁻¹ ^ j)) =ᶠ[𝓝 u]
        fun t : ℝ => (((invSqrtPiCoeff j / Real.sqrt Real.pi) * t ^ (-((j : ℝ) + 1 / 2)) : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      unfold invSqrtPi
      rw [Real.sqrt_mul Real.pi_pos.le t, Complex.ofReal_mul, mul_inv,
        Real.rpow_neg ht.le, Real.rpow_add ht, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      push_cast
      rw [inv_pow]
      field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne', (Real.sqrt_pos.mpr ht).ne', htC]
    rw [hpow_eq.deriv_eq]
    have hdr : HasDerivAt (fun t : ℝ => (invSqrtPiCoeff j / Real.sqrt Real.pi) * t ^ (-((j : ℝ) + 1 / 2)))
        ((invSqrtPiCoeff j / Real.sqrt Real.pi) * (-((j : ℝ) + 1 / 2) * u ^ (-((j : ℝ) + 1 / 2) - 1))) u :=
      (Real.hasDerivAt_rpow_const (Or.inl hu.ne')).const_mul _
    have hdc := hdr.ofReal_comp
    rw [hdc.deriv]
    dsimp only [invSqrtPi]
    rw [show invSqrtPiCoeff (j + 1) = -((j : ℝ) + 1 / 2) * invSqrtPiCoeff j from rfl,
      Real.sqrt_mul Real.pi_pos.le u,
      show -((j : ℝ) + 1 / 2) - 1 = -(((j + 1 : ℕ) : ℝ) + 1 / 2) by push_cast; ring,
      Real.rpow_neg hu.le, Real.rpow_add hu, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    push_cast
    rw [mul_inv, inv_pow]
    field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne', (Real.sqrt_pos.mpr hu).ne', huC]

private lemma differentiableAt_iteratedDeriv_invSqrtPi (j : ℕ) {u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (iteratedDeriv j invSqrtPi) u := by
  have hloc : iteratedDeriv j invSqrtPi =ᶠ[𝓝 u]
      fun t : ℝ => (invSqrtPiCoeff j : ℂ) * invSqrtPi t * ((t : ℂ)⁻¹ ^ j) := by
    filter_upwards [Ioi_mem_nhds hu] with t ht
    exact iteratedDeriv_invSqrtPi j t ht
  rw [hloc.differentiableAt_iff]
  have hsq : DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (Real.pi * t)) u :=
    (Real.hasDerivAt_sqrt (mul_pos Real.pi_pos hu).ne').comp u
      ((hasDerivAt_id u).const_mul Real.pi) |>.differentiableAt
  have hinv : DifferentiableAt ℝ invSqrtPi u :=
    (Complex.ofRealCLM.differentiableAt.comp u hsq).inv
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hu)).ne')
  have hpow : DifferentiableAt ℝ (fun t : ℝ => ((t : ℂ)⁻¹ ^ j)) u :=
    (Complex.ofRealCLM.differentiableAt.inv (Complex.ofReal_ne_zero.mpr hu.ne')).pow j
  exact (differentiableAt_const _ |>.mul hinv).mul hpow

private lemma iteratedDeriv_parametric_exp_integral
    {s : Set ℝ} (hs : MeasurableSet s) {φ g : ℝ → ℂ} {u₀ : ℝ}
    (hφ_m : AEStronglyMeasurable φ (volume.restrict s))
    (hg_m : AEStronglyMeasurable g (volume.restrict s))
    (hφ_re : ∀ x ∈ s, 0 ≤ (φ x).re)
    (hdom : ∀ k : ℕ, IntegrableOn (fun x : ℝ => ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-u₀ * (φ x).re)) s volume) :
    ∀ (j : ℕ),
      (∀ u : ℝ, u₀ < u →
        iteratedDeriv j (fun v : ℝ => ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x) u =
          ∫ x in s, (-φ x) ^ j * Complex.exp (-(u : ℂ) * φ x) * g x) ∧
      (∀ u : ℝ, u₀ < u →
        DifferentiableAt ℝ (iteratedDeriv j (fun v : ℝ => ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x)) u) := by
  have haes : ∀ (k : ℕ) (v : ℝ),
      AEStronglyMeasurable (fun x : ℝ => (-φ x) ^ k * Complex.exp (-(v : ℂ) * φ x) * g x) (volume.restrict s) :=
    fun k v => ((hφ_m.neg.pow k).mul
      (Complex.continuous_exp.comp_aestronglyMeasurable (aestronglyMeasurable_const.mul hφ_m))).mul hg_m
  have hnorm_le : ∀ (k : ℕ) {v : ℝ} {x : ℝ}, u₀ ≤ v → x ∈ s →
      ‖(-φ x) ^ k * Complex.exp (-(v : ℂ) * φ x) * g x‖ ≤
        ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-u₀ * (φ x).re) := by
    intro k v x hv hx
    rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_exp]
    have hre : (-(v : ℂ) * φ x).re = -v * (φ x).re := by simp [Complex.mul_re]
    rw [hre]
    have hexp : Real.exp (-v * (φ x).re) ≤ Real.exp (-u₀ * (φ x).re) :=
      Real.exp_le_exp.mpr (by nlinarith [hφ_re x hx])
    calc ‖φ x‖ ^ k * Real.exp (-v * (φ x).re) * ‖g x‖
        = ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-v * (φ x).re) := by ring
      _ ≤ ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-u₀ * (φ x).re) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hint_step : ∀ (k : ℕ) (u : ℝ), u₀ < u →
      Integrable (fun x : ℝ => (-φ x) ^ k * Complex.exp (-(u : ℂ) * φ x) * g x) (volume.restrict s) := by
    intro k u hu
    refine (hdom k).mono' (haes k u) ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    exact hnorm_le k hu.le hx
  have hhasDeriv_step : ∀ (k : ℕ) (u : ℝ), u₀ < u →
      HasDerivAt (fun v : ℝ => ∫ x in s, (-φ x) ^ k * Complex.exp (-(v : ℂ) * φ x) * g x)
        (∫ x in s, (-φ x) ^ (k + 1) * Complex.exp (-(u : ℂ) * φ x) * g x) u := by
    intro k u hu
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (v : ℝ) (x : ℝ) => (-φ x) ^ k * Complex.exp (-(v : ℂ) * φ x) * g x)
      (F' := fun (v : ℝ) (x : ℝ) => (-φ x) ^ (k + 1) * Complex.exp (-(v : ℂ) * φ x) * g x)
      (Ioi_mem_nhds hu)
      (Filter.Eventually.of_forall fun v => haes k v)
      (hint_step k u hu)
      (haes (k + 1) u)
      ?_ (hdom (k + 1)) ?_).2
    · filter_upwards [ae_restrict_mem hs] with x hx v hv
      exact hnorm_le (k + 1) (Set.mem_Ioi.mp hv).le hx
    · filter_upwards [ae_restrict_mem hs] with x _ v _
      have hd1 : HasDerivAt (fun w : ℝ => -(w : ℂ) * φ x) (-φ x) v := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := v)).neg).mul_const (φ x)
      have hd2 : HasDerivAt (fun w : ℝ => Complex.exp (-(w : ℂ) * φ x))
          (Complex.exp (-(v : ℂ) * φ x) * (-φ x)) v := hd1.cexp
      have hd3 := (hd2.const_mul ((-φ x) ^ k)).mul_const (g x)
      exact hd3.congr_deriv (by rw [pow_succ]; ring)
  have heq : ∀ (j : ℕ) (u : ℝ), u₀ < u →
      iteratedDeriv j (fun v : ℝ => ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x) u =
        ∫ x in s, (-φ x) ^ j * Complex.exp (-(u : ℂ) * φ x) * g x := by
    intro j
    induction j with
    | zero => intro u _; simp
    | succ j ih =>
      intro u hu
      have hloc : iteratedDeriv j (fun v : ℝ => ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x) =ᶠ[𝓝 u]
          fun v => ∫ x in s, (-φ x) ^ j * Complex.exp (-(v : ℂ) * φ x) * g x := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact ih v hv
      rw [iteratedDeriv_succ, hloc.deriv_eq, (hhasDeriv_step j u hu).deriv]
  intro j
  refine ⟨heq j, fun u hu => ?_⟩
  have hloc : iteratedDeriv j (fun v : ℝ => ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x) =ᶠ[𝓝 u]
      fun v => ∫ x in s, (-φ x) ^ j * Complex.exp (-(v : ℂ) * φ x) * g x := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact heq j v hv
  exact hloc.differentiableAt_iff.mpr (hhasDeriv_step j u hu).differentiableAt

private lemma exp_decay_parametric_integral
    {s : Set ℝ} (hs : MeasurableSet s) {φ g : ℝ → ℂ}
    (hφ_m : AEStronglyMeasurable φ (volume.restrict s))
    (hg_m : AEStronglyMeasurable g (volume.restrict s))
    (hφ_re : ∀ x ∈ s, (2 : ℝ) ≤ (φ x).re)
    (hdom : ∀ k : ℕ, IntegrableOn (fun x : ℝ => ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re)) s volume) :
    (∀ (j : ℕ) (u : ℝ), (1 / 2 : ℝ) < u →
      DifferentiableAt ℝ (iteratedDeriv j (fun v : ℝ => invSqrtPi v * ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x)) u) ∧
    (∀ j : ℕ, ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv j (fun v : ℝ => invSqrtPi v * ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x) u‖ ≤
        C * Real.exp (-2 * u)) := by
  let H : ℝ → ℂ := fun v => ∫ x in s, Complex.exp (-(v : ℂ) * φ x) * g x
  have hH := iteratedDeriv_parametric_exp_integral hs hφ_m hg_m
    (fun x hx => by linarith [hφ_re x hx]) hdom
  have hH_bd : ∀ (k : ℕ) (u : ℝ), 1 ≤ u →
      ‖iteratedDeriv k H u‖ ≤
        (Real.exp 1 * ∫ x in s, ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re)) * Real.exp (-2 * u) := by
    intro k u hu
    rw [(hH k).1 u (by linarith)]
    calc ‖∫ x in s, (-φ x) ^ k * Complex.exp (-(u : ℂ) * φ x) * g x‖
        ≤ ∫ x in s, ‖(-φ x) ^ k * Complex.exp (-(u : ℂ) * φ x) * g x‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x in s, (‖φ x‖ ^ k * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re)) * Real.exp (-(2 * u - 1)) := by
          refine setIntegral_mono_on ?_ ((hdom k).mul_const _) hs fun x hx => ?_
          · refine ((hdom k).mono' ?_ ?_).norm
            · exact ((hφ_m.neg.pow k).mul
                (Complex.continuous_exp.comp_aestronglyMeasurable
                  (aestronglyMeasurable_const.mul hφ_m))).mul hg_m
            · filter_upwards [ae_restrict_mem hs] with x hx
              rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_exp,
                (show (-(u : ℂ) * φ x).re = -u * (φ x).re by simp [Complex.mul_re])]
              have hexp : Real.exp (-u * (φ x).re) ≤ Real.exp (-(1 / 2 : ℝ) * (φ x).re) :=
                Real.exp_le_exp.mpr (by nlinarith [hφ_re x hx])
              calc ‖φ x‖ ^ k * Real.exp (-u * (φ x).re) * ‖g x‖
                  = ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-u * (φ x).re) := by ring
                _ ≤ ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re) :=
                    mul_le_mul_of_nonneg_left hexp (by positivity)
          · rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_exp,
              (show (-(u : ℂ) * φ x).re = -u * (φ x).re by simp [Complex.mul_re])]
            have hre_le : -u * (φ x).re ≤ -(1 / 2 : ℝ) * (φ x).re + -(2 * u - 1) := by
              nlinarith [hφ_re x hx]
            have hexp : Real.exp (-u * (φ x).re) ≤
                Real.exp (-(1 / 2 : ℝ) * (φ x).re) * Real.exp (-(2 * u - 1)) := by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hre_le
            calc ‖φ x‖ ^ k * Real.exp (-u * (φ x).re) * ‖g x‖
                = ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-u * (φ x).re) := by ring
              _ ≤ ‖φ x‖ ^ k * ‖g x‖ * (Real.exp (-(1 / 2 : ℝ) * (φ x).re) * Real.exp (-(2 * u - 1))) :=
                  mul_le_mul_of_nonneg_left hexp (by positivity)
              _ = (‖φ x‖ ^ k * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re)) * Real.exp (-(2 * u - 1)) := by ring
      _ = (∫ x in s, ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re)) * Real.exp (-(2 * u - 1)) :=
          integral_mul_const _ _
      _ = (Real.exp 1 * ∫ x in s, ‖φ x‖ ^ k * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re)) * Real.exp (-2 * u) := by
          rw [show -(2 * u - 1) = 1 + (-2 * u) by ring, Real.exp_add]; ring
  have hmul : ∀ (j : ℕ) (u : ℝ), (1 / 2 : ℝ) < u →
      iteratedDeriv j (fun v => invSqrtPi v * H v) u =
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i invSqrtPi u * iteratedDeriv (j - i) H u :=
    fun j => iteratedDeriv_mul_Ioi j (fun k _ u hu => differentiableAt_iteratedDeriv_invSqrtPi k (by linarith))
      (fun k _ u hu => (hH k).2 u hu)
  constructor
  · intro j u hu
    have hloc : iteratedDeriv j (fun v => invSqrtPi v * H v) =ᶠ[𝓝 u]
        fun v => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i invSqrtPi v * iteratedDeriv (j - i) H v := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact hmul j v hv
    rw [hloc.differentiableAt_iff]
    refine DifferentiableAt.fun_sum fun i _ => ?_
    exact (differentiableAt_const _ |>.mul (differentiableAt_iteratedDeriv_invSqrtPi i (by linarith))).mul
      ((hH (j - i)).2 u hu)
  · intro j
    let C : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      (|invSqrtPiCoeff i| * (Real.sqrt Real.pi)⁻¹) *
      (Real.exp 1 * ∫ x in s, ‖φ x‖ ^ (j - i) * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re))
    refine ⟨C, fun u hu => ?_⟩
    rw [hmul j u (by linarith)]
    calc ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i invSqrtPi u * iteratedDeriv (j - i) H u‖
        ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i invSqrtPi u * iteratedDeriv (j - i) H u‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            ((j.choose i : ℝ) * (|invSqrtPiCoeff i| * (Real.sqrt Real.pi)⁻¹) *
              (Real.exp 1 * ∫ x in s, ‖φ x‖ ^ (j - i) * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re))) *
              Real.exp (-2 * u) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_natCast, iteratedDeriv_invSqrtPi i u (by linarith),
            norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_inv,
            Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ u)]
          have hinv_le : ‖invSqrtPi u‖ ≤ (Real.sqrt Real.pi)⁻¹ := by
            unfold invSqrtPi
            rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
            exact inv_anti₀ (Real.sqrt_pos.mpr Real.pi_pos) (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
          have hpow_le : (u⁻¹) ^ i ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu)
          have hw_le : |invSqrtPiCoeff i| * ‖invSqrtPi u‖ * (u⁻¹) ^ i ≤
              |invSqrtPiCoeff i| * (Real.sqrt Real.pi)⁻¹ := by
            calc |invSqrtPiCoeff i| * ‖invSqrtPi u‖ * (u⁻¹) ^ i
                ≤ |invSqrtPiCoeff i| * (Real.sqrt Real.pi)⁻¹ * 1 :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hinv_le (abs_nonneg _)) hpow_le (by positivity) (by positivity)
              _ = |invSqrtPiCoeff i| * (Real.sqrt Real.pi)⁻¹ := mul_one _
          have h1 : (j.choose i : ℝ) * (|invSqrtPiCoeff i| * ‖invSqrtPi u‖ * (u⁻¹) ^ i) ≤
              (j.choose i : ℝ) * (|invSqrtPiCoeff i| * (Real.sqrt Real.pi)⁻¹) :=
            mul_le_mul_of_nonneg_left hw_le (Nat.cast_nonneg _)
          have h2 := hH_bd (j - i) u hu
          calc (j.choose i : ℝ) * (|invSqrtPiCoeff i| * ‖invSqrtPi u‖ * (u⁻¹) ^ i) * ‖iteratedDeriv (j - i) H u‖
              ≤ ((j.choose i : ℝ) * (|invSqrtPiCoeff i| * (Real.sqrt Real.pi)⁻¹)) *
                  ((Real.exp 1 * ∫ x in s, ‖φ x‖ ^ (j - i) * ‖g x‖ * Real.exp (-(1 / 2 : ℝ) * (φ x).re)) *
                    Real.exp (-2 * u)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = _ := by ring
      _ = C * Real.exp (-2 * u) := by dsimp only [C]; rw [Finset.sum_mul]

private lemma integrable_pow_mul_exp_neg_sq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n * Real.exp (-c * x ^ 2)) volume := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-(c / 2) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by linarith)
  have hbound : ∃ B : ℝ, ∀ x : ℝ, |x| ^ n * Real.exp (-(c / 2) * x ^ 2) ≤ B := by
    have hpow : ∀ y : ℝ, 0 ≤ y → y ^ n ≤ (n.factorial : ℝ) / (c / 2) ^ n * Real.exp ((c / 2) * y) := by
      intro y hy
      have hsum := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ (c / 2) * y) (n + 1)
      have hterm : ((c / 2) * y) ^ n / (n.factorial : ℝ) ≤
          ∑ i ∈ Finset.range (n + 1), ((c / 2) * y) ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (f := fun i => ((c / 2) * y) ^ i / (i.factorial : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have hle := hterm.trans hsum
      rw [mul_pow] at hle
      have hpos_c : 0 < (c / 2) ^ n := by positivity
      have hpos_f : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
      rw [div_le_iff₀ hpos_f] at hle
      have h2 : y ^ n ≤ (n.factorial : ℝ) * Real.exp ((c / 2) * y) / (c / 2) ^ n :=
        (le_div_iff₀' hpos_c).mpr (by linarith)
      linarith [show (n.factorial : ℝ) * Real.exp ((c / 2) * y) / (c / 2) ^ n =
        (n.factorial : ℝ) / (c / 2) ^ n * Real.exp ((c / 2) * y) by ring]
    refine ⟨max 1 ((n.factorial : ℝ) / (c / 2) ^ n), fun x => ?_⟩
    by_cases hx1 : |x| ≤ 1
    · calc |x| ^ n * Real.exp (-(c / 2) * x ^ 2)
          ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg x) hx1)
              (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])) (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
        _ ≤ max 1 _ := le_max_left _ _
    · push Not at hx1
      have hle_sq : |x| ^ n ≤ (x ^ 2) ^ n := by
        have h1x : |x| ≤ x ^ 2 := by rw [← sq_abs]; nlinarith
        exact pow_le_pow_left₀ (abs_nonneg x) h1x n
      have hex := hpow (x ^ 2) (sq_nonneg x)
      have hprod : Real.exp ((c / 2) * x ^ 2) * Real.exp (-(c / 2) * x ^ 2) = 1 := by
        rw [← Real.exp_add]; simp
      calc |x| ^ n * Real.exp (-(c / 2) * x ^ 2)
          ≤ ((n.factorial : ℝ) / (c / 2) ^ n * Real.exp ((c / 2) * x ^ 2)) * Real.exp (-(c / 2) * x ^ 2) :=
            mul_le_mul_of_nonneg_right (hle_sq.trans hex) (Real.exp_pos _).le
        _ = (n.factorial : ℝ) / (c / 2) ^ n := by rw [mul_assoc, hprod, mul_one]
        _ ≤ max 1 _ := le_max_right _ _
  obtain ⟨B, hB⟩ := hbound
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |x| ^ n * Real.exp (-c * x ^ 2)) volume :=
    ((continuous_abs.pow n).mul (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2)))).aestronglyMeasurable
  refine (h1.const_mul (max B 0)).mono' hmeas (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hsplit : Real.exp (-c * x ^ 2) = Real.exp (-(c / 2) * x ^ 2) * Real.exp (-(c / 2) * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right ((hB x).trans (le_max_left B 0)) (Real.exp_pos _).le

private lemma real_gaussian_even_moment (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * m) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * (((2 * m).factorial : ℂ) / (4 ^ m * (m.factorial : ℂ))) *
        ((u ^ (-((m : ℝ) + 1 / 2)) : ℝ) : ℂ) := by
  induction m generalizing u with
  | zero =>
    have hrew : (fun x : ℝ => Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * 0)) =
        fun x : ℝ => Complex.ofRealCLM (Real.exp (-u * x ^ 2)) := by
      funext x; simp [Complex.ofReal_exp]
    rw [hrew, Complex.ofRealCLM.integral_comp_comm (integrable_exp_neg_mul_sq hu), integral_gaussian u]
    simp only [Complex.ofRealCLM_apply, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, div_one,
      Nat.cast_zero, zero_add]
    rw [Real.sqrt_div Real.pi_pos.le u, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
    push_cast; ring
  | succ m ih =>
    have hdom : ∀ k : ℕ, IntegrableOn
        (fun x : ℝ => ‖((x : ℂ) ^ 2)‖ ^ k * ‖((x : ℂ) ^ (2 * m))‖ * Real.exp (-(u / 2) * ((x : ℂ) ^ 2).re))
        Set.univ volume := by
      intro k
      rw [integrableOn_univ]
      have heq : (fun x : ℝ => ‖((x : ℂ) ^ 2)‖ ^ k * ‖((x : ℂ) ^ (2 * m))‖ * Real.exp (-(u / 2) * ((x : ℂ) ^ 2).re)) =
          fun x : ℝ => |x| ^ (2 * k + 2 * m) * Real.exp (-(u / 2) * x ^ 2) := by
        funext x
        rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, ← pow_add,
          (show ((x : ℂ) ^ 2).re = x ^ 2 by rw [← Complex.ofReal_pow, Complex.ofReal_re])]
      rw [heq]
      exact integrable_pow_mul_exp_neg_sq (by linarith) _
    have hpar := iteratedDeriv_parametric_exp_integral MeasurableSet.univ
      (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ 2)).aestronglyMeasurable
      (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ (2 * m))).aestronglyMeasurable
      (fun x _ => by rw [← Complex.ofReal_pow, Complex.ofReal_re]; exact sq_nonneg x) hdom
    have hd1 := (hpar 1).1 u (by linarith)
    rw [iteratedDeriv_one, Measure.restrict_univ] at hd1
    have hloc : (fun v : ℝ => ∫ x : ℝ, Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * m)) =ᶠ[𝓝 u]
        fun v : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ) * (((2 * m).factorial : ℂ) / (4 ^ m * (m.factorial : ℂ))) *
          ((v ^ (-((m : ℝ) + 1 / 2)) : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact ih hv
    rw [hloc.deriv_eq] at hd1
    have hdr : HasDerivAt (fun v : ℝ => v ^ (-((m : ℝ) + 1 / 2)))
        (-((m : ℝ) + 1 / 2) * u ^ (-((m : ℝ) + 1 / 2) - 1)) u :=
      Real.hasDerivAt_rpow_const (Or.inl hu.ne')
    have hdc := hdr.ofReal_comp.const_mul
      (((Real.sqrt Real.pi : ℝ) : ℂ) * (((2 * m).factorial : ℂ) / (4 ^ m * (m.factorial : ℂ))))
    rw [hdc.deriv] at hd1
    have hneg_int : (∫ x : ℝ, (-(x : ℂ) ^ 2) ^ 1 * Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * m)) =
        -(∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * (m + 1))) := by
      rw [← integral_neg]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      rw [pow_one, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]; ring
    rw [hneg_int] at hd1
    have hfact : ((2 * (m + 1)).factorial : ℂ) =
        (2 * (m : ℂ) + 2) * (2 * (m : ℂ) + 1) * ((2 * m).factorial : ℂ) := by
      have hnat : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
      exact_mod_cast hnat
    have hmf : ((m + 1).factorial : ℂ) = ((m : ℂ) + 1) * (m.factorial : ℂ) := by
      exact_mod_cast Nat.factorial_succ m
    have hm1_ne : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hmf_ne : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
    have h4_ne : (4 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    have hexp_eq : -((m : ℝ) + 1 / 2) - 1 = -(((m + 1 : ℕ) : ℝ) + 1 / 2) := by push_cast; ring
    rw [hexp_eq] at hd1
    have heq2 : ∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * (m + 1)) =
        -(((Real.sqrt Real.pi : ℝ) : ℂ) * (((2 * m).factorial : ℂ) / (4 ^ m * (m.factorial : ℂ))) *
          (((-((m : ℝ) + 1 / 2) * u ^ (-(((m + 1 : ℕ) : ℝ) + 1 / 2))) : ℝ) : ℂ)) := by
      calc ∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * (m + 1))
          = -(-(∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * (m + 1)))) := (neg_neg _).symm
        _ = _ := congrArg Neg.neg hd1.symm
    rw [heq2, hfact, hmf, pow_succ]
    push_cast
    field_simp [hm1_ne, hmf_ne, h4_ne]
    ring

private lemma invSqrtPi_mul_real_gaussian_even_moment (m : ℕ) {u : ℝ} (hu : 0 < u) :
    invSqrtPi u * ∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * m) =
      (((2 * m).factorial : ℂ) / (4 ^ m * (m.factorial : ℂ))) * ((u : ℂ)⁻¹ ^ (m + 1)) := by
  rw [real_gaussian_even_moment m hu]
  unfold invSqrtPi
  rw [Real.sqrt_mul Real.pi_pos.le u, Complex.ofReal_mul, mul_inv,
    Real.rpow_neg hu.le, Real.rpow_add hu, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsu : ((Real.sqrt u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne'
  have hsq : ((Real.sqrt u : ℝ) : ℂ) * ((Real.sqrt u : ℝ) : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
  push_cast
  rw [pow_succ, inv_pow, ← hsq]
  field_simp [hpi, hsu]

/-! #### D.4c. Unified Shifted-Gaussian Asymptotics (`gaussianKernelIntegral_hasAsympExp`) -/

private noncomputable def truncEval (S : PowerSeries ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, PowerSeries.coeff k S * ((u : ℂ)⁻¹ ^ k)

private lemma coeff_d_u_zero (S : PowerSeries ℂ) : PowerSeries.coeff 0 (d_u S) = 0 := by
  unfold d_u
  rw [map_neg, sq, mul_assoc, PowerSeries.coeff_zero_X_mul, neg_zero]

private lemma coeff_d_u_one (S : PowerSeries ℂ) : PowerSeries.coeff 1 (d_u S) = 0 := by
  unfold d_u
  rw [map_neg, sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul, neg_zero]

private lemma coeff_d_u_succ_succ (S : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (n + 2) (d_u S) = -((n + 1 : ℕ) : ℂ) * PowerSeries.coeff (n + 1) S := by
  unfold d_u
  rw [map_neg, sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative]
  push_cast; ring

private lemma hasDerivAt_truncEval (S : PowerSeries ℂ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (truncEval S N) (truncEval (d_u S) (N + 1) u) u := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hterm : ∀ k ∈ Finset.range N,
      HasDerivAt (fun v : ℝ => PowerSeries.coeff k S * ((v : ℂ)⁻¹ ^ k))
        (PowerSeries.coeff k S * (-(k : ℂ) * ((u : ℂ)⁻¹ ^ (k + 1)))) u := by
    intro k _
    have hinv : HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹) (-((u : ℂ) ^ 2)⁻¹) u := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := u)).fun_inv huC
      refine h.congr_deriv ?_
      simp [neg_div, one_div]
    have hpow := hinv.fun_pow k
    refine (hpow.const_mul (PowerSeries.coeff k S)).congr_deriv ?_
    cases k with
    | zero => simp
    | succ m =>
      rw [Nat.add_sub_cancel, pow_succ, pow_succ, inv_pow, inv_pow]
      field_simp [huC]; ring
  have hsum := HasDerivAt.fun_sum hterm
  refine hsum.congr_deriv ?_
  unfold truncEval
  rw [Finset.sum_range_succ', coeff_d_u_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases k with
  | zero => simp [coeff_d_u_one]
  | succ m =>
    rw [coeff_d_u_succ_succ]
    ring

private lemma iteratedDeriv_truncEval (S : PowerSeries ℂ) (N j : ℕ) :
    ∀ u : ℝ, 0 < u →
      iteratedDeriv j (truncEval S N) u = truncEval (d_u^[j] S) (N + j) u := by
  induction j generalizing S N with
  | zero => intro u _; simp
  | succ j ih =>
    intro u hu
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hloc : deriv (truncEval S N) =ᶠ[𝓝 u] truncEval (d_u S) (N + 1) := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact (hasDerivAt_truncEval S N hv).deriv
    have hloc_iter : iteratedDeriv j (deriv (truncEval S N)) u =
        iteratedDeriv j (truncEval (d_u S) (N + 1)) u := hloc.iteratedDeriv_eq j
    rw [hloc_iter, ih (d_u S) (N + 1) u hu, show N + 1 + j = N + (j + 1) by omega]

private lemma iteratedDeriv_id_ge_two (m : ℕ) :
    iteratedDeriv (m + 2) (fun w : ℂ => w) = 0 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have h1 : deriv (fun w : ℂ => w) = fun _ => (1 : ℂ) := deriv_id''
  have h2 : deriv (fun _ : ℂ => (1 : ℂ)) = fun _ => (0 : ℂ) := funext fun w => deriv_const w (1 : ℂ)
  rw [h1, h2]
  funext w
  simp

private lemma iteratedDeriv_dslope_zero {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ 0) (k : ℕ) :
    ((k + 1 : ℕ) : ℂ) * iteratedDeriv k (dslope ψ 0) 0 = iteratedDeriv (k + 1) ψ 0 := by
  have hmul_eq : (fun w : ℂ => w * dslope ψ 0 w) = fun w : ℂ => ψ w - ψ 0 := by
    funext w
    have h := sub_smul_dslope ψ 0 w
    simpa [sub_zero, smul_eq_mul] using h
  have hL : iteratedDeriv (k + 1) (fun w : ℂ => w * dslope ψ 0 w) 0 =
      ((k + 1 : ℕ) : ℂ) * iteratedDeriv k (dslope ψ 0) 0 := by
    have hleib := iteratedDeriv_mul (n := k + 1) (x := (0 : ℂ))
      (f := fun w : ℂ => w) (g := dslope ψ 0)
      analyticAt_id.contDiffAt (hψ.dslope 0).contDiffAt
    change iteratedDeriv (k + 1) ((fun w : ℂ => w) * dslope ψ 0) 0 = _
    rw [hleib, Finset.sum_eq_single 1]
    · simp [Nat.choose_one_right, iteratedDeriv_one]
    · intro i _ hi1
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
        rw [iteratedDeriv_id_ge_two m]; simp
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  have hR : iteratedDeriv (k + 1) (fun w : ℂ => ψ w - ψ 0) 0 = iteratedDeriv (k + 1) ψ 0 := by
    rw [iteratedDeriv_succ']
    have hderiv_sub : deriv (fun w : ℂ => ψ w - ψ 0) = deriv ψ := by
      funext w; exact deriv_sub_const (ψ 0)
    rw [hderiv_sub, ← iteratedDeriv_succ']
  rw [← hL, hmul_eq, hR]

private lemma dslope_taylor_remainder {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∀ {ψ : ℂ → ℂ}, (∀ w ∈ Metric.closedBall (0 : ℂ) R, AnalyticAt ℂ ψ w) →
      ∃ rem : ℂ → ℂ, (∀ w ∈ Metric.closedBall (0 : ℂ) R, AnalyticAt ℂ rem w) ∧
        ∀ w : ℂ, ψ w =
          (∑ k ∈ Finset.range N, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) * w ^ k) + w ^ N * rem w := by
  induction N with
  | zero =>
    intro ψ hψ
    exact ⟨ψ, hψ, fun w => by simp⟩
  | succ N ih =>
    intro ψ hψ
    have hψ0 : AnalyticAt ℂ ψ 0 := hψ 0 (Metric.mem_closedBall_self hR)
    have hd_an : ∀ w ∈ Metric.closedBall (0 : ℂ) R, AnalyticAt ℂ (dslope ψ 0) w :=
      fun w hw => (hψ w hw).dslope 0
    obtain ⟨rem, hrem_an, hrem_eq⟩ := ih hd_an
    refine ⟨rem, hrem_an, fun w => ?_⟩
    have hsl : ψ w = ψ 0 + w * dslope ψ 0 w := by
      have h := sub_smul_dslope ψ 0 w
      simp only [sub_zero, smul_eq_mul] at h
      linear_combination -h
    rw [hsl, hrem_eq w, mul_add, Finset.mul_sum, Finset.sum_range_succ']
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
    have hsum_eq :
        ∑ k ∈ Finset.range N, w * (iteratedDeriv k (dslope ψ 0) 0 / (k.factorial : ℂ) * w ^ k) =
        ∑ k ∈ Finset.range N, iteratedDeriv (k + 1) ψ 0 / ((k + 1).factorial : ℂ) * w ^ (k + 1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hdk := iteratedDeriv_dslope_zero hψ0 k
      have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have hfac : ((k + 1).factorial : ℂ) = ((k + 1 : ℕ) : ℂ) * (k.factorial : ℂ) := by
        exact_mod_cast Nat.factorial_succ k
      rw [← hdk, hfac, pow_succ']
      field_simp [hkf, hk1]
    rw [hsum_eq, ← mul_assoc, ← pow_succ']
    ring

/-- Shifted horizontal Gaussian integral `G_K(u) = (1 / √(π u)) ∫_{-∞}^∞ e^{-u (x + i/2)²} K((x + i/2)²) dx`. -/
private noncomputable def gaussianKernelIntegral (K : ℂ → ℂ) (u : ℝ) : ℂ :=
  invSqrtPi u * ∫ x : ℝ, Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) * K (((x : ℂ) + I / 2) ^ 2)

private lemma re_neg_mul_line_sq (u x : ℝ) :
    (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2).re = -u * (x ^ 2 - 1 / 4) := by
  have hsq : ((x : ℂ) + I / 2) ^ 2 = ((x ^ 2 - 1 / 4 : ℝ) : ℂ) + (x : ℂ) * I := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hsq, mul_add, Complex.add_re, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp [Complex.mul_re]

private lemma integrable_finset_sum_helper {ι E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} (s : Finset ι) {f : ι → ℝ → E}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun x : ℝ => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h1 : Integrable (f a) μ := hf a (Finset.mem_insert_self a s)
    have h2 : Integrable (fun x => ∑ i ∈ s, f i x) μ :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    refine (h1.add h2).congr (ae_of_all _ fun x => ?_)
    change f a x + ∑ i ∈ s, f i x = ∑ i ∈ insert a s, f i x
    exact (Finset.sum_insert (f := fun i => f i x) ha).symm

private lemma integral_finset_sum_helper {ι : Type*}
    {μ : Measure ℝ} (s : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ x : ℝ, (∑ i ∈ s, f i x) ∂μ = ∑ i ∈ s, ∫ x : ℝ, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h1 : Integrable (f a) μ := hf a (Finset.mem_insert_self a s)
    have h2 : Integrable (fun x => ∑ i ∈ s, f i x) μ :=
      integrable_finset_sum_helper s fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hrew : (fun x : ℝ => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; exact Finset.sum_insert ha
    rw [hrew, integral_add h1 h2, ih fun i hi => hf i (Finset.mem_insert_of_mem hi), Finset.sum_insert ha]

private lemma summable_nat_mul_geometric_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
  rcases eq_or_lt_of_le hr0 with rfl | hr_pos
  · have hz : (fun n : ℕ => (n : ℝ) * (0 : ℝ) ^ n) = fun _ => (0 : ℝ) := by
      funext n; cases n <;> simp
    rw [hz]; exact summable_zero
  · let a : ℝ := (1 - r) / (2 * r)
    have ha_pos : 0 < a := div_pos (by linarith) (by positivity)
    have hq_eq : r * (1 + a) = (1 + r) / 2 := by dsimp only [a]; field_simp [hr_pos.ne']; ring
    have hq0 : 0 ≤ (1 + r) / 2 := by linarith
    have hq1 : (1 + r) / 2 < 1 := by linarith
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left (1 / a))
    have hbern : 1 + (n : ℝ) * a ≤ (1 + a) ^ n := one_add_mul_le_pow (by linarith) n
    have hna : (n : ℝ) ≤ (1 / a) * (1 + a) ^ n := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ ha_pos]; linarith
    calc (n : ℝ) * r ^ n ≤ ((1 / a) * (1 + a) ^ n) * r ^ n :=
          mul_le_mul_of_nonneg_right hna (pow_nonneg hr0 n)
      _ = (1 / a) * (r * (1 + a)) ^ n := by rw [mul_pow]; ring
      _ = (1 / a) * ((1 + r) / 2) ^ n := by rw [hq_eq]

private lemma integrable_shifted_gaussian_mul_lin {B u : ℝ} (hu : 0 < u) :
    Integrable (fun x : ℝ => B * (1 + |x|) * Real.exp (-(u : ℝ) * (x ^ 2 - 1 / 4))) volume := by
  have heq : (fun x : ℝ => B * (1 + |x|) * Real.exp (-u * (x ^ 2 - 1 / 4))) =
      fun x : ℝ => (B * Real.exp (u / 4)) * (Real.exp (-u * x ^ 2) + |x| * Real.exp (-u * x ^ 2)) := by
    funext x
    rw [show -u * (x ^ 2 - 1 / 4) = u / 4 + (-u * x ^ 2) by ring, Real.exp_add]
    ring
  rw [heq]
  have h0 : Integrable (fun x : ℝ => Real.exp (-u * x ^ 2)) volume := integrable_exp_neg_mul_sq hu
  have h1 : Integrable (fun x : ℝ => |x| * Real.exp (-u * x ^ 2)) volume := by
    simpa using integrable_pow_mul_exp_neg_sq hu 1
  exact (h0.add h1).const_mul _

private lemma gaussianKernelIntegral_split {K : ℂ → ℂ} {B : ℝ}
    (hK_strip : ∀ z : ℂ, |z.re| < Real.pi → AnalyticAt ℂ (fun w => K (w ^ 2)) z)
    (hK_cont : Continuous (fun x : ℝ => K (((x : ℂ) + I / 2) ^ 2)))
    (hK_line : ∀ x : ℝ, ‖K (((x : ℂ) + I / 2) ^ 2)‖ ≤ B * (1 + |x|))
    {u : ℝ} (hu : 0 < u) :
    gaussianKernelIntegral K u =
      (invSqrtPi u * ∫ x in Set.Ioc (-Real.pi / 2) (Real.pi / 2),
        Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * K ((x : ℂ) ^ 2)) +
      ((invSqrtPi u * ∫ x in (Set.Ioc (-Real.pi / 2) (Real.pi / 2))ᶜ,
        Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) * K (((x : ℂ) + I / 2) ^ 2)) +
      I * (invSqrtPi u * ∫ y in Set.Ioc (0 : ℝ) (1 / 2),
        Complex.exp (-(u : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2) *
          K ((((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2)) -
      I * (invSqrtPi u * ∫ y in Set.Ioc (0 : ℝ) (1 / 2),
        Complex.exp (-(u : ℂ) * (((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2) *
          K ((((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2))) := by
  let s_mid : Set ℝ := Set.Ioc (-Real.pi / 2) (Real.pi / 2)
  have hint_full : Integrable
      (fun x : ℝ => Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) * K (((x : ℂ) + I / 2) ^ 2)) volume := by
    have hcont : Continuous
        (fun x : ℝ => Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) * K (((x : ℂ) + I / 2) ^ 2)) :=
      (Complex.continuous_exp.comp (continuous_const.mul ((Complex.continuous_ofReal.add continuous_const).pow 2))).mul
        hK_cont
    refine (integrable_shifted_gaussian_mul_lin (B := B) hu).mono' hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [norm_mul, Complex.norm_exp, re_neg_mul_line_sq u x]
    calc Real.exp (-u * (x ^ 2 - 1 / 4)) * ‖K (((x : ℂ) + I / 2) ^ 2)‖
        ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) * (B * (1 + |x|)) :=
          mul_le_mul_of_nonneg_left (hK_line x) (Real.exp_pos _).le
      _ = B * (1 + |x|) * Real.exp (-u * (x ^ 2 - 1 / 4)) := by ring
  have hsplit := (MeasureTheory.integral_add_compl (s := s_mid) measurableSet_Ioc hint_full).symm
  -- Cauchy rectangle on [-π/2, π/2] × [0, 1/2]
  let F : ℂ → ℂ := fun z => Complex.exp (-(u : ℂ) * z ^ 2) * K (z ^ 2)
  let z₁ : ℂ := ((-Real.pi / 2 : ℝ) : ℂ)
  let w₁ : ℂ := ((Real.pi / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * I
  have hz₁_re : z₁.re = -Real.pi / 2 := by simp [z₁]
  have hz₁_im : z₁.im = 0 := by simp [z₁]
  have hw₁_re : w₁.re = Real.pi / 2 := by simp [w₁]
  have hw₁_im : w₁.im = 1 / 2 := by simp [w₁]
  have hF_diff : DifferentiableOn ℂ F (Set.uIcc z₁.re w₁.re ×ℂ Set.uIcc z₁.im w₁.im) := by
    intro z hz
    have hz_re : z.re ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
      have h1 : z.re ∈ Set.uIcc z₁.re w₁.re := hz.1
      rwa [hz₁_re, hw₁_re, Set.uIcc_of_le (by linarith [Real.pi_pos])] at h1
    have habs : |z.re| < Real.pi := by
      rw [abs_lt]; constructor <;> linarith [hz_re.1, hz_re.2, Real.pi_pos]
    have h1 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(u : ℂ) * w ^ 2)) z :=
      (Complex.differentiable_exp _).comp z ((differentiableAt_id.pow 2).const_mul _)
    exact (h1.mul (hK_strip z habs).differentiableAt).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z₁ w₁ hF_diff
  rw [hz₁_re, hz₁_im, hw₁_re, hw₁_im,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi / 2 ≤ Real.pi / 2),
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi / 2 ≤ Real.pi / 2),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hrect
  have hbot : (∫ x in s_mid, F ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) =
      ∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * K ((x : ℂ) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => by simp [F]
  have htop : (∫ x in s_mid, F ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I)) =
      ∫ x in s_mid, Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) * K (((x : ℂ) + I / 2) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => by
      dsimp only [F]; congr 2 <;> (push_cast; ring)
  rw [hbot, htop, smul_eq_mul, smul_eq_mul] at hrect
  dsimp only [F] at hrect
  unfold gaussianKernelIntegral
  rw [hsplit]
  dsimp only [s_mid] at hrect ⊢
  linear_combination -invSqrtPi u * hrect

private lemma gaussianKernelIntegral_hasAsympExp {K : ℂ → ℂ} {B : ℝ}
    (hK0 : K 0 = 0)
    (hK_strip : ∀ z : ℂ, |z.re| < Real.pi → AnalyticAt ℂ (fun w => K (w ^ 2)) z)
    (hK_ball : ∀ w ∈ Metric.closedBall (0 : ℂ) ((Real.pi / 2) ^ 2), AnalyticAt ℂ K w)
    (hK_cont : Continuous (fun x : ℝ => K (((x : ℂ) + I / 2) ^ 2)))
    (hK_line : ∀ x : ℝ, ‖K (((x : ℂ) + I / 2) ^ 2)‖ ≤ B * (1 + |x|)) :
    ∀ j : ℕ, HasAsympExp (iteratedDeriv j (gaussianKernelIntegral K))
      (d_u^[j] (formalSeries (abelConv (dslope K 0)))) := by
  let ψ : ℂ → ℂ := dslope K 0
  let S : PowerSeries ℂ := formalSeries (abelConv ψ)
  let s_mid : Set ℝ := Set.Ioc (-Real.pi / 2) (Real.pi / 2)
  let I_main : ℝ → ℂ := fun u =>
    invSqrtPi u * ∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * K ((x : ℂ) ^ 2)
  let T1 : ℝ → ℂ := fun u =>
    invSqrtPi u * ∫ x in s_midᶜ, Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) * K (((x : ℂ) + I / 2) ^ 2)
  let T2 : ℝ → ℂ := fun u =>
    invSqrtPi u * ∫ y in Set.Ioc (0 : ℝ) (1 / 2),
      Complex.exp (-(u : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2) *
        K ((((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2)
  let T3 : ℝ → ℂ := fun u =>
    invSqrtPi u * ∫ y in Set.Ioc (0 : ℝ) (1 / 2),
      Complex.exp (-(u : ℂ) * (((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2) *
        K ((((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2)
  let T_exp : ℝ → ℂ := fun u => T1 u + I * T2 u - I * T3 u
  have hpi2 : (2 : ℝ) ≤ (Real.pi / 2) ^ 2 - 1 / 4 := by
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith
  -- Step 1: Exponential decay of T1, T2, T3 and hence T_exp
  have hT1 := exp_decay_parametric_integral (s := s_midᶜ) measurableSet_Ioc.compl
    (by fun_prop : Continuous (fun x : ℝ => ((x : ℂ) + I / 2) ^ 2)).aestronglyMeasurable
    hK_cont.aestronglyMeasurable
    (fun x hx => by
      have habs : Real.pi / 2 ≤ |x| := by
        simp only [s_mid, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with hle | hgt
        · rw [abs_of_nonpos (by linarith [Real.pi_pos])]; linarith
        · rw [abs_of_pos (by linarith [Real.pi_pos])]; linarith
      have hre : (((x : ℂ) + I / 2) ^ 2).re = x ^ 2 - 1 / 4 := by
        have := re_neg_mul_line_sq (-1) x; simpa using this
      rw [hre]
      have hsq : (Real.pi / 2) ^ 2 ≤ x ^ 2 := by nlinarith [habs, sq_abs x, Real.pi_pos]
      linarith)
    (fun k => by
      have hcont_d : Continuous (fun x : ℝ =>
          ‖((x : ℂ) + I / 2) ^ 2‖ ^ k * ‖K (((x : ℂ) + I / 2) ^ 2)‖ *
            Real.exp (-(1 / 2 : ℝ) * (((x : ℂ) + I / 2) ^ 2).re)) := by
        refine ((((by fun_prop : Continuous (fun x : ℝ => ((x : ℂ) + I / 2) ^ 2)).norm.pow k).mul
          hK_cont.norm).mul ?_)
        exact Real.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_re.comp (by fun_prop : Continuous (fun x : ℝ => ((x : ℂ) + I / 2) ^ 2))))
      have hdom_all : Integrable (fun x : ℝ =>
          (2 : ℝ) ^ (2 * k) * (1 + |x|) ^ (2 * k) * (B * (1 + |x|)) *
            (Real.exp (1 / 8) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) volume := by
        have hlin_pow : ∀ m : ℕ, Integrable (fun x : ℝ => (1 + |x|) ^ m * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) volume := by
          intro m
          have hrew : (fun x : ℝ => (1 + |x|) ^ m * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
              fun x : ℝ => ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * (|x| ^ i * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
            funext x; rw [add_comm, add_pow, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by simp; ring
          rw [hrew]
          exact integrable_finset_sum_helper _ fun i _ =>
            (integrable_pow_mul_exp_neg_sq (by norm_num : (0 : ℝ) < 1 / 2) i).const_mul _
        have hrew : (fun x : ℝ => (2 : ℝ) ^ (2 * k) * (1 + |x|) ^ (2 * k) * (B * (1 + |x|)) *
              (Real.exp (1 / 8) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) =
            fun x : ℝ => ((2 : ℝ) ^ (2 * k) * B * Real.exp (1 / 8)) *
              ((1 + |x|) ^ (2 * k + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
          funext x; rw [pow_succ]; ring
        rw [hrew]
        exact (hlin_pow (2 * k + 1)).const_mul _
      refine (hdom_all.integrableOn).mono' hcont_d.aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      have hre : (((x : ℂ) + I / 2) ^ 2).re = x ^ 2 - 1 / 4 := by
        have := re_neg_mul_line_sq (-1) x; simpa using this
      have hzn : ‖(x : ℂ) + I / 2‖ ≤ 1 + |x| := by
        calc ‖(x : ℂ) + I / 2‖ ≤ ‖(x : ℂ)‖ + ‖I / 2‖ := norm_add_le _ _
          _ = |x| + 1 / 2 := by simp [Complex.norm_real]
          _ ≤ 1 + |x| := by linarith
      have hsqn : ‖((x : ℂ) + I / 2) ^ 2‖ ^ k ≤ (2 : ℝ) ^ (2 * k) * (1 + |x|) ^ (2 * k) := by
        rw [norm_pow, ← pow_mul]
        calc ‖(x : ℂ) + I / 2‖ ^ (2 * k) ≤ (1 + |x|) ^ (2 * k) :=
              pow_le_pow_left₀ (norm_nonneg _) hzn _
          _ ≤ (2 : ℝ) ^ (2 * k) * (1 + |x|) ^ (2 * k) :=
              le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      have hexp : Real.exp (-(1 / 2 : ℝ) * (x ^ 2 - 1 / 4)) =
          Real.exp (1 / 8) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hre, hexp]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hsqn (hK_line x) (norm_nonneg _) (by positivity)) (by positivity))
  have hvert_cont : ∀ (c : ℝ), |c| = Real.pi / 2 →
      ContinuousOn (fun y : ℝ => K (((c : ℂ) + (y : ℂ) * I) ^ 2)) (Set.Icc 0 (1 / 2)) := by
    intro c hc y _
    have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
    have habs : |((c : ℂ) + (y : ℂ) * I).re| < Real.pi := by rw [hre, hc]; linarith [Real.pi_pos]
    have h1 : ContinuousAt (fun w : ℂ => K (w ^ 2)) ((c : ℂ) + (y : ℂ) * I) :=
      (hK_strip _ habs).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * I) y :=
      continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    exact (ContinuousAt.comp (g := fun w : ℂ => K (w ^ 2))
      (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I) h1 h2).continuousWithinAt
  have hT2 := exp_decay_parametric_integral (s := Set.Ioc (0 : ℝ) (1 / 2)) measurableSet_Ioc
    (by fun_prop : Continuous (fun y : ℝ => (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2)).aestronglyMeasurable
    ((hvert_cont (Real.pi / 2) (abs_of_pos (by positivity))).mono Set.Ioc_subset_Icc_self |>.aestronglyMeasurable
      measurableSet_Ioc)
    (fun y hy => by
      have hre : ((((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2).re = (Real.pi / 2) ^ 2 - y ^ 2 := by
        simp [sq, Complex.mul_re]
      rw [hre]; nlinarith [hy.1, hy.2, hpi2])
    (fun k => by
      refine ContinuousOn.integrableOn_Icc ?_ |>.mono_set Set.Ioc_subset_Icc_self
      refine (((by fun_prop : Continuous (fun y : ℝ => (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2)).norm.pow k).continuousOn.mul
        (hvert_cont (Real.pi / 2) (abs_of_pos (by positivity))).norm).mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp
        (by fun_prop : Continuous (fun y : ℝ => (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2))))).continuousOn)
  have hT3 := exp_decay_parametric_integral (s := Set.Ioc (0 : ℝ) (1 / 2)) measurableSet_Ioc
    (by fun_prop : Continuous (fun y : ℝ => (((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2)).aestronglyMeasurable
    ((hvert_cont (-Real.pi / 2) (by rw [neg_div, abs_neg, abs_of_pos (by positivity)])).mono
      Set.Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)
    (fun y hy => by
      have hre : ((((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2).re = (Real.pi / 2) ^ 2 - y ^ 2 := by
        simp [sq, Complex.mul_re]; ring
      rw [hre]; nlinarith [hy.1, hy.2, hpi2])
    (fun k => by
      refine ContinuousOn.integrableOn_Icc ?_ |>.mono_set Set.Ioc_subset_Icc_self
      refine (((by fun_prop : Continuous (fun y : ℝ => (((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2)).norm.pow k).continuousOn.mul
        (hvert_cont (-Real.pi / 2) (by rw [neg_div, abs_neg, abs_of_pos (by positivity)])).norm).mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp
        (by fun_prop : Continuous (fun y : ℝ => (((-Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) ^ 2))))).continuousOn)
  have hT_exp_deriv : ∀ (j : ℕ) (u : ℝ), (1 / 2 : ℝ) < u →
      iteratedDeriv j T_exp u =
        iteratedDeriv j T1 u + I * iteratedDeriv j T2 u - I * iteratedDeriv j T3 u := by
    intro j
    induction j with
    | zero => intro u _; rfl
    | succ j ih =>
      intro u hu
      have hloc : iteratedDeriv j T_exp =ᶠ[𝓝 u]
          fun v => iteratedDeriv j T1 v + I * iteratedDeriv j T2 v - I * iteratedDeriv j T3 v := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact ih v hv
      rw [iteratedDeriv_succ, hloc.deriv_eq]
      have hd1 : HasDerivAt (iteratedDeriv j T1) (iteratedDeriv (j + 1) T1 u) u := by
        rw [iteratedDeriv_succ]; exact (hT1.1 j u hu).hasDerivAt
      have hd2 : HasDerivAt (fun v => I * iteratedDeriv j T2 v) (I * iteratedDeriv (j + 1) T2 u) u := by
        rw [iteratedDeriv_succ]; exact (hT2.1 j u hu).hasDerivAt.const_mul I
      have hd3 : HasDerivAt (fun v => I * iteratedDeriv j T3 v) (I * iteratedDeriv (j + 1) T3 u) u := by
        rw [iteratedDeriv_succ]; exact (hT3.1 j u hu).hasDerivAt.const_mul I
      exact ((hd1.fun_add hd2).fun_sub hd3).deriv
  have hT_exp_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j T_exp) u := by
    intro j
    filter_upwards [eventually_gt_atTop (1 / 2 : ℝ)] with u hu
    have hloc : iteratedDeriv j T_exp =ᶠ[𝓝 u]
        fun v => iteratedDeriv j T1 v + I * iteratedDeriv j T2 v - I * iteratedDeriv j T3 v := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact hT_exp_deriv j v hv
    rw [hloc.differentiableAt_iff]
    exact ((hT1.1 j u hu).fun_add ((hT2.1 j u hu).const_mul I)).fun_sub ((hT3.1 j u hu).const_mul I)
  have hT_exp_bd : ∀ j : ℕ, ∃ δ > 0, ∃ A : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j T_exp u‖ ≤ C * u ^ A * Real.exp (-δ * u) := by
    intro j
    obtain ⟨C1, hC1⟩ := hT1.2 j
    obtain ⟨C2, hC2⟩ := hT2.2 j
    obtain ⟨C3, hC3⟩ := hT3.2 j
    refine ⟨2, by norm_num, 0, C1 + C2 + C3, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    rw [hT_exp_deriv j u (by linarith), pow_zero, mul_one]
    calc ‖iteratedDeriv j T1 u + I * iteratedDeriv j T2 u - I * iteratedDeriv j T3 u‖
        ≤ ‖iteratedDeriv j T1 u + I * iteratedDeriv j T2 u‖ + ‖I * iteratedDeriv j T3 u‖ := norm_sub_le _ _
      _ ≤ ‖iteratedDeriv j T1 u‖ + ‖I * iteratedDeriv j T2 u‖ + ‖I * iteratedDeriv j T3 u‖ := by
          linarith [norm_add_le (iteratedDeriv j T1 u) (I * iteratedDeriv j T2 u)]
      _ = ‖iteratedDeriv j T1 u‖ + ‖iteratedDeriv j T2 u‖ + ‖iteratedDeriv j T3 u‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
      _ ≤ C1 * Real.exp (-2 * u) + C2 * Real.exp (-2 * u) + C3 * Real.exp (-2 * u) := by
          linarith [hC1 u hu, hC2 u hu, hC3 u hu]
      _ = (C1 + C2 + C3) * Real.exp (-2 * u) := by ring
  -- Step 2: Smoothness and HasAsympExp of I_main
  have hK_mid_cont : ContinuousOn (fun x : ℝ => K ((x : ℂ) ^ 2)) (Set.Icc (-Real.pi / 2) (Real.pi / 2)) := by
    intro x hx
    have habs : |(x : ℂ).re| < Real.pi := by
      rw [Complex.ofReal_re, abs_lt]; constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
    exact (ContinuousAt.comp (g := fun w : ℂ => K (w ^ 2)) (f := Complex.ofReal)
      (hK_strip (x : ℂ) habs).continuousAt Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hI_par := iteratedDeriv_parametric_exp_integral (s := s_mid) measurableSet_Ioc (u₀ := 0)
    (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ 2)).aestronglyMeasurable
    ((hK_mid_cont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (fun x _ => by rw [← Complex.ofReal_pow, Complex.ofReal_re]; exact sq_nonneg x)
    (fun k => by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using
        (((by fun_prop : Continuous (fun x : ℝ => ‖(x : ℂ) ^ 2‖ ^ k)).continuousOn).fun_mul hK_mid_cont.norm))
  have hI_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j I_main) u := by
    intro j
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hloc : iteratedDeriv j I_main =ᶠ[𝓝 u]
        fun v => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i invSqrtPi v *
          iteratedDeriv (j - i) (fun t : ℝ => ∫ x in s_mid, Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) * K ((x : ℂ) ^ 2)) v := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact iteratedDeriv_mul_Ioi j (fun k _ t ht => differentiableAt_iteratedDeriv_invSqrtPi k ht)
        (fun k _ t ht => (hI_par k).2 t ht) v hv
    rw [hloc.differentiableAt_iff]
    refine DifferentiableAt.fun_sum fun i _ => ?_
    exact (differentiableAt_const _ |>.mul (differentiableAt_iteratedDeriv_invSqrtPi i hu)).mul
      ((hI_par (j - i)).2 u hu)
  have hI_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j I_main) (d_u^[j] S) := by
    intro j M
    have hψ_ball : ∀ w ∈ Metric.closedBall (0 : ℂ) ((Real.pi / 2) ^ 2), AnalyticAt ℂ ψ w :=
      fun w hw => (hK_ball w hw).dslope 0
    have hR0 : 0 ≤ (Real.pi / 2) ^ 2 := by positivity
    -- Expand ψ to order M via iterated dslope
    obtain ⟨rem, hrem_an, hrem_eq⟩ := dslope_taylor_remainder hR0 M hψ_ball
    have hK_eq : ∀ x : ℝ, K ((x : ℂ) ^ 2) =
        (∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) * (x : ℂ) ^ (2 * k + 2)) +
          (x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2) := by
      intro x
      have hsl : K ((x : ℂ) ^ 2) = (x : ℂ) ^ 2 * ψ ((x : ℂ) ^ 2) := by
        have h := sub_smul_dslope K 0 ((x : ℂ) ^ 2)
        simp only [sub_zero, smul_eq_mul, hK0] at h
        exact h.symm
      rw [hsl, hrem_eq ((x : ℂ) ^ 2), mul_add, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← pow_mul, show 2 * k + 2 = 2 + 2 * k by ring, pow_add]; ring
      · rw [← pow_mul, show 2 * M + 2 = 2 + 2 * M by ring, pow_add]; ring
    -- Split I_main(u) = truncEval S (M + 2) u - TailPoly(u) + RemInt(u) on u > 0
    let TailPoly : ℝ → ℂ := fun u =>
      ∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
        (invSqrtPi u * ∫ x in s_midᶜ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))
    let RemInt : ℝ → ℂ := fun u =>
      invSqrtPi u * ∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) *
        ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))
    have hrem_mid_cont : ContinuousOn (fun x : ℝ => rem ((x : ℂ) ^ 2)) (Set.Icc (-Real.pi / 2) (Real.pi / 2)) := by
      intro x hx
      have hmem : ((x : ℂ) ^ 2) ∈ Metric.closedBall (0 : ℂ) ((Real.pi / 2) ^ 2) := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        have habs : |x| ≤ Real.pi / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
        nlinarith [abs_nonneg x]
      exact (ContinuousAt.comp (g := rem) (f := fun t : ℝ => (t : ℂ) ^ 2)
        (hrem_an _ hmem).continuousAt (Complex.continuous_ofReal.continuousAt.pow 2)).continuousWithinAt
    have hI_split : ∀ u : ℝ, 0 < u →
        I_main u = truncEval S (M + 2) u - TailPoly u + RemInt u := by
      intro u hu
      have hint_term : ∀ k ∈ Finset.range M,
          IntegrableOn (fun x : ℝ =>
            (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              (Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))) s_mid volume := by
        intro k _
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
        exact continuousOn_const.mul ((Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.pow 2))).mul
          (Complex.continuous_ofReal.pow _)).continuousOn
      have hint_rem : IntegrableOn (fun x : ℝ =>
          Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))) s_mid volume := by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
        exact ((Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.pow 2))).continuousOn.mul
          ((Complex.continuous_ofReal.pow _).continuousOn.mul hrem_mid_cont))
      have hint_main :
          (∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * K ((x : ℂ) ^ 2)) =
            (∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              ∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) +
            ∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2)) := by
        have hrew : ∀ x ∈ s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * K ((x : ℂ) ^ 2) =
            (∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              (Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))) +
            Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2)) := by
          intro x _
          rw [hK_eq x, mul_add, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun k _ => by ring
        rw [setIntegral_congr_fun measurableSet_Ioc hrew,
          integral_add (integrable_finset_sum_helper _ hint_term) hint_rem,
          integral_finset_sum_helper _ hint_term]
        congr 1
        refine Finset.sum_congr rfl fun k _ => integral_const_mul _ _
      have hsplit_k : ∀ k : ℕ,
          (∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) =
            (∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) -
            (∫ x in s_midᶜ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) := by
        intro k
        have hint_full_k : Integrable
            (fun x : ℝ => Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) volume := by
          refine (integrable_pow_mul_exp_neg_sq hu (2 * k + 2)).mono'
            (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))).aestronglyMeasurable
            (ae_of_all _ fun x => ?_)
          rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            (show (-(u : ℂ) * (x : ℂ) ^ 2).re = -u * x ^ 2 by
              rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re])]
          rw [mul_comm]
        have h := MeasureTheory.integral_add_compl (s := s_mid) measurableSet_Ioc hint_full_k
        linear_combination h
      have hS_eq : truncEval S (M + 2) u =
          ∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
            (invSqrtPi u * ∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) := by
        have hS_form : S = PowerSeries.X ^ 2 * eulerSeriesOf ψ :=
          formalSeries_abelConv_eq (hψ_ball 0 (Metric.mem_closedBall_self hR0))
        unfold truncEval
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        have hc0 : PowerSeries.coeff 0 S = 0 := by
          rw [hS_form, sq, mul_assoc, PowerSeries.coeff_zero_X_mul]
        have hc1 : PowerSeries.coeff 1 S = 0 := by
          rw [hS_form, sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
        rw [hc0, hc1, zero_mul, zero_mul, add_zero, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hck : PowerSeries.coeff (k + 2) S =
            (((2 * k + 1).factorial : ℂ) / (2 ^ (2 * k + 1) * ((k.factorial : ℂ) ^ 2))) *
              iteratedDeriv k ψ 0 := by
          rw [hS_form, sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
          simp [eulerSeriesOf]
        have hmom := invSqrtPi_mul_real_gaussian_even_moment (k + 1) hu
        rw [show 2 * (k + 1) = 2 * k + 2 by ring] at hmom
        rw [hmom, hck]
        have hfac2 : ((2 * k + 2).factorial : ℂ) = (2 * (k : ℂ) + 2) * ((2 * k + 1).factorial : ℂ) := by
          exact_mod_cast Nat.factorial_succ (2 * k + 1)
        have hfack : ((k + 1).factorial : ℂ) = ((k : ℂ) + 1) * (k.factorial : ℂ) := by
          exact_mod_cast Nat.factorial_succ k
        have hkf_ne : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
        have hk1_ne : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have h2_ne : (2 : ℂ) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
        have h4_eq : (4 : ℂ) ^ (k + 1) = 2 * (2 : ℂ) ^ (2 * k + 1) := by
          rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
          congr 1
        rw [hfac2, hfack, h4_eq]
        field_simp [hkf_ne, hk1_ne, h2_ne]
      dsimp only [I_main, TailPoly, RemInt]
      rw [hint_main, mul_add, Finset.mul_sum, hS_eq]
      have hdiff_sum :
          (∑ k ∈ Finset.range M, invSqrtPi u * ((iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              ∫ x in s_mid, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))) =
          (∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              (invSqrtPi u * ∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))) -
          (∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              (invSqrtPi u * ∫ x in s_midᶜ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsplit_k k]; ring
      rw [hdiff_sum]
    -- Exponential decay of each term in TailPoly
    have hTail_k : ∀ k : ℕ,
        (∀ (m : ℕ) (u : ℝ), (1 / 2 : ℝ) < u →
          DifferentiableAt ℝ (iteratedDeriv m (fun v : ℝ =>
            invSqrtPi v * ∫ x in s_midᶜ, Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2))) u) ∧
        (∀ m : ℕ, ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u →
          ‖iteratedDeriv m (fun v : ℝ =>
            invSqrtPi v * ∫ x in s_midᶜ, Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) u‖ ≤
            C * Real.exp (-2 * u)) := fun k =>
      exp_decay_parametric_integral (s := s_midᶜ) measurableSet_Ioc.compl
        (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ 2)).aestronglyMeasurable
        (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ (2 * k + 2))).aestronglyMeasurable
        (fun x hx => by
          have habs : Real.pi / 2 ≤ |x| := by
            simp only [s_mid, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
            rcases hx with hle | hgt
            · rw [abs_of_nonpos (by linarith [Real.pi_pos])]; linarith
            · rw [abs_of_pos (by linarith [Real.pi_pos])]; linarith
          rw [← Complex.ofReal_pow, Complex.ofReal_re]
          have hsq : (Real.pi / 2) ^ 2 ≤ x ^ 2 := by nlinarith [habs, sq_abs x, Real.pi_pos]
          linarith)
        (fun r => by
          refine (integrable_pow_mul_exp_neg_sq (by norm_num : (0 : ℝ) < 1 / 2) (2 * r + (2 * k + 2))).integrableOn.congr_fun
            (fun x _ => ?_) measurableSet_Ioc.compl
          rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, ← pow_add,
            (show ((x : ℂ) ^ 2).re = x ^ 2 by rw [← Complex.ofReal_pow, Complex.ofReal_re])])
    have hTail_deriv : ∀ (m : ℕ) (u : ℝ), (1 / 2 : ℝ) < u →
        iteratedDeriv m TailPoly u =
          ∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
            iteratedDeriv m (fun v : ℝ =>
              invSqrtPi v * ∫ x in s_midᶜ, Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) u := by
      intro m
      induction m with
      | zero => intro u _; simp [TailPoly]
      | succ m ihm =>
        intro u hu
        have hloc : iteratedDeriv m TailPoly =ᶠ[𝓝 u]
            fun v => ∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              iteratedDeriv m (fun t : ℝ =>
                invSqrtPi t * ∫ x in s_midᶜ, Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) v := by
          filter_upwards [Ioi_mem_nhds hu] with v hv
          exact ihm v hv
        rw [iteratedDeriv_succ, hloc.deriv_eq]
        have hsum_d := HasDerivAt.fun_sum (u := Finset.range M) fun k _ => by
          have hd := ((hTail_k k).1 m u hu).hasDerivAt.const_mul (iteratedDeriv k ψ 0 / (k.factorial : ℂ))
          rw [← iteratedDeriv_succ] at hd
          exact hd
        exact hsum_d.deriv
    have hTail_diff : ∀ (m : ℕ) (u : ℝ), (1 / 2 : ℝ) < u → DifferentiableAt ℝ (iteratedDeriv m TailPoly) u := by
      intro m u hu
      have hloc : iteratedDeriv m TailPoly =ᶠ[𝓝 u]
          fun v => ∑ k ∈ Finset.range M, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
            iteratedDeriv m (fun t : ℝ =>
              invSqrtPi t * ∫ x in s_midᶜ, Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * k + 2)) v := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact hTail_deriv m v hv
      rw [hloc.differentiableAt_iff]
      exact DifferentiableAt.fun_sum fun k _ => ((hTail_k k).1 m u hu).const_mul _
    -- Bound on iteratedDeriv j RemInt u
    obtain ⟨B_rem, hB_rem⟩ := isCompact_Icc.exists_bound_of_continuousOn hrem_mid_cont
    have hRem_par := iteratedDeriv_parametric_exp_integral (s := s_mid) measurableSet_Ioc (u₀ := 0)
      (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ 2)).aestronglyMeasurable
      ((((by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ (2 * M + 2))).continuousOn.fun_mul hrem_mid_cont).mono
        Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
      (fun x _ => by rw [← Complex.ofReal_pow, Complex.ofReal_re]; exact sq_nonneg x)
      (fun k => by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
        simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using
          (((by fun_prop : Continuous (fun x : ℝ => ‖(x : ℂ) ^ 2‖ ^ k)).continuousOn).fun_mul
            ((by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ (2 * M + 2))).continuousOn.fun_mul hrem_mid_cont).norm))
    have hRem_deriv_eq : ∀ (m : ℕ) (u : ℝ), 0 < u →
        iteratedDeriv m RemInt u =
          ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) * iteratedDeriv i invSqrtPi u *
            iteratedDeriv (m - i) (fun v : ℝ => ∫ x in s_mid,
              Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))) u :=
      fun m => iteratedDeriv_mul_Ioi m (fun k _ u hu => differentiableAt_iteratedDeriv_invSqrtPi k hu)
        (fun k _ u hu => (hRem_par k).2 u hu)
    have hRem_diff : ∀ (m : ℕ) (u : ℝ), 0 < u → DifferentiableAt ℝ (iteratedDeriv m RemInt) u := by
      intro m u hu
      have hloc : iteratedDeriv m RemInt =ᶠ[𝓝 u]
          fun v => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) * iteratedDeriv i invSqrtPi v *
            iteratedDeriv (m - i) (fun t : ℝ => ∫ x in s_mid,
              Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))) v := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact hRem_deriv_eq m v hv
      rw [hloc.differentiableAt_iff]
      refine DifferentiableAt.fun_sum fun i _ => ?_
      exact (differentiableAt_const _ |>.mul (differentiableAt_iteratedDeriv_invSqrtPi i hu)).mul
        ((hRem_par (m - i)).2 u hu)
    have hTrunc_diff : ∀ (m : ℕ) (u : ℝ), 0 < u → DifferentiableAt ℝ (iteratedDeriv m (truncEval S (M + 2))) u := by
      intro m u hu
      have hloc : iteratedDeriv m (truncEval S (M + 2)) =ᶠ[𝓝 u] truncEval (d_u^[m] S) (M + 2 + m) := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact iteratedDeriv_truncEval S (M + 2) m v hv
      rw [hloc.differentiableAt_iff]
      exact (hasDerivAt_truncEval _ _ hu).differentiableAt
    have hI_deriv_split : ∀ (m : ℕ) (u : ℝ), (1 / 2 : ℝ) < u →
        iteratedDeriv m I_main u =
          iteratedDeriv m (truncEval S (M + 2)) u - iteratedDeriv m TailPoly u + iteratedDeriv m RemInt u := by
      intro m
      induction m with
      | zero => intro u hu; simpa using hI_split u (by linarith)
      | succ m ihm =>
        intro u hu
        have hloc : iteratedDeriv m I_main =ᶠ[𝓝 u]
            fun v => iteratedDeriv m (truncEval S (M + 2)) v - iteratedDeriv m TailPoly v + iteratedDeriv m RemInt v := by
          filter_upwards [Ioi_mem_nhds hu] with v hv
          exact ihm v hv
        rw [iteratedDeriv_succ, hloc.deriv_eq]
        have hd1 : HasDerivAt (iteratedDeriv m (truncEval S (M + 2)))
            (iteratedDeriv (m + 1) (truncEval S (M + 2)) u) u := by
          rw [iteratedDeriv_succ]; exact (hTrunc_diff m u (by linarith)).hasDerivAt
        have hd2 : HasDerivAt (iteratedDeriv m TailPoly) (iteratedDeriv (m + 1) TailPoly u) u := by
          rw [iteratedDeriv_succ]; exact (hTail_diff m u hu).hasDerivAt
        have hd3 : HasDerivAt (iteratedDeriv m RemInt) (iteratedDeriv (m + 1) RemInt u) u := by
          rw [iteratedDeriv_succ]; exact (hRem_diff m u (by linarith)).hasDerivAt
        exact ((hd1.sub hd2).add hd3).deriv
    -- Combine the 3 bounds at order M!
    -- Bound 1: truncation error of truncEval (d_u^[j] S) (M + 2 + j) - truncEval (d_u^[j] S) M
    let C_tr : ℝ := ∑ k ∈ Finset.Ico M (M + 2 + j), ‖PowerSeries.coeff k (d_u^[j] S)‖
    -- Bound 2: exponential tail TailPoly -> O(exp(-2 u)) ≤ C_tail / u^M
    have hTail_exp : ∃ C_t : ℝ, ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv j TailPoly u‖ ≤ C_t * Real.exp (-2 * u) := by
      choose Ck hCk using fun k : ℕ => (hTail_k k).2 j
      refine ⟨∑ k ∈ Finset.range M, ‖iteratedDeriv k ψ 0 / (k.factorial : ℂ)‖ * max (Ck k) 0, fun u hu => ?_⟩
      rw [hTail_deriv j u (by linarith)]
      calc ‖∑ k ∈ Finset.range M, _‖
          ≤ ∑ k ∈ Finset.range M, ‖(iteratedDeriv k ψ 0 / (k.factorial : ℂ)) * _‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range M, (‖iteratedDeriv k ψ 0 / (k.factorial : ℂ)‖ * max (Ck k) 0) * Real.exp (-2 * u) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [norm_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left ((hCk k u hu).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)) (norm_nonneg _)
        _ = _ := by rw [Finset.sum_mul]
    obtain ⟨C_t, hC_t⟩ := hTail_exp
    have hTail_poly : ∃ C_tp : ℝ, ∀ᶠ u : ℝ in atTop, ‖iteratedDeriv j TailPoly u‖ ≤ C_tp / u ^ M := by
      have h0 : HasAsympExp (iteratedDeriv j TailPoly) 0 :=
        HasAsympExp.zero_of_exp_decay (δ := 2) (by norm_num) (A := 0) (C := C_t)
          (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu; simpa using hC_t u hu)
      obtain ⟨C_tp, hC_tp⟩ := h0 M
      exact ⟨C_tp, by filter_upwards [hC_tp] with u hu; simpa using hu⟩
    obtain ⟨C_tp, hC_tp⟩ := hTail_poly
    -- Bound 3: RemInt j-th derivative ≤ C_rem / u^M for u ≥ 1
    let C_rem : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |invSqrtPiCoeff i| * max B_rem 0 *
      (((2 * (M + 1 + (j - i))).factorial : ℝ) / (4 ^ (M + 1 + (j - i)) * ((M + 1 + (j - i)).factorial : ℝ)))
    have hRem_bd : ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv j RemInt u‖ ≤ C_rem / u ^ M := by
      intro u hu
      have hu_pos : 0 < u := by linarith
      rw [hRem_deriv_eq j u hu_pos]
      calc ‖∑ i ∈ Finset.range (j + 1), _‖
          ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i invSqrtPi u *
              iteratedDeriv (j - i) (fun v : ℝ => ∫ x in s_mid,
                Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))) u‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (j + 1),
              ((j.choose i : ℝ) * |invSqrtPiCoeff i| * max B_rem 0 *
                (((2 * (M + 1 + (j - i))).factorial : ℝ) /
                  (4 ^ (M + 1 + (j - i)) * ((M + 1 + (j - i)).factorial : ℝ)))) / u ^ M := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hile : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [(hRem_par (j - i)).1 u hu_pos, norm_mul, norm_mul, Complex.norm_natCast,
              iteratedDeriv_invSqrtPi i u hu_pos, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
            let p : ℕ := M + 1 + (j - i)
            have hint_norm :
                ‖∫ x in s_mid, (-(x : ℂ) ^ 2) ^ (j - i) * Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) *
                    ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))‖ ≤
                  max B_rem 0 * ∫ x : ℝ, Real.exp (-u * x ^ 2) * x ^ (2 * p) := by
              have hle_real : ∀ x ∈ s_mid,
                  ‖(-(x : ℂ) ^ 2) ^ (j - i) * Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) *
                      ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))‖ ≤
                    max B_rem 0 * (Real.exp (-u * x ^ 2) * x ^ (2 * p)) := by
                intro x hx
                rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_pow, norm_pow,
                  Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
                  (show (-(u : ℂ) * (x : ℂ) ^ 2).re = -u * x ^ 2 by
                    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re])]
                have hrb : ‖rem ((x : ℂ) ^ 2)‖ ≤ max B_rem 0 :=
                  (hB_rem x (Set.Ioc_subset_Icc_self hx)).trans (le_max_left _ _)
                have hxpow : (|x| ^ 2) ^ (j - i) * |x| ^ (2 * M + 2) = x ^ (2 * p) := by
                  rw [← pow_mul, ← pow_add, show 2 * (j - i) + (2 * M + 2) = 2 * p by dsimp only [p]; omega,
                    pow_mul, sq_abs, ← pow_mul]
                calc (|x| ^ 2) ^ (j - i) * Real.exp (-u * x ^ 2) * (|x| ^ (2 * M + 2) * ‖rem ((x : ℂ) ^ 2)‖)
                    = ‖rem ((x : ℂ) ^ 2)‖ * (Real.exp (-u * x ^ 2) * ((|x| ^ 2) ^ (j - i) * |x| ^ (2 * M + 2))) := by ring
                  _ = ‖rem ((x : ℂ) ^ 2)‖ * (Real.exp (-u * x ^ 2) * x ^ (2 * p)) := by rw [hxpow]
                  _ ≤ max B_rem 0 * (Real.exp (-u * x ^ 2) * x ^ (2 * p)) :=
                      mul_le_mul_of_nonneg_right hrb (by
                        have : 0 ≤ x ^ (2 * p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p
                        positivity)
              have hint_rhs : Integrable (fun x : ℝ => Real.exp (-u * x ^ 2) * x ^ (2 * p)) volume := by
                refine (integrable_pow_mul_exp_neg_sq hu_pos (2 * p)).congr (ae_of_all _ fun x => ?_)
                dsimp only; rw [mul_comm, pow_mul, sq_abs, ← pow_mul]
              have hint_lhs : IntegrableOn (fun x : ℝ =>
                  ‖(-(x : ℂ) ^ 2) ^ (j - i) * Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) *
                    ((x : ℂ) ^ (2 * M + 2) * rem ((x : ℂ) ^ 2))‖) s_mid volume := by
                refine (hint_rhs.const_mul (max B_rem 0)).integrableOn.mono' ?_ ?_
                · exact ((((by fun_prop : Continuous (fun x : ℝ => (-(x : ℂ) ^ 2) ^ (j - i))).mul
                    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2)))).continuousOn.mul
                    ((Complex.continuous_ofReal.pow _).continuousOn.mul hrem_mid_cont)).mono
                    Set.Ioc_subset_Icc_self).norm.aestronglyMeasurable measurableSet_Ioc
                · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
                  rw [Real.norm_of_nonneg (norm_nonneg _)]
                  exact hle_real x hx
              calc ‖∫ x in s_mid, _‖
                  ≤ ∫ x in s_mid, ‖_‖ := norm_integral_le_integral_norm _
                _ ≤ ∫ x in s_mid, max B_rem 0 * (Real.exp (-u * x ^ 2) * x ^ (2 * p)) :=
                    setIntegral_mono_on hint_lhs ((hint_rhs.const_mul _).integrableOn) measurableSet_Ioc hle_real
                _ = max B_rem 0 * ∫ x in s_mid, Real.exp (-u * x ^ 2) * x ^ (2 * p) := integral_const_mul _ _
                _ ≤ max B_rem 0 * ∫ x : ℝ, Real.exp (-u * x ^ 2) * x ^ (2 * p) := by
                    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
                    exact setIntegral_le_integral hint_rhs (ae_of_all _ fun x => by
                      have : 0 ≤ x ^ (2 * p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p
                      positivity)
            have hmom_real : ‖invSqrtPi u‖ * (∫ x : ℝ, Real.exp (-u * x ^ 2) * x ^ (2 * p)) =
                (((2 * p).factorial : ℝ) / (4 ^ p * (p.factorial : ℝ))) * (u⁻¹ ^ (p + 1)) := by
              have hC := invSqrtPi_mul_real_gaussian_even_moment p hu_pos
              have hreal_int : (∫ x : ℝ, Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * p)) =
                  ((∫ x : ℝ, Real.exp (-u * x ^ 2) * x ^ (2 * p) : ℝ) : ℂ) := by
                have hrew : (fun x : ℝ => Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ (2 * p)) =
                    fun x : ℝ => Complex.ofRealCLM (Real.exp (-u * x ^ 2) * x ^ (2 * p)) := by
                  funext x; simp [Complex.ofReal_exp]
                have hint_r : Integrable (fun x : ℝ => Real.exp (-u * x ^ 2) * x ^ (2 * p)) volume := by
                  refine (integrable_pow_mul_exp_neg_sq hu_pos (2 * p)).congr (ae_of_all _ fun x => ?_)
                  dsimp only; rw [mul_comm, pow_mul, sq_abs, ← pow_mul]
                rw [hrew, Complex.ofRealCLM.integral_comp_comm hint_r]; rfl
              rw [hreal_int] at hC
              have hnorm := congrArg norm hC
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun x => by
                have : 0 ≤ x ^ (2 * p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p
                positivity)] at hnorm
              rw [hnorm, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
              congr 1
              have hpos_c : 0 ≤ (((2 * p).factorial : ℝ) / (4 ^ p * (p.factorial : ℝ))) := by positivity
              rw [show (((2 * p).factorial : ℂ) / (4 ^ p * (p.factorial : ℂ))) =
                ((((2 * p).factorial : ℝ) / (4 ^ p * (p.factorial : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
                Complex.norm_real, Real.norm_of_nonneg hpos_c]
            have hpow_le : (u⁻¹) ^ i * (u⁻¹) ^ (p + 1) ≤ 1 / u ^ M := by
              rw [← pow_add, one_div, ← inv_pow]
              exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hu) (by dsimp only [p]; omega)
            calc (j.choose i : ℝ) * (|invSqrtPiCoeff i| * ‖invSqrtPi u‖ * (u⁻¹) ^ i) * ‖∫ x in s_mid, _‖
                ≤ (j.choose i : ℝ) * (|invSqrtPiCoeff i| * ‖invSqrtPi u‖ * (u⁻¹) ^ i) *
                    (max B_rem 0 * ∫ x : ℝ, Real.exp (-u * x ^ 2) * x ^ (2 * p)) :=
                  mul_le_mul_of_nonneg_left hint_norm (by positivity)
              _ = (j.choose i : ℝ) * |invSqrtPiCoeff i| * max B_rem 0 *
                    (‖invSqrtPi u‖ * ∫ x : ℝ, Real.exp (-u * x ^ 2) * x ^ (2 * p)) * (u⁻¹) ^ i := by ring
              _ = (j.choose i : ℝ) * |invSqrtPiCoeff i| * max B_rem 0 *
                    (((2 * p).factorial : ℝ) / (4 ^ p * (p.factorial : ℝ))) * ((u⁻¹) ^ i * (u⁻¹) ^ (p + 1)) := by
                  rw [hmom_real]; ring
              _ ≤ (j.choose i : ℝ) * |invSqrtPiCoeff i| * max B_rem 0 *
                    (((2 * p).factorial : ℝ) / (4 ^ p * (p.factorial : ℝ))) * (1 / u ^ M) :=
                  mul_le_mul_of_nonneg_left hpow_le (by positivity)
              _ = _ := by ring
        _ = C_rem / u ^ M := by dsimp only [C_rem]; rw [Finset.sum_div]
    refine ⟨C_tr + C_tp + C_rem, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ), hC_tp] with u hu htail_u
    have hu_pos : 0 < u := by linarith
    rw [hI_deriv_split j u (by linarith), iteratedDeriv_truncEval S (M + 2) j u hu_pos]
    have htr_diff : truncEval (d_u^[j] S) (M + 2 + j) u -
        ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k) =
        ∑ k ∈ Finset.Ico M (M + 2 + j), PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k) := by
      unfold truncEval
      have hdisj : Finset.range M ∪ Finset.Ico M (M + 2 + j) = Finset.range (M + 2 + j) := by
        ext k; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
      rw [← hdisj, Finset.sum_union (Finset.disjoint_left.mpr fun k hk1 hk2 => by
        have := Finset.mem_range.mp hk1; have := (Finset.mem_Ico.mp hk2).1; omega)]
      ring
    have htr_bd : ‖truncEval (d_u^[j] S) (M + 2 + j) u -
        ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k)‖ ≤ C_tr / u ^ M := by
      rw [htr_diff]
      calc ‖∑ k ∈ Finset.Ico M (M + 2 + j), _‖
          ≤ ∑ k ∈ Finset.Ico M (M + 2 + j), ‖PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Ico M (M + 2 + j), ‖PowerSeries.coeff k (d_u^[j] S)‖ / u ^ M := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le, div_eq_mul_inv, ← inv_pow]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hu) (Finset.mem_Ico.mp hk).1)
              (norm_nonneg _)
        _ = C_tr / u ^ M := by dsimp only [C_tr]; rw [Finset.sum_div]
    calc ‖truncEval (d_u^[j] S) (M + 2 + j) u - iteratedDeriv j TailPoly u + iteratedDeriv j RemInt u -
            ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k)‖
        = ‖(truncEval (d_u^[j] S) (M + 2 + j) u -
            ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k)) +
            (-iteratedDeriv j TailPoly u) + iteratedDeriv j RemInt u‖ := by congr 1; ring
      _ ≤ ‖truncEval (d_u^[j] S) (M + 2 + j) u -
            ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k)‖ +
            ‖iteratedDeriv j TailPoly u‖ + ‖iteratedDeriv j RemInt u‖ := by
          have h1 := norm_add_le
            ((truncEval (d_u^[j] S) (M + 2 + j) u -
              ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k)) +
              (-iteratedDeriv j TailPoly u)) (iteratedDeriv j RemInt u)
          have h2 := norm_add_le
            (truncEval (d_u^[j] S) (M + 2 + j) u -
              ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] S) * ((u : ℂ)⁻¹ ^ k))
            (-iteratedDeriv j TailPoly u)
          rw [norm_neg] at h2
          linarith
      _ ≤ C_tr / u ^ M + C_tp / u ^ M + C_rem / u ^ M := by linarith [hRem_bd u hu]
      _ = (C_tr + C_tp + C_rem) / u ^ M := by ring
  -- Step 3: Combine I_main + T_exp via HasAsympExp.add_exp_companion!
  have hcomb := HasAsympExp.add_exp_companion hI_diff hT_exp_diff hI_asymp hT_exp_bd
  have hG_deriv : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (gaussianKernelIntegral K) u = iteratedDeriv j (fun v => I_main v + T_exp v) u := by
    intro j
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hloc : gaussianKernelIntegral K =ᶠ[𝓝 u] fun v => I_main v + T_exp v := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact gaussianKernelIntegral_split hK_strip hK_cont hK_line hv
    exact hloc.iteratedDeriv_eq j
  intro j M
  obtain ⟨C, hC⟩ := hcomb j M
  refine ⟨C, ?_⟩
  filter_upwards [hC, hG_deriv j] with u hu hdu
  rwa [hdu]

/-! #### D.4d. Exact Horizontal Shifted-Gaussian Representations for `baseHeatInt` and `baseHeatHalf` -/

private lemma shifted_gaussian_fourier (a : ℝ) {u : ℝ} (hu : 0 < u) :
    ∫ x : ℝ, Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) *
        Complex.exp (I * (a : ℂ) * ((x : ℂ) + I / 2)) =
      ((Real.sqrt (Real.pi / u) : ℝ) : ℂ) * Complex.exp (-((a : ℂ) ^ 2 / (4 * (u : ℂ)))) := by
  have hrew : (fun x : ℝ => Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) *
        Complex.exp (I * (a : ℂ) * ((x : ℂ) + I / 2))) =
      fun x : ℝ => Complex.exp ((-(u : ℂ)) * (x : ℂ) ^ 2 + (I * ((a : ℂ) - (u : ℂ))) * (x : ℂ) +
        ((u : ℂ) / 4 - (a : ℂ) / 2)) := by
    funext x
    rw [← Complex.exp_add]
    congr 1; ring_nf; rw [Complex.I_sq]; ring
  rw [hrew, integral_cexp_quadratic (b := -(u : ℂ)) (by simpa using hu)]
  have hsqrt : ((Real.pi : ℂ) / -(-(u : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / u) : ℝ) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_div, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow (div_pos Real.pi_pos hu).le]
    push_cast; rfl
  have hexp : ((u : ℂ) / 4 - (a : ℂ) / 2) - (I * ((a : ℂ) - (u : ℂ))) ^ 2 / (4 * -(u : ℂ)) =
      -((a : ℂ) ^ 2 / (4 * (u : ℂ))) := by
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    rw [mul_pow, Complex.I_sq]
    field_simp [huC]; ring
  rw [hsqrt, hexp]

private lemma sin_line_lower_bound (x : ℝ) :
    Real.sinh (1 / 2) ≤ ‖Complex.sin ((x : ℂ) + I / 2)‖ := by
  have hsin : Complex.sin ((x : ℂ) + I / 2) =
      (Complex.exp (((x : ℂ) + I / 2) * I) - Complex.exp (-(((x : ℂ) + I / 2) * I))) / (2 * I) := by
    rw [Complex.sin]; field_simp [Complex.I_ne_zero]; ring_nf; rw [Complex.I_sq]; ring
  have h1 : ‖Complex.exp (((x : ℂ) + I / 2) * I)‖ = Real.exp (-(1 / 2)) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have h2 : ‖Complex.exp (-(((x : ℂ) + I / 2) * I))‖ = Real.exp (1 / 2) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have htri := norm_sub_norm_le (Complex.exp (-(((x : ℂ) + I / 2) * I))) (Complex.exp (((x : ℂ) + I / 2) * I))
  rw [norm_sub_rev, h1, h2] at htri
  rw [hsin, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, Real.sinh_eq]
  linarith

private lemma sin_line_ne_zero (x : ℝ) : Complex.sin ((x : ℂ) + I / 2) ≠ 0 := by
  intro h0
  have h := sin_line_lower_bound x
  rw [h0, norm_zero] at h
  have hpos : 0 < Real.sinh (1 / 2) := by
    rw [Real.sinh_eq]
    have h1 : 1 < Real.exp (1 / 2) := Real.one_lt_exp_iff.mpr (by norm_num)
    have h2 : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  linarith

private lemma cos_line_upper_bound (x : ℝ) :
    ‖Complex.cos ((x : ℂ) + I / 2)‖ ≤ Real.cosh (1 / 2) := by
  have hcos : Complex.cos ((x : ℂ) + I / 2) =
      (Complex.exp (((x : ℂ) + I / 2) * I) + Complex.exp (-(((x : ℂ) + I / 2) * I))) / 2 := by
    rw [Complex.cos]; ring_nf
  have h1 : ‖Complex.exp (((x : ℂ) + I / 2) * I)‖ = Real.exp (-(1 / 2)) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have h2 : ‖Complex.exp (-(((x : ℂ) + I / 2) * I))‖ = Real.exp (1 / 2) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hcos, norm_div, Complex.norm_ofNat, Real.cosh_eq]
  linarith [norm_add_le (Complex.exp (((x : ℂ) + I / 2) * I)) (Complex.exp (-(((x : ℂ) + I / 2) * I)))]

private lemma tsum_nat_succ_mul_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * q ^ n) ∧
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * q ^ n) = (1 - q)⁻¹ ^ 2 := by
  have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (fun h => by rw [← h] at hq; simp at hq)
  have hsum_geom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_norm_lt_one hq
  have hsum_lin : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * q ^ n) := by
    have hreal : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖q‖ ^ n) := by
      have h0 : Summable (fun n : ℕ => (n : ℝ) * ‖q‖ ^ n) :=
        summable_nat_mul_geometric_of_lt_one (norm_nonneg q) hq
      have h1 : Summable (fun n : ℕ => ‖q‖ ^ n) := summable_geometric_of_lt_one (norm_nonneg q) hq
      exact (h0.add h1).congr fun n => by push_cast; ring
    exact Summable.of_norm (hreal.congr fun n => by rw [norm_mul, Complex.norm_natCast, norm_pow])
  refine ⟨hsum_lin, ?_⟩
  let S : ℂ := ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * q ^ n
  have hS1 : S = 1 + ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * q ^ (n + 1) := by
    have h := hsum_lin.tsum_eq_zero_add
    simpa only [S, Nat.zero_add, Nat.cast_one, pow_zero, mul_one,
      show ∀ n : ℕ, n + 1 + 1 = n + 2 from fun _ => rfl] using h
  have hqS : q * S = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * q ^ (n + 1) := by
    dsimp only [S]; rw [← tsum_mul_left]
    exact tsum_congr fun n => by rw [pow_succ']; ring
  have hshift1 : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℂ) * q ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsum_lin
  have hshift2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * q ^ (n + 1)) :=
    (hsum_lin.mul_left q).congr fun n => by rw [pow_succ']; ring
  have hsub : (1 - q) * S = (1 - q)⁻¹ := by
    have h1 : (1 - q) * S = S - q * S := by ring
    have h2 : S - q * S =
        1 + ((∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * q ^ (n + 1)) -
          (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * q ^ (n + 1))) := by
      rw [hqS, hS1]; ring
    calc (1 - q) * S = 1 + ((∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * q ^ (n + 1)) -
            (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * q ^ (n + 1))) := h1.trans h2
      _ = 1 + ∑' n : ℕ, q ^ (n + 1) := by
          rw [← hshift1.tsum_sub hshift2]
          congr 1; refine tsum_congr fun n => by push_cast; ring
      _ = ∑' n : ℕ, q ^ n := by simpa using hsum_geom.tsum_eq_zero_add.symm
      _ = (1 - q)⁻¹ := tsum_geometric_of_norm_lt_one hq
  calc S = (1 - q)⁻¹ * ((1 - q) * S) := by field_simp [h1q]
    _ = (1 - q)⁻¹ ^ 2 := by rw [hsub, sq]

private lemma tsum_int_trig (x : ℝ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * ((x : ℂ) + I / 2))) =
      -1 / (4 * Complex.sin ((x : ℂ) + I / 2) ^ 2) := by
  let z : ℂ := (x : ℂ) + I / 2
  let q : ℂ := Complex.exp (2 * I * z)
  have hq_norm : ‖q‖ = Real.exp (-1) := by
    dsimp only [q, z]; rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have hq_lt : ‖q‖ < 1 := by rw [hq_norm]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (fun h => by rw [← h] at hq_lt; simp at hq_lt)
  have hsum := (tsum_nat_succ_mul_pow hq_lt).2
  have hLHS : (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z)) =
      q * ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * q ^ n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    dsimp only [q]
    rw [← Complex.exp_nat_mul]
    calc ((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z)
        = ((n + 1 : ℕ) : ℂ) * (Complex.exp (2 * I * z) * Complex.exp ((n : ℂ) * (2 * I * z))) := by
          rw [← Complex.exp_add]; congr 2; push_cast; ring
      _ = Complex.exp (2 * I * z) * (((n + 1 : ℕ) : ℂ) * Complex.exp ((n : ℂ) * (2 * I * z))) := by ring
  rw [hLHS, hsum]
  have hsin_sq : Complex.sin z ^ 2 = -(1 - q) ^ 2 / (4 * q) := by
    let r : ℂ := Complex.exp (I * z)
    have hr_ne : r ≠ 0 := Complex.exp_ne_zero _
    have hq_eq : q = r ^ 2 := by dsimp only [q, r]; rw [sq, ← Complex.exp_add]; congr 1; ring
    have hsin : Complex.sin z = (r - r⁻¹) / (2 * I) := by
      dsimp only [r]; rw [Complex.sin, ← Complex.exp_neg]
      field_simp [Complex.I_ne_zero]; ring_nf; rw [Complex.I_sq]; ring
    rw [hsin, hq_eq, div_pow, mul_pow, Complex.I_sq]
    field_simp [hr_ne]; ring
  have hq_ne : q ≠ 0 := Complex.exp_ne_zero _
  rw [hsin_sq]
  field_simp [h1q, hq_ne]

private lemma tsum_half_trig (x : ℝ) :
    (∑' k : ℕ, ((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * ((x : ℂ) + I / 2))) =
      -Complex.cos ((x : ℂ) + I / 2) / (4 * Complex.sin ((x : ℂ) + I / 2) ^ 2) := by
  let z : ℂ := (x : ℂ) + I / 2
  let r : ℂ := Complex.exp (I * z)
  let q : ℂ := r ^ 2
  have hq_eq : q = Complex.exp (2 * I * z) := by
    dsimp only [q, r]; rw [sq, ← Complex.exp_add]; congr 1; ring
  have hq_norm : ‖q‖ = Real.exp (-1) := by
    rw [hq_eq]; dsimp only [z]; rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have hq_lt : ‖q‖ < 1 := by rw [hq_norm]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (fun h => by rw [← h] at hq_lt; simp at hq_lt)
  have hlin := tsum_nat_succ_mul_pow hq_lt
  have hgeom : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_norm_lt_one hq_lt
  have hLHS : (∑' k : ℕ, ((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z)) =
      r * ((∑' k : ℕ, ((k + 1 : ℕ) : ℂ) * q ^ k) - (1 / 2 : ℂ) * ∑' k : ℕ, q ^ k) := by
    rw [← tsum_mul_left, ← hlin.1.tsum_sub (hgeom.mul_left _), ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hexp : Complex.exp (I * (2 * (k : ℂ) + 1) * z) = r * q ^ k := by
      rw [hq_eq]; dsimp only [r]
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; ring
    rw [hexp]; push_cast; ring
  rw [hLHS, hlin.2, tsum_geometric_of_norm_lt_one hq_lt]
  have hr_ne : r ≠ 0 := Complex.exp_ne_zero _
  have hcos : Complex.cos z = (r + r⁻¹) / 2 := by
    dsimp only [r]; rw [Complex.cos, ← Complex.exp_neg]; congr 1; congr 1
    · congr 1; ring
    · congr 1; ring
  have hsin : Complex.sin z = (r - r⁻¹) / (2 * I) := by
    dsimp only [r]; rw [Complex.sin, ← Complex.exp_neg]
    field_simp [Complex.I_ne_zero]; ring_nf; rw [Complex.I_sq]; ring
  have hsin_sq : Complex.sin z ^ 2 = -(1 - q) ^ 2 / (4 * q) := by
    rw [hsin, div_pow, mul_pow, Complex.I_sq]
    change (r - r⁻¹) ^ 2 / (2 ^ 2 * -1) = -(1 - r ^ 2) ^ 2 / (4 * r ^ 2)
    field_simp [hr_ne]; ring
  have hq_ne : q ≠ 0 := pow_ne_zero 2 hr_ne
  rw [hcos, hsin_sq]
  change r * ((1 - q)⁻¹ ^ 2 - 1 / 2 * (1 - q)⁻¹) = -((r + r⁻¹) / 2) / (4 * (-(1 - q) ^ 2 / (4 * q)))
  have hq_r2 : q = r ^ 2 := rfl
  field_simp [h1q, hq_ne, hr_ne]
  rw [hq_r2]; ring

private lemma ibp_inv_z_sq {u : ℝ} (hu : 0 < u) :
    (∫ x : ℝ, Complex.exp (-(u : ℂ) * ((x : ℂ) + I / 2) ^ 2) / (4 * ((x : ℂ) + I / 2) ^ 2)) =
      -((u : ℂ) / 2) * ((Real.sqrt (Real.pi / u) : ℝ) : ℂ) := by
  let z : ℝ → ℂ := fun x => (x : ℂ) + I / 2
  have hz_ne : ∀ x : ℝ, z x ≠ 0 := fun x h0 => by
    have him := congrArg Complex.im h0; simp [z] at him
  have hz_norm : ∀ x : ℝ, (1 / 2 : ℝ) ≤ ‖z x‖ := fun x => by
    simpa [z, one_div] using Complex.abs_im_le_norm (z x)
  let F : ℝ → ℂ := fun x => Complex.exp (-(u : ℂ) * z x ^ 2) * (-(1 / (4 * z x)))
  let F' : ℝ → ℂ := fun x =>
    ((u : ℂ) / 2) * Complex.exp (-(u : ℂ) * z x ^ 2) +
      Complex.exp (-(u : ℂ) * z x ^ 2) / (4 * z x ^ 2)
  have hderiv : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    have hdz : HasDerivAt z 1 x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).fun_add (hasDerivAt_const x (I / 2))).congr_deriv (by simp)
    have hde : HasDerivAt (fun t => Complex.exp (-(u : ℂ) * z t ^ 2))
        (Complex.exp (-(u : ℂ) * z x ^ 2) * (-(u : ℂ) * (2 * z x))) x := by
      have hsq := (hdz.fun_pow 2).const_mul (-(u : ℂ))
      exact hsq.cexp.congr_deriv (by ring)
    have hdi : HasDerivAt (fun t => -(1 / (4 * z t))) (1 / (4 * z x ^ 2)) x := by
      have h1 := ((hdz.const_mul (4 : ℂ)).fun_inv (mul_ne_zero (by norm_num) (hz_ne x))).fun_neg
      refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp [one_div])).congr_deriv ?_
      field_simp [hz_ne x]
    exact (hde.fun_mul hdi).congr_deriv (by
      dsimp only [F']; field_simp [hz_ne x]; ring)
  have hint_g1 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2)) volume := by
    refine (integrable_shifted_gaussian_mul_lin (B := 1) hu).mono'
      (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_exp, re_neg_mul_line_sq u x]
    nlinarith [abs_nonneg x, Real.exp_pos (-u * (x ^ 2 - 1 / 4))]
  have hint_g2 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) / (4 * z x ^ 2)) volume := by
    refine (integrable_shifted_gaussian_mul_lin (B := 1) hu).mono'
      ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).div
        (continuous_const.mul ((by fun_prop : Continuous z).pow 2))
        (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hz_ne x)))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_exp, re_neg_mul_line_sq u x]
    have h4 : (1 : ℝ) ≤ 4 * ‖z x‖ ^ 2 := by nlinarith [hz_norm x]
    have hdiv : Real.exp (-u * (x ^ 2 - 1 / 4)) / (4 * ‖z x‖ ^ 2) ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) :=
      div_le_self (Real.exp_pos _).le h4
    nlinarith [abs_nonneg x, Real.exp_pos (-u * (x ^ 2 - 1 / 4))]
  have htend : ∀ (l : Filter ℝ), (l = atTop ∨ l = atBot) → Tendsto F l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (a := fun x : ℝ => Real.exp (u / 4) * Real.exp (-u * x ^ 2)) (fun x => ?_) ?_
    · change ‖F x‖ ≤ Real.exp (u / 4) * Real.exp (-u * x ^ 2)
      dsimp only [F]
      rw [norm_mul, norm_neg, norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_exp,
        re_neg_mul_line_sq u x, show -u * (x ^ 2 - 1 / 4) = u / 4 + (-u * x ^ 2) by ring, Real.exp_add]
      have h2 : (1 : ℝ) / (4 * ‖z x‖) ≤ 1 := by
        rw [div_le_one (by linarith [hz_norm x])]; linarith [hz_norm x]
      calc Real.exp (u / 4) * Real.exp (-u * x ^ 2) * (1 / (4 * ‖z x‖))
          ≤ Real.exp (u / 4) * Real.exp (-u * x ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := mul_one _
    · have hsq_top : Tendsto (fun x : ℝ => x ^ 2) l atTop := by
        rcases hl with rfl | rfl
        · exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
        · have hneg : Tendsto (fun x : ℝ => (-x) ^ 2) atBot atTop :=
            (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_neg_atBot_atTop
          simpa using hneg
      have hneg_bot : Tendsto (fun x : ℝ => -u * x ^ 2) l atBot := by
        have h := hsq_top.const_mul_atTop hu
        have h2 := tendsto_neg_atTop_atBot.comp h
        exact h2.congr fun x => by dsimp only [Function.comp_apply]; ring
      have hexp0 : Tendsto (fun x : ℝ => Real.exp (-u * x ^ 2)) l (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hneg_bot
      simpa using hexp0.const_mul (Real.exp (u / 4))
  have hftc := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv
    ((hint_g1.const_mul _).add hint_g2) (htend atBot (Or.inr rfl)) (htend atTop (Or.inl rfl))
  dsimp only [F'] at hftc
  rw [sub_self, integral_add (hint_g1.const_mul _) hint_g2, integral_const_mul] at hftc
  have hg0 := shifted_gaussian_fourier 0 hu
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, zero_pow two_ne_zero,
    zero_div, neg_zero] at hg0
  rw [hg0] at hftc
  linear_combination hftc

private lemma hasDerivAt_ccos_real {z : ℝ → ℂ} {z' : ℂ} {x : ℝ} (hdz : HasDerivAt z z' x) :
    HasDerivAt (fun t : ℝ => Complex.cos (z t)) (-Complex.sin (z x) * z') x := by
  have h1 : HasDerivAt (fun t : ℝ => (Complex.exp (z t * I) + Complex.exp (-(z t * I))) / 2)
      (((Complex.exp (z x * I) * (z' * I)) + (Complex.exp (-(z x * I)) * -(z' * I))) / 2) x :=
    (((hdz.mul_const I).cexp).fun_add (((hdz.mul_const I).fun_neg).cexp)).div_const 2
  refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by rw [Complex.cos, neg_mul])).congr_deriv ?_
  rw [Complex.sin, neg_mul]; ring

private lemma hasDerivAt_csin_real {z : ℝ → ℂ} {z' : ℂ} {x : ℝ} (hdz : HasDerivAt z z' x) :
    HasDerivAt (fun t : ℝ => Complex.sin (z t)) (Complex.cos (z x) * z') x := by
  have h1 : HasDerivAt (fun t : ℝ => (Complex.exp (-(z t * I)) - Complex.exp (z t * I)) * I / 2)
      ((((Complex.exp (-(z x * I)) * -(z' * I)) - (Complex.exp (z x * I) * (z' * I))) * I) / 2) x :=
    (((((hdz.mul_const I).fun_neg).cexp).fun_sub ((hdz.mul_const I).cexp)).mul_const I).div_const 2
  refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by rw [Complex.sin, neg_mul])).congr_deriv ?_
  rw [Complex.cos, neg_mul]; ring_nf; rw [Complex.I_sq]; ring

private lemma baseHeatInt_eq_gaussianKernelIntegral {u : ℝ} (hu : 0 < u) :
    (2 : ℂ) / (u : ℂ) ^ 2 * (baseHeatInt (1 / u) - (u : ℂ) / 2) =
      gaussianKernelIntegral heatIntKernel u := by
  let z : ℝ → ℂ := fun x => (x : ℂ) + I / 2
  have hz_ne : ∀ x : ℝ, z x ≠ 0 := fun x h0 => by
    have him := congrArg Complex.im h0; simp [z] at him
  have hz_norm : ∀ x : ℝ, (1 / 2 : ℝ) ≤ ‖z x‖ := fun x => by
    simpa [z, one_div] using Complex.abs_im_le_norm (z x)
  -- Step 1: Fubini / integral_tsum for baseHeatInt (1/u)
  have hbase_int : ((Real.sqrt (Real.pi / u) : ℝ) : ℂ) * baseHeatInt (1 / u) =
      ∫ x : ℝ, Complex.exp (-(u : ℂ) * z x ^ 2) * (-1 / (4 * Complex.sin (z x) ^ 2)) := by
    have htsum_eq : ∀ x : ℝ,
        Complex.exp (-(u : ℂ) * z x ^ 2) * (-1 / (4 * Complex.sin (z x) ^ 2)) =
          ∑' n : ℕ, Complex.exp (-(u : ℂ) * z x ^ 2) *
            (((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x)) := by
      intro x; rw [← tsum_int_trig x, ← tsum_mul_left]
    simp_rw [htsum_eq]
    have hswap :
        (∫ x : ℝ, ∑' n : ℕ, Complex.exp (-(u : ℂ) * z x ^ 2) *
            (((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x))) =
        ∑' n : ℕ, ∫ x : ℝ, Complex.exp (-(u : ℂ) * z x ^ 2) *
            (((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x)) := by
      refine MeasureTheory.integral_tsum (fun n => by fun_prop) ?_
      have hterm_lintegral : ∀ n : ℕ,
          (∫⁻ x : ℝ, ‖Complex.exp (-(u : ℂ) * z x ^ 2) *
              (((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x))‖ₑ) =
          ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ)) *
            Real.exp (u / 4) * Real.sqrt (Real.pi / u)) := by
        intro n
        have hnorm_eq : ∀ x : ℝ,
            ‖Complex.exp (-(u : ℂ) * z x ^ 2) *
                (((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x))‖ =
              (((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ)) * Real.exp (u / 4)) *
                Real.exp (-u * x ^ 2) := by
          intro x
          rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp, Complex.norm_exp,
            re_neg_mul_line_sq u x, show -u * (x ^ 2 - 1 / 4) = u / 4 + (-u * x ^ 2) by ring,
            (show (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x).re = -((n + 1 : ℕ) : ℝ) by
              simp [z, Complex.mul_re, Complex.add_re, Complex.add_im]; ring),
            Real.exp_add]
          ring
        have hint_n : Integrable (fun x : ℝ =>
            (((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ)) * Real.exp (u / 4)) *
              Real.exp (-u * x ^ 2)) volume := (integrable_exp_neg_mul_sq hu).const_mul _
        calc (∫⁻ x : ℝ, ‖Complex.exp (-(u : ℂ) * z x ^ 2) *
                (((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x))‖ₑ)
            = ∫⁻ x : ℝ, ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ)) *
                Real.exp (u / 4)) * Real.exp (-u * x ^ 2)) := by
                refine lintegral_congr fun x => ?_
                rw [← ofReal_norm, hnorm_eq x]
          _ = ENNReal.ofReal (∫ x : ℝ, (((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ)) *
                Real.exp (u / 4)) * Real.exp (-u * x ^ 2)) :=
                (ofReal_integral_eq_lintegral_ofReal hint_n (ae_of_all _ fun _ => by positivity)).symm
          _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ)) *
                Real.exp (u / 4) * Real.sqrt (Real.pi / u)) := by
                rw [integral_const_mul, integral_gaussian u, mul_assoc]
      simp_rw [hterm_lintegral]
      have hsumm : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ)) *
          Real.exp (u / 4) * Real.sqrt (Real.pi / u)) := by
        have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        have h0 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * Real.exp (-1) ^ n) := by
          have ha := summable_nat_mul_geometric_of_lt_one (Real.exp_pos _).le hlt
          have hb := summable_geometric_of_lt_one (Real.exp_pos _).le hlt
          exact (ha.add hb).congr fun n => by push_cast; ring
        refine (h0.mul_right (Real.exp (-1) * Real.exp (u / 4) * Real.sqrt (Real.pi / u))).congr fun n => ?_
        rw [show -((n + 1 : ℕ) : ℝ) = (n : ℝ) * (-1) + (-1) by push_cast; ring, Real.exp_add, Real.exp_nat_mul]
        ring
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsumm]
      exact ENNReal.ofReal_ne_top
    rw [hswap]
    unfold baseHeatInt
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hrew_n : (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) *
          (((n + 1 : ℕ) : ℂ) * Complex.exp (I * (2 * ((n + 1 : ℕ) : ℂ)) * z x))) =
        fun x : ℝ => ((n + 1 : ℕ) : ℂ) * (Complex.exp (-(u : ℂ) * z x ^ 2) *
          Complex.exp (I * ((2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * z x)) := by
      funext x; push_cast; ring
    rw [hrew_n, integral_const_mul, shifted_gaussian_fourier (2 * ((n + 1 : ℕ) : ℝ)) hu]
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hexp : -(((2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 / (4 * (u : ℂ))) =
        -(((1 / u : ℝ) : ℂ)) * (((n + 1 : ℕ) : ℂ) ^ 2) := by
      push_cast; field_simp [huC]; ring
    rw [hexp]; ring
  -- Step 2: 1D IBP on F(x) = exp(-u z^2) * (1/4) * (cos z / sin z - 1 / z)
  let F : ℝ → ℂ := fun x => Complex.exp (-(u : ℂ) * z x ^ 2) * ((1 / 4 : ℂ) * (Complex.cos (z x) / Complex.sin (z x) - 1 / z x))
  let F' : ℝ → ℂ := fun x =>
    -((u : ℂ) / 2) * (Complex.exp (-(u : ℂ) * z x ^ 2) * heatIntKernel (z x ^ 2)) +
      Complex.exp (-(u : ℂ) * z x ^ 2) * (-1 / (4 * Complex.sin (z x) ^ 2)) +
      Complex.exp (-(u : ℂ) * z x ^ 2) / (4 * z x ^ 2)
  have hK_val : ∀ x : ℝ, heatIntKernel (z x ^ 2) = z x * Complex.cos (z x) / Complex.sin (z x) - 1 := by
    intro x
    unfold heatIntKernel
    have hmul := mul_sinSqrt_sq (z x)
    have hss_ne : sinSqrt (z x ^ 2) ≠ 0 := fun h0 => sin_line_ne_zero x (by rw [← hmul, h0, mul_zero])
    rw [cosSqrt_sq, ← hmul]
    field_simp [hz_ne x, hss_ne]
  have hderiv : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    have hdz : HasDerivAt z 1 x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).fun_add (hasDerivAt_const x (I / 2))).congr_deriv (by simp)
    have hde : HasDerivAt (fun t => Complex.exp (-(u : ℂ) * z t ^ 2))
        (Complex.exp (-(u : ℂ) * z x ^ 2) * (-(u : ℂ) * (2 * z x))) x :=
      (((hdz.fun_pow 2).const_mul (-(u : ℂ))).cexp).congr_deriv (by ring)
    have hdcos : HasDerivAt (fun t => Complex.cos (z t)) (-Complex.sin (z x)) x :=
      (hasDerivAt_ccos_real hdz).congr_deriv (by simp)
    have hdsin : HasDerivAt (fun t => Complex.sin (z t)) (Complex.cos (z x)) x :=
      (hasDerivAt_csin_real hdz).congr_deriv (by simp)
    have hdcot : HasDerivAt (fun t => Complex.cos (z t) / Complex.sin (z t))
        (-1 / Complex.sin (z x) ^ 2) x := by
      refine (hdcos.fun_div hdsin (sin_line_ne_zero x)).congr_deriv ?_
      have hsc := Complex.sin_sq_add_cos_sq (z x)
      congr 1; linear_combination -hsc
    have hdin : HasDerivAt (fun t => (1 : ℂ) / z t) (-1 / z x ^ 2) x := by
      have h1 := hdz.fun_inv (hz_ne x)
      refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp [one_div])).congr_deriv ?_
      field_simp [hz_ne x]
    have hd2 := (hdcot.fun_sub hdin).const_mul (1 / 4 : ℂ)
    refine (hde.fun_mul hd2).congr_deriv ?_
    dsimp only [F']
    rw [hK_val x]
    field_simp [hz_ne x, sin_line_ne_zero x]
    ring
  have hsinh_pos : 0 < Real.sinh (1 / 2) := by
    rw [Real.sinh_eq]
    linarith [Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1 / 2),
      Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)]
  have hcot_bd : ∀ x : ℝ, ‖Complex.cos (z x) / Complex.sin (z x)‖ ≤ Real.cosh (1 / 2) / Real.sinh (1 / 2) := by
    intro x; rw [norm_div]
    exact div_le_div₀ (by positivity) (cos_line_upper_bound x) hsinh_pos (sin_line_lower_bound x)
  have hint1 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) * heatIntKernel (z x ^ 2)) volume := by
    let B : ℝ := Real.cosh (1 / 2) / Real.sinh (1 / 2) + 1
    refine (integrable_shifted_gaussian_mul_lin (B := B) hu).mono' ?_ (ae_of_all _ fun x => ?_)
    · have hcont : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) *
          (z x * Complex.cos (z x) / Complex.sin (z x) - 1)) :=
        (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).mul
          ((((by fun_prop : Continuous z).mul (Complex.continuous_cos.comp (by fun_prop : Continuous z))).div
            (Complex.continuous_sin.comp (by fun_prop : Continuous z)) sin_line_ne_zero).sub continuous_const)
      exact hcont.aestronglyMeasurable.congr (ae_of_all _ fun x => by dsimp only; rw [hK_val x])
    · rw [hK_val x, norm_mul, Complex.norm_exp, re_neg_mul_line_sq u x]
      have hzn : ‖z x‖ ≤ 1 + |x| := by
        calc ‖(x : ℂ) + I / 2‖ ≤ ‖(x : ℂ)‖ + ‖I / 2‖ := norm_add_le _ _
          _ = |x| + 1 / 2 := by simp [Complex.norm_real]
          _ ≤ 1 + |x| := by linarith
      have hKb : ‖z x * Complex.cos (z x) / Complex.sin (z x) - 1‖ ≤ B * (1 + |x|) := by
        calc ‖z x * Complex.cos (z x) / Complex.sin (z x) - 1‖
            ≤ ‖z x * (Complex.cos (z x) / Complex.sin (z x))‖ + ‖(1 : ℂ)‖ := by
              rw [mul_div_assoc]; exact norm_sub_le _ _
          _ = ‖z x‖ * ‖Complex.cos (z x) / Complex.sin (z x)‖ + 1 := by rw [norm_mul, norm_one]
          _ ≤ (1 + |x|) * (Real.cosh (1 / 2) / Real.sinh (1 / 2)) + (1 + |x|) := by
              have := mul_le_mul hzn (hcot_bd x) (norm_nonneg _) (by positivity)
              linarith [abs_nonneg x]
          _ = B * (1 + |x|) := by dsimp only [B]; ring
      calc Real.exp (-u * (x ^ 2 - 1 / 4)) * ‖z x * Complex.cos (z x) / Complex.sin (z x) - 1‖
          ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) * (B * (1 + |x|)) :=
            mul_le_mul_of_nonneg_left hKb (Real.exp_pos _).le
        _ = B * (1 + |x|) * Real.exp (-u * (x ^ 2 - 1 / 4)) := by ring
  have hint2 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) * (-1 / (4 * Complex.sin (z x) ^ 2))) volume := by
    let B : ℝ := 1 / (4 * Real.sinh (1 / 2) ^ 2)
    refine (integrable_shifted_gaussian_mul_lin (B := B) hu).mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).mul
        (continuous_const.div (continuous_const.mul ((Complex.continuous_sin.comp (by fun_prop : Continuous z)).pow 2))
          (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 2 (sin_line_ne_zero x))))).aestronglyMeasurable
    · rw [norm_mul, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_exp,
        re_neg_mul_line_sq u x]
      have hs2 : 4 * Real.sinh (1 / 2) ^ 2 ≤ 4 * ‖Complex.sin (z x)‖ ^ 2 := by
        nlinarith [sin_line_lower_bound x, hsinh_pos]
      have hdiv : 1 / (4 * ‖Complex.sin (z x)‖ ^ 2) ≤ B :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) hs2
      have h1x : B ≤ B * (1 + |x|) := le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg x])
      calc Real.exp (-u * (x ^ 2 - 1 / 4)) * (1 / (4 * ‖Complex.sin (z x)‖ ^ 2))
          ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) * (B * (1 + |x|)) :=
            mul_le_mul_of_nonneg_left (hdiv.trans h1x) (Real.exp_pos _).le
        _ = B * (1 + |x|) * Real.exp (-u * (x ^ 2 - 1 / 4)) := by ring
  have hint3 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) / (4 * z x ^ 2)) volume := by
    refine (integrable_shifted_gaussian_mul_lin (B := 1) hu).mono'
      ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).div
        (continuous_const.mul ((by fun_prop : Continuous z).pow 2))
        (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hz_ne x)))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_exp, re_neg_mul_line_sq u x]
    have h4 : (1 : ℝ) ≤ 4 * ‖z x‖ ^ 2 := by nlinarith [hz_norm x]
    have hdiv : Real.exp (-u * (x ^ 2 - 1 / 4)) / (4 * ‖z x‖ ^ 2) ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) :=
      div_le_self (Real.exp_pos _).le h4
    nlinarith [abs_nonneg x, Real.exp_pos (-u * (x ^ 2 - 1 / 4))]
  have htend : ∀ (l : Filter ℝ), (l = atTop ∨ l = atBot) → Tendsto F l (𝓝 0) := by
    intro l hl
    let C : ℝ := (1 / 4 : ℝ) * (Real.cosh (1 / 2) / Real.sinh (1 / 2) + 2) * Real.exp (u / 4)
    refine squeeze_zero_norm (a := fun x : ℝ => C * Real.exp (-u * x ^ 2)) (fun x => ?_) ?_
    · change ‖F x‖ ≤ C * Real.exp (-u * x ^ 2)
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_exp, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num,
        re_neg_mul_line_sq u x, show -u * (x ^ 2 - 1 / 4) = u / 4 + (-u * x ^ 2) by ring, Real.exp_add]
      have h2 : ‖Complex.cos (z x) / Complex.sin (z x) - 1 / z x‖ ≤
          Real.cosh (1 / 2) / Real.sinh (1 / 2) + 2 := by
        have hiz : ‖(1 : ℂ) / z x‖ ≤ 2 := by
          rw [norm_div, norm_one]; exact (div_le_iff₀ (by linarith [hz_norm x])).mpr (by linarith [hz_norm x])
        linarith [norm_sub_le (Complex.cos (z x) / Complex.sin (z x)) (1 / z x), hcot_bd x]
      calc Real.exp (u / 4) * Real.exp (-u * x ^ 2) * ((1 / 4 : ℝ) * ‖Complex.cos (z x) / Complex.sin (z x) - 1 / z x‖)
          ≤ Real.exp (u / 4) * Real.exp (-u * x ^ 2) * ((1 / 4 : ℝ) * (Real.cosh (1 / 2) / Real.sinh (1 / 2) + 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by positivity)
        _ = C * Real.exp (-u * x ^ 2) := by dsimp only [C]; ring
    · have hsq_top : Tendsto (fun x : ℝ => x ^ 2) l atTop := by
        rcases hl with rfl | rfl
        · exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
        · have hneg : Tendsto (fun x : ℝ => (-x) ^ 2) atBot atTop :=
            (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_neg_atBot_atTop
          simpa using hneg
      have hneg_bot : Tendsto (fun x : ℝ => -u * x ^ 2) l atBot := by
        have h := hsq_top.const_mul_atTop hu
        have h2 := tendsto_neg_atTop_atBot.comp h
        exact h2.congr fun x => by dsimp only [Function.comp_apply]; ring
      simpa using (Real.tendsto_exp_atBot.comp hneg_bot).const_mul C
  have hftc := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv
    (((hint1.const_mul _).add hint2).add hint3) (htend atBot (Or.inr rfl)) (htend atTop (Or.inl rfl))
  have h12 : Integrable (fun x : ℝ => -((u : ℂ) / 2) * (Complex.exp (-(u : ℂ) * z x ^ 2) * heatIntKernel (z x ^ 2)) +
      Complex.exp (-(u : ℂ) * z x ^ 2) * (-1 / (4 * Complex.sin (z x) ^ 2))) volume :=
    (hint1.const_mul _).add hint2
  dsimp only [F'] at hftc
  rw [sub_self, integral_add h12 hint3,
    integral_add (hint1.const_mul _) hint2, integral_const_mul, ← hbase_int, ibp_inv_z_sq hu] at hftc
  unfold gaussianKernelIntegral invSqrtPi
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsu : ((Real.sqrt u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne'
  have hsq : ((Real.sqrt u : ℝ) : ℂ) * ((Real.sqrt u : ℝ) : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
  rw [Real.sqrt_mul Real.pi_pos.le u, Complex.ofReal_mul]
  rw [Real.sqrt_div Real.pi_pos.le u, Complex.ofReal_div] at hftc
  have hrel : ∫ x : ℝ, Complex.exp (-(u : ℂ) * z x ^ 2) * heatIntKernel (z x ^ 2) =
      (2 : ℂ) / (u : ℂ) * (((Real.sqrt Real.pi : ℝ) : ℂ) / ((Real.sqrt u : ℝ) : ℂ)) *
        (baseHeatInt (1 / u) - (u : ℂ) / 2) := by
    field_simp [huC, hsu] at hftc ⊢
    linear_combination -hftc
  rw [hrel]
  field_simp [huC, hpi, hsu]
  rw [← hsq]; ring

private lemma baseHeatHalf_eq_gaussianKernelIntegral {u : ℝ} (hu : 0 < u) :
    (2 : ℂ) / (u : ℂ) ^ 2 * (baseHeatHalf (1 / u) - (u : ℂ) / 2) =
      gaussianKernelIntegral heatHalfKernel u := by
  let z : ℝ → ℂ := fun x => (x : ℂ) + I / 2
  have hz_ne : ∀ x : ℝ, z x ≠ 0 := fun x h0 => by
    have him := congrArg Complex.im h0; simp [z] at him
  have hz_norm : ∀ x : ℝ, (1 / 2 : ℝ) ≤ ‖z x‖ := fun x => by
    simpa [z, one_div] using Complex.abs_im_le_norm (z x)
  -- Step 1: Fubini / integral_tsum for baseHeatHalf (1/u)
  have hbase_half : ((Real.sqrt (Real.pi / u) : ℝ) : ℂ) * baseHeatHalf (1 / u) =
      ∫ x : ℝ, Complex.exp (-(u : ℂ) * z x ^ 2) * (-Complex.cos (z x) / (4 * Complex.sin (z x) ^ 2)) := by
    have htsum_eq : ∀ x : ℝ,
        Complex.exp (-(u : ℂ) * z x ^ 2) * (-Complex.cos (z x) / (4 * Complex.sin (z x) ^ 2)) =
          ∑' k : ℕ, Complex.exp (-(u : ℂ) * z x ^ 2) *
            (((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z x)) := by
      intro x; rw [← tsum_half_trig x, ← tsum_mul_left]
    simp_rw [htsum_eq]
    have hswap :
        (∫ x : ℝ, ∑' k : ℕ, Complex.exp (-(u : ℂ) * z x ^ 2) *
            (((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z x))) =
        ∑' k : ℕ, ∫ x : ℝ, Complex.exp (-(u : ℂ) * z x ^ 2) *
            (((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z x)) := by
      refine MeasureTheory.integral_tsum (fun k => by fun_prop) ?_
      have hterm_lintegral : ∀ k : ℕ,
          (∫⁻ x : ℝ, ‖Complex.exp (-(u : ℂ) * z x ^ 2) *
              (((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z x))‖ₑ) =
          ENNReal.ofReal (((k : ℝ) + 1 / 2) * Real.exp (-((k : ℝ) + 1 / 2)) *
            Real.exp (u / 4) * Real.sqrt (Real.pi / u)) := by
        intro k
        have hnorm_eq : ∀ x : ℝ,
            ‖Complex.exp (-(u : ℂ) * z x ^ 2) *
                (((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z x))‖ =
              (((k : ℝ) + 1 / 2) * Real.exp (-((k : ℝ) + 1 / 2)) * Real.exp (u / 4)) *
                Real.exp (-u * x ^ 2) := by
          intro x
          rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
            (show ‖(k : ℂ) + 1 / 2‖ = (k : ℝ) + 1 / 2 by
              rw [show (k : ℂ) + 1 / 2 = (((k : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; rfl,
                Complex.norm_real, Real.norm_of_nonneg (by positivity)]),
            re_neg_mul_line_sq u x, show -u * (x ^ 2 - 1 / 4) = u / 4 + (-u * x ^ 2) by ring,
            (show (I * (2 * (k : ℂ) + 1) * z x).re = -((k : ℝ) + 1 / 2) by
              simp [z, Complex.mul_re, Complex.add_re, Complex.add_im]; ring),
            Real.exp_add]
          ring
        have hint_k : Integrable (fun x : ℝ =>
            (((k : ℝ) + 1 / 2) * Real.exp (-((k : ℝ) + 1 / 2)) * Real.exp (u / 4)) *
              Real.exp (-u * x ^ 2)) volume := (integrable_exp_neg_mul_sq hu).const_mul _
        calc (∫⁻ x : ℝ, ‖Complex.exp (-(u : ℂ) * z x ^ 2) *
                (((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z x))‖ₑ)
            = ∫⁻ x : ℝ, ENNReal.ofReal ((((k : ℝ) + 1 / 2) * Real.exp (-((k : ℝ) + 1 / 2)) *
                Real.exp (u / 4)) * Real.exp (-u * x ^ 2)) := by
                refine lintegral_congr fun x => ?_
                rw [← ofReal_norm, hnorm_eq x]
          _ = ENNReal.ofReal (∫ x : ℝ, (((k : ℝ) + 1 / 2) * Real.exp (-((k : ℝ) + 1 / 2)) *
                Real.exp (u / 4)) * Real.exp (-u * x ^ 2)) :=
                (ofReal_integral_eq_lintegral_ofReal hint_k (ae_of_all _ fun _ => by positivity)).symm
          _ = ENNReal.ofReal (((k : ℝ) + 1 / 2) * Real.exp (-((k : ℝ) + 1 / 2)) *
                Real.exp (u / 4) * Real.sqrt (Real.pi / u)) := by
                rw [integral_const_mul, integral_gaussian u, mul_assoc]
      simp_rw [hterm_lintegral]
      have hsumm : Summable (fun k : ℕ => ((k : ℝ) + 1 / 2) * Real.exp (-((k : ℝ) + 1 / 2)) *
          Real.exp (u / 4) * Real.sqrt (Real.pi / u)) := by
        have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        have h0 : Summable (fun k : ℕ => ((k : ℝ) + 1 / 2) * Real.exp (-1) ^ k) := by
          have ha := summable_nat_mul_geometric_of_lt_one (Real.exp_pos _).le hlt
          have hb := (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left (1 / 2 : ℝ)
          exact (ha.add hb).congr fun k => by ring
        refine (h0.mul_right (Real.exp (-(1 / 2)) * Real.exp (u / 4) * Real.sqrt (Real.pi / u))).congr fun k => ?_
        rw [show -((k : ℝ) + 1 / 2) = (k : ℝ) * (-1) + (-(1 / 2)) by ring, Real.exp_add, Real.exp_nat_mul]
        ring
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsumm]
      exact ENNReal.ofReal_ne_top
    rw [hswap]
    unfold baseHeatHalf
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hrew_k : (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) *
          (((k : ℂ) + 1 / 2) * Complex.exp (I * (2 * (k : ℂ) + 1) * z x))) =
        fun x : ℝ => ((k : ℂ) + 1 / 2) * (Complex.exp (-(u : ℂ) * z x ^ 2) *
          Complex.exp (I * ((2 * (k : ℝ) + 1 : ℝ) : ℂ) * z x)) := by
      funext x; push_cast; ring
    rw [hrew_k, integral_const_mul, shifted_gaussian_fourier (2 * (k : ℝ) + 1) hu]
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hexp : -(((2 * (k : ℝ) + 1 : ℝ) : ℂ) ^ 2 / (4 * (u : ℂ))) =
        -(((1 / u : ℝ) : ℂ)) * (((k : ℂ) + 1 / 2) ^ 2) := by
      push_cast; field_simp [huC]; ring
    rw [hexp]; ring
  -- Step 2: 1D IBP on F(x) = exp(-u z^2) * (1/4) * (1 / sin z - 1 / z)
  let F : ℝ → ℂ := fun x => Complex.exp (-(u : ℂ) * z x ^ 2) * ((1 / 4 : ℂ) * (1 / Complex.sin (z x) - 1 / z x))
  let F' : ℝ → ℂ := fun x =>
    -((u : ℂ) / 2) * (Complex.exp (-(u : ℂ) * z x ^ 2) * heatHalfKernel (z x ^ 2)) +
      Complex.exp (-(u : ℂ) * z x ^ 2) * (-Complex.cos (z x) / (4 * Complex.sin (z x) ^ 2)) +
      Complex.exp (-(u : ℂ) * z x ^ 2) / (4 * z x ^ 2)
  have hK_val : ∀ x : ℝ, heatHalfKernel (z x ^ 2) = z x / Complex.sin (z x) - 1 := by
    intro x
    unfold heatHalfKernel
    have hmul := mul_sinSqrt_sq (z x)
    have hss_ne : sinSqrt (z x ^ 2) ≠ 0 := fun h0 => sin_line_ne_zero x (by rw [← hmul, h0, mul_zero])
    rw [← hmul]
    field_simp [hz_ne x, hss_ne]
  have hderiv : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    have hdz : HasDerivAt z 1 x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).fun_add (hasDerivAt_const x (I / 2))).congr_deriv (by simp)
    have hde : HasDerivAt (fun t => Complex.exp (-(u : ℂ) * z t ^ 2))
        (Complex.exp (-(u : ℂ) * z x ^ 2) * (-(u : ℂ) * (2 * z x))) x :=
      (((hdz.fun_pow 2).const_mul (-(u : ℂ))).cexp).congr_deriv (by ring)
    have hdsin : HasDerivAt (fun t => Complex.sin (z t)) (Complex.cos (z x)) x :=
      (hasDerivAt_csin_real hdz).congr_deriv (by simp)
    have hdcsc : HasDerivAt (fun t => (1 : ℂ) / Complex.sin (z t))
        (-Complex.cos (z x) / Complex.sin (z x) ^ 2) x := by
      have h1 := hdsin.fun_inv (sin_line_ne_zero x)
      refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp [one_div])).congr_deriv ?_
      field_simp [sin_line_ne_zero x]
    have hdin : HasDerivAt (fun t => (1 : ℂ) / z t) (-1 / z x ^ 2) x := by
      have h1 := hdz.fun_inv (hz_ne x)
      refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp [one_div])).congr_deriv ?_
      field_simp [hz_ne x]
    have hd2 := (hdcsc.fun_sub hdin).const_mul (1 / 4 : ℂ)
    refine (hde.fun_mul hd2).congr_deriv ?_
    dsimp only [F']
    rw [hK_val x]
    field_simp [hz_ne x, sin_line_ne_zero x]
    ring
  have hsinh_pos : 0 < Real.sinh (1 / 2) := by
    rw [Real.sinh_eq]
    linarith [Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1 / 2),
      Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)]
  have hcsc_bd : ∀ x : ℝ, ‖(1 : ℂ) / Complex.sin (z x)‖ ≤ 1 / Real.sinh (1 / 2) := by
    intro x; rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left zero_le_one hsinh_pos (sin_line_lower_bound x)
  have hint1 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) * heatHalfKernel (z x ^ 2)) volume := by
    let B : ℝ := 1 / Real.sinh (1 / 2) + 1
    refine (integrable_shifted_gaussian_mul_lin (B := B) hu).mono' ?_ (ae_of_all _ fun x => ?_)
    · have hcont : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) *
          (z x / Complex.sin (z x) - 1)) :=
        (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).mul
          (((by fun_prop : Continuous z).div
            (Complex.continuous_sin.comp (by fun_prop : Continuous z)) sin_line_ne_zero).sub continuous_const)
      exact hcont.aestronglyMeasurable.congr (ae_of_all _ fun x => by dsimp only; rw [hK_val x])
    · rw [hK_val x, norm_mul, Complex.norm_exp, re_neg_mul_line_sq u x]
      have hzn : ‖z x‖ ≤ 1 + |x| := by
        calc ‖(x : ℂ) + I / 2‖ ≤ ‖(x : ℂ)‖ + ‖I / 2‖ := norm_add_le _ _
          _ = |x| + 1 / 2 := by simp [Complex.norm_real]
          _ ≤ 1 + |x| := by linarith
      have hKb : ‖z x / Complex.sin (z x) - 1‖ ≤ B * (1 + |x|) := by
        calc ‖z x / Complex.sin (z x) - 1‖
            ≤ ‖z x * ((1 : ℂ) / Complex.sin (z x))‖ + ‖(1 : ℂ)‖ := by
              rw [mul_one_div]; exact norm_sub_le _ _
          _ = ‖z x‖ * ‖(1 : ℂ) / Complex.sin (z x)‖ + 1 := by rw [norm_mul, norm_one]
          _ ≤ (1 + |x|) * (1 / Real.sinh (1 / 2)) + (1 + |x|) := by
              have := mul_le_mul hzn (hcsc_bd x) (norm_nonneg _) (by positivity)
              linarith [abs_nonneg x]
          _ = B * (1 + |x|) := by dsimp only [B]; ring
      calc Real.exp (-u * (x ^ 2 - 1 / 4)) * ‖z x / Complex.sin (z x) - 1‖
          ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) * (B * (1 + |x|)) :=
            mul_le_mul_of_nonneg_left hKb (Real.exp_pos _).le
        _ = B * (1 + |x|) * Real.exp (-u * (x ^ 2 - 1 / 4)) := by ring
  have hint2 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) *
      (-Complex.cos (z x) / (4 * Complex.sin (z x) ^ 2))) volume := by
    let B : ℝ := Real.cosh (1 / 2) / (4 * Real.sinh (1 / 2) ^ 2)
    refine (integrable_shifted_gaussian_mul_lin (B := B) hu).mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).mul
        ((Complex.continuous_cos.comp (by fun_prop : Continuous z)).neg.div
          (continuous_const.mul ((Complex.continuous_sin.comp (by fun_prop : Continuous z)).pow 2))
          (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 2 (sin_line_ne_zero x))))).aestronglyMeasurable
    · rw [norm_mul, norm_div, norm_neg, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_exp,
        re_neg_mul_line_sq u x]
      have hs2 : 4 * Real.sinh (1 / 2) ^ 2 ≤ 4 * ‖Complex.sin (z x)‖ ^ 2 := by
        nlinarith [sin_line_lower_bound x, hsinh_pos]
      have hdiv : ‖Complex.cos (z x)‖ / (4 * ‖Complex.sin (z x)‖ ^ 2) ≤ B :=
        div_le_div₀ (by positivity) (cos_line_upper_bound x) (by positivity) hs2
      have h1x : B ≤ B * (1 + |x|) := le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg x])
      calc Real.exp (-u * (x ^ 2 - 1 / 4)) * (‖Complex.cos (z x)‖ / (4 * ‖Complex.sin (z x)‖ ^ 2))
          ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) * (B * (1 + |x|)) :=
            mul_le_mul_of_nonneg_left (hdiv.trans h1x) (Real.exp_pos _).le
        _ = B * (1 + |x|) * Real.exp (-u * (x ^ 2 - 1 / 4)) := by ring
  have hint3 : Integrable (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2) / (4 * z x ^ 2)) volume := by
    refine (integrable_shifted_gaussian_mul_lin (B := 1) hu).mono'
      ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(u : ℂ) * z x ^ 2))).div
        (continuous_const.mul ((by fun_prop : Continuous z).pow 2))
        (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hz_ne x)))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_exp, re_neg_mul_line_sq u x]
    have h4 : (1 : ℝ) ≤ 4 * ‖z x‖ ^ 2 := by nlinarith [hz_norm x]
    have hdiv : Real.exp (-u * (x ^ 2 - 1 / 4)) / (4 * ‖z x‖ ^ 2) ≤ Real.exp (-u * (x ^ 2 - 1 / 4)) :=
      div_le_self (Real.exp_pos _).le h4
    nlinarith [abs_nonneg x, Real.exp_pos (-u * (x ^ 2 - 1 / 4))]
  have htend : ∀ (l : Filter ℝ), (l = atTop ∨ l = atBot) → Tendsto F l (𝓝 0) := by
    intro l hl
    let C : ℝ := (1 / 4 : ℝ) * (1 / Real.sinh (1 / 2) + 2) * Real.exp (u / 4)
    refine squeeze_zero_norm (a := fun x : ℝ => C * Real.exp (-u * x ^ 2)) (fun x => ?_) ?_
    · change ‖F x‖ ≤ C * Real.exp (-u * x ^ 2)
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_exp, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num,
        re_neg_mul_line_sq u x, show -u * (x ^ 2 - 1 / 4) = u / 4 + (-u * x ^ 2) by ring, Real.exp_add]
      have h2 : ‖1 / Complex.sin (z x) - 1 / z x‖ ≤ 1 / Real.sinh (1 / 2) + 2 := by
        have hiz : ‖(1 : ℂ) / z x‖ ≤ 2 := by
          rw [norm_div, norm_one]; exact (div_le_iff₀ (by linarith [hz_norm x])).mpr (by linarith [hz_norm x])
        linarith [norm_sub_le ((1 : ℂ) / Complex.sin (z x)) (1 / z x), hcsc_bd x]
      calc Real.exp (u / 4) * Real.exp (-u * x ^ 2) * ((1 / 4 : ℝ) * ‖1 / Complex.sin (z x) - 1 / z x‖)
          ≤ Real.exp (u / 4) * Real.exp (-u * x ^ 2) * ((1 / 4 : ℝ) * (1 / Real.sinh (1 / 2) + 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by positivity)
        _ = C * Real.exp (-u * x ^ 2) := by dsimp only [C]; ring
    · have hsq_top : Tendsto (fun x : ℝ => x ^ 2) l atTop := by
        rcases hl with rfl | rfl
        · exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
        · have hneg : Tendsto (fun x : ℝ => (-x) ^ 2) atBot atTop :=
            (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_neg_atBot_atTop
          simpa using hneg
      have hneg_bot : Tendsto (fun x : ℝ => -u * x ^ 2) l atBot := by
        have h := hsq_top.const_mul_atTop hu
        have h2 := tendsto_neg_atTop_atBot.comp h
        exact h2.congr fun x => by dsimp only [Function.comp_apply]; ring
      simpa using (Real.tendsto_exp_atBot.comp hneg_bot).const_mul C
  have hftc := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv
    (((hint1.const_mul _).add hint2).add hint3) (htend atBot (Or.inr rfl)) (htend atTop (Or.inl rfl))
  have h12 : Integrable (fun x : ℝ => -((u : ℂ) / 2) * (Complex.exp (-(u : ℂ) * z x ^ 2) * heatHalfKernel (z x ^ 2)) +
      Complex.exp (-(u : ℂ) * z x ^ 2) * (-Complex.cos (z x) / (4 * Complex.sin (z x) ^ 2))) volume :=
    (hint1.const_mul _).add hint2
  dsimp only [F'] at hftc
  rw [sub_self, integral_add h12 hint3,
    integral_add (hint1.const_mul _) hint2, integral_const_mul, ← hbase_half, ibp_inv_z_sq hu] at hftc
  unfold gaussianKernelIntegral invSqrtPi
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsu : ((Real.sqrt u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne'
  have hsq : ((Real.sqrt u : ℝ) : ℂ) * ((Real.sqrt u : ℝ) : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
  rw [Real.sqrt_mul Real.pi_pos.le u, Complex.ofReal_mul]
  rw [Real.sqrt_div Real.pi_pos.le u, Complex.ofReal_div] at hftc
  have hrel : ∫ x : ℝ, Complex.exp (-(u : ℂ) * z x ^ 2) * heatHalfKernel (z x ^ 2) =
      (2 : ℂ) / (u : ℂ) * (((Real.sqrt Real.pi : ℝ) : ℂ) / ((Real.sqrt u : ℝ) : ℂ)) *
        (baseHeatHalf (1 / u) - (u : ℂ) / 2) := by
    field_simp [huC, hsu] at hftc ⊢
    linear_combination -hftc
  rw [hrel]
  field_simp [huC, hpi, hsu]
  rw [← hsq]; ring

/-! #### D.4e. Unconditional `ℂ(t)`-D-Transcendence of `baseHeatInt`, `baseHeatHalf`, and Every Even-Dimensional Simply Connected CROSS Heat Trace -/

private lemma strip_sq_not_heatPole {z : ℂ} (hz : |z.re| < Real.pi) :
    z ^ 2 ∉ Set.range (fun m : ℕ => (heatPole m : ℂ)) := by
  rintro ⟨m, hm⟩
  have hre_sq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq, Complex.mul_re]
  have him_sq : (z ^ 2).im = 2 * z.re * z.im := by simp [sq, Complex.mul_im]; ring
  have him0 : (z ^ 2).im = 0 := by rw [← hm]; simp
  have hre_pos : 0 < (z ^ 2).re := by rw [← hm]; simpa using heatPole_pos m
  have hzim : z.im = 0 := by
    rcases mul_eq_zero.mp (by linarith [him_sq, him0] : 2 * z.re * z.im = 0) with h2r | hi
    · have hzr0 : z.re = 0 := (mul_eq_zero.mp h2r).resolve_left two_ne_zero
      rw [hzr0] at hre_sq; nlinarith [sq_nonneg z.im]
    · exact hi
  have hre_eq : z.re ^ 2 = (Real.pi * ((m : ℝ) + 1)) ^ 2 := by
    have := congrArg Complex.re hm
    rw [hre_sq, hzim, Complex.ofReal_re] at this
    simpa [heatPole] using this.symm
  have habs_ge : Real.pi ≤ |z.re| := by
    have h1 : (Real.pi * ((m : ℝ) + 1)) ^ 2 = |z.re| ^ 2 := by rw [sq_abs, hre_eq]
    have h2 : Real.pi ≤ Real.pi * ((m : ℝ) + 1) := le_mul_of_one_le_right Real.pi_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) m])
    nlinarith [abs_nonneg z.re, Real.pi_pos]
  linarith

private lemma ball_not_heatPole {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) ((Real.pi / 2) ^ 2)) :
    w ∉ Set.range (fun m : ℕ => (heatPole m : ℂ)) := by
  rintro ⟨m, hm⟩
  have hnorm : ‖w‖ ≤ (Real.pi / 2) ^ 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  rw [← hm, Complex.norm_real, Real.norm_of_nonneg (heatPole_pos m).le] at hnorm
  unfold heatPole at hnorm
  have h1 : Real.pi ≤ Real.pi * ((m : ℝ) + 1) := le_mul_of_one_le_right Real.pi_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) m])
  nlinarith [Real.pi_pos]

/-- **Unconditional `ℂ(t)`-D-Transcendence of the Integer-Lattice Base Heat Trace**:
`baseHeatInt(t) = ∑_{n ≥ 1} n e^{-t n²}` satisfies NO nonzero rational-coefficient
differential equation over `ℂ(t)` as `t → 0+`. Zero hypotheses! -/
theorem baseHeatInt_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val baseHeatInt t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 := by
  by_contra hP_ne
  obtain ⟨r', Q, hQ_ne, hQ_ev⟩ := invVar_ade_transfer baseHeatInt_analyticOn P hP_ne hP
  have hsinh_pos : 0 < Real.sinh (1 / 2) := by
    rw [Real.sinh_eq]
    linarith [Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1 / 2),
      Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)]
  have hK_val : ∀ x : ℝ, heatIntKernel (((x : ℂ) + I / 2) ^ 2) =
      ((x : ℂ) + I / 2) * Complex.cos ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2) - 1 := by
    intro x; unfold heatIntKernel
    have hz_ne : (x : ℂ) + I / 2 ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp at this
    have hmul := mul_sinSqrt_sq ((x : ℂ) + I / 2)
    rw [cosSqrt_sq, ← hmul, mul_div_mul_left _ _ hz_ne]
  have hK_cont : Continuous (fun x : ℝ => heatIntKernel (((x : ℂ) + I / 2) ^ 2)) := by
    have h : Continuous (fun x : ℝ =>
        ((x : ℂ) + I / 2) * Complex.cos ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2) - 1) :=
      ((((Complex.continuous_ofReal.add continuous_const).mul
        (Complex.continuous_cos.comp (Complex.continuous_ofReal.add continuous_const))).div
        (Complex.continuous_sin.comp (Complex.continuous_ofReal.add continuous_const)) sin_line_ne_zero).sub
        continuous_const)
    exact h.congr fun x => (hK_val x).symm
  have hK_line : ∀ x : ℝ, ‖heatIntKernel (((x : ℂ) + I / 2) ^ 2)‖ ≤
      (Real.cosh (1 / 2) / Real.sinh (1 / 2) + 1) * (1 + |x|) := by
    intro x; rw [hK_val x]
    have hzn : ‖(x : ℂ) + I / 2‖ ≤ 1 + |x| := by
      calc ‖(x : ℂ) + I / 2‖ ≤ ‖(x : ℂ)‖ + ‖I / 2‖ := norm_add_le _ _
        _ = |x| + 1 / 2 := by simp [Complex.norm_real]
        _ ≤ 1 + |x| := by linarith
    have hcot : ‖Complex.cos ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2)‖ ≤
        Real.cosh (1 / 2) / Real.sinh (1 / 2) := by
      rw [norm_div]
      exact div_le_div₀ (by positivity) (cos_line_upper_bound x) hsinh_pos (sin_line_lower_bound x)
    calc ‖((x : ℂ) + I / 2) * Complex.cos ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2) - 1‖
        ≤ ‖((x : ℂ) + I / 2) * (Complex.cos ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2))‖ + ‖(1 : ℂ)‖ := by
          rw [mul_div_assoc]; exact norm_sub_le _ _
      _ = ‖(x : ℂ) + I / 2‖ * ‖Complex.cos ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2)‖ + 1 := by
          rw [norm_mul, norm_one]
      _ ≤ (1 + |x|) * (Real.cosh (1 / 2) / Real.sinh (1 / 2)) + (1 + |x|) := by
          have := mul_le_mul hzn hcot (norm_nonneg _) (by positivity)
          linarith [abs_nonneg x]
      _ = (Real.cosh (1 / 2) / Real.sinh (1 / 2) + 1) * (1 + |x|) := by ring
  have hAsymp := gaussianKernelIntegral_hasAsympExp (K := heatIntKernel)
    (B := Real.cosh (1 / 2) / Real.sinh (1 / 2) + 1) heatIntKernel_zero
    (fun z hz => AnalyticAt.comp (g := heatIntKernel) (f := fun w : ℂ => w ^ 2)
      (heatIntKernel_analyticAt (strip_sq_not_heatPole hz)) (analyticAt_id.fun_pow 2))
    (fun w hw => heatIntKernel_analyticAt (ball_not_heatPole hw)) hK_cont hK_line
  have hQ_G : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r' + 1) => iteratedDeriv j.val (gaussianKernelIntegral heatIntKernel) u)
        (evalRatU Q (u : ℂ)) = 0 := by
    filter_upwards [hQ_ev, eventually_gt_atTop (0 : ℝ)] with u hu hu_pos
    have hloc : (fun w : ℝ => (2 : ℂ) / (w : ℂ) ^ 2 * (baseHeatInt (1 / w) - (w : ℂ) / 2)) =ᶠ[𝓝 u]
        gaussianKernelIntegral heatIntKernel := by
      filter_upwards [Ioi_mem_nhds hu_pos] with w hw
      exact baseHeatInt_eq_gaussianKernelIntegral hw
    have hj : (fun j : Fin (r' + 1) =>
          iteratedDeriv j.val (fun w : ℝ => (2 : ℂ) / (w : ℂ) ^ 2 * (baseHeatInt (1 / w) - (w : ℂ) / 2)) u) =
        fun j : Fin (r' + 1) => iteratedDeriv j.val (gaussianKernelIntegral heatIntKernel) u :=
      funext fun j => hloc.iteratedDeriv_eq j.val
    rwa [← hj]
  exact hQ_ne (branchPoint_stokes_vandermonde_no_rat_ade_of_asymp
    (abelConv_branchPointStokesData heatIntBorel_meromorphicBorelData) hAsymp Q hQ_G)

/-- **Unconditional `ℂ(t)`-D-Transcendence of the Half-Integer Base Heat Trace**:
`baseHeatHalf(t) = ∑_{k ≥ 0} (k + 1/2) e^{-t (k + 1/2)²}` satisfies NO nonzero rational-coefficient
differential equation over `ℂ(t)` as `t → 0+`. Zero hypotheses! -/
theorem baseHeatHalf_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val baseHeatHalf t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 := by
  by_contra hP_ne
  obtain ⟨r', Q, hQ_ne, hQ_ev⟩ := invVar_ade_transfer baseHeatHalf_analyticOn P hP_ne hP
  have hsinh_pos : 0 < Real.sinh (1 / 2) := by
    rw [Real.sinh_eq]
    linarith [Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1 / 2),
      Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)]
  have hK_val : ∀ x : ℝ, heatHalfKernel (((x : ℂ) + I / 2) ^ 2) =
      ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2) - 1 := by
    intro x; unfold heatHalfKernel
    have hz_ne : (x : ℂ) + I / 2 ≠ 0 := fun h0 => by have := congrArg Complex.im h0; simp at this
    have hmul := mul_sinSqrt_sq ((x : ℂ) + I / 2)
    rw [← hmul, ← one_div, ← mul_div_mul_left (1 : ℂ) (sinSqrt (((x : ℂ) + I / 2) ^ 2)) hz_ne, mul_one]
  have hK_cont : Continuous (fun x : ℝ => heatHalfKernel (((x : ℂ) + I / 2) ^ 2)) := by
    have h : Continuous (fun x : ℝ =>
        ((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2) - 1) :=
      (((Complex.continuous_ofReal.add continuous_const).div
        (Complex.continuous_sin.comp (Complex.continuous_ofReal.add continuous_const)) sin_line_ne_zero).sub
        continuous_const)
    exact h.congr fun x => (hK_val x).symm
  have hK_line : ∀ x : ℝ, ‖heatHalfKernel (((x : ℂ) + I / 2) ^ 2)‖ ≤
      (1 / Real.sinh (1 / 2) + 1) * (1 + |x|) := by
    intro x; rw [hK_val x]
    have hzn : ‖(x : ℂ) + I / 2‖ ≤ 1 + |x| := by
      calc ‖(x : ℂ) + I / 2‖ ≤ ‖(x : ℂ)‖ + ‖I / 2‖ := norm_add_le _ _
        _ = |x| + 1 / 2 := by simp [Complex.norm_real]
        _ ≤ 1 + |x| := by linarith
    have hcsc : ‖(1 : ℂ) / Complex.sin ((x : ℂ) + I / 2)‖ ≤ 1 / Real.sinh (1 / 2) := by
      rw [norm_div, norm_one]
      exact div_le_div_of_nonneg_left zero_le_one hsinh_pos (sin_line_lower_bound x)
    calc ‖((x : ℂ) + I / 2) / Complex.sin ((x : ℂ) + I / 2) - 1‖
        ≤ ‖((x : ℂ) + I / 2) * ((1 : ℂ) / Complex.sin ((x : ℂ) + I / 2))‖ + ‖(1 : ℂ)‖ := by
          rw [mul_one_div]; exact norm_sub_le _ _
      _ = ‖(x : ℂ) + I / 2‖ * ‖(1 : ℂ) / Complex.sin ((x : ℂ) + I / 2)‖ + 1 := by
          rw [norm_mul, norm_one]
      _ ≤ (1 + |x|) * (1 / Real.sinh (1 / 2)) + (1 + |x|) := by
          have := mul_le_mul hzn hcsc (norm_nonneg _) (by positivity)
          linarith [abs_nonneg x]
      _ = (1 / Real.sinh (1 / 2) + 1) * (1 + |x|) := by ring
  have hAsymp := gaussianKernelIntegral_hasAsympExp (K := heatHalfKernel)
    (B := 1 / Real.sinh (1 / 2) + 1) heatHalfKernel_zero
    (fun z hz => AnalyticAt.comp (g := heatHalfKernel) (f := fun w : ℂ => w ^ 2)
      (heatHalfKernel_analyticAt (strip_sq_not_heatPole hz)) (analyticAt_id.fun_pow 2))
    (fun w hw => heatHalfKernel_analyticAt (ball_not_heatPole hw)) hK_cont hK_line
  have hQ_G : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r' + 1) => iteratedDeriv j.val (gaussianKernelIntegral heatHalfKernel) u)
        (evalRatU Q (u : ℂ)) = 0 := by
    filter_upwards [hQ_ev, eventually_gt_atTop (0 : ℝ)] with u hu hu_pos
    have hloc : (fun w : ℝ => (2 : ℂ) / (w : ℂ) ^ 2 * (baseHeatHalf (1 / w) - (w : ℂ) / 2)) =ᶠ[𝓝 u]
        gaussianKernelIntegral heatHalfKernel := by
      filter_upwards [Ioi_mem_nhds hu_pos] with w hw
      exact baseHeatHalf_eq_gaussianKernelIntegral hw
    have hj : (fun j : Fin (r' + 1) =>
          iteratedDeriv j.val (fun w : ℝ => (2 : ℂ) / (w : ℂ) ^ 2 * (baseHeatHalf (1 / w) - (w : ℂ) / 2)) u) =
        fun j : Fin (r' + 1) => iteratedDeriv j.val (gaussianKernelIntegral heatHalfKernel) u :=
      funext fun j => hloc.iteratedDeriv_eq j.val
    rwa [← hj]
  exact hQ_ne (branchPoint_stokes_vandermonde_no_rat_ade_of_asymp
    (abelConv_branchPointStokesData heatHalfBorel_meromorphicBorelData) hAsymp Q hQ_G)

/-- **Master Unconditional All-CROSS Heat-Trace Theorem**:
For EVERY even-dimensional simply connected compact rank-1 symmetric space
(`S^{2r}`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`), its shifted spectral heat trace satisfies NO nonzero
rational-coefficient algebraic differential equation over `ℂ(t)` as `t → 0+`! -/
theorem evenCROSS_heatTrace_no_rat_ade (M : SimplyConnectedCROSS) (hEven : Even M.realDim)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (evenCROSSHeatTrace M) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  evenCROSS_heatTrace_no_rat_ade_of_baseHeat baseHeatInt_no_rat_ade baseHeatHalf_no_rat_ade M hEven P hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on every even sphere `S^{2r}` (`r ≥ 1`). -/
theorem evenSphere_heatTrace_no_rat_ade {d : ℕ} (hd : 1 ≤ d)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (evenSphereHeatTrace d) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 := by
  have hM := evenCROSS_heatTrace_no_rat_ade (.sphere (2 * d) (by omega)) ⟨d, by simp [SimplyConnectedCROSS.realDim]; ring⟩ P
  have heq : evenCROSSHeatTrace (.sphere (2 * d) (by omega)) = evenSphereHeatTrace d := by
    funext t; simp [evenCROSSHeatTrace]
  rw [heq] at hM
  exact hM hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on every complex projective space `ℂℙⁿ` (`n ≥ 1`). -/
theorem cpn_heatTrace_no_rat_ade {n : ℕ} (hn : 1 ≤ n)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (cpnHeatTrace n) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  evenCROSS_heatTrace_no_rat_ade (.cp n hn) ⟨n, by simp [SimplyConnectedCROSS.realDim]; ring⟩ P hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on every quaternionic projective space `ℍℙⁿ` (`n ≥ 1`). -/
theorem hpn_heatTrace_no_rat_ade {n : ℕ} (hn : 1 ≤ n)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (hpnHeatTrace n) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  evenCROSS_heatTrace_no_rat_ade (.hp n hn) ⟨2 * n, by simp [SimplyConnectedCROSS.realDim]; ring⟩ P hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on the Cayley octonionic projective plane `𝕆ℙ²`. -/
theorem op2_heatTrace_no_rat_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val op2HeatTrace t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  evenCROSS_heatTrace_no_rat_ade .op2 ⟨8, by simp [SimplyConnectedCROSS.realDim]⟩ P hP

end UnconditionalBaseHeatDTrans

end HeatTraceClosure

end
end PakPrimes.RankOneSymmetricParity
