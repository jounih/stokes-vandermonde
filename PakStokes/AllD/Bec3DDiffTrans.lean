module

public import PakStokes.AllD.Bec3DAnalytic
public import PakStokes.AllD.SquareQuotientsAndDivisors
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.SumTwoSquares
import all PakStokes.AllD.Bec3DAnalytic
import all PakStokes.AllD.SquareQuotientsAndDivisors
import all PakStokes.AllD.PowerPartitions
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

/-! # Wave 11 (Module 3): 100% Unconditional Differential Transcendence & Joint Independence of Physical 3D Ideal Bose–Einstein & Fermi–Dirac Gases (and Joint 1D + 3D Quantum Gases)

Establishes **100% unconditionally from Mathlib** (zero placeholders, standard axioms only):

1. **Formal 3D Ideal Bose–Einstein & Fermi–Dirac Partition Functions (`ℂ[[q]]`):**
   - `bec3DSeries` (`Z_BEC^{(3)}(q) = ∏_{N ≥ 1} (1 - q^N)^{-r_3(N)} = ∏_{n ∈ ℤ³ \ {0}} (1 - q^{|n|²})^{-1}`),
     dilations `bec3DDilated a`, integer powers `bec3DZPow k`, and logarithmic derivative
     `logDerivBec3D` (`F_BEC^{(3)}(q) = q (d/dq) log Z_BEC^{(3)}(q) = ∑_{k, N ≥ 1} N r_3(N) q^{k N}`).
   - `fermi3DSeries` (`Z_FD^{(3)}(q) = Z_BEC^{(3)}(q) / Z_BEC^{(3)}(q²) = ∏_{N ≥ 1} (1 + q^N)^{r_3(N)}`),
     with exact formal Euler-product identity `fermi3DSeries_eq_eulerProd` and dilations `fermi3DDilated a`.
   - Exact formal logarithmic derivative identities `X_mul_deriv_bec3DDilated`, `X_mul_deriv_bec3DSeries`,
     and `X_mul_deriv_bec3DZPow`.
2. **`bec3DProfile : SqRayProfile logDerivBec3D`:**
   - Discharges the unified `d = 2` zero-tilt wave-profile interface completely from
     `bec3D_analytic_identity` (`Bec3DAnalytic.lean`), with `scalePow = 4`, `polarHigh = 5`,
     and exact wave multiplicity `bec3DWaveMult N = N · ∑_{d ∣ N} r_3(d) / d^{3/2} ≥ 6 N > 0`.
3. **100% Unconditional 3D Ideal Bose–Einstein & Fermi–Dirac Crown Jewels:**
   - `logDerivBec3D_non_ade`, `logDerivBec3D_dilations_diff_indep`,
   - **`bec3D_non_ade`** (`Z_BEC^{(3)}(q)` is differentially transcendental over `ℂ(q)`),
   - **`bec3D_zpow_non_ade`** (`Z_BEC^{(3)}(q)^k` for EVERY `k ∈ ℤ \ {0}`),
   - **`bec3D_dilations_diff_indep`** (ALL distinct dilations `{Z_BEC^{(3)}(q^{a_i})}` are jointly
     differentially independent over `ℂ(q)`),
   - **`fermi3D_non_ade`** (`Z_FD^{(3)}(q)` is non-ADE over `ℂ(q)`),
   - **`fermi3D_dilations_diff_indep`** (ALL distinct dilations `{Z_FD^{(3)}(q^{a_i})}` are jointly
     differentially independent over `ℂ(q)`),
   - **`bec3D_fermi3D_joint_diff_indep`** (at a single temperature variable, 3D Bose `Z_BEC^{(3)}(q)`
     and 3D Fermi `Z_FD^{(3)}(q)` are **jointly differentially independent over `ℂ(q)`**!),
   - **`bec3D_bose_fermi_quotient_rank`** (arbitrary full-row-rank integer exponent matrix on
     distinct 3D Bose dilations, yielding mixed Bose–Fermi differential transcendence degree),
   - `bec3D_forest_quotients_diff_indep`.
4. **100% Unconditional Joint Differential Independence of 1D and 3D Ideal Quantum Gases:**
   - Using Dirichlet's theorem on primes in arithmetic progressions (`7 mod 8` where `r_3(p) = 0`,
     and `1 mod 4` where Fermat's two-square theorem gives `r_3(p) ≥ 1`), proves the exact
     `(2J) × (2J)` prime-block determinant non-vanishing on `d = 2` ray `sqRay0`, giving:
     - `logDeriv_bec1D_bec3D_dilations_diff_indep`,
     - `bec1D_bec3D_dilations_diff_indep`,
     - **`bec1D_bec3D_joint_diff_indep`** (`(Z_BEC^{(1)}(q), Z_BEC^{(3)}(q))` jointly differentially
       independent over `ℂ(q)`),
     - **`quantumGases_1D_3D_bose_fermi_joint_diff_indep`** (ALL FOUR physical ideal quantum gas
       partition functions `(Z_BEC^{(1)}(q), Z_FD^{(1)}(q), Z_BEC^{(3)}(q), Z_FD^{(3)}(q))`
       are **jointly differentially independent over `ℂ(q)`**!). -/

public section
namespace CubicTheta.AllD
open Complex Filter Set PowerSeries MvPolynomial Matrix Flow MeasureTheory
open scoped Topology Matrix
noncomputable section

/-! ### 1. Formal 3D Bose–Einstein & Fermi–Dirac Partition Series and Exact Log-Derivative Identities -/

/-- Weighted divisor sum `∑_{d ∣ N} d · r_3(d)` for `N ≥ 1` (coefficient of `q^N` in `F_BEC^{(3)}(q)`). -/
def bec3DDivSum (N : ℕ) : ℕ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (· ∣ N), d * r3Count d

/-- Formal logarithmic derivative `F_BEC^{(3)}(q) = q (d/dq) log Z_BEC^{(3)}(q) = ∑_{N ≥ 1} (∑_{d ∣ N} d r_3(d)) q^N`. -/
def logDerivBec3D : PowerSeries ℂ :=
  PowerSeries.mk fun N ↦ if N = 0 then 0 else (bec3DDivSum N : ℂ)

/-- Formal dilated logarithmic derivative `F_BEC^{(3)}(q^a)`. -/
def logDerivBec3DDilated (a : ℕ) : PowerSeries ℂ :=
  seriesDilated logDerivBec3D a

/-- Finite truncated Euler product `∏_{d=1}^M (1 - q^{a d})^{-r_3(d)}` in `ℂ[[q]]`. -/
def bec3DTrunc (a M : ℕ) : PowerSeries ℂ :=
  ∏ d ∈ Finset.Icc 1 M, (geomSeriesPow (a * d)) ^ (r3Count d)

/-- Formal dilated 3D ideal Bose–Einstein partition function
`Z_BEC^{(3)}(q^a) = ∏_{N ≥ 1} (1 - q^{a N})^{-r_3(N)}`. -/
def bec3DDilated (a : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun N ↦ PowerSeries.coeff N (bec3DTrunc a N)

/-- Physical 3D ideal Bose–Einstein condensate grand partition function
`Z_BEC^{(3)}(q) = ∏_{n ∈ ℤ³ \ {0}} (1 - q^{|n|²})^{-1} = ∏_{N ≥ 1} (1 - q^N)^{-r_3(N)}`. -/
def bec3DSeries : PowerSeries ℂ := bec3DDilated 1

theorem constantCoeff_bec3DDilated (a : ℕ) :
    PowerSeries.constantCoeff (bec3DDilated a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, bec3DDilated, PowerSeries.coeff_mk, bec3DTrunc]
  simp

theorem isUnit_bec3DDilated (a : ℕ) : IsUnit (bec3DDilated a) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_bec3DDilated]; exact isUnit_one)

theorem bec3DDilated_ne_zero (a : ℕ) : bec3DDilated a ≠ 0 :=
  (isUnit_bec3DDilated a).ne_zero

theorem bec3DSeries_ne_zero : bec3DSeries ≠ 0 :=
  bec3DDilated_ne_zero 1

/-- Exact integer power `Z_BEC^{(3)}(q)^k ∈ ℂ[[q]]` for EVERY `k : ℤ`. -/
def bec3DZPow (k : ℤ) : PowerSeries ℂ :=
  (((isUnit_bec3DDilated 1).unit ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)

theorem bec3DZPow_ne_zero (k : ℤ) : bec3DZPow k ≠ 0 :=
  Units.ne_zero _

theorem bec3DZPow_natCast (k : ℕ) : bec3DZPow (k : ℤ) = bec3DSeries ^ k := by
  simp [bec3DZPow, bec3DSeries]

/-- Formal unit for the dilated 3D ideal Fermi–Dirac gas `Z_FD^{(3)}(q^a) = Z_BEC^{(3)}(q^a) / Z_BEC^{(3)}(q^{2a})`. -/
def fermi3DUnit (a : ℕ+) : (PowerSeries ℂ)ˣ :=
  (isUnit_bec3DDilated a.val).unit * (isUnit_bec3DDilated (2 * a.val)).unit⁻¹

/-- Formal dilated 3D ideal Fermi–Dirac gas partition function
`Z_FD^{(3)}(q^a) = ∏_{N ≥ 1} (1 + q^{a N})^{r_3(N)} = Z_BEC^{(3)}(q^a) / Z_BEC^{(3)}(q^{2a})`. -/
def fermi3DDilated (a : ℕ+) : PowerSeries ℂ := (fermi3DUnit a : PowerSeries ℂ)

/-- Physical 3D ideal Fermi–Dirac gas partition function
`Z_FD^{(3)}(q) = ∏_{n ∈ ℤ³ \ {0}} (1 + q^{|n|²}) = Z_BEC^{(3)}(q) / Z_BEC^{(3)}(q²)`. -/
def fermi3DSeries : PowerSeries ℂ := fermi3DDilated 1

/-- Physical 1D ideal Bose–Einstein condensate partition function
`Z_BEC^{(1)}(q) = ∏_{n ∈ ℤ \ {0}} (1 - q^{n²})^{-1} = P_2(q)²`. -/
def bec1DGas : PowerSeries ℂ := powerPartSeries 2 ^ 2

private lemma coeff_geomSeriesPow_pow_mul_eq {m N : ℕ} (hm : N < m) (r : ℕ) (S : PowerSeries ℂ) :
    PowerSeries.coeff N (S * (geomSeriesPow m) ^ r) = PowerSeries.coeff N S := by
  induction r generalizing S with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, coeff_geomSeriesPow_mul_eq hm, ih]

private lemma coeff_bec3DTrunc_stable {a M N : ℕ} (ha : 1 ≤ a) (hMN : N ≤ M) :
    PowerSeries.coeff N (bec3DTrunc a M) = PowerSeries.coeff N (bec3DTrunc a N) := by
  induction M, hMN using Nat.le_induction with
  | base => rfl
  | succ k hNk ih =>
    unfold bec3DTrunc
    rw [show Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp), mul_comm]
    have hlt : N < a * (k + 1) := by nlinarith
    rw [coeff_geomSeriesPow_pow_mul_eq hlt]
    exact ih

private lemma X_mul_deriv_geomSeriesPow_pow {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) ((geomSeriesPow m) ^ r) =
      (PowerSeries.C ((r * m : ℕ) : ℂ) * PowerSeries.X ^ m * geomSeriesPow m) *
        (geomSeriesPow m) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 := X_mul_deriv_geomSeriesPow hm
    have hcast : (((r + 1) * m : ℕ) : ℂ) = ((r * m : ℕ) : ℂ) + (m : ℂ) := by
      push_cast; ring
    rw [hcast, map_add]
    linear_combination (geomSeriesPow m) ^ r * h1 + geomSeriesPow m * ih

/-- **Exact Formal Logarithmic Derivative of `Z_BEC^{(3)}(q^a)` (`a ≥ 1`)**:
`q · (d/dq) Z_BEC^{(3)}(q^a) = a · F_BEC^{(3)}(q^a) · Z_BEC^{(3)}(q^a)`. -/
theorem X_mul_deriv_bec3DDilated {a : ℕ} (ha : 1 ≤ a) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (bec3DDilated a) =
      (PowerSeries.C (a : ℂ) * logDerivBec3DDilated a) * bec3DDilated a := by
  ext N
  let M := N + 1
  have htrunc := X_mul_deriv_finset_prod (Finset.Icc 1 M)
    (fun d ↦ (geomSeriesPow (a * d)) ^ (r3Count d))
    (fun d ↦ PowerSeries.C ((r3Count d * (a * d) : ℕ) : ℂ) * PowerSeries.X ^ (a * d) *
      geomSeriesPow (a * d))
    (fun d hd ↦ by
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      exact X_mul_deriv_geomSeriesPow_pow (Nat.mul_pos ha hd1) (r3Count d))
  have hcoeff_eq := congrArg (PowerSeries.coeff N) htrunc
  have hlhs : PowerSeries.coeff N (PowerSeries.X * PowerSeries.derivative (R := ℂ) (bec3DDilated a)) =
      PowerSeries.coeff N (PowerSeries.X * PowerSeries.derivative (R := ℂ) (bec3DTrunc a M)) := by
    cases N with
    | zero => simp
    | succ N' =>
      rw [← pow_one (PowerSeries.X : PowerSeries ℂ), PowerSeries.coeff_X_pow_mul',
          PowerSeries.coeff_X_pow_mul']
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, PowerSeries.coeff_derivative]
      congr 1
      rw [bec3DDilated, PowerSeries.coeff_mk]
      exact (coeff_bec3DTrunc_stable ha (by omega : N' + 1 ≤ M)).symm
  have hsum_coeff (k : ℕ) (hk : k ≤ N) :
      PowerSeries.coeff k (∑ d ∈ Finset.Icc 1 M,
        PowerSeries.C ((r3Count d * (a * d) : ℕ) : ℂ) * PowerSeries.X ^ (a * d) *
          geomSeriesPow (a * d)) =
      PowerSeries.coeff k (PowerSeries.C (a : ℂ) * logDerivBec3DDilated a) := by
    rw [map_sum, PowerSeries.coeff_C_mul, logDerivBec3DDilated, seriesDilated, PowerSeries.coeff_mk]
    have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 M) :
        PowerSeries.coeff k (PowerSeries.C ((r3Count d * (a * d) : ℕ) : ℂ) * PowerSeries.X ^ (a * d) *
          geomSeriesPow (a * d)) =
        if k = 0 then 0 else if a * d ∣ k then ((r3Count d * (a * d) : ℕ) : ℂ) else 0 := by
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hm : 1 ≤ a * d := Nat.mul_pos ha hd1
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      by_cases hk0 : k = 0
      · subst hk0; simp [show ¬ a * d ≤ 0 by omega]
      · simp only [hk0, ↓reduceIte]
        by_cases hle : a * d ≤ k
        · simp only [hle, ↓reduceIte, geomSeriesPow, PowerSeries.coeff_mk]
          have hiff : a * d ∣ k - a * d ↔ a * d ∣ k := by
            constructor
            · intro h; rw [← Nat.sub_add_cancel hle]; exact dvd_add h (dvd_refl _)
            · intro h; exact (Nat.dvd_sub_iff_left hle (dvd_refl _)).mpr h
          by_cases hdvd : a * d ∣ k
          · simp [hdvd, hiff.mpr hdvd]
          · simp [hdvd, mt hiff.mp hdvd]
        · have hnd : ¬ a * d ∣ k := fun h ↦ hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h)
          simp [hle, hnd]
    rw [Finset.sum_congr rfl hterm]
    by_cases hk0 : k = 0
    · subst hk0; simp [logDerivBec3D]
    · simp only [hk0, ↓reduceIte]
      by_cases hak : a ∣ k
      · have hka_pos : 0 < k / a := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hak) ha
        simp only [hak, ↓reduceIte, logDerivBec3D, PowerSeries.coeff_mk, hka_pos.ne', bec3DDivSum,
          Nat.cast_sum, Finset.mul_sum]
        rw [← Finset.sum_filter]
        have hfilt : (Finset.Icc 1 M).filter (fun d ↦ a * d ∣ k) =
            (Finset.Icc 1 (k / a)).filter (· ∣ k / a) := by
          ext d; simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨hd1, _⟩, hdvd⟩
            have hdvd' : d ∣ k / a := by
              obtain ⟨q, hq⟩ := hdvd
              refine ⟨q, Nat.eq_of_mul_eq_mul_left ha ?_⟩
              rw [Nat.mul_div_cancel' hak, hq]; ring
            exact ⟨⟨hd1, Nat.le_of_dvd hka_pos hdvd'⟩, hdvd'⟩
          · rintro ⟨⟨hd1, hdle⟩, hdvd'⟩
            have hleM : d ≤ M := hdle.trans ((Nat.div_le_self k a).trans (by omega))
            have hdvd : a * d ∣ k := by
              obtain ⟨q, hq⟩ := hdvd'
              refine ⟨q, ?_⟩
              rw [← Nat.mul_div_cancel' hak, hq]; ring
            exact ⟨⟨hd1, hleM⟩, hdvd⟩
        rw [hfilt]
        apply Finset.sum_congr rfl; intro d _
        push_cast; ring
      · simp only [hak, ↓reduceIte, mul_zero]
        apply Finset.sum_eq_zero; intro d _
        have hnd : ¬ a * d ∣ k := fun h ↦ hak ((dvd_mul_right a d).trans h)
        simp [hnd]
  have hrhs : PowerSeries.coeff N ((∑ d ∈ Finset.Icc 1 M,
        PowerSeries.C ((r3Count d * (a * d) : ℕ) : ℂ) * PowerSeries.X ^ (a * d) *
          geomSeriesPow (a * d)) * bec3DTrunc a M) =
      PowerSeries.coeff N ((PowerSeries.C (a : ℂ) * logDerivBec3DDilated a) * bec3DDilated a) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    have hsum : i + j = N := Finset.mem_antidiagonal.mp hij
    rw [hsum_coeff i (by omega), bec3DDilated, PowerSeries.coeff_mk,
        coeff_bec3DTrunc_stable ha (by omega : j ≤ M)]
  rw [hlhs]
  change PowerSeries.coeff N (PowerSeries.X * PowerSeries.derivative (R := ℂ)
      (∏ d ∈ Finset.Icc 1 M, (geomSeriesPow (a * d)) ^ (r3Count d))) = _
  rw [hcoeff_eq]
  exact hrhs

theorem X_mul_deriv_bec3DSeries :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) bec3DSeries =
      logDerivBec3D * bec3DSeries := by
  simpa [bec3DSeries, logDerivBec3DDilated, seriesDilated_one] using X_mul_deriv_bec3DDilated le_rfl

theorem X_mul_deriv_bec3DZPow (k : ℤ) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (bec3DZPow k) =
      (PowerSeries.C (k : ℂ) * logDerivBec3D) * bec3DZPow k :=
  X_mul_deriv_unit_zpow (isUnit_bec3DDilated 1).unit logDerivBec3D X_mul_deriv_bec3DSeries k

/-- **Exact Euler Product Identity for the Dilated 3D Ideal Fermi–Dirac Gas**:
`[q^N] Z_FD^{(3)}(q^a) = [q^N] ∏_{d=1}^N (1 + q^{a d})^{r_3(d)}` for EVERY `a : ℕ+`, `N : ℕ`! -/
theorem fermi3DDilated_eq_eulerProd (a : ℕ+) (N : ℕ) :
    PowerSeries.coeff N (fermi3DDilated a) =
      PowerSeries.coeff N (∏ d ∈ Finset.Icc 1 N,
        (1 + (PowerSeries.X : PowerSeries ℂ) ^ (a.val * d)) ^ (r3Count d)) := by
  let P_N : PowerSeries ℂ :=
    ∏ d ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : PowerSeries ℂ) ^ (a.val * d)) ^ (r3Count d)
  have hmul_trunc : bec3DTrunc a.val N = P_N * bec3DTrunc (2 * a.val) N := by
    unfold bec3DTrunc P_N
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hm : 1 ≤ a.val * d := Nat.mul_pos a.pos hd1
    have h2 : geomSeriesPow (a.val * d) =
        (1 + (PowerSeries.X : PowerSeries ℂ) ^ (a.val * d)) * geomSeriesPow (2 * a.val * d) := by
      have hg := geomSeriesPow_eq_finset_sum_mul hm (by decide : 1 ≤ 2)
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zero_mul, pow_zero,
        one_mul, mul_assoc] using hg
    rw [h2, mul_pow]
  have hmul_series : ∀ M ≤ N,
      PowerSeries.coeff M (fermi3DDilated a * bec3DDilated (2 * a.val)) =
        PowerSeries.coeff M (P_N * bec3DDilated (2 * a.val)) := by
    intro M hMN
    have hunit : fermi3DDilated a * bec3DDilated (2 * a.val) = bec3DDilated a.val := by
      change ((fermi3DUnit a : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        (((isUnit_bec3DDilated (2 * a.val)).unit : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = _
      rw [← Units.val_mul, fermi3DUnit, mul_assoc, inv_mul_cancel, mul_one]
      exact (isUnit_bec3DDilated a.val).unit_spec
    rw [hunit, bec3DDilated, PowerSeries.coeff_mk, ← coeff_bec3DTrunc_stable a.pos hMN,
        hmul_trunc, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl; rintro ⟨i, j⟩ hij
    have hsum : i + j = M := Finset.mem_antidiagonal.mp hij
    rw [bec3DDilated, PowerSeries.coeff_mk,
        coeff_bec3DTrunc_stable (Nat.mul_pos (by decide) a.pos) (by omega : j ≤ N)]
  have hdiff : ∀ M ≤ N, PowerSeries.coeff M (fermi3DDilated a) = PowerSeries.coeff M P_N := by
    intro M
    induction M using Nat.strong_induction_on with
    | ind M ih =>
      intro hMN
      have heq := hmul_series M hMN
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul] at heq
      have h0_mem : (M, 0) ∈ Finset.antidiagonal M := Finset.mem_antidiagonal.mpr (add_zero M)
      rw [← Finset.add_sum_erase _ _ h0_mem, ← Finset.add_sum_erase _ _ h0_mem] at heq
      have hrest :
          (∑ x ∈ (Finset.antidiagonal M).erase (M, 0),
              PowerSeries.coeff x.1 (fermi3DDilated a) *
                PowerSeries.coeff x.2 (bec3DDilated (2 * a.val))) =
          ∑ x ∈ (Finset.antidiagonal M).erase (M, 0),
              PowerSeries.coeff x.1 P_N *
                PowerSeries.coeff x.2 (bec3DDilated (2 * a.val)) := by
        apply Finset.sum_congr rfl; rintro ⟨i, j⟩ hx
        have hne : (i, j) ≠ (M, 0) := (Finset.mem_erase.mp hx).1
        have hsum : i + j = M := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
        have hilt : i < M := by
          by_contra hge; apply hne; exact Prod.ext (by omega) (by omega)
        rw [ih i hilt (by omega)]
      have hc0 : PowerSeries.coeff 0 (bec3DDilated (2 * a.val)) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_bec3DDilated]
      rw [hrest, hc0, mul_one, mul_one] at heq
      exact add_right_cancel heq
  exact hdiff N le_rfl

/-- **Exact Euler Product Identity for the Physical 3D Ideal Fermi–Dirac Gas**:
`[q^N] Z_FD^{(3)}(q) = [q^N] ∏_{d=1}^N (1 + q^d)^{r_3(d)}` for EVERY `N : ℕ`! -/
theorem fermi3DSeries_eq_eulerProd (N : ℕ) :
    PowerSeries.coeff N fermi3DSeries =
      PowerSeries.coeff N (∏ d ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : PowerSeries ℂ) ^ d) ^ (r3Count d)) := by
  simpa only [fermi3DSeries, PNat.one_coe, one_mul] using fermi3DDilated_eq_eulerProd 1 N

/-! ### 2. Unconditional `SqRayProfile` for the Physical 3D Bose–Einstein Condensate -/

theorem r3Count_one : r3Count 1 = 6 := by decide

theorem r3Count_le (N : ℕ) : r3Count N ≤ (2 * N + 1) ^ 3 := by
  unfold r3Count
  calc _ ≤ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
              (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ))).card :=
        Finset.card_le_card (Finset.filter_subset ..)
    _ = ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card) ^ 3 := by
        simp only [Finset.card_product]; ring
    _ = (2 * N + 1) ^ 3 := by
        congr 1; rw [Int.card_Icc]; omega

/-- Exact 3D BEC Stokes wave multiplicity `c_3(N) = N · ∑_{d ∣ N} r_3(d) / d^{3/2}`! -/
def bec3DWaveMult (N : ℕ) : ℝ :=
  (N : ℝ) * ∑ d ∈ (Finset.Icc 1 N).filter (· ∣ N), (r3Count d : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))

theorem bec3DWaveMult_nonneg (N : ℕ) : 0 ≤ bec3DWaveMult N :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ ↦ by positivity)

theorem bec3DWaveMult_ge_six_mul {N : ℕ} (hN : 1 ≤ N) : 6 * (N : ℝ) ≤ bec3DWaveMult N := by
  unfold bec3DWaveMult
  have h1mem : 1 ∈ (Finset.Icc 1 N).filter (· ∣ N) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, one_dvd N⟩
  have hle : (r3Count 1 : ℝ) / (((1 : ℕ) : ℝ) * Real.sqrt ((1 : ℕ) : ℝ)) ≤
      ∑ d ∈ (Finset.Icc 1 N).filter (· ∣ N), (r3Count d : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ)) :=
    Finset.single_le_sum (f := fun d : ℕ ↦ (r3Count d : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ)))
      (fun _ _ ↦ by positivity) h1mem
  rw [r3Count_one, Nat.cast_one, Real.sqrt_one, mul_one, div_one, Nat.cast_ofNat] at hle
  calc 6 * (N : ℝ) = (N : ℝ) * 6 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)

theorem bec3DWaveMult_prime {p : ℕ} (hp : p.Prime) :
    bec3DWaveMult p = 6 * (p : ℝ) + (r3Count p : ℝ) / Real.sqrt (p : ℝ) := by
  unfold bec3DWaveMult
  have hfilt : (Finset.Icc 1 p).filter (· ∣ p) = {1, p} := by
    ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hdvd⟩; exact (Nat.dvd_prime hp).mp hdvd
    · rintro (rfl | hd)
      · exact ⟨⟨le_rfl, hp.one_lt.le⟩, one_dvd p⟩
      · rw [hd]; exact ⟨⟨hp.one_lt.le, le_rfl⟩, dvd_refl p⟩
  rw [hfilt, Finset.sum_pair hp.ne_one.symm, r3Count_one, Nat.cast_one, Real.sqrt_one, mul_one,
      div_one, Nat.cast_ofNat]
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hs0 : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos)).ne'
  field_simp [hp0, hs0]

theorem bec3DWaveMult_le (N : ℕ) : bec3DWaveMult N ≤ 27 * (N : ℝ) ^ 5 := by
  by_cases hN0 : N = 0
  · subst hN0; simp [bec3DWaveMult]
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
    unfold bec3DWaveMult
    have hsum_le : (∑ d ∈ (Finset.Icc 1 N).filter (· ∣ N),
        (r3Count d : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))) ≤ 27 * (N : ℝ) ^ 4 := by
      calc (∑ d ∈ (Finset.Icc 1 N).filter (· ∣ N),
              (r3Count d : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ)))
          ≤ ∑ d ∈ (Finset.Icc 1 N).filter (· ∣ N), 27 * (N : ℝ) ^ 3 := by
            apply Finset.sum_le_sum; intro d hd
            have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
            have hdN : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
            have hden : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt (d : ℝ) := by
              have hsq : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by simpa using Real.sqrt_le_sqrt hd1
              nlinarith
            have hr : (r3Count d : ℝ) ≤ (2 * (d : ℝ) + 1) ^ 3 := by exact_mod_cast r3Count_le d
            have h2d : 2 * (d : ℝ) + 1 ≤ 3 * (N : ℝ) := by linarith
            calc (r3Count d : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))
                ≤ (r3Count d : ℝ) / 1 := div_le_div_of_nonneg_left (Nat.cast_nonneg _) zero_lt_one hden
              _ = (r3Count d : ℝ) := div_one _
              _ ≤ (2 * (d : ℝ) + 1) ^ 3 := hr
              _ ≤ (3 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h2d 3
              _ = 27 * (N : ℝ) ^ 3 := by ring
        _ ≤ ∑ _d ∈ Finset.Icc 1 N, 27 * (N : ℝ) ^ 3 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) fun _ _ _ ↦ by positivity
        _ = 27 * (N : ℝ) ^ 4 := by simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    calc (N : ℝ) * _ ≤ (N : ℝ) * (27 * (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg _)
      _ = 27 * (N : ℝ) ^ 5 := by ring

private lemma psValue_logDerivBec3D_eq {X : ℝ} (hX : 0 < X) :
    psValue logDerivBec3D (qRayD 3 X) =
      ∑' N : ℕ+, (((r3Count N.val : ℝ) * (N.val : ℝ) /
        (Real.exp ((N.val : ℝ) / X ^ 2) - 1) : ℝ) : ℂ) := by
  let t : ℝ := 1 / X ^ 2
  have ht : 0 < t := by positivity
  let term (kd : ℕ+ × ℕ+) : ℂ := ((r3Count kd.2.val : ℂ) * (kd.2.val : ℂ)) * (qRayD 3 X) ^ (kd.1.val * kd.2.val)
  have hq_norm : ‖qRayD 3 X‖ = Real.exp (-t) := by
    unfold qRayD; dsimp only [t]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsum_prod : Summable (fun kd : ℕ+ × ℕ+ ↦ ‖term kd‖) := by
    have hsum_norm : Summable (fun kd : ℕ+ × ℕ+ ↦
        (r3Count kd.2.val : ℝ) * (kd.2.val : ℝ) * Real.exp (-t * ((kd.1.val : ℝ) * (kd.2.val : ℝ)))) := by
      have hdom : Summable (fun kd : ℕ+ × ℕ+ ↦
          27 * (Real.exp (-(t / 2) * (kd.1.val : ℝ)) *
            ((kd.2.val : ℝ) ^ 4 * Real.exp (-(t / 2) * (kd.2.val : ℝ))))) := by
        have hs1 : Summable (fun k : ℕ+ ↦ Real.exp (-(t / 2) * (k.val : ℝ))) := by
          simpa only [Function.comp_def, pow_zero, one_mul] using
            (Real.summable_pow_mul_exp_neg_nat_mul 0 (half_pos ht)).comp_injective PNat.coe_injective
        have hs2 : Summable (fun d : ℕ+ ↦ (d.val : ℝ) ^ 4 * Real.exp (-(t / 2) * (d.val : ℝ))) :=
          (Real.summable_pow_mul_exp_neg_nat_mul 4 (half_pos ht)).comp_injective PNat.coe_injective
        exact (hs1.mul_of_nonneg hs2 (fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ by positivity)).mul_left 27
      refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun kd ↦ ?_) hdom
      have hk1 : (1 : ℝ) ≤ (kd.1.val : ℝ) := by exact_mod_cast kd.1.pos
      have hd1 : (1 : ℝ) ≤ (kd.2.val : ℝ) := by exact_mod_cast kd.2.pos
      have hr : (r3Count kd.2.val : ℝ) ≤ 27 * (kd.2.val : ℝ) ^ 3 := by
        have h1 : (r3Count kd.2.val : ℝ) ≤ (2 * (kd.2.val : ℝ) + 1) ^ 3 := by exact_mod_cast r3Count_le kd.2.val
        have h2 : 2 * (kd.2.val : ℝ) + 1 ≤ 3 * (kd.2.val : ℝ) := by linarith
        exact h1.trans ((pow_le_pow_left₀ (by positivity) h2 3).trans_eq (by ring))
      have hexp : Real.exp (-t * ((kd.1.val : ℝ) * (kd.2.val : ℝ))) ≤
          Real.exp (-(t / 2) * (kd.1.val : ℝ)) * Real.exp (-(t / 2) * (kd.2.val : ℝ)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
        have h12 : (kd.1.val : ℝ) + (kd.2.val : ℝ) ≤ 2 * ((kd.1.val : ℝ) * (kd.2.val : ℝ)) := by nlinarith
        nlinarith
      calc (r3Count kd.2.val : ℝ) * (kd.2.val : ℝ) * Real.exp (-t * ((kd.1.val : ℝ) * (kd.2.val : ℝ)))
          ≤ (27 * (kd.2.val : ℝ) ^ 3) * (kd.2.val : ℝ) *
              (Real.exp (-(t / 2) * (kd.1.val : ℝ)) * Real.exp (-(t / 2) * (kd.2.val : ℝ))) := by gcongr
        _ = _ := by ring
    refine hsum_norm.congr fun kd ↦ ?_
    simp only [term, norm_mul, norm_pow, Complex.norm_natCast, hq_norm, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have h_eq1 : psValue logDerivBec3D (qRayD 3 X) = ∑' kd : ℕ+ × ℕ+, term kd := by
    let g (kd : ℕ+ × ℕ+) : ℕ := kd.1.val * kd.2.val
    rw [(hsum_prod.of_norm.hasSum.tsum_fiberwise g).tsum_eq.symm]
    unfold psValue
    apply tsum_congr; intro N
    by_cases hN0 : N = 0
    · subst hN0
      have : IsEmpty (g ⁻¹' {0}) := ⟨fun kd ↦ mul_ne_zero kd.val.1.pos.ne' kd.val.2.pos.ne' kd.property⟩
      simp [psTerm, logDerivBec3D]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      let S := (Finset.Icc 1 N).filter (· ∣ N)
      let e : g ⁻¹' {N} ≃ S :=
        { toFun := fun kd ↦ ⟨kd.val.2.val, Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨kd.val.2.pos,
              Nat.le_of_dvd hNpos ⟨kd.val.1.val, by rw [mul_comm]; exact kd.property.symm⟩⟩,
             ⟨kd.val.1.val, by rw [mul_comm]; exact kd.property.symm⟩⟩⟩
          invFun := fun d ↦
            have hd_pos : 0 < d.val := (Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1).1
            have hdvd : d.val ∣ N := (Finset.mem_filter.mp d.property).2
            have hk_pos : 0 < N / d.val := Nat.div_pos (Nat.le_of_dvd hNpos hdvd) hd_pos
            ⟨(⟨N / d.val, hk_pos⟩, ⟨d.val, hd_pos⟩), Nat.div_mul_cancel hdvd⟩
          left_inv := fun ⟨⟨k, d⟩, hkd⟩ ↦ Subtype.ext (Prod.ext (PNat.eq (by
            change N / d.val = k.val
            have h1 : k.val * d.val = N := hkd
            rw [← h1]; exact Nat.mul_div_cancel k.val d.pos)) rfl)
          right_inv := fun ⟨_, _⟩ ↦ rfl }
      let _ : Fintype (g ⁻¹' {N}) := Fintype.ofEquiv S e.symm
      rw [tsum_fintype, Fintype.sum_equiv e (fun kd ↦ term kd.val)
          (fun d ↦ ((r3Count d.val : ℂ) * (d.val : ℂ)) * (qRayD 3 X) ^ N)
          (fun kd ↦ by simp only [term, e, Equiv.coe_fn_mk, show kd.val.1.val * kd.val.2.val = N from kd.property])]
      rw [Finset.univ_eq_attach, Finset.sum_attach S (fun d ↦ ((r3Count d : ℂ) * (d : ℂ)) * (qRayD 3 X) ^ N),
          ← Finset.sum_mul]
      simp only [psTerm, logDerivBec3D, PowerSeries.coeff_mk, hN0, ↓reduceIte, bec3DDivSum, Nat.cast_sum,
        Nat.cast_mul, S]
      congr 1; apply Finset.sum_congr rfl; intro d _; ring
  have hsum_swap : Summable (fun dk : ℕ+ × ℕ+ ↦ term (dk.2, dk.1)) :=
    hsum_prod.of_norm.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
  have h_eq2 : (∑' kd : ℕ+ × ℕ+, term kd) = ∑' d : ℕ+, ∑' k : ℕ+, term (k, d) := by
    rw [← (Equiv.prodComm ℕ+ ℕ+).tsum_eq term]
    exact hsum_swap.tsum_prod' fun d ↦ hsum_prod.of_norm.comp_injective fun k₁ k₂ h ↦ by injection h
  rw [h_eq1, h_eq2]
  apply tsum_congr; intro d
  have hq_d : ‖(qRayD 3 X) ^ d.val‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (qRayD_disk hX) d.pos.ne'
  have hterm_d : (∑' k : ℕ+, term (k, d)) =
      ((r3Count d.val : ℂ) * (d.val : ℂ)) * ∑' k : ℕ+, ((qRayD 3 X) ^ d.val) ^ k.val := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro k; simp [term, ← pow_mul, mul_comm]
  rw [hterm_d, tsum_pnat_eq_tsum_succ (f := fun k : ℕ ↦ ((qRayD 3 X) ^ d.val) ^ k)]
  simp_rw [pow_succ' ((qRayD 3 X) ^ d.val)]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq_d]
  have hexp_d : (qRayD 3 X) ^ d.val = (((Real.exp ((d.val : ℝ) / X ^ 2))⁻¹ : ℝ) : ℂ) := by
    simp only [qRayD, ← Complex.ofReal_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 2; push_cast; ring
  rw [hexp_d]
  have hepos : 0 < Real.exp ((d.val : ℝ) / X ^ 2) := Real.exp_pos _
  have hegt1 : 1 < Real.exp ((d.val : ℝ) / X ^ 2) :=
    Real.one_lt_exp_iff.mpr (div_pos (Nat.cast_pos.mpr d.pos) (pow_pos hX 2))
  have hE0 : ((Real.exp ((d.val : ℝ) / X ^ 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hepos.ne'
  have hE1 : ((Real.exp ((d.val : ℝ) / X ^ 2) : ℝ) : ℂ) - 1 ≠ 0 := by
    intro h; have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at hre; linarith
  have hden : (1 : ℂ) - (((Real.exp ((d.val : ℝ) / X ^ 2) : ℝ) : ℂ))⁻¹ ≠ 0 := by
    intro h; have h1 : (1 - (((Real.exp ((d.val : ℝ) / X ^ 2) : ℝ) : ℂ))⁻¹) *
      ((Real.exp ((d.val : ℝ) / X ^ 2) : ℝ) : ℂ) = 0 := by rw [h, zero_mul]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hE0] at h1; exact hE1 h1
  push_cast
  field_simp [hE0, hE1, hden]

/-- **100% Unconditional `SqRayProfile` for the Physical 3D Ideal Bose–Einstein Condensate `F_BEC^{(3)}(q)`**! -/
def bec3DProfile : SqRayProfile logDerivBec3D where
  coeffBoundPow := 5
  coeffBoundC := 27
  coeffBound_nonneg := by norm_num
  coeffBound n := by
    rw [logDerivBec3D, PowerSeries.coeff_mk]
    split_ifs with h0
    · simp; positivity
    · rw [Complex.norm_natCast]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hdiv_le : (bec3DDivSum n : ℝ) ≤ 27 * (n : ℝ) ^ 5 := by
        unfold bec3DDivSum
        rw [Nat.cast_sum]
        calc (∑ d ∈ (Finset.Icc 1 n).filter (· ∣ n), ((d * r3Count d : ℕ) : ℝ))
            ≤ ∑ d ∈ (Finset.Icc 1 n).filter (· ∣ n), 27 * (n : ℝ) ^ 4 := by
              apply Finset.sum_le_sum; intro d hd
              have hdN : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
              have hr : (r3Count d : ℝ) ≤ (2 * (d : ℝ) + 1) ^ 3 := by exact_mod_cast r3Count_le d
              have h2d : 2 * (d : ℝ) + 1 ≤ 3 * (n : ℝ) := by linarith
              rw [Nat.cast_mul]
              calc (d : ℝ) * (r3Count d : ℝ)
                  ≤ (n : ℝ) * (3 * (n : ℝ)) ^ 3 :=
                    mul_le_mul hdN (hr.trans (pow_le_pow_left₀ (by positivity) h2d 3))
                      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
                _ = 27 * (n : ℝ) ^ 4 := by ring
          _ ≤ ∑ _d ∈ Finset.Icc 1 n, 27 * (n : ℝ) ^ 4 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) fun _ _ _ ↦ by positivity
          _ = 27 * (n : ℝ) ^ 5 := by simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      exact hdiv_le.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 5) (by norm_num))
  scalePow := 4
  polarHigh := 5
  polarPoly := Polynomial.C bec3DConst - Polynomial.X ^ 3
  waveAmp := fun ℓ N ↦
    (if ℓ.val = 0 then (-2 * (Real.pi : ℂ) ^ 2 * I) else (2 * (Real.pi : ℂ) ^ 2 * I)) *
      ((bec3DWaveMult N.val : ℝ) : ℂ)
  waveBoundPow := 5
  waveBoundC := 54 * Real.pi ^ 2
  waveBound_nonneg := by positivity
  waveBound ℓ N := by
    have hnorm_pm : ‖if ℓ.val = 0 then (-2 * (Real.pi : ℂ) ^ 2 * I) else (2 * (Real.pi : ℂ) ^ 2 * I)‖ =
        2 * Real.pi ^ 2 := by
      split_ifs <;>
        simp [norm_neg, norm_pow, Complex.norm_real, Complex.norm_I, abs_of_pos Real.pi_pos]
    rw [norm_mul, hnorm_pm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bec3DWaveMult_nonneg N.val)]
    calc (2 * Real.pi ^ 2) * bec3DWaveMult N.val
        ≤ (2 * Real.pi ^ 2) * (27 * (N.val : ℝ) ^ 5) :=
          mul_le_mul_of_nonneg_left (bec3DWaveMult_le N.val) (by positivity)
      _ = (54 * Real.pi ^ 2) * (N.val : ℝ) ^ 5 := by ring
  prime_amp_ne_zero p hp := by
    have hp_pos : (0 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.pos
    have hmult_pos : 0 < bec3DWaveMult p.val :=
      lt_of_lt_of_le (by linarith) (bec3DWaveMult_ge_six_mul p.pos)
    have hpi : (-2 * (Real.pi : ℂ) ^ 2 * I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
        (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) Complex.I_ne_zero
    simp only [↓reduceIte]
    exact mul_ne_zero hpi (Complex.ofReal_ne_zero.mpr hmult_pos.ne')
  decomp := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
    rw [psValue_logDerivBec3D_eq hX, bec3D_analytic_identity hX]
    have hpol : ((X : ℂ) ^ 5) * (Polynomial.C bec3DConst - Polynomial.X ^ 3).eval ((X : ℂ)⁻¹) =
        bec3DConst * (X : ℂ) ^ 5 - (X : ℂ) ^ 2 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      field_simp [hX0]
    rw [hpol]
    congr 1; congr 1
    -- Regroup the `(d, j)` wave sum by `N = d * j` into `∑'_{ℓN : Fin 2 × ℕ+}`!
    let w (ℓ : Fin 2) (dj : ℕ+ × ℕ+) : ℂ :=
      ((((r3Count dj.1.val : ℝ) * (dj.2.val : ℝ) / Real.sqrt (dj.1.val : ℝ) : ℝ) : ℂ)) *
        (if ℓ.val = 0 then (-2 * (Real.pi : ℂ) ^ 2 * I) else (2 * (Real.pi : ℂ) ^ 2 * I)) *
        Complex.exp (-ppRay 2 ℓ.val * (((Real.sqrt (dj.1.val : ℝ) * Real.sqrt (dj.2.val : ℝ) * X : ℝ) : ℂ)))
    have hnorm_pm (ℓ : Fin 2) :
        ‖if ℓ.val = 0 then (-2 * (Real.pi : ℂ) ^ 2 * I) else (2 * (Real.pi : ℂ) ^ 2 * I)‖ = 2 * Real.pi ^ 2 := by
      split_ifs <;>
        simp [norm_neg, norm_pow, Complex.norm_real, Complex.norm_I, abs_of_pos Real.pi_pos]
    have hsum_w (ℓ : Fin 2) : Summable (fun dj : ℕ+ × ℕ+ ↦ ‖w ℓ dj‖) := by
      let c : ℝ := 2 * Real.pi ^ (3 / 2 : ℝ) * X
      have hc : 0 < c := by positivity
      have hre_ray : (ppRay 2 ℓ.val).re = 2 * Real.pi ^ (3 / 2 : ℝ) := by
        fin_cases ℓ
        · dsimp only; exact (congrArg Complex.re ppRay_two_zero).trans (by simp [sqRay0])
        · dsimp only; exact (congrArg Complex.re ppRay_two_one).trans (by simp [sqRay1])
      have hs_d : Summable (fun d : ℕ+ ↦ (d.val : ℝ) ^ 3 * Real.exp (-(c / 2) * (d.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) :=
        summable_pow_mul_exp_neg_rpow (d := 2) (by decide) (half_pos hc) 3
      have hs_j : Summable (fun j : ℕ+ ↦ (j.val : ℝ) ^ 1 * Real.exp (-(c / 2) * (j.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) :=
        summable_pow_mul_exp_neg_rpow (d := 2) (by decide) (half_pos hc) 1
      have hdom : Summable (fun dj : ℕ+ × ℕ+ ↦
          (54 * Real.pi ^ 2) *
            (((dj.1.val : ℝ) ^ 3 * Real.exp (-(c / 2) * (dj.1.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) *
             ((dj.2.val : ℝ) ^ 1 * Real.exp (-(c / 2) * (dj.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))))) :=
        (hs_d.mul_of_nonneg hs_j (fun _ ↦ by positivity) (fun _ ↦ by positivity)).mul_left _
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun dj ↦ ?_) hdom
      have hd1 : (1 : ℝ) ≤ (dj.1.val : ℝ) := by exact_mod_cast dj.1.pos
      have hj1 : (1 : ℝ) ≤ (dj.2.val : ℝ) := by exact_mod_cast dj.2.pos
      have hsd1 : (1 : ℝ) ≤ Real.sqrt (dj.1.val : ℝ) := by simpa using Real.sqrt_le_sqrt hd1
      have hsj1 : (1 : ℝ) ≤ Real.sqrt (dj.2.val : ℝ) := by simpa using Real.sqrt_le_sqrt hj1
      have hr : (r3Count dj.1.val : ℝ) ≤ 27 * (dj.1.val : ℝ) ^ 3 := by
        have h1 : (r3Count dj.1.val : ℝ) ≤ (2 * (dj.1.val : ℝ) + 1) ^ 3 := by exact_mod_cast r3Count_le dj.1.val
        have h2 : 2 * (dj.1.val : ℝ) + 1 ≤ 3 * (dj.1.val : ℝ) := by linarith
        exact h1.trans ((pow_le_pow_left₀ (by positivity) h2 3).trans_eq (by ring))
      have hre_e : (-ppRay 2 ℓ.val * (((Real.sqrt (dj.1.val : ℝ) * Real.sqrt (dj.2.val : ℝ) * X : ℝ) : ℂ))).re =
          -c * (Real.sqrt (dj.1.val : ℝ) * Real.sqrt (dj.2.val : ℝ)) := by
        rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
            sub_zero, hre_ray]; dsimp [c]; ring
      have hexp_s : Real.exp (-c * (Real.sqrt (dj.1.val : ℝ) * Real.sqrt (dj.2.val : ℝ))) ≤
          Real.exp (-(c / 2) * (dj.1.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) *
            Real.exp (-(c / 2) * (dj.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
        rw [show (1 / ((2 : ℕ) : ℝ)) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        have h1 : Real.sqrt (dj.1.val : ℝ) + Real.sqrt (dj.2.val : ℝ) ≤
            2 * (Real.sqrt (dj.1.val : ℝ) * Real.sqrt (dj.2.val : ℝ)) := by nlinarith
        nlinarith
      simp only [w, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (r3Count dj.1.val : ℝ) * (dj.2.val : ℝ) / Real.sqrt (dj.1.val : ℝ) by positivity),
        hnorm_pm, Complex.norm_exp, hre_e, pow_one]
      have hdiv_le : (r3Count dj.1.val : ℝ) * (dj.2.val : ℝ) / Real.sqrt (dj.1.val : ℝ) ≤
          27 * (dj.1.val : ℝ) ^ 3 * (dj.2.val : ℝ) := by
        calc _ ≤ (r3Count dj.1.val : ℝ) * (dj.2.val : ℝ) / 1 :=
              div_le_div_of_nonneg_left (by positivity) zero_lt_one hsd1
          _ = (r3Count dj.1.val : ℝ) * (dj.2.val : ℝ) := div_one _
          _ ≤ (27 * (dj.1.val : ℝ) ^ 3) * (dj.2.val : ℝ) := by gcongr
      calc ((r3Count dj.1.val : ℝ) * (dj.2.val : ℝ) / Real.sqrt (dj.1.val : ℝ)) * (2 * Real.pi ^ 2) *
            Real.exp (-c * (Real.sqrt (dj.1.val : ℝ) * Real.sqrt (dj.2.val : ℝ)))
          ≤ (27 * (dj.1.val : ℝ) ^ 3 * (dj.2.val : ℝ)) * (2 * Real.pi ^ 2) *
              (Real.exp (-(c / 2) * (dj.1.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) *
                Real.exp (-(c / 2) * (dj.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) := by gcongr
        _ = _ := by ring
    let rhsTerm (ℓN : Fin 2 × ℕ+) : ℂ :=
      (if ℓN.1.val = 0 then (-2 * (Real.pi : ℂ) ^ 2 * I) else (2 * (Real.pi : ℂ) ^ 2 * I)) *
        ((bec3DWaveMult ℓN.2.val : ℝ) : ℂ) *
        Complex.exp (-ppWaveRate 2 ℓN.1 ℓN.2 * (X : ℂ))
    have hgroup (ℓ : Fin 2) : (∑' dj : ℕ+ × ℕ+, w ℓ dj) = ∑' N : ℕ+, rhsTerm (ℓ, N) := by
      let g (dj : ℕ+ × ℕ+) : ℕ+ := ⟨dj.1.val * dj.2.val, mul_pos dj.1.pos dj.2.pos⟩
      rw [(hsum_w ℓ).of_norm.hasSum.tsum_fiberwise g |>.tsum_eq.symm]
      apply tsum_congr; intro N
      let S := (Finset.Icc 1 N.val).filter (· ∣ N.val)
      let e : g ⁻¹' {N} ≃ S :=
        { toFun := fun dj ↦ ⟨dj.val.1.val, Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨dj.val.1.pos,
              Nat.le_of_dvd N.pos ⟨dj.val.2.val, (congrArg Subtype.val dj.property).symm⟩⟩,
             ⟨dj.val.2.val, (congrArg Subtype.val dj.property).symm⟩⟩⟩
          invFun := fun d ↦
            have hd_pos : 0 < d.val := (Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1).1
            have hdvd : d.val ∣ N.val := (Finset.mem_filter.mp d.property).2
            have hj_pos : 0 < N.val / d.val := Nat.div_pos (Nat.le_of_dvd N.pos hdvd) hd_pos
            ⟨(⟨d.val, hd_pos⟩, ⟨N.val / d.val, hj_pos⟩), PNat.eq (Nat.mul_div_cancel' hdvd)⟩
          left_inv := fun ⟨⟨d, j⟩, hdj⟩ ↦ Subtype.ext (Prod.ext rfl (PNat.eq (by
            change N.val / d.val = j.val
            have h1 : d.val * j.val = N.val := congrArg Subtype.val hdj
            rw [← h1]; exact Nat.mul_div_cancel_left j.val d.pos)))
          right_inv := fun ⟨_, _⟩ ↦ rfl }
      let _ : Fintype (g ⁻¹' {N}) := Fintype.ofEquiv S e.symm
      rw [tsum_fintype, Fintype.sum_equiv e (fun dj ↦ w ℓ dj.val)
          (fun d ↦ (if ℓ.val = 0 then (-2 * (Real.pi : ℂ) ^ 2 * I) else (2 * (Real.pi : ℂ) ^ 2 * I)) *
            ((((N.val : ℝ) * ((r3Count d.val : ℝ) / ((d.val : ℝ) * Real.sqrt (d.val : ℝ))) : ℝ) : ℂ)) *
            Complex.exp (-ppWaveRate 2 ℓ N * (X : ℂ)))
          (fun dj ↦ by
            have hdj : dj.val.1.val * dj.val.2.val = N.val := congrArg Subtype.val dj.property
            have hd_pos : (0 : ℝ) < (dj.val.1.val : ℝ) := by exact_mod_cast dj.val.1.pos
            have hsd_pos : 0 < Real.sqrt (dj.val.1.val : ℝ) := Real.sqrt_pos.mpr hd_pos
            have hN_sqrt : Real.sqrt (N.val : ℝ) = Real.sqrt (dj.val.1.val : ℝ) * Real.sqrt (dj.val.2.val : ℝ) := by
              rw [← hdj, Nat.cast_mul, Real.sqrt_mul hd_pos.le]
            have hN_rpow : (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) = Real.sqrt (N.val : ℝ) := by
              rw [Real.sqrt_eq_rpow]; norm_num
            have hcoeff_real : (r3Count dj.val.1.val : ℝ) * (dj.val.2.val : ℝ) / Real.sqrt (dj.val.1.val : ℝ) =
                (N.val : ℝ) * ((r3Count dj.val.1.val : ℝ) / ((dj.val.1.val : ℝ) * Real.sqrt (dj.val.1.val : ℝ))) := by
              have hN_cast : (N.val : ℝ) = (dj.val.1.val : ℝ) * (dj.val.2.val : ℝ) := by exact_mod_cast hdj.symm
              rw [hN_cast]; field_simp [hd_pos.ne', hsd_pos.ne']
            dsimp only [w, e, Equiv.coe_fn_mk, ppWaveRate]
            rw [hcoeff_real, hN_rpow, hN_sqrt]
            have hexp : -ppRay 2 ℓ.val * (((Real.sqrt (dj.val.1.val : ℝ) * Real.sqrt (dj.val.2.val : ℝ) * X : ℝ) : ℂ)) =
                -(((Real.sqrt (dj.val.1.val : ℝ) * Real.sqrt (dj.val.2.val : ℝ) : ℝ) : ℂ) * ppRay 2 ℓ.val) * (X : ℂ) := by
              push_cast; ring
            rw [hexp]; ring)]
      rw [Finset.univ_eq_attach,
          Finset.sum_attach S (fun d : ℕ ↦
            (if ℓ.val = 0 then (-2 * (Real.pi : ℂ) ^ 2 * I) else (2 * (Real.pi : ℂ) ^ 2 * I)) *
            ((((N.val : ℝ) * ((r3Count d : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))) : ℝ) : ℂ)) *
            Complex.exp (-ppWaveRate 2 ℓ N * (X : ℂ)))]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Complex.ofReal_sum, ← Finset.mul_sum]
      rfl
    have hsum_rhs_norm : Summable (fun ℓN : Fin 2 × ℕ+ ↦ ‖rhsTerm ℓN‖) := by
      rw [← (Equiv.sigmaEquivProd (Fin 2) ℕ+).summable_iff]
      refine (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr ⟨fun ℓ ↦ ?_, hasSum_fintype _ |>.summable⟩
      have hc : 0 < (ppRay 2 ℓ.val).re * X := mul_pos (ppRay_re_pos (by decide) ℓ.isLt) hX
      have hdom := (summable_pow_mul_exp_neg_rpow (d := 2) (by decide) hc 5).mul_left (54 * Real.pi ^ 2)
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) hdom
      have hre : (-ppWaveRate 2 ℓ N * (X : ℂ)).re =
          -((ppRay 2 ℓ.val).re * X) * (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := by
        simp [ppWaveRate, Complex.mul_re]; ring
      simp only [Equiv.sigmaEquivProd_apply, rhsTerm, norm_mul, hnorm_pm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (bec3DWaveMult_nonneg N.val), Complex.norm_exp, hre]
      calc (2 * Real.pi ^ 2) * bec3DWaveMult N.val * _
          ≤ (2 * Real.pi ^ 2) * (27 * (N.val : ℝ) ^ 5) * _ := by gcongr; exact bec3DWaveMult_le N.val
        _ = _ := by ring
    have hsum_rhs : Summable rhsTerm := hsum_rhs_norm.of_norm
    have hval_split : (∑' ℓN : Fin 2 × ℕ+, rhsTerm ℓN) =
        (∑' N : ℕ+, rhsTerm (0, N)) + (∑' N : ℕ+, rhsTerm (1, N)) := by
      rw [hsum_rhs.tsum_prod' (fun ℓ ↦ hsum_rhs.comp_injective fun N₁ N₂ h ↦ by injection h),
          tsum_fintype, Fin.sum_univ_two]
    have hwd_sum (ℓ : Fin 2) : Summable (fun d : ℕ+ ↦ ∑' j : ℕ+, w ℓ (d, j)) := by
      have h1 := ((Equiv.sigmaEquivProd ℕ+ ℕ+).summable_iff.mpr (hsum_w ℓ))
      have h2 := (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mp h1
      refine Summable.of_norm_bounded (g := fun d : ℕ+ ↦ ∑' j : ℕ+, ‖w ℓ (d, j)‖) h2.2 fun d ↦
        norm_tsum_le_tsum_norm ((hsum_w ℓ).comp_injective fun j₁ j₂ h ↦ by injection h)
    symm
    rw [hval_split, ← hgroup 0, ← hgroup 1,
        (hsum_w 0).of_norm.tsum_prod' (fun d ↦ (hsum_w 0).of_norm.comp_injective fun j₁ j₂ h ↦ by injection h),
        (hsum_w 1).of_norm.tsum_prod' (fun d ↦ (hsum_w 1).of_norm.comp_injective fun j₁ j₂ h ↦ by injection h),
        ← (hwd_sum 0).tsum_add (hwd_sum 1)]
    apply tsum_congr; intro d
    have hs0 : Summable (fun j : ℕ+ ↦ w 0 (d, j)) :=
      (hsum_w 0).of_norm.comp_injective fun j₁ j₂ h ↦ by injection h
    have hs1 : Summable (fun j : ℕ+ ↦ w 1 (d, j)) :=
      (hsum_w 1).of_norm.comp_injective fun j₁ j₂ h ↦ by injection h
    rw [← hs0.tsum_add hs1]
    apply tsum_congr; intro j
    dsimp only [w]
    rw [show (0 : Fin 2).val = 0 from rfl, show (1 : Fin 2).val = 1 from rfl,
        ppRay_two_zero, ppRay_two_one]
    simp only [↓reduceIte, one_ne_zero]; ring

/-! ### 3. 100% Unconditional 3D Ideal Bose–Einstein & Fermi–Dirac Differential Transcendence -/

/-- **100% UNCONDITIONAL Differential Transcendence of the 3D BEC Internal Energy Series
`F_BEC^{(3)}(q) = ∑_{N ≥ 1} (∑_{d ∣ N} d r_3(d)) q^N` over `ℂ(q)`**! -/
theorem logDerivBec3D_non_ade :
    AlgebraicIndependent ℂ (seriesCoordinates logDerivBec3D) :=
  sqRayProfile_non_ade bec3DProfile

/-- **100% UNCONDITIONAL Joint Differential Independence of ALL Distinct 3D BEC Log-Derivative
Dilations `{F_BEC^{(3)}(q^{a_1}), …, F_BEC^{(3)}(q^{a_s})}` over `ℂ(q)`**! -/
theorem logDerivBec3D_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ logDerivBec3DDilated (a i).val)) :=
  sqRayProfile_dilations_diff_indep bec3DProfile a ha

/-- **100% UNCONDITIONAL Differential Transcendence of the Physical 3D Ideal Bose–Einstein
Condensate `Z_BEC^{(3)}(q) = ∏_{n ∈ ℤ³ \ {0}} (1 - q^{|n|²})^{-1}` over `ℂ(q)`**! -/
theorem bec3D_non_ade :
    AlgebraicIndependent ℂ (seriesCoordinates bec3DSeries) :=
  diffTrans_of_logDeriv (c := 1) bec3DSeries_ne_zero one_ne_zero
    (by simpa using X_mul_deriv_bec3DSeries) logDerivBec3D_non_ade

/-- **100% UNCONDITIONAL Differential Transcendence of ALL Nonzero Integer Powers
`Z_BEC^{(3)}(q)^k` (`k ∈ ℤ \ {0}`) over `ℂ(q)`**! -/
theorem bec3D_zpow_non_ade {k : ℤ} (hk : k ≠ 0) :
    AlgebraicIndependent ℂ (seriesCoordinates (bec3DZPow k)) :=
  diffTrans_of_logDeriv (c := (k : ℂ)) (bec3DZPow_ne_zero k)
    (Int.cast_ne_zero.mpr hk) (X_mul_deriv_bec3DZPow k) logDerivBec3D_non_ade

/-- **100% UNCONDITIONAL Joint Differential Independence of ALL Distinct 3D BEC Dilations
`{Z_BEC^{(3)}(q^{a_1}), …, Z_BEC^{(3)}(q^{a_s})}` over `ℂ(q)`**! -/
theorem bec3D_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ bec3DDilated (a i).val)) :=
  kolchin_logDeriv_joint_indep
    (fun i ↦ logDerivBec3DDilated (a i).val)
    (fun i ↦ bec3DDilated (a i).val)
    (fun i ↦ ((a i).val : ℂ))
    (fun i ↦ bec3DDilated_ne_zero (a i).val)
    (fun i ↦ by exact_mod_cast (a i).pos.ne')
    (fun i ↦ X_mul_deriv_bec3DDilated (a i).pos)
    (logDerivBec3D_dilations_diff_indep a ha)

/-- **Codex's 3D Bose–Fermi Quotient-Rank Theorem (100% Unconditional)**:
For ANY finite injective family of dilations `a : Fin n → ℕ+` and ANY integer matrix
`M : Matrix (Fin r) (Fin n) ℤ` with `ℚ`-linearly independent rows, the Laurent-monomial products
`Y_i = ∏_j Z_BEC^{(3)}(q^{a_j})^{M_{ij}}` are **jointly differentially independent over `ℂ(q)`**!
In particular, any family of mixed 3D Bose and 3D Fermi dilations whose integer exponent matrix
on the underlying 3D Bose dilations has full row rank is jointly differentially independent! -/
theorem bec3D_bose_fermi_quotient_rank {r n : ℕ}
    (a : Fin n → ℕ+) (ha : Function.Injective a)
    (M : Matrix (Fin r) (Fin n) ℤ)
    (hM : LinearIndependent ℚ (fun i : Fin r ↦ fun j : Fin n ↦ (M i j : ℚ))) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i : Fin r ↦
      ((∏ j : Fin n, (isUnit_bec3DDilated (a j).val).unit ^ M i j :
        (PowerSeries ℂ)ˣ) : PowerSeries ℂ))) :=
  monomial_family_diff_indep_of_logDeriv
    (fun j ↦ logDerivBec3DDilated (a j).val)
    (fun j ↦ (isUnit_bec3DDilated (a j).val).unit)
    (fun j ↦ ((a j).val : ℂ))
    (fun j ↦ by exact_mod_cast (a j).pos.ne')
    (fun j ↦ X_mul_deriv_bec3DDilated (a j).pos)
    (logDerivBec3D_dilations_diff_indep a ha) M hM

/-- **100% UNCONDITIONAL Single-Temperature Joint Differential Independence of 3D Bose and 3D Fermi
Gases `(Z_BEC^{(3)}(q), Z_FD^{(3)}(q))` over `ℂ(q)`**! -/
theorem bec3D_fermi3D_joint_diff_indep :
    AlgebraicIndependent ℂ (jointSeriesCoordinates ![bec3DSeries, fermi3DSeries]) := by
  let a : Fin 2 → ℕ+ := ![1, 2]
  have ha : Function.Injective a := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [a]
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, -1]
  have hM : LinearIndependent ℚ (fun i : Fin 2 ↦ fun j : Fin 2 ↦ (M i j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]; intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, M,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_one, Int.cast_zero, Int.cast_neg] at h0 h1
    intro i; fin_cases i <;> dsimp <;> linarith
  have hind := bec3D_bose_fermi_quotient_rank a ha M hM
  have heq : (fun i : Fin 2 ↦
      ((∏ j : Fin 2, (isUnit_bec3DDilated (a j).val).unit ^ M i j :
        (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = ![bec3DSeries, fermi3DSeries] := by
    funext i; fin_cases i
    · simp [a, M, bec3DSeries, Fin.prod_univ_two]
    · simp [a, M, fermi3DSeries, fermi3DDilated, fermi3DUnit, Fin.prod_univ_two]
  rwa [heq] at hind

/-- **100% UNCONDITIONAL Forest / Distinct-Source Quotient Independence for 3D BEC Dilations**:
For ANY finite family of edges `(u_i, v_i)` with `u` injective and `u_i < v_i`, the quotients
`{Z_BEC^{(3)}(q^{u_i}) / Z_BEC^{(3)}(q^{v_i})}` are jointly differentially independent over `ℂ(q)`! -/
theorem bec3D_forest_quotients_diff_indep {r : ℕ}
    (u v : Fin r → ℕ+) (hu : Function.Injective u) (huv : ∀ i, u i < v i) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i : Fin r ↦
      (((isUnit_bec3DDilated (u i).val).unit *
        (isUnit_bec3DDilated (v i).val).unit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ))) := by
  simpa only [zpow_one] using distinctSource_quotient_pow_diff_indep
    (fun m ↦ logDerivBec3DDilated m.val)
    (fun m ↦ (isUnit_bec3DDilated m.val).unit)
    (fun m ↦ (m.val : ℂ))
    (fun m ↦ by exact_mod_cast m.pos.ne')
    (fun m ↦ X_mul_deriv_bec3DDilated m.pos)
    (fun b hb ↦ logDerivBec3D_dilations_diff_indep b hb)
    u v hu huv 1 one_ne_zero

/-- **100% UNCONDITIONAL Joint Differential Independence of ALL Distinct 3D Ideal Fermi–Dirac Gas
Dilations `{Z_FD^{(3)}(q^{a_1}), …, Z_FD^{(3)}(q^{a_s})}` over `ℂ(q)`**! -/
theorem fermi3D_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ fermi3DDilated (a i))) := by
  have huv : ∀ i : Fin s, a i < 2 * a i := fun i ↦ by
    change (a i).val < 2 * (a i).val; nlinarith [(a i).pos]
  simpa only [fermi3DDilated, fermi3DUnit, PNat.mul_coe, PNat.val_ofNat] using
    bec3D_forest_quotients_diff_indep a (fun i ↦ 2 * a i) ha huv

/-- **100% UNCONDITIONAL Differential Transcendence of the Physical 3D Ideal Fermi–Dirac Gas
`Z_FD^{(3)}(q) = ∏_{n ∈ ℤ³ \ {0}} (1 + q^{|n|²})` over `ℂ(q)`**! -/
theorem fermi3D_non_ade :
    AlgebraicIndependent ℂ (seriesCoordinates fermi3DSeries) := by
  have hind := fermi3D_dilations_diff_indep (fun _ : Fin 1 ↦ 1) (fun i j _ ↦ Subsingleton.elim i j)
  exact single_diffTrans_of_joint hind

/-! ### 4. 100% Unconditional Joint Differential Independence of 1D & 3D Ideal Quantum Gases -/

/-- Elementary Legendre mod-8 obstruction: no integer `n ≡ 7 (mod 8)` is a sum of three squares. -/
theorem r3Count_eq_zero_of_mod_eight_eq_seven {n : ℕ} (hn : n % 8 = 7) : r3Count n = 0 := by
  unfold r3Count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ heq
  have hsq_mod (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
    have h1 : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by rw [sq, sq, Int.mul_emod]
    rw [h1]
    have hlo : 0 ≤ x % 8 := Int.emod_nonneg x (by decide)
    have hhi : x % 8 < 8 := Int.emod_lt_of_pos x (by decide)
    interval_cases (x % 8) <;> decide
  have hsum_mod : (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) % 8 = 7 := by
    rw [heq]; exact_mod_cast hn
  have h1 := hsq_mod v.1
  have h2 := hsq_mod v.2.1
  have h3 := hsq_mod v.2.2
  omega

/-- Via Fermat's two-square theorem (`Nat.Prime.sq_add_sq`), every prime `p ≡ 1 (mod 4)` satisfies
`r_3(p) ≥ 1`. -/
theorem r3Count_pos_of_prime_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    1 ≤ r3Count p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have ha_le : (a : ℤ) ≤ (p : ℤ) := by
    have h1 : a ≤ a ^ 2 := Nat.le_self_pow (by decide) a
    have h2 : a ^ 2 ≤ p := by omega
    exact_mod_cast h1.trans h2
  have hb_le : (b : ℤ) ≤ (p : ℤ) := by
    have h1 : b ≤ b ^ 2 := Nat.le_self_pow (by decide) b
    have h2 : b ^ 2 ≤ p := by omega
    exact_mod_cast h1.trans h2
  have hmem : ((a : ℤ), ((b : ℤ), (0 : ℤ))) ∈
      (Finset.Icc (-(p : ℤ)) (p : ℤ) ×ˢ (Finset.Icc (-(p : ℤ)) (p : ℤ) ×ˢ
        Finset.Icc (-(p : ℤ)) (p : ℤ))).filter
        (fun v : ℤ × ℤ × ℤ ↦ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (p : ℤ)) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, ha_le⟩, ⟨by omega, hb_le⟩, ⟨by omega, by omega⟩⟩, ?_⟩
    have hz : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) = (p : ℤ) := by exact_mod_cast hab
    linarith
  exact Finset.card_pos.mpr ⟨_, hmem⟩

private noncomputable def apPrimeSeq (A q a : ℕ) (hq : q ≠ 0) (hcop : a.Coprime q) : ℕ → ℕ
  | 0 => Classical.choose (Nat.forall_exists_prime_gt_and_modEq A hq hcop)
  | n + 1 => Classical.choose (Nat.forall_exists_prime_gt_and_modEq (apPrimeSeq A q a hq hcop n) hq hcop)

private lemma apPrimeSeq_spec (A q a : ℕ) (hq : q ≠ 0) (hcop : a.Coprime q) :
    ∀ n : ℕ, A < apPrimeSeq A q a hq hcop n ∧
      (apPrimeSeq A q a hq hcop n).Prime ∧
      apPrimeSeq A q a hq hcop n ≡ a [MOD q] ∧
      (∀ m < n, apPrimeSeq A q a hq hcop m < apPrimeSeq A q a hq hcop n) := by
  intro n
  induction n with
  | zero =>
    obtain ⟨hgt, hpr, hmod⟩ := Classical.choose_spec (Nat.forall_exists_prime_gt_and_modEq A hq hcop)
    exact ⟨hgt, hpr, hmod, fun _ hm ↦ (Nat.not_lt_zero _ hm).elim⟩
  | succ n ih =>
    obtain ⟨hgt_n, _, _, hmono_n⟩ := ih
    obtain ⟨hgt, hpr, hmod⟩ :=
      Classical.choose_spec (Nat.forall_exists_prime_gt_and_modEq (apPrimeSeq A q a hq hcop n) hq hcop)
    refine ⟨hgt_n.trans hgt, hpr, hmod, fun m hm ↦ ?_⟩
    rcases (Nat.lt_succ_iff.mp hm).eq_or_lt with rfl | hlt
    · exact hgt
    · exact (hmono_n m hlt).trans hgt

private lemma apPrimeSeq_strictMono (A q a : ℕ) (hq : q ≠ 0) (hcop : a.Coprime q) :
    StrictMono (apPrimeSeq A q a hq hcop) :=
  fun _ _ hlt ↦ (apPrimeSeq_spec A q a hq hcop _).2.2.2 _ hlt

/-- `SqRayProfile` wrapper around Wave 9's `powerPartStokesProfileTwo` for `F_2(q) = logDerivPowerPart 2`. -/
def powerPartTwoProfile : SqRayProfile (logDerivPowerPart 2) where
  coeffBoundPow := 2
  coeffBoundC := 1
  coeffBound_nonneg := zero_le_one
  coeffBound n := by
    rw [logDerivPowerPart, logDerivPowerPartDilated, PowerSeries.coeff_mk]
    split_ifs with h0 hdvd
    · simp; positivity
    · rw [Complex.norm_natCast, one_mul, Nat.div_one]
      have hle : powerDivSum 2 n ≤ n ^ 3 := by
        unfold powerDivSum
        calc ∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ k ^ 2 ∣ n), k ^ 2
            ≤ ∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ k ^ 2 ∣ n), n ^ 2 := by
              apply Finset.sum_le_sum; intro k hk
              exact Nat.pow_le_pow_left (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2 2
          _ ≤ ∑ _k ∈ Finset.Icc 1 n, n ^ 2 :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset ..)
          _ = n ^ 3 := by simp [pow_succ, mul_comm]
      -- Wait: `powerDivSum 2 n ≤ n * n = n^2` because each `k^2 ∣ n` satisfies `k^2 ≤ n`!
      have hle2 : powerDivSum 2 n ≤ n ^ 2 := by
        unfold powerDivSum
        calc ∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ k ^ 2 ∣ n), k ^ 2
            ≤ ∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ k ^ 2 ∣ n), n := by
              apply Finset.sum_le_sum; intro k hk
              exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Finset.mem_filter.mp hk).2
          _ ≤ ∑ _k ∈ Finset.Icc 1 n, n :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset ..)
          _ = n ^ 2 := by simp [sq]
      exact (Nat.cast_le (α := ℝ).mpr hle2).trans
        (by rw [Nat.cast_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2)
    · simp; positivity
  scalePow := 3
  polarHigh := 3
  polarPoly := Polynomial.C ((1 / 2 : ℂ) * sqPartConst) - Polynomial.C (1 / 2 : ℂ) * Polynomial.X
  waveAmp := fun ℓ N ↦ -(1 / 2 : ℂ) * ((powerPartMult 2 N.val : ℝ) : ℂ) * ppWaveRate 2 ℓ N
  waveBoundPow := 2
  waveBoundC := (1 / 2 : ℝ) * (2 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt 2)
  waveBound_nonneg := by positivity
  waveBound ℓ N := by
    have hnorm_ray : ‖ppRay 2 ℓ.val‖ = 2 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt 2 := by
      fin_cases ℓ
      · change ‖ppRay 2 0‖ = _
        rw [ppRay_two_zero, sqRay0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity), Complex.norm_def, Complex.normSq_apply]; norm_num
      · change ‖ppRay 2 1‖ = _
        rw [ppRay_two_one, sqRay1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity), Complex.norm_def, Complex.normSq_apply]; norm_num
    have hN1 : (1 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast N.pos
    have hrpow_le : (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) ≤ (N.val : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 / ((2 : ℕ) : ℝ)) ≤ 1)
    have hmult_nn : 0 ≤ powerPartMult 2 N.val :=
      Finset.sum_nonneg fun _ _ ↦ by positivity
    have hmult_le : powerPartMult 2 N.val ≤ (N.val : ℝ) := by
      unfold powerPartMult
      calc ∑ k ∈ (Finset.Icc 1 N.val).filter (fun k ↦ k ^ 2 ∣ N.val), (k : ℝ)⁻¹
          ≤ ∑ _k ∈ (Finset.Icc 1 N.val).filter (fun k ↦ k ^ 2 ∣ N.val), (1 : ℝ) := by
            apply Finset.sum_le_sum; intro k hk
            exact inv_le_one_of_one_le₀ (by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1)
        _ ≤ ∑ _k ∈ Finset.Icc 1 N.val, (1 : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) fun _ _ _ ↦ zero_le_one
        _ = (N.val : ℝ) := by simp
    have hnorm_half : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [norm_mul, norm_mul, hnorm_half, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmult_nn,
        ppWaveRate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), hnorm_ray]
    calc (1 / 2 : ℝ) * powerPartMult 2 N.val * ((N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) * (2 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt 2))
        ≤ (1 / 2 : ℝ) * (N.val : ℝ) * ((N.val : ℝ) * (2 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt 2)) := by gcongr
      _ = ((1 / 2 : ℝ) * (2 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt 2)) * (N.val : ℝ) ^ 2 := by ring
  prime_amp_ne_zero p hp := by
    rw [powerPartMult_prime (by decide) hp, Complex.ofReal_one, mul_one]
    have hhalf : -(1 / 2 : ℂ) ≠ 0 := by norm_num
    have hr : ppWaveRate 2 ⟨0, by decide⟩ p ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by exact_mod_cast p.pos) _).ne')
        (ppExtremeRay_ne_zero (by decide))
    exact mul_ne_zero hhalf hr
  decomp := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), powerPartStokesProfileTwo.decomp] with X hX hdec
    have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
    have hdec' := congrArg (((1 / 2 : ℂ) * (X : ℂ) ^ 3) * ·) hdec
    simp only [rescaledLogDerivPP, powerPartStokesProfileTwo, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, show (2 + 1 : ℕ) = 3 by rfl, Nat.cast_ofNat] at hdec'
    have hlhs : ((1 / 2 : ℂ) * (X : ℂ) ^ 3) * (2 * ((X : ℂ)⁻¹) ^ 3 * psValue (logDerivPowerPart 2) (qRayD 3 X)) =
        psValue (logDerivPowerPart 2) (qRayD 3 X) := by field_simp [hX0]
    rw [hlhs] at hdec'
    rw [hdec', mul_add]
    congr 1
    · simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]; ring
    · unfold WaveExpansion.value
      rw [mul_comm (1 / 2 : ℂ), mul_assoc, ← tsum_mul_left]
      congr 1; apply tsum_congr; intro ℓN
      simp only [WaveExpansion.term, ppWaveJet, pow_zero, mul_one]
      ring

private lemma seriesDilated_logDerivPowerPart_two (a : ℕ) :
    seriesDilated (logDerivPowerPart 2) a = logDerivPowerPartDilated 2 a := by
  ext N
  by_cases hN0 : N = 0
  · subst hN0; simp [seriesDilated, logDerivPowerPart, logDerivPowerPartDilated]
  · simp only [seriesDilated, logDerivPowerPart, logDerivPowerPartDilated, PowerSeries.coeff_mk,
      hN0, ↓reduceIte]
    by_cases ha : a ∣ N
    · have hdiv0 : N / a ≠ 0 := by
        intro h0
        have : a * (N / a) = N := Nat.mul_div_cancel' ha
        rw [h0, mul_zero] at this; exact hN0 this.symm
      simp [ha, hdiv0]
    · simp [ha]

/-- Exact `(2J) × (2J)` prime-block determinant non-vanishing for the coupled 1D/3D BEC pair:
with `J + 1` primes `p ≡ 7 (mod 8)` (where `r_3(p) = 0`) and `J - 1` primes `p ≡ 1 (mod 4)`
(where `r_3(p) ≥ 1`), the coupled limit matrix `L` is nonsingular! -/
private lemma bec1D_bec3D_block_det_ne_zero {J : ℕ} (hJ : 1 ≤ J)
    (p : Fin (2 * J) → ℕ+) (hp_inj : Function.Injective p)
    (hp_prime : ∀ ν, (p ν).val.Prime)
    (hp_mod8 : ∀ ν : Fin (2 * J), ν.val < J + 1 → (p ν).val % 8 = 7)
    (hp_mod4 : ∀ ν : Fin (2 * J), J + 1 ≤ ν.val → (p ν).val % 4 = 1)
    (e : Fin (2 * J) → ℂ) (he : ∀ ν, e ν ≠ 0)
    (C₁ C₃ β : ℂ) (hC₁ : C₁ ≠ 0) (hC₃ : C₃ ≠ 0) (hβ : β ≠ 0) :
    (Matrix.of fun ν k : Fin (2 * J) ↦
      if k.val < J then
        e ν * (C₁ * (Real.sqrt ((p ν).val : ℝ) : ℂ)) *
          (β * (Real.sqrt ((p ν).val : ℝ) : ℂ)) ^ k.val
      else
        e ν * (C₃ * ((bec3DWaveMult (p ν).val : ℝ) : ℂ)) *
          (β * (Real.sqrt ((p ν).val : ℝ) : ℂ)) ^ (k.val - J)).det ≠ 0 := by
  let L : Matrix (Fin (2 * J)) (Fin (2 * J)) ℂ := Matrix.of fun ν k ↦
    if k.val < J then
      e ν * (C₁ * (Real.sqrt ((p ν).val : ℝ) : ℂ)) *
        (β * (Real.sqrt ((p ν).val : ℝ) : ℂ)) ^ k.val
    else
      e ν * (C₃ * ((bec3DWaveMult (p ν).val : ℝ) : ℂ)) *
        (β * (Real.sqrt ((p ν).val : ℝ) : ℂ)) ^ (k.val - J)
  change L.det ≠ 0
  intro hdet0
  obtain ⟨v, hv_ne, hv_ker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  let u : Fin J → ℂ := fun j ↦ C₁ * β ^ j.val * v ⟨j.val, by omega⟩
  let w : Fin J → ℂ := fun j ↦ C₃ * β ^ j.val * v ⟨J + j.val, by omega⟩
  let U : Polynomial ℂ := ∑ j : Fin J, Polynomial.C (u j) * Polynomial.X ^ j.val
  let W : Polynomial ℂ := ∑ j : Fin J, Polynomial.C (w j) * Polynomial.X ^ j.val
  have hU_coeff (n : ℕ) : U.coeff n = if h : n < J then u ⟨n, h⟩ else 0 := by
    rw [show U.coeff n = (Polynomial.lcoeff ℂ n) U from rfl, map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : n < J
    · simp only [h, ↓reduceDIte]
      rw [Finset.sum_eq_single ⟨n, h⟩]
      · simp
      · intro j _ hne
        have hnj : n ≠ j.val := fun h' ↦ hne (Fin.ext h'.symm)
        simp [hnj]
      · intro hm; exact (hm (Finset.mem_univ _)).elim
    · simp only [h, ↓reduceDIte]
      apply Finset.sum_eq_zero; intro j _
      have hnj : n ≠ j.val := by omega
      simp [hnj]
  have hW_coeff (n : ℕ) : W.coeff n = if h : n < J then w ⟨n, h⟩ else 0 := by
    rw [show W.coeff n = (Polynomial.lcoeff ℂ n) W from rfl, map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : n < J
    · simp only [h, ↓reduceDIte]
      rw [Finset.sum_eq_single ⟨n, h⟩]
      · simp
      · intro j _ hne
        have hnj : n ≠ j.val := fun h' ↦ hne (Fin.ext h'.symm)
        simp [hnj]
      · intro hm; exact (hm (Finset.mem_univ _)).elim
    · simp only [h, ↓reduceDIte]
      apply Finset.sum_eq_zero; intro j _
      have hnj : n ≠ j.val := by omega
      simp [hnj]
  let y (ν : Fin (2 * J)) : ℂ := (Real.sqrt ((p ν).val : ℝ) : ℂ)
  have hy_ne0 (ν : Fin (2 * J)) : y ν ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (p ν).pos)).ne'
  have hy_sq (ν : Fin (2 * J)) : y ν ^ 2 = ((p ν).val : ℂ) := by
    dsimp only [y]; rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hy_inj : Function.Injective y := fun ν₁ ν₂ h ↦ by
    have hsq : ((p ν₁).val : ℂ) = ((p ν₂).val : ℂ) := by rw [← hy_sq ν₁, ← hy_sq ν₂, h]
    exact hp_inj (PNat.eq (Nat.cast_injective hsq))
  -- Every row equation reduces to `U(y ν) + (6 y ν + r_3(p ν) / p ν) W(y ν) = 0`!
  have hrow (ν : Fin (2 * J)) :
      U.eval (y ν) + (6 * y ν + ((r3Count (p ν).val : ℂ) / ((p ν).val : ℂ))) * W.eval (y ν) = 0 := by
    have h0 := congrFun hv_ker ν
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h0
    let splitEquiv : Fin J ⊕ Fin J ≃ Fin (2 * J) :=
      { toFun := fun
          | Sum.inl j => ⟨j.val, by omega⟩
          | Sum.inr j => ⟨J + j.val, by omega⟩
        invFun := fun k => if hk : k.val < J then Sum.inl ⟨k.val, hk⟩ else Sum.inr ⟨k.val - J, by omega⟩
        left_inv := fun s => by cases s with
          | inl j => simp [j.isLt]
          | inr j =>
            have hnot : ¬ J + j.val < J := by omega
            simp only [hnot, ↓reduceDIte, Nat.add_sub_cancel_left]
        right_inv := fun k => by
          by_cases hk : k.val < J
          · simp [hk]
          · simp only [hk, ↓reduceDIte]; ext; dsimp; omega }
    rw [← Fintype.sum_equiv splitEquiv (fun s ↦ L ν (splitEquiv s) * v (splitEquiv s))
          (fun k ↦ L ν k * v k) (fun _ ↦ rfl),
        Fintype.sum_sum_type] at h0
    have hleft : (∑ j : Fin J, L ν (splitEquiv (Sum.inl j)) * v (splitEquiv (Sum.inl j))) =
        e ν * y ν * U.eval (y ν) := by
      rw [show U.eval (y ν) = (Polynomial.evalRingHom (y ν)) U from rfl, map_sum]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      simp only [splitEquiv, Equiv.coe_fn_mk, L, Matrix.of_apply, j.isLt, ↓reduceIte, u, y, mul_pow]
      ring
    have hright : (∑ j : Fin J, L ν (splitEquiv (Sum.inr j)) * v (splitEquiv (Sum.inr j))) =
        e ν * y ν * ((6 * y ν + ((r3Count (p ν).val : ℂ) / ((p ν).val : ℂ))) * W.eval (y ν)) := by
      have hmult : ((bec3DWaveMult (p ν).val : ℝ) : ℂ) =
          y ν * (6 * y ν + ((r3Count (p ν).val : ℂ) / ((p ν).val : ℂ))) := by
        rw [bec3DWaveMult_prime (hp_prime ν)]
        push_cast
        change 6 * ((p ν).val : ℂ) + (r3Count (p ν).val : ℂ) / y ν = _
        rw [← hy_sq ν]
        field_simp [hy_ne0 ν]
      rw [show W.eval (y ν) = (Polynomial.evalRingHom (y ν)) W from rfl, map_sum]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      have hnot : ¬ J + j.val < J := by omega
      simp only [splitEquiv, Equiv.coe_fn_mk, L, Matrix.of_apply, hnot, ↓reduceIte,
        Nat.add_sub_cancel_left, hmult, w, y, mul_pow]
      ring
    rw [hleft, hright, ← mul_add] at h0
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (he ν) (hy_ne0 ν))
  -- Step 1: `P := U + 6 X W` has degree `≤ J` and vanishes at `J + 1` distinct `7 mod 8` primes, hence `P = 0`!
  let P : Polynomial ℂ := U + Polynomial.C 6 * Polynomial.X * W
  have hP_deg : P.natDegree ≤ J := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    simp only [P, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul]
    have hU0 : U.coeff n = 0 := by rw [hU_coeff]; simp [show ¬ n < J by omega]
    have hW0 : W.coeff (n - 1) = 0 := by rw [hW_coeff]; simp [show ¬ n - 1 < J by omega]
    cases n with
    | zero => omega
    | succ n' => simp only [Nat.add_sub_cancel] at hW0; simp [hU0, hW0]
  have hP_zero : P = 0 := by
    by_contra hPne
    let S₁ : Finset (Fin (2 * J)) := Finset.univ.filter fun ν ↦ ν.val < J + 1
    have hS₁_card : S₁.card = J + 1 := by
      let e₁ : Fin (J + 1) ≃ S₁ :=
        { toFun := fun k ↦ ⟨⟨k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩⟩
          invFun := fun ν ↦ ⟨ν.val.val, (Finset.mem_filter.mp ν.property).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      rw [← Fintype.card_coe, Fintype.card_congr e₁.symm, Fintype.card_fin]
    have hsub : S₁.image y ⊆ P.roots.toFinset := by
      intro z hz
      obtain ⟨ν, hνS, rfl⟩ := Finset.mem_image.mp hz
      have hlt : ν.val < J + 1 := (Finset.mem_filter.mp hνS).2
      have hr0 : r3Count (p ν).val = 0 := r3Count_eq_zero_of_mod_eight_eq_seven (hp_mod8 ν hlt)
      have hev : P.eval (y ν) = 0 := by
        have h1 := hrow ν
        rw [hr0, Nat.cast_zero, zero_div, add_zero] at h1
        simpa only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X] using h1
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPne).mpr hev)
    have hcard_le : J + 1 ≤ P.natDegree := by
      calc J + 1 = S₁.card := hS₁_card.symm
        _ = (S₁.image y).card := (Finset.card_image_of_injective S₁ hy_inj).symm
        _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
    omega
  -- Step 2: Coefficient of `X^J` in `P = 0` forces `w (J - 1) = 0`, so `deg(W) < J - 1`!
  have hw_top : w ⟨J - 1, by omega⟩ = 0 := by
    have hcoeffJ : P.coeff J = 0 := by rw [hP_zero, Polynomial.coeff_zero]
    simp only [P, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul] at hcoeffJ
    have hUJ : U.coeff J = 0 := by rw [hU_coeff]; simp
    have hX : (Polynomial.X * W).coeff J = W.coeff (J - 1) := by
      cases J with
      | zero => omega
      | succ J' => simp
    rw [hUJ, zero_add, hX, hW_coeff] at hcoeffJ
    have hlt : J - 1 < J := by omega
    simp only [hlt, ↓reduceDIte] at hcoeffJ
    exact (mul_eq_zero.mp hcoeffJ).resolve_left (by norm_num)
  -- Step 3: Remaining `J - 1` primes `≡ 1 (mod 4)` (with `r_3(p) ≥ 1`) force `W = 0`!
  have hW_zero : W = 0 := by
    by_cases hJ1 : J = 1
    · ext n
      rw [hW_coeff, Polynomial.coeff_zero]
      split_ifs with hn
      · have hn0 : n = 0 := by omega
        subst hn0
        have heq : (⟨0, hn⟩ : Fin J) = ⟨J - 1, by omega⟩ := Fin.ext (by omega)
        rw [heq]; exact hw_top
      · rfl
    · have hW_deg : W.natDegree ≤ J - 2 := by
        apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro n hn
        rw [hW_coeff]
        split_ifs with hlt
        · have heq : (⟨n, hlt⟩ : Fin J) = ⟨J - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [heq]; exact hw_top
        · rfl
      by_contra hWne
      let S₂ : Finset (Fin (2 * J)) := Finset.univ.filter fun ν ↦ J + 1 ≤ ν.val
      have hS₂_card : S₂.card = J - 1 := by
        let e₂ : Fin (J - 1) ≃ S₂ :=
          { toFun := fun k ↦ ⟨⟨J + 1 + k.val, by omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩⟩
            invFun := fun ν ↦ ⟨ν.val.val - (J + 1), by have := (Finset.mem_filter.mp ν.property).2; omega⟩
            left_inv := fun k ↦ Fin.ext (by dsimp; omega)
            right_inv := fun ν ↦ Subtype.ext (Fin.ext (by
              have := (Finset.mem_filter.mp ν.property).2; dsimp; omega)) }
        rw [← Fintype.card_coe, Fintype.card_congr e₂.symm, Fintype.card_fin]
      have hsub : S₂.image y ⊆ W.roots.toFinset := by
        intro z hz
        obtain ⟨ν, hνS, rfl⟩ := Finset.mem_image.mp hz
        have hge : J + 1 ≤ ν.val := (Finset.mem_filter.mp hνS).2
        have hrpos : 1 ≤ r3Count (p ν).val :=
          r3Count_pos_of_prime_mod_four_eq_one (hp_prime ν) (hp_mod4 ν hge)
        have hrow' := hrow ν
        have hPev : U.eval (y ν) + 6 * y ν * W.eval (y ν) = 0 := by
          have := congrArg (Polynomial.eval (y ν)) hP_zero
          simpa only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_zero] using this
        have hterm : ((r3Count (p ν).val : ℂ) / ((p ν).val : ℂ)) * W.eval (y ν) = 0 := by
          linear_combination hrow' - hPev
        have hratio_ne0 : ((r3Count (p ν).val : ℂ) / ((p ν).val : ℂ)) ≠ 0 :=
          div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (p ν).pos.ne')
        have hev : W.eval (y ν) = 0 := (mul_eq_zero.mp hterm).resolve_left hratio_ne0
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hWne).mpr hev)
      have hcard_le : J - 1 ≤ W.natDegree := by
        calc J - 1 = S₂.card := hS₂_card.symm
          _ = (S₂.image y).card := (Finset.card_image_of_injective S₂ hy_inj).symm
          _ ≤ W.roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ W.roots.card := Multiset.toFinset_card_le _
          _ ≤ W.natDegree := Polynomial.card_roots' W
      omega
  -- Step 4: `W = 0` and `P = 0` imply `U = 0`, hence `v = 0`!
  have hU_zero : U = 0 := by
    dsimp only [P] at hP_zero
    rw [hW_zero, mul_zero, add_zero] at hP_zero; exact hP_zero
  apply hv_ne
  ext k
  by_cases hk : k.val < J
  · have hu0 : u ⟨k.val, hk⟩ = 0 := by
      have h1 := congrArg (fun q : Polynomial ℂ ↦ q.coeff k.val) hU_zero
      rw [hU_coeff, Polynomial.coeff_zero] at h1
      simpa only [hk, ↓reduceDIte] using h1
    dsimp only [u] at hu0
    exact (mul_eq_zero.mp hu0).resolve_left (mul_ne_zero hC₁ (pow_ne_zero _ hβ))
  · have hkj : k.val - J < J := by omega
    have hw0 : w ⟨k.val - J, hkj⟩ = 0 := by
      have h1 := congrArg (fun q : Polynomial ℂ ↦ q.coeff (k.val - J)) hW_zero
      rw [hW_coeff, Polynomial.coeff_zero] at h1
      simpa only [hkj, ↓reduceDIte] using h1
    dsimp only [w] at hw0
    have hk_eq : (⟨J + (k.val - J), by omega⟩ : Fin (2 * J)) = k := Fin.ext (by dsimp; omega)
    rw [hk_eq] at hw0
    exact (mul_eq_zero.mp hw0).resolve_left (mul_ne_zero hC₃ (pow_ne_zero _ hβ))

/-- Decreasing-dilation core for joint differential independence of `(F_2(q^{a_i}), F_BEC^{(3)}(q^{a_i}))`. -/
private theorem logDeriv_bec1D_bec3D_dilations_diff_indep_dec {s : ℕ}
    (a : Fin s → ℕ+) (hdec : ∀ i j : Fin s, i < j → (a j).val < (a i).val) :
    let F : Fin s × Fin 2 → PowerSeries ℂ := fun ib ↦
      if ib.2.val = 0 then logDerivPowerPartDilated 2 (a ib.1).val
      else logDerivBec3DDilated (a ib.1).val
    AlgebraicIndependent ℂ (jointSeriesCoordinates (F ∘ finProdFinEquiv.symm)) := by
  classical
  intro F
  let A : ℕ := ∏ i : Fin s, (a i).val
  have hA_pos : 0 < A := Finset.prod_pos fun i _ ↦ (a i).pos
  have hA_dvd : ∀ i : Fin s, (a i).val ∣ A := fun i ↦
    Finset.dvd_prod_of_mem (fun k ↦ (a k).val) (Finset.mem_univ i)
  have hA_ge : ∀ i : Fin s, (a i).val ≤ A := fun i ↦ Nat.le_of_dvd hA_pos (hA_dvd i)
  have hdec_le : ∀ i j : Fin s, i ≤ j → (a j).val ≤ (a i).val := fun i j hij ↦ by
    rcases hij.eq_or_lt with rfl | hlt; exact le_rfl; exact (hdec i j hlt).le
  let _ : Algebra (Polynomial ℂ) RayGerm := (ppPolyToGerm 2).toAlgebra
  have hpoly_inj : Function.Injective (algebraMap (Polynomial ℂ) RayGerm) := ppPolyToGerm_injective (by decide)
  rw [algebraicIndependent_iff]
  intro Q hQ_eval
  let J : ℕ := (Q.vars.sup fun u ↦ Option.elim' 0 (fun ij ↦ ij.2) u) + 1
  have hJ : 1 ≤ J := Nat.succ_pos _
  have hQ_vars : ∀ u ∈ Q.vars, ∀ ij : Fin (s * 2) × ℕ, u = some ij → ij.2 < J := by
    intro u hu ij heq; subst heq
    have hle : ij.2 ≤ Q.vars.sup fun u ↦ Option.elim' 0 (fun p ↦ p.2) u :=
      Finset.le_sup (f := fun u ↦ Option.elim' 0 (fun p ↦ p.2) u) hu
    omega
  let ι := Fin s ×ₗ Fin (2 * J)
  let emb : Option ι → Option (Fin (s * 2) × ℕ) := Option.map fun r ↦
    let i := (ofLex r).1; let k := (ofLex r).2
    if k.val < J then (finProdFinEquiv (i, ⟨0, by decide⟩), k.val)
    else (finProdFinEquiv (i, ⟨1, by decide⟩), k.val - J)
  let liftVar : Option (Fin (s * 2) × ℕ) → Option ι
    | none => none
    | some (p, j) =>
      let ib := finProdFinEquiv.symm p
      if h : j < J then
        if ib.2.val = 0 then some (toLex (ib.1, ⟨j, by omega⟩))
        else some (toLex (ib.1, ⟨J + j, by omega⟩))
      else none
  let Q₀ : MvPolynomial (Option ι) ℂ := MvPolynomial.rename liftVar Q
  have hQ_eq : MvPolynomial.rename emb Q₀ = Q := by
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_eq_aeval]
    have hcongr : ∀ u ∈ Q.vars, emb (liftVar u) = u := fun u hu ↦ by
      cases u with
      | none => rfl
      | some pj =>
        rcases pj with ⟨p, j⟩
        have hj : j < J := hQ_vars (some (p, j)) hu (p, j) rfl
        dsimp only [liftVar]
        simp only [hj, ↓reduceDIte]
        set ib := finProdFinEquiv.symm p
        have hfin : ib.2 = ⟨0, by decide⟩ ∨ ib.2 = ⟨1, by decide⟩ := by
          rcases ib with ⟨i, b⟩; fin_cases b <;> simp
        rcases hfin with hb0 | hb1
        · have hbval : ib.2.val = 0 := by rw [hb0]
          simp only [hbval, ↓reduceIte, emb, Option.map_some, ofLex_toLex, hj]
          congr 1; ext
          · have hpair : (ib.1, (⟨0, by decide⟩ : Fin 2)) = ib := Prod.ext rfl hb0.symm
            rw [hpair]; simp [ib]; omega
          · rfl
        · have hbval : ib.2.val ≠ 0 := by rw [hb1]; decide
          have hnot : ¬ J + j < J := by omega
          simp only [hbval, ↓reduceIte, emb, Option.map_some, ofLex_toLex, hnot, Nat.add_sub_cancel_left]
          congr 1; ext
          · have hpair : (ib.1, (⟨1, by decide⟩ : Fin 2)) = ib := Prod.ext rfl hb1.symm
            rw [hpair]; simp [ib]; omega
          · rfl
    have h1 : MvPolynomial.aeval (MvPolynomial.X (R := ℂ) ∘ (emb ∘ liftVar)) Q =
        MvPolynomial.aeval (MvPolynomial.X (R := ℂ)) Q := by
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      apply Finset.sum_congr rfl; intro m hm; congr 1
      apply Finsupp.prod_congr; intro u hu
      simp only [Function.comp_apply, hcongr u ((MvPolynomial.mem_vars_iff_mem_support u).mpr ⟨m, hm, hu⟩)]
    rw [h1]
    exact congrFun (congrArg DFunLike.coe (MvPolynomial.aeval_X_left (R := ℂ) (σ := Option (Fin (s * 2) × ℕ)))) Q
  let Q₁ : MvPolynomial ι (Polynomial ℂ) := ppOptionToPolyMv ι Q₀
  let fTracked : ι → PPTracked 2 (ppDilKeyRate 2 A) := fun r ↦
    let i := (ofLex r).1; let k := (ofLex r).2
    if k.val < J then sqProfDilJetTracked powerPartTwoProfile hA_pos (a i) (hA_dvd i) k.val
    else sqProfDilJetTracked bec3DProfile hA_pos (a i) (hA_dvd i) (k.val - J)
  obtain ⟨E, hE_val, hE_marked⟩ := ppEvalPolyMv_tracked (d := 2) (by decide) hA_pos fTracked Q₁
  have hE_zero : ∀ᶠ X : ℝ in atTop, E.exp.value X = 0 := by
    have hall_f : ∀ᶠ X : ℝ in atTop, ∀ r : ι,
        (fTracked r).exp.value X =
          psValue (jointSeriesCoordinates (F ∘ finProdFinEquiv.symm) (emb (some r))) (qRayD 3 X) := by
      refine ((Filter.eventually_all_finset (Finset.univ : Finset ι)).mpr fun r _ ↦ ?_).mono
        fun X hX r ↦ hX r (Finset.mem_univ r)
      by_cases hk : (ofLex r).2.val < J
      · have hft : fTracked r =
            sqProfDilJetTracked powerPartTwoProfile hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1)
              (ofLex r).2.val := by simp [fTracked, hk]
        have hR : emb (some r) = some (finProdFinEquiv ((ofLex r).1, ⟨0, by decide⟩), (ofLex r).2.val) := by
          simp [emb, hk]
        filter_upwards [sqProfDilJetTracked_value powerPartTwoProfile hA_pos (a (ofLex r).1)
          (hA_dvd (ofLex r).1) (ofLex r).2.val] with X hX
        rw [hft, hX, hR]
        simp only [jointSeriesCoordinates, Function.comp_apply, Equiv.symm_apply_apply, F,
          ↓reduceIte, seriesDilated_logDerivPowerPart_two]
      · have hft : fTracked r =
            sqProfDilJetTracked bec3DProfile hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1)
              ((ofLex r).2.val - J) := by simp [fTracked, hk]
        have hR : emb (some r) = some (finProdFinEquiv ((ofLex r).1, ⟨1, by decide⟩), (ofLex r).2.val - J) := by
          simp [emb, hk]
        filter_upwards [sqProfDilJetTracked_value bec3DProfile hA_pos (a (ofLex r).1)
          (hA_dvd (ofLex r).1) ((ofLex r).2.val - J)] with X hX
        rw [hft, hX, hR]
        simp only [jointSeriesCoordinates, Function.comp_apply, Equiv.symm_apply_apply, F,
          one_ne_zero, ↓reduceIte, logDerivBec3DDilated]
    filter_upwards [eventually_gt_atTop (0 : ℝ), hE_val, hall_f] with X hX hEv hfv
    rw [hEv]
    let g_X : Option (Fin (s * 2) × ℕ) → ℂ := fun u ↦
      psValue (jointSeriesCoordinates (F ∘ finProdFinEquiv.symm) u) (qRayD 3 X)
    have hcongr_ev : MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD 3 X))
          (fun r ↦ (fTracked r).exp.value X) Q₁ =
        MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD 3 X))
          (fun r ↦ g_X (emb (some r))) Q₁ := by congr 1; funext r; exact hfv r
    rw [hcongr_ev, ppEval₂_optionToPolyMv]
    have hps_coord : Option.elim' (qRayD 3 X) (fun r ↦ g_X (emb (some r))) = g_X ∘ emb := by
      funext u; cases u with
      | none => exact (ps_nome_abs (qRayD 3 X)).2.symm
      | some r => rfl
    have habs_coord : ∀ u : Option (Fin (s * 2) × ℕ),
        PSAbsAt (jointSeriesCoordinates (F ∘ finProdFinEquiv.symm) u) (qRayD 3 X) := by
      rintro (_ | ⟨p, j⟩)
      · exact (ps_nome_abs _).1
      · dsimp only [jointSeriesCoordinates, Function.comp_apply, F]
        split_ifs
        · rw [← seriesDilated_logDerivPowerPart_two]
          exact sqProf_jet_abs powerPartTwoProfile _ j (qRayD_disk hX)
        · exact sqProf_jet_abs bec3DProfile _ j (qRayD_disk hX)
    rw [hps_coord, ← MvPolynomial.eval_rename emb g_X Q₀, hQ_eq]
    have hps := (ps_polynomial_value Q habs_coord).2
    rw [← hps, hQ_eval]; simp [psValue, psTerm]
  have hmarked_zero : MvPolynomial.aeval (R := Polynomial ℂ) (fun r ↦ (fTracked r).marked) Q₁ = 0 := by
    rw [← hE_marked]; exact E.separate_zero hE_zero
  -- Choose `s * (2J)` pairwise distinct primes `> A`: in each block, first `J + 1` are `7 mod 8`, last `J - 1` are `1 mod 4`!
  let idxEquiv : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let primeOf (r : ι) : ℕ+ :=
    if (ofLex r).2.val < J + 1 then
      ⟨apPrimeSeq A 8 7 (by decide) (by decide) (idxEquiv r).val,
        (apPrimeSeq_spec A 8 7 (by decide) (by decide) _).2.1.pos⟩
    else
      ⟨apPrimeSeq A 4 1 (by decide) (by decide) (idxEquiv r).val,
        (apPrimeSeq_spec A 4 1 (by decide) (by decide) _).2.1.pos⟩
  have hprime_prime (r : ι) : (primeOf r).val.Prime := by
    by_cases h : (ofLex r).2.val < J + 1
    · simp only [primeOf, h, ↓reduceIte]
      exact (apPrimeSeq_spec A 8 7 (by decide) (by decide) _).2.1
    · simp only [primeOf, h, ↓reduceIte]
      exact (apPrimeSeq_spec A 4 1 (by decide) (by decide) _).2.1
  have hprime_gt_A (r : ι) : A < (primeOf r).val := by
    by_cases h : (ofLex r).2.val < J + 1
    · simp only [primeOf, h, ↓reduceIte]
      exact (apPrimeSeq_spec A 8 7 (by decide) (by decide) _).1
    · simp only [primeOf, h, ↓reduceIte]
      exact (apPrimeSeq_spec A 4 1 (by decide) (by decide) _).1
  have hprime_mod8 (r : ι) (h : (ofLex r).2.val < J + 1) : (primeOf r).val % 8 = 7 := by
    simp only [primeOf, h, ↓reduceIte]
    exact (apPrimeSeq_spec A 8 7 (by decide) (by decide) _).2.2.1
  have hprime_mod4 (r : ι) (h : J + 1 ≤ (ofLex r).2.val) : (primeOf r).val % 4 = 1 := by
    have hnot : ¬ (ofLex r).2.val < J + 1 := by omega
    simp only [primeOf, hnot, ↓reduceIte]
    exact (apPrimeSeq_spec A 4 1 (by decide) (by decide) _).2.2.1
  have hprime_inj : Function.Injective primeOf := by
    intro r₁ r₂ h
    have hval : (primeOf r₁).val = (primeOf r₂).val := congrArg Subtype.val h
    by_cases h1 : (ofLex r₁).2.val < J + 1 <;> by_cases h2 : (ofLex r₂).2.val < J + 1
    · simp only [primeOf, h1, h2, ↓reduceIte] at hval
      exact idxEquiv.injective (Fin.ext ((apPrimeSeq_strictMono A 8 7 (by decide) (by decide)).injective hval))
    · have hm1 := hprime_mod8 r₁ h1
      have hm2 := hprime_mod4 r₂ (by omega)
      omega
    · have hm1 := hprime_mod4 r₁ (by omega)
      have hm2 := hprime_mod8 r₂ h2
      omega
    · simp only [primeOf, h1, h2, ↓reduceIte] at hval
      exact idxEquiv.injective (Fin.ext ((apPrimeSeq_strictMono A 4 1 (by decide) (by decide)).injective hval))
  let marks : ι → Core 2 := fun r ↦ ppDilCore (by decide) (a (ofLex r).1) (primeOf r)
  have hmarks_inj : Function.Injective marks := fun r₁ r₂ h ↦ by
    have h1 := (ppDilCore_prime_dvd_iff (d := 2) (by decide) (a (ofLex r₁).1) (primeOf r₁) (hprime_prime r₁)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₁))).1
    rw [show ppDilCore (d := 2) (by decide) (a (ofLex r₁).1) (primeOf r₁) = marks r₁ from rfl, h] at h1
    have h2 := ((ppDilCore_prime_dvd_iff (d := 2) (by decide) (a (ofLex r₂).1) (primeOf r₂) (hprime_prime r₂)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₂))).2 (primeOf r₁).val (hprime_prime r₁)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₁))).mp h1
    exact hprime_inj (PNat.eq h2)
  let restr : MvPowerSeries (Core 2) RayGerm →+* MvPowerSeries ι RayGerm :=
    restrictVars marks hmarks_inj
  let fRestr : ι → MvPowerSeries ι RayGerm := fun r ↦ restr (fTracked r).marked
  let Jac : Matrix ι ι (MvPowerSeries ι RayGerm) :=
    Matrix.of fun r c ↦ MvPowerSeries.pderiv r (fRestr c)
  have hJac_single : ∀ (r c : ι) (m : ι →₀ ℕ),
      MvPowerSeries.coeff m (Jac r c) ≠ 0 →
        ∃ N : ℕ+, ppDilCore (d := 2) (by decide) (a (ofLex c).1) N = marks r ∧
          m = Finsupp.single r (ppDilExp (d := 2) (by decide) A (a (ofLex c).1) N - 1) := by
    intro r c m hm
    change MvPowerSeries.coeff m (MvPowerSeries.pderiv r (fRestr c)) ≠ 0 at hm
    rw [MvPowerSeries.coeff_pderiv] at hm
    have hc_nz : MvPowerSeries.coeff ((m + Finsupp.single r 1).mapDomain marks) (fTracked c).marked ≠ 0 :=
      left_ne_zero_of_mul hm
    have hmap_ne0 : (m + Finsupp.single r 1).mapDomain marks ≠ 0 := fun h0 ↦ by
      have h1 := DFunLike.congr_fun h0 (marks r)
      rw [ppMapDomain_apply_inj hmarks_inj, Finsupp.add_apply, Finsupp.single_eq_same] at h1
      simp at h1
    have hex : ∃ N : ℕ+, (m + Finsupp.single r 1).mapDomain marks = ppDilModeExp (by decide) A (a (ofLex c).1) N := by
      dsimp only [fTracked] at hc_nz
      split_ifs at hc_nz with hc
      · rw [sqProfDilJetTracked_marked_eq, map_sum] at hc_nz
        obtain ⟨ℓ, _, hℓ_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc_nz
        rw [MvPowerSeries.coeff_C_mul] at hℓ_nz
        have hadd_nz := right_ne_zero_of_mul hℓ_nz
        rw [map_add, MvPowerSeries.coeff_C] at hadd_nz
        simp only [hmap_ne0, ↓reduceIte, zero_add] at hadd_nz
        by_contra hnot; push Not at hnot
        exact hadd_nz ((sqProfDilWaveTracked_coeff powerPartTwoProfile hA_pos (a (ofLex c).1) (hA_dvd (ofLex c).1) ℓ _).1 hnot)
      · rw [sqProfDilJetTracked_marked_eq, map_sum] at hc_nz
        obtain ⟨ℓ, _, hℓ_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc_nz
        rw [MvPowerSeries.coeff_C_mul] at hℓ_nz
        have hadd_nz := right_ne_zero_of_mul hℓ_nz
        rw [map_add, MvPowerSeries.coeff_C] at hadd_nz
        simp only [hmap_ne0, ↓reduceIte, zero_add] at hadd_nz
        by_contra hnot; push Not at hnot
        exact hadd_nz ((sqProfDilWaveTracked_coeff bec3DProfile hA_pos (a (ofLex c).1) (hA_dvd (ofLex c).1) ℓ _).1 hnot)
    obtain ⟨N, hN⟩ := hex
    have hcore_eq : ppDilCore (by decide) (a (ofLex c).1) N = marks r := by
      by_contra hne_c
      have h1 := DFunLike.congr_fun hN (marks r)
      rw [ppMapDomain_apply_inj hmarks_inj, Finsupp.add_apply, Finsupp.single_eq_same,
          ppDilModeExp, Finsupp.single_eq_of_ne (Ne.symm hne_c)] at h1
      omega
    have hm_single : m = Finsupp.single r (ppDilExp (d := 2) (by decide) A (a (ofLex c).1) N - 1) := by
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
    (fun r ↦ ppDilExp (d := 2) (by decide) A (a (ofLex r).1) (primeOf r) - 1) (fun _ _ ↦ Finset.mem_univ _)
  have hmStar_apply (r : ι) : mStar r = ppDilExp (d := 2) (by decide) A (a (ofLex r).1) (primeOf r) - 1 := rfl
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
        · have hr_lt_r₀ : r < r₀ := Prod.Lex.left _ _ (show (ofLex r).1 < (ofLex r₀).1 by
            exact Fin.lt_def.mpr (by omega))
          have hmr_eq : m r = mStar r := hprefix r hr_lt_r₀
          obtain ⟨N, hcore, hm_single⟩ := hJac_single r (π.symm r) _ (hrow_nz r)
          have hmr_val : m r = ppDilExp (d := 2) (by decide) A (a (ofLex (π.symm r)).1) N - 1 := by
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
          have hdom := ppDil_block_dominance (d := 2) (by decide) hA_pos (hA_dvd (ofLex r).1)
            (hA_dvd (ofLex (π.symm r)).1) (hprime_prime r)
            (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r)) (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r))
            hle_a hcore
          have he_eq : ppDilExp (d := 2) (by decide) A (a (ofLex (π.symm r)).1) N =
              ppDilExp (d := 2) (by decide) A (a (ofLex r).1) (primeOf r) := by
            have h1 := ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd (ofLex r).1) (primeOf r)
            have h2 := ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd (ofLex (π.symm r)).1) N
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
    have hmr₀ : m r₀ = ppDilExp (d := 2) (by decide) A (a (ofLex (π.symm r₀)).1) N₀ - 1 := by
      have := DFunLike.congr_fun hm_single₀ r₀; simpa only [Finsupp.single_eq_same] using this
    have hdom₀ := (ppDil_block_dominance (d := 2) (by decide) hA_pos (hA_dvd (ofLex r₀).1)
      (hA_dvd (ofLex (π.symm r₀)).1) (hprime_prime r₀)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₀)) (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₀))
      (hdec_le _ _ hge_r₀) hcore₀).1
    have hlt_r₀' : m r₀ < ppDilExp (d := 2) (by decide) A (a (ofLex r₀).1) (primeOf r₀) - 1 := hr₀_lt
    omega
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
    have hmr : mStar r = ppDilExp (d := 2) (by decide) A (a (ofLex c).1) N - 1 := by
      have := DFunLike.congr_fun hm_single r; simpa only [Finsupp.single_eq_same] using this
    have hdom := ppDil_block_dominance (d := 2) (by decide) hA_pos (hA_dvd (ofLex r).1)
      (hA_dvd (ofLex c).1) (hprime_prime r)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r)) (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r))
      (hdec_le _ _ hlt.le) hcore
    have he_eq : ppDilExp (d := 2) (by decide) A (a (ofLex c).1) N =
        ppDilExp (d := 2) (by decide) A (a (ofLex r).1) (primeOf r) := by
      have h1 := ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd (ofLex r).1) (primeOf r)
      have h2 := ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd (ofLex c).1) N
      rw [hmStar_apply] at hmr; omega
    exact (hdec (ofLex r).1 (ofLex c).1 hlt).ne (congrArg Subtype.val (hdom.2 he_eq).1)
  have hB_det : B.det = ∏ i : Fin s, (Matrix.of fun ν k : Fin (2 * J) ↦ B (toLex (i, ν)) (toLex (i, k))).det := by
    rw [← Matrix.det_transpose, hB_tri.det_fintype]
    apply Finset.prod_congr rfl; intro i _
    let e : {x : ι // blk x = i} ≃ Fin (2 * J) :=
      { toFun := fun x ↦ (ofLex x.val).2
        invFun := fun ν ↦ ⟨toLex (i, ν), rfl⟩
        left_inv := fun ⟨x, hx⟩ ↦ Subtype.ext (ofLex.injective (Prod.ext hx.symm rfl))
        right_inv := fun _ ↦ rfl }
    rw [← Matrix.det_reindex_self e (Bᵀ.toSquareBlock blk i), ← Matrix.det_transpose]; rfl
  have hblock_unit (i : Fin s) :
      IsUnit (Matrix.of fun ν k : Fin (2 * J) ↦ B (toLex (i, ν)) (toLex (i, k))).det := by
    let σ := ppDilScale 2 (a i).val
    let hσ := ppDilScale_pos (d := 2) (a i).pos
    let M (X : ℝ) : Matrix (Fin (2 * J)) (Fin (2 * J)) ℂ := Matrix.of fun ν k ↦
      ((ppDilExp (d := 2) (by decide) A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
        if k.val < J then
          ∑ ℓ ∈ Finset.range (k.val + 1),
            qPolyCoeff 3 k.val ℓ X *
              (sqProfDilWaveExp powerPartTwoProfile σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf (toLex (i, ν))) X
        else
          ∑ ℓ ∈ Finset.range (k.val - J + 1),
            qPolyCoeff 3 (k.val - J) ℓ X *
              (sqProfDilWaveExp bec3DProfile σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf (toLex (i, ν))) X
    have hB_eq (ν k : Fin (2 * J)) : B (toLex (i, ν)) (toLex (i, k)) = Germ.ofFun (fun X ↦ M X ν k) := by
      let r := toLex (i, ν); let c := toLex (i, k)
      change MvPowerSeries.coeff (Finsupp.single r (mStar r)) (MvPowerSeries.pderiv r (fRestr c)) = _
      rw [MvPowerSeries.coeff_pderiv]
      have he_pos := ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd i) (primeOf r)
      have hsucc : mStar r + 1 = ppDilExp (d := 2) (by decide) A (a i) (primeOf r) := Nat.sub_add_cancel he_pos
      have hadd_s : Finsupp.single r (mStar r) + Finsupp.single r 1 =
          Finsupp.single r (ppDilExp (d := 2) (by decide) A (a i) (primeOf r)) := by
        rw [← Finsupp.single_add, hsucc]
      have hmap_s : (Finsupp.single r (ppDilExp (d := 2) (by decide) A (a i) (primeOf r))).mapDomain marks =
          ppDilModeExp (by decide) A (a i) (primeOf r) := by rw [Finsupp.mapDomain_single]; rfl
      have hmode_ne0 : ppDilModeExp (d := 2) (by decide) A (a i) (primeOf r) ≠ 0 := fun h0 ↦ by
        have := DFunLike.congr_fun h0 (ppDilCore (d := 2) (by decide) (a i) (primeOf r))
        simp only [ppDilModeExp, Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at this
        exact he_pos.ne' this
      rw [Finsupp.single_eq_same, hadd_s]
      change MvPowerSeries.coeff ((Finsupp.single r (ppDilExp (d := 2) (by decide) A (a i) (primeOf r))).mapDomain marks)
        (fTracked c).marked * ((mStar r : RayGerm) + 1) = _
      rw [hmap_s]
      have hnat : ((mStar r : RayGerm) + 1) =
          Germ.ofFun (fun _ : ℝ ↦ ((ppDilExp (d := 2) (by decide) A (a i) (primeOf r) : ℕ) : ℂ)) := by
        rw [show ((mStar r : RayGerm) + 1) = ((mStar r + 1 : ℕ) : RayGerm) by push_cast; rfl, hsucc]; rfl
      let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
      by_cases hk : k.val < J
      · have hfc : fTracked c = sqProfDilJetTracked powerPartTwoProfile hA_pos (a i) (hA_dvd i) k.val := by
          simp [fTracked, c, hk]
        rw [hfc, sqProfDilJetTracked_marked_eq, map_sum]
        have hterm_eq (ℓ : ℕ) :
            MvPowerSeries.coeff (ppDilModeExp (by decide) A (a i) (primeOf r))
              (MvPowerSeries.C (Germ.ofFun (qPolyCoeff 3 k.val ℓ)) *
                (MvPowerSeries.C (Germ.ofFun (sqProfDilPolarCoeff powerPartTwoProfile σ hσ ℓ).value) +
                  (sqProfDilWaveTracked powerPartTwoProfile hA_pos (a i) (hA_dvd i) ℓ).marked)) =
            Germ.ofFun (fun X ↦ qPolyCoeff 3 k.val ℓ X *
              (sqProfDilWaveExp powerPartTwoProfile σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf r) X) := by
          rw [MvPowerSeries.coeff_C_mul, map_add, MvPowerSeries.coeff_C]
          simp only [hmode_ne0, ↓reduceIte, zero_add]
          rw [(sqProfDilWaveTracked_coeff powerPartTwoProfile hA_pos (a i) (hA_dvd i) ℓ _).2 (primeOf r) rfl]; rfl
        rw [Finset.sum_congr rfl (fun ℓ _ ↦ hterm_eq ℓ), hnat, mul_comm]
        change H _ * ∑ ℓ ∈ Finset.range (k.val + 1), H _ = _
        rw [← map_sum, ← map_mul]; apply Germ.coe_eq.mpr
        filter_upwards with X
        simp only [M, Matrix.of_apply, hk, ↓reduceIte, Pi.mul_apply, Finset.sum_apply]; rfl
      · have hfc : fTracked c = sqProfDilJetTracked bec3DProfile hA_pos (a i) (hA_dvd i) (k.val - J) := by
          simp [fTracked, c, hk]
        rw [hfc, sqProfDilJetTracked_marked_eq, map_sum]
        have hterm_eq (ℓ : ℕ) :
            MvPowerSeries.coeff (ppDilModeExp (by decide) A (a i) (primeOf r))
              (MvPowerSeries.C (Germ.ofFun (qPolyCoeff 3 (k.val - J) ℓ)) *
                (MvPowerSeries.C (Germ.ofFun (sqProfDilPolarCoeff bec3DProfile σ hσ ℓ).value) +
                  (sqProfDilWaveTracked bec3DProfile hA_pos (a i) (hA_dvd i) ℓ).marked)) =
            Germ.ofFun (fun X ↦ qPolyCoeff 3 (k.val - J) ℓ X *
              (sqProfDilWaveExp bec3DProfile σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf r) X) := by
          rw [MvPowerSeries.coeff_C_mul, map_add, MvPowerSeries.coeff_C]
          simp only [hmode_ne0, ↓reduceIte, zero_add]
          rw [(sqProfDilWaveTracked_coeff bec3DProfile hA_pos (a i) (hA_dvd i) ℓ _).2 (primeOf r) rfl]; rfl
        rw [Finset.sum_congr rfl (fun ℓ _ ↦ hterm_eq ℓ), hnat, mul_comm]
        change H _ * ∑ ℓ ∈ Finset.range (k.val - J + 1), H _ = _
        rw [← map_sum, ← map_mul]; apply Germ.coe_eq.mpr
        filter_upwards with X
        simp only [M, Matrix.of_apply, hk, ↓reduceIte, Pi.mul_apply, Finset.sum_apply]; rfl
    have hdet_germ : (Matrix.of fun ν k : Fin (2 * J) ↦ B (toLex (i, ν)) (toLex (i, k))).det =
        Germ.ofFun (fun X ↦ (M X).det) := by
      let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
      have hmat : (Matrix.of fun ν k : Fin (2 * J) ↦ B (toLex (i, ν)) (toLex (i, k))) =
          H.mapMatrix (Matrix.of fun ν k : Fin (2 * J) ↦ fun X ↦ M X ν k) := by ext ν k; exact hB_eq ν k
      rw [hmat, ← RingHom.map_det]; apply Germ.coe_eq.mpr
      filter_upwards with X
      simp only [Matrix.det_apply, Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, Matrix.of_apply]
    rw [hdet_germ]
    let colScale (X : ℝ) (k : Fin (2 * J)) : ℂ :=
      if k.val < J then ((X ^ (-((3 * k.val : ℕ) : ℝ) - (3 : ℝ)) : ℝ) : ℂ)
      else ((X ^ (-((3 * (k.val - J) : ℕ) : ℝ) - (4 : ℝ)) : ℝ) : ℂ)
    let Mscaled (X : ℝ) : Matrix (Fin (2 * J)) (Fin (2 * J)) ℂ := Matrix.of fun ν k ↦ colScale X k * M X ν k
    let eν (ν : Fin (2 * J)) : ℂ :=
      ((ppDilExp (d := 2) (by decide) A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ)
    let C₁ : ℂ := -(1 / 2 : ℂ) * sqRay0 * ((σ : ℂ) ^ 3)
    let C₃ : ℂ := (-2 * (Real.pi : ℂ) ^ 2 * I) * ((σ : ℂ) ^ 4)
    let β : ℂ := -(((2 : ℂ)⁻¹) * (((σ : ℝ) : ℂ) * sqRay0))
    let L : Matrix (Fin (2 * J)) (Fin (2 * J)) ℂ := Matrix.of fun ν k ↦
      if k.val < J then
        eν ν * (C₁ * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) *
          (β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) ^ k.val
      else
        eν ν * (C₃ * ((bec3DWaveMult (primeOf (toLex (i, ν))).val : ℝ) : ℂ)) *
          (β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) ^ (k.val - J)
    have hrate_eq (ν : Fin (2 * J)) :
        ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν))) =
          (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ) * sqRay0 := by
      simp only [ppWaveRate, ppRay_two_zero]
      congr 2; rw [Real.sqrt_eq_rpow]; norm_num
    have hlim_entry (ν k : Fin (2 * J)) : Tendsto (fun X ↦ Mscaled X ν k) atTop (𝓝 (L ν k)) := by
      -- Unified column limit helper for any `SqRayProfile`!
      have hcol_lim {F' : PowerSeries ℂ} (P' : SqRayProfile F') (j : ℕ) :
          Tendsto (fun X : ℝ ↦
            ((X ^ (-((3 * j : ℕ) : ℝ) - (P'.scalePow : ℝ)) : ℝ) : ℂ) *
              (eν ν * ∑ ℓ ∈ Finset.range (j + 1),
                qPolyCoeff 3 j ℓ X *
                  (sqProfDilWaveExp P' σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf (toLex (i, ν))) X))
          atTop (𝓝 (eν ν * (P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ P'.scalePow)) *
            (β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) ^ j)) := by
        have hterm (ℓ : ℕ) (hℓ : ℓ ∈ Finset.range (j + 1)) :
            Tendsto (fun X : ℝ ↦
              ((X ^ (-((3 * j : ℕ) : ℝ) - (P'.scalePow : ℝ)) : ℝ) : ℂ) *
                (qPolyCoeff 3 j ℓ X *
                  (sqProfDilWaveExp P' σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf (toLex (i, ν))) X))
            atTop (𝓝 (if ℓ = j then
              P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ P'.scalePow) *
                (β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) ^ j else 0)) := by
          have hℓ_le : ℓ ≤ j := by have := Finset.mem_range.mp hℓ; omega
          have hamp_lim := (sqDilAmp_limit P'.scalePow σ (ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν)))) ℓ).const_mul
            (P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))))
          by_cases hℓj : ℓ = j
          · subst ℓ; simp only [↓reduceIte]
            have hprod := (qPolyCoeff_diag_limit (d := 3) (by decide) j).mul hamp_lim
            have hlim_eq : ((((3 - 1 : ℕ) : ℂ)⁻¹) ^ j) *
                (P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
                  (((σ : ℂ) ^ P'.scalePow) *
                    (-(((σ : ℝ) : ℂ) * ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν))))) ^ j)) =
                P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ P'.scalePow) *
                  (β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) ^ j := by
              rw [show ((3 - 1 : ℕ) : ℂ) = 2 by norm_num, hrate_eq ν]
              have hbase : β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ) =
                  (2 : ℂ)⁻¹ * (-(((σ : ℝ) : ℂ) * ((Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ) * sqRay0))) := by
                dsimp only [β]; ring
              rw [hbase, mul_pow]; ring
            rw [hlim_eq] at hprod
            refine hprod.congr' ?_
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
            have hcol : ((X ^ (-((3 * j : ℕ) : ℝ) - (P'.scalePow : ℝ)) : ℝ) : ℂ) =
                ((X ^ (-((3 * j : ℕ) : ℝ)) : ℝ) : ℂ) * ((X ^ (-(P'.scalePow : ℝ)) : ℝ) : ℂ) := by
              rw [← Complex.ofReal_mul, ← Real.rpow_add hX, sub_eq_add_neg]
            rw [hcol]
            change ((X ^ (-((3 * j : ℕ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff 3 j j X *
              (P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
                (((X ^ (-(P'.scalePow : ℝ)) : ℝ) : ℂ) *
                  sqDilAmp P'.scalePow σ (ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν)))) j X)) = _
            simp only [sqProfDilWaveExp]; ring
          · simp only [hℓj, ↓reduceIte]
            have hlt : (((3 : ℤ) * (j : ℤ)) - ((j - ℓ : ℕ) : ℤ)) < (((3 * j : ℕ) : ℤ)) := by
              have : 0 < j - ℓ := by omega
              push_cast; omega
            have hprod := ((qPolyCoeff_QCoeff (d := 3) (by decide) j ℓ hℓ_le).tendsto_zero_of_lt (by decide) hlt).mul hamp_lim
            rw [zero_mul] at hprod
            refine hprod.congr' ?_
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
            have hcol : ((X ^ (-((3 * j : ℕ) : ℝ) - (P'.scalePow : ℝ)) : ℝ) : ℂ) =
                ((X ^ (-(((3 * j : ℕ) : ℤ) : ℝ)) : ℝ) : ℂ) * ((X ^ (-(P'.scalePow : ℝ)) : ℝ) : ℂ) := by
              rw [← Complex.ofReal_mul, ← Real.rpow_add hX, Int.cast_natCast, sub_eq_add_neg]
            rw [hcol]
            change ((X ^ (-(((3 * j : ℕ) : ℤ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff 3 j ℓ X *
              (P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
                (((X ^ (-(P'.scalePow : ℝ)) : ℝ) : ℂ) *
                  sqDilAmp P'.scalePow σ (ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν)))) ℓ X)) = _
            simp only [sqProfDilWaveExp]; ring
        have hsum := (tendsto_finsetSum (Finset.range (j + 1)) hterm).const_mul (eν ν)
        rw [Finset.sum_ite_eq' (Finset.range (j + 1)) j] at hsum
        simp only [Finset.mem_range.mpr (Nat.lt_succ_self j), ↓reduceIte] at hsum
        rw [show eν ν * (P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ P'.scalePow) *
            (β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) ^ j) =
            eν ν * (P'.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ P'.scalePow)) *
            (β * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ)) ^ j by ring] at hsum
        refine hsum.congr fun X ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ℓ _; ring
      by_cases hk : k.val < J
      · have h1 := hcol_lim powerPartTwoProfile k.val
        have hamp1 : powerPartTwoProfile.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ 3) =
            C₁ * (Real.sqrt ((primeOf (toLex (i, ν))).val : ℝ) : ℂ) := by
          simp only [powerPartTwoProfile, powerPartMult_prime (d := 2) (by decide) (hprime_prime (toLex (i, ν))),
            Complex.ofReal_one, mul_one, hrate_eq ν, C₁]
          ring
        rw [show powerPartTwoProfile.scalePow = 3 from rfl, hamp1] at h1
        dsimp only [L, Matrix.of_apply]; simp only [hk, ↓reduceIte]
        refine h1.congr fun X ↦ ?_
        simp only [Mscaled, M, colScale, Matrix.of_apply, hk, ↓reduceIte, eν]; ring
      · have h3 := hcol_lim bec3DProfile (k.val - J)
        have hamp3 : bec3DProfile.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ 4) =
            C₃ * ((bec3DWaveMult (primeOf (toLex (i, ν))).val : ℝ) : ℂ) := by
          simp only [bec3DProfile, ↓reduceIte, C₃]; ring
        rw [show bec3DProfile.scalePow = 4 from rfl, hamp3] at h3
        dsimp only [L, Matrix.of_apply]; simp only [hk, ↓reduceIte]
        refine h3.congr fun X ↦ ?_
        simp only [Mscaled, M, colScale, Matrix.of_apply, hk, ↓reduceIte, eν]; ring
    have hlim_det := ppTendsto_matrix_det Mscaled L hlim_entry
    have hL_det_ne0 : L.det ≠ 0 := by
      have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
      have hsq0 : sqRay0 ≠ 0 := by
        rw [← ppRay_two_zero]; exact ppExtremeRay_ne_zero (by decide)
      have hC₁ : C₁ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hsq0) (pow_ne_zero 3 hσ0)
      have hC₃ : C₃ ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
          (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) Complex.I_ne_zero) (pow_ne_zero 4 hσ0)
      have hβ : β ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero two_ne_zero) (mul_ne_zero hσ0 hsq0))
      exact bec1D_bec3D_block_det_ne_zero hJ
        (fun ν ↦ primeOf (toLex (i, ν)))
        (fun ν₁ ν₂ h ↦ congrArg (fun x ↦ (ofLex x).2) (hprime_inj h))
        (fun ν ↦ hprime_prime (toLex (i, ν)))
        (fun ν hlt ↦ hprime_mod8 (toLex (i, ν)) hlt)
        (fun ν hge ↦ hprime_mod4 (toLex (i, ν)) hge)
        eν
        (fun ν ↦ by dsimp only [eν]; exact_mod_cast (ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd i) _).ne')
        C₁ C₃ β hC₁ hC₃ hβ
    have hev_nz : ∀ᶠ X : ℝ in atTop, (M X).det ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), hlim_det.eventually_ne hL_det_ne0] with X _ hsc
      have hsc_eq : Mscaled X = M X * Matrix.diagonal (colScale X) := by
        ext ν k; simp only [Mscaled, Matrix.of_apply, Matrix.mul_diagonal]; ring
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
  have hrestr_alg (P_mv : MvPolynomial ι (Polynomial ℂ)) :
      MvPolynomial.aeval (R := Polynomial ℂ) fRestr P_mv =
        restr (MvPolynomial.aeval (R := Polynomial ℂ) (fun r ↦ (fTracked r).marked) P_mv) := by
    induction P_mv using MvPolynomial.induction_on with
    | C R =>
      simp only [MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply]
      exact (restrictVars_C marks hmarks_inj (algebraMap (Polynomial ℂ) RayGerm R)).symm
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p r hp => simp only [map_mul, MvPolynomial.aeval_X, hp]; rfl
  have hQ₁_zero : Q₁ = 0 := (algebraicIndependent_iff.mp hindep) Q₁ (by rw [hrestr_alg, hmarked_zero, map_zero])
  have hQ₀_zero : Q₀ = 0 := ppOptionToPolyMv_injective ι (hQ₁_zero.trans (map_zero _).symm)
  rw [← hQ_eq, hQ₀_zero, map_zero]

/-- **100% UNCONDITIONAL Joint Differential Independence of ALL 1D and 3D BEC Log-Derivative Dilations
`{F_2(q^{a_1}), …, F_2(q^{a_s}), F_BEC^{(3)}(q^{a_1}), …, F_BEC^{(3)}(q^{a_s})}` over `ℂ(q)`**! -/
theorem logDeriv_bec1D_bec3D_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    let F : Fin s × Fin 2 → PowerSeries ℂ := fun ib ↦
      if ib.2.val = 0 then logDerivPowerPartDilated 2 (a ib.1).val
      else logDerivBec3DDilated (a ib.1).val
    AlgebraicIndependent ℂ (jointSeriesCoordinates (F ∘ finProdFinEquiv.symm)) := by
  classical
  intro F
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
  have hindep_dec := logDeriv_bec1D_bec3D_dilations_diff_indep_dec (a ∘ π) hdec
  let eIdx : Fin (s * 2) ≃ Fin (s * 2) :=
    finProdFinEquiv.symm.trans ((π.prodCongr (Equiv.refl (Fin 2))).trans finProdFinEquiv)
  let e : Option (Fin (s * 2) × ℕ) ≃ Option (Fin (s * 2) × ℕ) :=
    Equiv.optionCongr (eIdx.prodCongr (Equiv.refl ℕ))
  have hcomp :
      jointSeriesCoordinates
          ((fun ib : Fin s × Fin 2 ↦
            if ib.2.val = 0 then logDerivPowerPartDilated 2 ((a ∘ π) ib.1).val
            else logDerivBec3DDilated ((a ∘ π) ib.1).val) ∘ finProdFinEquiv.symm) =
        jointSeriesCoordinates (F ∘ finProdFinEquiv.symm) ∘ e := by
    funext u; cases u with
    | none => rfl
    | some pj =>
      rcases pj with ⟨p, j⟩
      simp only [jointSeriesCoordinates, Function.comp_apply, e, Equiv.optionCongr_apply,
        Option.map_some, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, eIdx,
        Equiv.trans_apply, Equiv.symm_apply_apply, F, Prod.map_fst, Prod.map_snd]
  dsimp only at hindep_dec
  rw [hcomp] at hindep_dec
  exact (algebraicIndependent_equiv' e rfl).mp hindep_dec

/-- **100% UNCONDITIONAL Joint Differential Independence of ALL 1D & 3D Bose Dilations
`{P_2(q^{a_i}), Z_BEC^{(3)}(q^{a_i})}` over `ℂ(q)`**! -/
theorem bec1D_bec3D_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    let P : Fin s × Fin 2 → PowerSeries ℂ := fun ib ↦
      if ib.2.val = 0 then powerPartDilated 2 (a ib.1).val
      else bec3DDilated (a ib.1).val
    AlgebraicIndependent ℂ (jointSeriesCoordinates (P ∘ finProdFinEquiv.symm)) := by
  intro P
  let F : Fin s × Fin 2 → PowerSeries ℂ := fun ib ↦
    if ib.2.val = 0 then logDerivPowerPartDilated 2 (a ib.1).val
    else logDerivBec3DDilated (a ib.1).val
  refine kolchin_logDeriv_joint_indep
    (F ∘ finProdFinEquiv.symm)
    (P ∘ finProdFinEquiv.symm)
    (fun p ↦ ((a (finProdFinEquiv.symm p).1).val : ℂ))
    (fun p ↦ by
      dsimp only [Function.comp_apply, P]
      split_ifs
      · exact powerPartDilated_ne_zero 2 _
      · exact bec3DDilated_ne_zero _)
    (fun p ↦ by exact_mod_cast (a (finProdFinEquiv.symm p).1).pos.ne')
    (fun p ↦ by
      dsimp only [Function.comp_apply, F, P]
      split_ifs
      · exact X_mul_deriv_powerPartDilated (by decide) (a _).pos
      · exact X_mul_deriv_bec3DDilated (a _).pos)
    (logDeriv_bec1D_bec3D_dilations_diff_indep a ha)

/-- **100% UNCONDITIONAL Joint Differential Independence of ALL FOUR Physical Ideal Quantum Gases
at a Single Temperature Variable**:
`(Z_BEC^{(1)}(q), Z_FD^{(1)}(q), Z_BEC^{(3)}(q), Z_FD^{(3)}(q))` are **jointly differentially
independent over `ℂ(q)`**! -/
theorem quantumGases_1D_3D_bose_fermi_joint_diff_indep :
    AlgebraicIndependent ℂ
      (jointSeriesCoordinates ![bec1DGas, fermi1DGas, bec3DSeries, fermi3DSeries]) := by
  let a : Fin 2 → ℕ+ := ![1, 2]
  have ha : Function.Injective a := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [a]
  let F : Fin 2 × Fin 2 → PowerSeries ℂ := fun ib ↦
    if ib.2.val = 0 then logDerivPowerPartDilated 2 (a ib.1).val
    else logDerivBec3DDilated (a ib.1).val
  let U : Fin 2 × Fin 2 → (PowerSeries ℂ)ˣ := fun ib ↦
    if ib.2.val = 0 then (isUnit_powerPartDilated 2 (a ib.1).val).unit
    else (isUnit_bec3DDilated (a ib.1).val).unit
  -- `finProdFinEquiv` maps `(0,0)↦0 [P_2(q)]`, `(0,1)↦1 [Z_3(q)]`, `(1,0)↦2 [P_2(q^2)]`, `(1,1)↦3 [Z_3(q^2)]`!
  let M : Matrix (Fin 4) (Fin 4) ℤ :=
    !![2, 0,  0,  0;
       2, 0, -2,  0;
       0, 1,  0,  0;
       0, 1,  0, -1]
  have hM : LinearIndependent ℚ (fun i : Fin 4 ↦ fun j : Fin 4 ↦ (M i j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]; intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    have h3 := congrFun hv 3
    simp [Fin.sum_univ_four, M] at h0 h1 h2 h3
    intro i; fin_cases i <;> dsimp <;> linarith
  have hind := monomial_family_diff_indep_of_logDeriv
    (F ∘ finProdFinEquiv.symm)
    (U ∘ finProdFinEquiv.symm)
    (fun p ↦ ((a (finProdFinEquiv.symm p).1).val : ℂ))
    (fun p ↦ by exact_mod_cast (a (finProdFinEquiv.symm p).1).pos.ne')
    (fun p ↦ by
      dsimp only [Function.comp_apply, F, U]
      split_ifs
      · exact X_mul_deriv_powerPartDilated (by decide) (a _).pos
      · exact X_mul_deriv_bec3DDilated (a _).pos)
    (logDeriv_bec1D_bec3D_dilations_diff_indep a ha) M hM
  have heq : (fun i : Fin 4 ↦
      ((∏ j : Fin 4, (U ∘ finProdFinEquiv.symm) j ^ M i j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) =
      ![bec1DGas, fermi1DGas, bec3DSeries, fermi3DSeries] := by
    have hp0 : (finProdFinEquiv (m := 2) (n := 2)).symm (0 : Fin (2 * 2)) = (0, 0) := by decide
    have hp1 : (finProdFinEquiv (m := 2) (n := 2)).symm (1 : Fin (2 * 2)) = (0, 1) := by decide
    have hp2 : (finProdFinEquiv (m := 2) (n := 2)).symm (2 : Fin (2 * 2)) = (1, 0) := by decide
    have hp3 : (finProdFinEquiv (m := 2) (n := 2)).symm (3 : Fin (2 * 2)) = (1, 1) := by decide
    funext i; fin_cases i
    · simp only [Fin.prod_univ_four, Function.comp_apply, hp0, hp1, hp2, hp3, U, a]
      have hM0 : M 0 0 = 2 ∧ M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 0 3 = 0 := by decide
      change (((isUnit_powerPartDilated 2 1).unit ^ M 0 0 *
          (isUnit_bec3DDilated 1).unit ^ M 0 1 *
          (isUnit_powerPartDilated 2 2).unit ^ M 0 2 *
          (isUnit_bec3DDilated 2).unit ^ M 0 3 : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = bec1DGas
      rw [hM0.1, hM0.2.1, hM0.2.2.1, hM0.2.2.2]
      simp only [zpow_zero, mul_one]
      change (((isUnit_powerPartDilated 2 1).unit ^ (2 : ℕ) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = _
      rw [Units.val_pow_eq_pow_val]; rfl
    · simp only [Fin.prod_univ_four, Function.comp_apply, hp0, hp1, hp2, hp3, U, a]
      have hM1 : M 1 0 = 2 ∧ M 1 1 = 0 ∧ M 1 2 = -2 ∧ M 1 3 = 0 := by decide
      change (((isUnit_powerPartDilated 2 1).unit ^ M 1 0 *
          (isUnit_bec3DDilated 1).unit ^ M 1 1 *
          (isUnit_powerPartDilated 2 2).unit ^ M 1 2 *
          (isUnit_bec3DDilated 2).unit ^ M 1 3 : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = fermi1DGas
      rw [hM1.1, hM1.2.1, hM1.2.2.1, hM1.2.2.2]
      simp only [zpow_zero, mul_one]
      change (((isUnit_powerPartDilated 2 1).unit ^ (2 : ℤ) *
          (isUnit_powerPartDilated 2 2).unit ^ (-2 : ℤ) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
        ((((isUnit_powerPartDilated 2 1).unit *
          (isUnit_powerPartDilated 2 2).unit⁻¹ : (PowerSeries ℂ)ˣ) ^ (2 : ℕ) : (PowerSeries ℂ)ˣ) :
          PowerSeries ℂ)
      congr 1
      rw [mul_pow, inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg]; rfl
    · simp only [Fin.prod_univ_four, Function.comp_apply, hp0, hp1, hp2, hp3, U, a]
      have hM2 : M 2 0 = 0 ∧ M 2 1 = 1 ∧ M 2 2 = 0 ∧ M 2 3 = 0 := by decide
      change (((isUnit_powerPartDilated 2 1).unit ^ M 2 0 *
          (isUnit_bec3DDilated 1).unit ^ M 2 1 *
          (isUnit_powerPartDilated 2 2).unit ^ M 2 2 *
          (isUnit_bec3DDilated 2).unit ^ M 2 3 : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = bec3DSeries
      rw [hM2.1, hM2.2.1, hM2.2.2.1, hM2.2.2.2]
      simp only [zpow_zero, zpow_one, one_mul, mul_one]; rfl
    · simp only [Fin.prod_univ_four, Function.comp_apply, hp0, hp1, hp2, hp3, U, a]
      have hM3 : M 3 0 = 0 ∧ M 3 1 = 1 ∧ M 3 2 = 0 ∧ M 3 3 = -1 := by decide
      change (((isUnit_powerPartDilated 2 1).unit ^ M 3 0 *
          (isUnit_bec3DDilated 1).unit ^ M 3 1 *
          (isUnit_powerPartDilated 2 2).unit ^ M 3 2 *
          (isUnit_bec3DDilated 2).unit ^ M 3 3 : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = fermi3DSeries
      rw [hM3.1, hM3.2.1, hM3.2.2.1, hM3.2.2.2]
      simp only [zpow_zero, zpow_one, _root_.zpow_neg_one, one_mul, mul_one]; rfl
  rwa [heq] at hind

/-- **100% UNCONDITIONAL Joint Differential Independence of 1D and 3D Ideal Bose–Einstein Condensates
`(Z_BEC^{(1)}(q), Z_BEC^{(3)}(q))` over `ℂ(q)`**! -/
theorem bec1D_bec3D_joint_diff_indep :
    AlgebraicIndependent ℂ (jointSeriesCoordinates ![bec1DGas, bec3DSeries]) := by
  let emb : Option (Fin 2 × ℕ) → Option (Fin 4 × ℕ)
    | none => none
    | some (i, j) => some (if i.val = 0 then (0, j) else (2, j))
  have hemb : Function.Injective emb := by
    intro u v h
    cases u with
    | none => cases v with
      | none => rfl
      | some _ => simp [emb] at h
    | some ij => cases v with
      | none => simp [emb] at h
      | some kl =>
        rcases ij with ⟨i, j⟩; rcases kl with ⟨k, l⟩
        fin_cases i <;> fin_cases k <;> simp [emb] at h <;> simp [h]
  have hcomp : jointSeriesCoordinates ![bec1DGas, bec3DSeries] =
      jointSeriesCoordinates ![bec1DGas, fermi1DGas, bec3DSeries, fermi3DSeries] ∘ emb := by
    funext u; cases u with
    | none => rfl
    | some ij =>
      rcases ij with ⟨i, j⟩
      fin_cases i <;> rfl
  rw [hcomp]
  exact quantumGases_1D_3D_bose_fermi_joint_diff_indep.comp emb hemb

/-- **100% UNCONDITIONAL Joint Differential Independence of `P_2(q)` (Partitions into Squares) and
`Z_BEC^{(3)}(q)` (3D Ideal Bose–Einstein Condensate) over `ℂ(q)`**! -/
theorem powerPart2_bec3D_joint_diff_indep :
    AlgebraicIndependent ℂ (jointSeriesCoordinates ![powerPartSeries 2, bec3DSeries]) := by
  have hind := bec1D_bec3D_dilations_diff_indep (fun _ : Fin 1 ↦ 1) (fun i j _ ↦ Subsingleton.elim i j)
  let e : Option (Fin 2 × ℕ) ≃ Option (Fin (1 * 2) × ℕ) :=
    Equiv.optionCongr ((finCongr (by decide : 2 = 1 * 2)).prodCongr (Equiv.refl ℕ))
  have hcomp : jointSeriesCoordinates ![powerPartSeries 2, bec3DSeries] =
      jointSeriesCoordinates
        ((fun ib : Fin 1 × Fin 2 ↦
          if ib.2.val = 0 then powerPartDilated 2 ((fun _ : Fin 1 ↦ (1 : ℕ+)) ib.1).val
          else bec3DDilated ((fun _ : Fin 1 ↦ (1 : ℕ+)) ib.1).val) ∘ finProdFinEquiv.symm) ∘ e := by
    funext u; cases u with
    | none => rfl
    | some ij =>
      rcases ij with ⟨i, j⟩
      fin_cases i
      · have h0 : finProdFinEquiv.symm (0 : Fin (1 * 2)) = (0, 0) := by decide
        simp [jointSeriesCoordinates, e, h0, powerPartSeries]
      · have h1 : finProdFinEquiv.symm (1 : Fin (1 * 2)) = (0, 1) := by decide
        simp [jointSeriesCoordinates, e, h1, bec3DSeries]
  rw [hcomp]
  exact (algebraicIndependent_equiv' e rfl).mpr hind

end
end CubicTheta.AllD
