module

public import PakStokes.AllD.PowerPartitions
public import Mathlib.NumberTheory.ZetaValues
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

/-! # Wave 11 (Module 1): Quotient-Rank Differential Independence, Unified `d = 2` Zero-Tilt Engine, and the Square-Divisor Series `L_{2, 0}(q)`

Establishes 100% unconditionally from Mathlib on top of Wave 9 (`PakStokes.AllD.PowerPartitions`):

1. **General Multiplicative Quotient-Rank Transfer (`monomial_family_diff_indep_of_logDeriv`):**
   For ANY family of units `U : Fin n → (PowerSeries ℂ)ˣ` whose logarithmic derivatives
   `q U_j' = c_j F_j U_j` (`c_j ≠ 0`) have jointly differentially independent `{F_j}` over `ℂ(q)`,
   and ANY integer matrix `M : Matrix (Fin r) (Fin n) ℤ` with `ℚ`-linearly independent rows,
   the Laurent-monomial family `Y_i = ∏_j U_j^{M_{ij}}` is **jointly differentially independent
   over `ℂ(q)`**!
2. **Wave-9 Square-Partition Quotient & Forest Corollaries (100% Unconditional):**
   - `squarePart_monomial_family_diff_indep` (Codex's full-row-rank theorem for `P_2(q^a)`),
   - `distinctSquaresPart` (`Q_2(q) = ∏_{n ≥ 1} (1 + q^{n²}) = P_2(q) / P_2(q²)`, with exact
     Euler product identity `distinctSquaresPart_eq_eulerProd`),
   - `overpartSquares` (`\overline{P}_2(q) = ∏_{n ≥ 1} (1 + q^{n²}) / (1 - q^{n²}) = P_2(q)² / P_2(q²)`),
   - `kRegularSquares` (`B_{a, k}(q) = ∏_{n ≥ 1} (1 + q^{a n²} + ⋯ + q^{(k-1) a n²}) = P_2(q^a) / P_2(q^{k a})`,
     with exact Euler product identity `kRegularSquares_eq_eulerProd`),
   - `fermi1DGas` (`Z_FD^{(1)}(q) = ∏_{n ∈ ℤ \ {0}} (1 + q^{n²}) = Q_2(q)²`),
   - `distinctSquares_non_ade`, `overpartSquares_non_ade`,
     **`distinctSquares_overpartSquares_joint_diff_indep`**,
     `distinctSquares_dilations_diff_indep`, `kRegularSquares_dilations_diff_indep`,
     `fermi1D_non_ade`, `fermi1D_dilations_diff_indep`, and
     `squarePart_forest_quotients_diff_indep`!
3. **Unified `d = 2` Zero-Tilt Wave-Profile Engine (`SqRayProfile`):**
   Proves `sqRayProfile_dilations_diff_indep` and `sqRayProfile_non_ade` once and for all for
   ANY formal power series `F ∈ ℂ[[q]]` with polynomial coefficient growth and a `d = 2`
   elementary Stokes decomposition along `{sqRay0, sqRay1}` whose extreme-ray prime amplitudes
   never vanish — reused verbatim for both `L_{2, 0}(q)` and the physical 3D BEC `F_BEC^{(3)}(q)`!
4. **100% Unconditional Square-Divisor Generating Function `L_{2, 0}(q) = ∑_{N ≥ 1} d_□(N) q^N`:**
   - Exact 1-term pure elementary identity `squareDivisor_analytic_identity` (using 1D Poisson
     summation + `sqRem_identity` + 2nd derivative of `fourier_sqRem`, ZERO contour integrals!),
   - **`squareDivisor_non_ade`** and **`squareDivisor_dilations_diff_indep`**! -/

public section
namespace CubicTheta.AllD
open Complex Filter Set PowerSeries MvPolynomial Matrix Flow MeasureTheory
open scoped Topology Matrix FourierTransform
noncomputable section

/-! ### 1. General Multiplicative Quotient-Rank Transfer & Wave-9 Corollaries -/

private lemma X_mul_deriv_unit_zpow (u : (PowerSeries ℂ)ˣ) (g : PowerSeries ℂ)
    (hlog : PowerSeries.X * PowerSeries.derivative (R := ℂ) (u : PowerSeries ℂ) =
      g * (u : PowerSeries ℂ)) (k : ℤ) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) ((u ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
      (PowerSeries.C (k : ℂ) * g) * ((u ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
  have hnat (m : ℕ) :
      PowerSeries.X * PowerSeries.derivative (R := ℂ) ((u : PowerSeries ℂ) ^ m) =
        (PowerSeries.C (m : ℂ) * g) * (u : PowerSeries ℂ) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
          Nat.cast_add, Nat.cast_one, map_add, map_one]
      linear_combination (u : PowerSeries ℂ) ^ m * hlog + (u : PowerSeries ℂ) * ih
  cases k with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Int.cast_natCast]
    exact hnat m
  | negSucc m =>
    have hinv_eq : ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        (u : PowerSeries ℂ) ^ (m + 1) = 1 := by
      change ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        ((u ^ (m + 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1
      rw [← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add]
      have h0 : Int.negSucc m + ((m + 1 : ℕ) : ℤ) = 0 := by omega
      rw [h0, zpow_zero, Units.val_one]
    have hd_prod := congrArg (PowerSeries.X * PowerSeries.derivative (R := ℂ) ·) hinv_eq
    rw [PowerSeries.derivative_one, mul_zero, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hd_prod
    have hd_prod' :
        (PowerSeries.X * PowerSeries.derivative (R := ℂ)
            ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) *
          (u : PowerSeries ℂ) ^ (m + 1) +
        ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
          ((PowerSeries.C ((m + 1 : ℕ) : ℂ) * g) * (u : PowerSeries ℂ) ^ (m + 1)) = 0 := by
      linear_combination hd_prod - ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) * hnat (m + 1)
    have hmul := congrArg (· * ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) hd_prod'
    rw [zero_mul, add_mul] at hmul
    have hcancel1 :
        (PowerSeries.X * PowerSeries.derivative (R := ℂ)
            ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) *
          (u : PowerSeries ℂ) ^ (m + 1) *
          ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
        PowerSeries.X * PowerSeries.derivative (R := ℂ)
          ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
      rw [mul_assoc, mul_comm ((u : PowerSeries ℂ) ^ (m + 1)), hinv_eq, mul_one]
    have hcancel2 :
        ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
          ((PowerSeries.C ((m + 1 : ℕ) : ℂ) * g) * (u : PowerSeries ℂ) ^ (m + 1)) *
          ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
        (PowerSeries.C ((m + 1 : ℕ) : ℂ) * g) *
          ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
      calc _ = (PowerSeries.C ((m + 1 : ℕ) : ℂ) * g) *
              (((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
                (u : PowerSeries ℂ) ^ (m + 1)) *
              ((u ^ Int.negSucc m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by ring
        _ = _ := by rw [hinv_eq, mul_one]
    rw [hcancel1, hcancel2] at hmul
    have hcast : ((Int.negSucc m : ℤ) : ℂ) = -((m + 1 : ℕ) : ℂ) := by simp [Int.cast_negSucc]
    rw [hcast, map_neg]
    linear_combination hmul

private lemma formalJet_linearComb {n : ℕ} (a : Fin n → ℂ) (F : Fin n → PowerSeries ℂ) (k : ℕ) :
    formalJet (∑ j : Fin n, PowerSeries.C (a j) * F j) k =
      ∑ j : Fin n, PowerSeries.C (a j) * formalJet (F j) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [formalJet, Function.iterate_succ_apply']
    change PowerSeries.derivative (R := ℂ) (formalJet (∑ j : Fin n, PowerSeries.C (a j) * F j) k) = _
    rw [ih, map_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul,
        mul_zero, add_zero]
    congr 1
    exact (Function.iterate_succ_apply' (PowerSeries.derivative (R := ℂ)) k (F j)).symm

private lemma linearComb_joint_diff_indep {r n : ℕ}
    (F : Fin n → PowerSeries ℂ)
    (hF : AlgebraicIndependent ℂ (jointSeriesCoordinates F))
    (A : Matrix (Fin r) (Fin n) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (hAB : A * B = 1) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i : Fin r ↦
      ∑ j : Fin n, PowerSeries.C (A i j) * F j)) := by
  let G : Fin r → PowerSeries ℂ := fun i ↦ ∑ j : Fin n, PowerSeries.C (A i j) * F j
  let Φ : MvPolynomial (Option (Fin r × ℕ)) ℂ →ₐ[ℂ] MvPolynomial (Option (Fin n × ℕ)) ℂ :=
    MvPolynomial.aeval fun
      | none => MvPolynomial.X none
      | some (i, k) => ∑ j : Fin n, MvPolynomial.C (A i j) * MvPolynomial.X (some (j, k))
  let Ψ : MvPolynomial (Option (Fin n × ℕ)) ℂ →ₐ[ℂ] MvPolynomial (Option (Fin r × ℕ)) ℂ :=
    MvPolynomial.aeval fun
      | none => MvPolynomial.X none
      | some (j, k) => ∑ i : Fin r, MvPolynomial.C (B j i) * MvPolynomial.X (some (i, k))
  have hΨΦ : ∀ P : MvPolynomial (Option (Fin r × ℕ)) ℂ, Ψ (Φ P) = P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => simp [Φ, Ψ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p u hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      cases u with
      | none => simp [Φ, Ψ]
      | some ik =>
        rcases ik with ⟨i, k⟩
        simp only [Φ, MvPolynomial.aeval_X, map_sum, map_mul]
        simp only [Ψ, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        have hinner (i' : Fin r) :
            (∑ j : Fin n, MvPolynomial.C (A i j) *
              (MvPolynomial.C (B j i') * MvPolynomial.X (some (i', k)))) =
            MvPolynomial.C ((A * B) i i') * MvPolynomial.X (some (i', k)) := by
          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro j _
          rw [map_mul]; ring
        simp_rw [hinner, hAB, Matrix.one_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro i' _ hne; simp [hne.symm]
        · intro h; exact (h (Finset.mem_univ i)).elim
  have hΦ_inj : Function.Injective Φ := Function.LeftInverse.injective hΨΦ
  have hcomp : MvPolynomial.aeval (jointSeriesCoordinates G) =
      (MvPolynomial.aeval (jointSeriesCoordinates F)).comp Φ := by
    apply MvPolynomial.algHom_ext
    intro u
    cases u with
    | none => simp [Φ, jointSeriesCoordinates]
    | some ik =>
      rcases ik with ⟨i, k⟩
      simp only [AlgHom.comp_apply, Φ, MvPolynomial.aeval_X, map_sum, map_mul,
        MvPolynomial.aeval_C, jointSeriesCoordinates, G, formalJet_linearComb]
      rfl
  rw [algebraicIndependent_iff_injective_aeval, hcomp]
  exact (algebraicIndependent_iff_injective_aeval.mp hF).comp hΦ_inj

/-- **General Multiplicative Quotient-Rank Theorem (100% Unconditional)**:
For ANY family of formal power-series units `U : Fin n → (PowerSeries ℂ)ˣ` satisfying
`q · U_j' = c_j · F_j · U_j` (`c_j ≠ 0`) with `{F_j}` jointly differentially independent over `ℂ(q)`,
and ANY integer exponent matrix `M : Matrix (Fin r) (Fin n) ℤ` whose rows are `ℚ`-linearly
independent, the Laurent-monomial products `Y_i = ∏_j U_j^{M_{ij}}` are **jointly differentially
independent over `ℂ(q)`**! -/
theorem monomial_family_diff_indep_of_logDeriv {r n : ℕ}
    (F : Fin n → PowerSeries ℂ)
    (U : Fin n → (PowerSeries ℂ)ˣ)
    (c : Fin n → ℂ) (hc : ∀ j, c j ≠ 0)
    (hlog : ∀ j, PowerSeries.X * PowerSeries.derivative (R := ℂ) (U j : PowerSeries ℂ) =
      (PowerSeries.C (c j) * F j) * (U j : PowerSeries ℂ))
    (hF : AlgebraicIndependent ℂ (jointSeriesCoordinates F))
    (M : Matrix (Fin r) (Fin n) ℤ)
    (hM : LinearIndependent ℚ (fun i : Fin r ↦ fun j : Fin n ↦ (M i j : ℚ))) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i : Fin r ↦
      ((∏ j : Fin n, U j ^ M i j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ))) := by
  let Mq : Matrix (Fin r) (Fin n) ℚ := Matrix.of fun i j ↦ (M i j : ℚ)
  let rowMap : (Fin r → ℚ) →ₗ[ℚ] (Fin n → ℚ) := Matrix.vecMulLinear Mq
  have hrow_inj : Function.Injective rowMap := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hlin : ∑ i : Fin r, v i • (fun j : Fin n ↦ (M i j : ℚ)) = 0 := by
      ext j
      have hj := congrFun hv j
      simpa only [rowMap, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Mq, Matrix.of_apply] using hj
    have h0 := (Fintype.linearIndependent_iff.mp hM) v hlin
    ext i; exact h0 i
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective rowMap (LinearMap.ker_eq_bot.mpr hrow_inj)
  let Bq : Matrix (Fin n) (Fin r) ℚ := Matrix.of fun j i ↦ L (Pi.single j 1) i
  have hMBq : Mq * Bq = 1 := by
    ext i i'
    have hev : L (rowMap (Pi.single i 1)) = Pi.single i 1 := by
      have := LinearMap.congr_fun hL (Pi.single i 1)
      simpa using this
    have hrow_single : rowMap (Pi.single i 1) = ∑ j : Fin n, (M i j : ℚ) • Pi.single j 1 := by
      ext j
      simp [rowMap, Matrix.vecMul, dotProduct, Mq, Pi.single_apply]
    have hlhs : L (rowMap (Pi.single i 1)) i' = (Mq * Bq) i i' := by
      rw [hrow_single, map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Mq, Bq,
        Matrix.of_apply]
    rw [← hlhs, hev, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = i' <;> simp [h, eq_comm]
  let A : Matrix (Fin r) (Fin n) ℂ := Matrix.of fun i j ↦ (M i j : ℂ) * c j
  let B : Matrix (Fin n) (Fin r) ℂ := Matrix.of fun j i ↦ (c j)⁻¹ * ((Bq j i : ℚ) : ℂ)
  have hAB : A * B = 1 := by
    ext i i'
    have hq := congrArg (Rat.cast (K := ℂ)) (congrFun (congrFun hMBq i) i')
    simp only [Matrix.mul_apply, Mq, Matrix.of_apply, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
      Matrix.one_apply] at hq
    rw [Matrix.mul_apply]
    have hterm (j : Fin n) : A i j * B j i' = (M i j : ℂ) * ((Bq j i' : ℚ) : ℂ) := by
      simp only [A, B, Matrix.of_apply]
      have hcj := hc j
      field_simp [hcj]
    simp_rw [hterm]
    rw [hq, Matrix.one_apply]
    split_ifs <;> simp
  let G : Fin r → PowerSeries ℂ := fun i ↦ ∑ j : Fin n, PowerSeries.C (A i j) * F j
  have hG : AlgebraicIndependent ℂ (jointSeriesCoordinates G) :=
    linearComb_joint_diff_indep F hF A B hAB
  let Y : Fin r → PowerSeries ℂ :=
    fun i ↦ ((∏ j : Fin n, U j ^ M i j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
  have hlogY (i : Fin r) :
      PowerSeries.X * PowerSeries.derivative (R := ℂ) (Y i) =
        (PowerSeries.C (1 : ℂ) * G i) * Y i := by
    have hval : Y i = ∏ j : Fin n, ((U j ^ M i j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
      change (Units.coeHom (PowerSeries ℂ)) (∏ j : Fin n, U j ^ M i j) = _
      exact map_prod (Units.coeHom (PowerSeries ℂ)) _ _
    rw [hval]
    have heach (j : Fin n) (_ : j ∈ (Finset.univ : Finset (Fin n))) :
        PowerSeries.X * PowerSeries.derivative (R := ℂ)
            ((U j ^ M i j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
          (PowerSeries.C (A i j) * F j) * ((U j ^ M i j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
      have h1 := X_mul_deriv_unit_zpow (U j) (PowerSeries.C (c j) * F j) (hlog j) (M i j)
      simpa only [A, Matrix.of_apply, map_mul, mul_assoc] using h1
    rw [X_mul_deriv_finset_prod Finset.univ _ _ heach, map_one, one_mul]
  exact kolchin_logDeriv_joint_indep G Y (fun _ ↦ 1)
    (fun i ↦ Units.ne_zero _) (fun _ ↦ one_ne_zero) hlogY hG

/-- **Codex's Quotient-Rank Theorem for Square-Partition Dilations (`P_2(q^a)`) — 100% Unconditional**:
For ANY finite injective family of dilations `a : Fin n → ℕ+` and ANY integer matrix
`M : Matrix (Fin r) (Fin n) ℤ` with `ℚ`-linearly independent rows, the Laurent-monomial products
`Y_i = ∏_j P_2(q^{a_j})^{M_{ij}}` are **jointly differentially independent over `ℂ(q)`**! -/
theorem squarePart_monomial_family_diff_indep {r n : ℕ}
    (a : Fin n → ℕ+) (ha : Function.Injective a)
    (M : Matrix (Fin r) (Fin n) ℤ)
    (hM : LinearIndependent ℚ (fun i : Fin r ↦ fun j : Fin n ↦ (M i j : ℚ))) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i : Fin r ↦
      ((∏ j : Fin n, (isUnit_powerPartDilated 2 (a j).val).unit ^ M i j :
        (PowerSeries ℂ)ˣ) : PowerSeries ℂ))) :=
  monomial_family_diff_indep_of_logDeriv
    (fun j ↦ logDerivPowerPartDilated 2 (a j).val)
    (fun j ↦ (isUnit_powerPartDilated 2 (a j).val).unit)
    (fun j ↦ ((a j).val : ℂ))
    (fun j ↦ by exact_mod_cast (a j).property.ne')
    (fun j ↦ X_mul_deriv_powerPartDilated (by decide) (a j).property)
    (logDerivPowerPart_2_dilations_diff_indep a ha) M hM

private lemma single_diffTrans_of_joint {S : PowerSeries ℂ}
    (h : AlgebraicIndependent ℂ (jointSeriesCoordinates (fun _ : Fin 1 ↦ S))) :
    AlgebraicIndependent ℂ (seriesCoordinates S) := by
  let e : ℕ ≃ Option (Fin 1 × ℕ) :=
    { toFun := fun | 0 => none | j + 1 => some (0, j)
      invFun := fun | none => 0 | some (_, j) => j + 1
      left_inv := fun | 0 => rfl | _ + 1 => rfl
      right_inv := fun | none => rfl | some (i, _) => by rw [Subsingleton.elim i 0] }
  exact (algebraicIndependent_equiv' e (by funext n; cases n <;> rfl)).mpr h

/-- Formal unit for `k`-regular square partitions `B_{a, k}(q) = P_2(q^a) / P_2(q^{k a})`. -/
def kRegularSquaresUnit (a k : ℕ+) : (PowerSeries ℂ)ˣ :=
  (isUnit_powerPartDilated 2 a.val).unit * (isUnit_powerPartDilated 2 (k.val * a.val)).unit⁻¹

/-- Formal power series for `k`-regular square partitions
`B_{a, k}(q) = ∏_{n ≥ 1} (1 + q^{a n²} + ⋯ + q^{(k-1) a n²}) = P_2(q^a) / P_2(q^{k a})`. -/
def kRegularSquares (a k : ℕ+) : PowerSeries ℂ := (kRegularSquaresUnit a k : PowerSeries ℂ)

/-- Formal power series for partitions into **distinct squares**:
`Q_2(q) = ∏_{n ≥ 1} (1 + q^{n²}) = P_2(q) / P_2(q²)`. -/
def distinctSquaresPart : PowerSeries ℂ := kRegularSquares 1 2

/-- Formal power series for **overpartitions into squares**:
`\overline{P}_2(q) = ∏_{n ≥ 1} (1 + q^{n²}) / (1 - q^{n²}) = P_2(q)² / P_2(q²)`. -/
def overpartSquares : PowerSeries ℂ :=
  (((isUnit_powerPartDilated 2 1).unit ^ (2 : ℤ) *
    (isUnit_powerPartDilated 2 2).unit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)

/-- Formal power series for the **1D ideal Fermi–Dirac gas**:
`Z_FD^{(1)}(q) = ∏_{n ∈ ℤ \ {0}} (1 + q^{n²}) = Q_2(q)²`. -/
def fermi1DGas : PowerSeries ℂ := distinctSquaresPart ^ 2

private lemma geomSeriesPow_eq_finset_sum_mul {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    geomSeriesPow m = (∑ r ∈ Finset.range k, PowerSeries.X ^ (r * m)) * geomSeriesPow (k * m) := by
  have h1 : (1 - (PowerSeries.X : PowerSeries ℂ) ^ m) *
      (∑ r ∈ Finset.range k, (PowerSeries.X : PowerSeries ℂ) ^ (r * m)) =
      1 - (PowerSeries.X : PowerSeries ℂ) ^ (k * m) := by
    rw [sub_mul, one_mul, Finset.mul_sum]
    have hshift : (∑ r ∈ Finset.range k,
          (PowerSeries.X : PowerSeries ℂ) ^ m * (PowerSeries.X : PowerSeries ℂ) ^ (r * m)) =
        ∑ r ∈ Finset.range k, (PowerSeries.X : PowerSeries ℂ) ^ ((r + 1) * m) := by
      apply Finset.sum_congr rfl; intro r _
      rw [← pow_add]; congr 1; ring
    rw [hshift, ← Finset.sum_sub_distrib]
    have htele := Finset.sum_range_sub' (fun r ↦ (PowerSeries.X : PowerSeries ℂ) ^ (r * m)) k
    simpa only [zero_mul, pow_zero] using htele
  have hkm : 1 ≤ k * m := Nat.mul_pos hk hm
  calc geomSeriesPow m
      = geomSeriesPow m * 1 := (mul_one _).symm
    _ = geomSeriesPow m * ((1 - PowerSeries.X ^ (k * m)) * geomSeriesPow (k * m)) := by
          rw [geomSeriesPow_mul_one_sub hkm]
    _ = geomSeriesPow m * ((1 - PowerSeries.X ^ m) *
          (∑ r ∈ Finset.range k, PowerSeries.X ^ (r * m)) * geomSeriesPow (k * m)) := by rw [← h1]
    _ = ((1 - PowerSeries.X ^ m) * geomSeriesPow m) *
          ((∑ r ∈ Finset.range k, PowerSeries.X ^ (r * m)) * geomSeriesPow (k * m)) := by ring
    _ = (∑ r ∈ Finset.range k, PowerSeries.X ^ (r * m)) * geomSeriesPow (k * m) := by
          rw [geomSeriesPow_mul_one_sub hm, one_mul]

/-- Exact Euler product identity for `kRegularSquares a k`:
`[q^N] B_{a, k}(q) = [q^N] ∏_{n=1}^N (1 + q^{a n²} + ⋯ + q^{(k-1) a n²})` for EVERY `N : ℕ`! -/
theorem kRegularSquares_eq_eulerProd (a k : ℕ+) (N : ℕ) :
    PowerSeries.coeff N (kRegularSquares a k) =
      PowerSeries.coeff N (∏ n ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.range k.val, (PowerSeries.X : PowerSeries ℂ) ^ (r * (a.val * n ^ 2))) := by
  let P_N : PowerSeries ℂ :=
    ∏ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.range k.val,
      (PowerSeries.X : PowerSeries ℂ) ^ (r * (a.val * n ^ 2))
  have hmul_trunc : powerPartTrunc 2 a.val N = P_N * powerPartTrunc 2 (k.val * a.val) N := by
    unfold powerPartTrunc P_N
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm : 1 ≤ a.val * n ^ 2 := Nat.mul_pos a.pos (pow_pos hn1 2)
    simpa only [mul_assoc] using geomSeriesPow_eq_finset_sum_mul hm k.pos
  have hmul_series : ∀ M ≤ N,
      PowerSeries.coeff M (kRegularSquares a k * powerPartDilated 2 (k.val * a.val)) =
        PowerSeries.coeff M (P_N * powerPartDilated 2 (k.val * a.val)) := by
    intro M hMN
    have hunit : kRegularSquares a k * powerPartDilated 2 (k.val * a.val) =
        powerPartDilated 2 a.val := by
      change ((kRegularSquaresUnit a k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        (((isUnit_powerPartDilated 2 (k.val * a.val)).unit : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = _
      rw [← Units.val_mul, kRegularSquaresUnit, mul_assoc, inv_mul_cancel, mul_one]
      exact (isUnit_powerPartDilated 2 a.val).unit_spec
    rw [hunit, powerPartDilated, PowerSeries.coeff_mk,
        ← coeff_powerPartTrunc_stable (by decide) a.pos hMN, hmul_trunc,
        PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl; rintro ⟨i, j⟩ hij
    have hsum : i + j = M := Finset.mem_antidiagonal.mp hij
    rw [powerPartDilated, PowerSeries.coeff_mk,
        coeff_powerPartTrunc_stable (by decide) (Nat.mul_pos k.pos a.pos) (by omega : j ≤ N)]
  have hdiff_zero : ∀ M ≤ N,
      PowerSeries.coeff M (kRegularSquares a k) = PowerSeries.coeff M P_N := by
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
              PowerSeries.coeff x.1 (kRegularSquares a k) *
                PowerSeries.coeff x.2 (powerPartDilated 2 (k.val * a.val))) =
          ∑ x ∈ (Finset.antidiagonal M).erase (M, 0),
              PowerSeries.coeff x.1 P_N *
                PowerSeries.coeff x.2 (powerPartDilated 2 (k.val * a.val)) := by
        apply Finset.sum_congr rfl; rintro ⟨i, j⟩ hx
        have hne : (i, j) ≠ (M, 0) := (Finset.mem_erase.mp hx).1
        have hsum : i + j = M := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
        have hilt : i < M := by
          by_contra hge; apply hne; exact Prod.ext (by omega) (by omega)
        rw [ih i hilt (by omega)]
      have hc0 : PowerSeries.coeff 0 (powerPartDilated 2 (k.val * a.val)) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_powerPartDilated]
      rw [hrest, hc0, mul_one, mul_one] at heq
      exact add_right_cancel heq
  exact hdiff_zero N le_rfl

/-- Exact Euler product identity for partitions into distinct squares
`Q_2(q) = ∏_{n ≥ 1} (1 + q^{n²})`. -/
theorem distinctSquaresPart_eq_eulerProd (N : ℕ) :
    PowerSeries.coeff N distinctSquaresPart =
      PowerSeries.coeff N (∏ n ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : PowerSeries ℂ) ^ (n ^ 2))) := by
  simpa only [distinctSquaresPart, PNat.val_ofNat, PNat.one_coe, one_mul, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, zero_mul, pow_zero, one_mul] using
    kRegularSquares_eq_eulerProd 1 2 N

/-- Exact algebraic factorization `\overline{P}_2(q) = P_2(q) · Q_2(q)`. -/
theorem overpartSquares_eq_mul :
    overpartSquares = powerPartSeries 2 * distinctSquaresPart := by
  change (((isUnit_powerPartDilated 2 1).unit ^ (2 : ℤ) *
      (isUnit_powerPartDilated 2 2).unit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
    (((isUnit_powerPartDilated 2 1).unit : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
    (((isUnit_powerPartDilated 2 1).unit *
      (isUnit_powerPartDilated 2 2).unit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
  rw [← Units.val_mul]
  congr 1
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, mul_assoc]

/-- **100% Unconditional Joint Differential Independence of `(Q_2, \overline{P}_2)` over `ℂ(q)`**
(Codex's invertible `2 × 2` unimodular matrix `[[1, -1], [2, -1]]`)! -/
theorem distinctSquares_overpartSquares_joint_diff_indep :
    AlgebraicIndependent ℂ (jointSeriesCoordinates ![distinctSquaresPart, overpartSquares]) := by
  let a : Fin 2 → ℕ+ := ![1, 2]
  have ha : Function.Injective a := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [a]
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 2, -1]
  have hM : LinearIndependent ℚ (fun i : Fin 2 ↦ fun j : Fin 2 ↦ (M i j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, M,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_one, Int.cast_neg, Int.cast_ofNat] at h0 h1
    intro i; fin_cases i <;> dsimp <;> linarith
  have hind := squarePart_monomial_family_diff_indep a ha M hM
  have heq : (fun i : Fin 2 ↦
      ((∏ j : Fin 2, (isUnit_powerPartDilated 2 (a j).val).unit ^ M i j :
        (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = ![distinctSquaresPart, overpartSquares] := by
    funext i; fin_cases i
    · simp [a, M, distinctSquaresPart, kRegularSquares, kRegularSquaresUnit, Fin.prod_univ_two]
    · simp [a, M, overpartSquares, Fin.prod_univ_two]
  rwa [heq] at hind

/-- **100% Unconditional Differential Transcendence of Partitions into Distinct Squares
`Q_2(q) = ∏_{n ≥ 1} (1 + q^{n²})` over `ℂ(q)`**! -/
theorem distinctSquares_non_ade :
    AlgebraicIndependent ℂ (seriesCoordinates distinctSquaresPart) := by
  let a : Fin 2 → ℕ+ := ![1, 2]
  have ha : Function.Injective a := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [a]
  let M : Matrix (Fin 1) (Fin 2) ℤ := !![1, -1]
  have hM : LinearIndependent ℚ (fun i : Fin 1 ↦ fun j : Fin 2 ↦ (M i j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]; intro v hv
    have h0 := congrFun hv 0
    simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, M,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Int.cast_one, mul_one] at h0
    intro i; fin_cases i; exact h0
  have hind := squarePart_monomial_family_diff_indep a ha M hM
  have heq : (fun i : Fin 1 ↦
      ((∏ j : Fin 2, (isUnit_powerPartDilated 2 (a j).val).unit ^ M i j :
        (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = fun _ ↦ distinctSquaresPart := by
    funext i; fin_cases i
    simp [a, M, distinctSquaresPart, kRegularSquares, kRegularSquaresUnit, Fin.prod_univ_two]
  rw [heq] at hind
  exact single_diffTrans_of_joint hind

/-- **100% Unconditional Differential Transcendence of Overpartitions into Squares
`\overline{P}_2(q) = ∏_{n ≥ 1} (1 + q^{n²}) / (1 - q^{n²})` over `ℂ(q)`**! -/
theorem overpartSquares_non_ade :
    AlgebraicIndependent ℂ (seriesCoordinates overpartSquares) := by
  let a : Fin 2 → ℕ+ := ![1, 2]
  have ha : Function.Injective a := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [a]
  let M : Matrix (Fin 1) (Fin 2) ℤ := !![2, -1]
  have hM : LinearIndependent ℚ (fun i : Fin 1 ↦ fun j : Fin 2 ↦ (M i j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]; intro v hv
    have h1 := congrFun hv 1
    simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, M,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_eq_zero] at h1
    intro i; fin_cases i; exact h1
  have hind := squarePart_monomial_family_diff_indep a ha M hM
  have heq : (fun i : Fin 1 ↦
      ((∏ j : Fin 2, (isUnit_powerPartDilated 2 (a j).val).unit ^ M i j :
        (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = fun _ ↦ overpartSquares := by
    funext i; fin_cases i
    simp [a, M, overpartSquares, Fin.prod_univ_two]
  rw [heq] at hind
  exact single_diffTrans_of_joint hind

/-- **100% Unconditional Differential Transcendence of the 1D Ideal Fermi–Dirac Gas
`Z_FD^{(1)}(q) = ∏_{n ∈ ℤ \ {0}} (1 + q^{n²}) = Q_2(q)²` over `ℂ(q)`**! -/
theorem fermi1D_non_ade :
    AlgebraicIndependent ℂ (seriesCoordinates fermi1DGas) := by
  let a : Fin 2 → ℕ+ := ![1, 2]
  have ha : Function.Injective a := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [a]
  let M : Matrix (Fin 1) (Fin 2) ℤ := !![2, -2]
  have hM : LinearIndependent ℚ (fun i : Fin 1 ↦ fun j : Fin 2 ↦ (M i j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]; intro v hv
    have h0 := congrFun hv 0
    simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, M,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Int.cast_ofNat] at h0
    intro i; fin_cases i; dsimp; linarith
  have hind := squarePart_monomial_family_diff_indep a ha M hM
  have heq : (fun i : Fin 1 ↦
      ((∏ j : Fin 2, (isUnit_powerPartDilated 2 (a j).val).unit ^ M i j :
        (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = fun _ ↦ fermi1DGas := by
    funext i; fin_cases i
    simp only [a, M, fermi1DGas, distinctSquaresPart, kRegularSquares, kRegularSquaresUnit,
      Fin.prod_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, PNat.val_ofNat, mul_one]
    change (((isUnit_powerPartDilated 2 1).unit ^ (2 : ℤ) *
        (isUnit_powerPartDilated 2 2).unit ^ (-2 : ℤ) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
      ((((isUnit_powerPartDilated 2 1).unit *
        (isUnit_powerPartDilated 2 2).unit⁻¹ : (PowerSeries ℂ)ˣ) ^ (2 : ℕ) : (PowerSeries ℂ)ˣ) :
        PowerSeries ℂ)
    congr 1
    rw [mul_pow, inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg]; rfl
  rw [heq] at hind
  exact single_diffTrans_of_joint hind

/-- **General Oriented-DAG / Distinct-Source Quotient Independence Theorem (100% Unconditional)**:
For ANY family of log-derivative-independent units `U : ℕ+ → (PowerSeries ℂ)ˣ`, any integer
exponent `e ≠ 0`, and any finite family of edges `(u_i, v_i) : Fin r → ℕ+ × ℕ+` with `u` injective
and `u_i < v_i` for every `i`, the quotient-powers `{(U (u_i) / U (v_i))^e}` are **jointly
differentially independent over `ℂ(q)`**! -/
theorem distinctSource_quotient_pow_diff_indep {r : ℕ}
    (F : ℕ+ → PowerSeries ℂ) (U : ℕ+ → (PowerSeries ℂ)ˣ) (c : ℕ+ → ℂ)
    (hc : ∀ m, c m ≠ 0)
    (hlog : ∀ m, PowerSeries.X * PowerSeries.derivative (R := ℂ) (U m : PowerSeries ℂ) =
      (PowerSeries.C (c m) * F m) * (U m : PowerSeries ℂ))
    (hF : ∀ {n : ℕ} (a : Fin n → ℕ+), Function.Injective a →
      AlgebraicIndependent ℂ (jointSeriesCoordinates (fun j ↦ F (a j))))
    (u v : Fin r → ℕ+) (hu : Function.Injective u) (huv : ∀ i, u i < v i)
    (e : ℤ) (he : e ≠ 0) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i : Fin r ↦
      (((U (u i) * (U (v i))⁻¹) ^ e : (PowerSeries ℂ)ˣ) : PowerSeries ℂ))) := by
  classical
  let V : Finset ℕ+ := Finset.univ.image u ∪ Finset.univ.image v
  let n := V.card
  let enum : Fin n ≃ V := (Fintype.equivFinOfCardEq (Fintype.card_coe V)).symm
  let a : Fin n → ℕ+ := fun j ↦ (enum j).val
  have ha : Function.Injective a := fun j₁ j₂ h ↦ enum.injective (Subtype.ext h)
  have hu_mem (i : Fin r) : u i ∈ V := Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ i))
  have hv_mem (i : Fin r) : v i ∈ V := Finset.mem_union_right _ (Finset.mem_image_of_mem v (Finset.mem_univ i))
  let idxU (i : Fin r) : Fin n := enum.symm ⟨u i, hu_mem i⟩
  let idxV (i : Fin r) : Fin n := enum.symm ⟨v i, hv_mem i⟩
  have ha_idxU (i : Fin r) : a (idxU i) = u i := by simp [a, idxU]
  have ha_idxV (i : Fin r) : a (idxV i) = v i := by simp [a, idxV]
  have hidx_ne (i : Fin r) : idxU i ≠ idxV i := fun h ↦
    (huv i).ne (by rw [← ha_idxU i, ← ha_idxV i, h])
  let M : Matrix (Fin r) (Fin n) ℤ :=
    Matrix.of fun i j ↦ (if j = idxU i then e else 0) - (if j = idxV i then e else 0)
  have hM : LinearIndependent ℚ (fun i : Fin r ↦ fun j : Fin n ↦ (M i j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro lam hlam
    by_contra hnot
    push Not at hnot
    let S : Finset (Fin r) := Finset.univ.filter fun i ↦ lam i ≠ 0
    have hSne : S.Nonempty := by
      obtain ⟨i, hi⟩ := hnot
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    obtain ⟨i₀, hi₀S, hmin⟩ := S.exists_min_image (fun i ↦ (u i).val) hSne
    have hlam₀ : lam i₀ ≠ 0 := (Finset.mem_filter.mp hi₀S).2
    have hev := congrFun hlam (idxU i₀)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, M, Matrix.of_apply] at hev
    rw [Finset.sum_eq_single i₀] at hev
    · simp only [↓reduceIte, hidx_ne i₀, sub_zero] at hev
      have heQ : (e : ℚ) ≠ 0 := Int.cast_ne_zero.mpr he
      exact mul_ne_zero hlam₀ heQ hev
    · intro i _ hne
      by_cases hl : lam i = 0
      · rw [hl, zero_mul]
      · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hl⟩
        have h1 : idxU i₀ ≠ idxU i := fun h ↦
          hne (hu (by rw [← ha_idxU i, ← ha_idxU i₀, h])).symm
        have h2 : idxU i₀ ≠ idxV i := fun h ↦ by
          have hu_eq : u i₀ = v i := by rw [← ha_idxU i₀, ← ha_idxV i, h]
          have hle : (u i₀).val ≤ (u i).val := hmin i hiS
          have hlt : (u i).val < (v i).val := huv i
          rw [← hu_eq] at hlt; omega
        simp [h1, h2]
    · intro h; exact (h (Finset.mem_univ i₀)).elim
  have hind := monomial_family_diff_indep_of_logDeriv
    (fun j ↦ F (a j)) (fun j ↦ U (a j)) (fun j ↦ c (a j))
    (fun j ↦ hc (a j)) (fun j ↦ hlog (a j)) (hF a ha) M hM
  have heq : (fun i : Fin r ↦
      ((∏ j : Fin n, U (a j) ^ M i j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) =
      (fun i : Fin r ↦ (((U (u i) * (U (v i))⁻¹) ^ e : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) := by
    funext i
    congr 1
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (idxU i))]
    have hv_mem_er : idxV i ∈ Finset.univ.erase (idxU i) :=
      Finset.mem_erase.mpr ⟨(hidx_ne i).symm, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase _ _ hv_mem_er]
    have hrest : (∏ j ∈ (Finset.univ.erase (idxU i)).erase (idxV i), U (a j) ^ M i j) = 1 := by
      apply Finset.prod_eq_one; intro j hj
      have hnv : j ≠ idxV i := (Finset.mem_erase.mp hj).1
      have hnu : j ≠ idxU i := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      simp [M, hnu, hnv]
    rw [hrest, mul_one, ha_idxU i, ha_idxV i]
    have hMu : M i (idxU i) = e := by simp [M, hidx_ne i]
    have hMv : M i (idxV i) = -e := by simp [M, (hidx_ne i).symm]
    rw [hMu, hMv, mul_zpow, _root_.inv_zpow, ← _root_.zpow_neg]
  rwa [heq] at hind

/-- **Codex's Forest / Distinct-Source Quotient Corollary for Square Partitions (100% Unconditional)**:
For ANY finite family of edges `(u_i, v_i)` with `u` injective and `u_i < v_i`,
the quotients `{P_2(q^{u_i}) / P_2(q^{v_i})}` are jointly differentially independent over `ℂ(q)`! -/
theorem squarePart_forest_quotients_diff_indep {r : ℕ}
    (u v : Fin r → ℕ+) (hu : Function.Injective u) (huv : ∀ i, u i < v i) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i : Fin r ↦
      (((isUnit_powerPartDilated 2 (u i).val).unit *
        (isUnit_powerPartDilated 2 (v i).val).unit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ))) := by
  simpa only [zpow_one] using distinctSource_quotient_pow_diff_indep
    (fun m ↦ logDerivPowerPartDilated 2 m.val)
    (fun m ↦ (isUnit_powerPartDilated 2 m.val).unit)
    (fun m ↦ (m.val : ℂ))
    (fun m ↦ by exact_mod_cast m.property.ne')
    (fun m ↦ X_mul_deriv_powerPartDilated (by decide) m.property)
    (fun a ha ↦ logDerivPowerPart_2_dilations_diff_indep a ha)
    u v hu huv 1 one_ne_zero

/-- **100% Unconditional Joint Differential Independence of ALL `k`-Regular Square-Partition Dilations**:
For EVERY `k ≥ 2` and ANY finite family of pairwise distinct positive integers `a_1, …, a_s`,
the `k`-regular square-partition dilations `{B_{a_i, k}(q) = P_2(q^{a_i}) / P_2(q^{k a_i})}` are
**jointly differentially independent over `ℂ(q)`**! -/
theorem kRegularSquares_dilations_diff_indep {s : ℕ} (k : ℕ+) (hk : 2 ≤ k.val)
    (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ kRegularSquares (a i) k)) := by
  have huv : ∀ i : Fin s, a i < k * a i := fun i ↦ by
    change (a i).val < k.val * (a i).val
    nlinarith [(a i).pos]
  simpa only [kRegularSquares, kRegularSquaresUnit, PNat.mul_coe] using
    squarePart_forest_quotients_diff_indep a (fun i ↦ k * a i) ha huv

/-- **100% Unconditional Joint Differential Independence of Distinct-Squares Dilations
`{Q_2(q^{a_1}), …, Q_2(q^{a_s})}` over `ℂ(q)`**! -/
theorem distinctSquares_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ kRegularSquares (a i) 2)) :=
  kRegularSquares_dilations_diff_indep 2 (by decide) a ha

/-- **100% Unconditional Joint Differential Independence of 1D Fermi–Dirac Gas Dilations
`{Z_FD^{(1)}(q^{a_1}), …, Z_FD^{(1)}(q^{a_s})}` over `ℂ(q)`**! -/
theorem fermi1D_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ (kRegularSquares (a i) 2) ^ 2)) := by
  have huv : ∀ i : Fin s, a i < 2 * a i := fun i ↦ by
    change (a i).val < 2 * (a i).val; nlinarith [(a i).pos]
  have hind := distinctSource_quotient_pow_diff_indep
    (fun m ↦ logDerivPowerPartDilated 2 m.val)
    (fun m ↦ (isUnit_powerPartDilated 2 m.val).unit)
    (fun m ↦ (m.val : ℂ))
    (fun m ↦ by exact_mod_cast m.property.ne')
    (fun m ↦ X_mul_deriv_powerPartDilated (by decide) m.property)
    (fun b hb ↦ logDerivPowerPart_2_dilations_diff_indep b hb)
    a (fun i ↦ 2 * a i) ha huv 2 (by decide)
  have heq : (fun i : Fin s ↦
      ((((isUnit_powerPartDilated 2 (a i).val).unit *
          (isUnit_powerPartDilated 2 (2 * a i).val).unit⁻¹) ^ (2 : ℤ) : (PowerSeries ℂ)ˣ) :
        PowerSeries ℂ)) = fun i ↦ (kRegularSquares (a i) 2) ^ 2 := by
    funext i
    simp only [kRegularSquares, kRegularSquaresUnit, PNat.mul_coe, PNat.val_ofNat]
    change (((_ ^ (2 : ℕ) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = _
    rw [Units.val_pow_eq_pow_val]
  rwa [heq] at hind

/-! ### 2. Unified `d = 2` Zero-Tilt Wave-Profile Engine (`SqRayProfile`) -/

/-- Formal dilation `F(q^a) ∈ ℂ[[q]]` of any formal power series `F ∈ ℂ[[q]]`. -/
def seriesDilated (F : PowerSeries ℂ) (a : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun N ↦ if N = 0 then PowerSeries.coeff 0 F
    else if a ∣ N then PowerSeries.coeff (N / a) F else 0

theorem seriesDilated_one (F : PowerSeries ℂ) : seriesDilated F 1 = F := by
  ext N; cases N <;> simp [seriesDilated]

/-- **Unified `d = 2` Elementary Zero-Tilt Stokes Profile** for ANY formal power series
`F ∈ ℂ[[q]]` whose evaluation along `q = exp(-1 / X²)` (`qRayD 3 X`) admits an exact
Laurent background `X^{polarHigh} · polarPoly(X⁻¹)` plus pure-exponential waves along the two
`d = 2` rays `{sqRay0, sqRay1}` with polynomially bounded constant amplitudes `waveAmp ℓ N`
that never vanish on the extreme ray `ℓ = 0` at primes `p`! -/
structure SqRayProfile (F : PowerSeries ℂ) where
  coeffBoundPow : ℕ
  coeffBoundC : ℝ
  coeffBound_nonneg : 0 ≤ coeffBoundC
  coeffBound : ∀ n : ℕ, ‖PowerSeries.coeff n F‖ ≤ coeffBoundC * (n + 1 : ℝ) ^ coeffBoundPow
  scalePow : ℕ
  polarHigh : ℕ
  polarPoly : Polynomial ℂ
  waveAmp : Fin 2 → ℕ+ → ℂ
  waveBoundPow : ℕ
  waveBoundC : ℝ
  waveBound_nonneg : 0 ≤ waveBoundC
  waveBound : ∀ ℓ N, ‖waveAmp ℓ N‖ ≤ waveBoundC * (N.val : ℝ) ^ waveBoundPow
  prime_amp_ne_zero : ∀ p : ℕ+, p.val.Prime → waveAmp ⟨0, by decide⟩ p ≠ 0
  decomp : ∀ᶠ X : ℝ in atTop,
    psValue F (qRayD 3 X) =
      ((X : ℂ) ^ polarHigh) * polarPoly.eval ((X : ℂ)⁻¹) +
      ((X : ℂ) ^ scalePow) * ∑' ℓN : Fin 2 × ℕ+,
        waveAmp ℓN.1 ℓN.2 * Complex.exp (-ppWaveRate 2 ℓN.1 ℓN.2 * (X : ℂ))

section SqRayEngine

private lemma sqProf_coeff_bound {F : PowerSeries ℂ} (P : SqRayProfile F) (a j n : ℕ) :
    ‖PowerSeries.coeff n (formalJet (seriesDilated F a) j)‖ ≤
      (j.factorial * P.coeffBoundC * (j + 1 : ℝ) ^ P.coeffBoundPow) *
        (n + 1 : ℝ) ^ (j + P.coeffBoundPow) := by
  rw [formalJet, PowerSeries.coeff_iterate_derivative, seriesDilated, PowerSeries.coeff_mk]
  have h1 : ‖if n + j = 0 then PowerSeries.coeff 0 F
      else if a ∣ n + j then PowerSeries.coeff ((n + j) / a) F else 0‖ ≤
      P.coeffBoundC * (n + j + 1 : ℝ) ^ P.coeffBoundPow := by
    split_ifs with h0 hdvd
    · refine (P.coeffBound 0).trans ?_
      apply mul_le_mul_of_nonneg_left _ P.coeffBound_nonneg
      exact pow_le_pow_left₀ (by norm_num)
        (by simp only [Nat.cast_zero, zero_add]; linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) j]) _
    · refine (P.coeffBound ((n + j) / a)).trans ?_
      apply mul_le_mul_of_nonneg_left _ P.coeffBound_nonneg
      have hdiv : ((n + j) / a : ℕ) ≤ n + j := Nat.div_le_self _ _
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hdiv 1) _
    · simp only [norm_zero]; exact mul_nonneg P.coeffBound_nonneg (by positivity)
  have h2 : (n + j + 1 : ℝ) ^ P.coeffBoundPow ≤
      (j + 1 : ℝ) ^ P.coeffBoundPow * (n + 1 : ℝ) ^ P.coeffBoundPow := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) j]) _
  have h3 : (((n + 1).ascFactorial j : ℕ) : ℝ) ≤ j.factorial * (n + 1 : ℝ) ^ j := by
    exact_mod_cast Nat.ascFactorial_le_factorial_mul_pow (n + 1) j
  rw [norm_mul, Complex.norm_natCast]
  calc _ ≤ (j.factorial * (n + 1 : ℝ) ^ j) *
        (P.coeffBoundC * ((j + 1 : ℝ) ^ P.coeffBoundPow * (n + 1 : ℝ) ^ P.coeffBoundPow)) :=
        mul_le_mul h3 (h1.trans (mul_le_mul_of_nonneg_left h2 P.coeffBound_nonneg))
          (norm_nonneg _) (by positivity)
    _ = (j.factorial * P.coeffBoundC * (j + 1 : ℝ) ^ P.coeffBoundPow) *
        (n + 1 : ℝ) ^ (j + P.coeffBoundPow) := by rw [pow_add]; ring

private lemma sqProf_bound_on {F : PowerSeries ℂ} (P : SqRayProfile F) (a j : ℕ)
    {q : ℂ} {r : ℝ} (h : ‖q‖ ≤ r) (n : ℕ) :
    ‖psTerm (formalJet (seriesDilated F a) j) q n‖ ≤
      (j.factorial * P.coeffBoundC * (j + 1 : ℝ) ^ P.coeffBoundPow) *
        ((n + 1 : ℝ) ^ (j + P.coeffBoundPow) * r ^ n) := by
  rw [psTerm, norm_mul, norm_pow, ← mul_assoc]
  exact mul_le_mul (sqProf_coeff_bound P a j n)
    (pow_le_pow_left₀ (norm_nonneg _) h _) (by positivity)
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.coeffBound_nonneg) (by positivity)) (by positivity))

private lemma sqProf_jet_abs {F : PowerSeries ℂ} (P : SqRayProfile F) (a j : ℕ)
    {q : ℂ} (hq : ‖q‖ < 1) :
    PSAbsAt (formalJet (seriesDilated F a) j) q := by
  obtain ⟨r, hr, h1⟩ := exists_between hq
  exact ((shifted_geom_pp (j + P.coeffBoundPow) ((norm_nonneg _).trans_lt hr) h1).mul_left _).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (sqProf_bound_on P a j hr.le)

private lemma sqProf_jet_deriv {F : PowerSeries ℂ} (P : SqRayProfile F) (a j : ℕ)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt (psValue (formalJet (seriesDilated F a) j))
      (psValue (formalJet (seriesDilated F a) (j + 1)) q) q := by
  obtain ⟨r, hr, h1⟩ := exists_between hq
  have rp := (norm_nonneg _).trans_lt hr
  let f (n : ℕ) (z : ℂ) := psTerm (formalJet (seriesDilated F a) j) z (n + 1)
  let g (n : ℕ) (z : ℂ) := psTerm (formalJet (seriesDilated F a) (j + 1)) z n
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (f n) (g n z) z := by
    have he : PowerSeries.coeff n (formalJet (seriesDilated F a) (j + 1)) =
        PowerSeries.coeff (n + 1) (formalJet (seriesDilated F a) j) * (n + 1) := by
      rw [formalJet, Function.iterate_succ_apply', PowerSeries.coeff_derivative]; rfl
    simpa [f, g, psTerm, he, mul_assoc] using
      ((hasDerivAt_pow (n + 1) z).const_mul (PowerSeries.coeff (n + 1) (formalJet (seriesDilated F a) j)))
  have hs := hasDerivAt_tsum_of_isPreconnected
    ((shifted_geom_pp ((j + 1) + P.coeffBoundPow) rp h1).mul_left
      (↑(j + 1).factorial * P.coeffBoundC * (↑(j + 1) + 1 : ℝ) ^ P.coeffBoundPow))
    (t := Metric.ball (0 : ℂ) r) Metric.isOpen_ball (convex_ball (0 : ℂ) _).isPreconnected
    (fun n z _ ↦ hd n z) (fun n z hz ↦ sqProf_bound_on P a _ (by simpa using (Metric.mem_ball.mp hz).le) n)
    (y₀ := q) (by simpa using hr)
    ((sqProf_jet_abs P a j hq).of_norm.comp_injective
      (show Function.Injective (fun n : ℕ ↦ n + 1) by intro i k hh; exact Nat.add_right_cancel hh))
    (by simpa using hr)
  have near : psValue (formalJet (seriesDilated F a) j) =ᶠ[𝓝 q]
      fun z ↦ PowerSeries.coeff 0 (formalJet (seriesDilated F a) j) + ∑' n, f n z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show q ∈ Metric.ball (0 : ℂ) 1 by simpa using hq)] with z hz
    have h := (sqProf_jet_abs P a j (by simpa using hz : ‖z‖ < 1)).of_norm.sum_add_tsum_nat_add 1
    simpa [psValue, f, psTerm] using h.symm
  exact (hs.const_add _).congr_of_eventuallyEq near

private lemma sqProf_jet_analytic {F : PowerSeries ℂ} (P : SqRayProfile F) (a j : ℕ) :
    AnalyticOnNhd ℂ (psValue (formalJet (seriesDilated F a) j)) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro q hq
  exact (sqProf_jet_deriv P a j (by simpa using hq)).differentiableAt.differentiableWithinAt

private lemma sqProf_dilated_value_eq {F : PowerSeries ℂ} {a : ℕ} (ha : 1 ≤ a) (q : ℂ) :
    psValue (seriesDilated F a) q = psValue F (q ^ a) := by
  let f (n : ℕ) : ℕ := a * n
  have hinj : Function.Injective f := fun x y h ↦ Nat.eq_of_mul_eq_mul_left ha h
  have hzero : ∀ k ∉ Set.range f, psTerm (seriesDilated F a) q k = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · exact (hk ⟨0, by simp [f, hk0]⟩).elim
    · have hnd : ¬ a ∣ k := fun ⟨n, hn⟩ ↦ hk ⟨n, hn.symm⟩
      simp [psTerm, seriesDilated, hk0, hnd]
  have hsupp : Function.support (psTerm (seriesDilated F a) q) ⊆ Set.range f := by
    intro k hk; by_contra hnot; exact hk (hzero k hnot)
  rw [psValue, ← hinj.tsum_eq hsupp, psValue]
  apply tsum_congr; intro n
  cases n with
  | zero => simp [psTerm, seriesDilated, f]
  | succ n' =>
    have han0 : a * (n' + 1) ≠ 0 := mul_ne_zero (by omega) (Nat.succ_ne_zero n')
    have hdiv : a * (n' + 1) / a = n' + 1 := Nat.mul_div_cancel_left (n' + 1) ha
    simp only [psTerm, seriesDilated, PowerSeries.coeff_mk, f, han0, ↓reduceIte,
      dvd_mul_right, hdiv, pow_mul]

/-- Exact `ℓ`-th `X`-derivative amplitude of `(σ X)^K · exp(-σ r X)`. -/
private def sqDilAmp (K : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) (X : ℝ) : ℂ :=
  ((σ : ℂ) ^ K) *
    ∑ t ∈ Finset.range (ℓ + 1),
      ((Nat.choose ℓ t * K.descFactorial t : ℕ) : ℂ) *
        (if t ≤ K then (X : ℂ) ^ (K - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)

private lemma sqDilAmp_deriv (K : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) (X : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.exp (-(((σ : ℝ) : ℂ) * r) * (y : ℂ)) * sqDilAmp K σ r ℓ y)
      (Complex.exp (-(((σ : ℝ) : ℂ) * r) * (X : ℂ)) * sqDilAmp K σ r (ℓ + 1) X) X := by
  let lam : ℂ := ((σ : ℝ) : ℂ) * r
  let f (y : ℝ) : ℂ := ((σ : ℂ) ^ K) * (y : ℂ) ^ K
  let g (y : ℝ) : ℂ := Complex.exp (-lam * (y : ℂ))
  have hf_iter (k : ℕ) (y : ℝ) :
      iteratedDeriv k f y = ((σ : ℂ) ^ K) *
        ((K.descFactorial k : ℕ) : ℂ) * (if k ≤ K then (y : ℂ) ^ (K - k) else 0) := by
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
    change iteratedDeriv k (fun z : ℝ ↦ ((σ : ℂ) ^ K) * (z : ℂ) ^ K) y = _
    rw [iteratedDeriv_const_mul_field, hpow K k y]; ring
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
        Complex.exp (-lam * (y : ℂ)) * sqDilAmp K σ r k y := by
    have hcf : ContDiff ℝ k f := contDiff_const.mul (Complex.ofRealCLM.contDiff.pow K)
    have hcg : ContDiff ℝ k g := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
    rw [iteratedDeriv_fun_mul hcf.contDiffAt hcg.contDiffAt]
    simp only [sqDilAmp, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _
    rw [hf_iter t y, hg_iter (k - t) y]
    push_cast; dsimp [lam]; ring
  have hd_leib : HasDerivAt (iteratedDeriv ℓ (fun z : ℝ ↦ f z * g z))
      (iteratedDeriv (ℓ + 1) (fun z : ℝ ↦ f z * g z) X) X := by
    have hcf : ContDiff ℝ (ℓ + 1) f := contDiff_const.mul (Complex.ofRealCLM.contDiff.pow K)
    have hcg : ContDiff ℝ (ℓ + 1) g := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
    rw [iteratedDeriv_succ]
    exact ((hcf.mul hcg).differentiable_iteratedDeriv ℓ (by exact_mod_cast Nat.lt_succ_self ℓ) X).hasDerivAt
  rw [show iteratedDeriv ℓ (fun z : ℝ ↦ f z * g z) =
      fun y : ℝ ↦ Complex.exp (-lam * (y : ℂ)) * sqDilAmp K σ r ℓ y from funext (hleib ℓ),
      hleib (ℓ + 1) X] at hd_leib
  exact hd_leib

private lemma sqDilAmp_powerClass (K : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) :
    PowerClass 0 (sqDilAmp K σ r ℓ) := by
  have hterm (t : ℕ) : PowerClass 0 (fun X : ℝ ↦
      ((σ : ℂ) ^ K) *
        (((Nat.choose ℓ t * K.descFactorial t : ℕ) : ℂ) *
          (if t ≤ K then (X : ℂ) ^ (K - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t))) := by
    by_cases ht : t ≤ K
    · simp only [ht, ↓reduceIte]
      have hpow : PowerClass 0 (fun X : ℝ ↦ (X : ℂ) ^ (K - t)) := by
        refine ⟨(K - t : ℕ), fun _ ↦ 1, RayDensity.const 1, ?_⟩
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        have h1 : raySum (fun _ ↦ (1 : ℂ)) X = 1 := by
          simp only [raySum, integral_smul_const, integral_exp_neg_Ioi_zero, one_smul]
        simp [h1, Complex.real_smul, Real.rpow_natCast]
      have hconst := PowerClass.const (((σ : ℂ) ^ K) *
        (((Nat.choose ℓ t * K.descFactorial t : ℕ) : ℂ) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)))
      have hm := hconst.mul hpow
      rw [zero_add] at hm
      exact hm.congr (Eventually.of_forall fun X ↦ by ring)
    · simp only [ht, ↓reduceIte, mul_zero, zero_mul]
      exact PowerClass.const 0
  have hsum : ∀ S : Finset ℕ, PowerClass 0 (fun X : ℝ ↦
      ∑ t ∈ S, ((σ : ℂ) ^ K) *
        (((Nat.choose ℓ t * K.descFactorial t : ℕ) : ℂ) *
          (if t ≤ K then (X : ℂ) ^ (K - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using PowerClass.const 0
    | @insert a S ha ih => simpa [Finset.sum_insert ha] using (hterm a).add ih
  exact (hsum (Finset.range (ℓ + 1))).congr (Eventually.of_forall fun X ↦ by
    simp only [sqDilAmp, Finset.mul_sum])

private lemma sqDilAmp_limit (K : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) :
    Tendsto (fun X : ℝ ↦ ((X ^ (-(K : ℝ)) : ℝ) : ℂ) * sqDilAmp K σ r ℓ X)
      atTop (𝓝 (((σ : ℂ) ^ K) * (-(((σ : ℝ) : ℂ) * r)) ^ ℓ)) := by
  have hterm (t : ℕ) (_ : t ∈ Finset.range (ℓ + 1)) :
      Tendsto (fun X : ℝ ↦ ((X ^ (-(K : ℝ)) : ℝ) : ℂ) *
        (((Nat.choose ℓ t * K.descFactorial t : ℕ) : ℂ) *
          (if t ≤ K then (X : ℂ) ^ (K - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)))
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
      by_cases htle : t ≤ K
      · simp only [htle, ↓reduceIte]
        have hpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ht0
        have hdec : Tendsto (fun X : ℝ ↦ ((X ^ (-(t : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) :=
          (Complex.continuous_ofReal.tendsto 0).comp (tendsto_rpow_neg_atTop hpos)
        have hmul := (hdec.const_mul (((Nat.choose ℓ t * K.descFactorial t : ℕ) : ℂ) *
          (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)))
        rw [mul_zero] at hmul
        refine hmul.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        have hpow : ((X ^ (-(K : ℝ)) : ℝ) : ℂ) * (X : ℂ) ^ (K - t) =
            ((X ^ (-(t : ℝ)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Real.rpow_natCast X (K - t),
              ← Real.rpow_add hX]
          congr 2; have : ((K - t : ℕ) : ℝ) = (K : ℝ) - (t : ℝ) := Nat.cast_sub htle; linarith
        linear_combination (((Nat.choose ℓ t * K.descFactorial t : ℕ) : ℂ) *
          (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)) * hpow.symm
      · simp only [htle, ↓reduceIte, mul_zero, zero_mul]; exact tendsto_const_nhds
  have hsum := tendsto_finsetSum (Finset.range (ℓ + 1)) hterm
  rw [Finset.sum_ite_eq' (Finset.range (ℓ + 1)) 0] at hsum
  simp only [Finset.mem_range.mpr (Nat.succ_pos ℓ), ↓reduceIte] at hsum
  have hmul := hsum.const_mul ((σ : ℂ) ^ K)
  refine hmul.congr fun X ↦ ?_
  simp only [sqDilAmp, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _; ring

private def sqProfDilWaveExp {F : PowerSeries ℂ} (P : SqRayProfile F)
    (σ : ℝ) (hσ : 0 < σ) (ℓ : ℕ) : WaveExpansion (Fin 2 × ℕ+) where
  rate := fun ℓN ↦ ((σ : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2
  amplitude := fun ℓN X ↦ P.waveAmp ℓN.1 ℓN.2 * sqDilAmp P.scalePow σ (ppWaveRate 2 ℓN.1 ℓN.2) ℓ X
  budget := fun ℓN ↦
    (‖P.waveAmp ℓN.1 ℓN.2‖ *
      (‖(σ : ℂ) ^ P.scalePow‖ *
        ∑ t ∈ Finset.range (ℓ + 1),
          ((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℝ) *
            (σ * ‖ppWaveRate 2 ℓN.1 ℓN.2‖) ^ (ℓ - t))) *
      Real.exp (-(σ * (ppWaveRate 2 ℓN.1 ℓN.2).re))
  loss := P.scalePow
  re_nonneg := fun ℓN ↦ by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hσ.le (ppWaveRate_re_pos (by decide) ℓN.1 ℓN.2).le
  budget_nonneg := fun _ ↦
    mul_nonneg (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
          (pow_nonneg (mul_nonneg hσ.le (norm_nonneg _)) _))))
      (Real.exp_nonneg _)
  summable_budget := by
    rw [← (Equiv.sigmaEquivProd (Fin 2) ℕ+).summable_iff]
    refine (summable_sigma_of_nonneg fun _ ↦
      mul_nonneg (mul_nonneg (norm_nonneg _)
        (mul_nonneg (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
            (pow_nonneg (mul_nonneg hσ.le (norm_nonneg _)) _))))
        (Real.exp_nonneg _)).mpr ⟨fun j ↦ ?_, hasSum_fintype _ |>.summable⟩
    have hc : 0 < σ * (ppRay 2 j.val).re := mul_pos hσ (ppRay_re_pos (by decide) j.isLt)
    let Ksum : ℝ := ∑ t ∈ Finset.range (ℓ + 1),
      ((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℝ) * (1 + σ * ‖ppRay 2 j.val‖) ^ ℓ
    let C : ℝ := P.waveBoundC * (‖(σ : ℂ) ^ P.scalePow‖ * Ksum)
    have hdom := (summable_pow_mul_exp_neg_rpow (d := 2) (by decide) hc (P.waveBoundPow + ℓ)).mul_left C
    refine Summable.of_nonneg_of_le (fun _ ↦
      mul_nonneg (mul_nonneg (norm_nonneg _)
        (mul_nonneg (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
            (pow_nonneg (mul_nonneg hσ.le (norm_nonneg _)) _))))
        (Real.exp_nonneg _)) (fun N ↦ ?_) hdom
    have hN1 : (1 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast N.property
    have hrpow_le : (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) ≤ (N.val : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 / ((2 : ℕ) : ℝ)) ≤ 1)
    have hnorm_rate : ‖ppWaveRate 2 j N‖ ≤ ‖ppRay 2 j.val‖ * (N.val : ℝ) := by
      rw [ppWaveRate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_comm]
      exact mul_le_mul_of_nonneg_left hrpow_le (norm_nonneg _)
    have hsum_le : (∑ t ∈ Finset.range (ℓ + 1),
          ((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℝ) *
            (σ * ‖ppWaveRate 2 j N‖) ^ (ℓ - t)) ≤ Ksum * (N.val : ℝ) ^ ℓ := by
      dsimp only [Ksum]; rw [Finset.sum_mul]
      apply Finset.sum_le_sum; intro t _
      have h1 : σ * ‖ppWaveRate 2 j N‖ ≤ (1 + σ * ‖ppRay 2 j.val‖) * (N.val : ℝ) := by
        have := mul_le_mul_of_nonneg_left hnorm_rate hσ.le
        nlinarith [norm_nonneg (ppRay 2 j.val)]
      have h2 : (σ * ‖ppWaveRate 2 j N‖) ^ (ℓ - t) ≤
          (1 + σ * ‖ppRay 2 j.val‖) ^ ℓ * (N.val : ℝ) ^ ℓ := by
        calc (σ * ‖ppWaveRate 2 j N‖) ^ (ℓ - t)
            ≤ ((1 + σ * ‖ppRay 2 j.val‖) * (N.val : ℝ)) ^ (ℓ - t) :=
              pow_le_pow_left₀ (by positivity) h1 _
          _ ≤ ((1 + σ * ‖ppRay 2 j.val‖) * (N.val : ℝ)) ^ ℓ :=
              pow_le_pow_right₀ (by nlinarith [mul_nonneg hσ.le (norm_nonneg (ppRay 2 j.val))])
                (Nat.sub_le ℓ t)
          _ = (1 + σ * ‖ppRay 2 j.val‖) ^ ℓ * (N.val : ℝ) ^ ℓ := mul_pow ..
      calc _ ≤ ((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℝ) *
              ((1 + σ * ‖ppRay 2 j.val‖) ^ ℓ * (N.val : ℝ) ^ ℓ) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    have hre : -(σ * (ppWaveRate 2 j N).re) =
        -(σ * (ppRay 2 j.val).re) * (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := by
      simp [ppWaveRate, Complex.mul_re]; ring
    simp only [Equiv.sigmaEquivProd_apply]
    rw [hre]
    have hwb := P.waveBound j N
    have hwb_nn : 0 ≤ P.waveBoundC * (N.val : ℝ) ^ P.waveBoundPow :=
      mul_nonneg P.waveBound_nonneg (by positivity)
    calc _ ≤ (P.waveBoundC * (N.val : ℝ) ^ P.waveBoundPow *
            (‖(σ : ℂ) ^ P.scalePow‖ * (Ksum * (N.val : ℝ) ^ ℓ))) *
          Real.exp (-(σ * (ppRay 2 j.val).re) * (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by gcongr
      _ = C * ((N.val : ℝ) ^ (P.waveBoundPow + ℓ) *
          Real.exp (-(σ * (ppRay 2 j.val).re) * (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) := by
          dsimp [C]; rw [pow_add]; ring
  bound := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX ℓN
    have hre_eq : (((σ : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2).re = σ * (ppWaveRate 2 ℓN.1 ℓN.2).re := by
      simp [Complex.mul_re]
    have hcancel_rhs : ∀ A : ℝ,
        A * Real.exp (-(σ * (ppWaveRate 2 ℓN.1 ℓN.2).re)) *
          Real.exp (σ * (ppWaveRate 2 ℓN.1 ℓN.2).re) * X ^ P.scalePow = A * X ^ P.scalePow := fun A ↦ by
      rw [mul_assoc A, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [hre_eq, hcancel_rhs, norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold sqDilAmp
    rw [norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc ‖∑ t ∈ Finset.range (ℓ + 1),
            ((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℂ) *
              (if t ≤ P.scalePow then (X : ℂ) ^ (P.scalePow - t) else 0) *
                (-(((σ : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2)) ^ (ℓ - t)‖
        ≤ ∑ t ∈ Finset.range (ℓ + 1),
            ‖((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℂ) *
              (if t ≤ P.scalePow then (X : ℂ) ^ (P.scalePow - t) else 0) *
                (-(((σ : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2)) ^ (ℓ - t)‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range (ℓ + 1),
            ((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℝ) *
              (σ * ‖ppWaveRate 2 ℓN.1 ℓN.2‖) ^ (ℓ - t) * X ^ P.scalePow := by
          apply Finset.sum_le_sum; intro t _
          rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_neg, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
          split_ifs with ht
          · rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hX)]
            have hpow : X ^ (P.scalePow - t) ≤ X ^ P.scalePow := pow_le_pow_right₀ hX (Nat.sub_le _ _)
            calc _ = ((Nat.choose ℓ t * P.scalePow.descFactorial t : ℕ) : ℝ) *
                    (σ * ‖ppWaveRate 2 ℓN.1 ℓN.2‖) ^ (ℓ - t) * X ^ (P.scalePow - t) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
          · simp; positivity
      _ = _ := (Finset.sum_mul _ _ _).symm

private lemma sqProfDilWaveExp_value_zero {F : PowerSeries ℂ} (P : SqRayProfile F)
    (σ : ℝ) (hσ : 0 < σ) :
    ∀ᶠ X : ℝ in atTop,
      (sqProfDilWaveExp P σ hσ 0).value X =
        ((((σ * X : ℝ) : ℂ) ^ P.scalePow)) * ∑' ℓN : Fin 2 × ℕ+,
          P.waveAmp ℓN.1 ℓN.2 * Complex.exp (-ppWaveRate 2 ℓN.1 ℓN.2 * ((σ * X : ℝ) : ℂ)) := by
  filter_upwards [(sqProfDilWaveExp P σ hσ 0).norm_summable] with X _
  unfold WaveExpansion.value
  rw [← tsum_mul_left]
  apply tsum_congr; intro ℓN
  simp only [WaveExpansion.term, sqProfDilWaveExp, sqDilAmp, Nat.zero_add, Finset.range_one,
    Finset.sum_singleton, Nat.choose_zero_right, Nat.descFactorial_zero, mul_one, Nat.cast_one,
    Nat.zero_le, ↓reduceIte, Nat.sub_zero, pow_zero, one_mul, Complex.ofReal_mul, mul_pow]
  have hexp : -(((σ : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2) * (X : ℂ) =
      -ppWaveRate 2 ℓN.1 ℓN.2 * ((σ : ℂ) * (X : ℂ)) := by ring
  rw [hexp]; ring

private lemma sqProfDilWaveExp_derivatives {F : PowerSeries ℂ} (P : SqRayProfile F)
    (σ : ℝ) (hσ : 0 < σ) (ℓ : ℕ) :
    iteratedDeriv ℓ (sqProfDilWaveExp P σ hσ 0).value =ᶠ[atTop]
      (sqProfDilWaveExp P σ hσ ℓ).value := by
  apply WaveExpansion.iteratedDeriv_value (sqProfDilWaveExp P σ hσ)
  intro k
  filter_upwards with X ℓN
  have hd_a := (sqDilAmp_deriv P.scalePow σ (ppWaveRate 2 ℓN.1 ℓN.2) k X).const_mul (P.waveAmp ℓN.1 ℓN.2)
  convert hd_a using 1
  · funext y; simp only [WaveExpansion.term, sqProfDilWaveExp]; ring
  · simp only [WaveExpansion.term, sqProfDilWaveExp]; ring

private lemma sqProfDilPolar_props {F : PowerSeries ℂ} (P : SqRayProfile F) (σ : ℝ) (ℓ : ℕ) :
    let pol (X : ℝ) : ℂ := (((σ * X : ℝ) : ℂ) ^ P.polarHigh) *
      P.polarPoly.eval ((((σ * X : ℝ) : ℂ))⁻¹)
    PowerClass 0 (iteratedDeriv ℓ pol) ∧
      ∃ (B : ℝ) (L : ℕ), 0 ≤ B ∧ ∀ᶠ X : ℝ in atTop, ‖iteratedDeriv ℓ pol X‖ ≤ B * X ^ L := by
  intro pol
  have hmon (k : ℕ) (c : ℂ) :
      let f (X : ℝ) : ℂ := c * (X : ℂ) ^ P.polarHigh * ((X : ℂ)⁻¹) ^ k
      PowerClass 0 (iteratedDeriv ℓ f) ∧
      ∃ (B : ℝ) (L : ℕ), 0 ≤ B ∧ ∀ᶠ X : ℝ in atTop, ‖iteratedDeriv ℓ f X‖ ≤ B * X ^ L := by
    intro f
    let e : ℤ := (P.polarHigh : ℤ) - (k : ℤ)
    have hf_eq : ∀ X > 0, f X = c * ((X ^ (e : ℝ) : ℝ) : ℂ) := fun X hX ↦ by
      dsimp only [f, e]
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Real.rpow_sub hX,
          Real.rpow_natCast, Real.rpow_natCast, Complex.ofReal_div, Complex.ofReal_pow,
          Complex.ofReal_pow, inv_pow, div_eq_mul_inv, mul_assoc]
    have hiter (m : ℕ) : ∀ X > 0, iteratedDeriv m f X =
        ppFall e c m * ((X ^ ((e : ℝ) - (m : ℝ)) : ℝ) : ℂ) := by
      induction m with
      | zero =>
        intro X hX; simp only [iteratedDeriv_zero, ppFall, Nat.cast_zero, sub_zero]; exact hf_eq X hX
      | succ m ih =>
        intro X hX; rw [iteratedDeriv_succ]
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
      rw [hiter ℓ X hX, h1, zero_add, Complex.real_smul, mul_comm]; push_cast; rfl
    · refine ⟨‖ppFall e c ℓ‖, P.polarHigh, norm_nonneg _, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
      have hX0 : 0 < X := zero_lt_one.trans_le hX
      rw [hiter ℓ X hX0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hX0.le _)]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hle : (e : ℝ) - (ℓ : ℝ) ≤ (P.polarHigh : ℝ) := by
        dsimp [e]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) ℓ]
      have hr := Real.rpow_le_rpow_of_exponent_le hX hle
      rwa [Real.rpow_natCast] at hr
  have hpol_eq : pol = fun X : ℝ ↦ ∑ k ∈ P.polarPoly.support,
      (((σ : ℂ) ^ P.polarHigh * P.polarPoly.coeff k * ((σ : ℂ)⁻¹) ^ k) *
        (X : ℂ) ^ P.polarHigh * ((X : ℂ)⁻¹) ^ k) := by
    funext X; dsimp only [pol]
    rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Complex.ofReal_mul, mul_pow, mul_inv, mul_pow]; ring
  have hsum_rec : ∀ S : Finset ℕ,
      let f (X : ℝ) : ℂ := ∑ k ∈ S,
        (((σ : ℂ) ^ P.polarHigh * P.polarPoly.coeff k * ((σ : ℂ)⁻¹) ^ k) *
          (X : ℂ) ^ P.polarHigh * ((X : ℂ)⁻¹) ^ k)
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
      let fk (X : ℝ) : ℂ := ((σ : ℂ) ^ P.polarHigh * P.polarPoly.coeff k * ((σ : ℂ)⁻¹) ^ k) *
        (X : ℂ) ^ P.polarHigh * ((X : ℂ)⁻¹) ^ k
      let fS (X : ℝ) : ℂ := ∑ r ∈ S,
        (((σ : ℂ) ^ P.polarHigh * P.polarPoly.coeff r * ((σ : ℂ)⁻¹) ^ r) *
          (X : ℂ) ^ P.polarHigh * ((X : ℂ)⁻¹) ^ r)
      have hcdk : ∀ X > 0, ContDiffAt ℝ ℓ fk X := fun X hX ↦ by
        have hco : ContDiffAt ℝ ℓ (fun y : ℝ ↦ (y : ℂ)) X := Complex.ofRealCLM.contDiff.contDiffAt
        exact (contDiffAt_const.mul (hco.pow P.polarHigh)).mul
          ((hco.inv (Complex.ofReal_ne_zero.mpr hX.ne')).pow k)
      have hsplit : ∀ X > 0, iteratedDeriv ℓ (fun y ↦ fk y + fS y) X =
          iteratedDeriv ℓ fk X + iteratedDeriv ℓ fS X := fun X hX ↦
        iteratedDeriv_fun_add (hcdk X hX) (hcdS X hX)
      obtain ⟨hpck, Bk, Lk, hBk, hbk⟩ := hmon k _
      have hfun_eq : (fun X : ℝ ↦ ∑ r ∈ insert k S,
          (((σ : ℂ) ^ P.polarHigh * P.polarPoly.coeff r * ((σ : ℂ)⁻¹) ^ r) *
            (X : ℂ) ^ P.polarHigh * ((X : ℂ)⁻¹) ^ r)) = fun X : ℝ ↦ fk X + fS X := by
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

private def sqProfDilPolarCoeff {F : PowerSeries ℂ} (P : SqRayProfile F)
    (σ : ℝ) (_hσ : 0 < σ) (ℓ : ℕ) : Physical.RayCoefficient :=
  let pol (X : ℝ) : ℂ := (((σ * X : ℝ) : ℂ) ^ P.polarHigh) *
    P.polarPoly.eval ((((σ * X : ℝ) : ℂ))⁻¹)
  let hb := (sqProfDilPolar_props P σ ℓ).2
  { value := iteratedDeriv ℓ pol
    budget := Classical.choose hb
    loss := Classical.choose (Classical.choose_spec hb)
    nonneg := (Classical.choose_spec (Classical.choose_spec hb)).1
    bound := (Classical.choose_spec (Classical.choose_spec hb)).2 }

private lemma sqProfDilPolarCoeff_powerClass {F : PowerSeries ℂ} (P : SqRayProfile F)
    (σ : ℝ) (hσ : 0 < σ) (ℓ : ℕ) : PowerClass 0 (sqProfDilPolarCoeff P σ hσ ℓ).value :=
  (sqProfDilPolar_props P σ ℓ).1

private def sqProfDilWaveTracked {F : PowerSeries ℂ} (P : SqRayProfile F)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (ℓ : ℕ) :
    PPTracked 2 (ppDilKeyRate 2 A) where
  Index := Fin 2 × ℕ+
  exp := sqProfDilWaveExp P (ppDilScale 2 m.val) (ppDilScale_pos m.pos) ℓ
  finite_window R := by
    have hσ := ppDilScale_pos (d := 2) m.pos
    have hsub : {ℓN : Fin 2 × ℕ+ | (((ppDilScale 2 m.val : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2).re ≤ R} ⊆
        ⋃ j : Fin 2, (fun N ↦ (j, N)) '' {N : ℕ+ | (ppWaveRate 2 j N).re ≤ R / ppDilScale 2 m.val} := by
      rintro ⟨j, N⟩ h
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
      exact mem_iUnion.mpr ⟨j, N, (le_div_iff₀' hσ).mpr h, rfl⟩
    refine (Set.finite_iUnion fun j ↦ ?_).subset hsub
    apply Set.Finite.image
    have hc := ppRay_re_pos (d := 2) (by decide) j.isLt
    obtain ⟨M, hM⟩ := exists_nat_gt (max 0 ((R / ppDilScale 2 m.val) / (ppRay 2 j.val).re) ^ 2)
    have hsubN : {N : ℕ+ | (ppWaveRate 2 j N).re ≤ R / ppDilScale 2 m.val} ⊆
        Subtype.val ⁻¹' (Set.Iic M) := by
      intro N hN; change (ppWaveRate 2 j N).re ≤ _ at hN
      have hre : (ppWaveRate 2 j N).re = (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) * (ppRay 2 j.val).re := by
        simp [ppWaveRate, Complex.mul_re]
      rw [hre] at hN
      have hle : (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) ≤
          max 0 ((R / ppDilScale 2 m.val) / (ppRay 2 j.val).re) :=
        ((le_div_iff₀ hc).mpr hN).trans (le_max_right _ _)
      have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hle 2
      rw [← Real.rpow_natCast ((N.val : ℝ) ^ _), ← Real.rpow_mul (Nat.cast_nonneg _)] at hpow
      norm_num at hpow
      change N.val ≤ M; exact_mod_cast (hpow.trans hM.le)
    exact ((Set.finite_Iic M).preimage Subtype.val_injective.injOn).subset hsubN
  pc0 := fun ℓN ↦ by
    have h := (PowerClass.const (P.waveAmp ℓN.1 ℓN.2)).mul
      (sqDilAmp_powerClass P.scalePow (ppDilScale 2 m.val) (ppWaveRate 2 ℓN.1 ℓN.2) ℓ)
    rwa [zero_add] at h
  halfSpace := fun ℓN ↦ by
    change 0 ≤ ppRotIm 2 (((ppDilScale 2 m.val : ℝ) : ℂ) *
      ((((ℓN.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) : ℝ) : ℂ) * ppRay 2 ℓN.1.val))
    rw [← mul_assoc, ← Complex.ofReal_mul, ppRotIm_smul_real]
    exact mul_nonneg (mul_nonneg (ppDilScale_pos m.pos).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (ppRotIm_nonneg (by decide) ℓN.1.isLt)
  extreme_range := fun ℓN h0 ↦ by
    change ppRotIm 2 (((ppDilScale 2 m.val : ℝ) : ℂ) *
      ((((ℓN.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) : ℝ) : ℂ) * ppRay 2 ℓN.1.val)) = 0 at h0
    rw [← mul_assoc, ← Complex.ofReal_mul, ppRotIm_smul_real] at h0
    have hpos : 0 < ppDilScale 2 m.val * (ℓN.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) :=
      mul_pos (ppDilScale_pos m.pos) (Real.rpow_pos_of_pos (by exact_mod_cast ℓN.2.pos) _)
    have hray0 : ppRotIm 2 (ppRay 2 ℓN.1.val) = 0 := (mul_eq_zero.mp h0).resolve_left hpos.ne'
    have hℓ0 : ℓN.1.val = 0 := by
      by_contra hne; linarith [ppRotIm_other_pos (d := 2) (by decide) (Nat.pos_of_ne_zero hne) ℓN.1.isLt]
    refine ⟨ppDilModeExp (by decide) A m ℓN.2, ?_⟩
    rw [ppDilKeyRate_modeExp (by decide) hA hdiv ℓN.2]
    change ((ppDilScale 2 m.val : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2 = _
    congr 2; exact Fin.ext hℓ0

private def sqProfDilJetTracked {F : PowerSeries ℂ} (P : SqRayProfile F)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    PPTracked 2 (ppDilKeyRate 2 A) :=
  let rec go : ℕ → PPTracked 2 (ppDilKeyRate 2 A)
    | 0 =>
      let q0 := ppQPolyRayCoeff (d := 2) (by decide) j 0
      let b0 := sqProfDilPolarCoeff P (ppDilScale 2 m.val) (ppDilScale_pos m.pos) 0
      (PPTracked.ofCoeff q0 (ppQPolyRayCoeff_powerClass (d := 2) (by decide) j 0)).mul
        ((PPTracked.ofCoeff b0 (sqProfDilPolarCoeff_powerClass P _ _ 0)).add
          (sqProfDilWaveTracked P hA m hdiv 0))
    | k + 1 =>
      let qk := ppQPolyRayCoeff (d := 2) (by decide) j (k + 1)
      let bk := sqProfDilPolarCoeff P (ppDilScale 2 m.val) (ppDilScale_pos m.pos) (k + 1)
      (go k).add ((PPTracked.ofCoeff qk (ppQPolyRayCoeff_powerClass (d := 2) (by decide) j (k + 1))).mul
        ((PPTracked.ofCoeff bk (sqProfDilPolarCoeff_powerClass P _ _ (k + 1))).add
          (sqProfDilWaveTracked P hA m hdiv (k + 1))))
  go j

private lemma sqProfDilJetTracked_value {F : PowerSeries ℂ} (P : SqRayProfile F)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      (sqProfDilJetTracked P hA m hdiv j).exp.value X =
        psValue (formalJet (seriesDilated F m.val) j) (qRayD 3 X) := by
  let σ := ppDilScale 2 m.val
  let hσ := ppDilScale_pos (d := 2) m.pos
  let pol (X : ℝ) : ℂ := (((σ * X : ℝ) : ℂ) ^ P.polarHigh) *
    P.polarPoly.eval ((((σ * X : ℝ) : ℂ))⁻¹)
  have hval_split : ∀ᶠ X : ℝ in atTop,
      psValue (seriesDilated F m.val) (qRayD 3 X) =
        pol X + (sqProfDilWaveExp P σ hσ 0).value X := by
    have hdec := (tendsto_id.const_mul_atTop hσ).eventually P.decomp
    filter_upwards [eventually_gt_atTop (0 : ℝ), hdec, sqProfDilWaveExp_value_zero P σ hσ] with X _ hD hW
    simp only [id_eq] at hD
    rw [sqProf_dilated_value_eq m.pos, ← ppQRay_dilScale (d := 2) (by decide) m X, hD, hW]
  have hiter_split (ℓ : ℕ) :
      iteratedDeriv ℓ (fun X ↦ psValue (seriesDilated F m.val) (qRayD 3 X)) =ᶠ[atTop]
        fun X ↦ (sqProfDilPolarCoeff P σ hσ ℓ).value X + (sqProfDilWaveExp P σ hσ ℓ).value X := by
    obtain ⟨L, hL⟩ := eventually_atTop.1 hval_split
    have h1 : iteratedDeriv ℓ (fun X ↦ psValue (seriesDilated F m.val) (qRayD 3 X)) =ᶠ[atTop]
        iteratedDeriv ℓ (fun X ↦ pol X + (sqProfDilWaveExp P σ hσ 0).value X) :=
      (eventually_gt_atTop L).mono fun X hX ↦ by
        have hloc : (fun x ↦ psValue (seriesDilated F m.val) (qRayD 3 x)) =ᶠ[𝓝 X]
            fun x ↦ pol x + (sqProfDilWaveExp P σ hσ 0).value x :=
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
          simpa only [iteratedDeriv_zero] using (hlin.fun_pow P.polarHigh).fun_mul hpoly
        | succ r ihr => rw [iteratedDeriv_succ]; exact ihr.deriv
      exact (han k).differentiableAt
    have hwav_diff (k : ℕ) : ∀ᶠ X : ℝ in atTop,
        DifferentiableAt ℝ (iteratedDeriv k (sqProfDilWaveExp P σ hσ 0).value) X := by
      have hd_val := (sqProfDilWaveExp P σ hσ k).hasDerivAt_value (sqProfDilWaveExp P σ hσ (k + 1))
        (Eventually.of_forall fun X ℓN ↦ by
          have hd_a := (sqDilAmp_deriv P.scalePow σ (ppWaveRate 2 ℓN.1 ℓN.2) k X).const_mul (P.waveAmp ℓN.1 ℓN.2)
          convert hd_a using 1
          · funext y; simp only [WaveExpansion.term, sqProfDilWaveExp]; ring
          · simp only [WaveExpansion.term, sqProfDilWaveExp]; ring)
      obtain ⟨Lw, hLw⟩ := eventually_atTop.1 (sqProfDilWaveExp_derivatives P σ hσ k)
      filter_upwards [hd_val, eventually_gt_atTop Lw] with X hX hLX
      exact hX.differentiableAt.congr_of_eventuallyEq ((lt_mem_nhds hLX).mono fun y hy ↦ hLw y hy.le)
    have hadd_iter : ∀ k, iteratedDeriv k (fun X ↦ pol X + (sqProfDilWaveExp P σ hσ 0).value X) =ᶠ[atTop]
        fun X ↦ iteratedDeriv k pol X + iteratedDeriv k (sqProfDilWaveExp P σ hσ 0).value X := by
      intro k
      induction k with
      | zero => filter_upwards with X; simp
      | succ k ih =>
        obtain ⟨L1, hL1⟩ := eventually_atTop.1 ih
        filter_upwards [eventually_gt_atTop (max L1 0), hwav_diff k] with X hX hdw
        have hX0 : 0 < X := lt_of_le_of_lt (le_max_right _ _) hX
        have hL1X : L1 < X := lt_of_le_of_lt (le_max_left _ _) hX
        rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ]
        have hnear : iteratedDeriv k (fun y ↦ pol y + (sqProfDilWaveExp P σ hσ 0).value y) =ᶠ[𝓝 X]
            fun y ↦ iteratedDeriv k pol y + iteratedDeriv k (sqProfDilWaveExp P σ hσ 0).value y :=
          (lt_mem_nhds hL1X).mono fun y hy ↦ hL1 y hy.le
        rw [hnear.deriv_eq, deriv_fun_add (hpol_cd k X hX0) hdw]
    filter_upwards [h1, hadd_iter ℓ, sqProfDilWaveExp_derivatives P σ hσ ℓ] with X h1' h2' h3'
    rw [h1', h2', h3']; rfl
  have hjet_eq_iter : ∀ᶠ X : ℝ in atTop,
      psValue (formalJet (seriesDilated F m.val) j) (qRayD 3 X) =
        ∑ ℓ ∈ Finset.range (j + 1),
          qPolyCoeff 3 j ℓ X *
            ((sqProfDilPolarCoeff P σ hσ ℓ).value X + (sqProfDilWaveExp P σ hσ ℓ).value X) := by
    have hsmooth : ∀ ℓ ≤ j, ∀ᶠ X : ℝ in atTop,
        DifferentiableAt ℝ (iteratedDeriv ℓ (fun y ↦ psValue (seriesDilated F m.val) (qRayD 3 y))) X := by
      intro ℓ _
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have han : ∀ r, AnalyticAt ℝ (iteratedDeriv r (fun y ↦ psValue (seriesDilated F m.val) (qRayD 3 y))) X := by
        intro r; induction r with
        | zero =>
          exact (((sqProf_jet_analytic P m.val 0) _ (by simpa using qRayD_disk hX)).restrictScalars
            (𝕜 := ℝ)).comp (qRayD_analytic hX)
        | succ r ihr => rw [iteratedDeriv_succ]; exact ihr.deriv
      exact (han ℓ).differentiableAt
    have hiterQ (k : ℕ) {X : ℝ} (hX : 0 < X) :
        psValue (formalJet (seriesDilated F m.val) k) (qRayD 3 X) =
          iterQDeriv 3 k (fun y ↦ psValue (seriesDilated F m.val) (qRayD 3 y)) X := by
      induction k generalizing X with
      | zero => rfl
      | succ k ihk =>
        change _ = invSpeedD 3 X * deriv (iterQDeriv 3 k _) X
        have hnear : iterQDeriv 3 k (fun y ↦ psValue (seriesDilated F m.val) (qRayD 3 y)) =ᶠ[𝓝 X]
            fun y ↦ psValue (formalJet (seriesDilated F m.val) k) (qRayD 3 y) :=
          (lt_mem_nhds hX).mono fun y hy ↦ (ihk hy).symm
        have hcomp : HasDerivAt (fun y ↦ psValue (formalJet (seriesDilated F m.val) k) (qRayD 3 y))
            (speedD 3 X * psValue (formalJet (seriesDilated F m.val) (k + 1)) (qRayD 3 X)) X := by
          simpa [Function.comp_def, mul_comm] using!
            ((sqProf_jet_deriv P m.val k (qRayD_disk hX)).scomp X (qRayD_deriv (by decide) hX))
        rw [hnear.deriv_eq, hcomp.deriv, ← mul_assoc, invSpeedD_mul_speedD (by decide) hX, one_mul]
    have hchain := iterQDeriv_eq_sum (d := 3) (by decide) (fun y ↦ psValue (seriesDilated F m.val) (qRayD 3 y)) j hsmooth
    have hall := (Filter.eventually_all_finset (Finset.range (j + 1))).mpr fun ℓ _ ↦ hiter_split ℓ
    filter_upwards [eventually_gt_atTop (0 : ℝ), hchain, hall] with X hX hch hl
    rw [hiterQ j hX, hch]
    apply Finset.sum_congr rfl; intro ℓ hℓ; rw [hl ℓ hℓ]
  have hgo_val : ∀ k ≤ j, ∀ᶠ X : ℝ in atTop,
      (sqProfDilJetTracked.go P hA m hdiv j k).exp.value X =
        ∑ ℓ ∈ Finset.range (k + 1),
          qPolyCoeff 3 j ℓ X *
            ((sqProfDilPolarCoeff P σ hσ ℓ).value X + (sqProfDilWaveExp P σ hσ ℓ).value X) := by
    intro k hk
    induction k with
    | zero =>
      filter_upwards [(PPTracked.ofCoeff (ppQPolyRayCoeff (d := 2) (by decide) j 0) _).exp.value_mul _,
        (PPTracked.ofCoeff (sqProfDilPolarCoeff P σ hσ 0) _).exp.value_add _] with X hm ha
      change ((PPTracked.ofCoeff (ppQPolyRayCoeff (d := 2) (by decide) j 0) _).exp.mul
        ((PPTracked.ofCoeff (sqProfDilPolarCoeff P σ hσ 0) _).exp.add
          (sqProfDilWaveTracked P hA m hdiv 0).exp)).value X = _
      rw [hm, ha]
      have hrc (a : Physical.RayCoefficient) : a.expansion.value X = a.value X := by
        unfold WaveExpansion.value WaveExpansion.term Physical.RayCoefficient.expansion; simp
      change (ppQPolyRayCoeff (d := 2) (by decide) j 0).expansion.value X *
        ((sqProfDilPolarCoeff P σ hσ 0).expansion.value X + (sqProfDilWaveExp P σ hσ 0).value X) = _
      rw [hrc, hrc]
      have hq : (ppQPolyRayCoeff (d := 2) (by decide) j 0).value X = qPolyCoeff 3 j 0 X := by
        unfold ppQPolyRayCoeff; split_ifs; rfl
      rw [hq]; simp
    | succ k ih =>
      filter_upwards [ih (by omega),
        (sqProfDilJetTracked.go P hA m hdiv j k).exp.value_add _,
        (PPTracked.ofCoeff (ppQPolyRayCoeff (d := 2) (by decide) j (k + 1)) _).exp.value_mul _,
        (PPTracked.ofCoeff (sqProfDilPolarCoeff P σ hσ (k + 1)) _).exp.value_add _] with X hprev hadd hm ha
      change ((sqProfDilJetTracked.go P hA m hdiv j k).exp.add
        ((PPTracked.ofCoeff (ppQPolyRayCoeff (d := 2) (by decide) j (k + 1)) _).exp.mul
          ((PPTracked.ofCoeff (sqProfDilPolarCoeff P σ hσ (k + 1)) _).exp.add
            (sqProfDilWaveTracked P hA m hdiv (k + 1)).exp))).value X = _
      rw [hadd, hprev, hm, ha]
      conv_rhs => rw [Finset.sum_range_succ]
      congr 1
      have hrc (a : Physical.RayCoefficient) : a.expansion.value X = a.value X := by
        unfold WaveExpansion.value WaveExpansion.term Physical.RayCoefficient.expansion; simp
      change (ppQPolyRayCoeff (d := 2) (by decide) j (k + 1)).expansion.value X *
        ((sqProfDilPolarCoeff P σ hσ (k + 1)).expansion.value X +
          (sqProfDilWaveExp P σ hσ (k + 1)).value X) = _
      rw [hrc, hrc]
      have hq : (ppQPolyRayCoeff (d := 2) (by decide) j (k + 1)).value X = qPolyCoeff 3 j (k + 1) X := by
        unfold ppQPolyRayCoeff; split_ifs; rfl
      rw [hq]
  filter_upwards [hgo_val j le_rfl, hjet_eq_iter] with X h1 h2
  exact h1.trans h2.symm

private lemma sqProfDilJetTracked_marked_eq {F : PowerSeries ℂ} (P : SqRayProfile F)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    (sqProfDilJetTracked P hA m hdiv j).marked =
      ∑ ℓ ∈ Finset.range (j + 1),
        MvPowerSeries.C (Germ.ofFun (qPolyCoeff 3 j ℓ)) *
          (MvPowerSeries.C (Germ.ofFun (sqProfDilPolarCoeff P (ppDilScale 2 m.val) (ppDilScale_pos m.pos) ℓ).value) +
            (sqProfDilWaveTracked P hA m hdiv ℓ).marked) := by
  have hinj := ppDilKeyRate_injective (d := 2) (by decide) hA
  have hface := fun k ↦ ppRotIm_dilKeyRate (d := 2) (A := A) (by decide) k
  have hgo : ∀ k ≤ j, (sqProfDilJetTracked.go P hA m hdiv j k).marked =
      ∑ ℓ ∈ Finset.range (k + 1),
        MvPowerSeries.C (Germ.ofFun (qPolyCoeff 3 j ℓ)) *
          (MvPowerSeries.C (Germ.ofFun (sqProfDilPolarCoeff P (ppDilScale 2 m.val) (ppDilScale_pos m.pos) ℓ).value) +
            (sqProfDilWaveTracked P hA m hdiv ℓ).marked) := by
    intro k hk
    have hq_val (r : ℕ) : (ppQPolyRayCoeff (d := 2) (by decide) j r).value = qPolyCoeff 3 j r := by
      unfold ppQPolyRayCoeff; split_ifs <;> rfl
    induction k with
    | zero =>
      simp only [sqProfDilJetTracked.go, PPTracked.marked_mul _ _ hinj hface,
        PPTracked.marked_add, PPTracked.marked_ofCoeff _ _ hinj, hq_val,
        Nat.zero_add, Finset.range_one, Finset.sum_singleton]
    | succ k ih =>
      simp only [sqProfDilJetTracked.go, PPTracked.marked_add, PPTracked.marked_mul _ _ hinj hface,
        PPTracked.marked_ofCoeff _ _ hinj, hq_val, ih (by omega), Finset.sum_range_succ]
  exact hgo j le_rfl

private lemma sqProfDilWaveTracked_coeff {F : PowerSeries ℂ} (P : SqRayProfile F)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (ℓ : ℕ) (k : Core 2 →₀ ℕ) :
    ((∀ N : ℕ+, k ≠ ppDilModeExp (by decide) A m N) →
        MvPowerSeries.coeff k (sqProfDilWaveTracked P hA m hdiv ℓ).marked = 0) ∧
    (∀ N : ℕ+, k = ppDilModeExp (by decide) A m N →
        MvPowerSeries.coeff k (sqProfDilWaveTracked P hA m hdiv ℓ).marked =
          Germ.ofFun ((sqProfDilWaveExp P (ppDilScale 2 m.val) (ppDilScale_pos m.pos) ℓ).amplitude
            (⟨0, by decide⟩, N))) := by
  have hinj := ppDilKeyRate_injective (d := 2) (by decide) hA
  have hfiber (ℓN : Fin 2 × ℕ+) :
      (sqProfDilWaveTracked P hA m hdiv ℓ).exp.rate ℓN = ppDilKeyRate 2 A k ↔
        ℓN.1 = ⟨0, by decide⟩ ∧ ppDilModeExp (by decide) A m ℓN.2 = k := by
    constructor
    · intro hrate
      have hrot : ppRotIm 2 ((sqProfDilWaveTracked P hA m hdiv ℓ).exp.rate ℓN) = 0 := by
        rw [hrate]; exact ppRotIm_dilKeyRate (by decide) k
      have hℓ0 : ℓN.1.val = 0 := by
        change ppRotIm 2 (((ppDilScale 2 m.val : ℝ) : ℂ) *
          ((((ℓN.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) : ℝ) : ℂ) * ppRay 2 ℓN.1.val)) = 0 at hrot
        rw [← mul_assoc, ← Complex.ofReal_mul, ppRotIm_smul_real] at hrot
        have hpos : 0 < ppDilScale 2 m.val * (ℓN.2.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) :=
          mul_pos (ppDilScale_pos m.pos) (Real.rpow_pos_of_pos (by exact_mod_cast ℓN.2.pos) _)
        have hray0 := (mul_eq_zero.mp hrot).resolve_left hpos.ne'
        by_contra hne; linarith [ppRotIm_other_pos (d := 2) (by decide) (Nat.pos_of_ne_zero hne) ℓN.1.isLt]
      have hℓeq : ℓN.1 = ⟨0, by decide⟩ := Fin.ext hℓ0
      refine ⟨hℓeq, hinj ?_⟩
      rw [ppDilKeyRate_modeExp (by decide) hA hdiv ℓN.2, ← hrate]
      change ((ppDilScale 2 m.val : ℝ) : ℂ) * ppWaveRate 2 ⟨0, by decide⟩ ℓN.2 =
        ((ppDilScale 2 m.val : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2
      rw [hℓeq]
    · rintro ⟨hℓ, hk⟩
      rw [← hk, ppDilKeyRate_modeExp (by decide) hA hdiv ℓN.2]
      change ((ppDilScale 2 m.val : ℝ) : ℂ) * ppWaveRate 2 ℓN.1 ℓN.2 = _
      rw [hℓ]
  have hmode_inj : Function.Injective (ppDilModeExp (d := 2) (by decide) A m) := fun N₁ N₂ h ↦ by
    have h1 := congrArg (ppDilKeyRate 2 A) h
    rw [ppDilKeyRate_modeExp (by decide) hA hdiv N₁, ppDilKeyRate_modeExp (by decide) hA hdiv N₂] at h1
    have h2 := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ppDilScale_pos (d := 2) m.property).ne') h1
    have h3 := Complex.ofReal_injective (mul_right_cancel₀ (ppExtremeRay_ne_zero (by decide)) h2)
    have h4 : (N₁.val : ℝ) = (N₂.val : ℝ) :=
      (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num)).mp h3
    exact PNat.eq (Nat.cast_injective h4)
  constructor
  · intro hall
    change (∑ i : PPTracked.Fiber (sqProfDilWaveTracked P hA m hdiv ℓ) k, _) = 0
    have : IsEmpty (PPTracked.Fiber (sqProfDilWaveTracked P hA m hdiv ℓ) k) :=
      ⟨fun i ↦ hall i.val.2 ((hfiber i.val).mp i.property).2.symm⟩
    simp
  · intro N hN
    change (∑ i : PPTracked.Fiber (sqProfDilWaveTracked P hA m hdiv ℓ) k, _) = _
    let i₀ : PPTracked.Fiber (sqProfDilWaveTracked P hA m hdiv ℓ) k :=
      ⟨(⟨0, by decide⟩, N), (hfiber _).mpr ⟨rfl, hN.symm⟩⟩
    have huniq : ∀ i : PPTracked.Fiber (sqProfDilWaveTracked P hA m hdiv ℓ) k, i = i₀ := fun i ↦ by
      obtain ⟨hℓ, hmode⟩ := (hfiber i.val).mp i.property
      exact Subtype.ext (Prod.ext hℓ (hmode_inj (hmode.trans hN)))
    rw [Finset.sum_eq_single i₀ (fun i _ hne ↦ (hne (huniq i)).elim) (fun h ↦ (h (Finset.mem_univ _)).elim)]
    rfl

private theorem sqRayProfile_dilations_diff_indep_dec {F : PowerSeries ℂ} (P : SqRayProfile F)
    {s : ℕ} (a : Fin s → ℕ+) (hdec : ∀ i j : Fin s, i < j → (a j).val < (a i).val) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ seriesDilated F (a i).val)) := by
  classical
  let A : ℕ := ∏ i : Fin s, (a i).val
  have hA_pos : 0 < A := Finset.prod_pos fun i _ ↦ (a i).property
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
  let fTracked : ι → PPTracked 2 (ppDilKeyRate 2 A) :=
    fun r ↦ sqProfDilJetTracked P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val
  obtain ⟨E, hE_val, hE_marked⟩ := ppEvalPolyMv_tracked (d := 2) (by decide) hA_pos fTracked Q₁
  have hE_zero : ∀ᶠ X : ℝ in atTop, E.exp.value X = 0 := by
    have hall_f : ∀ᶠ X : ℝ in atTop, ∀ r : ι,
        (fTracked r).exp.value X =
          psValue (formalJet (seriesDilated F (a (ofLex r).1).val) (ofLex r).2.val) (qRayD 3 X) :=
      ((Filter.eventually_all_finset (Finset.univ : Finset ι)).mpr fun r _ ↦
        sqProfDilJetTracked_value P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val).mono
        fun X hX r ↦ hX r (Finset.mem_univ r)
    filter_upwards [eventually_gt_atTop (0 : ℝ), hE_val, hall_f] with X hX hEv hfv
    rw [hEv]
    have hcongr_ev : MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD 3 X))
          (fun r ↦ (fTracked r).exp.value X) Q₁ =
        MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD 3 X))
          (fun r ↦ psValue (formalJet (seriesDilated F (a (ofLex r).1).val) (ofLex r).2.val)
            (qRayD 3 X)) Q₁ := by congr 1; funext r; exact hfv r
    rw [hcongr_ev, ppEval₂_optionToPolyMv]
    let g_X : Option (Fin s × ℕ) → ℂ := fun u ↦
      psValue (jointSeriesCoordinates (fun i ↦ seriesDilated F (a i).val) u) (qRayD 3 X)
    have hps_coord : Option.elim' (qRayD 3 X)
          (fun r ↦ psValue (formalJet (seriesDilated F (a (ofLex r).1).val) (ofLex r).2.val)
            (qRayD 3 X)) = g_X ∘ emb := by
      funext u; cases u with
      | none => exact (ps_nome_abs (qRayD 3 X)).2.symm
      | some r => rfl
    have habs_coord : ∀ u : Option (Fin s × ℕ),
        PSAbsAt (jointSeriesCoordinates (fun i ↦ seriesDilated F (a i).val) u) (qRayD 3 X) := by
      rintro (_ | ⟨i, j⟩)
      · exact (ps_nome_abs _).1
      · exact sqProf_jet_abs P (a i).val j (qRayD_disk hX)
    rw [hps_coord, ← MvPolynomial.eval_rename emb g_X Q₀, hQ_eq]
    have hps := (ps_polynomial_value Q habs_coord).2
    rw [← hps, hQ_eval]; simp [psValue, psTerm]
  have hmarked_zero : MvPolynomial.aeval (R := Polynomial ℂ) (fun r ↦ (fTracked r).marked) Q₁ = 0 := by
    rw [← hE_marked]; exact E.separate_zero hE_zero
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
    rw [show fTracked c = sqProfDilJetTracked P hA_pos (a (ofLex c).1) (hA_dvd (ofLex c).1) (ofLex c).2.val from rfl,
        sqProfDilJetTracked_marked_eq, map_sum] at hc_nz
    obtain ⟨ℓ, _, hℓ_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc_nz
    rw [MvPowerSeries.coeff_C_mul] at hℓ_nz
    have hadd_nz := right_ne_zero_of_mul hℓ_nz
    have hmap_ne0 : (m + Finsupp.single r 1).mapDomain marks ≠ 0 := fun h0 ↦ by
      have h1 := DFunLike.congr_fun h0 (marks r)
      rw [ppMapDomain_apply_inj hmarks_inj, Finsupp.add_apply, Finsupp.single_eq_same] at h1
      simp at h1
    rw [map_add, MvPowerSeries.coeff_C] at hadd_nz
    simp only [hmap_ne0, ↓reduceIte, zero_add] at hadd_nz
    have hex : ∃ N : ℕ+, (m + Finsupp.single r 1).mapDomain marks = ppDilModeExp (by decide) A (a (ofLex c).1) N := by
      by_contra hnot; push Not at hnot
      exact hadd_nz ((sqProfDilWaveTracked_coeff P hA_pos (a (ofLex c).1) (hA_dvd (ofLex c).1) ℓ _).1 hnot)
    obtain ⟨N, hN⟩ := hex
    have he_pos := ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd (ofLex c).1) N
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
    let σ := ppDilScale 2 (a i).val
    let hσ := ppDilScale_pos (d := 2) (a i).pos
    let M (X : ℝ) : Matrix (Fin J) (Fin J) ℂ :=
      Matrix.of fun ν j ↦ ((ppDilExp (d := 2) (by decide) A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
        ∑ ℓ ∈ Finset.range (j.val + 1),
          qPolyCoeff 3 j.val ℓ X *
            (sqProfDilWaveExp P σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf (toLex (i, ν))) X
    have hB_eq (ν j : Fin J) : B (toLex (i, ν)) (toLex (i, j)) = Germ.ofFun (fun X ↦ M X ν j) := by
      let r := toLex (i, ν); let c := toLex (i, j)
      change MvPowerSeries.coeff (Finsupp.single r (mStar r)) (MvPowerSeries.pderiv r (fRestr c)) = _
      rw [MvPowerSeries.coeff_pderiv]
      have he_pos := ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd i) (primeOf r)
      have hmr_eq : mStar r = ppDilExp (d := 2) (by decide) A (a i) (primeOf r) - 1 := rfl
      have hsucc : mStar r + 1 = ppDilExp (d := 2) (by decide) A (a i) (primeOf r) := by
        rw [hmr_eq]; exact Nat.sub_add_cancel he_pos
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
      rw [hmap_s, show fTracked c = sqProfDilJetTracked P hA_pos (a i) (hA_dvd i) j.val from rfl,
          sqProfDilJetTracked_marked_eq, map_sum]
      have hterm_eq (ℓ : ℕ) :
          MvPowerSeries.coeff (ppDilModeExp (by decide) A (a i) (primeOf r))
            (MvPowerSeries.C (Germ.ofFun (qPolyCoeff 3 j.val ℓ)) *
              (MvPowerSeries.C (Germ.ofFun (sqProfDilPolarCoeff P σ hσ ℓ).value) +
                (sqProfDilWaveTracked P hA_pos (a i) (hA_dvd i) ℓ).marked)) =
          Germ.ofFun (fun X ↦ qPolyCoeff 3 j.val ℓ X *
            (sqProfDilWaveExp P σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf r) X) := by
        rw [MvPowerSeries.coeff_C_mul, map_add, MvPowerSeries.coeff_C]
        simp only [hmode_ne0, ↓reduceIte, zero_add]
        rw [(sqProfDilWaveTracked_coeff P hA_pos (a i) (hA_dvd i) ℓ _).2 (primeOf r) rfl]; rfl
      rw [Finset.sum_congr rfl (fun ℓ _ ↦ hterm_eq ℓ)]
      have hnat : ((mStar r : RayGerm) + 1) =
          Germ.ofFun (fun _ : ℝ ↦ ((ppDilExp (d := 2) (by decide) A (a i) (primeOf r) : ℕ) : ℂ)) := by
        rw [show ((mStar r : RayGerm) + 1) = ((mStar r + 1 : ℕ) : RayGerm) by push_cast; rfl, hsucc]; rfl
      rw [hnat, mul_comm]
      let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
      change H _ * ∑ ℓ ∈ Finset.range (j.val + 1), H _ = _
      rw [← map_sum, ← map_mul]; apply Germ.coe_eq.mpr
      filter_upwards with X
      change ((ppDilExp (d := 2) (by decide) A (a i) (primeOf r) : ℕ) : ℂ) *
        (∑ ℓ ∈ Finset.range (j.val + 1), fun X ↦ qPolyCoeff 3 j.val ℓ X *
          (sqProfDilWaveExp P σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf r) X) X = M X ν j
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
      ((X ^ (-((3 * j.val : ℕ) : ℝ) - (P.scalePow : ℝ)) : ℝ) : ℂ)
    let Mscaled (X : ℝ) : Matrix (Fin J) (Fin J) ℂ := Matrix.of fun ν j ↦ colScale X j * M X ν j
    let rowC (ν : Fin J) : ℂ := ((ppDilExp (d := 2) (by decide) A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
      P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) * ((σ : ℂ) ^ P.scalePow)
    let α (ν : Fin J) : ℂ := -(((2 : ℂ)⁻¹) * (((σ : ℝ) : ℂ) * ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν)))))
    let L : Matrix (Fin J) (Fin J) ℂ := Matrix.of fun ν j ↦ rowC ν * (α ν) ^ j.val
    have hlim_entry (ν j : Fin J) : Tendsto (fun X ↦ Mscaled X ν j) atTop (𝓝 (L ν j)) := by
      have hterm_lim (ℓ : ℕ) (hℓ : ℓ ∈ Finset.range (j.val + 1)) :
          Tendsto (fun X : ℝ ↦ colScale X j * (qPolyCoeff 3 j.val ℓ X *
            (sqProfDilWaveExp P σ hσ ℓ).amplitude (⟨0, by decide⟩, primeOf (toLex (i, ν))) X))
          atTop (𝓝 (if ℓ = j.val then
            P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
              ((σ : ℂ) ^ P.scalePow) * (α ν) ^ j.val else 0)) := by
        have hℓ_le : ℓ ≤ j.val := by have := Finset.mem_range.mp hℓ; omega
        have hamp_lim := (sqDilAmp_limit P.scalePow σ (ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν)))) ℓ).const_mul
          (P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))))
        by_cases hℓj : ℓ = j.val
        · subst hℓj; simp only [↓reduceIte]
          have hq_lim := qPolyCoeff_diag_limit (d := 3) (by decide) j.val
          have hprod := hq_lim.mul hamp_lim
          have hlim_eq : ((((3 - 1 : ℕ) : ℂ)⁻¹) ^ j.val) *
              (P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
                (((σ : ℂ) ^ P.scalePow) * (-(((σ : ℝ) : ℂ) * ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν))))) ^ j.val)) =
              P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
                ((σ : ℂ) ^ P.scalePow) * (α ν) ^ j.val := by
            have hdsub : ((3 - 1 : ℕ) : ℂ) = 2 := by norm_num
            rw [hdsub]; dsimp only [α]
            rw [show -((2 : ℂ)⁻¹ * (((σ : ℝ) : ℂ) * ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν))))) =
                (2 : ℂ)⁻¹ * (-(((σ : ℝ) : ℂ) * ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν))))) by ring, mul_pow]
            ring
          rw [hlim_eq] at hprod
          refine hprod.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
          have hcol : colScale X j =
              ((X ^ (-((3 * j.val : ℕ) : ℝ)) : ℝ) : ℂ) * ((X ^ (-(P.scalePow : ℝ)) : ℝ) : ℂ) := by
            dsimp [colScale]; rw [← Complex.ofReal_mul, ← Real.rpow_add hX]; congr 2
          rw [hcol]
          change ((X ^ (-((3 * j.val : ℕ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff 3 j.val j.val X *
            (P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
              (((X ^ (-(P.scalePow : ℝ)) : ℝ) : ℂ) *
                sqDilAmp P.scalePow σ (ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν)))) j.val X)) = _
          simp only [sqProfDilWaveExp]; ring
        · simp only [hℓj, ↓reduceIte]
          have hlt : (((3 : ℤ) * (j.val : ℤ)) - ((j.val - ℓ : ℕ) : ℤ)) < (((3 * j.val : ℕ) : ℤ)) := by
            have : 0 < j.val - ℓ := by omega
            push_cast; omega
          have hq_lim := (qPolyCoeff_QCoeff (d := 3) (by decide) j.val ℓ hℓ_le).tendsto_zero_of_lt (by decide) hlt
          have hprod := hq_lim.mul hamp_lim
          rw [zero_mul] at hprod
          refine hprod.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
          have hcol : colScale X j =
              ((X ^ (-(((3 * j.val : ℕ) : ℤ) : ℝ)) : ℝ) : ℂ) * ((X ^ (-(P.scalePow : ℝ)) : ℝ) : ℂ) := by
            dsimp [colScale]; rw [← Complex.ofReal_mul, ← Real.rpow_add hX]; congr 2
          rw [hcol]
          change ((X ^ (-(((3 * j.val : ℕ) : ℤ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff 3 j.val ℓ X *
            (P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
              (((X ^ (-(P.scalePow : ℝ)) : ℝ) : ℂ) *
                sqDilAmp P.scalePow σ (ppWaveRate 2 ⟨0, by decide⟩ (primeOf (toLex (i, ν)))) ℓ X)) = _
          simp only [sqProfDilWaveExp]; ring
      have hsum := (tendsto_finsetSum (Finset.range (j.val + 1)) hterm_lim).const_mul
        ((ppDilExp (d := 2) (by decide) A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ)
      rw [Finset.sum_ite_eq' (Finset.range (j.val + 1)) j.val] at hsum
      simp only [Finset.mem_range.mpr (Nat.lt_succ_self j.val), ↓reduceIte] at hsum
      have hL_eq : ((ppDilExp (d := 2) (by decide) A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
          (P.waveAmp ⟨0, by decide⟩ (primeOf (toLex (i, ν))) *
            ((σ : ℂ) ^ P.scalePow) * (α ν) ^ j.val) = L ν j := by
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
      have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
      apply mul_ne_zero
      · apply Finset.prod_ne_zero_iff.mpr; intro ν _
        exact mul_ne_zero
          (mul_ne_zero (by exact_mod_cast (ppDilExp_pos (d := 2) (by decide) hA_pos (hA_dvd i) _).ne')
            (P.prime_amp_ne_zero _ (hprime_prime (toLex (i, ν)))))
          (pow_ne_zero _ hσ0)
      · rw [Matrix.det_vandermonde_ne_zero_iff]
        intro ν₁ ν₂ hα
        have h1 := neg_inj.mp hα
        have h2 := mul_left_cancel₀ (inv_ne_zero (two_ne_zero (α := ℂ))) h1
        have h3 := mul_left_cancel₀ hσ0 h2
        have h4 := Complex.ofReal_injective (mul_right_cancel₀ (ppExtremeRay_ne_zero (by decide)) h3)
        have h5 := Nat.cast_injective ((Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num)).mp h4)
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

/-- **Master `d = 2` Zero-Tilt Dilation Independence Theorem**:
For ANY formal power series `F` with `P : SqRayProfile F` and ANY finite family of pairwise
distinct positive integers `a_1, …, a_s`, the dilations `{F(q^{a_1}), …, F(q^{a_s})}` are
**jointly differentially independent over `ℂ(q)`**! -/
theorem sqRayProfile_dilations_diff_indep {F : PowerSeries ℂ} (P : SqRayProfile F)
    {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ seriesDilated F (a i).val)) := by
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
  have hindep_dec := sqRayProfile_dilations_diff_indep_dec P (a ∘ π) hdec
  let e : Option (Fin s × ℕ) ≃ Option (Fin s × ℕ) :=
    Equiv.optionCongr (π.prodCongr (Equiv.refl ℕ))
  have hcomp : jointSeriesCoordinates (fun i ↦ seriesDilated F ((a ∘ π) i).val) =
      jointSeriesCoordinates (fun i ↦ seriesDilated F (a i).val) ∘ e := by
    funext u; cases u <;> rfl
  rw [hcomp] at hindep_dec
  exact (algebraicIndependent_equiv' e rfl).mp hindep_dec

/-- **Master `d = 2` Zero-Tilt Differential Transcendence Theorem**:
For ANY `F` with `P : SqRayProfile F`, `F` is differentially transcendental over `ℂ(q)`! -/
theorem sqRayProfile_non_ade {F : PowerSeries ℂ} (P : SqRayProfile F) :
    AlgebraicIndependent ℂ (seriesCoordinates F) := by
  have hind := sqRayProfile_dilations_diff_indep P (fun _ : Fin 1 ↦ 1) (fun i j _ ↦ Subsingleton.elim i j)
  have heq : (fun _ : Fin 1 ↦ seriesDilated F (1 : ℕ+).val) = fun _ ↦ F := by
    funext _; exact seriesDilated_one F
  rw [heq] at hind
  exact single_diffTrans_of_joint hind

end SqRayEngine

/-! ### 3. 100% Unconditional Square-Divisor Generating Function `L_{2, 0}(q) = ∑_{N ≥ 1} d_□(N) q^N` -/

/-- Number of square divisors `d_□(N) = #{n ≥ 1 : n² ∣ N}` for `N ≥ 1`. -/
def squareDivCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n ↦ n ^ 2 ∣ N)).card

/-- Formal square-divisor generating function
`L_{2, 0}(q) = ∑_{n ≥ 1} q^{n²} / (1 - q^{n²}) = ∑_{N ≥ 1} d_□(N) q^N ∈ ℂ[[q]]`. -/
def squareDivisorSeries : PowerSeries ℂ :=
  PowerSeries.mk fun N ↦ if N = 0 then 0 else (squareDivCount N : ℂ)

/-- Dilated square-divisor generating function `L_{2, 0}(q^a)`. -/
def squareDivisorDilated (a : ℕ) : PowerSeries ℂ :=
  seriesDilated squareDivisorSeries a

/-- Leading sub-polar constant `∫_{-∞}^{∞} (1 / (exp(u²) - 1) - 1 / u²) du`
(equal to `√π · ζ(1/2)`). -/
def sqDivConst : ℂ :=
  ∫ u : ℝ, if u = 0 then (-1 / 2 : ℂ) else (((1 / (Real.exp (u ^ 2) - 1) - 1 / u ^ 2 : ℝ) : ℂ))

private def sqDivFunc (t : ℝ) (x : ℝ) : ℂ :=
  if x = 0 then (-1 / 2 : ℂ) else (((1 / (Real.exp (t * x ^ 2) - 1) - 1 / (t * x ^ 2) : ℝ) : ℂ))

private lemma sqDivFunc_eq_x2_sqRem {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ((x : ℂ) ^ 2) * sqRem t x = sqDivFunc t x + (1 / 2 : ℂ) := by
  by_cases hx : x = 0
  · subst hx; simp [sqDivFunc]; ring
  · have h4 := sqRem_identity ht x
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    have hx2 : (x : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hxC
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hmul : (x : ℂ) ^ 2 * ((x : ℂ) ^ 2 * sqRem t x) =
        (x : ℂ) ^ 2 * (sqDivFunc t x + (1 / 2 : ℂ)) := by
      have hpow : (x : ℂ) ^ 2 * ((x : ℂ) ^ 2 * sqRem t x) = (x : ℂ) ^ 4 * sqRem t x := by ring
      rw [hpow, h4]
      simp only [sqFunc, sqDivFunc, hx, ↓reduceIte]
      push_cast
      field_simp [hxC, htC]
    exact mul_left_cancel₀ hx2 hmul

private lemma sqDivFunc_continuous {t : ℝ} (ht : 0 < t) : Continuous (sqDivFunc t) := by
  have hfun : sqDivFunc t = fun x : ℝ ↦ ((x : ℂ) ^ 2) * sqRem t x - (1 / 2 : ℂ) := by
    funext x; linear_combination -(sqDivFunc_eq_x2_sqRem ht x)
  rw [hfun]
  exact ((Complex.continuous_ofReal.pow 2).mul (sqRem_continuous ht)).sub continuous_const

private lemma sqDivFunc_norm_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖sqDivFunc t x‖ ≤ if x = 0 then 1 / 2 else 1 / (t * x ^ 2) := by
  by_cases hx : x = 0
  · subst hx; simp [sqDivFunc]
  · simp only [sqDivFunc, hx, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
    have hu : 0 < t * x ^ 2 := mul_pos ht (sq_pos_of_ne_zero hx)
    have hgt : t * x ^ 2 < Real.exp (t * x ^ 2) - 1 := by
      have h := Real.sum_le_exp_of_nonneg hu.le 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at h
      have hsq : 0 < (t * x ^ 2) ^ 2 / 2 := by positivity
      linarith
    have hpos_e : 0 < Real.exp (t * x ^ 2) - 1 := hu.trans hgt
    have h1 : 1 / (Real.exp (t * x ^ 2) - 1) ≤ 1 / (t * x ^ 2) :=
      one_div_le_one_div_of_le hu hgt.le
    have h2 : 0 ≤ 1 / (Real.exp (t * x ^ 2) - 1) := by positivity
    rw [abs_of_nonpos (by linarith)]
    linarith

private lemma sqDivFunc_integrable {t : ℝ} (ht : 0 < t) : Integrable (sqDivFunc t) := by
  let C : ℝ := max 2 (2 / t)
  have hbase : Integrable (fun x : ℝ ↦ C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  refine hbase.mono' (sqDivFunc_continuous ht).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  by_cases hx1 : x ^ 2 ≤ 1
  · by_cases hx0 : x = 0
    · subst hx0
      have h1 := sqDivFunc_norm_le ht 0; simp only [↓reduceIte] at h1
      calc ‖sqDivFunc t 0‖ ≤ 1 / 2 := h1
        _ ≤ 2 := by norm_num
        _ ≤ C := le_max_left _ _
        _ = C * (1 + 0 ^ 2)⁻¹ := by simp
    · have hu : 0 < t * x ^ 2 := mul_pos ht (sq_pos_of_ne_zero hx0)
      have hbd : ‖sqDivFunc t x‖ ≤ 1 := by
        simp only [sqDivFunc, hx0, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
        have hgt : t * x ^ 2 < Real.exp (t * x ^ 2) - 1 := by
          have h := Real.sum_le_exp_of_nonneg hu.le 3
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
            Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
            Nat.factorial_two, Nat.cast_ofNat] at h
          have hsq : 0 < (t * x ^ 2) ^ 2 / 2 := by positivity
          linarith
        have hpos_e : 0 < Real.exp (t * x ^ 2) - 1 := hu.trans hgt
        have hle1 : 1 / (t * x ^ 2) - 1 / (Real.exp (t * x ^ 2) - 1) ≤ 1 := by
          have hnum : Real.exp (t * x ^ 2) - 1 - t * x ^ 2 ≤ (t * x ^ 2) * (Real.exp (t * x ^ 2) - 1) := by
            have h1 : 1 + t * x ^ 2 ≤ Real.exp (t * x ^ 2) := by linarith [Real.add_one_le_exp (t * x ^ 2)]
            have h2 : (Real.exp (t * x ^ 2) - 1) - (t * x ^ 2) * (Real.exp (t * x ^ 2) - 1) ≤ t * x ^ 2 := by
              -- Use `1 - e^{-u} ≤ u` equivalently `(e^u - 1) ≤ u e^u`!
              have he : Real.exp (-(t * x ^ 2)) ≥ 1 - t * x ^ 2 := by linarith [Real.add_one_le_exp (-(t * x ^ 2))]
              have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos (t * x ^ 2)).le
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
              nlinarith
            linarith
          rw [div_sub_div _ _ hu.ne' hpos_e.ne', one_mul, mul_one, div_le_one (mul_pos hu hpos_e)]
          exact hnum
        rw [abs_of_nonpos (by have := one_div_le_one_div_of_le hu hgt.le; linarith)]
        linarith
      have h1 : (1 : ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
        rw [le_mul_inv_iff₀ (by positivity)]; linarith
      exact hbd.trans (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · push Not at hx1
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx1
    have hnorm := sqDivFunc_norm_le ht x; simp only [hx0, ↓reduceIte] at hnorm
    have h1 : 1 / (t * x ^ 2) ≤ (2 / t) * (1 + x ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : (2 / t) * (t * x ^ 2) = 2 * x ^ 2 := by field_simp [ht.ne']
      linarith
    exact hnorm.trans (h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

private lemma sqDivFunc_isBigO {t : ℝ} (ht : 0 < t) :
    (sqDivFunc t) =O[cocompact ℝ] fun x : ℝ ↦ |x| ^ (-(2 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / t, Filter.hasBasis_cocompact.eventually_iff.mpr
    ⟨Metric.closedBall (0 : ℝ) 1, isCompact_closedBall 0 1, fun x hx ↦ ?_⟩⟩
  have hgt : 1 < |x| := by
    have hnot : ¬ dist x 0 ≤ 1 := fun h ↦ hx (Metric.mem_closedBall.mpr h)
    rw [Real.dist_eq, sub_zero] at hnot; linarith
  have hx0 : x ≠ 0 := by rintro rfl; simp at hgt; linarith
  have hnorm := sqDivFunc_norm_le ht x; simp only [hx0, ↓reduceIte] at hnorm
  have hrpow : ‖|x| ^ (-(2 : ℝ))‖ = (x ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
        Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, sq_abs]
  rw [hrpow]
  calc ‖sqDivFunc t x‖ ≤ 1 / (t * x ^ 2) := hnorm
    _ = (1 / t) * (x ^ 2)⁻¹ := by ring

/-- Exact 2nd derivative of `𝓕 (sqRem t)` on `ξ > 0` (mirroring `iteratedDeriv_four_fourier_sqRem`). -/
private theorem iteratedDeriv_two_fourier_sqRem {t : ℝ} (ht : 0 < t) {ξ : ℝ} (hξ : 0 < ξ) :
    iteratedDeriv 2 (𝓕 (sqRem t)) ξ =
      ((2 * Real.pi : ℂ) ^ 2) *
        ∑' m : ℕ+, (1 / (2 * I * (m.val : ℂ))) *
          (sqA1 t m * Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (ξ : ℂ)) -
           sqA2 t m * Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (ξ : ℂ))) := by
  let term (k : ℕ) (m : ℕ+) (y : ℝ) : ℂ :=
    (1 / (2 * I * (m.val : ℂ))) *
      ((-2 * (Real.pi : ℂ) * sqA1 t m) ^ k *
          Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (y : ℂ)) / sqA1 t m -
       (-2 * (Real.pi : ℂ) * sqA2 t m) ^ k *
          Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (y : ℂ)) / sqA2 t m)
  have hnorm_a1 (m : ℕ+) : ‖sqA1 t m‖ = sqAlpha t m * Real.sqrt 2 := by
    rw [sqA1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqAlpha_pos ht m)]
    congr 1; rw [Complex.norm_def, Complex.normSq_apply]; norm_num
  have hnorm_a2 (m : ℕ+) : ‖sqA2 t m‖ = sqAlpha t m * Real.sqrt 2 := by
    rw [sqA2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqAlpha_pos ht m)]
    congr 1; rw [Complex.norm_def, Complex.normSq_apply]; norm_num
  have hα_split (m : ℕ+) : sqAlpha t m = Real.sqrt (Real.pi / t) * Real.sqrt (m.val : ℝ) := by
    unfold sqAlpha
    rw [show Real.pi * (m.val : ℝ) / t = (Real.pi / t) * (m.val : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
  have hterm_bound (k : ℕ) (a : ℝ) (ha : 0 < a) (m : ℕ+) (y : ℝ) (hy : a ≤ y) :
      ‖term k m y‖ ≤
        ((2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k *
          (Real.sqrt (t / Real.pi) / Real.sqrt 2)) *
        ((m.val : ℝ) ^ k * Real.exp (-(2 * Real.pi * Real.sqrt (Real.pi / t) * a) * Real.sqrt (m.val : ℝ))) := by
    let c : ℝ := 2 * Real.pi * Real.sqrt (Real.pi / t) * a
    let C : ℝ := (2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k *
      (Real.sqrt (t / Real.pi) / Real.sqrt 2)
    have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.property
    have hm_sqrt : (1 : ℝ) ≤ Real.sqrt (m.val : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
    have hre_bound : Real.exp (-2 * Real.pi * sqAlpha t m * y) ≤
        Real.exp (-c * Real.sqrt (m.val : ℝ)) := by
      apply Real.exp_le_exp.mpr; rw [hα_split m]; dsimp [c]
      have hpos : 0 ≤ 2 * Real.pi * Real.sqrt (Real.pi / t) * Real.sqrt (m.val : ℝ) := by positivity
      nlinarith
    have hpiece (A : ℂ) (hre : A.re = sqAlpha t m) (hnA : ‖A‖ = sqAlpha t m * Real.sqrt 2) :
        ‖(-2 * (Real.pi : ℂ) * A) ^ k * Complex.exp (-2 * (Real.pi : ℂ) * A * (y : ℂ)) / A‖ ≤
          C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by
      rw [norm_div, norm_mul, norm_pow, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_exp, hnA]
      have hre_exp : (-2 * (Real.pi : ℂ) * A * (y : ℂ)).re = -2 * Real.pi * sqAlpha t m * y := by
        simp [Complex.mul_re, hre]
      rw [hre_exp]
      have hinv_le : (sqAlpha t m * Real.sqrt 2)⁻¹ ≤ Real.sqrt (t / Real.pi) / Real.sqrt 2 := by
        rw [hα_split m, mul_assoc, mul_inv, div_eq_mul_inv]
        have h1 : (Real.sqrt (Real.pi / t))⁻¹ = Real.sqrt (t / Real.pi) := by
          rw [Real.sqrt_div ht.le, Real.sqrt_div Real.pi_pos.le, inv_div]
        rw [show (Real.sqrt (Real.pi * t⁻¹))⁻¹ = Real.sqrt (t / Real.pi) by rw [← div_eq_mul_inv, h1]]
        have h2 : (Real.sqrt (m.val : ℝ) * Real.sqrt 2)⁻¹ ≤ (Real.sqrt 2)⁻¹ := by
          apply inv_anti₀ (Real.sqrt_pos.mpr zero_lt_two); nlinarith [Real.sqrt_pos.mpr zero_lt_two]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have hpow_le : (2 * Real.pi * (sqAlpha t m * Real.sqrt 2)) ^ k ≤
          (2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k * (m.val : ℝ) ^ k := by
        rw [hα_split m, show 2 * Real.pi * (Real.sqrt (Real.pi / t) * Real.sqrt (m.val : ℝ) *
            Real.sqrt 2) = (2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) *
            Real.sqrt (m.val : ℝ) by ring, mul_pow]
        gcongr
        have h2 : Real.sqrt (m.val : ℝ) ^ 2 = (m.val : ℝ) := Real.sq_sqrt (by positivity)
        nlinarith [Real.sqrt_nonneg (m.val : ℝ)]
      have hα_pos : 0 < sqAlpha t m := sqAlpha_pos ht m
      rw [div_eq_mul_inv]
      calc (2 * Real.pi * (sqAlpha t m * Real.sqrt 2)) ^ k *
            Real.exp (-2 * Real.pi * sqAlpha t m * y) * (sqAlpha t m * Real.sqrt 2)⁻¹
          ≤ ((2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ k * (m.val : ℝ) ^ k) *
            Real.exp (-c * Real.sqrt (m.val : ℝ)) * (Real.sqrt (t / Real.pi) / Real.sqrt 2) := by gcongr
        _ = C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by dsimp [C]; ring
    have hpref : ‖(1 : ℂ) / (2 * I * (m.val : ℂ))‖ ≤ 1 / 2 := by
      rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one,
          Complex.norm_natCast]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    dsimp only [term]; rw [norm_mul]
    have hsub := (norm_sub_le _ _).trans (add_le_add
      (hpiece (sqA1 t m) (sqA1_re m) (hnorm_a1 m))
      (hpiece (sqA2 t m) (sqA2_re m) (hnorm_a2 m)))
    calc ‖(1 : ℂ) / (2 * I * (m.val : ℂ))‖ * _
        ≤ (1 / 2) * (C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) +
            C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ)))) :=
          mul_le_mul hpref hsub (norm_nonneg _) (by positivity)
      _ = C * ((m.val : ℝ) ^ k * Real.exp (-c * Real.sqrt (m.val : ℝ))) := by ring
  have hdiff_step (k : ℕ) (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y : ℝ ↦ ∑' m : ℕ+, term k m y) (∑' m : ℕ+, term (k + 1) m x) x := by
    let a : ℝ := x / 2; let b : ℝ := x + 1
    have ha : 0 < a := half_pos hx
    have hmem : x ∈ Ioo a b := ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
    have hd_each (m : ℕ+) (y : ℝ) : HasDerivAt (term k m) (term (k + 1) m y) y := by
      have h1 : HasDerivAt (fun z : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (z : ℂ)))
          ((-2 * (Real.pi : ℂ) * sqA1 t m) *
            Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (y : ℂ))) y := by
        have hlin : HasDerivAt (fun z : ℝ ↦ (-2 * (Real.pi : ℂ) * sqA1 t m) * (z : ℂ))
            (-2 * (Real.pi : ℂ) * sqA1 t m) y := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-2 * (Real.pi : ℂ) * sqA1 t m)
        simpa [mul_comm] using hlin.cexp
      have h2 : HasDerivAt (fun z : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (z : ℂ)))
          ((-2 * (Real.pi : ℂ) * sqA2 t m) *
            Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (y : ℂ))) y := by
        have hlin : HasDerivAt (fun z : ℝ ↦ (-2 * (Real.pi : ℂ) * sqA2 t m) * (z : ℂ))
            (-2 * (Real.pi : ℂ) * sqA2 t m) y := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-2 * (Real.pi : ℂ) * sqA2 t m)
        simpa [mul_comm] using hlin.cexp
      have hcomb := (((h1.const_mul ((-2 * (Real.pi : ℂ) * sqA1 t m) ^ k)).div_const (sqA1 t m)).sub
        ((h2.const_mul ((-2 * (Real.pi : ℂ) * sqA2 t m) ^ k)).div_const (sqA2 t m))).const_mul
        (1 / (2 * I * (m.val : ℂ)))
      convert hcomb using 1
      dsimp only [term]; rw [pow_succ, pow_succ]; ring
    have hc : 0 < 2 * Real.pi * Real.sqrt (Real.pi / t) * a := by positivity
    have hu_sum := (summable_pow_mul_exp_neg_sqrt hc (k + 1)).mul_left
      ((2 * Real.pi * Real.sqrt 2 * Real.sqrt (Real.pi / t)) ^ (k + 1) *
        (Real.sqrt (t / Real.pi) / Real.sqrt 2))
    have hsum_k : Summable (fun m : ℕ+ ↦ term k m x) :=
      Summable.of_norm_bounded ((summable_pow_mul_exp_neg_sqrt hc k).mul_left _)
        (fun m ↦ hterm_bound k a ha m x (by dsimp [a]; linarith))
    exact hasDerivAt_tsum_of_isPreconnected hu_sum isOpen_Ioo isPreconnected_Ioo
      (fun m y _ ↦ hd_each m y) (fun m y hy ↦ hterm_bound (k + 1) a ha m y hy.1.le)
      hmem hsum_k hmem
  have hiter : ∀ k : ℕ, ∀ x > 0, iteratedDeriv k (𝓕 (sqRem t)) x = ∑' m : ℕ+, term k m x := by
    intro k
    induction k with
    | zero =>
      intro x hx; rw [iteratedDeriv_zero, fourier_sqRem ht x]
      apply tsum_congr; intro m; simp [term, abs_of_pos hx]
    | succ k ih =>
      intro x hx; rw [iteratedDeriv_succ]
      have hnear : iteratedDeriv k (𝓕 (sqRem t)) =ᶠ[𝓝 x] fun y ↦ ∑' m : ℕ+, term k m y :=
        (lt_mem_nhds hx).mono fun y hy ↦ ih y hy
      rw [hnear.deriv_eq, (hdiff_step k x hx).deriv]
  rw [hiter 2 ξ hξ, ← tsum_mul_left]
  apply tsum_congr; intro m; dsimp only [term]
  field_simp [sqA1_ne_zero ht m, sqA2_ne_zero ht m]

private lemma iteratedDeriv_two_exp_neg_two_pi {ξ : ℝ} (hξ : 0 < ξ) :
    iteratedDeriv 2 (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) ξ =
      ((2 * Real.pi : ℂ) ^ 2) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ)) := by
  have heq : (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) =ᶠ[𝓝 ξ]
      fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
    (lt_mem_nhds hξ).mono fun y hy ↦ by dsimp only; rw [abs_of_pos hy]
  rw [heq.iteratedDeriv_eq 2]
  have hgen (k : ℕ) (x : ℝ) :
      iteratedDeriv k (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) x =
        (-2 * (Real.pi : ℂ)) ^ k * Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ)) := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun y : ℝ ↦
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) =
        fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) ^ k * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) from funext ih]
      have hd : HasDerivAt (fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) ^ k *
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)))
          ((-2 * (Real.pi : ℂ)) ^ (k + 1) * Complex.exp (-2 * (Real.pi : ℂ) * (x : ℂ))) x := by
        have h1 : HasDerivAt (fun y : ℝ ↦ (-2 * (Real.pi : ℂ)) * (y : ℂ)) (-2 * (Real.pi : ℂ)) x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-2 * (Real.pi : ℂ))
        convert (h1.cexp).const_mul ((-2 * (Real.pi : ℂ)) ^ k) using 1
        rw [pow_succ]; ring
      exact hd.deriv
  rw [hgen 2 ξ]; ring

/-- **Exact Explicit Fourier Transform of `sqDivFunc t` on `ξ > 0`** (ZERO contour integrals!). -/
private theorem fourier_sqDivFunc_pos {t : ℝ} (ht : 0 < t) {ξ : ℝ} (hξ : 0 < ξ) :
    𝓕 (sqDivFunc t) ξ =
      -∑' m : ℕ+, (1 / (2 * I * (m.val : ℂ))) *
        (sqA1 t m * Complex.exp (-2 * (Real.pi : ℂ) * sqA1 t m * (ξ : ℂ)) -
         sqA2 t m * Complex.exp (-2 * (Real.pi : ℂ) * sqA2 t m * (ξ : ℂ))) := by
  let Q (x : ℝ) : ℂ := (1 / 2 : ℂ) * ((x : ℂ) ^ 2 + 1)⁻¹
  let ψ (x : ℝ) : ℂ := sqRem t x - Q x
  have h1_int : Integrable (fun x : ℝ ↦ (((x : ℂ) ^ 2 + 1)⁻¹ : ℂ)) := by
    simpa using integrable_inv_sq_add (a := 1) (by simp)
  have hQ_int : Integrable Q := h1_int.const_mul (1 / 2 : ℂ)
  have hψ_int : Integrable ψ := (sqRem_integrable ht).sub hQ_int
  have hψ_x2 : ∀ x : ℝ, ((x : ℂ) ^ 2) * ψ x =
      sqDivFunc t x + (1 / 2 : ℂ) * ((x : ℂ) ^ 2 + 1)⁻¹ := by
    intro x; dsimp only [ψ, Q]
    rw [mul_sub, sqDivFunc_eq_x2_sqRem ht x]
    have hne : (x : ℂ) ^ 2 + 1 ≠ 0 := by simpa using lorentz_sq_add_ne_zero (a := 1) (by simp) x
    field_simp [hne]; ring
  have hψ2_int : Integrable (fun x : ℝ ↦ (x ^ 2 : ℝ) • ψ x) := by
    have hfun : (fun x : ℝ ↦ (x ^ 2 : ℝ) • ψ x) = fun x : ℝ ↦
        sqDivFunc t x + (1 / 2 : ℂ) * ((x : ℂ) ^ 2 + 1)⁻¹ := by
      funext x; rw [Complex.real_smul, Complex.ofReal_pow, hψ_x2 x]
    rw [hfun]; exact (sqDivFunc_integrable ht).add (h1_int.const_mul _)
  have hψ_moments : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (fun x : ℝ ↦ x ^ n • ψ x) := by
    intro n hn
    have hn2 : n ≤ 2 := by exact_mod_cast hn
    refine (hψ_int.norm.add hψ2_int.norm).mono' ?_ (Eventually.of_forall fun x ↦ ?_)
    · exact ((continuous_pow n).aestronglyMeasurable.smul hψ_int.aestronglyMeasurable)
    · simp only [Pi.add_apply, norm_smul, Real.norm_eq_abs, abs_pow]
      have hpow : |x| ^ n ≤ 1 + |x| ^ 2 := by
        by_cases hx1 : |x| ≤ 1
        · linarith [pow_le_one₀ (n := n) (abs_nonneg x) hx1, pow_nonneg (abs_nonneg x) 2]
        · push Not at hx1; linarith [pow_le_pow_right₀ hx1.le hn2]
      calc |x| ^ n * ‖ψ x‖ ≤ (1 + |x| ^ 2) * ‖ψ x‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ = ‖ψ x‖ + |x| ^ 2 * ‖ψ x‖ := by ring
  have hFψ_d2 := congrFun (Real.iteratedDeriv_fourier hψ_moments le_rfl) ξ
  have hFψ_val : 𝓕 (fun x : ℝ ↦ (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 • ψ x) ξ =
      -((2 * Real.pi : ℂ) ^ 2) *
        (𝓕 (sqDivFunc t) ξ + ((1 / 2 : ℂ) * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) := by
    have hfun : (fun x : ℝ ↦ (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 • ψ x) =
        fun x : ℝ ↦ -((2 * Real.pi : ℂ) ^ 2) *
          (sqDivFunc t x + (1 / 2 : ℂ) * ((x : ℂ) ^ 2 + 1)⁻¹) := by
      funext x; rw [smul_eq_mul, ← hψ_x2 x]
      calc (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 * ψ x
          = ((2 * (Real.pi : ℂ)) ^ 2 * I ^ 2) * ((x : ℂ) ^ 2 * ψ x) := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    rw [hfun, fourier_const_mul, fourier_add_eq (sqDivFunc_integrable ht) (h1_int.const_mul _),
        fourier_const_mul]
    have hL1 := fourier_lorentzian (a := 1) (by simp) ξ
    simp only [one_pow, div_one, mul_one, abs_of_pos hξ] at hL1
    rw [hL1]; ring
  have hFQ : ∀ y : ℝ, 𝓕 Q y =
      ((1 / 2 : ℂ) * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ)) := by
    intro y; change 𝓕 (fun x : ℝ ↦ (1 / 2 : ℂ) * ((x : ℂ) ^ 2 + 1)⁻¹) y = _
    rw [fourier_const_mul]
    have hL1 := fourier_lorentzian (a := 1) (by simp) y
    simp only [one_pow, div_one, mul_one] at hL1
    rw [hL1]; ring
  have hexp_cd : ContDiff ℝ 2 (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hFQ_d2 : iteratedDeriv 2 (𝓕 Q) ξ =
      ((2 * Real.pi : ℂ) ^ 2) *
        (((1 / 2 : ℂ) * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) := by
    have hfun : 𝓕 Q =ᶠ[𝓝 ξ] fun y : ℝ ↦
        ((1 / 2 : ℂ) * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
      (lt_mem_nhds hξ).mono fun y hy ↦ by rw [hFQ y, abs_of_pos hy]
    rw [hfun.iteratedDeriv_eq 2, iteratedDeriv_const_mul_field]
    have he1 : (fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * ((|y| : ℝ) : ℂ))) =ᶠ[𝓝 ξ]
        fun y : ℝ ↦ Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
      (lt_mem_nhds hξ).mono fun y hy ↦ by dsimp only; rw [abs_of_pos hy]
    rw [← he1.iteratedDeriv_eq 2, iteratedDeriv_two_exp_neg_two_pi hξ]; ring
  have hsplit_F : 𝓕 (sqRem t) = fun y ↦ 𝓕 ψ y + 𝓕 Q y := by
    ext y; have hsq : sqRem t = fun x ↦ ψ x + Q x := by funext x; dsimp [ψ]; ring
    rw [hsq, fourier_add_eq hψ_int hQ_int]
  have hψ_cd : ContDiffAt ℝ 2 (𝓕 ψ) ξ := by
    have hA : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (fun v : ℝ ↦ ‖v‖ ^ n * ‖ψ v‖) := by
      intro n hn; convert (hψ_moments n hn).norm with x; simp
    exact (Real.contDiff_fourier hA).contDiffAt
  have hQ_cd : ContDiffAt ℝ 2 (𝓕 Q) ξ := by
    have hfun : 𝓕 Q =ᶠ[𝓝 ξ] fun y : ℝ ↦
        ((1 / 2 : ℂ) * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ)) :=
      (lt_mem_nhds hξ).mono fun y hy ↦ by rw [hFQ y, abs_of_pos hy]
    exact (contDiff_const.mul hexp_cd).contDiffAt.congr_of_eventuallyEq hfun
  have hsum_d2 : iteratedDeriv 2 (𝓕 (sqRem t)) ξ =
      iteratedDeriv 2 (𝓕 ψ) ξ + iteratedDeriv 2 (𝓕 Q) ξ := by
    rw [hsplit_F]; exact iteratedDeriv_fun_add hψ_cd hQ_cd
  rw [iteratedDeriv_two_fourier_sqRem ht hξ, hFψ_d2, hFψ_val, hFQ_d2] at hsum_d2
  have hcancel :
      -((2 * Real.pi : ℂ) ^ 2) *
        (𝓕 (sqDivFunc t) ξ + ((1 / 2 : ℂ) * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) +
      ((2 * Real.pi : ℂ) ^ 2) *
        (((1 / 2 : ℂ) * (Real.pi : ℂ)) * Complex.exp (-2 * (Real.pi : ℂ) * (ξ : ℂ))) =
      -((2 * Real.pi : ℂ) ^ 2) * 𝓕 (sqDivFunc t) ξ := by ring
  rw [hcancel] at hsum_d2
  have h2pi2 : (2 * (Real.pi : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact mul_left_cancel₀ h2pi2 (by linear_combination hsum_d2)

private lemma fourier_sqDivFunc_at_X {X : ℝ} (hX : 0 < X) {ξ : ℝ} (hξ : 0 < ξ) :
    𝓕 (sqDivFunc (X ^ 2)⁻¹) ξ =
      (((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * (X : ℂ)) *
        ∑' m : ℕ+, (((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)⁻¹) *
          ((1 - I) * Complex.exp (-sqRay0 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) +
           (1 + I) * Complex.exp (-sqRay1 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)))) := by
  have ht : 0 < (X ^ 2)⁻¹ := by positivity
  rw [fourier_sqDivFunc_pos ht hξ, ← tsum_neg, ← tsum_mul_left]
  apply tsum_congr; intro m
  have hm : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
  have hα : sqAlpha (X ^ 2)⁻¹ m = Real.sqrt Real.pi * Real.sqrt (m.val : ℝ) * X := by
    unfold sqAlpha
    rw [div_inv_eq_mul, Real.sqrt_mul (by positivity), Real.sqrt_mul Real.pi_pos.le,
        Real.sqrt_sq hX.le]
  have hpi32 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add Real.pi_pos, Real.rpow_one]
  have hexp1 : -2 * (Real.pi : ℂ) * sqA1 (X ^ 2)⁻¹ m * (ξ : ℂ) =
      -sqRay1 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) := by
    simp only [sqA1, sqRay1, hα, hpi32]; push_cast; ring
  have hexp2 : -2 * (Real.pi : ℂ) * sqA2 (X ^ 2)⁻¹ m * (ξ : ℂ) =
      -sqRay0 * (((ξ * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) := by
    simp only [sqA2, sqRay0, hα, hpi32]; push_cast; ring
  rw [hexp1, hexp2]
  have hsq_m : ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) ^ 2 = (m.val : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hm.le, Complex.ofReal_natCast]
  have hsm0 : ((Real.sqrt (m.val : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hm).ne'
  have hm0 : (m.val : ℂ) ≠ 0 := by exact_mod_cast m.property.ne'
  simp only [sqA1, sqA2, hα]; push_cast
  field_simp [hm0, hsm0, Complex.I_ne_zero]
  rw [← hsq_m]
  ring_nf; simp [Complex.I_sq]; ring

private lemma fourier_sqDivFunc_zero_at_X {X : ℝ} (hX : 0 < X) :
    𝓕 (sqDivFunc (X ^ 2)⁻¹) 0 = (X : ℂ) * sqDivConst := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left (g := fun x : ℝ ↦ sqDivFunc (X ^ 2)⁻¹ x) X
  simp only [Complex.real_smul, abs_inv, abs_of_pos hX] at hsub
  have heq : (fun u : ℝ ↦ sqDivFunc (X ^ 2)⁻¹ (X * u)) =
      fun u : ℝ ↦ if u = 0 then (-1 / 2 : ℂ)
        else (((1 / (Real.exp (u ^ 2) - 1) - 1 / u ^ 2 : ℝ) : ℂ)) := by
    funext u
    by_cases hu : u = 0
    · subst hu; simp [sqDivFunc]
    · have hXu : X * u ≠ 0 := mul_ne_zero hX.ne' hu
      simp only [sqDivFunc, hXu, hu, ↓reduceIte]
      have harg : (X ^ 2)⁻¹ * (X * u) ^ 2 = u ^ 2 := by field_simp [hX.ne']
      rw [harg]
  have h2 : ∫ u : ℝ, sqDivFunc (X ^ 2)⁻¹ (X * u) = sqDivConst := by rw [heq]; rfl
  rw [h2] at hsub
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  calc ∫ x : ℝ, sqDivFunc (X ^ 2)⁻¹ x
      = (X : ℂ) * (((X : ℂ)⁻¹) * ∫ x : ℝ, sqDivFunc (X ^ 2)⁻¹ x) := by field_simp [hX0]
    _ = (X : ℂ) * sqDivConst := by rw [← Complex.ofReal_inv, ← hsub]

private lemma fourier_sqDivFunc_even (t : ℝ) (ξ : ℝ) : 𝓕 (sqDivFunc t) (-ξ) = 𝓕 (sqDivFunc t) ξ := by
  rw [← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg]
  have hfun : (fun x : ℝ ↦ sqDivFunc t (-x)) = sqDivFunc t := by
    funext x
    by_cases hx : x = 0
    · subst hx; simp [sqDivFunc]
    · simp [sqDivFunc, hx, neg_ne_zero.mpr hx]
  rw [hfun]

private lemma summable_fourier_sqDivFunc_int {X : ℝ} (hX : 0 < X) :
    Summable (fun k : ℤ ↦ 𝓕 (sqDivFunc (X ^ 2)⁻¹) (k : ℝ)) := by
  have hpos_sum : Summable (fun k : ℕ+ ↦ ‖𝓕 (sqDivFunc (X ^ 2)⁻¹) (k.val : ℝ)‖) := by
    let c₀ : ℝ := Real.pi ^ (3 / 2 : ℝ) * X
    have hc₀ : 0 < c₀ := by positivity
    let S₀ : ℝ := ∑' m : ℕ+, (m.val : ℝ) ^ 0 * Real.exp (-c₀ * Real.sqrt (m.val : ℝ))
    have hS₀_sum : Summable (fun m : ℕ+ ↦ (m.val : ℝ) ^ 0 * Real.exp (-c₀ * Real.sqrt (m.val : ℝ))) :=
      summable_pow_mul_exp_neg_sqrt hc₀ 0
    let C : ℝ := (Real.sqrt Real.pi / 2 * X) * (‖(1 : ℂ) - I‖ + ‖(1 : ℂ) + I‖) * S₀
    have hdom : Summable (fun k : ℕ+ ↦ C * Real.exp (-c₀ * (k.val : ℝ))) := by
      have h1 : Summable (fun n : ℕ ↦ Real.exp (-c₀ * (n : ℝ))) := by
        simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 hc₀
      exact (h1.subtype (fun n ↦ 0 < n)).mul_left C
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hdom
    have hk : (0 : ℝ) < (k.val : ℝ) := by exact_mod_cast k.property
    have hk1 : (1 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.property
    rw [fourier_sqDivFunc_at_X hX hk, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos hX]
    have hle_m (m : ℕ+) :
        ‖(((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)⁻¹) *
          ((1 - I) * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           (1 + I) * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)))‖ ≤
        ((‖(1 : ℂ) - I‖ + ‖(1 : ℂ) + I‖) * Real.exp (-c₀ * (k.val : ℝ))) *
          ((m.val : ℝ) ^ 0 * Real.exp (-c₀ * Real.sqrt (m.val : ℝ))) := by
      have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.property
      have hm_sqrt : (1 : ℝ) ≤ Real.sqrt (m.val : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
      have hre0 : (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
          -(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ)) := by
        simp [sqRay0, c₀, Complex.mul_re]; ring
      have hre1 : (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
          -(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ)) := by
        simp [sqRay1, c₀, Complex.mul_re]; ring
      have hexp_split : Real.exp (-(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ))) ≤
          Real.exp (-c₀ * (k.val : ℝ)) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hm_sqrt hc₀.le, mul_le_mul_of_nonneg_left hk1 hc₀.le]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hinv_le : (Real.sqrt (m.val : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm_sqrt
      have htri : ‖(1 - I) * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
          (1 + I) * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))‖ ≤
          (‖(1 : ℂ) - I‖ + ‖(1 : ℂ) + I‖) * Real.exp (-(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ))) := by
        calc _ ≤ ‖(1 - I) * Complex.exp _‖ + ‖(1 + I) * Complex.exp _‖ := norm_add_le _ _
          _ = (‖(1 : ℂ) - I‖ + ‖(1 : ℂ) + I‖) * Real.exp (-(2 * c₀ * (k.val : ℝ) * Real.sqrt (m.val : ℝ))) := by
              rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, hre0, hre1]; ring
      calc (Real.sqrt (m.val : ℝ))⁻¹ * _
          ≤ 1 * ((‖(1 : ℂ) - I‖ + ‖(1 : ℂ) + I‖) *
              (Real.exp (-c₀ * (k.val : ℝ)) * Real.exp (-c₀ * Real.sqrt (m.val : ℝ)))) :=
            mul_le_mul hinv_le (htri.trans (mul_le_mul_of_nonneg_left hexp_split (by positivity)))
              (norm_nonneg _) zero_le_one
        _ = _ := by simp [pow_zero]; ring
    have hinner : Summable (fun m : ℕ+ ↦
        ‖(((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)⁻¹) *
          ((1 - I) * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           (1 + I) * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)))‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle_m (hS₀_sum.mul_left _)
    have hts := (norm_tsum_le_tsum_norm hinner).trans (hinner.tsum_le_tsum hle_m (hS₀_sum.mul_left _))
    rw [tsum_mul_left] at hts
    calc (Real.sqrt Real.pi / 2 * X) * _
        ≤ (Real.sqrt Real.pi / 2 * X) *
            (((‖(1 : ℂ) - I‖ + ‖(1 : ℂ) + I‖) * Real.exp (-c₀ * (k.val : ℝ))) * S₀) :=
          mul_le_mul_of_nonneg_left hts (by positivity)
      _ = C * Real.exp (-c₀ * (k.val : ℝ)) := by dsimp [C]; ring
  have hnat : Summable (fun n : ℕ ↦ 𝓕 (sqDivFunc (X ^ 2)⁻¹) (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    exact (Equiv.pnatEquivNat.symm.summable_iff.mpr hpos_sum.of_norm).congr fun n ↦ by
      simp [Equiv.pnatEquivNat]
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hnat, ?_⟩
  refine hnat.congr fun n ↦ by rw [Int.cast_neg, Int.cast_natCast, fourier_sqDivFunc_even]

/-- **100% Unconditional Exact Analytic Identity for the Square-Divisor Series `L_{2, 0}(q)`**:
For EVERY `X > 0`:
```
∑'_{n : ℕ+} 1 / (exp(n² / X²) - 1)
  = (π² / 6) X² + (1/2) sqDivConst · X + 1/4
    + (√π / 2) X ∑'_{k : ℕ+} ∑'_{m : ℕ+} (1 / √m) *
        ((1 - I) exp(-sqRay0 * k * √m * X) + (1 + I) exp(-sqRay1 * k * √m * X))
```
(ZERO contour integrals, ZERO Mellin transforms, ZERO Bessel functions!). -/
theorem squareDivisor_analytic_identity {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ+, (((1 / (Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) - 1) : ℝ) : ℂ))) =
      (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (X : ℂ) ^ 2) +
      ((1 / 2 : ℂ) * sqDivConst * (X : ℂ)) + (1 / 4 : ℂ) +
      (((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * (X : ℂ)) *
        ∑' k : ℕ+, ∑' m : ℕ+, (((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)⁻¹) *
          ((1 - I) * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           (1 + I) * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) := by
  have ht : 0 < (X ^ 2)⁻¹ := by positivity
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (sqDivFunc_continuous ht) one_lt_two (sqDivFunc_isBigO ht) (summable_fourier_sqDivFunc_int hX) 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hpois
  have hdiv_even : ∀ x : ℝ, sqDivFunc (X ^ 2)⁻¹ (-x) = sqDivFunc (X ^ 2)⁻¹ x := fun x ↦ by
    by_cases hx : x = 0
    · subst hx; simp [sqDivFunc]
    · simp [sqDivFunc, hx, neg_ne_zero.mpr hx]
  have hdiv_sum_int : Summable (fun n : ℤ ↦ sqDivFunc (X ^ 2)⁻¹ (n : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((sqDivFunc_isBigO ht).comp_tendsto Int.tendsto_coe_cofinite)
  rw [tsum_int_even hdiv_even hdiv_sum_int,
      tsum_int_even (fourier_sqDivFunc_even (X ^ 2)⁻¹) (summable_fourier_sqDivFunc_int hX),
      fourier_sqDivFunc_zero_at_X hX] at hpois
  have h0 : sqDivFunc (X ^ 2)⁻¹ 0 = (-1 / 2 : ℂ) := by simp [sqDivFunc]
  rw [h0] at hpois
  -- Split `∑'_{n : ℕ+} (1/(exp(n²/X²) - 1) - X²/n²)` into the two convergent sums!
  have hsum_inv_sq_real : HasSum (fun n : ℕ+ ↦ (1 : ℝ) / (n.val : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    have h0' := hasSum_zeta_two
    rw [← hasSum_nat_add_iff' 1] at h0'
    simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, sub_zero] at h0'
    exact (Equiv.pnatEquivNat.symm.hasSum_iff.mp (h0'.congr_fun fun n ↦ by simp [Equiv.pnatEquivNat]))
  have hsum_zeta : Summable (fun n : ℕ+ ↦ ((((X ^ 2) / (n.val : ℝ) ^ 2 : ℝ) : ℂ))) := by
    have h1 : Summable (fun n : ℕ+ ↦ (X ^ 2) * ((1 : ℝ) / (n.val : ℝ) ^ 2)) :=
      hsum_inv_sq_real.summable.mul_left (X ^ 2)
    exact Complex.summable_ofReal.mpr (h1.congr fun n ↦ by ring)
  have hsum_pnat_div : Summable (fun n : ℕ+ ↦ sqDivFunc (X ^ 2)⁻¹ (n.val : ℝ)) := by
    have hnat : Summable (fun n : ℕ ↦ sqDivFunc (X ^ 2)⁻¹ (n : ℝ)) :=
      hdiv_sum_int.comp_injective Int.ofNat_injective
    exact hnat.comp_injective PNat.coe_injective
  have hterm_add (n : ℕ+) :
      sqDivFunc (X ^ 2)⁻¹ (n.val : ℝ) + (((X ^ 2 / (n.val : ℝ) ^ 2 : ℝ) : ℂ)) =
        (((1 / (Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) - 1) : ℝ) : ℂ)) := by
    have hn0 : (n.val : ℝ) ≠ 0 := by exact_mod_cast n.property.ne'
    simp only [sqDivFunc, hn0, ↓reduceIte]
    rw [← Complex.ofReal_add]
    congr 1
    have h1 : (X ^ 2)⁻¹ * (n.val : ℝ) ^ 2 = (n.val : ℝ) ^ 2 / X ^ 2 := by ring
    have h2 : 1 / ((X ^ 2)⁻¹ * (n.val : ℝ) ^ 2) = X ^ 2 / (n.val : ℝ) ^ 2 := by
      field_simp [hX.ne', hn0]
    rw [h2, h1]; ring
  have htsum_split :
      (∑' n : ℕ+, sqDivFunc (X ^ 2)⁻¹ (n.val : ℝ)) =
        (∑' n : ℕ+, (((1 / (Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) - 1) : ℝ) : ℂ))) -
        (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (X : ℂ) ^ 2) := by
    have hadd := hsum_pnat_div.tsum_add hsum_zeta
    simp_rw [hterm_add] at hadd
    have hzeta_val : (∑' n : ℕ+, (((X ^ 2 / (n.val : ℝ) ^ 2 : ℝ) : ℂ))) =
        (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (X : ℂ) ^ 2) := by
      have h1 : (fun n : ℕ+ ↦ (((X ^ 2 / (n.val : ℝ) ^ 2 : ℝ) : ℂ))) =
          fun n : ℕ+ ↦ ((X : ℂ) ^ 2) * (((1 / (n.val : ℝ) ^ 2 : ℝ) : ℂ)) := by
        funext n; push_cast; ring
      rw [h1, tsum_mul_left]
      have h2 : (∑' n : ℕ+, (((1 / (n.val : ℝ) ^ 2 : ℝ) : ℂ))) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_tsum, hsum_inv_sq_real.tsum_eq]
      rw [h2]; ring
    rw [hzeta_val] at hadd
    linear_combination -hadd
  have hrhs_waves : (∑' k : ℕ+, 𝓕 (sqDivFunc (X ^ 2)⁻¹) (k.val : ℝ)) =
      (((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * (X : ℂ)) *
        ∑' k : ℕ+, ∑' m : ℕ+, (((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)⁻¹) *
          ((1 - I) * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
           (1 + I) * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro k
    exact fourier_sqDivFunc_at_X hX (by exact_mod_cast k.property)
  rw [htsum_split, hrhs_waves] at hpois
  linear_combination (1 / 2 : ℂ) * hpois

private lemma psValue_squareDivisor_eq {X : ℝ} (hX : 0 < X) :
    psValue squareDivisorSeries (qRayD 3 X) =
      ∑' n : ℕ+, (((1 / (Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) - 1) : ℝ) : ℂ)) := by
  let t : ℝ := 1 / X ^ 2
  have ht : 0 < t := by positivity
  let term (mn : ℕ+ × ℕ+) : ℂ := (qRayD 3 X) ^ (mn.1.val * mn.2.val ^ 2)
  have hq_norm : ‖qRayD 3 X‖ = Real.exp (-t) := by
    unfold qRayD; dsimp only [t]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsum_prod : Summable (fun mn : ℕ+ × ℕ+ ↦ ‖term mn‖) := by
    have hsum_norm : Summable (fun mn : ℕ+ × ℕ+ ↦ Real.exp (-t * (mn.1.val * mn.2.val ^ 2))) := by
      rw [← (Equiv.sigmaEquivProd ℕ+ ℕ+).summable_iff]
      refine (summable_sigma_of_nonneg fun _ ↦ Real.exp_nonneg _).mpr ⟨fun m ↦ ?_, ?_⟩
      · have hm : 0 < t * (m.val : ℝ) := mul_pos ht (by exact_mod_cast m.pos)
        have h0 := (Real.summable_pow_mul_exp_neg_nat_mul 0 hm).comp_injective PNat.coe_injective
        refine Summable.of_nonneg_of_le (fun _ ↦ Real.exp_nonneg _) (fun n ↦ ?_) h0
        simp only [Function.comp_def, Equiv.sigmaEquivProd_apply, pow_zero, one_mul]
        apply Real.exp_le_exp.mpr
        have hn1 : (n.val : ℝ) ≤ (n.val : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ (n.val : ℝ) := by exact_mod_cast n.pos
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hn1 hm.le]
      · have hsn : Summable (fun n : ℕ+ ↦ Real.exp (-(t / 2) * (n.val : ℝ))) := by
          simpa only [Function.comp_def, pow_zero, one_mul] using
            (Real.summable_pow_mul_exp_neg_nat_mul 0 (half_pos ht)).comp_injective PNat.coe_injective
        have hdom := ((Real.summable_pow_mul_exp_neg_nat_mul 0 (half_pos ht)).comp_injective PNat.coe_injective).mul_left
          (∑' n : ℕ+, Real.exp (-(t / 2) * (n.val : ℝ)))
        refine Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ Real.exp_nonneg _) (fun m ↦ ?_) hdom
        have hm : 0 < t * (m.val : ℝ) := mul_pos ht (by exact_mod_cast m.pos)
        have hsm : Summable (fun n : ℕ+ ↦ Real.exp (-t * (m.val * n.val ^ 2))) := by
          refine Summable.of_nonneg_of_le (fun _ ↦ Real.exp_nonneg _) (fun n ↦ ?_)
            ((Real.summable_pow_mul_exp_neg_nat_mul 0 hm).comp_injective PNat.coe_injective)
          simp only [Function.comp_def, pow_zero, one_mul]
          apply Real.exp_le_exp.mpr
          have hn1 : (n.val : ℝ) ≤ (n.val : ℝ) ^ 2 := by
            have : (1 : ℝ) ≤ (n.val : ℝ) := by exact_mod_cast n.pos
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hn1 hm.le]
        have hts := hsm.tsum_le_tsum (fun n ↦ by
          have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.pos
          have hn1 : (1 : ℝ) ≤ (n.val : ℝ) := by exact_mod_cast n.pos
          have hnn : (n.val : ℝ) ≤ (n.val : ℝ) ^ 2 := by nlinarith
          have hadd : (n.val : ℝ) + (m.val : ℝ) ≤ 2 * ((m.val : ℝ) * (n.val : ℝ) ^ 2) := by nlinarith
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith)
          (hsn.mul_right (Real.exp (-(t / 2) * (m.val : ℝ))))
        rw [tsum_mul_right] at hts
        simpa only [Function.comp_def, Equiv.sigmaEquivProd_apply, pow_zero, one_mul] using hts
    refine hsum_norm.congr fun mn ↦ ?_
    simp only [term, norm_pow, hq_norm, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have h_eq1 : psValue squareDivisorSeries (qRayD 3 X) = ∑' mn : ℕ+ × ℕ+, term mn := by
    let g (mn : ℕ+ × ℕ+) : ℕ := mn.1.val * mn.2.val ^ 2
    rw [(hsum_prod.of_norm.hasSum.tsum_fiberwise g).tsum_eq.symm]
    unfold psValue
    apply tsum_congr; intro N
    by_cases hN0 : N = 0
    · subst hN0
      have : IsEmpty (g ⁻¹' {0}) := ⟨fun mn ↦ mul_ne_zero mn.val.1.pos.ne'
        (pow_ne_zero 2 mn.val.2.pos.ne') mn.property⟩
      simp [psTerm, squareDivisorSeries]
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
        (fun _ ↦ (qRayD 3 X) ^ N)
        (fun mn ↦ by simp only [term, show mn.val.1.val * mn.val.2.val ^ 2 = N from mn.property])]
      simp [psTerm, squareDivisorSeries, squareDivCount, hN0, S]
  have hsum_swap : Summable (fun nm : ℕ+ × ℕ+ ↦ term (nm.2, nm.1)) :=
    hsum_prod.of_norm.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
  have h_eq2 : (∑' mn : ℕ+ × ℕ+, term mn) = ∑' n : ℕ+, ∑' m : ℕ+, term (m, n) := by
    rw [← (Equiv.prodComm ℕ+ ℕ+).tsum_eq term]
    exact hsum_swap.tsum_prod' fun n ↦ hsum_prod.of_norm.comp_injective fun m₁ m₂ h ↦ by injection h
  rw [h_eq1, h_eq2]
  apply tsum_congr; intro n
  have hq_n : ‖(qRayD 3 X) ^ (n.val ^ 2)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (qRayD_disk hX) (pow_ne_zero 2 n.pos.ne')
  have hterm_n : (∑' m : ℕ+, term (m, n)) = ∑' m : ℕ+, ((qRayD 3 X) ^ (n.val ^ 2)) ^ m.val := by
    apply tsum_congr; intro m; simp [term, ← pow_mul, mul_comm]
  rw [hterm_n, tsum_pnat_eq_tsum_succ (f := fun m : ℕ ↦ ((qRayD 3 X) ^ (n.val ^ 2)) ^ m)]
  simp_rw [pow_succ' ((qRayD 3 X) ^ (n.val ^ 2))]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq_n]
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

/-- Shell-weighted wave multiplicity for `L_{2, 0}`: `(∑_{k² ∣ N} k) / √N`. -/
def sqDivWaveMult (N : ℕ) : ℝ :=
  (∑ k ∈ (Finset.Icc 1 N).filter (fun k ↦ k ^ 2 ∣ N), (k : ℝ)) / Real.sqrt (N : ℝ)

/-- **100% Unconditional `SqRayProfile` for the Square-Divisor Series `L_{2, 0}(q)`**! -/
def squareDivisorProfile : SqRayProfile squareDivisorSeries where
  coeffBoundPow := 1
  coeffBoundC := 1
  coeffBound_nonneg := zero_le_one
  coeffBound n := by
    rw [squareDivisorSeries, PowerSeries.coeff_mk]
    split_ifs with h0
    · simp; positivity
    · rw [Complex.norm_natCast, one_mul, pow_one]
      have hle : squareDivCount n ≤ n := by
        unfold squareDivCount
        calc ((Finset.Icc 1 n).filter (fun k ↦ k ^ 2 ∣ n)).card
            ≤ (Finset.Icc 1 n).card := Finset.card_le_card (Finset.filter_subset ..)
          _ = n := by simp
      have hcast : (squareDivCount n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
      linarith
  scalePow := 1
  polarHigh := 2
  polarPoly := Polynomial.C (((Real.pi ^ 2 / 6 : ℝ) : ℂ)) +
    Polynomial.C ((1 / 2 : ℂ) * sqDivConst) * Polynomial.X +
    Polynomial.C (1 / 4 : ℂ) * Polynomial.X ^ 2
  waveAmp := fun ℓ N ↦
    ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * ((sqDivWaveMult N.val : ℝ) : ℂ) *
      (if ℓ.val = 0 then (1 - I) else (1 + I))
  waveBoundPow := 2
  waveBoundC := Real.sqrt Real.pi / 2 * Real.sqrt 2
  waveBound_nonneg := by positivity
  waveBound ℓ N := by
    have hN1 : (1 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast N.pos
    have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt (N.val : ℝ) := by simpa using Real.sqrt_le_sqrt hN1
    have hmult_nn : 0 ≤ sqDivWaveMult N.val :=
      div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    have hmult_le : sqDivWaveMult N.val ≤ (N.val : ℝ) ^ 2 := by
      unfold sqDivWaveMult
      calc (∑ k ∈ (Finset.Icc 1 N.val).filter (fun k ↦ k ^ 2 ∣ N.val), (k : ℝ)) / Real.sqrt (N.val : ℝ)
          ≤ (∑ k ∈ (Finset.Icc 1 N.val).filter (fun k ↦ k ^ 2 ∣ N.val), (k : ℝ)) / 1 :=
            div_le_div_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) zero_lt_one hsqrt_ge
        _ = ∑ k ∈ (Finset.Icc 1 N.val).filter (fun k ↦ k ^ 2 ∣ N.val), (k : ℝ) := div_one _
        _ ≤ ∑ _k ∈ Finset.Icc 1 N.val, (N.val : ℝ) := by
            refine (Finset.sum_le_sum fun k hk ↦ ?_).trans
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) fun _ _ _ ↦ Nat.cast_nonneg _)
            exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
        _ = (N.val : ℝ) ^ 2 := by simp [sq]
    have hnorm_pm : ‖if ℓ.val = 0 then (1 : ℂ) - I else 1 + I‖ = Real.sqrt 2 := by
      split_ifs <;> (rw [Complex.norm_def, Complex.normSq_apply]; norm_num)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_nonneg hmult_nn, hnorm_pm]
    calc (Real.sqrt Real.pi / 2) * sqDivWaveMult N.val * Real.sqrt 2
        ≤ (Real.sqrt Real.pi / 2) * (N.val : ℝ) ^ 2 * Real.sqrt 2 := by gcongr
      _ = (Real.sqrt Real.pi / 2 * Real.sqrt 2) * (N.val : ℝ) ^ 2 := by ring
  prime_amp_ne_zero p hp := by
    have hfilt : (Finset.Icc 1 p.val).filter (fun k ↦ k ^ 2 ∣ p.val) = {1} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hdvd⟩; exact Nat.isUnit_iff.mp (rfree_of_prime (by decide) hp k hdvd)
      · rintro rfl; exact ⟨⟨le_rfl, hp.one_lt.le⟩, by simp⟩
    have hmult_pos : 0 < sqDivWaveMult p.val := by
      rw [sqDivWaveMult, hfilt, Finset.sum_singleton, Nat.cast_one]
      exact div_pos zero_lt_one (Real.sqrt_pos.mpr (by exact_mod_cast p.pos))
    have h1m : (1 : ℂ) - I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
    simp only [↓reduceIte]
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
      (Complex.ofReal_ne_zero.mpr hmult_pos.ne')) h1m
  decomp := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
    rw [psValue_squareDivisor_eq hX, squareDivisor_analytic_identity hX]
    have hpol : ((X : ℂ) ^ 2) * (Polynomial.C (((Real.pi ^ 2 / 6 : ℝ) : ℂ)) +
        Polynomial.C ((1 / 2 : ℂ) * sqDivConst) * Polynomial.X +
        Polynomial.C (1 / 4 : ℂ) * Polynomial.X ^ 2).eval ((X : ℂ)⁻¹) =
        (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (X : ℂ) ^ 2) +
        ((1 / 2 : ℂ) * sqDivConst * (X : ℂ)) + (1 / 4 : ℂ) := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow]
      field_simp [hX0]
    rw [hpol, pow_one]
    congr 1
    -- Regroup the `(k, m)` wave sum by `N = k² m` into `∑'_{ℓN : Fin 2 × ℕ+}`!
    let w (ℓ : Fin 2) (km : ℕ+ × ℕ+) : ℂ :=
      ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * (((Real.sqrt (km.2.val : ℝ) : ℝ) : ℂ)⁻¹) *
        (if ℓ.val = 0 then (1 - I) else (1 + I)) *
        Complex.exp (-ppRay 2 ℓ.val * (((km.1.val : ℝ) * Real.sqrt (km.2.val : ℝ) * X : ℝ) : ℂ))
    have hsum_w (ℓ : Fin 2) : Summable (fun km : ℕ+ × ℕ+ ↦ ‖w ℓ km‖) := by
      let c : ℝ := 2 * Real.pi ^ (3 / 2 : ℝ) * X
      have hc : 0 < c := by positivity
      have hre_ray : (ppRay 2 ℓ.val).re = 2 * Real.pi ^ (3 / 2 : ℝ) := by
        fin_cases ℓ
        · dsimp only; exact (congrArg Complex.re ppRay_two_zero).trans (by simp [sqRay0])
        · dsimp only; exact (congrArg Complex.re ppRay_two_one).trans (by simp [sqRay1])
      have hnorm_pm : ‖if ℓ.val = 0 then (1 : ℂ) - I else 1 + I‖ = Real.sqrt 2 := by
        split_ifs <;> (rw [Complex.norm_def, Complex.normSq_apply]; norm_num)
      let K0 : ℝ := Real.sqrt Real.pi / 2 * Real.sqrt 2
      rw [← (Equiv.sigmaEquivProd ℕ+ ℕ+).summable_iff]
      refine (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr ⟨fun k ↦ ?_, ?_⟩
      · have hdom := (summable_pow_mul_exp_neg_rpow (d := 2) (by decide)
          (mul_pos hc (Nat.cast_pos.mpr k.pos)) 0).mul_left K0
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hdom
        have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.pos
        have hm_sq : (1 : ℝ) ≤ Real.sqrt (m.val : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
        have hre_e : (-ppRay 2 ℓ.val * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
            -(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := by
          rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
              sub_zero, hre_ray, Real.sqrt_eq_rpow]; dsimp [c]; norm_num; ring
        simp only [Equiv.sigmaEquivProd_apply, w, norm_mul, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Real.sqrt Real.pi / 2),
          abs_of_nonneg (Real.sqrt_nonneg _), hnorm_pm, Complex.norm_exp, hre_e, pow_zero, one_mul]
        have hinv_le : (Real.sqrt (m.val : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm_sq
        calc (Real.sqrt Real.pi / 2) * (Real.sqrt (m.val : ℝ))⁻¹ * Real.sqrt 2 *
              Real.exp (-(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))
            ≤ (Real.sqrt Real.pi / 2) * 1 * Real.sqrt 2 *
              Real.exp (-(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by gcongr
          _ = K0 * Real.exp (-(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by dsimp [K0]; ring
      · let c₀ : ℝ := c / 2
        have hc₀ : 0 < c₀ := half_pos hc
        let S₀ := ∑' m : ℕ+, (m.val : ℝ) ^ 0 * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))
        have hS₀ : Summable (fun m : ℕ+ ↦ (m.val : ℝ) ^ 0 * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) :=
          summable_pow_mul_exp_neg_rpow (d := 2) (by decide) hc₀ 0
        have hdom := ((Real.summable_pow_mul_exp_neg_nat_mul 0 hc₀).comp_injective PNat.coe_injective).mul_left
          (K0 * S₀)
        refine Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hdom
        have hk1 : (1 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.pos
        have hle_m (m : ℕ+) : ‖w ℓ (k, m)‖ ≤
            (K0 * Real.exp (-c₀ * (k.val : ℝ))) *
              ((m.val : ℝ) ^ 0 * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) := by
          have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.pos
          have hm_r : (1 : ℝ) ≤ (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := Real.one_le_rpow hm1 (by norm_num)
          have hm_sq : (1 : ℝ) ≤ Real.sqrt (m.val : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
          have hre_e : (-ppRay 2 ℓ.val * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
              -(2 * c₀ * (k.val : ℝ) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by
            rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
                sub_zero, hre_ray, Real.sqrt_eq_rpow]; dsimp [c₀, c]; norm_num; ring
          have hexp_s : Real.exp (-(2 * c₀ * (k.val : ℝ) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) ≤
              Real.exp (-c₀ * (k.val : ℝ)) * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
            have h1 : (k.val : ℝ) + (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) ≤
                2 * ((k.val : ℝ) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by nlinarith
            nlinarith
          simp only [w, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < Real.sqrt Real.pi / 2),
            abs_of_nonneg (Real.sqrt_nonneg _), hnorm_pm, Complex.norm_exp, hre_e, pow_zero, one_mul]
          have hinv_le : (Real.sqrt (m.val : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm_sq
          calc (Real.sqrt Real.pi / 2) * (Real.sqrt (m.val : ℝ))⁻¹ * Real.sqrt 2 *
                Real.exp (-(2 * c₀ * (k.val : ℝ) * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))))
              ≤ (Real.sqrt Real.pi / 2) * 1 * Real.sqrt 2 *
                (Real.exp (-c₀ * (k.val : ℝ)) * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))) := by gcongr
            _ = _ := by dsimp [K0]; ring
        have hinner : Summable (fun m : ℕ+ ↦ ‖w ℓ (k, m)‖) :=
          Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle_m (hS₀.mul_left _)
        have hts := hinner.tsum_le_tsum hle_m (hS₀.mul_left _)
        rw [tsum_mul_left] at hts
        simp only [Function.comp_def, Equiv.sigmaEquivProd_apply, pow_zero, one_mul]
        exact hts.trans_eq (by dsimp only [S₀]; ring)
    let rhsTerm (ℓN : Fin 2 × ℕ+) : ℂ :=
      ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * ((sqDivWaveMult ℓN.2.val : ℝ) : ℂ) *
        (if ℓN.1.val = 0 then (1 - I) else (1 + I)) *
        Complex.exp (-ppWaveRate 2 ℓN.1 ℓN.2 * (X : ℂ))
    have hgroup (ℓ : Fin 2) : (∑' km : ℕ+ × ℕ+, w ℓ km) = ∑' N : ℕ+, rhsTerm (ℓ, N) := by
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
          (fun k ↦ ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * (((k.val : ℝ) / Real.sqrt (N.val : ℝ) : ℝ) : ℂ) *
            (if ℓ.val = 0 then (1 - I) else (1 + I)) *
            Complex.exp (-ppWaveRate 2 ℓ N * (X : ℂ)))
          (fun km ↦ by
            have hkm : km.val.1.val ^ 2 * km.val.2.val = N.val := congrArg Subtype.val km.property
            have hk_pos : (0 : ℝ) < (km.val.1.val : ℝ) := by exact_mod_cast km.val.1.pos
            have hN_sqrt : Real.sqrt (N.val : ℝ) = (km.val.1.val : ℝ) * Real.sqrt (km.val.2.val : ℝ) := by
              rw [← hkm, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk_pos.le]
            have hinv_m : (Real.sqrt (km.val.2.val : ℝ))⁻¹ = (km.val.1.val : ℝ) / Real.sqrt (N.val : ℝ) := by
              have hsm : Real.sqrt (km.val.2.val : ℝ) ≠ 0 :=
                (Real.sqrt_pos.mpr (by exact_mod_cast km.val.2.pos)).ne'
              rw [hN_sqrt]; field_simp [hk_pos.ne', hsm]
            have hN_rpow : (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) = Real.sqrt (N.val : ℝ) := by
              rw [Real.sqrt_eq_rpow]; norm_num
            dsimp only [w, e, Equiv.coe_fn_mk, ppWaveRate]
            rw [hN_rpow, ← Complex.ofReal_inv, hinv_m]
            congr 2
            rw [hN_sqrt]; push_cast; ring)]
      rw [Finset.univ_eq_attach,
          Finset.sum_attach S (fun k : ℕ ↦ ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) *
            (((k : ℝ) / Real.sqrt (N.val : ℝ) : ℝ) : ℂ) *
            (if ℓ.val = 0 then (1 - I) else (1 + I)) *
            Complex.exp (-ppWaveRate 2 ℓ N * (X : ℂ)))]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Complex.ofReal_sum, ← Finset.sum_div]
      rfl
    have hsum_rhs_norm : Summable (fun ℓN : Fin 2 × ℕ+ ↦ ‖rhsTerm ℓN‖) := by
      rw [← (Equiv.sigmaEquivProd (Fin 2) ℕ+).summable_iff]
      refine (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr ⟨fun ℓ ↦ ?_, hasSum_fintype _ |>.summable⟩
      have hc : 0 < (ppRay 2 ℓ.val).re * X := mul_pos (ppRay_re_pos (by decide) ℓ.isLt) hX
      have hnorm_pm : ‖if ℓ.val = 0 then (1 : ℂ) - I else 1 + I‖ = Real.sqrt 2 := by
        split_ifs <;> (rw [Complex.norm_def, Complex.normSq_apply]; norm_num)
      have hdom := (summable_pow_mul_exp_neg_rpow (d := 2) (by decide) hc 2).mul_left
        (Real.sqrt Real.pi / 2 * Real.sqrt 2)
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) hdom
      have hN1 : (1 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast N.pos
      have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt (N.val : ℝ) := by simpa using Real.sqrt_le_sqrt hN1
      have hmult_nn : 0 ≤ sqDivWaveMult N.val :=
        div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      have hmult_le : sqDivWaveMult N.val ≤ (N.val : ℝ) ^ 2 := by
        unfold sqDivWaveMult
        calc _ ≤ (∑ k ∈ (Finset.Icc 1 N.val).filter (fun k ↦ k ^ 2 ∣ N.val), (k : ℝ)) / 1 :=
              div_le_div_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) zero_lt_one hsqrt_ge
          _ = _ := div_one _
          _ ≤ ∑ _k ∈ Finset.Icc 1 N.val, (N.val : ℝ) :=
              (Finset.sum_le_sum fun k hk ↦ by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2).trans
                (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) fun _ _ _ ↦ Nat.cast_nonneg _)
          _ = (N.val : ℝ) ^ 2 := by simp [sq]
      have hre : (-ppWaveRate 2 ℓ N * (X : ℂ)).re =
          -((ppRay 2 ℓ.val).re * X) * (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := by
        simp [ppWaveRate, Complex.mul_re]; ring
      simp only [Equiv.sigmaEquivProd_apply, rhsTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < Real.sqrt Real.pi / 2), abs_of_nonneg hmult_nn,
        hnorm_pm, Complex.norm_exp, hre]
      calc (Real.sqrt Real.pi / 2) * sqDivWaveMult N.val * Real.sqrt 2 *
            Real.exp (-((ppRay 2 ℓ.val).re * X) * (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ)))
          ≤ (Real.sqrt Real.pi / 2) * (N.val : ℝ) ^ 2 * Real.sqrt 2 *
            Real.exp (-((ppRay 2 ℓ.val).re * X) * (N.val : ℝ) ^ (1 / ((2 : ℕ) : ℝ))) := by gcongr
        _ = _ := by ring
    have hsum_rhs : Summable rhsTerm := hsum_rhs_norm.of_norm
    have hval_split : (∑' ℓN : Fin 2 × ℕ+, rhsTerm ℓN) =
        (∑' N : ℕ+, rhsTerm (0, N)) + (∑' N : ℕ+, rhsTerm (1, N)) := by
      rw [hsum_rhs.tsum_prod' (fun ℓ ↦ hsum_rhs.comp_injective fun N₁ N₂ h ↦ by injection h),
          tsum_fintype, Fin.sum_univ_two]
    have hwk_sum (ℓ : Fin 2) : Summable (fun k : ℕ+ ↦ ∑' m : ℕ+, w ℓ (k, m)) := by
      have h1 := ((Equiv.sigmaEquivProd ℕ+ ℕ+).summable_iff.mpr (hsum_w ℓ))
      have h2 := (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mp h1
      refine Summable.of_norm_bounded (g := fun k : ℕ+ ↦ ∑' m : ℕ+, ‖w ℓ (k, m)‖) h2.2 fun k ↦
        norm_tsum_le_tsum_norm ((hsum_w ℓ).comp_injective fun m₁ m₂ h ↦ by injection h)
    have hrhs_eq : (∑' ℓN : Fin 2 × ℕ+, rhsTerm ℓN) =
        ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) *
          ∑' k : ℕ+, ∑' m : ℕ+, (((Real.sqrt (m.val : ℝ) : ℝ) : ℂ)⁻¹) *
            ((1 - I) * Complex.exp (-sqRay0 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)) +
             (1 + I) * Complex.exp (-sqRay1 * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ))) := by
      rw [hval_split, ← hgroup 0, ← hgroup 1,
          (hsum_w 0).of_norm.tsum_prod' (fun k ↦ (hsum_w 0).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h),
          (hsum_w 1).of_norm.tsum_prod' (fun k ↦ (hsum_w 1).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h),
          ← (hwk_sum 0).tsum_add (hwk_sum 1), ← tsum_mul_left]
      apply tsum_congr; intro k
      have hs0 : Summable (fun m : ℕ+ ↦ w 0 (k, m)) :=
        ((hsum_w 0).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h)
      have hs1 : Summable (fun m : ℕ+ ↦ w 1 (k, m)) :=
        ((hsum_w 1).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h)
      rw [← hs0.tsum_add hs1, ← tsum_mul_left]
      apply tsum_congr; intro m
      dsimp only [w]
      rw [show (0 : Fin 2).val = 0 from rfl, show (1 : Fin 2).val = 1 from rfl,
          ppRay_two_zero, ppRay_two_one]
      simp only [↓reduceIte, one_ne_zero]; ring
    change (((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * (X : ℂ)) * _ = (X : ℂ) * ∑' ℓN : Fin 2 × ℕ+, rhsTerm ℓN
    rw [hrhs_eq]; ring

/-- **100% UNCONDITIONAL Differential Transcendence of the Square-Divisor Generating Function
`L_{2, 0}(q) = ∑_{n ≥ 1} q^{n²} / (1 - q^{n²}) = ∑_{N ≥ 1} d_□(N) q^N` over `ℂ(q)`**! -/
theorem squareDivisor_non_ade :
    AlgebraicIndependent ℂ (seriesCoordinates squareDivisorSeries) :=
  sqRayProfile_non_ade squareDivisorProfile

/-- **100% UNCONDITIONAL Joint Differential Independence of Distinct Square-Divisor Dilations
`{L_{2, 0}(q^{a_1}), …, L_{2, 0}(q^{a_s})}` over `ℂ(q)`**! -/
theorem squareDivisor_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i ↦ squareDivisorDilated (a i).val)) :=
  sqRayProfile_dilations_diff_indep squareDivisorProfile a ha

end
end CubicTheta.AllD
