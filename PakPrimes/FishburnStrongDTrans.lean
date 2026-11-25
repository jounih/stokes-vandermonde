module

public import PakPrimes.FishburnTorusKnots
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Strong Differential Transcendence over Convergent Meromorphic Germs `ℂ({x})`

This module upgrades `PakPrimes.FishburnTorusKnots` (differential transcendence over `ℂ(x)`) to
**strong differential transcendence over the field `ℂ({x})` of convergent meromorphic germs at `0`**
(matching the full base field of Bostan–Di Vizio–Raschel, AJM 2024, Theorem 3 & §2.2.6, and
Klazar 2003) for:
- the literal Fishburn ordinary generating function `fishburnSeries`,
- Glaisher's `T`-number / trefoil Euler series `fishburnEulerSeries`, and
- ALL torus knots `T(p, q)` (`2 ≤ p`, `2 ≤ q`), both `torusKnotEulerSeries p q` and
  `torusKnotPerturbativeSeries p q`.

### Architecture
1. **Ring `ℂ{x}` (`ConvergentPowerSeries`) & Field `ℂ({x})` (`FractionRing ConvergentPowerSeries`)**:
   Defines `IsConvergentPS`, packages `ConvergentPowerSeries : Subring (PowerSeries ℂ)`, proves the
   exact bridge `isConvergentPS_iff_exists_analyticAt` to Mathlib's `AnalyticAt ℂ`, constructs
   analytic evaluation `evalConv` with `HasAsympExp`, and establishes closure under `derivative`,
   `exp`, `rescale`, `zagierSubst`, and `PowerSeries.subst` (`g.constantCoeff = 0`).
2. **Entire Exponential-Type Borel Minor Embedding (`convMinor`, `abelConv_conv_borel_transfer`)**:
   Embeds every `a ∈ ℂ{w}` as an entire exponential-type Borel minor with zero Stokes jump and
   exact Laplace value `evalConv a p⁻¹`, upgrading `abelConv_borel_transfer` to `MvPolynomial`
   over `ConvergentPowerSeries`.
3. **Lowest-`w`-Order Branch-Point Stokes–Vandermonde Descent over `ℂ{w}` (`L_conv`, `coeffW`,
   `abelConv_no_conv_ade`)**:
   Establishes the `α = 1/2` branch-point Stokes jump on the lateral Abel-convolution sums,
   proves strict `Y`-total-degree drop and exact shift invariance for `L_conv`, extracts the
   lowest-`w`-order non-constant polynomial `coeffW k₀ Qmin`, and derives the Vandermonde
   contradiction.
4. **Invertible Triangular Transfers & Flagship Meromorphic Theorems**:
   Proves `triangular_aeval_injective`, transfers `X^2 * E → E`, `scaleNegPS`, and Zagier's
   substitution `fishburnSeries → fishburnEulerSeries`, clears denominators from `ℂ({x})` to
   `ℂ{x}`, and exports the four flagship unconditional theorems over `ℂ({x})`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.FishburnStrongDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
  PakPrimes.BranchPointStokes PakPrimes.PrimeNome PakPrimes.FishburnTorusKnots
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Ring of Convergent Power Series `ℂ{x}` & Bridge to `AnalyticAt ℂ` -/

/-- Geometric coefficient growth characterizing convergent power series at `0`:
`∃ C ≥ 0, R > 0, ∀ n, ‖[X^n] f‖ ≤ C * R^n`. -/
@[expose] def IsConvergentPS (f : PowerSeries ℂ) : Prop :=
  ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ n : ℕ, ‖PowerSeries.coeff n f‖ ≤ C * R ^ n

lemma isConvergentPS_zero : IsConvergentPS (0 : PowerSeries ℂ) :=
  ⟨0, 1, le_rfl, zero_lt_one, fun n => by simp⟩

lemma isConvergentPS_C (c : ℂ) : IsConvergentPS (PowerSeries.C c) := by
  refine ⟨‖c‖, 1, norm_nonneg c, zero_lt_one, fun n => ?_⟩
  cases n with
  | zero => simp
  | succ n => simp [norm_nonneg]

lemma isConvergentPS_one : IsConvergentPS (1 : PowerSeries ℂ) := by
  simpa [map_one] using isConvergentPS_C 1

lemma isConvergentPS_X : IsConvergentPS (PowerSeries.X : PowerSeries ℂ) := by
  refine ⟨1, 1, zero_le_one, zero_lt_one, fun n => ?_⟩
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

lemma isConvergentPS_neg {f : PowerSeries ℂ} (hf : IsConvergentPS f) :
    IsConvergentPS (-f) := by
  obtain ⟨C, R, hC, hR, hbd⟩ := hf
  exact ⟨C, R, hC, hR, fun n => by simpa using hbd n⟩

lemma isConvergentPS_add {f g : PowerSeries ℂ}
    (hf : IsConvergentPS f) (hg : IsConvergentPS g) :
    IsConvergentPS (f + g) := by
  obtain ⟨Cf, Rf, hCf, hRf, hbdf⟩ := hf
  obtain ⟨Cg, Rg, hCg, hRg, hbdg⟩ := hg
  let R : ℝ := max Rf Rg
  have hR : 0 < R := lt_of_lt_of_le hRf (le_max_left _ _)
  refine ⟨Cf + Cg, R, add_nonneg hCf hCg, hR, fun n => ?_⟩
  rw [map_add, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (hbdf n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hRf.le (le_max_left _ _) n) hCf)
  · exact (hbdg n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hRg.le (le_max_right _ _) n) hCg)

private lemma nat_succ_le_two_pow (n : ℕ) : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
  have hnat : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  exact_mod_cast hnat

lemma isConvergentPS_mul {f g : PowerSeries ℂ}
    (hf : IsConvergentPS f) (hg : IsConvergentPS g) :
    IsConvergentPS (f * g) := by
  obtain ⟨Cf, Rf, hCf, hRf, hbdf⟩ := hf
  obtain ⟨Cg, Rg, hCg, hRg, hbdg⟩ := hg
  let R₀ : ℝ := max Rf Rg
  have hR₀ : 0 < R₀ := lt_of_lt_of_le hRf (le_max_left _ _)
  refine ⟨Cf * Cg, 2 * R₀, mul_nonneg hCf hCg, by positivity, fun n => ?_⟩
  rw [PowerSeries.coeff_mul]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal n, (Cf * Cg) * R₀ ^ n := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [norm_mul]
        have hf1 : ‖PowerSeries.coeff p.1 f‖ ≤ Cf * R₀ ^ p.1 :=
          (hbdf p.1).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hRf.le (le_max_left _ _) p.1) hCf)
        have hg2 : ‖PowerSeries.coeff p.2 g‖ ≤ Cg * R₀ ^ p.2 :=
          (hbdg p.2).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hRg.le (le_max_right _ _) p.2) hCg)
        calc ‖PowerSeries.coeff p.1 f‖ * ‖PowerSeries.coeff p.2 g‖
            ≤ (Cf * R₀ ^ p.1) * (Cg * R₀ ^ p.2) :=
              mul_le_mul hf1 hg2 (norm_nonneg _) (mul_nonneg hCf (pow_nonneg hR₀.le _))
          _ = (Cf * Cg) * (R₀ ^ p.1 * R₀ ^ p.2) := by ring
          _ = (Cf * Cg) * R₀ ^ n := by rw [← pow_add, hsum]
    _ = ((n + 1 : ℕ) : ℝ) * ((Cf * Cg) * R₀ ^ n) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ n * ((Cf * Cg) * R₀ ^ n) :=
        mul_le_mul_of_nonneg_right (nat_succ_le_two_pow n) (by positivity)
    _ = (Cf * Cg) * (2 * R₀) ^ n := by rw [mul_pow]; ring

/-- The subring `ℂ{x} ⊆ ℂ[[x]]` of convergent power series at `0`. -/
@[expose] def convergentSubring : Subring (PowerSeries ℂ) where
  carrier := {f : PowerSeries ℂ | IsConvergentPS f}
  mul_mem' hf hg := isConvergentPS_mul hf hg
  one_mem' := isConvergentPS_one
  add_mem' hf hg := isConvergentPS_add hf hg
  zero_mem' := isConvergentPS_zero
  neg_mem' hf := isConvergentPS_neg hf

/-- The integral domain `ℂ{x}` of convergent power series at `0`. -/
abbrev ConvergentPowerSeries : Type := convergentSubring

/-- Canonical injective ring embedding `ℂ{x} ↪ ℂ[[x]]`. -/
@[expose] def toPS : ConvergentPowerSeries →+* PowerSeries ℂ :=
  convergentSubring.subtype

lemma toPS_injective : Function.Injective toPS := Subtype.val_injective

@[simp] lemma toPS_apply (a : ConvergentPowerSeries) : toPS a = a.val := rfl

/-- Constant embedding `ℂ →+* ℂ{x}`. -/
@[expose] def convC : ℂ →+* ConvergentPowerSeries where
  toFun c := ⟨PowerSeries.C c, isConvergentPS_C c⟩
  map_one' := Subtype.ext (map_one PowerSeries.C)
  map_mul' a b := Subtype.ext (map_mul PowerSeries.C a b)
  map_zero' := Subtype.ext (map_zero PowerSeries.C)
  map_add' a b := Subtype.ext (map_add PowerSeries.C a b)

/-- Coordinate indeterminate `X ∈ ℂ{x}`. -/
@[expose] def convX : ConvergentPowerSeries := ⟨PowerSeries.X, isConvergentPS_X⟩

lemma isConvergentPS_coe_poly (p : Polynomial ℂ) : IsConvergentPS (p : PowerSeries ℂ) := by
  let C : ℝ := ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖
  refine ⟨C, 1, Finset.sum_nonneg fun _ _ => norm_nonneg _, zero_lt_one, fun n => ?_⟩
  rw [Polynomial.coeff_coe, one_pow, mul_one]
  by_cases hn : n ≤ p.natDegree
  · exact Finset.single_le_sum (f := fun k => ‖p.coeff k‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn), norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Polynomial embedding `ℂ[x] →+* ℂ{x}`. -/
@[expose] def polyToConv : Polynomial ℂ →+* ConvergentPowerSeries where
  toFun p := ⟨(p : PowerSeries ℂ), isConvergentPS_coe_poly p⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' p q := Subtype.ext (by simp)

@[simp] lemma toPS_polyToConv (p : Polynomial ℂ) :
    toPS (polyToConv p) = (p : PowerSeries ℂ) := rfl

@[simp] lemma toPS_convC (c : ℂ) : toPS (convC c) = PowerSeries.C c := rfl

@[simp] lemma toPS_convX : toPS convX = PowerSeries.X := rfl

/-- General power-series ball construction from absolute summability on a circle of radius `r > 0`. -/
private lemma hasFPowerSeriesOnBall_tsum_of_bound (c : ℕ → ℂ) {r : ℝ} (hr : 0 < r)
    (hs : Summable fun n : ℕ => ‖c n‖ * r ^ n) :
    HasFPowerSeriesOnBall (fun z : ℂ => ∑' n : ℕ, c n * z ^ n)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 (ENNReal.ofReal r) := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  let rn : NNReal := ⟨r, hr.le⟩
  have hr_eq : (rn : ENNReal) = ENNReal.ofReal r := (ENNReal.ofReal_eq_coe_nnreal hr.le).symm
  have hr_le : ENNReal.ofReal r ≤ p.radius := by
    rw [← hr_eq]
    refine p.le_radius_of_bound (∑' k : ℕ, ‖c k‖ * r ^ k) fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
    exact hs.le_tsum n fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le k)
  refine ⟨hr_le, ENNReal.ofReal_pos.mpr hr, fun {y} hy => ?_⟩
  rw [Metric.mem_eball, edist_zero_right, ← hr_eq, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] at hy
  have hyn : ‖y‖ < r := hy
  have hsum_y : Summable fun n : ℕ => c n * y ^ n := by
    refine Summable.of_norm_bounded hs fun n => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hyn.le n) (norm_nonneg _)
  have hfn : (fun n : ℕ => p n fun _ => y) = fun n : ℕ => c n * y ^ n := by
    funext n
    simpa [p, smul_eq_mul] using FormalMultilinearSeries.ofScalars_apply_eq c y n
  rw [zero_add, hfn]
  exact hsum_y.hasSum

/-- **Textbook Pinning Equivalence (`ℂ{x}` = Holomorphic Germs at `0`)**:
A formal power series `f ∈ ℂ[[x]]` belongs to `ConvergentPowerSeries` if and only if it is the
Taylor series at `0` of a function `g : ℂ → ℂ` analytic at `0` (`AnalyticAt ℂ g 0`). -/
theorem isConvergentPS_iff_exists_analyticAt (f : PowerSeries ℂ) :
    IsConvergentPS f ↔
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
        ∀ n : ℕ, PowerSeries.coeff n f = iteratedDeriv n g 0 / (n.factorial : ℂ) := by
  constructor
  · rintro ⟨C, R, hC, hR, hbd⟩
    let r : ℝ := (2 * R)⁻¹
    have hr : 0 < r := by positivity
    have hs : Summable fun n : ℕ => ‖PowerSeries.coeff n f‖ * r ^ n := by
      have hgeom : Summable fun n : ℕ => C * (1 / 2 : ℝ) ^ n :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le n))
        (fun n => ?_) hgeom
      have hRr : R * r = 1 / 2 := by dsimp only [r]; field_simp [hR.ne']
      calc ‖PowerSeries.coeff n f‖ * r ^ n
          ≤ (C * R ^ n) * r ^ n := mul_le_mul_of_nonneg_right (hbd n) (pow_nonneg hr.le n)
        _ = C * (R * r) ^ n := by rw [mul_pow]; ring
        _ = C * (1 / 2 : ℝ) ^ n := by rw [hRr]
    let g : ℂ → ℂ := fun z => ∑' n : ℕ, PowerSeries.coeff n f * z ^ n
    have hball := hasFPowerSeriesOnBall_tsum_of_bound (fun n => PowerSeries.coeff n f) hr hs
    have han : AnalyticAt ℂ g 0 := hball.analyticAt
    refine ⟨g, han, fun n => ?_⟩
    have heq := hball.hasFPowerSeriesAt.eq_formalMultilinearSeries han.hasFPowerSeriesAt
    have hval := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n fun _ => (1 : ℂ)) heq
    simpa [FormalMultilinearSeries.ofScalars_apply_eq] using hval
  · rintro ⟨g, hg, hcoeff⟩
    obtain ⟨r, hr⟩ := hg.hasFPowerSeriesAt
    let p := FormalMultilinearSeries.ofScalars ℂ fun n => iteratedDeriv n g 0 / (n.factorial : ℂ)
    have hpos_rad : (0 : ENNReal) < p.radius := lt_of_lt_of_le hr.r_pos hr.r_le
    obtain ⟨ρ, hρ_pos, hρ_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos_rad
    have hρ_real_pos : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast (ENNReal.coe_pos.mp hρ_pos)
    obtain ⟨a, ha, ho⟩ := p.isLittleO_of_lt_radius hρ_lt
    have hev : ∀ᶠ n : ℕ in atTop, ‖p n‖ * (ρ : ℝ) ^ n ≤ 1 := by
      have h1 := ho.bound (show (0 : ℝ) < 1 by norm_num)
      filter_upwards [h1] with n hn
      have han_le : a ^ n ≤ 1 := pow_le_one₀ ha.1.le ha.2.le
      have hnn : 0 ≤ ‖p n‖ * (ρ : ℝ) ^ n := mul_nonneg (norm_nonneg _) (pow_nonneg hρ_real_pos.le n)
      rw [Real.norm_of_nonneg hnn, one_mul, Real.norm_of_nonneg (pow_nonneg ha.1.le n)] at hn
      exact hn.trans han_le
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    let C : ℝ := max 1 (∑ k ∈ Finset.range N, ‖p k‖ * (ρ : ℝ) ^ k)
    have hC : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
    refine ⟨C, (ρ : ℝ)⁻¹, hC, inv_pos.mpr hρ_real_pos, fun n => ?_⟩
    have hnorm_eq : ‖PowerSeries.coeff n f‖ = ‖p n‖ := by
      rw [hcoeff n, FormalMultilinearSeries.ofScalars_norm]
    have hmul_le : ‖p n‖ * (ρ : ℝ) ^ n ≤ C := by
      by_cases hn : N ≤ n
      · exact (hN n hn).trans (le_max_left _ _)
      · have hlt : n < N := Nat.lt_of_not_ge hn
        exact (Finset.single_le_sum (f := fun k => ‖p k‖ * (ρ : ℝ) ^ k)
          (fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hρ_real_pos.le k))
          (Finset.mem_range.mpr hlt)).trans (le_max_right _ _)
    rw [hnorm_eq, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hρ_real_pos n)]
    exact hmul_le

/-- Analytic evaluation `evalConv a z = ∑' n, [X^n] a * z^n` of a convergent power series. -/
@[expose] def evalConv (a : ConvergentPowerSeries) (z : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n a.val * z ^ n

lemma evalConv_summable_norm (a : ConvergentPowerSeries) {C R : ℝ}
    (_hC : 0 ≤ C) (hR : 0 < R) (hbd : ∀ n, ‖PowerSeries.coeff n a.val‖ ≤ C * R ^ n)
    {z : ℂ} (hz : ‖z‖ < R⁻¹) :
    Summable fun n : ℕ => ‖PowerSeries.coeff n a.val * z ^ n‖ := by
  have hRz_lt : R * ‖z‖ < 1 := by
    calc R * ‖z‖ < R * R⁻¹ := mul_lt_mul_of_pos_left hz hR
      _ = 1 := mul_inv_cancel₀ hR.ne'
  have hgeom : Summable fun n : ℕ => C * (R * ‖z‖) ^ n :=
    (summable_geometric_of_lt_one (mul_nonneg hR.le (norm_nonneg z)) hRz_lt).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hgeom
  rw [norm_mul, norm_pow, mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hbd n) (pow_nonneg (norm_nonneg z) n)

lemma evalConv_hasSum (a : ConvergentPowerSeries) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (hbd : ∀ n, ‖PowerSeries.coeff n a.val‖ ≤ C * R ^ n)
    {z : ℂ} (hz : ‖z‖ < R⁻¹) :
    HasSum (fun n : ℕ => PowerSeries.coeff n a.val * z ^ n) (evalConv a z) :=
  (evalConv_summable_norm a hC hR hbd hz).of_norm.hasSum

lemma evalConv_zero (z : ℂ) : evalConv 0 z = 0 := by
  simp [evalConv]

lemma evalConv_C (c z : ℂ) : evalConv (convC c) z = c := by
  unfold evalConv convC
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [PowerSeries.coeff_C, hn]

lemma evalConv_X (z : ℂ) : evalConv convX z = z := by
  unfold evalConv convX
  rw [tsum_eq_single 1]
  · simp
  · intro n hn; simp [PowerSeries.coeff_X, hn]

lemma evalConv_poly (p : Polynomial ℂ) (z : ℂ) : evalConv (polyToConv p) z = p.eval z := by
  unfold evalConv polyToConv
  rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1))]
  · rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => by simp
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hn)]

lemma evalConv_add_of_lt (a b : ConvergentPowerSeries) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → evalConv (a + b) z = evalConv a z + evalConv b z := by
  obtain ⟨Ca, Ra, hCa, hRa, hbda⟩ := a.property
  obtain ⟨Cb, Rb, hCb, hRb, hbdb⟩ := b.property
  refine ⟨min Ra⁻¹ Rb⁻¹, lt_min (inv_pos.mpr hRa) (inv_pos.mpr hRb), fun z hz => ?_⟩
  have hsa := (evalConv_summable_norm a hCa hRa hbda (lt_of_lt_of_le hz (min_le_left _ _))).of_norm
  have hsb := (evalConv_summable_norm b hCb hRb hbdb (lt_of_lt_of_le hz (min_le_right _ _))).of_norm
  unfold evalConv
  change ∑' n, PowerSeries.coeff n (a.val + b.val) * z ^ n = _
  simp_rw [map_add, add_mul]
  exact hsa.tsum_add hsb

lemma evalConv_add_eventually (a b : ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop, evalConv (a + b) (u : ℂ)⁻¹ = evalConv a (u : ℂ)⁻¹ + evalConv b (u : ℂ)⁻¹ := by
  obtain ⟨r, hr, hadd⟩ := evalConv_add_of_lt a b
  filter_upwards [eventually_gt_atTop r⁻¹] with u hu
  have hu_pos : 0 < u := lt_trans (inv_pos.mpr hr) hu
  refine hadd (u : ℂ)⁻¹ ?_
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
  exact (inv_lt_comm₀ hu_pos hr).mpr hu

lemma evalConv_mul_of_lt (a b : ConvergentPowerSeries) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → evalConv (a * b) z = evalConv a z * evalConv b z := by
  obtain ⟨Ca, Ra, hCa, hRa, hbda⟩ := a.property
  obtain ⟨Cb, Rb, hCb, hRb, hbdb⟩ := b.property
  refine ⟨min Ra⁻¹ Rb⁻¹, lt_min (inv_pos.mpr hRa) (inv_pos.mpr hRb), fun z hz => ?_⟩
  have hsa := evalConv_summable_norm a hCa hRa hbda (lt_of_lt_of_le hz (min_le_left _ _))
  have hsb := evalConv_summable_norm b hCb hRb hbdb (lt_of_lt_of_le hz (min_le_right _ _))
  symm
  unfold evalConv
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb]
  refine tsum_congr fun n => ?_
  change _ = PowerSeries.coeff n (a.val * b.val) * z ^ n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← hsum, pow_add]; ring

lemma evalConv_mul_eventually (a b : ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop, evalConv (a * b) (u : ℂ)⁻¹ = evalConv a (u : ℂ)⁻¹ * evalConv b (u : ℂ)⁻¹ := by
  obtain ⟨r, hr, hmul⟩ := evalConv_mul_of_lt a b
  filter_upwards [eventually_gt_atTop r⁻¹] with u hu
  have hu_pos : 0 < u := lt_trans (inv_pos.mpr hr) hu
  refine hmul (u : ℂ)⁻¹ ?_
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
  exact (inv_lt_comm₀ hu_pos hr).mpr hu

lemma evalConv_eventually_bdd (a : ConvergentPowerSeries) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ u : ℝ in atTop, ‖evalConv a (u : ℂ)⁻¹‖ ≤ B := by
  obtain ⟨C, R, hC, hR, hbd⟩ := a.property
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * R)] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hRu : R * u⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hu_pos]; linarith
  have hz : ‖(u : ℂ)⁻¹‖ < R⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    have hlt : R < u := by linarith
    exact (inv_lt_inv₀ hu_pos hR).mpr hlt
  have hsn := evalConv_summable_norm a hC hR hbd hz
  have hgeom : Summable fun n : ℕ => C * (1 / 2 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hle : ‖evalConv a (u : ℂ)⁻¹‖ ≤ ∑' n : ℕ, C * (1 / 2 : ℝ) ^ n := by
    refine (norm_tsum_le_tsum_norm hsn).trans ?_
    refine hsn.tsum_le_tsum (fun n => ?_) hgeom
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    calc ‖PowerSeries.coeff n a.val‖ * u⁻¹ ^ n
        ≤ (C * R ^ n) * u⁻¹ ^ n := mul_le_mul_of_nonneg_right (hbd n) (by positivity)
      _ = C * (R * u⁻¹) ^ n := by rw [mul_pow]; ring
      _ ≤ C * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRu n) hC
  refine hle.trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num; ring

/-- Every convergent power series `a ∈ ℂ{w}` has exact all-orders `1/u` asymptotic expansion
equal to `a.val` along `u → +∞`. -/
theorem evalConv_hasAsympExp (a : ConvergentPowerSeries) :
    HasAsympExp (fun u : ℝ => evalConv a (u : ℂ)⁻¹) a.val := by
  obtain ⟨C, R, hC, hR, hbd⟩ := a.property
  intro M
  refine ⟨2 * C * R ^ M, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * R)] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hRu : R * u⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hu_pos]; linarith
  have hz : ‖(u : ℂ)⁻¹‖ < R⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    exact (inv_lt_inv₀ hu_pos hR).mpr (by linarith)
  have hsn := evalConv_summable_norm a hC hR hbd hz
  have htail : evalConv a (u : ℂ)⁻¹ -
      ∑ k ∈ Finset.range M, PowerSeries.coeff k a.val * (u : ℂ)⁻¹ ^ k =
      ∑' k : ℕ, PowerSeries.coeff (k + M) a.val * (u : ℂ)⁻¹ ^ (k + M) := by
    have hsplit := hsn.of_norm.sum_add_tsum_nat_add M
    exact sub_eq_of_eq_add' hsplit.symm
  rw [htail]
  have hsn_shift : Summable fun k : ℕ => ‖PowerSeries.coeff (k + M) a.val * (u : ℂ)⁻¹ ^ (k + M)‖ :=
    hsn.comp_injective (add_left_injective M)
  have hgeom : Summable fun k : ℕ => (C * R ^ M / u ^ M) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ‖∑' k : ℕ, PowerSeries.coeff (k + M) a.val * (u : ℂ)⁻¹ ^ (k + M)‖ ≤
      ∑' k : ℕ, (C * R ^ M / u ^ M) * (1 / 2 : ℝ) ^ k := by
    refine (norm_tsum_le_tsum_norm hsn_shift).trans ?_
    refine hsn_shift.tsum_le_tsum (fun k => ?_) hgeom
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    calc ‖PowerSeries.coeff (k + M) a.val‖ * u⁻¹ ^ (k + M)
        ≤ (C * R ^ (k + M)) * u⁻¹ ^ (k + M) :=
          mul_le_mul_of_nonneg_right (hbd (k + M)) (by positivity)
      _ = (C * R ^ M * u⁻¹ ^ M) * (R * u⁻¹) ^ k := by
          rw [pow_add, pow_add, mul_pow]; ring
      _ ≤ (C * R ^ M * u⁻¹ ^ M) * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRu k) (by positivity)
      _ = (C * R ^ M / u ^ M) * (1 / 2 : ℝ) ^ k := by rw [inv_pow, div_eq_mul_inv]; ring
  refine hle.trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num; ring

/-! #### 1B. Closure of `ℂ{x}` under Derivative, Exponential, Rescaling, and Substitution -/

lemma isConvergentPS_derivative {f : PowerSeries ℂ} (hf : IsConvergentPS f) :
    IsConvergentPS (PowerSeries.derivative f) := by
  obtain ⟨C, R, hC, hR, hbd⟩ := hf
  refine ⟨C * R, 2 * R, mul_nonneg hC hR.le, by positivity, fun n => ?_⟩
  have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [PowerSeries.coeff_derivative, hcast, norm_mul, Complex.norm_natCast, mul_comm]
  calc ((n + 1 : ℕ) : ℝ) * ‖PowerSeries.coeff (n + 1) f‖
      ≤ (2 : ℝ) ^ n * (C * R ^ (n + 1)) :=
        mul_le_mul (nat_succ_le_two_pow n) (hbd (n + 1)) (norm_nonneg _) (by positivity)
    _ = (C * R) * (2 * R) ^ n := by rw [pow_succ, mul_pow]; ring

/-- Formal derivative restricted to `ConvergentPowerSeries`. -/
@[expose] def convDeriv (a : ConvergentPowerSeries) : ConvergentPowerSeries :=
  ⟨PowerSeries.derivative a.val, isConvergentPS_derivative a.property⟩

@[simp] lemma toPS_convDeriv (a : ConvergentPowerSeries) :
    toPS (convDeriv a) = PowerSeries.derivative (toPS a) := rfl

lemma isConvergentPS_exp : IsConvergentPS (PowerSeries.exp ℂ) := by
  refine ⟨1, 1, zero_le_one, zero_lt_one, fun n => ?_⟩
  rw [PowerSeries.coeff_exp, one_pow, mul_one]
  simp only [map_div₀, map_one, map_natCast, norm_div, norm_one, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  exact div_le_one_of_le₀ h1 (by positivity)

lemma isConvergentPS_rescale (c : ℂ) {f : PowerSeries ℂ} (hf : IsConvergentPS f) :
    IsConvergentPS (PowerSeries.rescale c f) := by
  obtain ⟨C, R, hC, hR, hbd⟩ := hf
  let R' : ℝ := max ‖c‖ 1 * R
  have hR' : 0 < R' := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hR
  refine ⟨C, R', hC, hR', fun n => ?_⟩
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow]
  calc ‖c‖ ^ n * ‖PowerSeries.coeff n f‖
      ≤ (max ‖c‖ 1) ^ n * (C * R ^ n) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) (le_max_left _ _) n) (hbd n)
          (norm_nonneg _) (by positivity)
    _ = C * R' ^ n := by dsimp only [R']; rw [mul_pow]; ring

lemma isConvergentPS_zagierSubst : IsConvergentPS zagierSubst :=
  isConvergentPS_add isConvergentPS_one
    (isConvergentPS_neg (isConvergentPS_rescale (-24 : ℂ) isConvergentPS_exp))

/-- Convergent exponential series `exp(c t) = rescale c (exp ℂ) ∈ ℂ{t}`. -/
@[expose] def convExp (c : ℂ) : ConvergentPowerSeries :=
  ⟨PowerSeries.rescale c (PowerSeries.exp ℂ), isConvergentPS_rescale c isConvergentPS_exp⟩

lemma convExp_zero : convExp 0 = 1 := by
  apply Subtype.ext
  ext n
  cases n with
  | zero => simp [convExp]
  | succ k => simp [convExp]

lemma convExp_add (c d : ℂ) : convExp (c + d) = convExp c * convExp d := by
  apply Subtype.ext
  ext n
  change PowerSeries.coeff n (PowerSeries.rescale (c + d) (PowerSeries.exp ℂ)) =
    PowerSeries.coeff n (PowerSeries.rescale c (PowerSeries.exp ℂ) *
      PowerSeries.rescale d (PowerSeries.exp ℂ))
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_div₀, map_one, map_natCast]
  rw [add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hch : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hcn : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hfnk : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  rw [← hch]
  field_simp [hfk, hfnk, hcn]

lemma isUnit_convExp (c : ℂ) : IsUnit (convExp c) :=
  isUnit_iff_exists_inv.mpr ⟨convExp (-c), by rw [← convExp_add, add_neg_cancel, convExp_zero]⟩

private lemma norm_coeff_mul_weighted_sum (a b : PowerSeries ℂ) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n (a * b)‖ * r ^ n ≤
      (∑ i ∈ Finset.range N, ‖PowerSeries.coeff i a‖ * r ^ i) *
      (∑ j ∈ Finset.range N, ‖PowerSeries.coeff j b‖ * r ^ j) := by
  let F : ℕ × ℕ → ℝ := fun p => (‖PowerSeries.coeff p.1 a‖ * r ^ p.1) * (‖PowerSeries.coeff p.2 b‖ * r ^ p.2)
  have hF_nn : ∀ p, 0 ≤ F p := fun p => by positivity
  have h1 : ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n (a * b)‖ * r ^ n ≤
      ∑ n ∈ Finset.range N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [PowerSeries.coeff_mul]
    calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 b‖ * r ^ n
        ≤ (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 b‖) * r ^ n :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr n)
      _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 b‖ * r ^ n :=
          Finset.sum_mul _ _ _
      _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          dsimp only [F]; rw [norm_mul, ← hsum, pow_add]; ring
  have h2 : (∑ n ∈ Finset.range N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p) =
      ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => p.1 + p.2 < N), F p := by
    rw [← Finset.sum_sigma (f := fun x : Σ _ : ℕ, ℕ × ℕ => F x.2)]
    refine Finset.sum_bij (fun x _ => x.2) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · intro x₁ hx₁ x₂ hx₂ he
      simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hx₁ hx₂
      exact Sigma.ext (by rw [← hx₁.2, ← hx₂.2, he]) (heq_of_eq he)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      exact ⟨⟨p.1 + p.2, p⟩, by simp [Finset.HasAntidiagonal.mem_antidiagonal, hp.2], rfl⟩
    · intro _ _; rfl
  have h3 : (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => p.1 + p.2 < N), F p) ≤
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, F p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => hF_nn p
  have h4 : (∑ p ∈ Finset.range N ×ˢ Finset.range N, F p) =
      (∑ i ∈ Finset.range N, ‖PowerSeries.coeff i a‖ * r ^ i) *
      (∑ j ∈ Finset.range N, ‖PowerSeries.coeff j b‖ * r ^ j) := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  exact (h1.trans (h2.le.trans h3)).trans_eq h4

private lemma norm_coeff_pow_weighted_sum (g : PowerSeries ℂ) {r : ℝ} (hr : 0 ≤ r)
    {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n (g ^ k)‖ * r ^ n ≤
      (∑ m ∈ Finset.range N, ‖PowerSeries.coeff m g‖ * r ^ m) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Finset.sum_eq_single 0]
    · simp
    · intro n _ hn; simp [PowerSeries.coeff_one, hn]
    · intro h0; exact absurd (Finset.mem_range.mpr hN) h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    refine (norm_coeff_mul_weighted_sum (g ^ k) g hr N).trans ?_
    exact mul_le_mul_of_nonneg_right ih
      (Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr m))

/-- Closure of `ℂ{x}` under formal composition `f.subst g` whenever `g(0) = 0`. -/
theorem isConvergentPS_subst {f g : PowerSeries ℂ}
    (hf : IsConvergentPS f) (hg : IsConvergentPS g)
    (hg0 : PowerSeries.constantCoeff g = 0) :
    IsConvergentPS (f.subst g) := by
  obtain ⟨Cf, Rf, hCf, hRf, hbdf⟩ := hf
  obtain ⟨Cg, Rg, hCg, hRg, hbdg⟩ := hg
  let K : ℝ := 4 * max Rg 1 * max Cg 1 * max Rf 1
  have hK_pos : 0 < K := by positivity
  let r : ℝ := K⁻¹
  have hr_pos : 0 < r := inv_pos.mpr hK_pos
  have hRg_r : Rg * r ≤ 1 / 2 := by
    have h1 : Rg ≤ max Rg 1 := le_max_left _ _
    have h2 : 1 ≤ max Cg 1 := le_max_right _ _
    have h3 : 1 ≤ max Rf 1 := le_max_right _ _
    have h4 : 2 * Rg ≤ K := by
      dsimp only [K]
      have hprod : 1 ≤ max Cg 1 * max Rf 1 := one_le_mul_of_one_le_of_one_le h2 h3
      have hmul : 4 * max Rg 1 ≤ 4 * max Rg 1 * (max Cg 1 * max Rf 1) :=
        le_mul_of_one_le_right (by positivity) hprod
      linarith
    rw [← div_eq_mul_inv, div_le_iff₀ hK_pos]; linarith
  let M : ℝ := 2 * Cg * Rg * r
  have hM_nn : 0 ≤ M := by positivity
  have hRfM : Rf * M ≤ 1 / 2 := by
    have h1 : Rg ≤ max Rg 1 := le_max_left _ _
    have h2 : Cg ≤ max Cg 1 := le_max_left _ _
    have h3 : Rf ≤ max Rf 1 := le_max_left _ _
    have h4 : 4 * (Rf * Cg * Rg) ≤ K := by
      dsimp only [K]
      have hprod : Rf * Cg * Rg ≤ max Rf 1 * max Cg 1 * max Rg 1 := by
        have h12 : Rf * Cg ≤ max Rf 1 * max Cg 1 :=
          mul_le_mul h3 h2 hCg (by positivity)
        exact mul_le_mul h12 h1 hRg.le (by positivity)
      linarith
    have hrew : Rf * M = (2 * (Rf * Cg * Rg)) / K := by dsimp only [M, r]; ring
    rw [hrew, div_le_iff₀ hK_pos]; linarith
  have hsum_g_le : ∀ N : ℕ, ∑ m ∈ Finset.range N, ‖PowerSeries.coeff m g‖ * r ^ m ≤ M := fun N => by
    have hgeom_sum : ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j ≤ 2 := by
      have h1 : (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) * (1 - 1 / 2) = 1 - (1 / 2 : ℝ) ^ N := by
        simpa [mul_comm] using geom_sum_mul_neg (1 / 2 : ℝ) N
      have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
      linarith
    cases N with
    | zero => simpa using hM_nn
    | succ N' =>
      rw [Finset.sum_range_succ']
      have hc0 : PowerSeries.coeff 0 g = 0 := by
        rwa [PowerSeries.coeff_zero_eq_constantCoeff]
      rw [hc0, norm_zero, zero_mul, add_zero]
      calc ∑ k ∈ Finset.range N', ‖PowerSeries.coeff (k + 1) g‖ * r ^ (k + 1)
          ≤ ∑ k ∈ Finset.range N', (Cg * Rg * r) * (1 / 2 : ℝ) ^ k := by
            refine Finset.sum_le_sum fun k _ => ?_
            calc ‖PowerSeries.coeff (k + 1) g‖ * r ^ (k + 1)
                ≤ (Cg * Rg ^ (k + 1)) * r ^ (k + 1) :=
                  mul_le_mul_of_nonneg_right (hbdg (k + 1)) (by positivity)
              _ = (Cg * Rg * r) * (Rg * r) ^ k := by rw [pow_succ', pow_succ', mul_pow]; ring
              _ ≤ (Cg * Rg * r) * (1 / 2 : ℝ) ^ k :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRg_r k) (by positivity)
        _ = (Cg * Rg * r) * ∑ k ∈ Finset.range N', (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
        _ ≤ (Cg * Rg * r) * 2 := by
            have h1 : ∑ k ∈ Finset.range N', (1 / 2 : ℝ) ^ k ≤ 2 := by
              have hge : (∑ j ∈ Finset.range N', (1 / 2 : ℝ) ^ j) * (1 - 1 / 2) =
                  1 - (1 / 2 : ℝ) ^ N' := by
                simpa [mul_comm] using geom_sum_mul_neg (1 / 2 : ℝ) N'
              have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N' := by positivity
              linarith
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = M := by dsimp only [M]; ring
  have hgk_bd : ∀ k n : ℕ, ‖PowerSeries.coeff n (g ^ k)‖ ≤ M ^ k * (r⁻¹) ^ n := fun k n => by
    have h1 : ‖PowerSeries.coeff n (g ^ k)‖ * r ^ n ≤
        ∑ m ∈ Finset.range (n + 1), ‖PowerSeries.coeff m (g ^ k)‖ * r ^ m :=
      Finset.single_le_sum (f := fun m => ‖PowerSeries.coeff m (g ^ k)‖ * r ^ m)
        (fun m _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr_pos.le m))
        (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have h2 : ∑ m ∈ Finset.range (n + 1), ‖PowerSeries.coeff m (g ^ k)‖ * r ^ m ≤ M ^ k :=
      (norm_coeff_pow_weighted_sum g hr_pos.le (Nat.succ_pos n) k).trans
        (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (hsum_g_le (n + 1)) k)
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hr_pos n)]
    exact h1.trans h2
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg0
  refine ⟨2 * Cf, r⁻¹, by positivity, inv_pos.mpr hr_pos, fun n => ?_⟩
  have hcoeff_subst : PowerSeries.coeff n (f.subst g) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff n (g ^ k) := by
    rw [PowerSeries.coeff_subst' hgs, finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun k _ => by simp [smul_eq_mul]
    · intro k hk
      rw [Function.mem_support] at hk
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hnot
      have hgt : n < k := Nat.lt_of_not_le (by omega)
      obtain ⟨q, hq⟩ := pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hg0) k
      have h0 : PowerSeries.coeff n (g ^ k) = 0 := by
        rw [hq, PowerSeries.coeff_X_pow_mul']
        simp [not_le.mpr hgt]
      exact hk (by simp [h0])
  rw [hcoeff_subst]
  have hgeom2 : ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k ≤ 2 := by
    have h1 : (∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j) * (1 - 1 / 2) =
        1 - (1 / 2 : ℝ) ^ (n + 1) := by
      simpa [mul_comm] using geom_sum_mul_neg (1 / 2 : ℝ) (n + 1)
    have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
    linarith
  calc ‖∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff n (g ^ k)‖
      ≤ ∑ k ∈ Finset.range (n + 1), ‖PowerSeries.coeff k f * PowerSeries.coeff n (g ^ k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (Cf * (r⁻¹) ^ n) * (1 / 2 : ℝ) ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        calc ‖PowerSeries.coeff k f‖ * ‖PowerSeries.coeff n (g ^ k)‖
            ≤ (Cf * Rf ^ k) * (M ^ k * (r⁻¹) ^ n) :=
              mul_le_mul (hbdf k) (hgk_bd k n) (norm_nonneg _) (by positivity)
          _ = (Cf * (r⁻¹) ^ n) * (Rf * M) ^ k := by rw [mul_pow Rf M]; ring
          _ ≤ (Cf * (r⁻¹) ^ n) * (1 / 2 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRfM k) (by positivity)
    _ = (Cf * (r⁻¹) ^ n) * ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ (Cf * (r⁻¹) ^ n) * 2 := mul_le_mul_of_nonneg_left hgeom2 (by positivity)
    _ = (2 * Cf) * (r⁻¹) ^ n := by ring

/-! ### 2. Entire Exponential-Type Borel Minor Embedding of `ℂ{w}` & Convergent Borel Transfer -/

/-- Entire exponential-type Borel minor representing a convergent power series `a ∈ ℂ{w}`
with zero Stokes jump across every ray:
`atom = [w^0] a`, `density(z) = ∑_{k ≥ 0} ([w^{k+1}] a / k!) z^k`. -/
@[expose] def convMinor (a : ConvergentPowerSeries) : Minor :=
  ⟨PowerSeries.coeff 0 a.val,
   fun z : ℂ => ∑' k : ℕ, (PowerSeries.coeff (k + 1) a.val / (k.factorial : ℂ)) * z ^ k⟩

private lemma convMinor_summable_bound (a : ConvergentPowerSeries) {C R : ℝ}
    (_hC : 0 ≤ C) (_hR : 0 < R) (hbd : ∀ n, ‖PowerSeries.coeff n a.val‖ ≤ C * R ^ n)
    {r : ℝ} (hr : 0 ≤ r) :
    Summable fun k : ℕ => ‖PowerSeries.coeff (k + 1) a.val / (k.factorial : ℂ)‖ * r ^ k := by
  have hexp : Summable fun k : ℕ => (C * R) * ((R * r) ^ k / (k.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial (R * r)).mul_left (C * R)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hr k))
    (fun k => ?_) hexp
  rw [norm_div, Complex.norm_natCast]
  calc ‖PowerSeries.coeff (k + 1) a.val‖ / (k.factorial : ℝ) * r ^ k
      ≤ (C * R ^ (k + 1)) / (k.factorial : ℝ) * r ^ k := by gcongr; exact hbd (k + 1)
    _ = (C * R) * ((R * r) ^ k / (k.factorial : ℝ)) := by rw [pow_succ', mul_pow]; ring

lemma convMinor_density_hasFPowerSeriesOnBall (a : ConvergentPowerSeries) {r : ℝ} (hr : 0 < r) :
    HasFPowerSeriesOnBall (convMinor a).density
      (FormalMultilinearSeries.ofScalars ℂ fun k => PowerSeries.coeff (k + 1) a.val / (k.factorial : ℂ))
      0 (ENNReal.ofReal r) := by
  obtain ⟨C, R, hC, hR, hbd⟩ := a.property
  exact hasFPowerSeriesOnBall_tsum_of_bound _ hr (convMinor_summable_bound a hC hR hbd hr.le)

/-- `(convMinor a).density` is an entire function (`AnalyticOnNhd ℂ _ Set.univ`). -/
theorem convMinor_density_entire (a : ConvergentPowerSeries) :
    AnalyticOnNhd ℂ (convMinor a).density Set.univ := by
  intro z _
  let r : ℝ := ‖z‖ + 1
  have hr : 0 < r := by positivity
  have hball := convMinor_density_hasFPowerSeriesOnBall a hr
  have hz_mem : z ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal r) := by
    rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm]
    have hcoe : (‖z‖₊ : ENNReal) = ENNReal.ofReal ‖z‖ :=
      (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg z)).symm
    rw [hcoe]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by dsimp only [r]; linarith)
  exact hball.analyticOnNhd z hz_mem

/-- Exact formal series match: `(convMinor a).toSeries = a.val`. -/
theorem convMinor_toSeries (a : ConvergentPowerSeries) :
    (convMinor a).toSeries = a.val := by
  have hball := convMinor_density_hasFPowerSeriesOnBall a zero_lt_one
  have han : AnalyticAt ℂ (convMinor a).density 0 := hball.analyticAt
  have heq := hball.hasFPowerSeriesAt.eq_formalMultilinearSeries han.hasFPowerSeriesAt
  ext n
  cases n with
  | zero => simp [Minor.toSeries, convMinor]
  | succ k =>
    simp only [Minor.toSeries, PowerSeries.coeff_mk]
    have hval := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p k fun _ => (1 : ℂ)) heq
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] at hval
    have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hmul := congrArg (fun x : ℂ => x * (k.factorial : ℂ)) hval
    rw [div_mul_cancel₀ _ hfac, div_mul_cancel₀ _ hfac] at hmul
    exact hmul.symm

/-- Global exponential-type bound for `Minor.pull d (convMinor a).density` along EVERY ray `d : ℂ`. -/
theorem convMinor_expType (a : ConvergentPowerSeries) (d : ℂ) :
    ExpType (Minor.pull d (convMinor a).density) := by
  obtain ⟨C, R, hC, hR, hbd⟩ := a.property
  refine ⟨‖d‖ * (C * R), R * ‖d‖, by positivity, by positivity, fun v hv => ?_⟩
  unfold Minor.pull convMinor
  dsimp only
  rw [norm_mul]
  have hsum_norm : Summable fun k : ℕ =>
      ‖(PowerSeries.coeff (k + 1) a.val / (k.factorial : ℂ)) * (d * (v : ℂ)) ^ k‖ := by
    have h1 := convMinor_summable_bound a hC hR hbd (norm_nonneg (d * (v : ℂ)))
    refine h1.congr fun k => by rw [← norm_pow, ← norm_mul]
  have hexp_sum : HasSum (fun k : ℕ => (C * R) * ((R * (‖d‖ * v)) ^ k / (k.factorial : ℝ)))
      ((C * R) * Real.exp (R * (‖d‖ * v))) := by
    have h1 := NormedSpace.expSeries_div_hasSum_exp (R * (‖d‖ * v))
    rw [← Real.exp_eq_exp_ℝ] at h1
    exact h1.mul_left (C * R)
  have hdv : ‖d * (v : ℂ)‖ = ‖d‖ * v := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv]
  have hdens : ‖∑' k : ℕ, (PowerSeries.coeff (k + 1) a.val / (k.factorial : ℂ)) * (d * (v : ℂ)) ^ k‖ ≤
      (C * R) * Real.exp (R * (‖d‖ * v)) := by
    refine (norm_tsum_le_tsum_norm hsum_norm).trans ?_
    rw [← hexp_sum.tsum_eq]
    refine hsum_norm.tsum_le_tsum (fun k => ?_) hexp_sum.summable
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, hdv]
    calc ‖PowerSeries.coeff (k + 1) a.val‖ / (k.factorial : ℝ) * (‖d‖ * v) ^ k
        ≤ (C * R ^ (k + 1)) / (k.factorial : ℝ) * (‖d‖ * v) ^ k := by gcongr; exact hbd (k + 1)
      _ = (C * R) * ((R * (‖d‖ * v)) ^ k / (k.factorial : ℝ)) := by rw [pow_succ', mul_pow]; ring
  calc ‖d‖ * ‖∑' k : ℕ, _‖ ≤ ‖d‖ * ((C * R) * Real.exp (R * (‖d‖ * v))) :=
        mul_le_mul_of_nonneg_left hdens (norm_nonneg d)
    _ = (‖d‖ * (C * R)) * Real.exp ((R * ‖d‖) * v) := by rw [← mul_assoc ‖d‖, ← mul_assoc R]

/-- Every `convMinor a` is `Good U d` on EVERY domain `U` and ray `d` (zero Stokes phenomenon!). -/
theorem convMinor_good (a : ConvergentPowerSeries) (U : Set ℂ) (d : ℂ) :
    (convMinor a).Good U d :=
  ⟨(convMinor_density_entire a).mono (Set.subset_univ U), convMinor_expType a d⟩

private lemma integrableOn_exp_neg_mul_pow_Ioi (k : ℕ) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun v : ℝ => Real.exp (-α * v) * v ^ k) (Ioi (0 : ℝ)) volume := by
  have hdom : IntegrableOn (fun v : ℝ => ((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (-(α / 2) * v))
      (Ioi (0 : ℝ)) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hdom.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow k)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv0.le k))]
    have hpow := Real.pow_div_factorial_le_exp (α / 2 * v) (by positivity) k
    have h1 : 0 < (α / 2) ^ k := pow_pos (by positivity) k
    have h2 : 0 < (k.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvk : v ^ k ≤ ((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (α / 2 * v) := by
      calc v ^ k ≤ (Real.exp (α / 2 * v) * (k.factorial : ℝ)) / (α / 2) ^ k :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc Real.exp (-α * v) * v ^ k
        ≤ Real.exp (-α * v) * (((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (α / 2 * v)) :=
          mul_le_mul_of_nonneg_left hvk (Real.exp_pos _).le
      _ = ((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (-(α / 2) * v) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

private lemma realLaplace_monomial_Ioi (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-α * v) * v ^ k = (k.factorial : ℝ) / α ^ (k + 1) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hcast : (fun v : ℝ => ((Real.exp (-α * v) * v ^ k : ℝ) : ℂ)) =
      fun v : ℝ => Complex.exp (-(α : ℂ) * (v : ℂ)) * (v : ℂ) ^ k := by
    funext v; push_cast; rfl
  rw [hcast, Minor.complexLaplace_monomial k (by simp [hα])]
  push_cast; rfl

/-- Exact Laplace transform value: `(convMinor a).value d p = evalConv a p⁻¹` eventually in `far d`. -/
theorem convMinor_value_eventually (a : ConvergentPowerSeries) (d : ℂ) :
    ∀ᶠ p in BorelStokesVandermonde.far d, (convMinor a).value d p = evalConv a p⁻¹ := by
  obtain ⟨C, R, hC, hR, hbd⟩ := a.property
  filter_upwards [eventually_bound_far d (R * ‖d‖)] with p hp
  have hpd_re : 0 < (p * d).re := lt_of_le_of_lt (by positivity) hp
  have hpd_ne : p * d ≠ 0 := fun h0 => by simp [h0] at hpd_re
  have hp_ne : p ≠ 0 := left_ne_zero_of_mul hpd_ne
  have hd_ne : d ≠ 0 := right_ne_zero_of_mul hpd_ne
  have hdn_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have hp_norm_gt : R < ‖p‖ := by
    have hre_le : (p * d).re ≤ ‖p * d‖ := Complex.re_le_norm (p * d)
    rw [norm_mul] at hre_le
    exact lt_of_mul_lt_mul_right (lt_of_lt_of_le hp hre_le) hdn_pos.le
  have hpinv_lt : ‖p⁻¹‖ < R⁻¹ := by
    rw [norm_inv]
    exact (inv_lt_inv₀ (norm_pos_iff.mpr hp_ne) hR).mpr hp_norm_gt
  let F : ℕ → ℝ → ℂ := fun k v =>
    (d ^ (k + 1) * (PowerSeries.coeff (k + 1) a.val / (k.factorial : ℂ))) *
      (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ k)
  have hF_int : ∀ k : ℕ, Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) := fun k => by
    refine Integrable.const_mul ?_ _
    refine (integrableOn_exp_neg_mul_pow_Ioi k hpd_re).mono' ?_ ?_
    · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.pow k)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := hv
      rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv0.le]
      have hre : (-(p * d) * (v : ℂ)).re = -(p * d).re * v := by simp [Complex.mul_re]; ring
      rw [hre]
  have hF_int_norm : ∀ k : ℕ,
      ∫ v in Ioi (0 : ℝ), ‖F k v‖ =
        ‖PowerSeries.coeff (k + 1) a.val‖ * (‖d‖ / (p * d).re) ^ (k + 1) := fun k => by
    have hpt : Set.EqOn (fun v : ℝ => ‖F k v‖)
        (fun v : ℝ => (‖d‖ ^ (k + 1) * (‖PowerSeries.coeff (k + 1) a.val‖ / (k.factorial : ℝ))) *
          (Real.exp (-(p * d).re * v) * v ^ k)) (Ioi (0 : ℝ)) := fun v hv => by
      have hv0 : 0 < v := hv
      dsimp only [F]
      rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_natCast, norm_mul, Complex.norm_exp,
        norm_pow, Complex.norm_real, Real.norm_of_nonneg hv0.le]
      have hre : (-(p * d) * (v : ℂ)).re = -(p * d).re * v := by simp [Complex.mul_re]; ring
      rw [hre]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      realLaplace_monomial_Ioi k hpd_re, div_pow]
    have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp [hfac]
  have hratio_lt : R * ‖d‖ / (p * d).re < 1 := (div_lt_one hpd_re).mpr hp
  have hF_sum : Summable fun k : ℕ => ∫ v in Ioi (0 : ℝ), ‖F k v‖ := by
    have hgeom : Summable fun k : ℕ => (C * (R * ‖d‖ / (p * d).re)) * (R * ‖d‖ / (p * d).re) ^ k :=
      (summable_geometric_of_lt_one (by positivity) hratio_lt).mul_left _
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) hgeom
    rw [hF_int_norm k]
    calc ‖PowerSeries.coeff (k + 1) a.val‖ * (‖d‖ / (p * d).re) ^ (k + 1)
        ≤ (C * R ^ (k + 1)) * (‖d‖ / (p * d).re) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (hbd (k + 1)) (by positivity)
      _ = C * (R * ‖d‖ / (p * d).re) ^ (k + 1) := by
          rw [mul_assoc, ← mul_pow, mul_div_assoc]
      _ = (C * (R * ‖d‖ / (p * d).re)) * (R * ‖d‖ / (p * d).re) ^ k := by rw [pow_succ']; ring
  have hF_tsum : ∀ v : ℝ, damped (p * d) (Minor.pull d (convMinor a).density) v = ∑' k : ℕ, F k v := by
    intro v
    unfold damped Minor.pull convMinor
    dsimp only
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    dsimp only [F]
    rw [mul_pow, pow_succ']; ring
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  unfold Minor.value complexLaplace
  have hfun_eq : (fun v : ℝ => damped (p * d) (Minor.pull d (convMinor a).density) v) =
      fun v : ℝ => ∑' k : ℕ, F k v := funext hF_tsum
  rw [hfun_eq, ← hswap]
  have hterm_val : ∀ k : ℕ, ∫ v in Ioi (0 : ℝ), F k v = PowerSeries.coeff (k + 1) a.val * p⁻¹ ^ (k + 1) := by
    intro k
    dsimp only [F]
    rw [integral_const_mul, Minor.complexLaplace_monomial k hpd_re, mul_pow, inv_pow]
    have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp [hfac, hp_ne, hd_ne]
  simp_rw [hterm_val]
  have hsum_eval : Summable fun n : ℕ => PowerSeries.coeff n a.val * p⁻¹ ^ n :=
    (evalConv_summable_norm a hC hR hbd hpinv_lt).of_norm
  have hsplit := hsum_eval.tsum_eq_zero_add
  simpa [convMinor, evalConv, pow_zero, mul_one] using hsplit.symm

/-! #### 2B. Coefficient Evaluation of `MvPolynomial` over `ℂ{w}` & Convergent Borel Transfer -/

/-- Formal evaluation of `Q ∈ ℂ{w}[Y_0, ..., Y_r]` at `(d_u^0 S, ..., d_u^r S)` in `ℂ[[w]]`. -/
@[expose] def formalEvalConv {r : ℕ} (S : PowerSeries ℂ)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) : PowerSeries ℂ :=
  MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => d_u^[j.val] S) Q

/-- Analytic evaluation of the `ℂ{w}` coefficients of `Q` at `z : ℂ`, yielding `ℂ[Y_0, ..., Y_r]`. -/
@[expose] def evalConvMvPoly {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (z : ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ α ∈ Q.support, MvPolynomial.monomial α (evalConv (Q.coeff α) z)

lemma evalConvMvPoly_coeff {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (z : ℂ) (α : Fin (r + 1) →₀ ℕ) :
    (evalConvMvPoly Q z).coeff α = evalConv (Q.coeff α) z := by
  classical
  unfold evalConvMvPoly
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ Q.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, evalConv_zero, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

lemma evalConvMvPoly_zero {r : ℕ} (z : ℂ) :
    evalConvMvPoly (0 : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) z = 0 := by
  ext α; simp [evalConvMvPoly_coeff, evalConv_zero]

lemma evalConvMvPoly_C {r : ℕ} (a : ConvergentPowerSeries) (z : ℂ) :
    evalConvMvPoly (MvPolynomial.C a : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) z =
      MvPolynomial.C (evalConv a z) := by
  ext α
  rw [evalConvMvPoly_coeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs
  · rfl
  · exact evalConv_zero z

lemma evalConvMvPoly_mul_X {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (j : Fin (r + 1)) (z : ℂ) :
    evalConvMvPoly (Q * MvPolynomial.X j) z = evalConvMvPoly Q z * MvPolynomial.X j := by
  classical
  ext α
  rw [evalConvMvPoly_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs
  · exact (evalConvMvPoly_coeff Q z _).symm
  · exact evalConv_zero z

lemma evalConvMvPoly_add_eventually {r : ℕ}
    (Q₁ Q₂ : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPoly (Q₁ + Q₂) (u : ℂ)⁻¹ =
        evalConvMvPoly Q₁ (u : ℂ)⁻¹ + evalConvMvPoly Q₂ (u : ℂ)⁻¹ := by
  classical
  let S := Q₁.support ∪ Q₂.support
  have hall : ∀ᶠ u : ℝ in atTop, ∀ α ∈ S,
      evalConv (Q₁.coeff α + Q₂.coeff α) (u : ℂ)⁻¹ =
        evalConv (Q₁.coeff α) (u : ℂ)⁻¹ + evalConv (Q₂.coeff α) (u : ℂ)⁻¹ :=
    (Filter.eventually_all_finset S).mpr fun α _ => evalConv_add_eventually (Q₁.coeff α) (Q₂.coeff α)
  filter_upwards [hall] with u hu
  ext α
  rw [evalConvMvPoly_coeff, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add,
    Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply,
    evalConvMvPoly_coeff, evalConvMvPoly_coeff]
  by_cases hα : α ∈ S
  · exact hu α hα
  · have h1 : α ∉ Q₁.support := fun h => hα (Finset.mem_union_left _ h)
    have h2 : α ∉ Q₂.support := fun h => hα (Finset.mem_union_right _ h)
    rw [MvPolynomial.notMem_support_iff.mp h1, MvPolynomial.notMem_support_iff.mp h2,
      add_zero, evalConv_zero, add_zero]

lemma evalConvMvPoly_smul_eventually {r : ℕ} (a : ConvergentPowerSeries)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPoly (a • Q) (u : ℂ)⁻¹ = evalConv a (u : ℂ)⁻¹ • evalConvMvPoly Q (u : ℂ)⁻¹ := by
  have hall : ∀ᶠ u : ℝ in atTop, ∀ α ∈ Q.support,
      evalConv (a * Q.coeff α) (u : ℂ)⁻¹ = evalConv a (u : ℂ)⁻¹ * evalConv (Q.coeff α) (u : ℂ)⁻¹ :=
    (Filter.eventually_all_finset Q.support).mpr fun α _ => evalConv_mul_eventually a (Q.coeff α)
  filter_upwards [hall] with u hu
  ext α
  rw [evalConvMvPoly_coeff, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
    evalConvMvPoly_coeff, smul_eq_mul, smul_eq_mul]
  by_cases hα : α ∈ Q.support
  · exact hu α hα
  · rw [MvPolynomial.notMem_support_iff.mp hα, mul_zero, evalConv_zero, mul_zero]

lemma evalConv_mul_natCast (a : ConvergentPowerSeries) (k : ℕ) (z : ℂ) :
    evalConv (a * (k : ConvergentPowerSeries)) z = evalConv a z * (k : ℂ) := by
  unfold evalConv
  rw [← tsum_mul_right]
  refine tsum_congr fun n => ?_
  have hcast : (a * (k : ConvergentPowerSeries)).val = a.val * PowerSeries.C (k : ℂ) := by
    change a.val * ((k : ConvergentPowerSeries) : PowerSeries ℂ) = a.val * PowerSeries.C (k : ℂ)
    simp
  rw [hcast, PowerSeries.coeff_mul_C]
  ring

lemma evalConvMvPoly_pderiv {r : ℕ} (j : Fin (r + 1))
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (z : ℂ) :
    evalConvMvPoly (MvPolynomial.pderiv j Q) z = MvPolynomial.pderiv j (evalConvMvPoly Q z) := by
  ext α
  rw [evalConvMvPoly_coeff, MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv,
    evalConvMvPoly_coeff]
  have hcast : ((α j : ConvergentPowerSeries) + 1) = (((α j + 1 : ℕ) : ConvergentPowerSeries)) := by
    push_cast; rfl
  have hcastC : ((α j : ℂ) + 1) = (((α j + 1 : ℕ) : ℂ)) := by push_cast; rfl
  rw [hcast, hcastC, evalConv_mul_natCast]

lemma HasAsympExp.sum_finset {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {S : ι → PowerSeries ℂ}
    (hf : ∀ i ∈ s, HasAsympExp (f i) (S i)) :
    HasAsympExp (fun u : ℝ => ∑ i ∈ s, f i u) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using HasAsympExp.const (0 : ℂ)
  | @insert a s ha ih =>
    have hfn : (fun u : ℝ => ∑ i ∈ insert a s, f i u) = fun u => f a u + ∑ i ∈ s, f i u := by
      funext u; exact Finset.sum_insert ha
    rw [hfn, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma HasAsympExp.pow_nat {f : ℝ → ℂ} {S : PowerSeries ℂ} (hf : HasAsympExp f S) (k : ℕ) :
    HasAsympExp (fun u : ℝ => f u ^ k) (S ^ k) := by
  induction k with
  | zero => simpa using HasAsympExp.const (1 : ℂ)
  | succ k ih =>
    have hfn : (fun u : ℝ => f u ^ (k + 1)) = fun u => f u ^ k * f u := by
      funext u; rw [pow_succ]
    rw [hfn, pow_succ]
    exact ih.mul hf

lemma HasAsympExp.prod_finset {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {S : ι → PowerSeries ℂ}
    (hf : ∀ i ∈ s, HasAsympExp (f i) (S i)) :
    HasAsympExp (fun u : ℝ => ∏ i ∈ s, f i u) (∏ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using HasAsympExp.const (1 : ℂ)
  | @insert a s ha ih =>
    have hfn : (fun u : ℝ => ∏ i ∈ insert a s, f i u) = fun u => f a u * ∏ i ∈ s, f i u := by
      funext u; exact Finset.prod_insert ha
    rw [hfn, Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- All-orders `1/u` asymptotic expansion of `eval (f · u) (evalConvMvPoly Q u⁻¹)`. -/
theorem HasAsympExp.mvPolynomial_evalConv {r : ℕ}
    {f : Fin (r + 1) → ℝ → ℂ} {S : Fin (r + 1) → PowerSeries ℂ}
    (hf : ∀ j : Fin (r + 1), HasAsympExp (f j) (S j))
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => f j u) (evalConvMvPoly Q (u : ℂ)⁻¹))
      (MvPolynomial.eval₂ toPS S Q) := by
  have hfn : (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => f j u)
        (evalConvMvPoly Q (u : ℂ)⁻¹)) =
      fun u : ℝ => ∑ α ∈ Q.support,
        evalConv (Q.coeff α) (u : ℂ)⁻¹ * ∏ j ∈ α.support, f j u ^ α j := by
    funext u
    unfold evalConvMvPoly
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.eval_monomial]
    rfl
  have hser : MvPolynomial.eval₂ toPS S Q =
      ∑ α ∈ Q.support, (Q.coeff α).val * ∏ j ∈ α.support, S j ^ α j := by
    rw [MvPolynomial.eval₂_eq]
    rfl
  rw [hfn, hser]
  refine HasAsympExp.sum_finset Q.support fun α _ => ?_
  exact (evalConv_hasAsympExp (Q.coeff α)).mul
    (HasAsympExp.prod_finset α.support fun j _ => HasAsympExp.pow_nat (hf j) (α j))

private inductive ConvBorelExpr where
  | conv (a : ConvergentPowerSeries)
  | leaf
  | add (e f : ConvBorelExpr)
  | mul (e f : ConvBorelExpr)
  | jet (e : ConvBorelExpr)

private def ConvBorelExpr.residual (a : Minor) : ConvBorelExpr → Minor
  | .conv c => convMinor c
  | .leaf => a
  | .add e f => (e.residual a).plus (f.residual a)
  | .mul e f => (e.residual a).times (f.residual a)
  | .jet e => (e.residual a).jet

private def ConvBorelExpr.eval (a : Minor) (d : ℂ) : ConvBorelExpr → ℂ → ℂ
  | .conv c => fun p => evalConv c p⁻¹
  | .leaf => a.value d
  | .add e f => fun p => e.eval a d p + f.eval a d p
  | .mul e f => fun p => e.eval a d p * f.eval a d p
  | .jet e => fun p => deriv (e.eval a d) p

private def ConvBorelExpr.ofBorel : BorelExpr → ConvBorelExpr
  | .const c => .conv (convC c)
  | .leaf => .leaf
  | .add e f => .add (ofBorel e) (ofBorel f)
  | .mul e f => .mul (ofBorel e) (ofBorel f)
  | .jet e => .jet (ofBorel e)

private lemma ConvBorelExpr.ofBorel_eval (e : BorelExpr) (a : Minor) (d : ℂ) :
    (ofBorel e).eval a d = e.eval a d := by
  induction e with
  | const c => funext p; simp [ofBorel, eval, BorelExpr.eval, evalConv_C]
  | leaf => rfl
  | add e f he hf => funext p; simp [ofBorel, eval, BorelExpr.eval, he, hf]
  | mul e f he hf => funext p; simp [ofBorel, eval, BorelExpr.eval, he, hf]
  | jet e he => funext p; simp [ofBorel, eval, BorelExpr.eval, he]

private lemma ConvBorelExpr.ofBorel_jetIter (j : ℕ) :
    ofBorel (Nat.iterate BorelExpr.jet j BorelExpr.leaf) = Nat.iterate .jet j .leaf := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ofBorel, ih]

private lemma ConvBorelExpr.represents (e : ConvBorelExpr) {U : Set ℂ} {d : ℂ} (hU : Domain U)
    (ray : ContainsRay U d) {a : Minor} (ha : a.Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[BorelStokesVandermonde.far d] (e.residual a).value d := by
  induction e with
  | conv c =>
    refine ⟨convMinor_good c U d, ?_⟩
    filter_upwards [convMinor_value_eventually c d] with p hp
    exact hp.symm
  | leaf => exact ⟨ha, .rfl⟩
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

private lemma ConvBorelExpr.exists_of_mvPoly {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∃ e : ConvBorelExpr,
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d →
        (e.residual a).toSeries = formalEvalConv a.toSeries Q) ∧
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d → 0 < d.re →
        ∀ᶠ u : ℝ in atTop,
          e.eval a d (u : ℂ) =
            MvPolynomial.eval
              (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => a.value d (t : ℂ)) u)
              (evalConvMvPoly Q (u : ℂ)⁻¹)) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    refine ⟨.conv c, fun _ _ _ _ _ _ => by simp [residual, formalEvalConv, convMinor_toSeries],
      fun _ _ _ _ _ _ _ => .of_forall fun u => by simp [eval, evalConvMvPoly_C]⟩
  | add Q₁ Q₂ h₁ h₂ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    obtain ⟨e₂, hs₂, he₂⟩ := h₂
    refine ⟨.add e₁ e₂, fun U d a hU ray ha => ?_, fun U d a hU ray ha hd => ?_⟩
    · have hg₁ := (e₁.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      have hg₂ := (e₂.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      rw [residual, Minor.toSeries_plus hg₁ hg₂, hs₁ U d a hU ray ha, hs₂ U d a hU ray ha,
        formalEvalConv, formalEvalConv, formalEvalConv, MvPolynomial.eval₂_add]
    · filter_upwards [he₁ U d a hU ray ha hd, he₂ U d a hU ray ha hd,
        evalConvMvPoly_add_eventually Q₁ Q₂] with u hu₁ hu₂ hadd
      simp only [eval, hu₁, hu₂, hadd, map_add]
  | mul_X Q₁ j h₁ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    let ej : ConvBorelExpr := Nat.iterate ConvBorelExpr.jet j.val ConvBorelExpr.leaf
    refine ⟨.mul e₁ ej, fun U d a hU ray ha => ?_, fun U d a hU ray ha hd => ?_⟩
    · have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
      have hg₁ := (e₁.represents hU ray ha).1.1 0 h0
      have hgj := (ej.represents hU ray ha).1.1 0 h0
      rw [residual, Minor.toSeries_times hg₁ hgj, hs₁ U d a hU ray ha]
      have hj_ser : ∀ k : ℕ, ((Nat.iterate ConvBorelExpr.jet k ConvBorelExpr.leaf).residual a).toSeries =
          d_u^[k] a.toSeries := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          have hgk := ((Nat.iterate ConvBorelExpr.jet k ConvBorelExpr.leaf).represents hU ray ha).1.1 0 h0
          rw [Function.iterate_succ_apply' ConvBorelExpr.jet k ConvBorelExpr.leaf,
            Function.iterate_succ_apply' d_u k a.toSeries]
          exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
      rw [hj_ser j.val, formalEvalConv, formalEvalConv, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    · have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU ray ha hd j.val).1
      filter_upwards [he₁ U d a hU ray ha hd, hjet_eq] with u hu₁ huj
      have heval_eq : ej.eval a d (u : ℂ) =
          (Nat.iterate BorelExpr.jet j.val BorelExpr.leaf).eval a d (u : ℂ) := by
        dsimp only [ej]; rw [← ofBorel_jetIter, ofBorel_eval]
      simp only [eval, evalConvMvPoly_mul_X, map_mul, MvPolynomial.eval_X]
      rw [heval_eq, hu₁, huj]

/-! #### 2C. Flanking Wedges, Lateral Abel Sums & `abelConv_conv_borel_transfer` -/

private def ε₀C {ψ ω res} (h : MeromorphicBorelData ψ ω res) : ℝ := min h.ε (ω 0 / 2)

private lemma ε₀C_pos {ψ ω res} (h : MeromorphicBorelData ψ ω res) : 0 < ε₀C h :=
  lt_min h.hε_pos (half_pos h.ω_pos)

private lemma ε₀C_lt_ω {ψ ω res} (h : MeromorphicBorelData ψ ω res) (m : ℕ) : ε₀C h < ω m :=
  lt_of_le_of_lt (min_le_right _ _)
    (lt_of_lt_of_le (half_lt_self h.ω_pos) (h.ω_mono.monotone (Nat.zero_le m)))

/-- Upper flanking ray `e^{i θ}` for `MeromorphicBorelData`. -/
@[expose] def dPlusC {ψ ω res} (h : MeromorphicBorelData ψ ω res) : ℂ :=
  Complex.exp (I * (h.θ : ℂ))

/-- Lower flanking ray `e^{-i θ}` for `MeromorphicBorelData`. -/
@[expose] def dMinusC {ψ ω res} (h : MeromorphicBorelData ψ ω res) : ℂ :=
  Complex.exp (I * ((-h.θ : ℝ) : ℂ))

private lemma dMinusC_eq {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    dMinusC h = Complex.exp (-I * (h.θ : ℂ)) := by
  unfold dMinusC; congr 1; push_cast; ring

private lemma dPlusC_re {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dPlusC h).re = Real.cos h.θ := by
  unfold dPlusC; rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re]

private lemma dPlusC_im {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dPlusC h).im = Real.sin h.θ := by
  unfold dPlusC; rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_im]

private lemma dMinusC_re {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dMinusC h).re = Real.cos h.θ := by
  unfold dMinusC
  rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

private lemma dMinusC_im {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dMinusC h).im = -Real.sin h.θ := by
  unfold dMinusC
  rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private lemma cos_pos_θC {ψ ω res} (h : MeromorphicBorelData ψ ω res) : 0 < Real.cos h.θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hθ₀_lt⟩

private lemma sin_pos_θC {ψ ω res} (h : MeromorphicBorelData ψ ω res) : 0 < Real.sin h.θ :=
  Real.sin_pos_of_pos_of_lt_pi h.hθ_pos (by linarith [h.hθ_lt, h.hθ₀_lt, Real.pi_pos])

private lemma tan_lt_tanC {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    Real.tan h.θ < Real.tan h.θ₀ :=
  Real.strictMonoOn_tan ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hθ₀_lt⟩
    ⟨by linarith [h.hθ_pos, h.hθ_lt, Real.pi_pos], h.hθ₀_lt⟩ h.hθ_lt

private def wedgePlusC (θ₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < Real.tan θ₀ * z.re}

private def wedgeMinusC (θ₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -(Real.tan θ₀ * z.re) < z.im}

private lemma wedgePlusC_domain {θ₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgePlusC θ₀ ε) := by
  refine ⟨Metric.isOpen_ball.union ?_, fun z hz t ht => ?_⟩
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re)))
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball, dist_zero_right] at hball ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · left; simpa [Metric.mem_ball] using hε
      · right
        refine ⟨by simp [Complex.mul_re]; exact mul_pos ht0 hre,
                by simp [Complex.mul_im]; exact mul_pos ht0 him, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero]
        nlinarith

private lemma wedgeMinusC_domain {θ₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgeMinusC θ₀ ε) := by
  refine ⟨Metric.isOpen_ball.union ?_, fun z hz t ht => ?_⟩
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt (continuous_const.mul Complex.continuous_re).neg Complex.continuous_im))
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball, dist_zero_right] at hball ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · left; simpa [Metric.mem_ball] using hε
      · right
        refine ⟨by simp [Complex.mul_re]; exact mul_pos ht0 hre,
                by simp [Complex.mul_im]; exact mul_neg_of_pos_of_neg ht0 him, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero]
        nlinarith

private lemma isPreconnected_of_starC {U : Set ℂ} (hU : Domain U) (h0 : (0 : ℂ) ∈ U) :
    IsPreconnected U := by
  refine isPreconnected_iff_subset_of_disjoint_closed.mpr fun s t hs ht hUst hst => ?_
  have hseg : ∀ z ∈ U, (z ∈ s ↔ (0 : ℂ) ∈ s) := fun z hz => by
    let γ : ℝ → ℂ := fun r => (r : ℂ) * z
    have hγ_cont : Continuous γ := Complex.continuous_ofReal.mul continuous_const
    have hγ_sub : γ '' Icc (0 : ℝ) 1 ⊆ U := by
      rintro w ⟨r, hr, rfl⟩; exact hU.star z hz r hr
    have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
      (isPreconnected_Icc).image γ hγ_cont.continuousOn
    have hsub_empty : (γ '' Icc (0 : ℝ) 1) ∩ (s ∩ t) = ∅ :=
      Set.subset_empty_iff.mp ((Set.inter_subset_inter_left _ hγ_sub).trans hst.subset)
    have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hconn s t hs ht
      (hγ_sub.trans hUst) hsub_empty
    have h0im : (0 : ℂ) ∈ γ '' Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [γ]⟩
    have hzim : z ∈ γ '' Icc (0 : ℝ) 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [γ]⟩
    rcases hsplit with hsub_s | hsub_t
    · exact ⟨fun _ => hsub_s h0im, fun _ => hsub_s hzim⟩
    · have h0t : (0 : ℂ) ∈ t := hsub_t h0im
      have hzt : z ∈ t := hsub_t hzim
      exact ⟨fun hzs => by have hm : z ∈ U ∩ (s ∩ t) := ⟨hz, hzs, hzt⟩; rw [hst] at hm; exact hm.elim,
             fun h0s => by have hm : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s, h0t⟩; rw [hst] at hm; exact hm.elim⟩
  rcases hUst h0 with h0s | h0t
  · left; intro z hz; exact (hseg z hz).mpr h0s
  · right; intro z hz
    rcases hUst hz with hzs | hzt
    · exfalso
      have h0s : (0 : ℂ) ∈ s := (hseg z hz).mp hzs
      have hm : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s, h0t⟩
      rw [hst] at hm; exact hm
    · exact hzt

private lemma wedgePlusC_containsRay {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    ContainsRay (wedgePlusC h.θ₀ (ε₀C h)) (dPlusC h) := fun v hv => by
  rcases eq_or_lt_of_le hv with rfl | hv0
  · left; simp [ε₀C_pos h]
  · right
    have hre : (dPlusC h * (v : ℂ)).re = Real.cos h.θ * v := by simp [dPlusC_re h, Complex.mul_re]
    have him : (dPlusC h * (v : ℂ)).im = Real.sin h.θ * v := by simp [dPlusC_im h, Complex.mul_im]
    refine ⟨by rw [hre]; exact mul_pos (cos_pos_θC h) hv0,
            by rw [him]; exact mul_pos (sin_pos_θC h) hv0, ?_⟩
    rw [hre, him]
    have htan : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θC h).ne']
    rw [htan]
    nlinarith [tan_lt_tanC h, mul_pos (cos_pos_θC h) hv0]

private lemma wedgeMinusC_containsRay {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    ContainsRay (wedgeMinusC h.θ₀ (ε₀C h)) (dMinusC h) := fun v hv => by
  rcases eq_or_lt_of_le hv with rfl | hv0
  · left; simp [ε₀C_pos h]
  · right
    have hre : (dMinusC h * (v : ℂ)).re = Real.cos h.θ * v := by simp [dMinusC_re h, Complex.mul_re]
    have him : (dMinusC h * (v : ℂ)).im = -(Real.sin h.θ * v) := by simp [dMinusC_im h, Complex.mul_im]
    refine ⟨by rw [hre]; exact mul_pos (cos_pos_θC h) hv0,
            by rw [him]; exact neg_lt_zero.mpr (mul_pos (sin_pos_θC h) hv0), ?_⟩
    rw [hre, him]
    have htan : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θC h).ne']
    rw [htan]
    nlinarith [tan_lt_tanC h, mul_pos (cos_pos_θC h) hv0]

private lemma wedgePlusC_subset_punctured {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    wedgePlusC h.θ₀ (ε₀C h) ⊆ puncturedWedge h.θ₀ h.ε ω := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left; rw [Metric.mem_ball] at hball ⊢; exact hball.trans_le (min_le_left _ _)
    · right; exact ⟨hre, by rw [abs_of_pos him]; exact hlt⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).le] at hball
      linarith [ε₀C_lt_ω h m]
    · simp at him

private lemma wedgeMinusC_subset_punctured {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    wedgeMinusC h.θ₀ (ε₀C h) ⊆ puncturedWedge h.θ₀ h.ε ω := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left; rw [Metric.mem_ball] at hball ⊢; exact hball.trans_le (min_le_left _ _)
    · right; exact ⟨hre, by rw [abs_of_neg him]; linarith⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).le] at hball
      linarith [ε₀C_lt_ω h m]
    · simp at him

/-- The Abel-convolution minor `⟨0, abelConv ψ⟩`. -/
@[expose] def aAbelC (ψ : ℂ → ℂ) : Minor := ⟨0, abelConv ψ⟩

private lemma aAbelC_toSeries (ψ : ℂ → ℂ) : (aAbelC ψ).toSeries = formalSeries (abelConv ψ) := rfl

private lemma aAbelC_good_plus {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (aAbelC ψ).Good (wedgePlusC h.θ₀ (ε₀C h)) (dPlusC h) :=
  ⟨abelConv_analyticOn (wedgePlusC_domain (ε₀C_pos h)) (h.analyticOn.mono (wedgePlusC_subset_punctured h)),
   abelConv_expType h.expType_plus⟩

private lemma aAbelC_good_minus {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (aAbelC ψ).Good (wedgeMinusC h.θ₀ (ε₀C h)) (dMinusC h) :=
  ⟨abelConv_analyticOn (wedgeMinusC_domain (ε₀C_pos h)) (h.analyticOn.mono (wedgeMinusC_subset_punctured h)),
   abelConv_expType (by rw [dMinusC_eq h]; exact h.expType_minus)⟩

private lemma analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroC {U : Set ℂ} {f : ℂ → ℂ}
    (hpre : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) : Set.EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz; simpa [smul_eq_mul] using hz
  have hdn : iteratedDeriv n f 0 = (n.factorial : ℂ) * g 0 := by
    rw [hloc.iteratedDeriv_eq n]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0 := analyticAt_id.pow n
    have hmul := iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ)) hpow_an.contDiffAt hg.contDiffAt
    rw [hmul]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ n) (0 : ℂ) * iteratedDeriv (n - i) g 0 =
          if i = n then (n.factorial : ℂ) * g 0 else 0 := fun i _ => by
      rw [iteratedDeriv_fun_pow_zero]
      split_ifs with hin
      · subst hin; simp [Nat.choose_self]
      · simp
    rw [Finset.sum_congr rfl hterm]; simp
  have hzero := hderiv n
  rw [hdn] at hzero
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) hzero

/-- **Convergent Borel–Laplace Transfer (`ℂ{w}` → Lateral Sums)**:
Any formal differential equation over `ConvergentPowerSeries` satisfied by `formalSeries (abelConv ψ)`
transfers identically to BOTH lateral Borel sums `g_pos` and `g_neg` as `u → +∞`. -/
theorem abelConv_conv_borel_transfer {ψ ω res} (h : MeromorphicBorelData ψ ω res)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries (abelConv ψ)) Q = 0) :
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (aAbelC ψ).value (dPlusC h) (t : ℂ)) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) ∧
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (aAbelC ψ).value (dMinusC h) (t : ℂ)) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) := by
  let Up := wedgePlusC h.θ₀ (ε₀C h)
  let Um := wedgeMinusC h.θ₀ (ε₀C h)
  have hUp_dom : Domain Up := wedgePlusC_domain (ε₀C_pos h)
  have hUm_dom : Domain Um := wedgeMinusC_domain (ε₀C_pos h)
  have hrayP : ContainsRay Up (dPlusC h) := wedgePlusC_containsRay h
  have hrayM : ContainsRay Um (dMinusC h) := wedgeMinusC_containsRay h
  have hgoodP : (aAbelC ψ).Good Up (dPlusC h) := aAbelC_good_plus h
  have hgoodM : (aAbelC ψ).Good Um (dMinusC h) := aAbelC_good_minus h
  have hreP : 0 < (dPlusC h).re := by rw [dPlusC_re h]; exact cos_pos_θC h
  have hreM : 0 < (dMinusC h).re := by rw [dMinusC_re h]; exact cos_pos_θC h
  obtain ⟨e, hs, he⟩ := ConvBorelExpr.exists_of_mvPoly Q
  have hres_series : (e.residual (aAbelC ψ)).toSeries = 0 := by
    rw [hs Up (dPlusC h) (aAbelC ψ) hUp_dom hrayP hgoodP, aAbelC_toSeries, hQ]
  have hatom : (e.residual (aAbelC ψ)).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series; simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual (aAbelC ψ)).density 0 = 0 := fun k => by
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series; simpa [Minor.toSeries] using this
  have h0P : (0 : ℂ) ∈ Up := by simpa using hrayP 0 le_rfl
  have h0M : (0 : ℂ) ∈ Um := by simpa using hrayM 0 le_rfl
  have hplus_dens : Set.EqOn (e.residual (aAbelC ψ)).density 0 Up :=
    analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroC (isPreconnected_of_starC hUp_dom h0P) h0P
      (e.represents hUp_dom hrayP hgoodP).1.1 hderiv_zero
  have hminus_dens : Set.EqOn (e.residual (aAbelC ψ)).density 0 Um :=
    analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroC (isPreconnected_of_starC hUm_dom h0M) h0M
      (e.represents hUm_dom hrayM hgoodM).1.1 hderiv_zero
  have ht_far : ∀ {d : ℂ}, 0 < d.re → Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far d) :=
    fun {d} hd => by
      rw [BorelStokesVandermonde.far, tendsto_comap_iff]
      have heq : ((fun p : ℂ => (p * d).re) ∘ fun u : ℝ => (u : ℂ)) = fun u : ℝ => u * d.re := by
        funext u; simp [Complex.mul_re]
      rw [heq]; exact tendsto_id.atTop_mul_const hd
  constructor
  · have hrep := (ht_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
    filter_upwards [hrep, he Up (dPlusC h) (aAbelC ψ) hUp_dom hrayP hgoodP hreP] with u hu_rep hu_ev
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hplus_dens (hrayP v hv.le)]
  · have hrep := (ht_far hreM).eventually (e.represents hUm_dom hrayM hgoodM).2
    filter_upwards [hrep, he Um (dMinusC h) (aAbelC ψ) hUm_dom hrayM hgoodM hreM] with u hu_rep hu_ev
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hminus_dens (hrayM v hv.le)]

/-! ### 3. Half-Integer Stokes Jump & Lowest-`w`-Order Vandermonde Descent over `ℂ{w}` -/

/-! #### 3A. Lateral Asymptotics & Half-Integer Branch-Point Stokes Jump on `aAbelC` -/

private lemma minor_value_hasAsympExpC (a : Minor) {U : Set ℂ} {d : ℂ}
    (hU : Domain U) (ray : ContainsRay U d) (ha : a.Good U d) (hd : 0 < d.re) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ))) (d_u^[j] a.toSeries) := by
  let ej : BorelExpr := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  obtain ⟨good_j, rep_j⟩ := ej.represents hU ray ha
  have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU ray ha hd j).1
  have hser_j : (ej.residual a).toSeries = d_u^[j] a.toSeries := by
    have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
    clear good_j rep_j hjet_eq
    induction j with
    | zero => rfl
    | succ k ih =>
      have hgk := ((Nat.iterate BorelExpr.jet k BorelExpr.leaf).represents hU ray ha).1.1 0 h0
      dsimp only [ej]
      rw [Function.iterate_succ_apply' BorelExpr.jet k BorelExpr.leaf,
        Function.iterate_succ_apply' d_u k a.toSeries]
      exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
  have ht_far : Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far d) := by
    rw [BorelStokesVandermonde.far, tendsto_comap_iff]
    have heq : ((fun p : ℂ => (p * d).re) ∘ fun u : ℝ => (u : ℂ)) = fun u : ℝ => u * d.re := by
      funext u; simp [Complex.mul_re]
    rw [heq]
    exact tendsto_id.atTop_mul_const hd
  intro M
  cases M with
  | zero =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU ray good_j hd 0
    refine ⟨C + ‖(ej.residual a).atom‖, ?_⟩
    filter_upwards [hC, hjet_eq, ht_far.eventually rep_j, eventually_ge_atTop (1 : ℝ)] with u hu hje hre hu1
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add, pow_one] at hu
    rw [← hje, hre]
    have h1 : ‖(ej.residual a).value d (u : ℂ)‖ ≤
        ‖(ej.residual a).value d (u : ℂ) - (ej.residual a).atom‖ + ‖(ej.residual a).atom‖ := by
      simpa [sub_add_cancel] using norm_add_le ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom) (ej.residual a).atom
    have hC0 : 0 ≤ C := by
      have hnn := norm_nonneg ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom)
      exact (div_nonneg_iff.mp (hnn.trans hu)).resolve_right (fun h => by linarith) |>.1
    have hCu : C / u ≤ C := by
      calc C / u ≤ C / 1 := div_le_div_of_nonneg_left hC0 zero_lt_one hu1
        _ = C := div_one C
    linarith
  | succ m =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU ray good_j hd m
    refine ⟨C, ?_⟩
    filter_upwards [hC, hjet_eq, ht_far.eventually rep_j] with u hu hje hre
    rw [← hje, hre]
    have hsum : ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (d_u^[j] a.toSeries) * ((u : ℂ)⁻¹ ^ k) =
        (ej.residual a).atom + ∑ k ∈ Finset.range m,
          iteratedDeriv k (ej.residual a).density 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
      rw [← hser_j, Finset.sum_range_succ']
      simp only [Minor.toSeries, PowerSeries.coeff_mk, pow_zero, mul_one, add_comm]
    rw [hsum]
    exact hu

private def halfRayDerivC (ψ : ℂ → ℂ) (d : ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in Ioi (0 : ℝ),
      (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
        (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ))

private lemma cpow_half_exp_mulC {σ t : ℝ} (hσ : |σ| < Real.pi / 2) (ht : 0 < t) :
    (Complex.exp (I * (σ : ℂ)) * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) =
      Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) := by
  have hne : Complex.exp (I * (σ : ℂ)) * (t : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr ht.ne')
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log (Complex.exp (I * (σ : ℂ)) * (t : ℂ)) = (Real.log t : ℂ) + I * (σ : ℂ) := by
    have hexp : Complex.exp ((Real.log t : ℂ) + I * (σ : ℂ)) = Complex.exp (I * (σ : ℂ)) * (t : ℂ) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ht, mul_comm]
    rw [← hexp, Complex.log_exp]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_zero, one_mul, zero_add]
      linarith [abs_lt.mp hσ, Real.pi_pos]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_zero, one_mul, zero_add]
      linarith [abs_lt.mp hσ, Real.pi_pos]
  rw [hlog, add_mul, Complex.exp_add, mul_comm]
  congr 1
  · congr 1; push_cast; ring
  · rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, Complex.ofReal_exp]
    congr 1; push_cast; ring

private lemma integrableOn_rpow_nat_add_half_mul_expC (j : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t)) (Ioi (0 : ℝ)) volume := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t)) (Ioc (0 : ℝ) 1) volume := by
    refine (integrableOn_const (C := (1 : ℝ)) (by simp : volume (Ioc (0 : ℝ) 1) ≠ ⊤)).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (Set.mem_Ioc.mp ht).1.ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (Real.exp_pos _).le)]
      have hrp : t ^ ((j : ℝ) + 1 / 2) ≤ 1 := Real.rpow_le_one ht0.le ht.2 (by positivity)
      have hexp : Real.exp (-r * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      simpa using mul_le_mul hrp hexp (Real.exp_pos _).le zero_le_one
  have h2 : IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t)) (Ioi (1 : ℝ)) volume := by
    refine ((integrableOn_exp_neg_mul_pow_Ioi (j + 1) hr).mono_set (Ioi_subset_Ioi zero_le_one)).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (lt_trans zero_lt_one ht).ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (Real.exp_pos _).le),
        mul_comm (Real.exp _)]
      have hrp : t ^ ((j : ℝ) + 1 / 2) ≤ t ^ (j + 1) := by
        calc t ^ ((j : ℝ) + 1 / 2) ≤ t ^ ((j + 1 : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le ht1 (by push_cast; linarith)
          _ = t ^ (j + 1) := Real.rpow_natCast t (j + 1)
      exact mul_le_mul_of_nonneg_right hrp (Real.exp_pos _).le
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1.union h2

private lemma halfRayDerivC_integrable {ψ : ℂ → ℂ} {σ : ℝ} (hσ : |σ| < Real.pi / 2)
    (hcont : ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0))
    {C D : ℝ} (hbd : ∀ t ≥ 0, ‖Minor.pull (Complex.exp (I * (σ : ℂ))) ψ t‖ ≤ C * Real.exp (D * t))
    (j : ℕ) {u : ℝ} (hu : D < u * Real.cos σ) :
    IntegrableOn (fun t : ℝ =>
      (-(Complex.exp (I * (σ : ℂ)) * (t : ℂ))) ^ j *
        Complex.exp (-(u : ℂ) * (Complex.exp (I * (σ : ℂ)) * (t : ℂ))) *
        Complex.exp (I * (σ : ℂ)) * (Complex.exp (I * (σ : ℂ)) * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) *
        ψ (Complex.exp (I * (σ : ℂ)) * (t : ℂ))) (Ioi (0 : ℝ)) volume := by
  let d : ℂ := Complex.exp (I * (σ : ℂ))
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.norm_exp_ofReal_mul_I σ
  have hd_re : d.re = Real.cos σ := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.exp_ofReal_mul_I_re σ
  have hdom : IntegrableOn (fun t : ℝ => C * (t ^ ((j : ℝ) + 1 / 2) * Real.exp (-(u * Real.cos σ - D) * t)))
      (Ioi (0 : ℝ)) volume :=
    (integrableOn_rpow_nat_add_half_mul_expC j (by linarith)).const_mul C
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have heq : EqOn (fun t : ℝ =>
        (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
          (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ)))
        (fun t : ℝ =>
          (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) *
            (Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ)) * Minor.pull d ψ t)
        (Ioi 0) := fun t ht => by
      dsimp only [d, Minor.pull]; rw [cpow_half_exp_mulC hσ ht]; ring
    refine ContinuousOn.congr ?_ heq
    exact (((((continuous_const.mul Complex.continuous_ofReal).neg.pow j).mul
      (Complex.continuous_exp.comp (continuous_const.mul (continuous_const.mul Complex.continuous_ofReal)))).mul
      (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt))).continuousOn).mul hcont
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hrewrite : (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
          (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ)) =
        (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) *
          Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * Minor.pull d ψ t := by
      dsimp only [d, Minor.pull]; rw [cpow_half_exp_mulC hσ ht0]; ring
    rw [hrewrite, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, hd_norm,
      one_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le, Complex.norm_exp,
      show I * ((σ / 2 : ℝ) : ℂ) = ((σ / 2 : ℝ) : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow]
    have hre : (-(u : ℂ) * (d * (t : ℂ))).re = -(u * Real.cos σ) * t := by
      simp [Complex.mul_re, hd_re]; ring
    rw [hre]
    have hpow : t ^ j * t ^ (1 / 2 : ℝ) = t ^ ((j : ℝ) + 1 / 2) := by
      rw [← Real.rpow_natCast t j, ← Real.rpow_add ht0]
    calc t ^ j * Real.exp (-(u * Real.cos σ) * t) * t ^ (1 / 2 : ℝ) * ‖Minor.pull d ψ t‖
        ≤ t ^ j * Real.exp (-(u * Real.cos σ) * t) * t ^ (1 / 2 : ℝ) * (C * Real.exp (D * t)) :=
          mul_le_mul_of_nonneg_left (hbd t ht0.le) (by positivity)
      _ = C * ((t ^ j * t ^ (1 / 2 : ℝ)) * (Real.exp (-(u * Real.cos σ) * t) * Real.exp (D * t))) := by ring
      _ = C * (t ^ ((j : ℝ) + 1 / 2) * Real.exp (-(u * Real.cos σ - D) * t)) := by
          rw [hpow, ← Real.exp_add]; congr 3; ring

private lemma hasDerivAt_halfRayDerivC {ψ : ℂ → ℂ} {σ : ℝ} (hσ : |σ| < Real.pi / 2)
    (hcont : ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0))
    {C D : ℝ} (hC : 0 ≤ C) (hbd : ∀ t ≥ 0, ‖Minor.pull (Complex.exp (I * (σ : ℂ))) ψ t‖ ≤ C * Real.exp (D * t))
    (k : ℕ) {u₀ : ℝ} (hu₀ : (D + 1) / Real.cos σ < u₀) :
    HasDerivAt (halfRayDerivC ψ (Complex.exp (I * (σ : ℂ))) k)
      (halfRayDerivC ψ (Complex.exp (I * (σ : ℂ))) (k + 1) u₀) u₀ := by
  let d : ℂ := Complex.exp (I * (σ : ℂ))
  have hcos : 0 < Real.cos σ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hσ)
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.norm_exp_ofReal_mul_I σ
  have hd_re : d.re = Real.cos σ := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.exp_ofReal_mul_I_re σ
  have hu₀_cos : D + 1 < u₀ * Real.cos σ := (div_lt_iff₀ hcos).mp hu₀
  let r₀ : ℝ := (D + 1 / 2) / Real.cos σ
  have hr₀_lt : r₀ < u₀ := by dsimp only [r₀]; rw [div_lt_iff₀ hcos]; linarith
  let s : Set ℝ := Ioi r₀
  have hs : s ∈ 𝓝 u₀ := Ioi_mem_nhds hr₀_lt
  let F : ℝ → ℝ → ℂ := fun u t =>
    (-(d * (t : ℂ))) ^ k * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
      (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ))
  let F' : ℝ → ℝ → ℂ := fun u t =>
    (-(d * (t : ℂ))) ^ (k + 1) * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
      (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ))
  let bound : ℝ → ℝ := fun t => C * (t ^ (((k + 1 : ℕ) : ℝ) + 1 / 2) * Real.exp (-(1 / 2 : ℝ) * t))
  have hF_meas : ∀ᶠ u in 𝓝 u₀, AEStronglyMeasurable (F u) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hs] with u hu
    have h1 : D + 1 / 2 < u * Real.cos σ := (div_lt_iff₀ hcos).mp hu
    exact (halfRayDerivC_integrable hσ hcont hbd k (by linarith)).aestronglyMeasurable
  have hF_int : Integrable (F u₀) (volume.restrict (Ioi (0 : ℝ))) :=
    halfRayDerivC_integrable hσ hcont hbd k (by linarith)
  have hF'_meas : AEStronglyMeasurable (F' u₀) (volume.restrict (Ioi (0 : ℝ))) :=
    (halfRayDerivC_integrable hσ hcont hbd (k + 1) (by linarith)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ u ∈ s, ‖F' u t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht u hu
    have ht0 : 0 < t := ht
    have hu_cos : D + 1 / 2 < u * Real.cos σ := (div_lt_iff₀ hcos).mp hu
    have hrew : F' u t = (-(d * (t : ℂ))) ^ (k + 1) * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) *
        Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * Minor.pull d ψ t := by
      dsimp only [F', d, Minor.pull]; rw [cpow_half_exp_mulC hσ ht0]; ring
    rw [hrew, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, hd_norm,
      one_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le, Complex.norm_exp,
      show I * ((σ / 2 : ℝ) : ℂ) = ((σ / 2 : ℝ) : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow]
    have hre : (-(u : ℂ) * (d * (t : ℂ))).re = -(u * Real.cos σ) * t := by
      simp [Complex.mul_re, hd_re]; ring
    rw [hre]
    have hpow : t ^ (k + 1) * t ^ (1 / 2 : ℝ) = t ^ (((k + 1 : ℕ) : ℝ) + 1 / 2) := by
      rw [← Real.rpow_natCast t (k + 1), ← Real.rpow_add ht0]
    have hexp_le : Real.exp (-(u * Real.cos σ) * t) * Real.exp (D * t) ≤ Real.exp (-(1 / 2 : ℝ) * t) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    calc t ^ (k + 1) * Real.exp (-(u * Real.cos σ) * t) * t ^ (1 / 2 : ℝ) * ‖Minor.pull d ψ t‖
        ≤ t ^ (k + 1) * Real.exp (-(u * Real.cos σ) * t) * t ^ (1 / 2 : ℝ) * (C * Real.exp (D * t)) :=
          mul_le_mul_of_nonneg_left (hbd t ht0.le) (by positivity)
      _ = C * ((t ^ (k + 1) * t ^ (1 / 2 : ℝ)) * (Real.exp (-(u * Real.cos σ) * t) * Real.exp (D * t))) := by ring
      _ ≤ C * (t ^ (((k + 1 : ℕ) : ℝ) + 1 / 2) * Real.exp (-(1 / 2 : ℝ) * t)) := by
          rw [hpow]; gcongr
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ u ∈ s, HasDerivAt (F · t) (F' u t) u := by
    filter_upwards with t u _
    have h1 : HasDerivAt (fun v : ℝ => Complex.exp (-(v : ℂ) * (d * (t : ℂ))))
        (Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * (-(d * (t : ℂ)))) u := by
      have hlin : HasDerivAt (fun v : ℝ => -(v : ℂ) * (d * (t : ℂ))) (-(d * (t : ℂ))) u := by
        simpa using ((hasDerivAt_id u).ofReal_comp.neg).mul_const (d * (t : ℂ))
      exact hlin.cexp
    have h2 := (((h1.const_mul ((-(d * (t : ℂ))) ^ k)).mul_const d).mul_const
      ((d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ))).mul_const (ψ (d * (t : ℂ)))
    exact h2.congr_deriv (by dsimp only [F']; rw [pow_succ]; ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    hbound ((integrableOn_rpow_nat_add_half_mul_expC (k + 1) (by norm_num)).const_mul C) hdiff).2.const_mul _

private lemma iteratedDeriv_and_contDiffAt_halfRayLaplaceC {ψ : ℂ → ℂ} {σ : ℝ} (hσ : |σ| < Real.pi / 2)
    (hcont : ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0))
    (hexp : ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ)) (j : ℕ) :
    (∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (halfRayLaplace ψ (Complex.exp (I * (σ : ℂ)))) u =
        halfRayDerivC ψ (Complex.exp (I * (σ : ℂ))) j u) ∧
    (∀ᶠ u : ℝ in atTop, ContDiffAt ℝ j (halfRayLaplace ψ (Complex.exp (I * (σ : ℂ)))) u) := by
  let d : ℂ := Complex.exp (I * (σ : ℂ))
  obtain ⟨C, D, hC, _, hbd⟩ := hexp
  let R₀ : ℝ := (D + 1) / Real.cos σ
  have hiter : ∀ k : ℕ, ∀ u : ℝ, R₀ < u →
      iteratedDeriv k (halfRayLaplace ψ d) u = halfRayDerivC ψ d k u := fun k => by
    induction k with
    | zero => intro u _; simp [halfRayLaplace, halfRayDerivC]
    | succ k ih =>
      intro u hu
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (halfRayLaplace ψ d) =ᶠ[𝓝 u] halfRayDerivC ψ d k :=
        Filter.eventually_of_mem (Ioi_mem_nhds hu) fun x hx => ih x hx
      rw [hev.deriv_eq, (hasDerivAt_halfRayDerivC hσ hcont hC hbd k hu).deriv]
  have hcd : ∀ m k : ℕ, ∀ u : ℝ, R₀ < u → ContDiffAt ℝ m (halfRayDerivC ψ d k) u := by
    intro m
    induction m with
    | zero =>
      intro k u hu
      exact contDiffAt_zero.mpr ⟨Ioi R₀, Ioi_mem_nhds hu,
        fun y hy => (hasDerivAt_halfRayDerivC hσ hcont hC hbd k hy).continuousAt.continuousWithinAt⟩
    | succ m ih =>
      intro k u hu
      rw [Nat.cast_add, Nat.cast_one, contDiffAt_succ_iff_hasFDerivAt]
      exact ⟨fun y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (halfRayDerivC ψ d (k + 1) y),
        ⟨Ioi R₀, Ioi_mem_nhds hu, fun y hy => (hasDerivAt_halfRayDerivC hσ hcont hC hbd k hy).hasFDerivAt⟩,
        (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)).contDiff.contDiffAt.comp u (ih (k + 1) u hu)⟩
  have h0eq : halfRayLaplace ψ d = halfRayDerivC ψ d 0 := by
    funext u; simp [halfRayLaplace, halfRayDerivC]
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_gt_atTop R₀] with u hu; exact hiter j u hu
  · rw [h0eq]; filter_upwards [eventually_gt_atTop R₀] with u hu; exact hcd j 0 u hu

private lemma continuousOn_cpow_half_re_nonnegC :
    ContinuousOn (fun z : ℂ => z ^ ((1 / 2 : ℝ) : ℂ)) {z : ℂ | 0 ≤ z.re} := by
  intro z hz
  change 0 ≤ z.re at hz
  by_cases hz0 : z = 0
  · subst hz0
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Complex.zero_cpow (by norm_num : ((1 / 2 : ℝ) : ℂ) ≠ 0),
      tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun w : ℂ => ‖w ^ ((1 / 2 : ℝ) : ℂ)‖) = fun w : ℂ => ‖w‖ ^ (1 / 2 : ℝ) := by
      funext w
      by_cases hw : w = 0
      · subst hw; simp
      · rw [Complex.norm_cpow_of_ne_zero hw]; simp
    rw [hnorm, show (0 : ℝ) = ‖(0 : ℂ)‖ ^ (1 / 2 : ℝ) by simp]
    exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.tendsto).comp
      continuous_norm.continuousAt.tendsto
  · have hslit : z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      rcases eq_or_lt_of_le hz with hre0 | hre_pos
      · right; intro him0; exact hz0 (Complex.ext hre0.symm him0)
      · exact Or.inl hre_pos
    exact ((hasDerivAt_id z).cpow_const hslit).continuousAt.continuousWithinAt

private lemma mem_closedTri_of_leC {R m x t : ℝ} (hx : x ∈ Icc 0 R) (ht : t ∈ Icc (-m) m) :
    (x : ℂ) * (1 + I * (t : ℂ)) ∈ closedTri R m := by
  have hre : ((x : ℂ) * (1 + I * (t : ℂ))).re = x := by simp [Complex.mul_re]
  have him : ((x : ℂ) * (1 + I * (t : ℂ))).im = x * t := by simp [Complex.mul_im]
  refine ⟨by rw [hre]; exact hx.1, by rw [hre]; exact hx.2, ?_⟩
  rw [hre, him, abs_mul, abs_of_nonneg hx.1, mul_comm m x]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) hx.1

private def TriBdIntC (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R

private lemma triBdIntC_of_continuousOn {F : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntC F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma triIntegral_addC {F G : ℂ → ℂ} {R m : ℝ} (hF : TriBdIntC F R m) (hG : TriBdIntC G R m) :
    triIntegral (fun z => F z + G z) R m = triIntegral F R m + triIntegral G R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (F ((x : ℂ) * (1 - I * (m : ℂ))) +
        G ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ))) +
        (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := funext fun _ => mul_add _ _ _
  have h3 : (fun x : ℝ => (1 + I * (m : ℂ)) * (F ((x : ℂ) * (1 + I * (m : ℂ))) +
        G ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))) +
        (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := funext fun _ => mul_add _ _ _
  rw [h1, h3, intervalIntegral.integral_add hF.1 hG.1,
    intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2 hG.2.2]; ring

private lemma triIntegral_const_mulC (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) := funext fun _ => by ring
  have h3 : (fun x : ℝ => (1 + I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) := funext fun _ => by ring
  rw [h1, h3]; simp_rw [intervalIntegral.integral_const_mul]; ring

private lemma triIntegral_sumC {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntC (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert a s ha ih =>
    have ha_int := hF a (Finset.mem_insert_self a s)
    have hs_int : ∀ i ∈ s, TriBdIntC (F i) R m := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hsum_int : TriBdIntC (fun z => ∑ i ∈ s, F i z) R m := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - I * (m : ℂ)) * ∑ i ∈ s, F i ((x : ℂ) * (1 - I * (m : ℂ)))) =
            ∑ i ∈ s, fun x : ℝ => (1 - I * (m : ℂ)) * F i ((x : ℂ) * (1 - I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun i hi => (hs_int i hi).1
      · have heq : (fun y : ℝ => ∑ i ∈ s, F i ((R : ℂ) + (y : ℂ) * I)) =
            ∑ i ∈ s, fun y : ℝ => F i ((R : ℂ) + (y : ℂ) * I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun i hi => (hs_int i hi).2.1
      · have heq : (fun x : ℝ => (1 + I * (m : ℂ)) * ∑ i ∈ s, F i ((x : ℂ) * (1 + I * (m : ℂ)))) =
            ∑ i ∈ s, fun x : ℝ => (1 + I * (m : ℂ)) * F i ((x : ℂ) * (1 + I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun i hi => (hs_int i hi).2.2
    have hpt : (fun z => ∑ i ∈ insert a s, F i z) = fun z => F a z + ∑ i ∈ s, F i z :=
      funext fun z => Finset.sum_insert ha
    rw [hpt, triIntegral_addC ha_int hsum_int, ih hs_int, Finset.sum_insert ha]

private lemma triIntegral_congrC {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ∀ x ∈ Icc 0 R, F ((x : ℂ) * (1 - I * (m : ℂ))) = G ((x : ℂ) * (1 - I * (m : ℂ))))
    (h2 : ∀ y ∈ Icc (-m * R) (m * R), F ((R : ℂ) + (y : ℂ) * I) = G ((R : ℂ) + (y : ℂ) * I))
    (h3 : ∀ x ∈ Icc 0 R, F ((x : ℂ) * (1 + I * (m : ℂ))) = G ((x : ℂ) * (1 + I * (m : ℂ)))) :
    triIntegral F R m = triIntegral G R m := by
  unfold triIntegral
  have hi1 := intervalIntegral.integral_congr (a := (0 : ℝ)) (b := R) (μ := volume)
    (f := fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ))))
    (g := fun x : ℝ => (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))))
    fun x hx => by dsimp only; rw [uIcc_of_le hR] at hx; rw [h1 x hx]
  have hi2 := intervalIntegral.integral_congr (a := -m * R) (b := m * R) (μ := volume)
    (f := fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I))
    (g := fun y : ℝ => G ((R : ℂ) + (y : ℂ) * I))
    fun y hy => by dsimp only; rw [uIcc_of_le (by nlinarith)] at hy; rw [h2 y hy]
  have hi3 := intervalIntegral.integral_congr (a := (0 : ℝ)) (b := R) (μ := volume)
    (f := fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))))
    (g := fun x : ℝ => (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))))
    fun x hx => by dsimp only; rw [uIcc_of_le hR] at hx; rw [h3 x hx]
  rw [hi1, hi2, hi3]

private lemma poleSub_analyticOn_cutOpenC {ψ ω res} (h : MeromorphicBorelData ψ ω res) (n : ℕ) :
    let Sn (z : ℂ) : ℂ := ∑ k ∈ Finset.range (n + 1), res k / (z - (ω k : ℂ))
    let Pset : Set ℂ := (fun k : ℕ => (ω k : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      by classical exact if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => ψ w - Sn w) else ψ z - Sn z
    AnalyticOnNhd ℂ ψn (borelWedge h.θ₀ (ε₀C h) ∩ {z : ℂ | z.re < ω (n + 1)}) := by
  classical
  intro Sn Pset ψn
  let Un : Set ℂ := borelWedge h.θ₀ (ε₀C h) ∩ {z : ℂ | z.re < ω (n + 1)}
  have hUn_open : IsOpen Un :=
    (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)))).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hP_fin : Pset.Finite := (Finset.finite_toSet (Finset.range (n + 1))).image _
  have hP_closed : IsClosed Pset := hP_fin.isClosed
  have hUn_sub : Un \ Pset ⊆ puncturedWedge h.θ₀ h.ε ω := by
    intro w ⟨hwU, hwP⟩
    refine ⟨?_, ?_⟩
    · rcases hwU.1 with hw_ball | hw_sec
      · left; exact Metric.ball_subset_ball (min_le_left _ _) hw_ball
      · right; exact hw_sec
    · rintro ⟨m, rfl⟩
      have hm_lt : ω m < ω (n + 1) := by simpa using hwU.2
      exact hwP ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr (h.ω_mono.lt_iff_lt.mp hm_lt)), rfl⟩
  have hSn_an : ∀ z ∈ Un \ Pset, AnalyticAt ℂ Sn z := fun z hz =>
    Finset.analyticAt_fun_sum _ fun m hm =>
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) fun h0 =>
        hz.2 ⟨m, Finset.mem_coe.mpr hm, (sub_eq_zero.mp h0).symm⟩
  intro z hzU
  by_cases hzP : z ∈ Pset
  · obtain ⟨k, hk_mem, rfl⟩ := hzP
    have hk : k < n + 1 := Finset.mem_range.mp hk_mem
    let hkFun : ℂ → ℂ := Function.update (fun ζ => (ζ - (ω k : ℂ)) * ψ ζ) (ω k : ℂ) (res k)
    let Qk : Set ℂ := Pset \ {(ω k : ℂ)}
    have hQk_closed : IsClosed Qk := (hP_fin.subset Set.sdiff_subset).isClosed
    let Vk : Set ℂ := Un \ Qk
    have hVk_open : IsOpen Vk := hUn_open.sdiff hQk_closed
    have hwk_Vk : (ω k : ℂ) ∈ Vk := ⟨hzU, fun hmem => hmem.2 rfl⟩
    have hmem_punc : Vk \ {(ω k : ℂ)} ∈ 𝓝[≠] (ω k : ℂ) := by
      rw [Set.sdiff_eq, inter_comm]
      exact inter_mem_nhdsWithin _ (hVk_open.mem_nhds hwk_Vk)
    have hhk_diff_punc : ∀ᶠ w in 𝓝[≠] (ω k : ℂ), DifferentiableAt ℂ hkFun w := by
      filter_upwards [hmem_punc] with w hw
      have hsub_open : Vk \ {(ω k : ℂ)} ⊆ Un \ Pset := fun ζ hζ =>
        ⟨hζ.1.1, fun hP => hζ.2 (by by_contra hne; exact hζ.1.2 ⟨hP, hne⟩)⟩
      have hψ_an : AnalyticAt ℂ ψ w := h.analyticOn w (hUn_sub (hsub_open hw))
      have hdiff_mul : DifferentiableAt ℂ (fun ζ => (ζ - (ω k : ℂ)) * ψ ζ) w :=
        (differentiableAt_id.sub_const _).mul hψ_an.differentiableAt
      have heq : hkFun =ᶠ[𝓝 w] fun ζ => (ζ - (ω k : ℂ)) * ψ ζ := by
        filter_upwards [isOpen_ne.mem_nhds hw.2] with ζ hζ
        exact Function.update_of_ne hζ _ _
      exact hdiff_mul.congr_of_eventuallyEq heq
    have hhk_an : AnalyticAt ℂ hkFun (ω k : ℂ) :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        hhk_diff_punc (continuousAt_update_same.mpr (h.simple_pole k))
    obtain ⟨ρ, hρ_pos, hρ_diff⟩ := Metric.eventually_nhds_iff.mp hhk_an.eventually_analyticAt
    have hgk_an : AnalyticAt ℂ (dslope hkFun (ω k : ℂ)) (ω k : ℂ) :=
      ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds _ hρ_pos)).mpr
        (fun w hw => (hρ_diff (Metric.mem_ball.mp hw)).differentiableAt.differentiableWithinAt)).analyticAt
        (Metric.ball_mem_nhds _ hρ_pos)
    let Gk (w : ℂ) : ℂ :=
      dslope hkFun (ω k : ℂ) w - ∑ m ∈ (Finset.range (n + 1)).erase k, res m / (w - (ω m : ℂ))
    have hGk_an : AnalyticAt ℂ Gk (ω k : ℂ) :=
      hgk_an.sub (Finset.analyticAt_fun_sum _ fun m hm =>
        analyticAt_const.div (analyticAt_id.sub analyticAt_const) fun h0 =>
          h.ω_mono.injective.ne (Finset.mem_erase.mp hm).1.symm (by exact_mod_cast sub_eq_zero.mp h0))
    have hGk_eq_punc : ∀ᶠ w in 𝓝[≠] (ω k : ℂ), ψ w - Sn w = Gk w := by
      filter_upwards [hmem_punc] with w hw
      have hw_ne : w ≠ (ω k : ℂ) := hw.2
      have hsub_ne : w - (ω k : ℂ) ≠ 0 := sub_ne_zero.mpr hw_ne
      have hslope_eq : dslope hkFun (ω k : ℂ) w = ψ w - res k / (w - (ω k : ℂ)) := by
        rw [dslope_of_ne hkFun hw_ne, slope_def_field]
        dsimp only [hkFun]
        rw [Function.update_of_ne hw_ne, Function.update_self]
        field_simp [hsub_ne]
      have hsum_split : Sn w = res k / (w - (ω k : ℂ)) +
          ∑ m ∈ (Finset.range (n + 1)).erase k, res m / (w - (ω m : ℂ)) := by
        dsimp only [Sn]
        rw [← Finset.add_sum_erase (Finset.range (n + 1)) (fun m => res m / (w - (ω m : ℂ)))
          (Finset.mem_range.mpr hk)]
      dsimp only [Gk]; rw [hslope_eq, hsum_split]; ring
    have hlim_eq : Filter.limUnder (𝓝[≠] (ω k : ℂ)) (fun w => ψ w - Sn w) = Gk (ω k : ℂ) :=
      (hGk_an.continuousAt.continuousWithinAt.tendsto.congr' (hGk_eq_punc.mono fun _ => Eq.symm)).limUnder_eq
    have hψ_loc : ψn =ᶠ[𝓝 (ω k : ℂ)] Gk := by
      have hmem_nhds : Vk ∩ {w : ℂ | w ≠ (ω k : ℂ) → ψ w - Sn w = Gk w} ∈ 𝓝 (ω k : ℂ) :=
        inter_mem (hVk_open.mem_nhds hwk_Vk) (eventually_nhdsWithin_iff.mp hGk_eq_punc)
      filter_upwards [hmem_nhds] with w ⟨hwVk, hw_imp⟩
      by_cases hwk : w = (ω k : ℂ)
      · subst hwk
        have hmemP : (ω k : ℂ) ∈ Pset := ⟨k, Finset.mem_coe.mpr (Finset.mem_range.mpr hk), rfl⟩
        dsimp only [ψn]; rw [ite_eq_left_iff.mpr (fun hnot => absurd hmemP hnot), hlim_eq]
      · have hw_not_P : w ∉ Pset := fun hP => hwVk.2 ⟨hP, hwk⟩
        dsimp only [ψn]; rw [ite_eq_right_iff.mpr (fun hmem => absurd hmem hw_not_P)]
        exact hw_imp hwk
    exact hGk_an.congr hψ_loc.symm
  · have hopen : IsOpen (Un \ Pset) := hUn_open.sdiff hP_closed
    have hdiff_an : AnalyticAt ℂ (fun w => ψ w - Sn w) z :=
      (h.analyticOn z (hUn_sub ⟨hzU, hzP⟩)).sub (hSn_an z ⟨hzU, hzP⟩)
    have heq : ψn =ᶠ[𝓝 z] fun w => ψ w - Sn w := by
      filter_upwards [hopen.mem_nhds ⟨hzU, hzP⟩] with w hw
      dsimp only [ψn]; exact ite_eq_right_iff.mpr (fun hmemP => absurd hmemP hw.2)
    exact hdiff_an.congr heq.symm

private lemma halfRayDeriv_stokes_jumpC {ψ ω res} (h : MeromorphicBorelData ψ ω res) (n j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖halfRayDerivC ψ (dMinusC h) j u - halfRayDerivC ψ (dPlusC h) j u -
        ∑ k ∈ Finset.range (n + 1),
          halfStokesCoeff ω res k * (-(ω k : ℂ)) ^ j * Complex.exp (-(ω k : ℂ) * (u : ℂ))‖ ≤
        C * Real.exp (-((ω n + ω (n + 1)) / 2) * u) := by
  classical
  let R : ℝ := (ω n + ω (n + 1)) / 2
  let mθ : ℝ := Real.tan h.θ
  let v₀ : ℝ := R / Real.cos h.θ
  have hω_pos : ∀ k : ℕ, 0 < ω k := fun k => lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le k))
  have hω_lt_R : ∀ k ≤ n, ω k < R := fun k hk => by
    have h1 : ω k ≤ ω n := h.ω_mono.monotone hk
    have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
    dsimp only [R]; linarith
  have hR_lt_ω : ∀ k, n + 1 ≤ k → R < ω k := fun k hk => by
    have h1 : ω (n + 1) ≤ ω k := h.ω_mono.monotone hk
    have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
    dsimp only [R]; linarith
  have hR_pos : 0 < R := lt_trans (hω_pos 0) (hω_lt_R 0 (Nat.zero_le n))
  have hcos : 0 < Real.cos h.θ := cos_pos_θC h
  have hm_pos : 0 < mθ := Real.tan_pos_of_pos_of_lt_pi_div_two h.hθ_pos (lt_trans h.hθ_lt h.hθ₀_lt)
  have hv₀_pos : 0 < v₀ := div_pos hR_pos hcos
  have hθ_abs : |h.θ| < Real.pi / 2 := abs_lt.mpr ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hθ₀_lt⟩
  have hnegθ_abs : |-h.θ| < Real.pi / 2 := by simpa [abs_neg] using hθ_abs
  have h_avoid :
      (∀ x : ℝ, ∀ k : ℕ, (x : ℂ) * (1 - I * (mθ : ℂ)) ≠ (ω k : ℂ)) ∧
      (∀ x : ℝ, ∀ k : ℕ, (x : ℂ) * (1 + I * (mθ : ℂ)) ≠ (ω k : ℂ)) ∧
      (∀ y : ℝ, ∀ k : ℕ, (R : ℂ) + (y : ℂ) * I ≠ (ω k : ℂ)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x k h0
      have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * (-mθ) = 0)).resolve_right (neg_ne_zero.mpr hm_pos.ne')
      subst hx0
      have hre := congrArg Complex.re h0
      simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
      linarith [hω_pos k]
    · intro x k h0
      have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * mθ = 0)).resolve_right hm_pos.ne'
      subst hx0
      have hre := congrArg Complex.re h0
      simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
      linarith [hω_pos k]
    · intro y k h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, Complex.ofReal_im, sub_zero, add_zero] at hre
      rcases le_or_gt k n with hkn | hnk
      · exact (hω_lt_R k hkn).ne hre.symm
      · exact (hR_lt_ω k hnk).ne hre
  let pref (u : ℝ) (z : ℂ) : ℂ :=
    ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * (-z) ^ j * Complex.exp (-(u : ℂ) * z) * z ^ ((1 / 2 : ℝ) : ℂ)
  let G (u : ℝ) (z : ℂ) : ℂ := pref u z * ψ z
  have htri_G : ∀ u : ℝ,
      triIntegral (G u) R mθ =
        ∑ k ∈ Finset.range (n + 1),
          halfStokesCoeff ω res k * (-(ω k : ℂ)) ^ j * Complex.exp (-(ω k : ℂ) * (u : ℂ)) := by
    intro u
    let Sn (z : ℂ) : ℂ := ∑ k ∈ Finset.range (n + 1), res k / (z - (ω k : ℂ))
    let Pset : Set ℂ := (fun k : ℕ => (ω k : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => ψ w - Sn w) else ψ z - Sn z
    let Un : Set ℂ := borelWedge h.θ₀ (ε₀C h) ∩ {z : ℂ | z.re < ω (n + 1)}
    have hUn_open : IsOpen Un :=
      (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im)
          (continuous_const.mul Complex.continuous_re)))).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hψn_an : AnalyticOnNhd ℂ ψn Un := poleSub_analyticOn_cutOpenC h n
    have htri_sub_Un : closedTri R mθ ⊆ Un := by
      intro z hz
      refine ⟨?_, lt_of_le_of_lt hz.2.1 (hR_lt_ω (n + 1) le_rfl)⟩
      rcases eq_or_lt_of_le hz.1 with hre0 | hre_pos
      · left
        have him0 : z.im = 0 := abs_nonpos_iff.mp (by simpa [← hre0] using hz.2.2)
        have hz0 : z = 0 := Complex.ext hre0.symm him0
        simpa [hz0, Metric.mem_ball, dist_zero_right] using ε₀C_pos h
      · right
        exact ⟨hre_pos, lt_of_le_of_lt hz.2.2 (mul_lt_mul_of_pos_right (tan_lt_tanC h) hre_pos)⟩
    have hpref_cont : ContinuousOn (pref u) (closedTri R mθ) := by
      have hsub_re : closedTri R mθ ⊆ {z : ℂ | 0 ≤ z.re} := fun z hz => hz.1
      exact (((continuousOn_const.mul (continuous_id.neg.pow j).continuousOn).mul
        (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (continuousOn_cpow_half_re_nonnegC.mono hsub_re))
    have hpref_diff_slit : DifferentiableOn ℂ (pref u) Complex.slitPlane := by
      intro z hz
      have hcp : DifferentiableAt ℂ (fun w : ℂ => w ^ ((1 / 2 : ℝ) : ℂ)) z :=
        ((hasDerivAt_id z).cpow_const hz).differentiableAt
      exact ((((differentiableAt_const _).mul (differentiableAt_id.neg.pow j)).mul
        ((differentiableAt_const _).mul differentiableAt_id).cexp).mul hcp).differentiableWithinAt
    have hpref_an_slit : AnalyticOnNhd ℂ (pref u) Complex.slitPlane :=
      hpref_diff_slit.analyticOnNhd Complex.isOpen_slitPlane
    have htri_ψn : triIntegral (fun z => pref u z * ψn z) R mθ = 0 :=
      triIntegral_eq_zero_of_analyticOn_pos hR_pos hm_pos (hUn_open.inter Complex.isOpen_slitPlane)
        (fun z hz => ⟨htri_sub_Un hz.1, Complex.mem_slitPlane_iff.mpr (Or.inl hz.2)⟩)
        (fun z hz => (hpref_an_slit z hz.2).mul (hψn_an z hz.1))
        (hpref_cont.mul (hψn_an.continuousOn.mono htri_sub_Un))
    let termK (k : ℕ) (z : ℂ) : ℂ := pref u z * (res k / (z - (ω k : ℂ)))
    have h_pole_term : ∀ k ∈ Finset.range (n + 1),
        triIntegral (termK k) R mθ =
          halfStokesCoeff ω res k * (-(ω k : ℂ)) ^ j * Complex.exp (-(ω k : ℂ) * (u : ℂ)) := by
      intro k hk
      have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      let gk (z : ℂ) : ℂ := res k * pref u z
      have hωk_slit : (ω k : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [hω_pos k]))
      have hgk_diff_slit : DifferentiableOn ℂ gk Complex.slitPlane :=
        (differentiableOn_const (res k)).mul hpref_diff_slit
      have hslope_an_slit : AnalyticOnNhd ℂ (dslope gk (ω k : ℂ)) Complex.slitPlane :=
        ((Complex.differentiableOn_dslope (Complex.isOpen_slitPlane.mem_nhds hωk_slit)).mpr
          hgk_diff_slit).analyticOnNhd Complex.isOpen_slitPlane
      have hslope_cont_tri : ContinuousOn (dslope gk (ω k : ℂ)) (closedTri R mθ) := by
        intro z hz
        by_cases hz0 : z = 0
        · subst hz0
          have hne0 : (0 : ℂ) ≠ (ω k : ℂ) := fun h0 => (hω_pos k).ne' (by exact_mod_cast h0.symm)
          have hsub_cont : ContinuousWithinAt (fun w : ℂ => (w - (ω k : ℂ))⁻¹ * (gk w - gk (ω k : ℂ)))
              (closedTri R mθ) 0 := by
            refine ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hne0)).continuousWithinAt.mul ?_
            exact ((continuousOn_const.mul hpref_cont) 0 hz).sub continuousWithinAt_const
          refine hsub_cont.congr_of_eventuallyEq ?_ (by rw [dslope_of_ne gk hne0, slope_def_field]; ring)
          filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hne0)] with w hw
          rw [dslope_of_ne gk hw, slope_def_field]; ring
        · have hslit : z ∈ Complex.slitPlane := by
            rw [Complex.mem_slitPlane_iff]
            rcases eq_or_lt_of_le hz.1 with hre0 | hre_pos
            · right; intro him0; exact hz0 (Complex.ext hre0.symm him0)
            · exact Or.inl hre_pos
          exact (hslope_an_slit z hslit).continuousAt.continuousWithinAt
      have htri_slope : triIntegral (dslope gk (ω k : ℂ)) R mθ = 0 :=
        triIntegral_eq_zero_of_analyticOn_pos hR_pos hm_pos Complex.isOpen_slitPlane
          (fun z hz => Complex.mem_slitPlane_iff.mpr (Or.inl hz.2))
          hslope_an_slit hslope_cont_tri
      have htri_inv : triIntegral (fun z => gk (ω k : ℂ) * (z - (ω k : ℂ))⁻¹) R mθ =
          gk (ω k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        rw [triIntegral_const_mulC, triIntegral_inv_sub (hω_pos k) (hω_lt_R k hk_le) hm_pos]
      have h_slope_int : TriBdIntC (dslope gk (ω k : ℂ)) R mθ := by
        refine triBdIntC_of_continuousOn hR_pos.le hm_pos.le
          (hslope_cont_tri.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx => ?_)
          (hslope_cont_tri.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
            fun y hy => ⟨by simp [hR_pos.le], by simp, by
              rw [show -mθ * R = -(mθ * R) by ring] at hy; simpa [R, mθ] using abs_le.mpr hy⟩)
          (hslope_cont_tri.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx =>
            mem_closedTri_of_leC hx ⟨by linarith, le_rfl⟩)
        have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by push_cast; ring
        rw [heq]; exact mem_closedTri_of_leC hx ⟨le_rfl, by linarith⟩
      have h_inv_int : TriBdIntC (fun z => gk (ω k : ℂ) * (z - (ω k : ℂ))⁻¹) R mθ :=
        triBdIntC_of_continuousOn hR_pos.le hm_pos.le
          (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀
            ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const)
            fun x h0 => h_avoid.1 x k (sub_eq_zero.mp h0))))
          (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀
            ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const)
            fun y h0 => h_avoid.2.2 y k (sub_eq_zero.mp h0))))
          (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀
            ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const)
            fun x h0 => h_avoid.2.1 x k (sub_eq_zero.mp h0))))
      have h_pt : ∀ z : ℂ, z ≠ (ω k : ℂ) →
          termK k z = dslope gk (ω k : ℂ) z + gk (ω k : ℂ) * (z - (ω k : ℂ))⁻¹ := fun z hz => by
        have hsub : z - (ω k : ℂ) ≠ 0 := sub_ne_zero.mpr hz
        rw [dslope_of_ne gk hz, slope_def_field]; dsimp only [termK, gk]; field_simp [hsub]; ring
      rw [triIntegral_congrC (G := fun z => dslope gk (ω k : ℂ) z + gk (ω k : ℂ) * (z - (ω k : ℂ))⁻¹)
            hR_pos.le hm_pos.le
            (fun x _ => h_pt _ (h_avoid.1 x k))
            (fun y _ => h_pt _ (h_avoid.2.2 y k))
            (fun x _ => h_pt _ (h_avoid.2.1 x k)),
          triIntegral_addC h_slope_int h_inv_int, htri_slope, zero_add, htri_inv]
      dsimp only [gk, pref, halfStokesCoeff]
      have hcpow : ((ω k : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) = ((Real.sqrt (ω k) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_cpow (hω_pos k).le, ← Real.sqrt_eq_rpow]
      rw [hcpow]
      have hpi_sqrt : ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * ((Real.sqrt (ω k) : ℝ) : ℂ) * (Real.pi : ℂ) =
          ((Real.sqrt (Real.pi * ω k) : ℝ) : ℂ) := by
        rw [Real.sqrt_mul Real.pi_pos.le, Complex.ofReal_mul]
        have hsq : (Real.pi : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
        have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
        rw [hsq]; field_simp [hsp]
      calc res k * (((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * (-(ω k : ℂ)) ^ j *
              Complex.exp (-(u : ℂ) * (ω k : ℂ)) * ((Real.sqrt (ω k) : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) * I)
          = 2 * I * (((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * ((Real.sqrt (ω k) : ℝ) : ℂ) * (Real.pi : ℂ)) *
              res k * (-(ω k : ℂ)) ^ j * Complex.exp (-(ω k : ℂ) * (u : ℂ)) := by
                rw [show -(u : ℂ) * (ω k : ℂ) = -(ω k : ℂ) * (u : ℂ) by ring]; ring
        _ = 2 * I * ((Real.sqrt (Real.pi * ω k) : ℝ) : ℂ) * res k *
              (-(ω k : ℂ)) ^ j * Complex.exp (-(ω k : ℂ) * (u : ℂ)) := by rw [hpi_sqrt]
    have h_Fψ_int : TriBdIntC (fun z => pref u z * ψn z) R mθ := by
      have hcont_all : ContinuousOn (fun z => pref u z * ψn z) (closedTri R mθ) :=
        hpref_cont.mul (hψn_an.continuousOn.mono htri_sub_Un)
      refine triBdIntC_of_continuousOn hR_pos.le hm_pos.le
        (hcont_all.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx => ?_)
        (hcont_all.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
          fun y hy => ⟨by simp [hR_pos.le], by simp, by
            rw [show -mθ * R = -(mθ * R) by ring] at hy; simpa [R, mθ] using abs_le.mpr hy⟩)
        (hcont_all.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx =>
          mem_closedTri_of_leC hx ⟨by linarith, le_rfl⟩)
      have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by push_cast; ring
      rw [heq]; exact mem_closedTri_of_leC hx ⟨le_rfl, by linarith⟩
    have h_term_int : ∀ k ∈ Finset.range (n + 1), TriBdIntC (termK k) R mθ := fun k _ => by
      refine triBdIntC_of_continuousOn hR_pos.le hm_pos.le
        ((hpref_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx => ?_).mul
          (Continuous.continuousOn (continuous_const.div
            ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const)
            fun x h0 => h_avoid.1 x k (sub_eq_zero.mp h0))))
        ((hpref_cont.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
          fun y hy => ⟨by simp [hR_pos.le], by simp, by
            rw [show -mθ * R = -(mθ * R) by ring] at hy; simpa [R, mθ] using abs_le.mpr hy⟩).mul
          (Continuous.continuousOn (continuous_const.div
            ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const)
            fun y h0 => h_avoid.2.2 y k (sub_eq_zero.mp h0))))
        ((hpref_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx =>
          mem_closedTri_of_leC hx ⟨by linarith, le_rfl⟩).mul
          (Continuous.continuousOn (continuous_const.div
            ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const)
            fun x h0 => h_avoid.2.1 x k (sub_eq_zero.mp h0))))
      have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by push_cast; ring
      dsimp only [Pi.mul_apply]; rw [heq]; exact mem_closedTri_of_leC hx ⟨le_rfl, by linarith⟩
    have h_sum_int : TriBdIntC (fun z => ∑ k ∈ Finset.range (n + 1), termK k z) R mθ := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) * ∑ k ∈ Finset.range (n + 1), termK k ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
            ∑ k ∈ Finset.range (n + 1), fun x : ℝ => (1 - I * (mθ : ℂ)) * termK k ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun k hk => (h_term_int k hk).1
      · have heq : (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), termK k ((R : ℂ) + (y : ℂ) * I)) =
            ∑ k ∈ Finset.range (n + 1), fun y : ℝ => termK k ((R : ℂ) + (y : ℂ) * I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun k hk => (h_term_int k hk).2.1
      · have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) * ∑ k ∈ Finset.range (n + 1), termK k ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
            ∑ k ∈ Finset.range (n + 1), fun x : ℝ => (1 + I * (mθ : ℂ)) * termK k ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun k hk => (h_term_int k hk).2.2
    have h_pt_G : ∀ z : ℂ, z ∉ Pset → G u z = pref u z * ψn z + ∑ k ∈ Finset.range (n + 1), termK k z := by
      intro z hz
      dsimp only [G, ψn, termK, Sn]
      rw [ite_eq_right_iff.mpr (fun hmem => absurd hmem hz), ← Finset.mul_sum]; ring
    rw [triIntegral_congrC (G := fun z => pref u z * ψn z + ∑ k ∈ Finset.range (n + 1), termK k z)
          hR_pos.le hm_pos.le
          (fun x _ => h_pt_G _ fun ⟨k, _, hk⟩ => h_avoid.1 x k hk.symm)
          (fun y _ => h_pt_G _ fun ⟨k, _, hk⟩ => h_avoid.2.2 y k hk.symm)
          (fun x _ => h_pt_G _ fun ⟨k, _, hk⟩ => h_avoid.2.1 x k hk.symm),
        triIntegral_addC h_Fψ_int h_sum_int, htri_ψn, zero_add,
        triIntegral_sumC _ _ R mθ h_term_int]
    exact Finset.sum_congr rfl h_pole_term
  have htail_bound : ∀ (σ : ℝ), |σ| < Real.pi / 2 → Real.cos σ = Real.cos h.θ →
      ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0) →
      ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) →
      ∃ K : ℝ, ∀ᶠ u : ℝ in atTop,
        ‖∫ t in Ioi v₀, Complex.exp (I * (σ : ℂ)) * G u (Complex.exp (I * (σ : ℂ)) * (t : ℂ))‖ ≤
          K * Real.exp (-R * u) := by
    intro σ hσ hcos_eq hcont hexp
    let d : ℂ := Complex.exp (I * (σ : ℂ))
    have hd_norm : ‖d‖ = 1 := by
      dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.norm_exp_ofReal_mul_I σ
    have hd_re : d.re = Real.cos h.θ := by
      dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re, hcos_eq]
    obtain ⟨Cexp, Dexp, hCexp, _, hbd⟩ := hexp
    have hbase : IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-(1 / 2 : ℝ) * t)) (Ioi 0) volume :=
      integrableOn_rpow_nat_add_half_mul_expC j (by norm_num)
    let Ij : ℝ := ∫ t in Ioi (0 : ℝ), t ^ ((j : ℝ) + 1 / 2) * Real.exp (-(1 / 2 : ℝ) * t)
    let K : ℝ := (Real.sqrt Real.pi)⁻¹ * Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Ij
    refine ⟨K, ?_⟩
    filter_upwards [eventually_gt_atTop ((Dexp + 1) / Real.cos h.θ)] with u hu
    have hu_re : Dexp + 1 < u * Real.cos h.θ := (div_lt_iff₀ hcos).mp hu
    have hF_int0 : IntegrableOn (fun t : ℝ => d * G u (d * (t : ℂ))) (Ioi 0) volume := by
      have hbase_int : IntegrableOn (fun t : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
          ((-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
            (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ)))) (Ioi 0) volume :=
        (halfRayDerivC_integrable hσ hcont hbd j (by rw [hcos_eq]; linarith)).const_mul _
      refine hbase_int.congr_fun (fun t _ => ?_) measurableSet_Ioi
      dsimp only [G, pref]; ring
    have hF_tail : IntegrableOn (fun t : ℝ => d * G u (d * (t : ℂ))) (Ioi v₀) volume :=
      hF_int0.mono_set (Ioi_subset_Ioi hv₀_pos.le)
    let bnd (t : ℝ) : ℝ :=
      ((Real.sqrt Real.pi)⁻¹ * Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u)) *
        (t ^ ((j : ℝ) + 1 / 2) * Real.exp (-(1 / 2 : ℝ) * t))
    have hbnd_int : IntegrableOn bnd (Ioi 0) volume := hbase.const_mul _
    have hpt_le : ∀ t ∈ Ioi v₀, ‖d * G u (d * (t : ℂ))‖ ≤ bnd t := fun t ht => by
      have ht0 : 0 < t := lt_trans hv₀_pos ht
      have hrew : d * G u (d * (t : ℂ)) =
          ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) *
            Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * Minor.pull d ψ t := by
        dsimp only [G, pref, d, Minor.pull]; rw [cpow_half_exp_mulC hσ ht0]; ring
      rw [hrew, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_pow, norm_neg, norm_mul, hd_norm, one_mul,
        Complex.norm_real, Real.norm_of_nonneg ht0.le, Complex.norm_exp,
        show I * ((σ / 2 : ℝ) : ℂ) = ((σ / 2 : ℝ) : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I,
        mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow t]
      have hre : (-(u : ℂ) * (d * (t : ℂ))).re = -(u * Real.cos h.θ) * t := by
        simp [Complex.mul_re, hd_re]; ring
      rw [hre]
      have hpow : t ^ j * t ^ (1 / 2 : ℝ) = t ^ ((j : ℝ) + 1 / 2) := by
        rw [← Real.rpow_natCast t j, ← Real.rpow_add ht0]
      have hv₀_eq : Real.cos h.θ * v₀ = R := by dsimp only [v₀]; field_simp [hcos.ne']
      have hexp_le : Real.exp (-(u * Real.cos h.θ) * t) * Real.exp (Dexp * t) ≤
          Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u) * Real.exp (-(1 / 2 : ℝ) * t) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        have h1 : (u * Real.cos h.θ - Dexp - 1 / 2) * v₀ ≤ (u * Real.cos h.θ - Dexp - 1 / 2) * t :=
          mul_le_mul_of_nonneg_left (le_of_lt ht) (by linarith)
        nlinarith [hv₀_eq]
      calc (Real.sqrt Real.pi)⁻¹ * t ^ j * Real.exp (-(u * Real.cos h.θ) * t) * t ^ (1 / 2 : ℝ) *
              ‖Minor.pull d ψ t‖
          ≤ (Real.sqrt Real.pi)⁻¹ * t ^ j * Real.exp (-(u * Real.cos h.θ) * t) * t ^ (1 / 2 : ℝ) *
              (Cexp * Real.exp (Dexp * t)) :=
            mul_le_mul_of_nonneg_left (hbd t ht0.le) (by positivity)
        _ = (Real.sqrt Real.pi)⁻¹ * Cexp * (t ^ j * t ^ (1 / 2 : ℝ)) *
              (Real.exp (-(u * Real.cos h.θ) * t) * Real.exp (Dexp * t)) := by ring
        _ ≤ (Real.sqrt Real.pi)⁻¹ * Cexp * t ^ ((j : ℝ) + 1 / 2) *
              (Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u) * Real.exp (-(1 / 2 : ℝ) * t)) := by
            rw [hpow]; exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
        _ = bnd t := by dsimp only [bnd]; ring
    calc ‖∫ t in Ioi v₀, d * G u (d * (t : ℂ))‖
        ≤ ∫ t in Ioi v₀, ‖d * G u (d * (t : ℂ))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi v₀, bnd t :=
          setIntegral_mono_on hF_tail.norm (hbnd_int.mono_set (Ioi_subset_Ioi hv₀_pos.le))
            measurableSet_Ioi hpt_le
      _ ≤ ∫ t in Ioi 0, bnd t :=
          setIntegral_mono_set hbnd_int
            ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) => by
              dsimp only [bnd]; exact mul_nonneg (by positivity)
                (mul_nonneg (Real.rpow_pos_of_pos ht _).le (Real.exp_pos _).le))
            (Eventually.of_forall fun _ hx => Ioi_subset_Ioi hv₀_pos.le hx)
      _ = K * Real.exp (-R * u) := by
          dsimp only [bnd, K, Ij]; rw [integral_const_mul]; ring
  have hcontP : ContinuousOn (Minor.pull (dPlusC h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgePlusC_subset_punctured h (wedgePlusC_containsRay h t (le_of_lt ht)))
  have hcontM : ContinuousOn (Minor.pull (dMinusC h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgeMinusC_subset_punctured h (wedgeMinusC_containsRay h t (le_of_lt ht)))
  have hexpM : ExpType (Minor.pull (dMinusC h) ψ) := by rw [dMinusC_eq h]; exact h.expType_minus
  obtain ⟨Kp, hKp⟩ := htail_bound h.θ hθ_abs rfl hcontP h.expType_plus
  obtain ⟨Km, hKm⟩ := htail_bound (-h.θ) hnegθ_abs (Real.cos_neg h.θ) hcontM hexpM
  have h_vert_sub : ∀ y ∈ Icc (-mθ * R) (mθ * R), (R : ℂ) + (y : ℂ) * I ∈ puncturedWedge h.θ₀ h.ε ω := by
    intro y hy
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add]
      rw [show -mθ * R = -(mθ * R) by ring] at hy
      exact ⟨hR_pos, lt_of_le_of_lt (abs_le.mpr hy) (mul_lt_mul_of_pos_right (tan_lt_tanC h) hR_pos)⟩
    · rintro ⟨k, hk⟩; exact h_avoid.2.2 y k hk.symm
  have hψ_vert_cont : ContinuousOn (fun y : ℝ => ψ ((R : ℂ) + (y : ℂ) * I)) (Icc (-mθ * R) (mθ * R)) :=
    h.analyticOn.continuousOn.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn h_vert_sub
  obtain ⟨Mψ, hMψ⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ_vert_cont
  let Kv : ℝ := (2 * mθ * R) * ((Real.sqrt Real.pi)⁻¹ * (R / Real.cos h.θ) ^ j *
    Real.sqrt (R / Real.cos h.θ) * max Mψ 0)
  have h_vert_bd : ∀ u : ℝ,
      ‖I * (∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I))‖ ≤ Kv * Real.exp (-R * u) := by
    intro u
    rw [norm_mul, Complex.norm_I, one_mul]
    have hpt : ∀ y ∈ uIoc (-mθ * R) (mθ * R),
        ‖G u ((R : ℂ) + (y : ℂ) * I)‖ ≤
          ((Real.sqrt Real.pi)⁻¹ * (R / Real.cos h.θ) ^ j * Real.sqrt (R / Real.cos h.θ) * max Mψ 0) *
            Real.exp (-R * u) := fun y hy => by
      rw [uIoc_of_le (by nlinarith)] at hy
      have hy_cc : y ∈ Icc (-mθ * R) (mθ * R) := ⟨hy.1.le, hy.2⟩
      have hnorm_z : ‖(R : ℂ) + (y : ℂ) * I‖ ≤ R / Real.cos h.θ := by
        rw [Complex.norm_def]
        have hy_abs : |y| ≤ mθ * R := abs_le.mpr (by simpa [neg_mul] using hy_cc)
        have hy_sq : y ^ 2 ≤ mθ ^ 2 * R ^ 2 := by
          rw [← sq_abs y]
          calc |y| ^ 2 ≤ (mθ * R) ^ 2 := sq_le_sq' (by linarith [abs_nonneg y]) hy_abs
            _ = mθ ^ 2 * R ^ 2 := by ring
        have hsec : 1 + mθ ^ 2 = (Real.cos h.θ) ^ (-2 : ℤ) := by
          dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, _root_.zpow_neg, zpow_two, div_pow,
            ← one_div, one_add_div (pow_ne_zero 2 hcos.ne'), Real.cos_sq_add_sin_sq, sq]
        have hnsq : Complex.normSq ((R : ℂ) + (y : ℂ) * I) ≤ (R / Real.cos h.θ) ^ 2 := by
          rw [Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
            mul_one, zero_add]
          calc R * R + y * y = R ^ 2 + y ^ 2 := by ring
            _ ≤ R ^ 2 + mθ ^ 2 * R ^ 2 := by linarith
            _ = R ^ 2 * (1 + mθ ^ 2) := by ring
            _ = R ^ 2 * (Real.cos h.θ) ^ (-2 : ℤ) := by rw [hsec]
            _ = (R / Real.cos h.θ) ^ 2 := by rw [_root_.zpow_neg, zpow_two, div_pow]; ring
        exact Real.sqrt_le_iff.mpr ⟨div_nonneg hR_pos.le hcos.le, hnsq⟩
      have hz_ne : (R : ℂ) + (y : ℂ) * I ≠ 0 := fun h0 => by
        have hre := congrArg Complex.re h0; simp at hre; linarith
      have hcpow_norm : ‖((R : ℂ) + (y : ℂ) * I) ^ ((1 / 2 : ℝ) : ℂ)‖ ≤ Real.sqrt (R / Real.cos h.θ) := by
        rw [Complex.norm_cpow_of_ne_zero hz_ne]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one,
          ← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt hnorm_z
      have hexp_norm : ‖Complex.exp (-(u : ℂ) * ((R : ℂ) + (y : ℂ) * I))‖ = Real.exp (-R * u) := by
        rw [Complex.norm_exp]; simp [Complex.mul_re]; ring
      dsimp only [G, pref]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_pow, norm_neg, hexp_norm]
      have hψ_le : ‖ψ ((R : ℂ) + (y : ℂ) * I)‖ ≤ max Mψ 0 := (hMψ y hy_cc).trans (le_max_left _ _)
      calc (Real.sqrt Real.pi)⁻¹ * ‖(R : ℂ) + (y : ℂ) * I‖ ^ j * Real.exp (-R * u) *
              ‖((R : ℂ) + (y : ℂ) * I) ^ ((1 / 2 : ℝ) : ℂ)‖ * ‖ψ ((R : ℂ) + (y : ℂ) * I)‖
          ≤ (Real.sqrt Real.pi)⁻¹ * (R / Real.cos h.θ) ^ j * Real.exp (-R * u) *
              Real.sqrt (R / Real.cos h.θ) * max Mψ 0 := by gcongr
        _ = ((Real.sqrt Real.pi)⁻¹ * (R / Real.cos h.θ) ^ j * Real.sqrt (R / Real.cos h.θ) * max Mψ 0) *
              Real.exp (-R * u) := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have habs : |mθ * R - -mθ * R| = 2 * mθ * R := by
      rw [show mθ * R - -mθ * R = 2 * mθ * R by ring, abs_of_pos (by positivity)]
    rw [habs] at hle
    calc ‖∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I)‖ ≤ _ := hle
      _ = Kv * Real.exp (-R * u) := by dsimp only [Kv]; ring
  obtain ⟨Cp, Dp, _, _, hbdp⟩ := h.expType_plus
  obtain ⟨Cm, Dm, _, _, hbdm⟩ := hexpM
  refine ⟨Kv + Km + Kp, ?_⟩
  filter_upwards [hKp, hKm,
    eventually_gt_atTop (max (Dp / Real.cos h.θ) (Dm / Real.cos h.θ))] with u hkp hkm hu_max
  have hup : Dp < u * Real.cos h.θ := (div_lt_iff₀ hcos).mp (lt_of_le_of_lt (le_max_left _ _) hu_max)
  have hum : Dm < u * Real.cos h.θ := (div_lt_iff₀ hcos).mp (lt_of_le_of_lt (le_max_right _ _) hu_max)
  have hintP : IntegrableOn (fun t : ℝ => dPlusC h * G u (dPlusC h * (t : ℂ))) (Ioi 0) volume := by
    have hbaseP : IntegrableOn (fun t : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
        ((-(dPlusC h * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (dPlusC h * (t : ℂ))) * dPlusC h *
          (dPlusC h * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (dPlusC h * (t : ℂ)))) (Ioi 0) volume :=
      (halfRayDerivC_integrable hθ_abs hcontP hbdp j hup).const_mul _
    refine hbaseP.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only [G, pref]; ring
  have hintM : IntegrableOn (fun t : ℝ => dMinusC h * G u (dMinusC h * (t : ℂ))) (Ioi 0) volume := by
    have hbaseM : IntegrableOn (fun t : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
        ((-(dMinusC h * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (dMinusC h * (t : ℂ))) * dMinusC h *
          (dMinusC h * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (dMinusC h * (t : ℂ)))) (Ioi 0) volume :=
      (halfRayDerivC_integrable hnegθ_abs hcontM hbdm j (by rwa [Real.cos_neg])).const_mul _
    refine hbaseM.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only [G, pref]; ring
  have hhrP : halfRayDerivC ψ (dPlusC h) j u = ∫ t in Ioi (0 : ℝ), dPlusC h * G u (dPlusC h * (t : ℂ)) := by
    unfold halfRayDerivC; rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_; dsimp only [G, pref]; ring
  have hhrM : halfRayDerivC ψ (dMinusC h) j u = ∫ t in Ioi (0 : ℝ), dMinusC h * G u (dMinusC h * (t : ℂ)) := by
    unfold halfRayDerivC; rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_; dsimp only [G, pref]; ring
  have hsplitP : (∫ t in (0 : ℝ)..v₀, dPlusC h * G u (dPlusC h * (t : ℂ))) +
      (∫ t in Ioi v₀, dPlusC h * G u (dPlusC h * (t : ℂ))) =
      ∫ t in Ioi (0 : ℝ), dPlusC h * G u (dPlusC h * (t : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintP (hintP.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hsplitM : (∫ t in (0 : ℝ)..v₀, dMinusC h * G u (dMinusC h * (t : ℂ))) +
      (∫ t in Ioi v₀, dMinusC h * G u (dMinusC h * (t : ℂ))) =
      ∫ t in Ioi (0 : ℝ), dMinusC h * G u (dMinusC h * (t : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintM (hintM.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hdP_mul : (1 + I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dPlusC h := by
    have hdP : dPlusC h = (Real.cos h.θ : ℂ) + (Real.sin h.θ : ℂ) * I := by
      unfold dPlusC; rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hdP]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
    field_simp [hc]
  have hdM_mul : (1 - I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dMinusC h := by
    have hdM : dMinusC h = (Real.cos h.θ : ℂ) - (Real.sin h.θ : ℂ) * I := by
      unfold dMinusC; rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]; ring
    rw [hdM]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
    field_simp [hc]
  have hcovP : ∫ t in (0 : ℝ)..v₀, dPlusC h * G u (dPlusC h * (t : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 + I * (mθ : ℂ)) * G u ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun t : ℝ => dPlusC h * G u (dPlusC h * (t : ℂ))) hcos.ne' (a := 0) (b := R)
    have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) * G u ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dPlusC h * G u (dPlusC h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 + I * (mθ : ℂ)) = dPlusC h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
        rw [hdP_mul]; push_cast; ring
      rw [harg, Complex.real_smul, hdP_mul]; push_cast; ring
    rw [heq, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne', one_smul, zero_div]
  have hcovM : ∫ t in (0 : ℝ)..v₀, dMinusC h * G u (dMinusC h * (t : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 - I * (mθ : ℂ)) * G u ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun t : ℝ => dMinusC h * G u (dMinusC h * (t : ℂ))) hcos.ne' (a := 0) (b := R)
    have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) * G u ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dMinusC h * G u (dMinusC h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 - I * (mθ : ℂ)) = dMinusC h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
        rw [hdM_mul]; push_cast; ring
      rw [harg, Complex.real_smul, hdM_mul]; push_cast; ring
    rw [heq, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne', one_smul, zero_div]
  have hdiff : halfRayDerivC ψ (dMinusC h) j u - halfRayDerivC ψ (dPlusC h) j u -
      ∑ k ∈ Finset.range (n + 1),
        halfStokesCoeff ω res k * (-(ω k : ℂ)) ^ j * Complex.exp (-(ω k : ℂ) * (u : ℂ)) =
      (∫ t in Ioi v₀, dMinusC h * G u (dMinusC h * (t : ℂ))) -
      (∫ t in Ioi v₀, dPlusC h * G u (dPlusC h * (t : ℂ))) -
      I * (∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I)) := by
    rw [← htri_G u, hhrM, hhrP, ← hsplitM, ← hsplitP, hcovM, hcovP]; unfold triIntegral; ring
  rw [hdiff]
  have htri_ineq : ‖(∫ t in Ioi v₀, dMinusC h * G u (dMinusC h * (t : ℂ))) -
        (∫ t in Ioi v₀, dPlusC h * G u (dPlusC h * (t : ℂ))) -
        I * (∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I))‖ ≤
      ‖∫ t in Ioi v₀, dMinusC h * G u (dMinusC h * (t : ℂ))‖ +
      ‖∫ t in Ioi v₀, dPlusC h * G u (dPlusC h * (t : ℂ))‖ +
      ‖I * (∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I))‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hv := h_vert_bd u
  have hkp' : ‖∫ t in Ioi v₀, dPlusC h * G u (dPlusC h * (t : ℂ))‖ ≤ Kp * Real.exp (-R * u) := hkp
  have hkm' : ‖∫ t in Ioi v₀, dMinusC h * G u (dMinusC h * (t : ℂ))‖ ≤ Km * Real.exp (-R * u) := hkm
  dsimp only [R] at hv hkp' hkm' ⊢
  linarith

private lemma abelConv_stokes_jumpC {ψ ω res} (h : MeromorphicBorelData ψ ω res) (n j : ℕ) :
    ∃ R' : ℝ, ω n < R' ∧ ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aAbelC ψ).value (dMinusC h) (t : ℂ)) u -
        iteratedDeriv j (fun t : ℝ => (aAbelC ψ).value (dPlusC h) (t : ℂ)) u -
        ∑ k ∈ Finset.range (n + 1),
          halfStokesCoeff ω res k * iteratedDeriv j (branchMode (1 / 2) (ω k : ℂ)) u‖ ≤
        C * Real.exp (-R' * u) := by
  let R' : ℝ := (ω n + ω (n + 1)) / 2
  have hR'_gt : ω n < R' := by have := h.ω_mono (Nat.lt_succ_self n); dsimp only [R']; linarith
  refine ⟨R', hR'_gt, ?_⟩
  have hθ_abs : |h.θ| < Real.pi / 2 := abs_lt.mpr ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hθ₀_lt⟩
  have hnegθ_abs : |-h.θ| < Real.pi / 2 := by simpa [abs_neg] using hθ_abs
  have hcontP : ContinuousOn (Minor.pull (dPlusC h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgePlusC_subset_punctured h (wedgePlusC_containsRay h t (le_of_lt ht)))
  have hcontM : ContinuousOn (Minor.pull (dMinusC h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgeMinusC_subset_punctured h (wedgeMinusC_containsRay h t (le_of_lt ht)))
  have hexpM : ExpType (Minor.pull (dMinusC h) ψ) := by rw [dMinusC_eq h]; exact h.expType_minus
  let gPos : ℝ → ℂ := fun t => (aAbelC ψ).value (dPlusC h) (t : ℂ)
  let gNeg : ℝ → ℂ := fun t => (aAbelC ψ).value (dMinusC h) (t : ℂ)
  let w : ℝ → ℂ := branchMode (1 / 2) 0
  let H : ℝ → ℂ := fun t =>
    halfRayLaplace ψ (dMinusC h) t - halfRayLaplace ψ (dPlusC h) t -
      ∑ k ∈ Finset.range (n + 1), halfStokesCoeff ω res k * Complex.exp (-(ω k : ℂ) * (t : ℂ))
  have hw_eq : ∀ t : ℝ, w t = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := fun t => by simp [w, branchMode]
  have hw_cd : ∀ t : ℝ, 0 < t → ContDiffAt ℝ j w t := fun t ht => by
    have hrp : ContDiffAt ℝ j (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) t := Real.contDiffAt_rpow_const (Or.inl ht.ne')
    have hEq : w = fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := funext hw_eq
    rw [hEq]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp t hrp
  have hexp_cd : ∀ k : ℕ, ∀ t : ℝ, ContDiffAt ℝ j (fun x : ℝ => Complex.exp (-(ω k : ℂ) * (x : ℂ))) t :=
    fun k t => (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).contDiffAt
  have hbm_cd : ∀ k : ℕ, ∀ t : ℝ, 0 < t → ContDiffAt ℝ j (branchMode (1 / 2) (ω k : ℂ)) t := fun k t ht => by
    have heq : branchMode (1 / 2) (ω k : ℂ) = fun x => w x * Complex.exp (-(ω k : ℂ) * (x : ℂ)) :=
      funext fun x => by simp [branchMode, w]
    rw [heq]; exact (hw_cd t ht).mul (hexp_cd k t)
  have hvalP := abelConv_value_eq_rpow_mul_halfRay hθ_abs hcontP h.expType_plus
  have hvalM := abelConv_value_eq_rpow_mul_halfRay hnegθ_abs hcontM hexpM
  have hcdP := (iteratedDeriv_and_contDiffAt_halfRayLaplaceC hθ_abs hcontP h.expType_plus j).2
  have hcdM := (iteratedDeriv_and_contDiffAt_halfRayLaplaceC hnegθ_abs hcontM hexpM j).2
  choose C_i hC_i using fun i : Fin (j + 1) => halfRayDeriv_stokes_jumpC h n i.val
  have h_all_jump := Filter.eventually_all.mpr hC_i
  have h_all_hrP := Filter.eventually_all.mpr fun i : Fin (j + 1) =>
    (iteratedDeriv_and_contDiffAt_halfRayLaplaceC hθ_abs hcontP h.expType_plus i.val).1
  have h_all_hrM := Filter.eventually_all.mpr fun i : Fin (j + 1) =>
    (iteratedDeriv_and_contDiffAt_halfRayLaplaceC hnegθ_abs hcontM hexpM i.val).1
  let Bw (i : ℕ) : ℝ := ∑ m ∈ Finset.range (i + 1), ‖(P_branch (1 / 2) 0 i).coeff m‖
  have hw_bd : ∀ i : ℕ, ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv i w u‖ ≤ Bw i := fun i u hu => by
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    rw [iteratedDeriv_branchMode (1 / 2) 0 i u hu0]
    simp only [branchMode, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [norm_mul, Complex.norm_real]
    change ‖u ^ (-(1 / 2 : ℝ))‖ * ‖Polynomial.eval (u : ℂ)⁻¹ (P_branch (1 / 2) 0 i)‖ ≤ Bw i
    rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos hu0 _).le]
    have hrp1 : u ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hu0.le]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hu (by norm_num))
    have hdeg : (P_branch (1 / 2) 0 i).natDegree < i + 1 := Nat.lt_succ_of_le (P_branch_natDegree_le (1 / 2) 0 i)
    rw [Polynomial.eval_eq_sum_range' hdeg]
    have hpol : ‖∑ m ∈ Finset.range (i + 1), (P_branch (1 / 2) 0 i).coeff m * (u : ℂ)⁻¹ ^ m‖ ≤ Bw i := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le]
      have hinv : u⁻¹ ^ m ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hu0.le) (inv_le_one_of_one_le₀ hu)
      calc ‖(P_branch (1 / 2) 0 i).coeff m‖ * u⁻¹ ^ m ≤ ‖(P_branch (1 / 2) 0 i).coeff m‖ * 1 :=
            mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ = ‖(P_branch (1 / 2) 0 i).coeff m‖ := mul_one _
    calc u ^ (-(1 / 2 : ℝ)) * ‖∑ m ∈ Finset.range (i + 1), (P_branch (1 / 2) 0 i).coeff m * (u : ℂ)⁻¹ ^ m‖
        ≤ 1 * Bw i := mul_le_mul hrp1 hpol (norm_nonneg _) zero_le_one
      _ = Bw i := one_mul _
  let Ctot : ℝ := ∑ i : Fin (j + 1), (j.choose i.val : ℝ) * Bw i.val * max (C_i ⟨j - i.val, by omega⟩) 0
  refine ⟨Ctot, ?_⟩
  have hnhdsP : ∀ᶠ u : ℝ in atTop, gPos =ᶠ[𝓝 u] fun t => w t * halfRayLaplace ψ (dPlusC h) t := by
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hvalP
    filter_upwards [eventually_gt_atTop U₀] with u hu
    filter_upwards [Ioi_mem_nhds hu] with t ht
    rw [hw_eq t]; exact hU₀ t (le_of_lt ht)
  have hnhdsM : ∀ᶠ u : ℝ in atTop, gNeg =ᶠ[𝓝 u] fun t => w t * halfRayLaplace ψ (dMinusC h) t := by
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hvalM
    filter_upwards [eventually_gt_atTop U₀] with u hu
    filter_upwards [Ioi_mem_nhds hu] with t ht
    rw [hw_eq t]; exact hU₀ t (le_of_lt ht)
  filter_upwards [hnhdsP, hnhdsM, hcdP, hcdM, h_all_jump, h_all_hrP, h_all_hrM,
    eventually_ge_atTop (1 : ℝ)] with u hlocP hlocM hcdPu hcdMu hju hhrPu hhrMu hu1
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hcd_gP : ContDiffAt ℝ j gPos u := ((hw_cd u hu0).mul hcdPu).congr_of_eventuallyEq hlocP
  have hcd_gM : ContDiffAt ℝ j gNeg u := ((hw_cd u hu0).mul hcdMu).congr_of_eventuallyEq hlocM
  have hcd_sum_bm : ContDiffAt ℝ j
      (fun t => ∑ k ∈ Finset.range (n + 1), halfStokesCoeff ω res k * branchMode (1 / 2) (ω k : ℂ) t) u :=
    ContDiffAt.sum fun k _ => contDiffAt_const.mul (hbm_cd k u hu0)
  have hcd_H : ContDiffAt ℝ j H u :=
    (hcdMu.sub hcdPu).sub (ContDiffAt.sum fun k _ => contDiffAt_const.mul (hexp_cd k u))
  have h_eq_loc : (fun t => gNeg t - gPos t -
        ∑ k ∈ Finset.range (n + 1), halfStokesCoeff ω res k * branchMode (1 / 2) (ω k : ℂ) t) =ᶠ[𝓝 u]
      fun t => w t * H t := by
    filter_upwards [hlocP, hlocM] with t hP hM
    dsimp only [H]
    rw [hM, hP, mul_sub, mul_sub, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun k _ => ?_
    simp only [branchMode, w, neg_zero, zero_mul, Complex.exp_zero, mul_one]; ring
  have h_lhs_eq : iteratedDeriv j gNeg u - iteratedDeriv j gPos u -
      ∑ k ∈ Finset.range (n + 1), halfStokesCoeff ω res k * iteratedDeriv j (branchMode (1 / 2) (ω k : ℂ)) u =
      iteratedDeriv j (fun t => w t * H t) u := by
    rw [← h_eq_loc.iteratedDeriv_eq j,
      iteratedDeriv_fun_sub (hcd_gM.sub hcd_gP) hcd_sum_bm,
      iteratedDeriv_fun_sub hcd_gM hcd_gP]
    congr 1
    rw [iteratedDeriv_fun_sum (fun k _ => contDiffAt_const.mul (hbm_cd k u hu0))]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (iteratedDeriv_const_mul (halfStokesCoeff ω res k) (hbm_cd k u hu0)).symm
  rw [h_lhs_eq, iteratedDeriv_fun_mul (hw_cd u hu0) hcd_H]
  have hderiv_H : ∀ i : ℕ, i ≤ j →
      iteratedDeriv i H u =
        halfRayDerivC ψ (dMinusC h) i u - halfRayDerivC ψ (dPlusC h) i u -
          ∑ k ∈ Finset.range (n + 1),
            halfStokesCoeff ω res k * (-(ω k : ℂ)) ^ i * Complex.exp (-(ω k : ℂ) * (u : ℂ)) := fun i hi => by
    have hcdM_i : ContDiffAt ℝ i (halfRayLaplace ψ (dMinusC h)) u := hcdMu.of_le (Nat.cast_le.mpr hi)
    have hcdP_i : ContDiffAt ℝ i (halfRayLaplace ψ (dPlusC h)) u := hcdPu.of_le (Nat.cast_le.mpr hi)
    have hexp_i : ∀ k : ℕ, ContDiffAt ℝ i (fun x : ℝ => Complex.exp (-(ω k : ℂ) * (x : ℂ))) u :=
      fun k => (hexp_cd k u).of_le (Nat.cast_le.mpr hi)
    have hcd_sum_e : ContDiffAt ℝ i
        (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), halfStokesCoeff ω res k * Complex.exp (-(ω k : ℂ) * (x : ℂ))) u :=
      ContDiffAt.sum fun k _ => contDiffAt_const.mul (hexp_i k)
    dsimp only [H]
    rw [iteratedDeriv_fun_sub (hcdM_i.sub hcdP_i) hcd_sum_e,
      iteratedDeriv_fun_sub hcdM_i hcdP_i]
    dsimp only [dMinusC, dPlusC]
    rw [hhrMu ⟨i, Nat.lt_succ_of_le hi⟩, hhrPu ⟨i, Nat.lt_succ_of_le hi⟩,
      iteratedDeriv_fun_sum (fun k _ => contDiffAt_const.mul (hexp_i k))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDeriv_const_mul _ (hexp_i k)]
    have hd_exp : ∀ m : ℕ, ∀ x : ℝ,
        iteratedDeriv m (fun t : ℝ => Complex.exp (-(ω k : ℂ) * (t : ℂ))) x =
          (-(ω k : ℂ)) ^ m * Complex.exp (-(ω k : ℂ) * (x : ℂ)) := fun m => by
      induction m with
      | zero => intro x; simp
      | succ m ihm =>
        intro x
        rw [iteratedDeriv_succ, show iteratedDeriv m (fun t : ℝ => Complex.exp (-(ω k : ℂ) * (t : ℂ))) =
          fun t : ℝ => (-(ω k : ℂ)) ^ m * Complex.exp (-(ω k : ℂ) * (t : ℂ)) from funext ihm]
        have hd : HasDerivAt (fun t : ℝ => (-(ω k : ℂ)) ^ m * Complex.exp (-(ω k : ℂ) * (t : ℂ)))
            ((-(ω k : ℂ)) ^ (m + 1) * Complex.exp (-(ω k : ℂ) * (x : ℂ))) x := by
          have h1 : HasDerivAt (fun t : ℝ => -(ω k : ℂ) * (t : ℂ)) (-(ω k : ℂ)) x := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(ω k : ℂ))
          exact (h1.cexp.const_mul _).congr_deriv (by rw [pow_succ]; ring)
        exact hd.deriv
    rw [hd_exp i u]; ring
  calc ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i w u * iteratedDeriv (j - i) H u‖
      ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i w u * iteratedDeriv (j - i) H u‖ :=
        norm_sum_le _ _
    _ = ∑ i : Fin (j + 1), ‖(j.choose i.val : ℂ) * iteratedDeriv i.val w u * iteratedDeriv (j - i.val) H u‖ :=
        (Fin.sum_univ_eq_sum_range _ (j + 1)).symm
    _ ≤ ∑ i : Fin (j + 1), (j.choose i.val : ℝ) * Bw i.val *
          (max (C_i ⟨j - i.val, by omega⟩) 0 * Real.exp (-R' * u)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        have hH_le : ‖iteratedDeriv (j - i.val) H u‖ ≤
            max (C_i ⟨j - i.val, by omega⟩) 0 * Real.exp (-R' * u) := by
          rw [hderiv_H (j - i.val) (Nat.sub_le j i.val)]
          exact (hju ⟨j - i.val, by omega⟩).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
        have hBw_nn : 0 ≤ Bw i.val := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h1 : (j.choose i.val : ℝ) * ‖iteratedDeriv i.val w u‖ ≤ (j.choose i.val : ℝ) * Bw i.val :=
          mul_le_mul_of_nonneg_left (hw_bd i.val u hu1) (Nat.cast_nonneg _)
        exact mul_le_mul h1 hH_le (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hBw_nn)
    _ = Ctot * Real.exp (-R' * u) := by
        dsimp only [Ctot]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring

/-! #### 3B. Convergent Branch-Point Operator `L_conv` & Lowest-`w`-Order Vandermonde Descent -/

/-- `ℂ{w}`-linear branch-point differential operator
`L_conv α r ω Q = ∑ j, P_branch α ω j • ∂_j Q`. -/
@[expose] def L_conv (α : ℝ) (r : ℕ) (ω : ℂ) :
    MvPolynomial (Fin (r + 1)) ConvergentPowerSeries →ₗ[ConvergentPowerSeries]
      MvPolynomial (Fin (r + 1)) ConvergentPowerSeries where
  toFun Q := ∑ j : Fin (r + 1), polyToConv (P_branch α ω j.val) • MvPolynomial.pderiv j Q
  map_add' P Q := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, smul_comm]

private lemma degree_pderiv_conv_lt {ι : Type*} (i : ι) (Q : MvPolynomial ι ConvergentPowerSeries)
    (h : 0 < Q.totalDegree) : (MvPolynomial.pderiv i Q).totalDegree < Q.totalDegree := by
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

private lemma totalDegree_conv_sum_lt {ι σ : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial σ ConvergentPowerSeries) {d : ℕ} (hd : 0 < d)
    (hf : ∀ i ∈ s, (f i).totalDegree < d) :
    (∑ i ∈ s, f i).totalDegree < d := by
  induction s using Finset.induction_on with
  | empty => simpa using hd
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (MvPolynomial.totalDegree_add _ _).trans_lt ?_
    exact max_lt (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Strict `Y`-total-degree drop under `L_conv α r ω`. -/
theorem degree_L_conv_lt (α : ℝ) {r : ℕ} (ω : ℂ)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (h : 0 < Q.totalDegree) :
    (L_conv α r ω Q).totalDegree < Q.totalDegree := by
  unfold L_conv
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine totalDegree_conv_sum_lt Finset.univ _ h fun j _ => ?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans_lt (degree_pderiv_conv_lt j Q h)

private lemma evalConvMvPoly_finset_sum_eventually {ι : Type*} {r : ℕ} (s : Finset ι)
    (f : ι → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPoly (∑ i ∈ s, f i) (u : ℂ)⁻¹ = ∑ i ∈ s, evalConvMvPoly (f i) (u : ℂ)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact Filter.Eventually.of_forall fun u => by simp [evalConvMvPoly_zero]
  | @insert a s ha ih =>
    filter_upwards [ih, evalConvMvPoly_add_eventually (f a) (∑ i ∈ s, f i)] with u hu hadd
    rw [Finset.sum_insert ha, hadd, hu, Finset.sum_insert ha]

/-- Eventually for `u → +∞`, evaluating `L_conv α r ω Q` at `w = u⁻¹` commutes with `evalConvMvPoly`. -/
lemma evalConvMvPoly_L_conv_eventually (α : ℝ) {r : ℕ} (ω : ℂ)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPoly (L_conv α r ω Q) (u : ℂ)⁻¹ =
        ∑ j : Fin (r + 1), (P_branch α ω j.val).eval (u : ℂ)⁻¹ •
          MvPolynomial.pderiv j (evalConvMvPoly Q (u : ℂ)⁻¹) := by
  unfold L_conv
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  have hsum := evalConvMvPoly_finset_sum_eventually (Finset.univ : Finset (Fin (r + 1)))
    (fun j => polyToConv (P_branch α ω j.val) • MvPolynomial.pderiv j Q)
  have hsmul : ∀ᶠ u : ℝ in atTop, ∀ j : Fin (r + 1),
      evalConvMvPoly (polyToConv (P_branch α ω j.val) • MvPolynomial.pderiv j Q) (u : ℂ)⁻¹ =
        (P_branch α ω j.val).eval (u : ℂ)⁻¹ • MvPolynomial.pderiv j (evalConvMvPoly Q (u : ℂ)⁻¹) := by
    refine Filter.eventually_all.mpr fun j => ?_
    filter_upwards [evalConvMvPoly_smul_eventually (polyToConv (P_branch α ω j.val)) (MvPolynomial.pderiv j Q)]
      with u hu
    rw [hu, evalConv_poly, evalConvMvPoly_pderiv]
  filter_upwards [hsum, hsmul] with u hus hsm
  rw [hus]
  exact Finset.sum_congr rfl fun j _ => hsm j

/-- Exact shift invariance: if `L_conv α r (ω k) Q = 0` for all `k < m`, then `evalConvMvPoly Q u⁻¹`
is identically invariant under all linear combinations of the Stokes jet vectors for `k < m`. -/
theorem eval_shift_of_L_conv_eq_zero (α : ℝ) {r : ℕ} (ω : ℕ → ℂ)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (m : ℕ)
    (hL : ∀ k < m, L_conv α r (ω k) Q = 0) :
    ∀ᶠ u : ℝ in atTop, ∀ (lam : ℕ → ℂ) (x : Fin (r + 1) → ℂ),
      MvPolynomial.eval
        (fun j : Fin (r + 1) =>
          x j + ∑ k ∈ Finset.range m, lam k * (P_branch α (ω k) j.val).eval (u : ℂ)⁻¹)
        (evalConvMvPoly Q (u : ℂ)⁻¹) =
      MvPolynomial.eval x (evalConvMvPoly Q (u : ℂ)⁻¹) := by
  have hall : ∀ᶠ u : ℝ in atTop, ∀ k ∈ Finset.range m,
      ∑ j : Fin (r + 1), (P_branch α (ω k) j.val).eval (u : ℂ)⁻¹ •
        MvPolynomial.pderiv j (evalConvMvPoly Q (u : ℂ)⁻¹) = 0 := by
    refine (Filter.eventually_all_finset (Finset.range m)).mpr fun k hk => ?_
    filter_upwards [evalConvMvPoly_L_conv_eventually α (ω k) Q] with u hu
    rw [← hu, hL k (Finset.mem_range.mp hk), evalConvMvPoly_zero]
  filter_upwards [hall] with u hu lam x
  suffices hsub : ∀ n ≤ m,
      MvPolynomial.eval
        (fun j : Fin (r + 1) =>
          x j + ∑ k ∈ Finset.range n, lam k * (P_branch α (ω k) j.val).eval (u : ℂ)⁻¹)
        (evalConvMvPoly Q (u : ℂ)⁻¹) =
      MvPolynomial.eval x (evalConvMvPoly Q (u : ℂ)⁻¹) from hsub m le_rfl
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n < m := Nat.lt_of_succ_le hn
    have hsplit : (fun j : Fin (r + 1) =>
        x j + ∑ k ∈ Finset.range (n + 1), lam k * (P_branch α (ω k) j.val).eval (u : ℂ)⁻¹) =
        fun j : Fin (r + 1) =>
          (x j + ∑ k ∈ Finset.range n, lam k * (P_branch α (ω k) j.val).eval (u : ℂ)⁻¹) +
            lam n * (P_branch α (ω n) j.val).eval (u : ℂ)⁻¹ := by
      funext j; rw [Finset.sum_range_succ, add_assoc]
    rw [hsplit, shift_invariant_of_pderiv_sum_eq_zero _ _ (hu n (Finset.mem_range.mpr hlt)),
      ih (Nat.le_of_lt hlt)]

/-- Vanishing order at `w = 0` of a convergent power series (`0` if the series is `0`). -/
@[expose] def psOrder (a : ConvergentPowerSeries) : ℕ := by
  classical exact if h : ∃ k : ℕ, PowerSeries.coeff k a.val ≠ 0 then Nat.find h else 0

lemma psOrder_coeff_ne_zero {a : ConvergentPowerSeries} (ha : a ≠ 0) :
    PowerSeries.coeff (psOrder a) a.val ≠ 0 := by
  classical
  have hex : ∃ k : ℕ, PowerSeries.coeff k a.val ≠ 0 := by
    by_contra! hall
    exact ha (Subtype.ext (PowerSeries.ext fun k => by simpa using hall k))
  unfold psOrder
  simp only [hex, ↓reduceDIte]
  exact Nat.find_spec hex

lemma psOrder_coeff_eq_zero_of_lt {a : ConvergentPowerSeries} {k : ℕ} (hk : k < psOrder a) :
    PowerSeries.coeff k a.val = 0 := by
  classical
  unfold psOrder at hk
  by_cases hex : ∃ n : ℕ, PowerSeries.coeff n a.val ≠ 0
  · simp only [hex, ↓reduceDIte] at hk
    exact not_not.mp (Nat.find_min hex hk)
  · simp only [hex, ↓reduceDIte] at hk
    exact absurd hk (Nat.not_lt_zero k)

/-- Minimum `w`-order among all non-constant (`α ≠ 0`) `Y`-monomials of `Q`. -/
@[expose] def minNonConstWOrd {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) : ℕ := by
  classical exact if h : (Q.support.erase 0).Nonempty then
    (Q.support.erase 0).inf' h fun α => psOrder (Q.coeff α)
  else 0

/-- `[w^k]` coefficient polynomial in `ℂ[Y_0, ..., Y_r]` over all non-constant (`α ≠ 0`) monomials. -/
@[expose] def coeffW {r : ℕ} (k : ℕ) (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    MvPolynomial (Fin (r + 1)) ℂ := by
  classical exact ∑ α ∈ Q.support.erase 0, MvPolynomial.monomial α (PowerSeries.coeff k (Q.coeff α).val)

private lemma coeffW_coeff {r : ℕ} (k : ℕ) (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (m : Fin (r + 1) →₀ ℕ) :
    (coeffW k Q).coeff m = if m = 0 then 0 else PowerSeries.coeff k (Q.coeff m).val := by
  classical
  unfold coeffW
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte]
    refine Finset.sum_eq_zero fun b hb => ?_
    simp [(Finset.mem_erase.mp hb).1]
  · simp only [hm0, ↓reduceIte]
    by_cases hmem : m ∈ Q.support.erase 0
    · rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hbm; simp [hbm]
      · intro hnot; exact absurd hmem hnot
    · have hnot : m ∉ Q.support := fun h => hmem (Finset.mem_erase.mpr ⟨hm0, h⟩)
      rw [MvPolynomial.notMem_support_iff.mp hnot, Subring.coe_zero, map_zero, Finset.sum_eq_zero]
      intro b hb
      rw [ite_eq_right_iff]
      intro hbm; subst hbm; exact absurd hb hmem

private lemma nonConst_support_nonempty {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (hpos : 0 < Q.totalDegree) :
    (Q.support.erase 0).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hle : Q.totalDegree ≤ 0 := by
    rw [MvPolynomial.totalDegree_eq]
    refine Finset.sup_le fun m hm => ?_
    by_cases hm0 : m = 0
    · subst hm0; simp
    · have : m ∈ Q.support.erase 0 := Finset.mem_erase.mpr ⟨hm0, hm⟩
      rw [hempty] at this; exact absurd this (Finset.notMem_empty m)
  omega

lemma coeffW_minNonConstWOrd_pos_deg {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (hpos : 0 < Q.totalDegree) :
    0 < (coeffW (minNonConstWOrd Q) Q).totalDegree := by
  classical
  have hne := nonConst_support_nonempty Q hpos
  obtain ⟨m, hm_mem, hm_min⟩ := Finset.exists_min_image (Q.support.erase 0)
    (fun α => psOrder (Q.coeff α)) hne
  have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm_mem).1
  have hm_supp : m ∈ Q.support := (Finset.mem_erase.mp hm_mem).2
  have hQm_ne : Q.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm_supp
  have hord_eq : minNonConstWOrd Q = psOrder (Q.coeff m) := by
    unfold minNonConstWOrd
    simp only [hne, ↓reduceDIte]
    apply le_antisymm
    · exact Finset.inf'_le _ hm_mem
    · exact (Finset.le_inf'_iff hne _).mpr fun b hb => hm_min b hb
  have hcoeff_ne : (coeffW (minNonConstWOrd Q) Q).coeff m ≠ 0 := by
    rw [coeffW_coeff, ite_eq_right_iff.mpr (fun h => absurd h hm0), hord_eq]
    exact psOrder_coeff_ne_zero hQm_ne
  have hm_supp' : m ∈ (coeffW (minNonConstWOrd Q) Q).support := MvPolynomial.mem_support_iff.mpr hcoeff_ne
  have hsum_pos : 0 < m.sum fun _ e => e := by
    by_contra h0
    push Not at h0
    have hz : m.sum (fun _ e => e) = 0 := Nat.eq_zero_of_le_zero h0
    have hall : ∀ i, m i = 0 := by
      intro i
      by_cases hi : i ∈ m.support
      · have hle := Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _) hi
        change m i ≤ m.sum (fun _ e => e) at hle
        omega
      · exact Finsupp.notMem_support_iff.mp hi
    exact hm0 (Finsupp.ext hall)
  exact lt_of_lt_of_le hsum_pos (MvPolynomial.le_totalDegree hm_supp')

/-- Lowest-`w`-order extraction: `L_conv α r ω Q = 0` forces
`D_freq r ω (coeffW (minNonConstWOrd Q) Q) = 0`. -/
theorem D_freq_coeffW_of_L_conv_eq_zero (α : ℝ) {r : ℕ} (ω : ℂ)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hpos : 0 < Q.totalDegree)
    (hL : L_conv α r ω Q = 0) :
    D_freq r ω (coeffW (minNonConstWOrd Q) Q) = 0 := by
  classical
  have hne := nonConst_support_nonempty Q hpos
  let k₀ : ℕ := minNonConstWOrd Q
  have hk₀_le : ∀ m : Fin (r + 1) →₀ ℕ, m ≠ 0 → ∀ k < k₀, PowerSeries.coeff k (Q.coeff m).val = 0 := by
    intro m hm0 k hk
    by_cases hmem : m ∈ Q.support
    · have hmem' : m ∈ Q.support.erase 0 := Finset.mem_erase.mpr ⟨hm0, hmem⟩
      have hle : k₀ ≤ psOrder (Q.coeff m) := by
        dsimp only [k₀]; unfold minNonConstWOrd
        simp only [hne, ↓reduceDIte]; exact Finset.inf'_le _ hmem'
      exact psOrder_coeff_eq_zero_of_lt (lt_of_lt_of_le hk hle)
    · rw [MvPolynomial.notMem_support_iff.mp hmem, Subring.coe_zero, map_zero]
  ext m
  change (D_freq r ω (coeffW k₀ Q)).coeff m = 0
  have hL_coeff : PowerSeries.coeff k₀ ((L_conv α r ω Q).coeff m).val = 0 := by
    rw [hL]; simp
  have h_expand : PowerSeries.coeff k₀ ((L_conv α r ω Q).coeff m).val =
      (D_freq r ω (coeffW k₀ Q)).coeff m := by
    unfold L_conv D_freq
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
    have hsum_val : (∑ j : Fin (r + 1), (polyToConv (P_branch α ω j.val) • MvPolynomial.pderiv j Q).coeff m).val =
        ∑ j : Fin (r + 1), ((polyToConv (P_branch α ω j.val) • MvPolynomial.pderiv j Q).coeff m).val :=
      map_sum toPS _ _
    rw [hsum_val, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, smul_eq_mul, smul_eq_mul,
      MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
    let m' : Fin (r + 1) →₀ ℕ := m + Finsupp.single j 1
    have hm'_ne : m' ≠ 0 := by
      intro h0
      have h1 : m' j = 0 := by rw [h0]; simp
      simp [m'] at h1
    have hval_mul : (polyToConv (P_branch α ω j.val) * (Q.coeff m' * ((m j : ConvergentPowerSeries) + 1))).val =
        ((P_branch α ω j.val : PowerSeries ℂ) * (Q.coeff m').val) * PowerSeries.C (((m j : ℂ) + 1)) := by
      change (P_branch α ω j.val : PowerSeries ℂ) *
          ((Q.coeff m').val * ((m j : PowerSeries ℂ) + 1)) = _
      have hcast : ((m j : PowerSeries ℂ) + 1) = PowerSeries.C ((m j : ℂ) + 1) := by
        simp [map_add, map_natCast, map_one]
      rw [hcast, mul_assoc]
    rw [hval_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (0, k₀)]
    · rw [Polynomial.coeff_coe, P_branch_coeff_zero α ω j.val, coeffW_coeff,
        ite_eq_right_iff.mpr (fun h => absurd h hm'_ne)]
      ring
    · intro ab hab hne_ab
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      have hlt : ab.2 < k₀ := by
        by_contra hge
        push Not at hge
        have ha0 : ab.1 = 0 := by omega
        have hb0 : ab.2 = k₀ := by omega
        exact hne_ab (Prod.ext ha0 hb0)
      rw [hk₀_le m' hm'_ne ab.2 hlt, mul_zero]
    · intro hnot
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal (a := (0, k₀)).mpr (zero_add k₀)) hnot
  rw [← h_expand, hL_coeff]

/-- Complex Vandermonde contradiction over `ℂ{w}`: if `L_conv α r (ω n) Q = 0` for `r + 1`
pairwise distinct frequencies `ω : Fin (r + 1) → ℂ`, then `Q` cannot have positive `Y`-total-degree. -/
theorem L_conv_vandermonde_contradiction (α : ℝ) {r : ℕ}
    (ω : Fin (r + 1) → ℂ) (hω_inj : Function.Injective ω)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hpos : 0 < Q.totalDegree)
    (hL : ∀ n : Fin (r + 1), L_conv α r (ω n) Q = 0) : False := by
  let P : MvPolynomial (Fin (r + 1)) ℂ := coeffW (minNonConstWOrd Q) Q
  have hP_pos : 0 < P.totalDegree := coeffW_minNonConstWOrd_pos_deg Q hpos
  have hD : ∀ n : Fin (r + 1), D_freq r (ω n) P = 0 := fun n =>
    D_freq_coeffW_of_L_conv_eq_zero α (ω n) Q hpos (hL n)
  let V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.vandermonde (fun n => -ω n)
  have hV_det : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    exact hω_inj (neg_inj.mp hab)
  have hpart : ∀ j : Fin (r + 1), MvPolynomial.pderiv j P = 0 := by
    intro j
    ext m
    change (MvPolynomial.pderiv j P).coeff m = 0
    let x : Fin (r + 1) → ℂ := fun k => (MvPolynomial.pderiv k P).coeff m
    have hVx : V.mulVec x = 0 := by
      ext n
      simp only [Matrix.mulVec, dotProduct, V, Matrix.vandermonde_apply, Pi.zero_apply, x]
      have h0 : (D_freq r (ω n) P).coeff m = 0 := by rw [hD n]; rfl
      unfold D_freq at h0
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at h0
      rw [MvPolynomial.coeff_sum] at h0
      simpa only [MvPolynomial.coeff_smul, smul_eq_mul] using h0
    have hx0 : x = 0 := by
      have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hV_det)
      calc x = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ).mulVec x := (Matrix.one_mulVec x).symm
        _ = (V⁻¹ * V).mulVec x := by rw [hinv]
        _ = V⁻¹.mulVec (V.mulVec x) := (Matrix.mulVec_mulVec x V⁻¹ V).symm
        _ = V⁻¹.mulVec 0 := by rw [hVx]
        _ = 0 := Matrix.mulVec_zero _
    exact congr_fun hx0 j
  have hPC : P = MvPolynomial.C (P.coeff 0) := by
    ext m
    rw [MvPolynomial.coeff_C]
    by_cases hm : m = 0
    · subst hm; simp
    · simp only [Ne.symm hm, ↓reduceIte]
      have hex : ∃ j : Fin (r + 1), m j ≠ 0 := by
        by_contra h
        push Not at h
        exact hm (Finsupp.ext h)
      obtain ⟨j, hj⟩ := hex
      let m' : Fin (r + 1) →₀ ℕ := m - Finsupp.single j 1
      have hpj := congr_arg (fun q : MvPolynomial (Fin (r + 1)) ℂ => q.coeff m') (hpart j)
      rw [MvPolynomial.coeff_pderiv] at hpj
      have h0 : (0 : MvPolynomial (Fin (r + 1)) ℂ).coeff m' = 0 := by simp
      rw [h0] at hpj
      have hsub : m' + Finsupp.single j 1 = m := by
        ext k
        dsimp only [m']
        by_cases hk : j = k
        · subst hk; simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, hk, ↓reduceIte,
            Nat.sub_zero, add_zero]
      rw [hsub] at hpj
      have hcast : ((m' j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' j)
      exact (mul_eq_zero.mp hpj).resolve_right hcast
  have hP0 : P.totalDegree = 0 := by rw [hPC]; exact MvPolynomial.totalDegree_C _
  omega

/-! #### 3C. Convergent Branch-Point Stokes–Vandermonde Engine & `abelConv_no_conv_ade` -/

/-- Analytic package for `ℂ{w}`-coefficient branch-point Stokes–Vandermonde descent. -/
structure ConvBranchPointStokesData (S : PowerSeries ℂ) (α : ℝ) (ω : ℕ → ℝ) (c : ℕ → ℂ) where
  ω_pos : 0 < ω 0
  ω_mono : StrictMono ω
  c_ne_zero : ∀ m : ℕ, c m ≠ 0
  g_pos : ℝ → ℂ
  g_neg : ℝ → ℂ
  g_pos_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j g_pos) (d_u^[j] S)
  g_neg_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j g_neg) (d_u^[j] S)
  conv_borel_transfer : ∀ {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries),
    formalEvalConv S Q = 0 →
      (∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u)
          (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) ∧
      (∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_neg u)
          (evalConvMvPoly Q (u : ℂ)⁻¹) = 0)
  stokes_jump : ∀ n j : ℕ, ∃ R' : ℝ, ω n < R' ∧ ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
    ‖iteratedDeriv j g_neg u - iteratedDeriv j g_pos u -
      ∑ m ∈ Finset.range (n + 1), c m * iteratedDeriv j (branchMode α (ω m : ℂ)) u‖ ≤
      C * Real.exp (-R' * u)

private lemma pow_mul_exp_neg_le_oneC (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, u ^ k * Real.exp (-δ * u) ≤ 1 := by
  have h1 : ∀ u : ℝ, 0 < u → u ^ k * Real.exp (-δ * u) ≤
      ((k + 1).factorial : ℝ) / (δ ^ (k + 1) * u) := by
    intro u hu_pos
    have hterm := Real.pow_div_factorial_le_exp (δ * u) (mul_nonneg hδ.le hu_pos.le) (k + 1)
    have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hexp : 0 < Real.exp (δ * u) := Real.exp_pos _
    rw [mul_pow, div_le_iff₀ hfac] at hterm
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexp (by positivity)]
    calc u ^ k * (δ ^ (k + 1) * u) = δ ^ (k + 1) * u ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ Real.exp (δ * u) * ((k + 1).factorial : ℝ) := hterm
      _ = ((k + 1).factorial : ℝ) * Real.exp (δ * u) := mul_comm _ _
  let B : ℝ := ((k + 1).factorial : ℝ) / δ ^ (k + 1) + 1
  filter_upwards [eventually_ge_atTop B] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le (by positivity : 0 < B) hu
  refine (h1 u hu_pos).trans ?_
  rw [div_le_one (by positivity)]
  have hdiv : ((k + 1).factorial : ℝ) / δ ^ (k + 1) ≤ u := by linarith
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ (k + 1))).mp hdiv |>.trans_eq (mul_comm _ _)

private lemma rpow_le_pow_of_ge_oneC (β : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    Real.rpow u β ≤ u ^ (Nat.ceil (max β 0)) := by
  have hle : β ≤ (Nat.ceil (max β 0) : ℝ) := (le_max_left β 0).trans (Nat.le_ceil _)
  calc Real.rpow u β ≤ Real.rpow u (Nat.ceil (max β 0) : ℝ) := Real.rpow_le_rpow_of_exponent_le hu hle
    _ = u ^ (Nat.ceil (max β 0)) := Real.rpow_natCast u _

private lemma norm_branchModeC (α : ℝ) (ω : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖branchMode α (ω : ℂ) u‖ = Real.rpow u (-α) * Real.exp (-ω * u) := by
  unfold branchMode
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hrp : 0 < Real.rpow u (-α) := Real.rpow_pos_of_pos hu (-α)
  rw [abs_of_pos hrp]
  congr 1; simp [Complex.mul_re]

private lemma P_branch_eval_inv_bdd (α : ℝ) (ω : ℂ) (j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    ‖(P_branch α ω j).eval (u : ℂ)⁻¹‖ ≤ ∑ k ∈ Finset.range (j + 1), ‖(P_branch α ω j).coeff k‖ := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hdeg : (P_branch α ω j).natDegree < j + 1 := Nat.lt_succ_of_le (P_branch_natDegree_le α ω j)
  rw [Polynomial.eval_eq_sum_range' hdeg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le]
  have hinv : u⁻¹ ^ k ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hu0.le) (inv_le_one_of_one_le₀ hu)
  calc ‖(P_branch α ω j).coeff k‖ * u⁻¹ ^ k ≤ ‖(P_branch α ω j).coeff k‖ * 1 :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = ‖(P_branch α ω j).coeff k‖ := mul_one _

private lemma HasAsympExp.eventually_bddC {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp f S) : ∃ B : ℝ, ∀ᶠ u : ℝ in atTop, ‖f u‖ ≤ B := by
  obtain ⟨C, hC⟩ := hf 1
  refine ⟨‖PowerSeries.coeff 0 S‖ + max C 0, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with u hu hu1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one] at hu
  have h1 : ‖f u‖ ≤ ‖f u - PowerSeries.coeff 0 S‖ + ‖PowerSeries.coeff 0 S‖ := by
    simpa [sub_add_cancel] using norm_add_le (f u - PowerSeries.coeff 0 S) (PowerSeries.coeff 0 S)
  have h2 : C / u ≤ max C 0 := by
    calc C / u ≤ max C 0 / u := div_le_div_of_nonneg_right (le_max_left C 0) (by linarith)
      _ ≤ max C 0 / 1 := div_le_div_of_nonneg_left (le_max_right C 0) zero_lt_one hu1
      _ = max C 0 := div_one _
  linarith

private lemma formalEvalConv_eq_zero_of_exp_small {S : PowerSeries ℂ} {f : ℝ → ℂ}
    (hf : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] S))
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    {δ : ℝ} (hδ : 0 < δ) {C : ℝ}
    (hbound : ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u)
        (evalConvMvPoly Q (u : ℂ)⁻¹)‖ ≤ C * Real.exp (-δ * u)) :
    formalEvalConv S Q = 0 := by
  have hexp : HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u)
        (evalConvMvPoly Q (u : ℂ)⁻¹))
      (formalEvalConv S Q) :=
    HasAsympExp.mvPolynomial_evalConv (fun j => hf j.val) Q
  refine hexp.eq_zero_of_flat fun M => ⟨max C 0, ?_⟩
  filter_upwards [hbound, pow_mul_exp_neg_le_oneC M hδ, eventually_ge_atTop (1 : ℝ)] with u hu hpe hu1
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  refine hu.trans ?_
  rw [le_div_iff₀ (pow_pos hu0 M)]
  calc C * Real.exp (-δ * u) * u ^ M
      ≤ max C 0 * Real.exp (-δ * u) * u ^ M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le) (by positivity)
    _ = max C 0 * (u ^ M * Real.exp (-δ * u)) := by ring
    _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hpe (le_max_right C 0)
    _ = max C 0 := mul_one _

/-- **Main Engine (`ℂ{w}`-Coefficient Branch-Point Stokes–Vandermonde Theorem)**:
Any formal series `S ∈ ℂ[[1/u]]` equipped with `ConvBranchPointStokesData S α ω c` satisfies
NO nonzero differential equation over `ConvergentPowerSeries` (`ℂ{w}`). -/
theorem conv_branchPoint_stokes_vandermonde_no_ade
    {S : PowerSeries ℂ} {α : ℝ} {ω : ℕ → ℝ} {c : ℕ → ℂ}
    (h : ConvBranchPointStokesData S α ω c)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv S Q = 0) : Q = 0 := by
  classical
  by_contra hQ_ne
  have hex : ∃ d : ℕ, ∃ P : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      P.totalDegree = d ∧ P ≠ 0 ∧ formalEvalConv S P = 0 :=
    ⟨Q.totalDegree, Q, rfl, hQ_ne, hQ⟩
  let Qmin := Classical.choose (Nat.find_spec hex)
  have hQmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hQmin_deg : Qmin.totalDegree = Nat.find hex := hQmin_spec.1
  have hQmin_ne : Qmin ≠ 0 := hQmin_spec.2.1
  have hQmin_zero : formalEvalConv S Qmin = 0 := hQmin_spec.2.2
  have hQmin_min : ∀ P : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      P ≠ 0 → P.totalDegree < Qmin.totalDegree → formalEvalConv S P ≠ 0 := by
    intro P hP_ne hP_deg hP_zero
    rw [hQmin_deg] at hP_deg
    exact Nat.find_min hex hP_deg ⟨P, rfl, hP_ne, hP_zero⟩
  have hQmin_pos_deg : 0 < Qmin.totalDegree := by
    by_contra! hle
    have h0 : Qmin.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev0 : formalEvalConv S
        (MvPolynomial.C (Qmin.coeff 0) : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) = 0 := by
      rw [← hC]; exact hQmin_zero
    have hp0 : toPS (Qmin.coeff 0) = 0 := by simpa [formalEvalConv] using hev0
    have hcoeff0 : Qmin.coeff 0 = 0 := toPS_injective (hp0.trans (map_zero toPS).symm)
    exact hQmin_ne (hC.trans (by rw [hcoeff0, map_zero]))
  have hω_pos : ∀ m : ℕ, 0 < ω m := fun m =>
    lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
  obtain ⟨hQ_pos, hQ_neg⟩ := h.conv_borel_transfer Qmin hQmin_zero
  -- Strong induction: L_conv α r (ω n) Qmin = 0 for all n < r + 1
  have hL_zero : ∀ n : ℕ, n < r + 1 → L_conv α r (ω n : ℂ) Qmin = 0 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      have h_prev : ∀ m < n, L_conv α r (ω m : ℂ) Qmin = 0 := fun m hm =>
        ih m hm (lt_trans hm hn)
      have h_shift_ev := eval_shift_of_L_conv_eq_zero α (fun k => (ω k : ℂ)) Qmin n h_prev
      have hL_eval_ev := evalConvMvPoly_L_conv_eventually α (ω n : ℂ) Qmin
      choose Bg hBg using fun j : Fin (r + 1) => HasAsympExp.eventually_bddC (h.g_pos_asymp j.val)
      have h_all_bg : ∀ᶠ u in atTop, ∀ j : Fin (r + 1), ‖iteratedDeriv j.val h.g_pos u‖ ≤ Bg j :=
        Filter.eventually_all.mpr hBg
      let M_p : ℝ := ∑ j : Fin (r + 1), ∑ k ∈ Finset.range (j.val + 1),
        ‖(P_branch α (ω n : ℂ) j.val).coeff k‖
      let M : ℝ := 2 + (∑ j : Fin (r + 1), |Bg j|) + M_p
      have hM_nonneg : 0 ≤ M := by
        have h1 : 0 ≤ ∑ j : Fin (r + 1), |Bg j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have h2 : 0 ≤ M_p := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        dsimp only [M]; linarith
      have hBg_le : ∀ j : Fin (r + 1), |Bg j| + 2 ≤ M := fun j => by
        have hs : |Bg j| ≤ ∑ i : Fin (r + 1), |Bg i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (Bg i)) (Finset.mem_univ j)
        have h2 : 0 ≤ M_p := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        dsimp only [M]; linarith
      have hv_bdd : ∀ u : ℝ, 1 ≤ u → ∀ j : Fin (r + 1),
          ‖(P_branch α (ω n : ℂ) j.val).eval (u : ℂ)⁻¹‖ ≤ M := fun u hu j => by
        have h1 := P_branch_eval_inv_bdd α (ω n : ℂ) j.val hu
        have h2 : ∑ k ∈ Finset.range (j.val + 1), ‖(P_branch α (ω n : ℂ) j.val).coeff k‖ ≤ M_p :=
          Finset.single_le_sum
            (f := fun j' : Fin (r + 1) => ∑ k ∈ Finset.range (j'.val + 1),
              ‖(P_branch α (ω n : ℂ) j'.val).coeff k‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
        have h3 : 0 ≤ ∑ i : Fin (r + 1), |Bg i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp only [M]; linarith
      choose R_j hR_j_gt C_j h_jump_j using fun j : Fin (r + 1) => h.stokes_jump n j.val
      let R' : ℝ := Finset.univ.inf' Finset.univ_nonempty R_j
      have hR'_gt : ω n < R' := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun j _ => hR_j_gt j
      have hR'_le : ∀ j : Fin (r + 1), R' ≤ R_j j := fun j => Finset.inf'_le R_j (Finset.mem_univ j)
      have hR'_pos : 0 < R' := lt_trans (hω_pos n) hR'_gt
      let C_rem : ℝ := ∑ j : Fin (r + 1), max (C_j j) 0
      have hC_rem_nonneg : 0 ≤ C_rem := Finset.sum_nonneg fun _ _ => le_max_right _ _
      have h_all_jump : ∀ᶠ u in atTop, ∀ j : Fin (r + 1),
          ‖iteratedDeriv j.val h.g_neg u - iteratedDeriv j.val h.g_pos u -
            ∑ m ∈ Finset.range (n + 1), c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖ ≤
            C_rem * Real.exp (-R' * u) := by
        filter_upwards [Filter.eventually_all.mpr h_jump_j, eventually_ge_atTop (0 : ℝ)] with u hu hu0 j
        refine (hu j).trans ?_
        have hexp_le : Real.exp (-R_j j * u) ≤ Real.exp (-R' * u) :=
          Real.exp_le_exp.mpr (by nlinarith [hR'_le j])
        calc C_j j * Real.exp (-R_j j * u)
            ≤ max (C_j j) 0 * Real.exp (-R_j j * u) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ max (C_j j) 0 * Real.exp (-R' * u) :=
              mul_le_mul_of_nonneg_left hexp_le (le_max_right _ _)
          _ ≤ C_rem * Real.exp (-R' * u) :=
              mul_le_mul_of_nonneg_right
                (Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j))
                (Real.exp_pos _).le
      -- Bound finite Stokes sum ≤ 1 eventually
      have hS_le1 : ∀ᶠ u : ℝ in atTop, ∀ j : Fin (r + 1),
          ‖∑ m ∈ Finset.range (n + 1), c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖ ≤ 1 := by
        have hterm : ∀ j : Fin (r + 1), ∀ m ∈ Finset.range (n + 1),
            ∀ᶠ u : ℝ in atTop,
              ‖c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
          intro j m _
          let Bp : ℝ := ∑ k ∈ Finset.range (j.val + 1), ‖(P_branch α (ω m : ℂ) j.val).coeff k‖
          let K : ℝ := (‖c m‖ * Bp + 1) * ((n + 1 : ℕ) : ℝ)
          let p : ℕ := Nat.ceil (max (-α) 0)
          filter_upwards [pow_mul_exp_neg_le_oneC (p + 1) (hω_pos m),
            eventually_ge_atTop (max K 1)] with u hpe huK
          have hu1 : 1 ≤ u := (le_max_right K 1).trans huK
          have huK' : K ≤ u := (le_max_left K 1).trans huK
          have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          rw [iteratedDeriv_branchMode α (ω m : ℂ) j.val u hu_pos,
            norm_mul, norm_mul, norm_branchModeC α (ω m) hu_pos]
          have hp_bd := P_branch_eval_inv_bdd α (ω m : ℂ) j.val hu1
          have hrp := rpow_le_pow_of_ge_oneC (-α) hu1
          have hBp_nn : 0 ≤ Bp := Finset.sum_nonneg fun _ _ => norm_nonneg _
          have h1 : ‖c m‖ * (Real.rpow u (-α) * Real.exp (-ω m * u)) *
              ‖(P_branch α (ω m : ℂ) j.val).eval (u : ℂ)⁻¹‖ ≤
              (‖c m‖ * Bp + 1) * (u ^ p * Real.exp (-ω m * u)) := by
            calc ‖c m‖ * (Real.rpow u (-α) * Real.exp (-ω m * u)) *
                  ‖(P_branch α (ω m : ℂ) j.val).eval (u : ℂ)⁻¹‖
                ≤ ‖c m‖ * (u ^ p * Real.exp (-ω m * u)) * Bp := by
                  refine mul_le_mul ?_ hp_bd (norm_nonneg _) (by positivity)
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hrp (Real.exp_pos _).le) (norm_nonneg _)
              _ = (‖c m‖ * Bp) * (u ^ p * Real.exp (-ω m * u)) := by ring
              _ ≤ (‖c m‖ * Bp + 1) * (u ^ p * Real.exp (-ω m * u)) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          rw [← mul_assoc]
          refine h1.trans ?_
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
          have h2 : (‖c m‖ * Bp + 1) * (u ^ p * Real.exp (-ω m * u)) * ((n + 1 : ℕ) : ℝ) =
              K * (u ^ p * Real.exp (-ω m * u)) := by dsimp only [K]; ring
          rw [h2]
          calc K * (u ^ p * Real.exp (-ω m * u))
              ≤ u * (u ^ p * Real.exp (-ω m * u)) :=
                mul_le_mul_of_nonneg_right huK' (by positivity)
            _ = u ^ (p + 1) * Real.exp (-ω m * u) := by rw [pow_succ']; ring
            _ ≤ 1 := hpe
        have hall := Filter.eventually_all.mpr fun j : Fin (r + 1) =>
          (Filter.eventually_all_finset (Finset.range (n + 1))).mpr fun m hm => hterm j m hm
        filter_upwards [hall] with u hu j
        refine (norm_sum_le _ _).trans ?_
        calc ∑ m ∈ Finset.range (n + 1),
              ‖c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖
            ≤ ∑ _m ∈ Finset.range (n + 1), (1 / ((n + 1 : ℕ) : ℝ)) :=
              Finset.sum_le_sum fun m hm => hu j m hm
          _ = 1 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div,
                mul_inv_cancel₀ (by positivity)]
      -- Uniform bounds on convergent coefficients + Lipschitz & Taylor constants on Qmin.support
      choose Bc hBc_nn hBc_ev using fun β : Fin (r + 1) →₀ ℕ => evalConv_eventually_bdd (Qmin.coeff β)
      have h_all_bc : ∀ᶠ u : ℝ in atTop, ∀ β ∈ Qmin.support, ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹‖ ≤ Bc β :=
        (Filter.eventually_all_finset Qmin.support).mpr fun β _ => hBc_ev β
      choose C_lip_β hC_lip_β h_lip_β using fun β : Fin (r + 1) →₀ ℕ =>
        eval_lipschitz_of_bounded (MvPolynomial.monomial β (1 : ℂ)) hM_nonneg
      choose C_tay_β hC_tay_β h_tay_β using fun β : Fin (r + 1) →₀ ℕ =>
        eval_shift_taylor_bound (MvPolynomial.monomial β (1 : ℂ)) hM_nonneg
      let C_L : ℝ := ∑ β ∈ Qmin.support, Bc β * C_lip_β β
      let C_T : ℝ := ∑ β ∈ Qmin.support, Bc β * C_tay_β β
      have hC_L_nn : 0 ≤ C_L := Finset.sum_nonneg fun β _ => mul_nonneg (hBc_nn β) (hC_lip_β β)
      have hC_T_nn : 0 ≤ C_T := Finset.sum_nonneg fun β _ => mul_nonneg (hBc_nn β) (hC_tay_β β)
      let δ₀ : ℝ := min (ω n) (R' - ω n)
      have hδ₀_pos : 0 < δ₀ := lt_min (hω_pos n) (sub_pos.mpr hR'_gt)
      let p_neg : ℕ := Nat.ceil (max (-α) 0)
      let p_pos : ℕ := Nat.ceil (max α 0)
      have hcn_pos : 0 < ‖c n‖ := norm_pos_iff.mpr (h.c_ne_zero n)
      have ha_small : ∀ᶠ u : ℝ in atTop, ‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u) ≤ 1 := by
        filter_upwards [pow_mul_exp_neg_le_oneC (p_neg + 1) (hω_pos n),
          eventually_ge_atTop (max ‖c n‖ 1)] with u hpe huK
        have hu1 : 1 ≤ u := (le_max_right _ _).trans huK
        have huc : ‖c n‖ ≤ u := (le_max_left _ _).trans huK
        calc ‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u)
            ≤ u * u ^ p_neg * Real.exp (-ω n * u) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              exact mul_le_mul huc (rpow_le_pow_of_ge_oneC (-α) hu1)
                (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hu1) _).le (by linarith)
          _ = u ^ (p_neg + 1) * Real.exp (-ω n * u) := by rw [pow_succ']
          _ ≤ 1 := hpe
      have hrem_small : ∀ᶠ u : ℝ in atTop, C_rem * Real.exp (-R' * u) ≤ 1 := by
        filter_upwards [pow_mul_exp_neg_le_oneC 1 hR'_pos,
          eventually_ge_atTop (max C_rem 1)] with u hpe huK
        have huC : C_rem ≤ u := (le_max_left _ _).trans huK
        calc C_rem * Real.exp (-R' * u) ≤ u ^ 1 * Real.exp (-R' * u) := by
              rw [pow_one]; exact mul_le_mul_of_nonneg_right huC (Real.exp_pos _).le
          _ ≤ 1 := hpe
      have hu_poly_exp : ∀ᶠ u : ℝ in atTop,
          u ^ (p_pos + p_neg) * Real.exp (-(δ₀ / 2) * u) ≤ 1 :=
        pow_mul_exp_neg_le_oneC (p_pos + p_neg) (half_pos hδ₀_pos)
      let C_fin : ℝ := (C_L * C_rem) / ‖c n‖ + C_T * ‖c n‖
      have h_bridge_bound : ∀ᶠ u : ℝ in atTop,
          ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val h.g_pos u)
            (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹)‖ ≤
            C_fin * Real.exp (-(δ₀ / 2) * u) := by
        filter_upwards [h_all_bg, h_all_jump, hQ_pos, hQ_neg, hS_le1, ha_small, hrem_small,
          hu_poly_exp, h_shift_ev, hL_eval_ev, h_all_bc, eventually_ge_atTop (1 : ℝ)]
          with u hbg hjump hpos hneg hS1 ha1 hrem1 hpoly_u hshift hLev hbc hu1
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
        let x : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val h.g_pos u
        let Svec : Fin (r + 1) → ℂ := fun j => ∑ m ∈ Finset.range (n + 1),
          c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u
        let y : Fin (r + 1) → ℂ := fun j => x j + Svec j
        let z : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val h.g_neg u
        let a : ℂ := c n * branchMode α (ω n : ℂ) u
        let v : Fin (r + 1) → ℂ := fun j => (P_branch α (ω n : ℂ) j.val).eval (u : ℂ)⁻¹
        have hx_le : ∀ j, ‖x j‖ ≤ M := fun j =>
          (hbg j).trans ((le_abs_self _).trans (by linarith [hBg_le j]))
        have hy_le : ∀ j, ‖y j‖ ≤ M := fun j => by
          calc ‖y j‖ ≤ ‖x j‖ + ‖Svec j‖ := norm_add_le _ _
            _ ≤ |Bg j| + 1 := add_le_add ((hbg j).trans (le_abs_self _)) (hS1 j)
            _ ≤ M := by linarith [hBg_le j]
        have hzy_le : ∀ j, ‖z j - y j‖ ≤ C_rem * Real.exp (-R' * u) := fun j => by
          have hsub_eq : z j - y j = iteratedDeriv j.val h.g_neg u - iteratedDeriv j.val h.g_pos u - Svec j := by
            simp only [y, x, z]; ring
          rw [hsub_eq]; exact hjump j
        have hz_le : ∀ j, ‖z j‖ ≤ M := fun j => by
          have hid : z j = y j + (z j - y j) := by ring
          rw [hid]
          calc ‖y j + (z j - y j)‖ ≤ ‖y j‖ + ‖z j - y j‖ := norm_add_le _ _
            _ ≤ (|Bg j| + 1) + 1 :=
                add_le_add ((norm_add_le _ _).trans
                  (add_le_add ((hbg j).trans (le_abs_self _)) (hS1 j)))
                  ((hzy_le j).trans hrem1)
            _ ≤ M := by linarith [hBg_le j]
        have ha_norm : ‖a‖ = ‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u) := by
          simp only [a, norm_mul, norm_branchModeC α (ω n) hu_pos]; ring
        have ha_le1 : ‖a‖ ≤ 1 := by rw [ha_norm]; exact ha1
        have ha_pos : 0 < ‖a‖ := by
          rw [ha_norm]; exact mul_pos (mul_pos hcn_pos (Real.rpow_pos_of_pos hu_pos _)) (Real.exp_pos _)
        have hQmin_decomp : evalConvMvPoly Qmin (u : ℂ)⁻¹ =
            ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ • MvPolynomial.monomial β (1 : ℂ) := by
          unfold evalConvMvPoly
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        -- Step A: Lipschitz bound ‖Qmin(u⁻¹, y)‖ ≤ (C_L * C_rem) * exp(-R' * u)
        have h_lip_y : ‖MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹)‖ ≤
            (C_L * C_rem) * Real.exp (-R' * u) := by
          have hyz : MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹) =
              ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                (MvPolynomial.eval y (MvPolynomial.monomial β (1 : ℂ)) -
                  MvPolynomial.eval z (MvPolynomial.monomial β (1 : ℂ))) := by
            have hneg' : MvPolynomial.eval z (evalConvMvPoly Qmin (u : ℂ)⁻¹) = 0 := hneg
            rw [← sub_zero (MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹)), ← hneg',
              hQmin_decomp]
            simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
              ← Finset.sum_sub_distrib, ← mul_sub]
          rw [hyz]
          calc ‖∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                  (MvPolynomial.eval y (MvPolynomial.monomial β 1) -
                    MvPolynomial.eval z (MvPolynomial.monomial β 1))‖
              ≤ ∑ β ∈ Qmin.support,
                  ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                    (MvPolynomial.eval y (MvPolynomial.monomial β 1) -
                      MvPolynomial.eval z (MvPolynomial.monomial β 1))‖ := norm_sum_le _ _
            _ ≤ ∑ β ∈ Qmin.support, Bc β * (C_lip_β β * (C_rem * Real.exp (-R' * u))) := by
                refine Finset.sum_le_sum fun β hβ => ?_
                rw [norm_mul]
                have hlk := h_lip_β β z y (C_rem * Real.exp (-R' * u))
                  (mul_nonneg hC_rem_nonneg (Real.exp_pos _).le) hz_le hy_le hzy_le
                rw [norm_sub_rev] at hlk
                exact mul_le_mul (hbc β hβ) hlk (norm_nonneg _) (hBc_nn β)
            _ = (C_L * C_rem) * Real.exp (-R' * u) := by
                have h1 : ∀ β ∈ Qmin.support,
                    Bc β * (C_lip_β β * (C_rem * Real.exp (-R' * u))) =
                    (Bc β * C_lip_β β) * (C_rem * Real.exp (-R' * u)) := fun β _ => (mul_assoc _ _ _).symm
                rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← mul_assoc]
        -- Step B: Exact shift invariance removes all modes m < n
        have h_shift_y : MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹) =
            MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) := by
          have hy_split : y = fun j : Fin (r + 1) =>
              (x j + a * v j) + ∑ m ∈ Finset.range n,
                (c m * branchMode α (ω m : ℂ) u) * (P_branch α (ω m : ℂ) j.val).eval (u : ℂ)⁻¹ := by
            funext j
            simp only [y, Svec, a, v]
            rw [Finset.sum_range_succ, iteratedDeriv_branchMode α (ω n : ℂ) j.val u hu_pos]
            have hinner : ∑ m ∈ Finset.range n, c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u =
                ∑ m ∈ Finset.range n, (c m * branchMode α (ω m : ℂ) u) *
                  (P_branch α (ω m : ℂ) j.val).eval (u : ℂ)⁻¹ := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [iteratedDeriv_branchMode α (ω m : ℂ) j.val u hu_pos]; ring
            rw [hinner]; ring
          rw [hy_split]
          exact hshift (fun m => c m * branchMode α (ω m : ℂ) u) (fun j => x j + a * v j)
        -- Step C: Multivariate Taylor bound
        have h_lin_eq : ∑ j : Fin (r + 1),
            MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
            MvPolynomial.eval x (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹) := by
          rw [hLev, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
          dsimp only [v]; ring
        have h_tay_y : ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
            a * MvPolynomial.eval x (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹)‖ ≤
            C_T * ‖a‖ ^ 2 := by
          have hpos' : MvPolynomial.eval x (evalConvMvPoly Qmin (u : ℂ)⁻¹) = 0 := hpos
          rw [← h_lin_eq]
          have hdecomp : MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
              a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
              ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                (MvPolynomial.eval (fun j => x j + a * v j) (MvPolynomial.monomial β 1) -
                  MvPolynomial.eval x (MvPolynomial.monomial β 1) -
                  a * ∑ j : Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv j (MvPolynomial.monomial β 1)) * v j) := by
            have h1 : MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                MvPolynomial.eval x (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
                MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                  a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j := by
              rw [hpos', sub_zero]
            rw [← h1]
            have hpd : ∀ j : Fin (r + 1),
                MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹) =
                ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ •
                  MvPolynomial.pderiv j (MvPolynomial.monomial β (1 : ℂ)) := by
              intro j
              rw [hQmin_decomp, map_sum]
              refine Finset.sum_congr rfl fun β _ => ?_
              rw [Derivation.map_smul_of_tower]
            have hsum_3 : a * ∑ j : Fin (r + 1),
                MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
                ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                  (a * ∑ j : Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv j (MvPolynomial.monomial β 1)) * v j) := by
              simp_rw [hpd, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
                Finset.sum_mul]
              rw [Finset.mul_sum]
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun j _ => by ring
            rw [hsum_3, hQmin_decomp]
            simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
              ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun β _ => by ring
          rw [hdecomp]
          calc ‖∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                  (MvPolynomial.eval (fun j => x j + a * v j) (MvPolynomial.monomial β 1) -
                    MvPolynomial.eval x (MvPolynomial.monomial β 1) -
                    a * ∑ j : Fin (r + 1),
                      MvPolynomial.eval x (MvPolynomial.pderiv j (MvPolynomial.monomial β 1)) * v j)‖
              ≤ ∑ β ∈ Qmin.support, ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹ * _‖ := norm_sum_le _ _
            _ ≤ ∑ β ∈ Qmin.support, Bc β * (C_tay_β β * ‖a‖ ^ 2) := by
                refine Finset.sum_le_sum fun β hβ => ?_
                rw [norm_mul]
                exact mul_le_mul (hbc β hβ) (h_tay_β β x v a hx_le (hv_bdd u hu1) ha_le1)
                  (norm_nonneg _) (hBc_nn β)
            _ = C_T * ‖a‖ ^ 2 := by
                dsimp only [C_T]; rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun β _ => by ring
        -- Step D: Triangle inequality & divide by ‖a‖
        have h_comb : ‖a‖ *
            ‖MvPolynomial.eval x (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹)‖ ≤
            (C_L * C_rem) * Real.exp (-R' * u) + C_T * ‖a‖ ^ 2 := by
          rw [← norm_mul]
          have htri : ‖a * MvPolynomial.eval x (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹)‖ ≤
              ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹)‖ +
              ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                a * MvPolynomial.eval x (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹)‖ := by
            simpa [sub_sub_cancel] using norm_sub_le
              (MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹))
              (MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                a * MvPolynomial.eval x (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹))
          have h_lip_av : ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹)‖ ≤
              (C_L * C_rem) * Real.exp (-R' * u) := by rwa [← h_shift_y]
          exact htri.trans (add_le_add h_lip_av h_tay_y)
        have h_div : ‖MvPolynomial.eval x (evalConvMvPoly (L_conv α r (ω n : ℂ) Qmin) (u : ℂ)⁻¹)‖ ≤
            ((C_L * C_rem) * Real.exp (-R' * u)) / ‖a‖ + C_T * ‖a‖ := by
          have hstep := (le_div_iff₀' ha_pos).mpr h_comb
          refine hstep.trans_eq ?_
          field_simp [ha_pos.ne']
        refine h_div.trans ?_
        have hrp_inv : (Real.rpow u (-α))⁻¹ = Real.rpow u α := by
          change (u ^ (-α))⁻¹ = u ^ α; rw [← Real.rpow_neg hu_pos.le, neg_neg]
        have hrp_pos_le : Real.rpow u α ≤ u ^ p_pos := rpow_le_pow_of_ge_oneC α hu1
        have hrp_neg_le : Real.rpow u (-α) ≤ u ^ p_neg := rpow_le_pow_of_ge_oneC (-α) hu1
        have hterm1 : ((C_L * C_rem) * Real.exp (-R' * u)) / ‖a‖ ≤
            ((C_L * C_rem) / ‖c n‖) * Real.exp (-(δ₀ / 2) * u) := by
          rw [ha_norm]
          have hrew : ((C_L * C_rem) * Real.exp (-R' * u)) /
              (‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u)) =
              ((C_L * C_rem) / ‖c n‖) * (Real.rpow u α * Real.exp (-(R' - ω n) * u)) := by
            have hexp_eq : Real.exp (-R' * u) =
                Real.exp (-(R' - ω n) * u) * Real.exp (-ω n * u) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [← hrp_inv, hexp_eq]
            field_simp [hcn_pos.ne', (Real.rpow_pos_of_pos hu_pos _).ne', (Real.exp_pos _).ne']
          rw [hrew]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpow_le : Real.rpow u α ≤ u ^ (p_pos + p_neg) :=
            hrp_pos_le.trans (pow_le_pow_right₀ hu1 (Nat.le_add_right _ _))
          have hexp_le : Real.exp (-(R' - ω n) * u) ≤ Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u) := by
            rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
            have hδle : δ₀ ≤ R' - ω n := min_le_right _ _
            nlinarith
          calc Real.rpow u α * Real.exp (-(R' - ω n) * u)
              ≤ u ^ (p_pos + p_neg) * (Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u)) :=
                mul_le_mul hpow_le hexp_le (Real.exp_pos _).le (by positivity)
            _ = (u ^ (p_pos + p_neg) * Real.exp (-(δ₀ / 2) * u)) * Real.exp (-(δ₀ / 2) * u) := by ring
            _ ≤ 1 * Real.exp (-(δ₀ / 2) * u) := mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le
            _ = Real.exp (-(δ₀ / 2) * u) := one_mul _
        have hterm2 : C_T * ‖a‖ ≤ (C_T * ‖c n‖) * Real.exp (-(δ₀ / 2) * u) := by
          rw [ha_norm]
          have hrew : C_T * (‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u)) =
              (C_T * ‖c n‖) * (Real.rpow u (-α) * Real.exp (-ω n * u)) := by ring
          rw [hrew]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpow_le : Real.rpow u (-α) ≤ u ^ (p_pos + p_neg) :=
            hrp_neg_le.trans (pow_le_pow_right₀ hu1 (Nat.le_add_left _ _))
          have hexp_le : Real.exp (-ω n * u) ≤ Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u) := by
            rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
            have hδle : δ₀ ≤ ω n := min_le_left _ _
            nlinarith
          calc Real.rpow u (-α) * Real.exp (-ω n * u)
              ≤ u ^ (p_pos + p_neg) * (Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u)) :=
                mul_le_mul hpow_le hexp_le (Real.exp_pos _).le (by positivity)
            _ = (u ^ (p_pos + p_neg) * Real.exp (-(δ₀ / 2) * u)) * Real.exp (-(δ₀ / 2) * u) := by ring
            _ ≤ 1 * Real.exp (-(δ₀ / 2) * u) := mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le
            _ = Real.exp (-(δ₀ / 2) * u) := one_mul _
        dsimp only [C_fin]
        linarith
      have hL_formal : formalEvalConv S (L_conv α r (ω n : ℂ) Qmin) = 0 :=
        formalEvalConv_eq_zero_of_exp_small h.g_pos_asymp (L_conv α r (ω n : ℂ) Qmin)
          (half_pos hδ₀_pos) h_bridge_bound
      by_contra hL_ne
      exact hQmin_min (L_conv α r (ω n : ℂ) Qmin) hL_ne
        (degree_L_conv_lt α (ω n : ℂ) Qmin hQmin_pos_deg) hL_formal
  have hω_inj : Function.Injective (fun n : Fin (r + 1) => (ω n.val : ℂ)) := by
    intro a b hab
    exact Fin.ext (h.ω_mono.injective (Complex.ofReal_injective hab))
  exact L_conv_vandermonde_contradiction α (fun n : Fin (r + 1) => (ω n.val : ℂ)) hω_inj
    Qmin hQmin_pos_deg (fun n => hL_zero n.val n.isLt)

/-- Complete `ConvBranchPointStokesData` for `formalSeries (abelConv ψ)` from any
positive-ray simple-pole meromorphic Borel kernel `ψ`. -/
def abelConv_convBranchPointStokesData {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    ConvBranchPointStokesData (formalSeries (abelConv ψ)) (1 / 2) ω (halfStokesCoeff ω res) where
  ω_pos := h.ω_pos
  ω_mono := h.ω_mono
  c_ne_zero := fun m => by
    unfold halfStokesCoeff
    have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    have hsq : ((Real.sqrt (Real.pi * ω m) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hωm)).ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hsq) (h.res_ne_zero m)
  g_pos := fun t => (aAbelC ψ).value (dPlusC h) (t : ℂ)
  g_neg := fun t => (aAbelC ψ).value (dMinusC h) (t : ℂ)
  g_pos_asymp := fun j =>
    minor_value_hasAsympExpC (aAbelC ψ) (wedgePlusC_domain (ε₀C_pos h)) (wedgePlusC_containsRay h)
      (aAbelC_good_plus h) (by rw [dPlusC_re h]; exact cos_pos_θC h) j
  g_neg_asymp := fun j =>
    minor_value_hasAsympExpC (aAbelC ψ) (wedgeMinusC_domain (ε₀C_pos h)) (wedgeMinusC_containsRay h)
      (aAbelC_good_minus h) (by rw [dMinusC_re h]; exact cos_pos_θC h) j
  conv_borel_transfer := fun Q hQ => abelConv_conv_borel_transfer h Q hQ
  stokes_jump := fun n j => abelConv_stokes_jumpC h n j

/-- **Unconditional `ℂ{w}`-Differential Transcendence of `formalSeries (abelConv ψ)`**:
For any positive-ray simple-pole meromorphic Borel kernel `ψ`, `formalSeries (abelConv ψ)`
satisfies NO nonzero algebraic differential equation over `ConvergentPowerSeries` (`ℂ{w}`). -/
theorem abelConv_no_conv_ade {ψ ω res} (h : MeromorphicBorelData ψ ω res)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries (abelConv ψ)) Q = 0) : Q = 0 :=
  conv_branchPoint_stokes_vandermonde_no_ade (abelConv_convBranchPointStokesData h) Q hQ

/-! ### 4. Invertible Triangular Transfers & Strong D-Transcendence over `ℂ({x})` -/

/-! #### 4A. Universal Invertible Triangular Substitution Lemma -/

private lemma aeval_congr_vars {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {p : MvPolynomial σ R} {f g : σ → A} (h : ∀ i ∈ p.vars, f i = g i) :
    MvPolynomial.aeval f p = MvPolynomial.aeval g p := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩)]

private lemma eval₂Hom_congr_varsC {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {p : MvPolynomial σ R} {f g : σ → S} (h : ∀ i ∈ p.vars, f i = g i) :
    MvPolynomial.eval₂Hom φ f p = MvPolynomial.eval₂Hom φ g p := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩)]

/-- **Invertible Triangular Substitution Theorem**:
Any `R`-algebra endomorphism `MvPolynomial.aeval g` of `MvPolynomial (Fin (r + 1)) R` that is
lower-triangular with unit diagonal (`g j = C (u j) * X j + S j`, `IsUnit (u j)`, and
`∀ k ∈ (S j).vars, k.val < j.val`) has an explicit left inverse and is therefore injective. -/
theorem triangular_aeval_injective {R : Type*} [CommRing R] {r : ℕ}
    (g : Fin (r + 1) → MvPolynomial (Fin (r + 1)) R)
    (u : Fin (r + 1) → R) (hu : ∀ j, IsUnit (u j))
    (S : Fin (r + 1) → MvPolynomial (Fin (r + 1)) R)
    (hg : ∀ j, g j = MvPolynomial.C (u j) * MvPolynomial.X j + S j)
    (hS : ∀ j, ∀ k ∈ (S j).vars, k.val < j.val) :
    Function.Injective
      (MvPolynomial.aeval g : MvPolynomial (Fin (r + 1)) R →ₐ[R] MvPolynomial (Fin (r + 1)) R) := by
  let invImgAux : ℕ → Fin (r + 1) → MvPolynomial (Fin (r + 1)) R :=
    Nat.rec (fun _ => 0) fun n prev j =>
      if j.val < n then prev j
      else MvPolynomial.C (↑((hu j).unit⁻¹) : R) * (MvPolynomial.X j - MvPolynomial.aeval prev (S j))
  have hstab : ∀ m n (j : Fin (r + 1)), j.val < n → n ≤ m → invImgAux m j = invImgAux n j := by
    intro m
    induction m with
    | zero =>
      intro n j hjn hnm
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst hn0; exact absurd hjn (Nat.not_lt_zero _)
    | succ m ih =>
      intro n j hjn hnm
      rcases eq_or_lt_of_le hnm with rfl | hlt
      · rfl
      · have hnm' : n ≤ m := Nat.le_of_lt_succ hlt
        have hjm : j.val < m := lt_of_lt_of_le hjn hnm'
        change (if j.val < m then invImgAux m j else _) = invImgAux n j
        simp only [hjm, ↓reduceIte]
        exact ih n j hjn hnm'
  let h : Fin (r + 1) → MvPolynomial (Fin (r + 1)) R := invImgAux (r + 1)
  have hleft : (MvPolynomial.aeval h).comp (MvPolynomial.aeval g) =
      AlgHom.id R (MvPolynomial (Fin (r + 1)) R) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X]
    rw [hg j, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
    have hj_eq : h j = MvPolynomial.C (↑((hu j).unit⁻¹) : R) *
        (MvPolynomial.X j - MvPolynomial.aeval (invImgAux j.val) (S j)) := by
      have hs := hstab (r + 1) (j.val + 1) j (Nat.lt_succ_self j.val) (Nat.succ_le_of_lt j.isLt)
      change invImgAux (r + 1) j = _
      rw [hs]
      change (if j.val < j.val then invImgAux j.val j
        else MvPolynomial.C (↑((hu j).unit⁻¹) : R) *
          (MvPolynomial.X j - MvPolynomial.aeval (invImgAux j.val) (S j))) = _
      simp only [lt_irrefl, ↓reduceIte]
    have hS_eq : MvPolynomial.aeval (invImgAux j.val) (S j) = MvPolynomial.aeval h (S j) :=
      aeval_congr_vars fun k hk =>
        (hstab (r + 1) j.val k (hS j k hk) (le_of_lt j.isLt)).symm
    rw [hj_eq, hS_eq, ← mul_assoc, ← map_mul, (hu j).mul_val_inv, map_one, one_mul, sub_add_cancel]
  intro P Q hPQ
  have h1 := congrArg (MvPolynomial.aeval h) hPQ
  have hP : MvPolynomial.aeval h (MvPolynomial.aeval g P) = P :=
    AlgHom.congr_fun hleft P
  have hQ : MvPolynomial.aeval h (MvPolynomial.aeval g Q) = Q :=
    AlgHom.congr_fun hleft Q
  rw [hP, hQ] at h1
  exact h1

/-! #### 4B. `X^2 * E → E` Convergent-Coefficient Transfer (`toXJetC`) -/

/-- Strong differential transcendence over the ring `ℂ{x}` of convergent power series at `0`:
`F` satisfies no nonzero algebraic differential equation with coefficients in `ConvergentPowerSeries`. -/
@[expose] def StronglyDTransOverConvergent (F : PowerSeries ℂ) : Prop :=
  ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries),
    MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet F j.val) P = 0 → P = 0

private def coeffDerivC (A : MvPolynomial ℕ (Polynomial ℂ)) : MvPolynomial ℕ (Polynomial ℂ) :=
  ∑ m ∈ A.support, MvPolynomial.monomial m (Polynomial.derivative (A.coeff m))

private lemma coeffDerivC_coeff (A : MvPolynomial ℕ (Polynomial ℂ)) (m : ℕ →₀ ℕ) :
    (coeffDerivC A).coeff m = Polynomial.derivative (A.coeff m) := by
  classical
  unfold coeffDerivC
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ A.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [hb]
    · intro hnot; exact absurd hm hnot
  · rw [Finset.sum_eq_zero (fun b hb => by simp [show b ≠ m from fun h => hm (h ▸ hb)]),
      MvPolynomial.notMem_support_iff.mp hm, map_zero]

private lemma coeffDerivC_C (p : Polynomial ℂ) :
    coeffDerivC (MvPolynomial.C p) = MvPolynomial.C (Polynomial.derivative p) := by
  apply MvPolynomial.ext; intro m
  rw [coeffDerivC_coeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs
  · rfl
  · simp

private lemma coeffDerivC_add (A B : MvPolynomial ℕ (Polynomial ℂ)) :
    coeffDerivC (A + B) = coeffDerivC A + coeffDerivC B := by
  apply MvPolynomial.ext; intro m
  simp only [coeffDerivC_coeff, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, map_add]

private lemma coeffDerivC_mul_X (A : MvPolynomial ℕ (Polynomial ℂ)) (i : ℕ) :
    coeffDerivC (A * MvPolynomial.X i) = coeffDerivC A * MvPolynomial.X i := by
  classical
  apply MvPolynomial.ext; intro m
  rw [coeffDerivC_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs
  · exact (coeffDerivC_coeff A _).symm
  · simp

private lemma coeffDerivC_vars_subset (A : MvPolynomial ℕ (Polynomial ℂ)) :
    (coeffDerivC A).vars ⊆ A.vars := by
  intro k hk
  rw [MvPolynomial.mem_vars_iff_mem_support] at hk ⊢
  obtain ⟨m, hm, hkm⟩ := hk
  refine ⟨m, ?_, hkm⟩
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [coeffDerivC_coeff] at hm
  intro h0; rw [h0, map_zero] at hm; exact hm rfl

private lemma vars_pderiv_subsetC {R : Type*} [CommSemiring R] (m : ℕ) (A : MvPolynomial ℕ R) :
    (MvPolynomial.pderiv m A).vars ⊆ A.vars := by
  intro k hk
  rw [MvPolynomial.mem_vars_iff_mem_support] at hk ⊢
  obtain ⟨d, hd, hkd⟩ := hk
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hd
  refine ⟨d + Finsupp.single m 1, MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hd), ?_⟩
  rw [Finsupp.mem_support_iff] at hkd ⊢
  simp only [Finsupp.coe_add, Pi.add_apply]; omega

private def dXOpC (A : MvPolynomial ℕ (Polynomial ℂ)) : MvPolynomial ℕ (Polynomial ℂ) :=
  MvPolynomial.C (-Polynomial.X ^ 2) * coeffDerivC A +
    ∑ k ∈ A.vars, MvPolynomial.pderiv k A * MvPolynomial.X (k + 1)

private def toXJetC : ℕ → MvPolynomial ℕ (Polynomial ℂ)
  | 0 => MvPolynomial.X 0
  | j + 1 => -dXOpC (toXJetC j) - MvPolynomial.C (Polynomial.C ((2 * j + 2 : ℕ) : ℂ) * Polynomial.X) * toXJetC j

private lemma d_u_eq_neg_X_sq_mul_derivC (f : PowerSeries ℂ) :
    d_u f = -(PowerSeries.X ^ 2 * PowerSeries.derivative f) := rfl

private lemma d_u_addC (f g : PowerSeries ℂ) : d_u (f + g) = d_u f + d_u g := by
  rw [d_u_eq_neg_X_sq_mul_derivC, d_u_eq_neg_X_sq_mul_derivC, d_u_eq_neg_X_sq_mul_derivC, map_add]; ring

private lemma d_u_mulC (f g : PowerSeries ℂ) : d_u (f * g) = d_u f * g + f * d_u g := by
  rw [d_u_eq_neg_X_sq_mul_derivC, d_u_eq_neg_X_sq_mul_derivC, d_u_eq_neg_X_sq_mul_derivC, Derivation.leibniz]
  simp only [smul_eq_mul]; ring

private lemma d_u_powC (f : PowerSeries ℂ) (k : ℕ) :
    d_u (f ^ k) = (k : ℂ) • (f ^ (k - 1) * d_u f) := by
  induction k with
  | zero =>
    rw [pow_zero, d_u_eq_neg_X_sq_mul_derivC, Derivation.map_one_eq_zero, mul_zero, neg_zero]; simp
  | succ k ih =>
    rw [pow_succ, d_u_mulC, ih]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, PowerSeries.smul_eq_C_mul]
      push_cast; simp only [map_add, map_natCast, map_one, pow_succ]; ring

private lemma d_u_coe_polyC (p : Polynomial ℂ) :
    d_u (p : PowerSeries ℂ) = -(PowerSeries.X ^ 2 * ((Polynomial.derivative p : Polynomial ℂ) : PowerSeries ℂ)) := by
  rw [d_u_eq_neg_X_sq_mul_derivC]; congr 2; ext n
  rw [PowerSeries.coeff_derivative, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_derivative]

private lemma dXOpC_eq_of_vars_subset (B : MvPolynomial ℕ (Polynomial ℂ)) (s : Finset ℕ) (hs : B.vars ⊆ s) :
    dXOpC B = MvPolynomial.C (-Polynomial.X ^ 2) * coeffDerivC B +
      ∑ k ∈ s, MvPolynomial.pderiv k B * MvPolynomial.X (k + 1) := by
  unfold dXOpC; congr 1
  refine Finset.sum_subset hs fun k _ hk => ?_
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hk, zero_mul]

private lemma dXOpC_add (A B : MvPolynomial ℕ (Polynomial ℂ)) :
    dXOpC (A + B) = dXOpC A + dXOpC B := by
  let s := (A + B).vars ∪ A.vars ∪ B.vars
  have hsAB : (A + B).vars ⊆ s := Finset.subset_union_left.trans Finset.subset_union_left
  have hsA : A.vars ⊆ s := Finset.subset_union_right.trans Finset.subset_union_left
  have hsB : B.vars ⊆ s := Finset.subset_union_right
  rw [dXOpC_eq_of_vars_subset (A + B) s hsAB, dXOpC_eq_of_vars_subset A s hsA,
    dXOpC_eq_of_vars_subset B s hsB, coeffDerivC_add, mul_add]
  have hsum : ∑ k ∈ s, MvPolynomial.pderiv k (A + B) * MvPolynomial.X (k + 1) =
      (∑ k ∈ s, MvPolynomial.pderiv k A * MvPolynomial.X (k + 1)) +
      (∑ k ∈ s, MvPolynomial.pderiv k B * MvPolynomial.X (k + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [map_add, add_mul]
  rw [hsum]; abel

private lemma evalX_dXOpC (S : PowerSeries ℂ) (A : MvPolynomial ℕ (Polynomial ℂ)) :
    d_u (MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun k => d_u^[k] S) A) =
      MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun k => d_u^[k] S) (dXOpC A) := by
  classical
  induction A using MvPolynomial.induction_on with
  | C p =>
    have hvars : (MvPolynomial.C p : MvPolynomial ℕ (Polynomial ℂ)).vars = ∅ := MvPolynomial.vars_C
    unfold dXOpC
    rw [hvars, Finset.sum_empty, add_zero, coeffDerivC_C, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, map_neg, map_pow,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_X]
    simpa [neg_mul] using d_u_coe_polyC p
  | add A B hA hB => rw [map_add, d_u_addC, hA, hB, dXOpC_add, map_add]
  | mul_X A i hA =>
    let s := insert i ((A * MvPolynomial.X i).vars ∪ A.vars)
    have hsAX : (A * MvPolynomial.X i).vars ⊆ s := Finset.subset_union_left.trans (Finset.subset_insert _ _)
    have hsA : A.vars ⊆ s := Finset.subset_union_right.trans (Finset.subset_insert _ _)
    have hi_s : i ∈ s := Finset.mem_insert_self _ _
    have hd_mulX : dXOpC (A * MvPolynomial.X i) = dXOpC A * MvPolynomial.X i + A * MvPolynomial.X (i + 1) := by
      rw [dXOpC_eq_of_vars_subset (A * MvPolynomial.X i) s hsAX, dXOpC_eq_of_vars_subset A s hsA,
        coeffDerivC_mul_X, ← mul_assoc, add_mul, Finset.sum_mul]
      have hsum : ∑ k ∈ s, MvPolynomial.pderiv k (A * MvPolynomial.X i) * MvPolynomial.X (k + 1) =
          (∑ k ∈ s, MvPolynomial.pderiv k A * MvPolynomial.X (k + 1) * MvPolynomial.X i) +
            A * MvPolynomial.X (i + 1) := by
        have hstep : ∀ k ∈ s, MvPolynomial.pderiv k (A * MvPolynomial.X i) * MvPolynomial.X (k + 1) =
            MvPolynomial.pderiv k A * MvPolynomial.X (k + 1) * MvPolynomial.X i +
              (if k = i then A * MvPolynomial.X (i + 1) else 0) := fun k _ => by
          rw [Derivation.leibniz, MvPolynomial.pderiv_X]; simp only [smul_eq_mul, Pi.single_apply]
          by_cases hki : k = i
          · subst hki; simp; ring
          · have hik : i ≠ k := Ne.symm hki; simp [hki, hik]; ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite_eq' s i,
          ite_eq_left_iff.mpr fun h => absurd hi_s h]
      rw [hsum]; ring
    rw [map_mul, d_u_mulC, hA, hd_mulX, map_add, map_mul, map_mul,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Function.iterate_succ_apply' d_u i S]

private lemma evalX_toXJetC (E : PowerSeries ℂ) (j : ℕ) :
    MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom
      (fun k => d_u^[k] (PowerSeries.X ^ 2 * E)) (toXJetC j) =
      PowerSeries.X ^ (2 * j + 2) * seriesJet E j := by
  induction j with
  | zero => simp [toXJetC, seriesJet]
  | succ j ih =>
    simp only [toXJetC, map_sub, map_neg, map_mul, MvPolynomial.eval₂Hom_C]
    rw [← evalX_dXOpC, ih, d_u_mulC]
    have hpow : d_u (PowerSeries.X ^ (2 * j + 2)) =
        -((2 * j + 2 : ℕ) : ℂ) • (PowerSeries.X ^ (2 * j + 3)) := by
      rw [d_u_powC, d_u_eq_neg_X_sq_mul_derivC, PowerSeries.derivative_X, mul_one]
      have hsub : 2 * j + 2 - 1 = 2 * j + 1 := by omega
      rw [hsub, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
      have hexp : (PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 1) * (-(PowerSeries.X : PowerSeries ℂ) ^ 2) =
          -((PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 3)) := by rw [mul_neg, ← pow_add]
      rw [hexp, map_neg]; ring
    have hder : d_u (seriesJet E j) = -(PowerSeries.X ^ 2 * seriesJet E (j + 1)) := by
      dsimp only [seriesJet]; rw [d_u_eq_neg_X_sq_mul_derivC, Function.iterate_succ_apply']
    rw [hpow, hder, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X,
      PowerSeries.smul_eq_C_mul]
    have h1 : (PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 2) * -(PowerSeries.X ^ 2 * seriesJet E (j + 1)) =
        -(PowerSeries.X ^ (2 * (j + 1) + 2) * seriesJet E (j + 1)) := by
      rw [mul_neg, ← mul_assoc, ← pow_add, show 2 * j + 2 + 2 = 2 * (j + 1) + 2 by omega]
    have h2 : (PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 3) = PowerSeries.X * PowerSeries.X ^ (2 * j + 2) := by
      rw [← pow_succ']
    rw [h1, h2]; push_cast; simp only [map_neg, map_add, map_mul, map_natCast, map_ofNat]; ring

private lemma toXJetC_triangular (j : ℕ) :
    ∃ R : MvPolynomial ℕ (Polynomial ℂ),
      (∀ k ∈ R.vars, k < j) ∧
      toXJetC j = MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X j + R := by
  induction j with
  | zero => exact ⟨0, by simp, by simp [toXJetC]⟩
  | succ j ih =>
    obtain ⟨R, hR_vars, hR_eq⟩ := ih
    let dR := dXOpC R
    have hdR_vars : ∀ k ∈ dR.vars, k < j + 1 := by
      intro k hk
      unfold dR dXOpC at hk
      rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hk) with h1 | h2
      · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h1) with hc | hd
        · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
        · exact Nat.lt_succ_of_lt (hR_vars k (coeffDerivC_vars_subset R hd))
      · obtain ⟨m, hm, hk_m⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ h2)
        rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk_m) with hm1 | hm2
        · exact Nat.lt_succ_of_lt (hR_vars k (vars_pderiv_subsetC m R hm1))
        · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hm2
          subst hm2; exact Nat.succ_lt_succ (hR_vars m hm)
    have hd_lead : dXOpC (MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X j) =
        MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X (j + 1) := by
      unfold dXOpC
      rw [coeffDerivC_mul_X, coeffDerivC_C, Polynomial.derivative_C, map_zero, zero_mul, mul_zero, zero_add]
      have hvars_sub : (MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X j).vars ⊆ {j} := by
        refine (MvPolynomial.vars_mul _ _).trans ?_
        rw [MvPolynomial.vars_C, MvPolynomial.vars_X, Finset.empty_union]
      rw [Finset.sum_subset hvars_sub (fun k _ hk => by
        rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hk, zero_mul]),
        Finset.sum_singleton, Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero,
        MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one]
    have hd_add : dXOpC (toXJetC j) =
        MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X (j + 1) + dR := by
      rw [hR_eq, dXOpC_add, hd_lead]
    let R' : MvPolynomial ℕ (Polynomial ℂ) :=
      -dR - MvPolynomial.C (Polynomial.C ((2 * j + 2 : ℕ) : ℂ) * Polynomial.X) * toXJetC j
    refine ⟨R', ?_, ?_⟩
    · intro k hk
      dsimp only [R'] at hk
      rcases Finset.mem_union.mp (MvPolynomial.vars_sub_subset (p := -dR) (q := _) hk) with h1 | h2
      · rw [MvPolynomial.vars_neg] at h1; exact hdR_vars k h1
      · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h2) with hc | ht
        · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
        · rw [hR_eq] at ht
          rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ ht) with ha | hb
          · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ ha) with hc2 | hx
            · exact absurd hc2 (by rw [MvPolynomial.vars_C]; simp)
            · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx; rw [hx]; exact Nat.lt_succ_self j
          · exact Nat.lt_succ_of_lt (hR_vars k hb)
    · dsimp only [toXJetC, R']
      rw [hd_add]
      have hpow : (MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ (j + 1))) : MvPolynomial ℕ (Polynomial ℂ)) =
          -MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) := by
        rw [pow_succ, mul_neg_one, map_neg, map_neg]
      rw [hpow]; ring

private lemma toXJetC_vars_le (j : ℕ) : ∀ k ∈ (toXJetC j).vars, k ≤ j := by
  obtain ⟨R, hR_vars, hR_eq⟩ := toXJetC_triangular j
  intro k hk
  rw [hR_eq] at hk
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hk) with h1 | h2
  · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h1) with hc | hx
    · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx; subst hx; exact le_rfl
  · exact le_of_lt (hR_vars k h2)

private def liftFinConv (r : ℕ) :
    MvPolynomial ℕ (Polynomial ℂ) →+* MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp polyToConv)
    (fun k => if hk : k < r + 1 then MvPolynomial.X ⟨k, hk⟩ else 0)

private lemma vars_liftFinConv_subset (r : ℕ) (q : MvPolynomial ℕ (Polynomial ℂ)) :
    ∀ i ∈ (liftFinConv r q).vars, i.val ∈ q.vars := by
  classical
  intro i hi
  rw [MvPolynomial.as_sum q, map_sum] at hi
  obtain ⟨m, hm, hi_m⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hi)
  have hmon : liftFinConv r (MvPolynomial.monomial m (q.coeff m)) =
      MvPolynomial.C (polyToConv (q.coeff m)) *
        m.prod fun n e => (if hn : n < r + 1 then MvPolynomial.X ⟨n, hn⟩ else 0) ^ e := by
    dsimp only [liftFinConv]
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]; rfl
  rw [hmon] at hi_m
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hi_m) with hc | hp
  · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
  · unfold Finsupp.prod at hp
    obtain ⟨n, hn, hi_n⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_prod _ hp)
    have hi_x : i ∈ (if h : n < r + 1 then
        (MvPolynomial.X ⟨n, h⟩ : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) else 0).vars :=
      MvPolynomial.vars_pow _ _ hi_n
    split_ifs at hi_x with hlt
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hi_x
      have hval : i.val = n := congrArg Fin.val hi_x
      rw [hval]
      exact (MvPolynomial.mem_vars_iff_mem_support n).mpr ⟨m, hm, hn⟩
    · simp at hi_x

private lemma invert_toXJetC_over_field {K : Type*} [Field K]
    (alg : ConvergentPowerSeries →+* K) (halg_inj : Function.Injective alg)
    {r M : ℕ} (P : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (wt : (Fin (r + 1) →₀ ℕ) → ℕ)
    (hwt_eq : ∀ m, wt m = m.sum fun j e => (2 * j.val + 2) * e)
    (hwt_le : ∀ m ∈ P.support, wt m ≤ M)
    (hPS_zero : (∑ m ∈ P.support, MvPolynomial.C (P.coeff m * convX ^ (M - wt m)) *
      m.prod fun j e => liftFinConv r (toXJetC j.val) ^ e) = 0) :
    P = 0 := by
  classical
  have hconvX_ne : convX ≠ 0 := by
    intro h0
    have h1 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 1 a.val) h0
    simp [convX] at h1
  have hxK_ne : alg convX ≠ 0 := fun h0 => hconvX_ne (halg_inj (h0.trans (map_zero alg).symm))
  let jetConv (j : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    liftFinConv r (toXJetC j.val)
  let g : Fin (r + 1) → MvPolynomial (Fin (r + 1)) K := fun j =>
    MvPolynomial.C ((alg convX ^ (2 * j.val + 2))⁻¹) * MvPolynomial.map alg (jetConv j)
  have hmap_PS : MvPolynomial.map alg (∑ m ∈ P.support, MvPolynomial.C (P.coeff m * convX ^ (M - wt m)) *
        m.prod fun j e => jetConv j ^ e) =
      MvPolynomial.C (alg convX ^ M) * MvPolynomial.aeval g (MvPolynomial.map alg P) := by
    rw [map_sum]
    conv_rhs => rw [MvPolynomial.as_sum P, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, MvPolynomial.map_C, map_mul, map_pow, MvPolynomial.map_monomial,
      MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
    unfold Finsupp.prod
    rw [map_prod]
    have hprod_g : (∏ j ∈ m.support, MvPolynomial.map alg (jetConv j ^ m j)) =
        MvPolynomial.C (alg convX ^ wt m) * ∏ j ∈ m.support, g j ^ m j := by
      have hstep : ∀ j ∈ m.support,
          MvPolynomial.map alg (jetConv j ^ m j) =
            MvPolynomial.C (alg convX ^ ((2 * j.val + 2) * m j)) * g j ^ m j := fun j _ => by
        rw [map_pow]
        have hg_eq : MvPolynomial.map alg (jetConv j) =
            MvPolynomial.C (alg convX ^ (2 * j.val + 2)) * g j := by
          dsimp only [g]
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hxK_ne), map_one, one_mul]
        rw [hg_eq, mul_pow, ← map_pow, ← pow_mul]
      rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
        hwt_eq m]
      rfl
    rw [hprod_g]
    have hexp : MvPolynomial.C (alg convX ^ (M - wt m)) * MvPolynomial.C (alg convX ^ wt m) =
        (MvPolynomial.C (alg convX ^ M) : MvPolynomial (Fin (r + 1)) K) := by
      rw [← map_mul, ← pow_add, Nat.sub_add_cancel (hwt_le m hm)]
    calc MvPolynomial.C (alg (P.coeff m) * alg convX ^ (M - wt m)) *
          (MvPolynomial.C (alg convX ^ wt m) * ∏ j ∈ m.support, g j ^ m j)
        = MvPolynomial.C (alg (P.coeff m)) *
            (MvPolynomial.C (alg convX ^ (M - wt m)) * MvPolynomial.C (alg convX ^ wt m)) *
            ∏ j ∈ m.support, g j ^ m j := by rw [map_mul]; ring
      _ = MvPolynomial.C (alg convX ^ M) *
            (MvPolynomial.C (alg (P.coeff m)) * ∏ j ∈ m.support, g j ^ m j) := by rw [hexp]; ring
  rw [hPS_zero, map_zero] at hmap_PS
  have hCM_ne : (MvPolynomial.C (alg convX ^ M) : MvPolynomial (Fin (r + 1)) K) ≠ 0 := fun h0 =>
    pow_ne_zero M hxK_ne (MvPolynomial.C_eq_zero.mp h0)
  have haeval0 : MvPolynomial.aeval g (MvPolynomial.map alg P) = 0 :=
    (mul_eq_zero.mp hmap_PS.symm).resolve_left hCM_ne
  choose R_nat hR_vars hR_eq using fun j : Fin (r + 1) => toXJetC_triangular j.val
  let u_K : Fin (r + 1) → K := fun j =>
    (alg convX ^ (2 * j.val + 2))⁻¹ * alg (convC ((-1 : ℂ) ^ j.val))
  let S_K : Fin (r + 1) → MvPolynomial (Fin (r + 1)) K := fun j =>
    MvPolynomial.C ((alg convX ^ (2 * j.val + 2))⁻¹) * MvPolynomial.map alg (liftFinConv r (R_nat j))
  have hu_K : ∀ j : Fin (r + 1), IsUnit (u_K j) := fun j => by
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hxK_ne)) ?_)
    intro h0
    have hc0 : convC ((-1 : ℂ) ^ j.val) = 0 := halg_inj (h0.trans (map_zero alg).symm)
    have hcoeff0 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 0 a.val) hc0
    simp [convC] at hcoeff0
  have hg_tri : ∀ j : Fin (r + 1), g j = MvPolynomial.C (u_K j) * MvPolynomial.X j + S_K j := fun j => by
    dsimp only [g, u_K, S_K, jetConv]
    rw [hR_eq j, map_add, map_mul]
    have hC_lift : liftFinConv r (MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j.val))) =
        MvPolynomial.C (convC ((-1 : ℂ) ^ j.val)) := by
      simp only [liftFinConv, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      congr 1; apply Subtype.ext; simp [polyToConv, convC]
    have hX_lift : liftFinConv r (MvPolynomial.X j.val) = MvPolynomial.X j := by
      simp only [liftFinConv, MvPolynomial.eval₂Hom_X', j.isLt, ↓reduceDIte]
    rw [hC_lift, hX_lift, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, map_mul]
    ring
  have hS_vars : ∀ j : Fin (r + 1), ∀ k ∈ (S_K j).vars, k.val < j.val := by
    intro j k hk
    dsimp only [S_K] at hk
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk) with hc | hr
    · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
    · have hk_lift : k ∈ (liftFinConv r (R_nat j)).vars :=
        MvPolynomial.vars_map (liftFinConv r (R_nat j)) alg hr
      exact hR_vars j k.val (vars_liftFinConv_subset r (R_nat j) k hk_lift)
  have hmapP0 : MvPolynomial.map alg P = 0 :=
    triangular_aeval_injective g u_K hu_K S_K hg_tri hS_vars (haeval0.trans (map_zero _).symm)
  exact MvPolynomial.map_injective alg halg_inj (hmapP0.trans (map_zero _).symm)

/-- **Pure-Algebra `ℂ{x}` Transfer (`X^2 * E → E`)**:
If `X^2 * E` satisfies no nonzero `d_u`-ADE over `ConvergentPowerSeries`, then `E` satisfies
no nonzero `d/dX`-ADE over `ConvergentPowerSeries`. -/
theorem stronglyDTransOverConvergent_of_X_sq_mul_no_conv_ade {E : PowerSeries ℂ}
    (hno : ∀ {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries),
      formalEvalConv (PowerSeries.X ^ 2 * E) Q = 0 → Q = 0) :
    StronglyDTransOverConvergent E := by
  classical
  intro r P hP
  let S : PowerSeries ℂ := PowerSeries.X ^ 2 * E
  let M : ℕ := (2 * r + 2) * P.totalDegree
  let jetConv (j : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    liftFinConv r (toXJetC j.val)
  have hjet_eval : ∀ j : Fin (r + 1),
      formalEvalConv S (jetConv j) = PowerSeries.X ^ (2 * j.val + 2) * seriesJet E j.val := by
    intro j
    let evS := MvPolynomial.eval₂Hom toPS (fun i : Fin (r + 1) => d_u^[i.val] S)
    have hcomp : ∀ p : MvPolynomial ℕ (Polynomial ℂ),
        evS (liftFinConv r p) =
          MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom
            (fun k => evS (if hk : k < r + 1 then MvPolynomial.X ⟨k, hk⟩ else 0)) p := fun p => by
      induction p using MvPolynomial.induction_on with
      | C c => simp [evS, liftFinConv]; rfl
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | mul_X a k ha =>
        rw [map_mul, map_mul, map_mul, ha]
        simp only [liftFinConv, MvPolynomial.eval₂Hom_X']
    change evS (liftFinConv r (toXJetC j.val)) = _
    rw [hcomp, ← evalX_toXJetC E j.val]
    refine eval₂Hom_congr_varsC _ fun k hk => ?_
    have hk_lt : k < r + 1 := Nat.lt_succ_of_le ((toXJetC_vars_le j.val k hk).trans (Nat.le_of_lt_succ j.isLt))
    simp [evS, hk_lt, S]
  let wt (m : Fin (r + 1) →₀ ℕ) : ℕ := m.sum fun j e => (2 * j.val + 2) * e
  have hwt_le : ∀ m ∈ P.support, wt m ≤ M := fun m hm => by
    have hdeg : (m.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hm
    have hterm : ∀ j ∈ m.support, (2 * j.val + 2) * m j ≤ (2 * r + 2) * m j := fun j _ =>
      Nat.mul_le_mul_right (m j) (by have := j.isLt; omega)
    calc wt m = ∑ j ∈ m.support, (2 * j.val + 2) * m j := rfl
      _ ≤ ∑ j ∈ m.support, (2 * r + 2) * m j := Finset.sum_le_sum hterm
      _ = (2 * r + 2) * ∑ j ∈ m.support, m j := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * r + 2) * P.totalDegree := Nat.mul_le_mul_left _ hdeg
  let P_S : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    ∑ m ∈ P.support, MvPolynomial.C (P.coeff m * convX ^ (M - wt m)) *
      m.prod fun j e => jetConv j ^ e
  have hPS_eval : formalEvalConv S P_S = 0 := by
    have heq : formalEvalConv S P_S =
        PowerSeries.X ^ M * MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet E j.val) P := by
      dsimp only [P_S, formalEvalConv]
      rw [MvPolynomial.eval₂_sum]
      conv_rhs => rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, map_mul, map_pow, toPS_convX]
      have hprod : MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => d_u^[i.val] S)
            (m.prod fun j e => jetConv j ^ e) =
          PowerSeries.X ^ wt m * ∏ j ∈ m.support, seriesJet E j.val ^ m j := by
        unfold Finsupp.prod
        rw [MvPolynomial.eval₂_prod]
        have hstep : ∀ j ∈ m.support,
            MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => d_u^[i.val] S) (jetConv j ^ m j) =
              PowerSeries.X ^ ((2 * j.val + 2) * m j) * seriesJet E j.val ^ m j := fun j _ => by
          rw [MvPolynomial.eval₂_pow, show MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => d_u^[i.val] S) (jetConv j) =
            formalEvalConv S (jetConv j) from rfl, hjet_eval j, mul_pow, ← pow_mul]
        rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        rfl
      rw [hprod]
      have hexp : (PowerSeries.X : PowerSeries ℂ) ^ (M - wt m) * PowerSeries.X ^ wt m =
          PowerSeries.X ^ M := by
        rw [← pow_add, Nat.sub_add_cancel (hwt_le m hm)]
      calc (toPS (P.coeff m) * PowerSeries.X ^ (M - wt m)) *
            (PowerSeries.X ^ wt m * ∏ j ∈ m.support, seriesJet E j.val ^ m j)
          = toPS (P.coeff m) * (PowerSeries.X ^ (M - wt m) * PowerSeries.X ^ wt m) *
              ∏ j ∈ m.support, seriesJet E j.val ^ m j := by ring
        _ = PowerSeries.X ^ M * (toPS (P.coeff m) * ∏ j ∈ m.support, seriesJet E j.val ^ m j) := by
            rw [hexp]; ring
    rw [heq, hP, mul_zero]
  have hPS_zero : P_S = 0 := hno P_S hPS_eval
  exact invert_toXJetC_over_field
    (algebraMap ConvergentPowerSeries (FractionRing ConvergentPowerSeries))
    (IsFractionRing.injective ConvergentPowerSeries (FractionRing ConvergentPowerSeries))
    P wt (fun _ => rfl) hwt_le hPS_zero

/-! #### 4C. Torus Knots `T(p, q)` & Sign-Flip Transfer over `ℂ{t}` -/

/-- Master convergent-coefficient differential transcendence for any positive-ray meromorphic
Borel kernel `ψ`. -/
theorem eulerSeries_stronglyDTransOverConvergent_of_meromorphicBorel {ψ ω res}
    (h : MeromorphicBorelData ψ ω res) :
    StronglyDTransOverConvergent (eulerSeriesOf ψ) := by
  refine stronglyDTransOverConvergent_of_X_sq_mul_no_conv_ade fun Q hQ => ?_
  have h0_mem : (0 : ℂ) ∈ puncturedWedge h.θ₀ h.ε ω :=
    ⟨Or.inl (by simp [h.hε_pos]), by
      rintro ⟨m, hm⟩
      dsimp only at hm
      exact (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).ne'
        (by exact_mod_cast hm)⟩
  rw [← formalSeries_abelConv_eq (h.analyticOn 0 h0_mem)] at hQ
  exact abelConv_no_conv_ade h Q hQ

private lemma analyticAt_iteratedDerivC {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (k : ℕ) :
    AnalyticAt ℂ (iteratedDeriv k f) z := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

private lemma iteratedDeriv_comp_const_mulC {f : ℂ → ℂ} (c : ℂ) (k : ℕ) :
    ∀ z : ℂ, AnalyticAt ℂ f (c * z) →
      iteratedDeriv k (fun w => f (c * w)) z = c ^ k * iteratedDeriv k f (c * z) := by
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hf
    rw [iteratedDeriv_succ]
    have hloc : iteratedDeriv k (fun w => f (c * w)) =ᶠ[𝓝 z] fun w => c ^ k * iteratedDeriv k f (c * w) := by
      have hev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ f (c * w) :=
        ((continuousAt_const.mul continuousAt_id).tendsto).eventually hf.eventually_analyticAt
      filter_upwards [hev] with w hw; exact ih w hw
    rw [hloc.deriv_eq]
    have hder : HasDerivAt (fun w => c ^ k * iteratedDeriv k f (c * w))
        (c ^ k * (iteratedDeriv (k + 1) f (c * z) * c)) z := by
      have h1 : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f (c * z)) (c * z) := by
        rw [iteratedDeriv_succ]
        exact (analyticAt_iteratedDerivC hf k).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun w => c * w) c z := by simpa using (hasDerivAt_id z).const_mul c
      exact (h1.comp z h2).const_mul (c ^ k)
    rw [hder.deriv, pow_succ]; ring

private lemma eulerSeriesOf_torusKnotPsi_eq {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    eulerSeriesOf (torusKnotPsi p q) = torusKnotEulerSeries p q := by
  have hdata := torusKnot_meromorphicBorelData hp hq
  have h0_mem : (0 : ℂ) ∈ puncturedWedge hdata.θ₀ hdata.ε (torusKnotFreq p q) :=
    ⟨Or.inl (by simp [hdata.hε_pos]), by
      rintro ⟨m, hm⟩
      dsimp only at hm
      exact (lt_of_lt_of_le hdata.ω_pos (hdata.ω_mono.monotone (Nat.zero_le m))).ne'
        (by exact_mod_cast hm)⟩
  have hpsi0 : AnalyticAt ℂ (torusKnotPsi p q) 0 := hdata.analyticOn 0 h0_mem
  have han0 : AnalyticAt ℂ (torusKnotBorel p q) 0 := by
    have heq : torusKnotBorel p q = fun z => (2 : ℂ)⁻¹ * torusKnotPsi p q ((4 : ℂ)⁻¹ * z) := by
      funext z; unfold torusKnotPsi; rw [show (4 : ℂ) * ((4 : ℂ)⁻¹ * z) = z by ring]; ring
    rw [heq]
    exact analyticAt_const.mul ((by simpa using hpsi0 : AnalyticAt ℂ (torusKnotPsi p q) ((4 : ℂ)⁻¹ * 0)).comp
      (analyticAt_const.mul analyticAt_id))
  ext k
  simp only [eulerSeriesOf, torusKnotEulerSeries, torusKnotCoeff, PowerSeries.coeff_mk]
  have hcomp : AnalyticAt ℂ (fun w => torusKnotBorel p q (4 * w)) 0 :=
    (by simpa using han0 : AnalyticAt ℂ (torusKnotBorel p q) (4 * 0)).comp (analyticAt_const.mul analyticAt_id)
  have hpsi_eq : iteratedDeriv k (torusKnotPsi p q) 0 =
      (2 : ℂ) * ((4 : ℂ) ^ k * iteratedDeriv k (torusKnotBorel p q) 0) := by
    change iteratedDeriv k (fun w : ℂ => (2 : ℂ) * torusKnotBorel p q (4 * w)) 0 = _
    rw [iteratedDeriv_const_mul (2 : ℂ) hcomp.contDiffAt,
      iteratedDeriv_comp_const_mulC (4 : ℂ) k 0 (by simpa using han0), mul_zero]
  rw [hpsi_eq]
  have hpow4 : (2 : ℂ) * (4 : ℂ) ^ k = (2 : ℂ) ^ (2 * k + 1) := by
    rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ']
  have h2p : (2 : ℂ) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hmul4 : (2 : ℂ) * ((4 : ℂ) ^ k * iteratedDeriv k (torusKnotBorel p q) 0) =
      (2 : ℂ) ^ (2 * k + 1) * iteratedDeriv k (torusKnotBorel p q) 0 := by
    rw [← mul_assoc, hpow4]
  rw [hmul4]
  field_simp [h2p, hfac]

/-- Strong D-transcendence over `ℂ{t}` for ALL torus knot Euler series `T(p, q)` (`p, q ≥ 2`). -/
theorem torusKnotEulerSeries_stronglyDTransOverConvergent {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StronglyDTransOverConvergent (torusKnotEulerSeries p q) := by
  rw [← eulerSeriesOf_torusKnotPsi_eq hp hq]
  exact eulerSeries_stronglyDTransOverConvergent_of_meromorphicBorel (torusKnot_meromorphicBorelData hp hq)

/-- Strong D-transcendence over `ℂ{t}` for Glaisher's `T`-number / Fishburn Euler series. -/
theorem fishburnEulerSeries_stronglyDTransOverConvergent :
    StronglyDTransOverConvergent fishburnEulerSeries :=
  torusKnotEulerSeries_stronglyDTransOverConvergent (p := 2) (q := 3) (by omega) (by omega)

/-- Sign-flip ring automorphism `a(t) ↦ a(-t)` restricted to `ConvergentPowerSeries`. -/
@[expose] def scaleNegConv : ConvergentPowerSeries →+* ConvergentPowerSeries where
  toFun a := ⟨scaleNegPS a.val, isConvergentPS_rescale (-1 : ℂ) a.property⟩
  map_one' := Subtype.ext (map_one scaleNegPS)
  map_mul' a b := Subtype.ext (map_mul scaleNegPS a.val b.val)
  map_zero' := Subtype.ext (map_zero scaleNegPS)
  map_add' a b := Subtype.ext (map_add scaleNegPS a.val b.val)

private lemma scaleNegPS_invol (F : PowerSeries ℂ) : scaleNegPS (scaleNegPS F) = F := by
  ext n; simp [scaleNegPS, PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow]

private lemma scaleNegConv_injective : Function.Injective scaleNegConv := by
  intro a b h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  have := congrArg scaleNegPS hv
  simpa [scaleNegConv, scaleNegPS_invol] using this

private lemma scaleNegPS_seriesJetC (F : PowerSeries ℂ) (j : ℕ) :
    scaleNegPS (seriesJet (scaleNegPS F) j) = (-1 : ℂ) ^ j • seriesJet F j := by
  have hder : ∀ G : PowerSeries ℂ, PowerSeries.derivative (scaleNegPS G) = -scaleNegPS (PowerSeries.derivative G) := by
    intro G; ext n; simp [scaleNegPS, PowerSeries.coeff_rescale, PowerSeries.coeff_derivative, pow_succ]; ring
  have hjet : ∀ G : PowerSeries ℂ, ∀ k : ℕ, seriesJet (scaleNegPS G) k = (-1 : ℂ) ^ k • scaleNegPS (seriesJet G k) := by
    intro G k
    induction k with
    | zero => simp [seriesJet]
    | succ k ih =>
      dsimp only [seriesJet] at ih ⊢
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        Derivation.map_smul_of_tower, hder, smul_neg, PowerSeries.smul_eq_C_mul,
        PowerSeries.smul_eq_C_mul, pow_succ, mul_neg_one, map_neg]; ring
  have h1 := hjet (scaleNegPS F) j
  rw [scaleNegPS_invol] at h1
  have h2 := congrArg (fun G : PowerSeries ℂ => (-1 : ℂ) ^ j • G) h1
  simp only [smul_smul, ← mul_pow] at h2
  norm_num at h2
  exact h2.symm

/-- Sign-flip invariance of strong D-transcendence over `ℂ{t}`. -/
theorem stronglyDTransOverConvergent_scaleNegPS {F : PowerSeries ℂ}
    (hF : StronglyDTransOverConvergent F) :
    StronglyDTransOverConvergent (scaleNegPS F) := by
  intro r P hP
  let g : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := fun j =>
    MvPolynomial.C (convC ((-1 : ℂ) ^ j.val)) * MvPolynomial.X j
  let Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    MvPolynomial.aeval g (MvPolynomial.map scaleNegConv P)
  have hQ_eval_gen : ∀ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet F j.val)
        (MvPolynomial.aeval g (MvPolynomial.map scaleNegConv R)) =
      scaleNegPS (MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet (scaleNegPS F) j.val) R) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
        MvPolynomial.eval₂_C]
      rfl
    | add A B hA hB =>
      simp only [map_add, MvPolynomial.eval₂_add] at hA hB ⊢
      rw [hA, hB]
    | mul_X A j hA =>
      simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X] at hA ⊢
      rw [hA]
      congr 1
      simp only [g, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
        toPS_convC, scaleNegPS_seriesJetC, PowerSeries.smul_eq_C_mul]
  have hQ_eval : MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet F j.val) Q =
      scaleNegPS (MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet (scaleNegPS F) j.val) P) :=
    hQ_eval_gen P
  rw [hP, map_zero] at hQ_eval
  have hQ0 : Q = 0 := hF Q hQ_eval
  have hu : ∀ j : Fin (r + 1), IsUnit (convC ((-1 : ℂ) ^ j.val)) := fun j =>
    isUnit_iff_exists_inv.mpr ⟨convC ((-1 : ℂ) ^ j.val), by
      rw [← map_mul, ← mul_pow]; norm_num⟩
  have hmap0 : MvPolynomial.map scaleNegConv P = 0 :=
    triangular_aeval_injective g (fun j => convC ((-1 : ℂ) ^ j.val)) hu (fun _ => 0)
      (fun j => by simp [g]) (fun _ _ hk => by simp at hk) (hQ0.trans (map_zero _).symm)
  exact MvPolynomial.map_injective scaleNegConv scaleNegConv_injective (hmap0.trans (map_zero _).symm)

/-- Strong D-transcendence over `ℂ{t}` for ALL torus knot perturbative WRT series `T(p, q)`. -/
theorem torusKnotPerturbativeSeries_stronglyDTransOverConvergent {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StronglyDTransOverConvergent (torusKnotPerturbativeSeries p q) := by
  have heq : torusKnotPerturbativeSeries p q = scaleNegPS (torusKnotEulerSeries p q) := by
    ext k; simp [torusKnotPerturbativeSeries, torusKnotEulerSeries, scaleNegPS, PowerSeries.coeff_rescale, mul_div_assoc]
  rw [heq]
  intro r P hP
  exact stronglyDTransOverConvergent_scaleNegPS (torusKnotEulerSeries_stronglyDTransOverConvergent hp hq) P hP

/-! #### 4D. Zagier Chain-Rule Matrix (`zagierJetMat`) & Literal Fishburn OGF over `ℂ{x}` -/

/-- Ring embedding `a(x) ↦ a(1 - exp(-24 t))` on `ConvergentPowerSeries`. -/
@[expose] def substZagierConv : ConvergentPowerSeries →+* ConvergentPowerSeries where
  toFun a := ⟨a.val.subst zagierSubst, isConvergentPS_subst a.property isConvergentPS_zagierSubst zagierSubst_constantCoeff⟩
  map_one' := Subtype.ext (by
    change (1 : PowerSeries ℂ).subst zagierSubst = 1
    simpa [PowerSeries.coe_substAlgHom zagierSubst_hasSubst] using
      map_one (PowerSeries.substAlgHom zagierSubst_hasSubst))
  map_mul' a b := Subtype.ext (PowerSeries.subst_mul zagierSubst_hasSubst a.val b.val)
  map_zero' := Subtype.ext (by
    change (0 : PowerSeries ℂ).subst zagierSubst = 0
    simpa [PowerSeries.coe_substAlgHom zagierSubst_hasSubst] using
      map_zero (PowerSeries.substAlgHom zagierSubst_hasSubst))
  map_add' a b := Subtype.ext (PowerSeries.subst_add zagierSubst_hasSubst a.val b.val)

lemma substZagierConv_injective : Function.Injective substZagierConv := by
  intro a b h
  apply Subtype.ext
  exact subst_injective_of_coeff_one_ne_zero zagierSubst_constantCoeff
    (by rw [zagierSubst_coeff_one]; norm_num) (congrArg Subtype.val h)

/-- Unit multiplier `(1/24) * exp(24 t) ∈ ℂ{t}` inverting `(d/dt)(1 - exp(-24 t)) = 24 exp(-24 t)`. -/
@[expose] def zagierStepUnit : ConvergentPowerSeries :=
  convC (24 : ℂ)⁻¹ * convExp 24

lemma isUnit_zagierStepUnit : IsUnit zagierStepUnit := by
  refine isUnit_iff_exists_inv.mpr ⟨convC 24 * convExp (-24), ?_⟩
  unfold zagierStepUnit
  calc (convC (24 : ℂ)⁻¹ * convExp 24) * (convC 24 * convExp (-24))
      = (convC (24 : ℂ)⁻¹ * convC 24) * (convExp 24 * convExp (-24)) := by ring
    _ = convC ((24 : ℂ)⁻¹ * 24) * convExp (24 + (-24)) := by rw [← map_mul, ← convExp_add]
    _ = 1 := by norm_num [convExp_zero]

private lemma zagierStepUnit_mul_deriv_zagierSubst :
    zagierStepUnit.val * PowerSeries.derivative zagierSubst = 1 := by
  rw [derivative_zagierSubst]
  have hrew : (zagierStepUnit * (convC 24 * convExp (-24))).val = 1 := by
    have h1 : zagierStepUnit * (convC 24 * convExp (-24)) = 1 := by
      unfold zagierStepUnit
      calc (convC (24 : ℂ)⁻¹ * convExp 24) * (convC 24 * convExp (-24))
          = (convC (24 : ℂ)⁻¹ * convC 24) * (convExp 24 * convExp (-24)) := by ring
        _ = convC ((24 : ℂ)⁻¹ * 24) * convExp (24 + (-24)) := by rw [← map_mul, ← convExp_add]
        _ = 1 := by norm_num [convExp_zero]
    rw [h1]; rfl
  simpa [convC, convExp, PowerSeries.smul_eq_C_mul] using hrew

/-- Upper-triangular chain-rule matrix `zagierJetMat j i ∈ ℂ{t}` expressing
`(seriesJet fishburnSeries j).subst zagierSubst = ∑_{i ≤ j} zagierJetMat j i * seriesJet fishburnEulerSeries i`. -/
@[expose] def zagierJetMat : ℕ → ℕ → ConvergentPowerSeries
  | 0, 0 => convExp 1
  | 0, _ + 1 => 0
  | j + 1, 0 => zagierStepUnit * convDeriv (zagierJetMat j 0)
  | j + 1, i + 1 => zagierStepUnit * (convDeriv (zagierJetMat j (i + 1)) + zagierJetMat j i)

lemma zagierJetMat_eq_zero_of_lt : ∀ {j i : ℕ}, j < i → zagierJetMat j i = 0 := by
  intro j
  induction j with
  | zero =>
    intro i hi
    cases i with
    | zero => omega
    | succ i' => rfl
  | succ j ih =>
    intro i hi
    cases i with
    | zero => omega
    | succ i' =>
      have h1 : j < i' + 1 := by omega
      have h2 : j < i' := by omega
      simp only [zagierJetMat, ih h1, ih h2, add_zero]
      have hd0 : convDeriv 0 = 0 := Subtype.ext (map_zero PowerSeries.derivative)
      rw [hd0, mul_zero]

lemma zagierJetMat_diag (j : ℕ) :
    zagierJetMat j j = zagierStepUnit ^ j * convExp 1 := by
  induction j with
  | zero => simp [zagierJetMat]
  | succ j ih =>
    simp only [zagierJetMat, zagierJetMat_eq_zero_of_lt (Nat.lt_succ_self j), ih]
    have hd0 : convDeriv 0 = 0 := Subtype.ext (map_zero PowerSeries.derivative)
    rw [hd0, zero_add, pow_succ', mul_assoc]

lemma isUnit_zagierJetMat_diag (j : ℕ) : IsUnit (zagierJetMat j j) := by
  rw [zagierJetMat_diag]
  exact (isUnit_zagierStepUnit.pow j).mul (isUnit_convExp 1)

private lemma convExp_one_val : (convExp 1).val = PowerSeries.exp ℂ := by
  ext n; simp [convExp]

/-- Exact chain-rule identity along Zagier's substitution `x = 1 - exp(-24 t)`:
`(seriesJet fishburnSeries j).subst zagierSubst = ∑_{i ≤ j} zagierJetMat j i * seriesJet fishburnEulerSeries i`. -/
theorem seriesJet_fishburnSeries_subst_zagier (j : ℕ) :
    (seriesJet fishburnSeries j).subst zagierSubst =
      ∑ i ∈ Finset.range (j + 1), (zagierJetMat j i).val * seriesJet fishburnEulerSeries i := by
  induction j with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, seriesJet, Function.iterate_zero,
      id_eq, zagierJetMat, convExp_one_val]
    exact zagier_formal_identity
  | succ j ih =>
    have hderiv_step : PowerSeries.derivative ((seriesJet fishburnSeries j).subst zagierSubst) =
        (seriesJet fishburnSeries (j + 1)).subst zagierSubst * PowerSeries.derivative zagierSubst := by
      rw [PowerSeries.derivative_subst zagierSubst_hasSubst]
      congr 1
      dsimp only [seriesJet]; rw [Function.iterate_succ_apply']
    have hnext : (seriesJet fishburnSeries (j + 1)).subst zagierSubst =
        zagierStepUnit.val * PowerSeries.derivative ((seriesJet fishburnSeries j).subst zagierSubst) := by
      rw [hderiv_step, mul_left_comm, zagierStepUnit_mul_deriv_zagierSubst, mul_one]
    rw [hnext, ih, map_sum]
    have hterm_deriv : ∀ i ∈ Finset.range (j + 1),
        PowerSeries.derivative ((zagierJetMat j i).val * seriesJet fishburnEulerSeries i) =
          (convDeriv (zagierJetMat j i)).val * seriesJet fishburnEulerSeries i +
          (zagierJetMat j i).val * seriesJet fishburnEulerSeries (i + 1) := fun i _ => by
      have hsucc : PowerSeries.derivative (seriesJet fishburnEulerSeries i) =
          seriesJet fishburnEulerSeries (i + 1) := by
        dsimp only [seriesJet]; rw [Function.iterate_succ_apply']
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hsucc, add_comm,
        mul_comm (seriesJet fishburnEulerSeries i)]
      rfl
    rw [Finset.sum_congr rfl hterm_deriv, Finset.sum_add_distrib]
    have hsum1 : ∑ i ∈ Finset.range (j + 1),
          (convDeriv (zagierJetMat j i)).val * seriesJet fishburnEulerSeries i =
        (convDeriv (zagierJetMat j 0)).val * seriesJet fishburnEulerSeries 0 +
        ∑ i ∈ Finset.range j,
          (convDeriv (zagierJetMat j (i + 1))).val * seriesJet fishburnEulerSeries (i + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    have hsum2 : ∑ i ∈ Finset.range (j + 1),
          (zagierJetMat j i).val * seriesJet fishburnEulerSeries (i + 1) =
        (∑ i ∈ Finset.range j, (zagierJetMat j i).val * seriesJet fishburnEulerSeries (i + 1)) +
        (zagierJetMat j j).val * seriesJet fishburnEulerSeries (j + 1) :=
      Finset.sum_range_succ _ j
    rw [hsum1, hsum2, Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [zagierJetMat, zagierJetMat_eq_zero_of_lt (Nat.lt_succ_self j)]
    have hd0 : convDeriv 0 = 0 := Subtype.ext (map_zero PowerSeries.derivative)
    rw [hd0, zero_add]
    have hmul_sum : zagierStepUnit.val *
        ((convDeriv (zagierJetMat j 0)).val * seriesJet fishburnEulerSeries 0 +
          ∑ i ∈ Finset.range j, (convDeriv (zagierJetMat j (i + 1))).val * seriesJet fishburnEulerSeries (i + 1) +
          ((∑ i ∈ Finset.range j, (zagierJetMat j i).val * seriesJet fishburnEulerSeries (i + 1)) +
            (zagierJetMat j j).val * seriesJet fishburnEulerSeries (j + 1))) =
        (zagierStepUnit * convDeriv (zagierJetMat j 0)).val * seriesJet fishburnEulerSeries 0 +
          (∑ i ∈ Finset.range j,
            (zagierStepUnit * (convDeriv (zagierJetMat j (i + 1)) + zagierJetMat j i)).val *
              seriesJet fishburnEulerSeries (i + 1)) +
          (zagierStepUnit * zagierJetMat j j).val * seriesJet fishburnEulerSeries (j + 1) := by
      have hcomb : ∑ i ∈ Finset.range j,
            (zagierStepUnit * (convDeriv (zagierJetMat j (i + 1)) + zagierJetMat j i)).val *
              seriesJet fishburnEulerSeries (i + 1) =
          zagierStepUnit.val *
            ((∑ i ∈ Finset.range j, (convDeriv (zagierJetMat j (i + 1))).val * seriesJet fishburnEulerSeries (i + 1)) +
              ∑ i ∈ Finset.range j, (zagierJetMat j i).val * seriesJet fishburnEulerSeries (i + 1)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change (zagierStepUnit.val * ((convDeriv (zagierJetMat j (i + 1))).val + (zagierJetMat j i).val)) * _ = _
        ring
      rw [hcomb]
      change _ = (zagierStepUnit.val * (convDeriv (zagierJetMat j 0)).val) * _ + _ +
        (zagierStepUnit.val * (zagierJetMat j j).val) * _
      ring
    rw [hmul_sum]
    ring

/-- **Strong Differential Transcendence over `ℂ{x}` of the Literal Fishburn OGF `fishburnSeries`**:
`P(x) = ∑_{m ≥ 0} ∏_{j=1}^m (1 - (1 - x)^j)` satisfies NO nonzero algebraic differential equation
with coefficients in `ConvergentPowerSeries` (`ℂ{x}`). -/
theorem fishburnSeries_stronglyDTransOverConvergent :
    StronglyDTransOverConvergent fishburnSeries := by
  intro r P hP
  let g_zag : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := fun j =>
    ∑ i : Fin (r + 1), MvPolynomial.C (zagierJetMat j.val i.val) * MvPolynomial.X i
  let P' : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    MvPolynomial.aeval g_zag (MvPolynomial.map substZagierConv P)
  have hP'_eval_gen : ∀ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => seriesJet fishburnEulerSeries i.val)
        (MvPolynomial.aeval g_zag (MvPolynomial.map substZagierConv R)) =
      (MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet fishburnSeries j.val) R).subst zagierSubst := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
        MvPolynomial.eval₂_C]
      rfl
    | add A B hA hB =>
      simp only [map_add, MvPolynomial.eval₂_add] at hA hB ⊢
      rw [hA, hB, PowerSeries.subst_add zagierSubst_hasSubst]
    | mul_X A j hA =>
      simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X] at hA ⊢
      rw [hA, PowerSeries.subst_mul zagierSubst_hasSubst]
      congr 1
      dsimp only [g_zag]
      rw [MvPolynomial.eval₂_sum]
      simp_rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, toPS_apply]
      rw [seriesJet_fishburnSeries_subst_zagier j.val, Fin.sum_univ_eq_sum_range
        (fun i => (zagierJetMat j.val i).val * seriesJet fishburnEulerSeries i) (r + 1)]
      symm
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt j.isLt)) fun i _ hnot => ?_
      have hgt : j.val < i := by rw [Finset.mem_range] at hnot; omega
      rw [zagierJetMat_eq_zero_of_lt hgt, Subring.coe_zero, zero_mul]
  have hP'_eval : MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => seriesJet fishburnEulerSeries i.val) P' =
      (MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet fishburnSeries j.val) P).subst zagierSubst :=
    hP'_eval_gen P
  rw [hP] at hP'_eval
  have hsubst0 : (0 : PowerSeries ℂ).subst zagierSubst = 0 := by
    simpa [PowerSeries.coe_substAlgHom zagierSubst_hasSubst] using
      map_zero (PowerSeries.substAlgHom zagierSubst_hasSubst)
  rw [hsubst0] at hP'_eval
  have hP'0 : P' = 0 := fishburnEulerSeries_stronglyDTransOverConvergent P' hP'_eval
  -- Split g_zag into unit diagonal + strictly lower triangular remainder
  let S_zag : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := fun j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i.val < j.val),
      MvPolynomial.C (zagierJetMat j.val i.val) * MvPolynomial.X i
  have hg_split : ∀ j : Fin (r + 1),
      g_zag j = MvPolynomial.C (zagierJetMat j.val j.val) * MvPolynomial.X j + S_zag j := fun j => by
    dsimp only [g_zag, S_zag]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    symm
    refine Finset.sum_subset (fun i hi => Finset.mem_erase.mpr
      ⟨fun h => (lt_irrefl j.val) (h ▸ (Finset.mem_filter.mp hi).2), Finset.mem_univ i⟩) fun i hi hnot => ?_
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    have hnotlt : ¬ i.val < j.val := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    have hgt : j.val < i.val := lt_of_le_of_ne (Nat.le_of_not_lt hnotlt) (fun h => hne (Fin.ext h.symm))
    rw [zagierJetMat_eq_zero_of_lt hgt, map_zero, zero_mul]
  have hS_vars : ∀ j : Fin (r + 1), ∀ k ∈ (S_zag j).vars, k.val < j.val := by
    intro j k hk
    dsimp only [S_zag] at hk
    obtain ⟨i, hi, hk_i⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hk)
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk_i) with hc | hx
    · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx
      subst hx
      exact (Finset.mem_filter.mp hi).2
  have hmap0 : MvPolynomial.map substZagierConv P = 0 :=
    triangular_aeval_injective g_zag (fun j => zagierJetMat j.val j.val)
      (fun j => isUnit_zagierJetMat_diag j.val) S_zag hg_split hS_vars (hP'0.trans (map_zero _).symm)
  exact MvPolynomial.map_injective substZagierConv substZagierConv_injective (hmap0.trans (map_zero _).symm)

/-! #### 4E. Field of Convergent Meromorphic Germs `ℂ({x})` & All 4 Flagship Theorems -/

/-- Canonical embedding `ℂ[[x]] ↪ Frac(ℂ[[x]])`. -/
@[expose] def fracPS_of_ps : PowerSeries ℂ →+* FractionRing (PowerSeries ℂ) :=
  algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))

/-- Canonical embedding `ℂ{x} ↪ Frac(ℂ[[x]])`. -/
@[expose] def convToFracPS : ConvergentPowerSeries →+* FractionRing (PowerSeries ℂ) :=
  fracPS_of_ps.comp toPS

lemma convToFracPS_injective : Function.Injective convToFracPS :=
  (IsFractionRing.injective (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))).comp toPS_injective

/-- Canonical field embedding `ℂ({x}) = Frac(ℂ{x}) ↪ Frac(ℂ[[x]])` of convergent meromorphic germs. -/
@[expose] def meromorphicGermToFracPS :
    FractionRing ConvergentPowerSeries →+* FractionRing (PowerSeries ℂ) :=
  IsFractionRing.lift convToFracPS_injective

/-- `ℂ({x})`-algebra structure on `Frac(ℂ[[x]])` induced by `meromorphicGermToFracPS`. -/
instance instAlgebraMeromorphicGermsFracPS :
    Algebra (FractionRing ConvergentPowerSeries) (FractionRing (PowerSeries ℂ)) :=
  meromorphicGermToFracPS.toAlgebra

/-- **Strong Differential Transcendence over Convergent Meromorphic Germs `ℂ({x})`**:
All formal derivatives `F, F', F'', ...` are algebraically independent over the field
`FractionRing ConvergentPowerSeries` (`ℂ({x})`) inside `FractionRing (PowerSeries ℂ)`. -/
@[expose] def StronglyDTransOverMeromorphicGerms (F : PowerSeries ℂ) : Prop :=
  AlgebraicIndependent (FractionRing ConvergentPowerSeries)
    (fun j : ℕ => fracPS_of_ps (seriesJet F j))

/-- Clearing denominators from the field `ℂ({x}) = FractionRing ConvergentPowerSeries` to the
ring `ℂ{x} = ConvergentPowerSeries`. -/
theorem stronglyDTransOverMeromorphicGerms_of_convergent {F : PowerSeries ℂ}
    (hF : StronglyDTransOverConvergent F) :
    StronglyDTransOverMeromorphicGerms F := by
  classical
  rw [StronglyDTransOverMeromorphicGerms, algebraicIndependent_iff]
  intro Q hQ
  let K := FractionRing ConvergentPowerSeries
  let alg : ConvergentPowerSeries →+* K := algebraMap ConvergentPowerSeries K
  have halg_inj : Function.Injective alg := IsFractionRing.injective ConvergentPowerSeries K
  choose num den hden_nz hdiv using fun α : ℕ →₀ ℕ =>
    IsFractionRing.div_surjective (A := ConvergentPowerSeries) (K := K) (Q.coeff α)
  have hden_ne : ∀ α : ℕ →₀ ℕ, den α ≠ 0 := fun α =>
    mem_nonZeroDivisors_iff_ne_zero.mp (hden_nz α)
  let D : ConvergentPowerSeries := ∏ β ∈ Q.support, den β
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun β _ => hden_ne β
  let Q_conv : MvPolynomial ℕ ConvergentPowerSeries :=
    ∑ α ∈ Q.support, MvPolynomial.monomial α (num α * ∏ β ∈ Q.support.erase α, den β)
  have hclear : MvPolynomial.map alg Q_conv = MvPolynomial.C (alg D) * Q := by
    apply MvPolynomial.ext
    intro α
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
    dsimp only [Q_conv]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ Q.support
    · rw [Finset.sum_eq_single α]
      · simp only [↓reduceIte, map_mul, map_prod]
        have hD_split : alg D = alg (den α) * ∏ β ∈ Q.support.erase α, alg (den β) := by
          dsimp only [D]; rw [map_prod, ← Finset.mul_prod_erase Q.support _ hα]
        have hden_alg_ne : alg (den α) ≠ 0 := fun h0 =>
          hden_ne α (halg_inj (h0.trans (map_zero alg).symm))
        rw [hD_split, ← hdiv α]
        change alg (num α) * ∏ β ∈ Q.support.erase α, alg (den β) =
          (alg (den α) * ∏ β ∈ Q.support.erase α, alg (den β)) * (alg (num α) / alg (den α))
        field_simp [hden_alg_ne]
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · have hsum0 : (∑ x ∈ Q.support, if x = α then num x * ∏ β ∈ Q.support.erase x, den β else 0) = 0 :=
        Finset.sum_eq_zero fun β hβ => by simp [show β ≠ α from fun h => hα (h ▸ hβ)]
      rw [hsum0, map_zero, MvPolynomial.notMem_support_iff.mp hα, mul_zero]
  have hmap_eval : MvPolynomial.aeval (fun j : ℕ => fracPS_of_ps (seriesJet F j)) (MvPolynomial.map alg Q_conv) =
      fracPS_of_ps (MvPolynomial.eval₂ toPS (seriesJet F) Q_conv) := by
    induction Q_conv using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.eval₂_C]
      change meromorphicGermToFracPS (alg a) = fracPS_of_ps (toPS a)
      exact IsFractionRing.lift_algebraMap convToFracPS_injective a
    | add A B hA hB =>
      simp only [map_add, MvPolynomial.eval₂_add] at hA hB ⊢
      rw [hA, hB]
    | mul_X A j hA =>
      simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X] at hA ⊢
      rw [hA]
  have hQ_conv_eval : MvPolynomial.eval₂ toPS (seriesJet F) Q_conv = 0 := by
    have h1 : fracPS_of_ps (MvPolynomial.eval₂ toPS (seriesJet F) Q_conv) = 0 := by
      rw [← hmap_eval, hclear, map_mul, hQ, mul_zero]
    exact IsFractionRing.injective (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))
      (h1.trans (map_zero fracPS_of_ps).symm)
  let r : ℕ := Q_conv.vars.sup id
  obtain ⟨P, hP_rename⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q_conv
    (Fin.val : Fin (r + 1) → ℕ) Fin.val_injective
    (fun i hi => ⟨⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩, rfl⟩)
  have hP_eval : MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet F j.val) P = 0 := by
    rw [← hP_rename, MvPolynomial.eval₂_rename] at hQ_conv_eval
    exact hQ_conv_eval
  have hP0 : P = 0 := hF P hP_eval
  have hQ_conv0 : Q_conv = 0 := by rw [← hP_rename, hP0, map_zero]
  rw [hQ_conv0, map_zero] at hclear
  have hCD_ne : (MvPolynomial.C (alg D) : MvPolynomial ℕ K) ≠ 0 := by
    intro h0
    exact hD_ne (halg_inj ((MvPolynomial.C_eq_zero.mp h0).trans (map_zero alg).symm))
  exact (mul_eq_zero.mp hclear.symm).resolve_left hCD_ne

/-- **Flagship Unconditional Theorem 1 — Literal Fishburn OGF over `ℂ({x})` (Bostan–Di Vizio–Raschel
AJM 2024, Theorem 3 & §2.2.6; Klazar 2003)**:
The literal divergent Fishburn ordinary generating function
`fishburnSeries = ∑_{m=0}^∞ ∏_{j=1}^m (1 - (1 - x)^j) ∈ ℂ[[x]]`
is **unconditionally strongly differentially transcendental over the field `ℂ({x})` of convergent
meromorphic germs at `0`**. -/
theorem fishburnSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms fishburnSeries :=
  stronglyDTransOverMeromorphicGerms_of_convergent fishburnSeries_stronglyDTransOverConvergent

/-- **Flagship Unconditional Theorem 2 — Glaisher's `T`-Number / Trefoil Euler Series over `ℂ({t})`**:
`fishburnEulerSeries = ∑_{k ≥ 0} (T_k / k!) t^k` is **unconditionally strongly differentially
transcendental over the field `ℂ({t})` of convergent meromorphic germs at `0`**. -/
theorem fishburnEulerSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms fishburnEulerSeries :=
  stronglyDTransOverMeromorphicGerms_of_convergent fishburnEulerSeries_stronglyDTransOverConvergent

/-- **Flagship Unconditional Theorem 3 — ALL Torus Knots `T(p, q)` Euler Series over `ℂ({t})`**:
For ALL integers `p, q ≥ 2`, `torusKnotEulerSeries p q` is **unconditionally strongly
differentially transcendental over the field `ℂ({t})` of convergent meromorphic germs at `0`**. -/
theorem torusKnotEulerSeries_stronglyDTrans {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StronglyDTransOverMeromorphicGerms (torusKnotEulerSeries p q) :=
  stronglyDTransOverMeromorphicGerms_of_convergent
    (torusKnotEulerSeries_stronglyDTransOverConvergent hp hq)

/-- **Flagship Unconditional Theorem 4 — ALL Torus Knots `T(p, q)` Perturbative WRT Series over `ℂ({t})`**:
For ALL integers `p, q ≥ 2`, the alternating Lawrence–Zagier / Hikami perturbative WRT series
`torusKnotPerturbativeSeries p q` is **unconditionally strongly differentially transcendental over
the field `ℂ({t})` of convergent meromorphic germs at `0`**. -/
theorem torusKnotPerturbativeSeries_stronglyDTrans {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StronglyDTransOverMeromorphicGerms (torusKnotPerturbativeSeries p q) :=
  stronglyDTransOverMeromorphicGerms_of_convergent
    (torusKnotPerturbativeSeries_stronglyDTransOverConvergent hp hq)

end
end PakPrimes.FishburnStrongDTrans
