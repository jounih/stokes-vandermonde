module

public import PakPrimes.MacMahonLogCoefficients
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Tactic.LinearCombination

/-! # The formal Euler product for plane partitions

Forgetting the factors of part size greater than `d` leaves the degree-`d` coefficient
unchanged. In the coefficientwise topology the product converges, and it is the unique
series with constant coefficient one and Euler logarithmic derivative `macmahonDivisorSeries`.
-/

public section
noncomputable section

namespace PakPrimes.DivisorAndMacMahon
open PowerSeries Filter
open scoped PowerSeries.WithPiTopology Topology BigOperators

/-- A factor of MacMahon's Euler product, indexed so the first exponent is one. -/
@[expose] def macmahonEulerFactor (i : ℕ) : PowerSeries ℂ :=
  ((1 - X ^ (i + 1))⁻¹) ^ (i + 1)

@[simp] theorem macmahonEulerFactor_constantCoeff (i : ℕ) :
    constantCoeff (macmahonEulerFactor i) = 1 := by
  simp [macmahonEulerFactor, PowerSeries.constantCoeff_inv]

private theorem geometric_mul_denominator (i : ℕ) :
    EulerGeometric i * (1 - X ^ (i + 1)) = 1 := by
  rw [mul_sub, mul_one]
  ext d
  rw [map_sub, coeff_mul_X_pow', coeff_one]
  by_cases h : i + 1 ≤ d
  · have hd : d ≠ 0 := by omega
    simp [h, hd, EulerGeometric, Nat.dvd_sub_iff_left h (dvd_refl (i + 1))]
  · by_cases hd : d = 0
    · simp [hd, EulerGeometric]
    · have hn : ¬(i + 1 ∣ d) := fun hav => h (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hav)
      simp [h, hd, hn, EulerGeometric]

/-- The geometric series representation of the inverse Euler denominator. -/
theorem EulerGeometric_eq_inv (i : ℕ) :
    EulerGeometric i = (1 - X ^ (i + 1))⁻¹ :=
  (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr (geometric_mul_denominator i)

theorem macmahonEulerFactor_ode (i : ℕ) :
    X * derivative (macmahonEulerFactor i) =
      (C (((i + 1 : ℕ) : ℂ)^2) * (EulerGeometric i - 1)) * macmahonEulerFactor i := by
  have h : EulerGeometric i - 1 = X ^ (i + 1) * EulerGeometric i := by
    linear_combination geometric_mul_denominator i
  have hc : C (((i + 1 : ℕ) : ℂ)^2) = ((i : PowerSeries ℂ) + 1)^2 := by
    rw [map_pow, Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one]
  rw [hc, h, EulerGeometric_eq_inv, macmahonEulerFactor, derivative_pow, derivative_inv',
    map_sub, derivative_one, derivative_X_pow_succ]
  simp only [Nat.add_sub_cancel, zero_sub, neg_mul_neg, Nat.cast_add, Nat.cast_one,
    map_add, map_natCast, map_one, pow_succ]
  ring

private theorem euler_prod (factor weight : ℕ → PowerSeries ℂ)
    (h : ∀ i, X * derivative (factor i) = weight i * factor i) (s : Finset ℕ) :
    X * derivative (∏ i ∈ s, factor i) = (∑ i ∈ s, weight i) * ∏ i ∈ s, factor i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, derivative.leibniz]
    simp only [smul_eq_mul]
    linear_combination (∏ j ∈ s, factor j) * h i + factor i * ih

private theorem coeff_euler (f : PowerSeries ℂ) (d : ℕ) :
    coeff d (X * derivative f) = (d : ℂ) * coeff d f := by
  cases d with
  | zero => simp [coeff_zero_X_mul]
  | succ n => simp [coeff_succ_X_mul, coeff_derivative, mul_comm]

private theorem coeff_ext_ode (f g l m : PowerSeries ℂ)
    (h0 : constantCoeff f = constantCoeff g)
    (hf : X * derivative f = l * f) (hg : X * derivative g = m * g)
    (hm : coeff 0 m = 0) (d : ℕ) (hlm : ∀ j ≤ d, coeff j l = coeff j m) :
    coeff d f = coeff d g := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases hd : d = 0
    · simpa [hd, coeff_zero_eq_constantCoeff] using h0
    have hF := congrArg (coeff d) hf
    have hG := congrArg (coeff d) hg
    rw [coeff_euler, coeff_mul] at hF hG
    apply mul_left_cancel₀ (show (d : ℂ) ≠ 0 by exact_mod_cast hd)
    rw [hF, hG]
    refine Finset.sum_congr rfl fun ab hab => ?_
    have hab' : ab.1 + ab.2 = d := by simpa using hab
    rw [hlm ab.1 (by omega)]
    by_cases ha : ab.1 = 0
    · simp [ha, hm]
    · have hlt : ab.2 < d := by omega
      rw [ih ab.2 hlt (fun j hj => hlm j (hj.trans hlt.le))]

private theorem finiteEulerProduct_ode (s : Finset ℕ) :
    X * derivative (∏ i ∈ s, macmahonEulerFactor i) =
      finiteEulerLog s * ∏ i ∈ s, macmahonEulerFactor i :=
  euler_prod _ _ macmahonEulerFactor_ode s

private theorem coeff_finiteEulerProduct_stable (d : ℕ) (s t : Finset ℕ)
    (hs : Finset.range d ⊆ s) (ht : Finset.range d ⊆ t) :
    coeff d (∏ i ∈ s, macmahonEulerFactor i) = coeff d (∏ i ∈ t, macmahonEulerFactor i) := by
  apply coeff_ext_ode _ _ _ _ (by simp) (finiteEulerProduct_ode s) (finiteEulerProduct_ode t)
  · rw [coeff_finiteEulerLog 0 t (by simp)]
    simp [macmahonDivisorSeries]
  · intro j hj
    rw [coeff_finiteEulerLog j s ((Finset.range_mono hj).trans hs),
      coeff_finiteEulerLog j t ((Finset.range_mono hj).trans ht)]

/-- The coefficientwise limit of the partial MacMahon products, defined by exact truncation. -/
@[expose] def macmahonProductLimit : PowerSeries ℂ :=
  PowerSeries.mk fun d => coeff d (∏ i ∈ Finset.range d, macmahonEulerFactor i)

/-- Every finite product containing the contributing factors yields the stabilized coefficient. -/
theorem coeff_macmahonProductLimit (d : ℕ) (s : Finset ℕ) (hs : Finset.range d ⊆ s) :
    coeff d (∏ i ∈ s, macmahonEulerFactor i) = coeff d macmahonProductLimit := by
  rw [macmahonProductLimit, coeff_mk]
  exact coeff_finiteEulerProduct_stable d s (Finset.range d) hs (by rfl)

@[simp] theorem macmahonProductLimit_constantCoeff : constantCoeff macmahonProductLimit = 1 := by
  simp [macmahonProductLimit]

/-- The logarithmic derivative of the coefficientwise Euler product is the divisor-square series. -/
theorem macmahonProductLimit_ode :
    X * derivative macmahonProductLimit = macmahonDivisorSeries * macmahonProductLimit := by
  ext d
  let s := Finset.range d
  have h := congrArg (coeff d) (finiteEulerProduct_ode s)
  rw [coeff_euler, coeff_mul] at h ⊢
  rw [← coeff_macmahonProductLimit d s (by rfl), h]
  refine Finset.sum_congr rfl fun ab hab => ?_
  have hsum : ab.1 + ab.2 = d := by simpa using hab
  rw [coeff_finiteEulerLog ab.1 s (Finset.range_mono (by omega)),
    coeff_macmahonProductLimit ab.2 s (Finset.range_mono (by omega))]

/-- The literal Euler product converges as an unordered product in the coefficientwise topology. -/
theorem hasProd_macmahonProductLimit :
    HasProd (fun i : ℕ => ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ (i + 1))
      macmahonProductLimit := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℂ _ _ _).2
  intro d
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (Finset.range d)] with s hs
  exact (coeff_macmahonProductLimit d s hs).symm

/-- Any normalized solution of MacMahon's formal differential equation has the exact
finite-product coefficients, in each degree in which all contributing factors are present. -/
theorem coeff_macmahonEulerProduct_of_ode {f : PowerSeries ℂ}
    (h0 : constantCoeff f = 1) (hODE : X * derivative f = macmahonDivisorSeries * f)
    (d : ℕ) (s : Finset ℕ) (hs : Finset.range d ⊆ s) :
    coeff d (∏ i ∈ s, macmahonEulerFactor i) = coeff d f := by
  apply coeff_ext_ode _ _ _ _ (by simp [h0]) (finiteEulerProduct_ode s) hODE
  · simp [macmahonDivisorSeries]
  · exact fun j hj => coeff_finiteEulerLog j s ((Finset.range_mono hj).trans hs)

/-- The normalized formal differential equation identifies the *literal* product. -/
theorem hasProd_macmahonEulerProduct_of_ode {f : PowerSeries ℂ}
    (h0 : constantCoeff f = 1) (hODE : X * derivative f = macmahonDivisorSeries * f) :
    HasProd (fun i : ℕ => ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ (i + 1)) f := by
  convert hasProd_macmahonProductLimit using 1
  ext d
  rw [macmahonProductLimit, coeff_mk]
  exact (coeff_macmahonEulerProduct_of_ode h0 hODE d (Finset.range d) (by rfl)).symm

end PakPrimes.DivisorAndMacMahon
