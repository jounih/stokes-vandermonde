module

public import PakPrimes.MacMahonEulerProduct
public import Mathlib.RingTheory.PowerSeries.Expand

/-! # Harmonic-trap Bose products

The shell indexed by `k` has degeneracy `(k+2).choose 2`. With zero-point energy
three half-quanta, its energy in half-quanta is `2*k+3`. Raising every energy by
half a quantum gives energy `k+2` in full quanta. Both products are at unit fugacity.
-/

public section
noncomputable section
namespace PakPrimes.HarmonicTrap
open PakPrimes.DivisorAndMacMahon PowerSeries Filter
open scoped PowerSeries.WithPiTopology Topology BigOperators

private def factor (g : ℕ → ℕ) (i : ℕ) : PowerSeries ℂ :=
  ((1 - X ^ (i+1))⁻¹) ^ g (i+1)

private def term (g : ℕ → ℕ) (i : ℕ) : PowerSeries ℂ :=
  C (((i+1 : ℕ) : ℂ) * (g (i+1) : ℂ)) * (EulerGeometric i - 1)

/-- The coefficient of the Euler logarithmic derivative is the divisor sum of
mode number times mode degeneracy. -/
@[expose] def modeSum (g : ℕ → ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => ∑ d ∈ n.divisors, (d : ℂ) * (g d : ℂ)

private lemma coeff_sum (g : ℕ → ℕ) (d : ℕ) (S : Finset ℕ) (h : Finset.range d ⊆ S) :
    coeff d (∑ i ∈ S, term g i) = coeff d (modeSum g) := by
  classical
  by_cases hd : d = 0
  · subst d
    simp [term, modeSum, PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [term, map_sum, PowerSeries.coeff_C_mul, map_sub, EulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, hd, ite_false, sub_zero, mul_ite, mul_one,
    mul_zero, modeSum]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hi).2, hd⟩
  · intro i hi j hj hij
    omega
  · intro j hj
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hj
    have hjpos := Nat.pos_of_mem_divisors hj
    have hjle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd
    have hsucc : j - 1 + 1 = j := by omega
    refine ⟨j - 1, Finset.mem_filter.mpr ⟨h (Finset.mem_range.mpr (by omega)), ?_⟩, hsucc⟩
    simpa only [hsucc] using hdvd


private lemma factor_ode (g : ℕ → ℕ) (i : ℕ) :
    X * derivative (factor g i) = term g i * factor g i := by
  have h : EulerGeometric i - 1 = X ^ (i+1) * EulerGeometric i := by
    have hden : EulerGeometric i * (1 - X ^ (i+1)) = 1 :=
      (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mp (EulerGeometric_eq_inv i)
    linear_combination hden
  have hc : C (((i+1 : ℕ) : ℂ) * (g (i+1) : ℂ)) =
      ((i : PowerSeries ℂ)+1) * (g (i+1) : PowerSeries ℂ) := by rw [map_mul, map_natCast, map_natCast, Nat.cast_add, Nat.cast_one]
  rw [factor, term, hc, h, EulerGeometric_eq_inv]
  cases he : g (i+1) with
  | zero => simp
  | succ e =>
    rw [derivative_pow, derivative_inv', map_sub, derivative_one, derivative_X_pow_succ]
    simp only [Nat.add_sub_cancel, zero_sub, neg_mul_neg,
      map_add, map_natCast, map_one, pow_succ, Nat.cast_succ]
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


private lemma stable (g : ℕ → ℕ) (d : ℕ) (s t : Finset ℕ)
    (hs : Finset.range d ⊆ s) (ht : Finset.range d ⊆ t) :
    coeff d (∏ i ∈ s, factor g i) = coeff d (∏ i ∈ t, factor g i) := by
  apply coeff_ext_ode _ _ _ _ (by simp [factor, PowerSeries.constantCoeff_inv])
    (euler_prod _ _ (factor_ode g) s) (euler_prod _ _ (factor_ode g) t)
  · rw [coeff_sum g 0 t (by simp)]
    simp [modeSum]
  · intro j hj
    rw [coeff_sum g j s ((Finset.range_mono hj).trans hs),
      coeff_sum g j t ((Finset.range_mono hj).trans ht)]

private def limitProduct (g : ℕ → ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun d => coeff d (∏ i ∈ Finset.range d, factor g i)

private lemma finite_coeff (g : ℕ → ℕ) (d : ℕ) (s : Finset ℕ) (hs : Finset.range d ⊆ s) :
    coeff d (∏ i ∈ s, factor g i) = coeff d (limitProduct g) := by
  rw [limitProduct, coeff_mk]
  exact stable _ _ _ _ hs (by rfl)

/-- The canonical Bose product with nonnegative integer mode degeneracies. -/
@[expose] def bose (g : ℕ → ℕ) : PowerSeries ℂ :=
  ∏' i : ℕ, ((1 - (X : PowerSeries ℂ)^(i+1))⁻¹)^(g (i+1))

private lemma hasProd_limit (g : ℕ → ℕ) : HasProd (factor g) (limitProduct g) := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℂ _ _ _).2
  intro d
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (Finset.range d)] with s hs
  exact (finite_coeff _ _ _ hs).symm

/-- Unordered, coefficientwise convergence of the literal Euler product. -/
theorem hasProd_bose (g : ℕ → ℕ) : HasProd
    (fun i : ℕ => ((1 - (X : PowerSeries ℂ)^(i+1))⁻¹)^(g (i+1))) (bose g) :=
  (hasProd_limit g).multipliable.hasProd

@[simp] theorem bose_constantCoeff (g : ℕ → ℕ) : constantCoeff (bose g) = 1 := by
  change constantCoeff (∏' i, factor g i) = 1
  rw [(hasProd_limit g).tprod_eq]
  simp [limitProduct]

theorem bose_euler (g : ℕ → ℕ) :
    X * derivative (bose g) = modeSum g * bose g := by
  change X * derivative (∏' i, factor g i) = modeSum g * ∏' i, factor g i
  rw [(hasProd_limit g).tprod_eq]
  ext d
  let s := Finset.range d
  have h := congrArg (coeff d) (euler_prod _ _ (factor_ode g) s)
  rw [coeff_euler, coeff_mul] at h ⊢
  rw [← finite_coeff g d s (by rfl), h]
  refine Finset.sum_congr rfl fun ab hab => ?_
  have hsum : ab.1 + ab.2 = d := by simpa using hab
  rw [coeff_sum g ab.1 s (Finset.range_mono (by omega)),
    finite_coeff g ab.2 s (Finset.range_mono (by omega))]

private lemma choose_succ_two (k : ℕ) : 2 * ((k+1).choose 2 : ℂ) = (k+1 : ℂ)*k := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k+1) 2
  simp [Nat.descFactorial, Nat.factorial] at h
  exact_mod_cast (by nlinarith [h] : 2 * (k+1).choose 2 = (k+1)*k)

/-- Raising all levels by half a quantum, with the full quantum as unit of energy. -/
theorem shifted_log :
    2 * modeSum (fun d => d.choose 2) = sigmaSeries 3 - sigmaSeries 2 := by
  ext n
  change coeff n (C (2 : ℂ) * _) = _
  simp only [coeff_C_mul, modeSum, sigmaSeries, coeff_mk, map_sub]
  by_cases hn : n=0
  · simp [hn]
  simp only [hn, ite_false, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  cases d with
  | zero => simp
  | succ k =>
    push_cast
    linear_combination ((k:ℂ)+1) * choose_succ_two k

theorem shifted_product_ode :
    2 * (X * derivative (bose (fun d => d.choose 2))) =
      (sigmaSeries 3 - sigmaSeries 2) * bose (fun d => d.choose 2) := by
  rw [bose_euler, ← mul_assoc, shifted_log]


/-- In the half-quantum nome, shell `k` occupies odd degree `2*k+3`. -/
@[expose] def centeredDeg (d : ℕ) : ℕ :=
  if 2 ∣ d then 0 else (d/2+1).choose 2

theorem centeredDeg_shell (k : ℕ) : centeredDeg (2*k+3) = (k+2).choose 2 := by
  simp only [centeredDeg, show ¬2∣2*k+3 by omega, ite_false]
  congr 1
  omega

private lemma centered_weight (d : ℕ) :
    8 * (d:ℂ) * (centeredDeg d : ℂ) =
      (if 2 ∣ d then 0 else (d:ℂ)^3) - (if 2 ∣ d then 0 else (d:ℂ)) := by
  by_cases h : 2 ∣ d
  · simp [centeredDeg, h]
  · let r := d / 2
    have hd : d = 2*r+1 := by dsimp [r]; omega
    have he : d / 2 = r := rfl
    simp only [centeredDeg, h, ite_false, he]
    rw [hd]
    push_cast
    linear_combination 4 * (2*(r:ℂ)+1) * choose_succ_two r

private lemma coeff_sigma (k n : ℕ) :
    coeff n (sigmaSeries k) = ∑ d ∈ n.divisors, (d:ℂ)^k := by
  by_cases h : n = 0 <;> simp [sigmaSeries, h]

private lemma even_divisors (k n : ℕ) :
    ∑ d ∈ n.divisors.filter (2 ∣ ·), (d:ℂ)^k =
      (2:ℂ)^k * coeff n (expand 2 (by decide) (sigmaSeries k)) := by
  classical
  by_cases h : 2 ∣ n
  · obtain ⟨r, rfl⟩ := h
    rw [coeff_expand_mul, coeff_sigma, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun d _ => 2*d) ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdr, hr⟩ := Nat.mem_divisors.mp hd
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul_left 2 hdr, by omega⟩, dvd_mul_right 2 d⟩
    · intro x hx y hy hxy
      omega
    · intro e he
      obtain ⟨her, d, rfl⟩ := Finset.mem_filter.mp he
      obtain ⟨hdr, hr⟩ := Nat.mem_divisors.mp her
      obtain ⟨c, hc⟩ := hdr
      refine ⟨d, Nat.mem_divisors.mpr ⟨⟨c, ?_⟩, by omega⟩, rfl⟩
      nlinarith [hc]
    · intro d hd
      push_cast
      ring
  · rw [coeff_expand_of_not_dvd _ _ _ h, mul_zero]
    apply Finset.sum_eq_zero
    intro d hd
    exact (h ((Finset.mem_filter.mp hd).2.trans
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1)).elim

private lemma odd_divisors (k n : ℕ) :
    ∑ d ∈ n.divisors, (if 2 ∣ d then 0 else (d:ℂ)^k) =
      coeff n (sigmaSeries k) - (2:ℂ)^k * coeff n (expand 2 (by decide) (sigmaSeries k)) := by
  rw [coeff_sigma, ← even_divisors, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp

/-- Exact Euler logarithmic derivative in the half-quantum nome. -/
theorem centered_log :
    8 * modeSum centeredDeg =
      (sigmaSeries 3 - 8 * expand 2 (by decide) (sigmaSeries 3)) -
      (sigmaSeries 1 - 2 * expand 2 (by decide) (sigmaSeries 1)) := by
  ext n
  change coeff n (C (8:ℂ) * _) =
    coeff n ((sigmaSeries 3 - C (8:ℂ) * _) - (sigmaSeries 1 - C (2:ℂ) * _))
  simp only [coeff_C_mul, modeSum, coeff_mk, map_sub]
  rw [Finset.mul_sum]
  conv_lhs =>
    enter [2, d]
    rw [← mul_assoc, centered_weight]
  rw [Finset.sum_sub_distrib, odd_divisors]
  have h := odd_divisors 1 n
  simp only [pow_one] at h
  rw [h]
  norm_num

theorem centered_product_ode :
    8 * (X * derivative (bose centeredDeg)) =
      ((sigmaSeries 3 - 8 * expand 2 (by decide) (sigmaSeries 3)) -
       (sigmaSeries 1 - 2 * expand 2 (by decide) (sigmaSeries 1))) * bose centeredDeg := by
  rw [bose_euler, ← mul_assoc, centered_log]


/-- Lowering every centered energy by half a quantum replaces the multiplicity
at full energy `d` by `(d+1).choose 2`. Relative to the upwards shift,
the extra multiplicity is `d`, the MacMahon exponent. -/
theorem opposite_shifts_product :
    bose (fun d => (d+1).choose 2) = macmahonSeries * bose (fun d => d.choose 2) := by
  have h := hasProd_macmahonEulerProduct.mul (hasProd_bose (fun d => d.choose 2))
  have hfun (n : ℕ) : (n+1).choose 2 = n + n.choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  simpa only [bose, hfun, pow_add] using h.tprod_eq

/-- A ratio of literal trap partition products equals the MacMahon series. -/
theorem opposite_shifts_ratio :
    bose (fun d => (d+1).choose 2) * (bose (fun d => d.choose 2))⁻¹ = macmahonSeries := by
  rw [opposite_shifts_product, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]

/-- The nome and every ordinary derivative of the opposite-shift ratio
are algebraically independent over the complex constants. -/
theorem opposite_shifts_ratio_algebraicIndependent :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates
      (bose (fun d => (d+1).choose 2) * (bose (fun d => d.choose 2))⁻¹)) := by
  rw [opposite_shifts_ratio]
  exact macmahonSeries_algebraicIndependent


/-- A `dimension`-dimensional oscillator with ground energy `ground` (in oscillator
quanta) has one state for each weak composition of its excess energy. The
formula below is used for positive dimension and positive ground energy. -/
@[expose] def shellMultiplicity (dimension ground n : ℕ) : ℕ :=
  if ground ≤ n then (n - ground + (dimension-1)).choose (dimension-1) else 0

/-- Literal isotropic grand partition product, at unit fugacity. -/
@[expose] def trap (dimension ground : ℕ) : PowerSeries ℂ :=
  bose (shellMultiplicity dimension ground)

private theorem multiplicity_descent (dim r n : ℕ) :
    shellMultiplicity (dim+2) r n =
      shellMultiplicity (dim+2) (r+1) n + shellMultiplicity (dim+1) r n := by
  by_cases h : n < r
  · simp [shellMultiplicity, show ¬ r ≤ n by omega, show ¬ r+1 ≤ n by omega]
  by_cases he : n=r
  · subst n
    simp [shellMultiplicity]
  have hn : r+1 ≤ n := by omega
  simp only [shellMultiplicity, (show r ≤ n by omega), hn, ite_true,
    Nat.add_sub_cancel]
  let a := n - (r+1) + (dim+1)
  have h1 : n-r + (dim+1) = a+1 := by dsimp [a]; omega
  have h2 : n-r + dim = a := by dsimp [a]; omega
  change (n-r+(dim+1)).choose (dim+1) = a.choose (dim+1) + (n-r+dim).choose dim
  rw [h1, h2, Nat.choose_succ_succ, Nat.add_comm]

/-- Raising the ground energy by one quantum removes one entire oscillator of one
lower dimension, coefficient by coefficient in the grand product. -/
theorem trap_dimension_descent (dim r : ℕ) :
    trap (dim+2) (r+1) = trap (dim+2) (r+2) * trap (dim+1) (r+1) := by
  have h := (hasProd_bose (shellMultiplicity (dim+2) (r+2))).mul
    (hasProd_bose (shellMultiplicity (dim+1) (r+1)))
  have hi (n : ℕ) := multiplicity_descent dim (r+1) n
  simpa only [trap, bose, hi, pow_add] using h.tprod_eq

/-- The adjacent-ground ratio in dimension at least two is itself a literal
lower-dimensional Bose product, with the lower of the two ground energies. -/
theorem trap_adjacent_ratio (dim r : ℕ) :
    trap (dim+2) (r+1) * (trap (dim+2) (r+2))⁻¹ = trap (dim+1) (r+1) := by
  have h0 : constantCoeff (trap (dim+2) (r+2)) ≠ 0 := by simp [trap]
  rw [trap_dimension_descent, mul_comm (trap (dim+2) (r+2)), mul_assoc,
    PowerSeries.mul_inv_cancel _ h0, mul_one]


/-- Multiplicative first difference of a family parametrized by its ground energy. -/
@[expose] def adjacentRatio (F : ℕ → PowerSeries ℂ) : ℕ → PowerSeries ℂ :=
  fun r => F r * (F (r+1))⁻¹

theorem iterated_trap_descent (k d : ℕ) :
    adjacentRatio^[k] (fun r => trap (d+1+k) (r+1)) = (fun r => trap (d+1) (r+1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have h : adjacentRatio (fun r => trap (d+1+(k+1)) (r+1)) =
        (fun r => trap (d+1+k) (r+1)) := by
      funext r
      simpa only [adjacentRatio, show d+1+(k+1) = (d+k)+2 by omega,
        show d+1+k = (d+k)+1 by omega] using trap_adjacent_ratio (d+k) r
    rw [h, ih]

theorem trap_two_ground_one : trap 2 1 = macmahonSeries := by
  rw [← hasProd_macmahonEulerProduct.tprod_eq]
  unfold trap bose
  congr 1
  funext i
  simp [shellMultiplicity, Nat.choose_one_right]

/-- For every spatial dimension `k+2`, the `k`th shift ratio of the actual
grand products at ground energies starting at one is exactly MacMahon's series.
Its nome and full ordinary jet are algebraically independent. -/
theorem iterated_trap_ratio_algebraicIndependent (k : ℕ) :
    AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates
      ((adjacentRatio^[k] (fun r => trap (2+k) (r+1))) 0)) := by
  rw [iterated_trap_descent k 1]
  change AlgebraicIndependent ℂ (PakPrimes.PrimeNome.seriesCoordinates (trap 2 1))
  rw [trap_two_ground_one]
  exact macmahonSeries_algebraicIndependent

end PakPrimes.HarmonicTrap
