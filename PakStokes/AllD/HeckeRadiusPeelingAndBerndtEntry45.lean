module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Berndt's Notebooks V Entry 45 Stieltjes Indeterminacy, Gross CM Hecke Radius Separation, Abstract Multivariate Radius Peeling, and Ramanujan's LN p. 343 Hidden Units

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard foundations only)
of four results from Ramanujan Waves 12–16:

1. **Settling Bruce Berndt's Open Remark on Ramanujan's `Notebooks V Ch. 32 Entry 45`:**
   - Defines the Stieltjes weight `entry45Weight v = v ^ (-1/2) / sinh(π v^(1/4))` and the
     constructive oscillatory perturbation
     `entry45Perturb v = exp(-2 π v^(1/4)) * sin(2 π v^(1/4))` on `v > 0`.
   - Proves `entry45Perturb_abs_le_const_mul_weight` and `entry45Perturb_abs_lt_weight`:
     `|entry45Perturb v| ≤ (2 / (π² e²)) * entry45Weight v < entry45Weight v` for all `v > 0`.
   - Proves `entry45Weight_moment_integrable` and `entry45Perturb_moment_integrable` on `(0, ∞)`
     for every `k : ℕ`.
   - Proves `entry45ComplexIntegral_eq` and `entry45Perturb_moment_zero`:
     `∫ v in Set.Ioi 0, v ^ k * entry45Perturb v = 0` for every `k : ℕ`, directly via the exact
     complex antiderivative and `(1 - I)^4 = -4 ∈ ℝ`.
   - Proves `entry45_stieltjes_indeterminate`: for every `ε ∈ [-1, 1]`,
     `w_ε(v) = entry45Weight v + ε * entry45Perturb v` is strictly positive on `(0, ∞)`, distinct
     both pointwise and as Borel measures for `ε₁ ≠ ε₂`, and shares identical `k`-th Stieltjes
     moments for every `k : ℕ`.

2. **Exact Gross CM Hecke Radius Separation (`> 1.7×`):**
   - Proves `exp_five_gt_128` (`128 < exp 5`), `pi_mul_sqrt_eleven_gt_ten` (`10 < π √11`),
     and `grossS_lt_inv_16384` (`exp(-π √ℓ) < 1 / 16384` for all `ℓ ≥ 11`).
   - Proves `nat_cube_le_eight_pow` (`(n + 1)^3 ≤ 8^n`) and the exact Lambert-series bound
     `‖E_4(q) - 1‖ ≤ 240 s / ((1 - s)(1 - 8 s)) < 1 / 64` for `‖q‖ ≤ s < 1 / 16384`.
   - Establishes the five exact rational intervals for `ρ_ℓ^2 / π^2 = ℓ |E_4(τ_ℓ)| / (3 g_{2,ℓ})`
     at `ℓ ∈ {163, 67, 43, 19, 11}`, proves every consecutive ratio satisfies
     `lower_{i+1} / upper_i ≥ 189 / 65 > (17 / 10)^2`, and deduces both
     `grossRadius_consecutive_ratio_gt` (`1.7 < ρ_{i+1} / ρ_i`) and strict monotonicity
     `grossRadius_strictMono` (`ρ_{163} < ρ_{67} < ρ_{43} < ρ_{19} < ρ_{11}`).

3. **Abstract Multivariate Natural-Boundary Radius Peeling Theorem:**
   - Proves the `CharZero` minimal-order / minimal-top-jet-degree separant nonvanishing theorem
     `exists_minimal_relation_nonzero_separant` in `MvPolynomial`.
   - Proves `radius_peeling_joint_diff_indep` and `radius_peeling_over_baseField`: backward
     induction peeling off `f_0, ..., f_{m-1}` with strictly increasing radii `r_0 < ... < r_{m-1}`
     over an already-independent entire-Borel base family `E`, establishing joint differential
     independence over both `K` and `K⟨E⟩`.
   - Instantiates the two-stage **10-Series Gross CM Theorem** (`grossCM_ten_series_radius_peeling`)
     using our proved `grossRadius_strictMono`, and the **Universal Pair Peeling Theorem**
     (`universal_pair_radius_peeling`).

4. **Ramanujan's Lost Notebook p. 343 Hidden Units in `ℤ[⁵√2]^×` (and `ℤ[⁷√2]^×`):**
   - Over any commutative ring with `θ^5 = 2`, proves `(1 + θ^2)^5 = 5 (1 + θ + θ^3)^2` and
     `(1 + θ + θ^3)(1 - θ - θ^2 + θ^4) = 1`.
   - Specializes to `θ = 2^(1/5) ∈ ℝ`, proves
     `√5 / (1 + 2^(2/5))^(5/2) = 1 - θ - θ^2 + θ^4`, and constructs it explicitly as a unit
     in the subring `ℤ[⁵√2] = Algebra.adjoin ℤ {2^(1/5)}`.
   - Bonus: verifies all three Block 2 generators in `ℤ[⁷√2]^×` for any commutative ring with
     `θ^7 = 2`.
-/

public section

namespace CubicTheta.AllD

open Complex Filter MeasureTheory MvPolynomial Set
open scoped BigOperators Classical Topology

noncomputable section

/-! ### 1. Settling Berndt's Open Remark on Ramanujan's `Notebooks V Ch. 32 Entry 45` -/

section BerndtEntry45

/-- Stieltjes density `w(v) = v^(-1/2) / sinh(π v^(1/4))` for Ramanujan's `Notebooks V`
Ch. 32 Entry 45 moment sequence `μ_k = ∫_0^∞ v^k w(v) dv`. -/
def entry45Weight (v : ℝ) : ℝ :=
  v ^ (-(1 : ℝ) / 2) / Real.sinh (Real.pi * v ^ ((1 : ℝ) / 4))

/-- Constructive oscillatory zero-moment perturbation
`h(v) = exp(-2 π v^(1/4)) * sin(2 π v^(1/4))` on `(0, ∞)`. -/
def entry45Perturb (v : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4)) * Real.sin (2 * Real.pi * v ^ ((1 : ℝ) / 4))

/-- One-parameter family of perturbed Stieltjes densities `w_ε(v) = w(v) + ε h(v)`. -/
def entry45PerturbedWeight (ε : ℝ) (v : ℝ) : ℝ :=
  entry45Weight v + ε * entry45Perturb v

/-- Complex decay parameter `α = 2 π (1 - I)` governing the Entry 45 perturbation moments. -/
def entry45Alpha : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * (1 - Complex.I)

/-- Explicit elementary antiderivative of `u ↦ u^n * exp(-α * u)` in `u`:
`F_n(α, u) = -exp(-α u) ∑_{j=0}^n (n! / j!) u^j / α^(n + 1 - j)`. -/
def entry45ComplexAntideriv (n : ℕ) (α : ℂ) (u : ℝ) : ℂ :=
  -Complex.exp (-α * (u : ℂ)) *
    ∑ j ∈ Finset.range (n + 1),
      ((n.factorial : ℂ) / (j.factorial : ℂ)) * ((u : ℂ) ^ j / α ^ (n + 1 - j))

/-- Composite antiderivative `G_k(v) = 4 * F_{4k+3}(α, v^(1/4))` of
`v ↦ v^k * exp(-2 π (1 - I) v^(1/4))` on `(0, ∞)`. -/
def entry45MomentAntideriv (k : ℕ) (v : ℝ) : ℂ :=
  4 * entry45ComplexAntideriv (4 * k + 3) entry45Alpha (v ^ ((1 : ℝ) / 4))

private lemma sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  linarith

private lemma self_le_sinh_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  · by_contra hlt
    push Not at hlt
    have hle : Real.sinh x ≤ x := le_of_lt hlt
    have hx0 : x ≤ 0 := Real.sinh_le_self_iff.mp hle
    linarith

private lemma sinh_lt_half_exp_of_pos {x : ℝ} :
    Real.sinh x < Real.exp x / 2 := by
  rw [Real.sinh_eq]
  have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
  linarith

private lemma quarter_exp_le_sinh {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h2x : (2 : ℝ) ≤ Real.exp (2 * x) := by
    have h1 := Real.add_one_le_exp (2 * x)
    linarith
  have hmul : Real.exp (-x) * Real.exp (2 * x) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hle : 2 * Real.exp (-x) ≤ Real.exp x := by
    calc
      2 * Real.exp (-x) ≤ Real.exp (2 * x) * Real.exp (-x) := by
        exact mul_le_mul_of_nonneg_right h2x (Real.exp_pos (-x)).le
      _ = Real.exp x := by rw [mul_comm, hmul]
  linarith

/-- Strict positivity of `entry45Weight` on `(0, ∞)`. -/
theorem entry45Weight_pos {v : ℝ} (hv : 0 < v) : 0 < entry45Weight v := by
  unfold entry45Weight
  apply div_pos
  · exact Real.rpow_pos_of_pos hv _
  · apply sinh_pos_of_pos
    exact mul_pos Real.pi_pos (Real.rpow_pos_of_pos hv _)

private lemma exp_neg_two_pi_le_const_mul_weight {v : ℝ} (hv : 0 < v) :
    Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4)) ≤
      (2 / (Real.pi ^ 2 * Real.exp 2)) * entry45Weight v := by
  set u : ℝ := v ^ ((1 : ℝ) / 4)
  have hu : 0 < u := Real.rpow_pos_of_pos hv _
  have hu_sq : u ^ 2 * v ^ (-(1 : ℝ) / 2) = 1 := by
    have h1 : u ^ 2 = v ^ ((1 : ℝ) / 2) := by
      dsimp [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
      congr 1
      norm_num
    rw [h1, ← Real.rpow_add hv]
    norm_num
  have hpiu : 0 < Real.pi * u := mul_pos Real.pi_pos hu
  have hsinh_pos : 0 < Real.sinh (Real.pi * u) := sinh_pos_of_pos hpiu
  have hsinh_lt : Real.sinh (Real.pi * u) < Real.exp (Real.pi * u) / 2 :=
    sinh_lt_half_exp_of_pos
  -- Elementary bound: (π u / 2) ≤ exp(π u / 2 - 1), hence u² exp(-π u) ≤ 4 / (π² e²).
  have ht_le : Real.pi * u / 2 ≤ Real.exp (Real.pi * u / 2 - 1) := by
    have h := Real.add_one_le_exp (Real.pi * u / 2 - 1)
    linarith
  have ht_sq : (Real.pi * u / 2) ^ 2 ≤ Real.exp (Real.pi * u - 2) := by
    have hnn : 0 ≤ Real.pi * u / 2 := by positivity
    have hsq := mul_self_le_mul_self hnn ht_le
    calc
      (Real.pi * u / 2) ^ 2 = (Real.pi * u / 2) * (Real.pi * u / 2) := sq _
      _ ≤ Real.exp (Real.pi * u / 2 - 1) * Real.exp (Real.pi * u / 2 - 1) := hsq
      _ = Real.exp (Real.pi * u - 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hexp_split : Real.exp (Real.pi * u - 2) = Real.exp (Real.pi * u) / Real.exp 2 :=
    Real.exp_sub (Real.pi * u) 2
  have hu2_exp : u ^ 2 * Real.exp (-(Real.pi * u)) ≤ 4 / (Real.pi ^ 2 * Real.exp 2) := by
    have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have he2 : 0 < Real.exp 2 := Real.exp_pos 2
    have h1 : Real.pi ^ 2 * u ^ 2 ≤ 4 * (Real.exp (Real.pi * u) / Real.exp 2) := by
      rw [hexp_split] at ht_sq
      nlinarith
    have h2 : u ^ 2 ≤ 4 * Real.exp (Real.pi * u) / (Real.pi ^ 2 * Real.exp 2) := by
      rw [le_div_iff₀ (mul_pos hpi2 he2)]
      have h1' : Real.pi ^ 2 * u ^ 2 * Real.exp 2 ≤ 4 * Real.exp (Real.pi * u) := by
        have := mul_le_mul_of_nonneg_right h1 he2.le
        field_simp at this ⊢
        linarith
      linarith
    calc
      u ^ 2 * Real.exp (-(Real.pi * u))
          ≤ (4 * Real.exp (Real.pi * u) / (Real.pi ^ 2 * Real.exp 2)) *
              Real.exp (-(Real.pi * u)) := by
            exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 4 / (Real.pi ^ 2 * Real.exp 2) := by
            rw [Real.exp_neg]
            have hexp_ne : Real.exp (Real.pi * u) ≠ 0 := (Real.exp_pos _).ne'
            field_simp
  have hmain : Real.exp (-2 * Real.pi * u) * Real.sinh (Real.pi * u) * u ^ 2 ≤
      2 / (Real.pi ^ 2 * Real.exp 2) := by
    have hstep1 : Real.exp (-2 * Real.pi * u) * Real.sinh (Real.pi * u) ≤
        Real.exp (-(Real.pi * u)) / 2 := by
      calc
        Real.exp (-2 * Real.pi * u) * Real.sinh (Real.pi * u)
            ≤ Real.exp (-2 * Real.pi * u) * (Real.exp (Real.pi * u) / 2) :=
              mul_le_mul_of_nonneg_left hsinh_lt.le (Real.exp_pos _).le
        _ = (Real.exp (-2 * Real.pi * u) * Real.exp (Real.pi * u)) / 2 := by ring
        _ = Real.exp (-(Real.pi * u)) / 2 := by
              rw [← Real.exp_add]
              congr 2
              ring
    calc
      Real.exp (-2 * Real.pi * u) * Real.sinh (Real.pi * u) * u ^ 2
          ≤ (Real.exp (-(Real.pi * u)) / 2) * u ^ 2 :=
            mul_le_mul_of_nonneg_right hstep1 (sq_nonneg u)
      _ = (u ^ 2 * Real.exp (-(Real.pi * u))) / 2 := by ring
      _ ≤ (4 / (Real.pi ^ 2 * Real.exp 2)) / 2 := by linarith
      _ = 2 / (Real.pi ^ 2 * Real.exp 2) := by ring
  have hw_eq : entry45Weight v = 1 / (u ^ 2 * Real.sinh (Real.pi * u)) := by
    unfold entry45Weight
    have hu2_ne : u ^ 2 ≠ 0 := (sq_pos_of_pos hu).ne'
    have hvr : v ^ (-(1 : ℝ) / 2) = 1 / u ^ 2 := by
      field_simp
      linarith
    rw [hvr, div_div]
  rw [hw_eq]
  have hden : 0 < u ^ 2 * Real.sinh (Real.pi * u) := mul_pos (sq_pos_of_pos hu) hsinh_pos
  calc
    Real.exp (-2 * Real.pi * u)
        = (Real.exp (-2 * Real.pi * u) * Real.sinh (Real.pi * u) * u ^ 2) /
            (u ^ 2 * Real.sinh (Real.pi * u)) := by
          have hs_ne : Real.sinh (Real.pi * u) ≠ 0 := hsinh_pos.ne'
          have hu2_ne : u ^ 2 ≠ 0 := (sq_pos_of_pos hu).ne'
          field_simp
    _ ≤ (2 / (Real.pi ^ 2 * Real.exp 2)) / (u ^ 2 * Real.sinh (Real.pi * u)) :=
          div_le_div_of_nonneg_right hmain hden.le
    _ = (2 / (Real.pi ^ 2 * Real.exp 2)) * (1 / (u ^ 2 * Real.sinh (Real.pi * u))) := by ring

/-- Sharp uniform ratio bound `|entry45Perturb v| ≤ (2 / (π² e²)) * entry45Weight v` for `v > 0`. -/
theorem entry45Perturb_abs_le_const_mul_weight {v : ℝ} (hv : 0 < v) :
    |entry45Perturb v| ≤ (2 / (Real.pi ^ 2 * Real.exp 2)) * entry45Weight v := by
  have habs_pert : |entry45Perturb v| ≤ Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4)) := by
    unfold entry45Perturb
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hsin : |Real.sin (2 * Real.pi * v ^ ((1 : ℝ) / 4))| ≤ 1 := Real.abs_sin_le_one _
    calc
      Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4)) * |Real.sin (2 * Real.pi * v ^ ((1 : ℝ) / 4))|
          ≤ Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4)) * 1 :=
            mul_le_mul_of_nonneg_left hsin (Real.exp_pos _).le
      _ = Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4)) := mul_one _
  exact le_trans habs_pert (exp_neg_two_pi_le_const_mul_weight hv)

/-- The uniform Entry 45 ratio bound `2 / (π² e²)` is strictly less than `1`. -/
theorem entry45_ratio_const_lt_one : 2 / (Real.pi ^ 2 * Real.exp 2) < 1 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have he : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hden : 2 < Real.pi ^ 2 * Real.exp 2 := by nlinarith
  rw [div_lt_one (by positivity)]
  exact hden

/-- Strict pointwise domination `|entry45Perturb v| < entry45Weight v` for all `v > 0`. -/
theorem entry45Perturb_abs_lt_weight {v : ℝ} (hv : 0 < v) :
    |entry45Perturb v| < entry45Weight v := by
  calc
    |entry45Perturb v|
        ≤ (2 / (Real.pi ^ 2 * Real.exp 2)) * entry45Weight v :=
          entry45Perturb_abs_le_const_mul_weight hv
    _ < 1 * entry45Weight v :=
          mul_lt_mul_of_pos_right entry45_ratio_const_lt_one (entry45Weight_pos hv)
    _ = entry45Weight v := one_mul _

/-- Every Stieltjes moment integrand `v ↦ v^k * entry45Weight v` is integrable on `(0, ∞)`. -/
theorem entry45Weight_moment_integrable (k : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ k * entry45Weight v) (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext v
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hv
      by_cases h1 : v ≤ 1
      · exact Or.inl ⟨hv, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (⟨hv, _⟩ | h1)
      · exact hv
      · linarith
  rw [hsplit]
  have hcont : ContinuousOn (fun v : ℝ => v ^ k * entry45Weight v) (Set.Ioi 0) := by
    refine (continuous_pow k).continuousOn.mul ?_
    unfold entry45Weight
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)
    · exact Real.continuous_sinh.comp_continuousOn
        (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)))
    · intro x hx
      exact (sinh_pos_of_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx _))).ne'
  apply IntegrableOn.union
  · -- Near 0⁺ on `(0, 1]`, dominate by `π⁻¹ * v^(-3/4)`.
    have hdom : IntegrableOn (fun v : ℝ => Real.pi⁻¹ * v ^ (-(3 : ℝ) / 4)) (Set.Ioc 0 1) := by
      have hi : IntervalIntegrable (fun v : ℝ => v ^ (-(3 : ℝ) / 4)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
      exact hi.const_mul Real.pi⁻¹
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0 := fun _ hx => hx.1
    refine hdom.mono' ((hcont.mono hsub).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hv0 : 0 < v := hv.1
    have hv1 : v ≤ 1 := hv.2
    have hw_pos : 0 < entry45Weight v := entry45Weight_pos hv0
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hv0.le k) hw_pos.le)]
    have hvk : v ^ k ≤ 1 := pow_le_one₀ hv0.le hv1
    have hsinh : Real.pi * v ^ ((1 : ℝ) / 4) ≤ Real.sinh (Real.pi * v ^ ((1 : ℝ) / 4)) :=
      self_le_sinh_of_nonneg (mul_nonneg Real.pi_pos.le (Real.rpow_nonneg hv0.le _))
    have hdiv : entry45Weight v ≤ Real.pi⁻¹ * v ^ (-(3 : ℝ) / 4) := by
      unfold entry45Weight
      have hle : v ^ (-(1 : ℝ) / 2) / Real.sinh (Real.pi * v ^ ((1 : ℝ) / 4)) ≤
          v ^ (-(1 : ℝ) / 2) / (Real.pi * v ^ ((1 : ℝ) / 4)) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hv0.le _)
          (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hv0 _)) hsinh
      calc
        v ^ (-(1 : ℝ) / 2) / Real.sinh (Real.pi * v ^ ((1 : ℝ) / 4))
            ≤ v ^ (-(1 : ℝ) / 2) / (Real.pi * v ^ ((1 : ℝ) / 4)) := hle
        _ = Real.pi⁻¹ * (v ^ (-(1 : ℝ) / 2) * v ^ (-((1 : ℝ) / 4))) := by
            rw [Real.rpow_neg hv0.le]
            ring
        _ = Real.pi⁻¹ * v ^ (-(3 : ℝ) / 4) := by
            rw [← Real.rpow_add hv0]
            congr 2
            norm_num
    calc
      v ^ k * entry45Weight v ≤ 1 * entry45Weight v :=
        mul_le_mul_of_nonneg_right hvk hw_pos.le
      _ = entry45Weight v := one_mul _
      _ ≤ Real.pi⁻¹ * v ^ (-(3 : ℝ) / 4) := hdiv
  · -- Near +∞ on `(1, ∞)`, dominate by `C * v^(-2)` using Taylor term `(4k+8)` of `exp`.
    set N : ℕ := 4 * k + 8
    set C : ℝ := 4 * (N.factorial : ℝ) / Real.pi ^ N
    have hdom : IntegrableOn (fun v : ℝ => C * v ^ (-(2 : ℝ))) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : ℝ)) < -1) zero_lt_one).const_mul C
    have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := fun _ hx => lt_trans zero_lt_one hx
    refine hdom.mono' ((hcont.mono hsub).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv1 : 1 < v := hv
    have hv0 : 0 < v := lt_trans zero_lt_one hv1
    have hw_pos : 0 < entry45Weight v := entry45Weight_pos hv0
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hv0.le k) hw_pos.le)]
    set u : ℝ := v ^ ((1 : ℝ) / 4)
    have hu1 : 1 ≤ u := Real.one_le_rpow hv1.le (by norm_num)
    have hpiu1 : 1 ≤ Real.pi * u := by
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    have hsinh_ge : Real.exp (Real.pi * u) / 4 ≤ Real.sinh (Real.pi * u) :=
      quarter_exp_le_sinh hpiu1
    have hterm_le : (Real.pi * u) ^ N / (N.factorial : ℝ) ≤ Real.exp (Real.pi * u) := by
      have hsum := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ Real.pi * u) (N + 1)
      have hmem : N ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_self N)
      have hnonneg : ∀ i ∈ Finset.range (N + 1), 0 ≤ (Real.pi * u) ^ i / (i.factorial : ℝ) :=
        fun _ _ => by positivity
      exact le_trans (Finset.single_le_sum hnonneg hmem) hsum
    have huN : u ^ N = v ^ (k + 2) := by
      dsimp [u, N]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv0.le, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hvr1 : v ^ (-(1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hv1.le (by norm_num)
    have hsinh_low : Real.pi ^ N * v ^ (k + 2) / (4 * (N.factorial : ℝ)) ≤
        Real.sinh (Real.pi * u) := by
      have h1 : (Real.pi * u) ^ N / (4 * (N.factorial : ℝ)) ≤ Real.exp (Real.pi * u) / 4 := by
        have h := div_le_div_of_nonneg_right hterm_le (by norm_num : (0 : ℝ) ≤ 4)
        rw [div_div, mul_comm (N.factorial : ℝ) 4] at h
        exact h
      rw [mul_pow, huN] at h1
      exact le_trans h1 hsinh_ge
    have hlow_pos : 0 < Real.pi ^ N * v ^ (k + 2) / (4 * (N.factorial : ℝ)) := by positivity
    have hdiv : entry45Weight v ≤ C / v ^ (k + 2) := by
      unfold entry45Weight
      calc
        v ^ (-(1 : ℝ) / 2) / Real.sinh (Real.pi * u)
            ≤ 1 / Real.sinh (Real.pi * u) :=
              div_le_div_of_nonneg_right hvr1 (sinh_pos_of_pos (by positivity)).le
        _ ≤ 1 / (Real.pi ^ N * v ^ (k + 2) / (4 * (N.factorial : ℝ))) :=
              div_le_div_of_nonneg_left zero_le_one hlow_pos hsinh_low
        _ = C / v ^ (k + 2) := by
              dsimp [C]
              have hpi_ne : Real.pi ^ N ≠ 0 := (pow_pos Real.pi_pos N).ne'
              have hfac_ne : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
              have hvk_ne : v ^ (k + 2) ≠ 0 := (pow_pos hv0 (k + 2)).ne'
              field_simp
    calc
      v ^ k * entry45Weight v ≤ v ^ k * (C / v ^ (k + 2)) :=
        mul_le_mul_of_nonneg_left hdiv (pow_nonneg hv0.le k)
      _ = C * v ^ (-(2 : ℝ)) := by
        have hv_ne : v ≠ 0 := hv0.ne'
        rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hv0.le, Real.rpow_natCast]
        rw [pow_add]
        field_simp

/-- Every perturbation moment integrand `v ↦ v^k * entry45Perturb v` is integrable on `(0, ∞)`. -/
theorem entry45Perturb_moment_integrable (k : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ k * entry45Perturb v) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun v : ℝ => v ^ k * entry45Perturb v) (Set.Ioi 0) := by
    refine (continuous_pow k).continuousOn.mul ?_
    unfold entry45Perturb
    have hrpow : ContinuousOn (fun v : ℝ => v ^ ((1 : ℝ) / 4)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hrpow)).mul
      (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul hrpow))
  refine (entry45Weight_moment_integrable k).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hv) k)]
  exact mul_le_mul_of_nonneg_left (entry45Perturb_abs_lt_weight hv).le (pow_nonneg (le_of_lt hv) k)

/-- Every perturbed density `w_ε` has all Stieltjes moments integrable on `(0, ∞)`. -/
theorem entry45PerturbedWeight_moment_integrable (ε : ℝ) (k : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ k * entry45PerturbedWeight ε v) (Set.Ioi 0) := by
  have heq : (fun v : ℝ => v ^ k * entry45PerturbedWeight ε v) =
      fun v : ℝ => v ^ k * entry45Weight v + ε * (v ^ k * entry45Perturb v) := by
    funext v
    unfold entry45PerturbedWeight
    ring
  rw [heq]
  exact (entry45Weight_moment_integrable k).add ((entry45Perturb_moment_integrable k).const_mul ε)

/-- Algebraic key: `(1 - I)^4 = -4` is purely real. -/
theorem one_sub_I_pow_four : (1 - Complex.I) ^ 4 = (-4 : ℂ) := by
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Hence `entry45Alpha ^ (4 k + 4)` is purely real for every `k : ℕ`. -/
theorem entry45Alpha_pow_four_mul_im_zero (k : ℕ) :
    (entry45Alpha ^ (4 * k + 4)).im = 0 := by
  unfold entry45Alpha
  rw [mul_pow, show 4 * k + 4 = 4 * (k + 1) by ring, pow_mul (1 - Complex.I),
    one_sub_I_pow_four]
  have hreal : (((2 * Real.pi : ℝ) : ℂ) ^ (4 * (k + 1)) * (-4 : ℂ) ^ (k + 1)) =
      (((2 * Real.pi) ^ (4 * (k + 1)) * (-4 : ℝ) ^ (k + 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hreal, Complex.ofReal_im]

private lemma entry45Alpha_re : entry45Alpha.re = 2 * Real.pi := by
  unfold entry45Alpha
  simp

private lemma entry45Alpha_ne_zero : entry45Alpha ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [entry45Alpha_re, Complex.zero_re] at hre
  linarith [Real.pi_pos]

private lemma entry45ComplexIntegrand_integrable (k : ℕ) :
    IntegrableOn
      (fun v : ℝ =>
        ((v ^ k : ℝ) : ℂ) * Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ)))
      (Set.Ioi 0) := by
  have hcont_f : ContinuousOn
      (fun v : ℝ =>
        ((v ^ k : ℝ) : ℂ) * Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ)))
      (Set.Ioi 0) := by
    have hr : ContinuousOn (fun v : ℝ => ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx))
    exact (Complex.continuous_ofReal.comp_continuousOn (continuous_pow k).continuousOn).mul
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hr))
  refine (entry45Weight_moment_integrable k).mono'
    (hcont_f.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hre : (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ)).re =
      -2 * Real.pi * v ^ ((1 : ℝ) / 4) := by
    unfold entry45Alpha
    simp
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hv.le k),
    Complex.norm_exp, hre]
  have hexp_le : Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4)) ≤ entry45Weight v := by
    calc
      Real.exp (-2 * Real.pi * v ^ ((1 : ℝ) / 4))
          ≤ (2 / (Real.pi ^ 2 * Real.exp 2)) * entry45Weight v :=
            exp_neg_two_pi_le_const_mul_weight hv
      _ ≤ 1 * entry45Weight v :=
            mul_le_mul_of_nonneg_right entry45_ratio_const_lt_one.le (entry45Weight_pos hv).le
      _ = entry45Weight v := one_mul _
  exact mul_le_mul_of_nonneg_left hexp_le (pow_nonneg hv.le k)

private lemma hasDerivAt_entry45ComplexAntideriv (n : ℕ) {α : ℂ} (hα : α ≠ 0) (u : ℝ) :
    HasDerivAt (entry45ComplexAntideriv n α)
      ((u : ℂ) ^ n * Complex.exp (-α * (u : ℂ))) u := by
  set S : ℝ → ℂ := fun t =>
    ∑ j ∈ Finset.range (n + 1),
      ((n.factorial : ℂ) / (j.factorial : ℂ)) * ((t : ℂ) ^ j / α ^ (n + 1 - j))
  set S' : ℝ → ℂ := fun t =>
    ∑ j ∈ Finset.range n,
      ((n.factorial : ℂ) / (j.factorial : ℂ)) * ((t : ℂ) ^ j / α ^ (n - j))
  have hS : HasDerivAt S (S' u) u := by
    have hterm : ∀ j ∈ Finset.range (n + 1),
        HasDerivAt (fun t : ℝ =>
            ((n.factorial : ℂ) / (j.factorial : ℂ)) * ((t : ℂ) ^ j / α ^ (n + 1 - j)))
          (((n.factorial : ℂ) / (j.factorial : ℂ)) *
            (((j : ℂ) * (u : ℂ) ^ (j - 1)) / α ^ (n + 1 - j))) u := by
      intro j _
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ j) ((j : ℂ) * (u : ℂ) ^ (j - 1) * 1) u :=
        h1.pow j
      rw [mul_one] at h2
      exact (h2.div_const (α ^ (n + 1 - j))).const_mul _
    have hsum := HasDerivAt.fun_sum hterm
    convert hsum using 1
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_div, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < n := Finset.mem_range.mp hj
    have hsub : n + 1 - (j + 1) = n - j := Nat.succ_sub_succ_eq_sub n j
    rw [hsub, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hfj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hαp : α ^ (n - j) ≠ 0 := pow_ne_zero _ hα
    field_simp
  have hexp : HasDerivAt (fun t : ℝ => -Complex.exp (-α * (t : ℂ)))
      (α * Complex.exp (-α * (u : ℂ))) u := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => -α * (t : ℂ)) (-α * 1) u := h1.const_mul (-α)
    rw [mul_one] at h2
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (-α * (t : ℂ)))
        (Complex.exp (-α * (u : ℂ)) * (-α)) u := h2.cexp
    have h4 : HasDerivAt (fun t : ℝ => -Complex.exp (-α * (t : ℂ)))
        (-(Complex.exp (-α * (u : ℂ)) * (-α))) u := h3.fun_neg
    convert h4 using 1
    ring
  have hprod : HasDerivAt (fun t : ℝ => -Complex.exp (-α * (t : ℂ)) * S t)
      (α * Complex.exp (-α * (u : ℂ)) * S u + -Complex.exp (-α * (u : ℂ)) * S' u) u :=
    hexp.fun_mul hS
  have hcancel : α * S u - S' u = (u : ℂ) ^ n := by
    dsimp [S, S']
    rw [Finset.mul_sum, Finset.sum_range_succ]
    have hlast : α * (((n.factorial : ℂ) / (n.factorial : ℂ)) * ((u : ℂ) ^ n / α ^ (n + 1 - n))) =
        (u : ℂ) ^ n := by
      have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hsub : n + 1 - n = 1 := by omega
      rw [hsub, pow_one]
      field_simp
    have hfirst :
        ∑ j ∈ Finset.range n,
            α * (((n.factorial : ℂ) / (j.factorial : ℂ)) * ((u : ℂ) ^ j / α ^ (n + 1 - j))) =
          ∑ j ∈ Finset.range n,
            ((n.factorial : ℂ) / (j.factorial : ℂ)) * ((u : ℂ) ^ j / α ^ (n - j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_lt : j < n := Finset.mem_range.mp hj
      have hpow : α ^ (n + 1 - j) = α * α ^ (n - j) := by
        rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ']
      rw [hpow]
      have hαp : α ^ (n - j) ≠ 0 := pow_ne_zero _ hα
      field_simp
    rw [hfirst, hlast]
    ring
  have hfun_eq : entry45ComplexAntideriv n α = fun t : ℝ => -Complex.exp (-α * (t : ℂ)) * S t :=
    rfl
  rw [hfun_eq]
  convert hprod using 1
  calc
    (u : ℂ) ^ n * Complex.exp (-α * (u : ℂ))
        = (α * S u - S' u) * Complex.exp (-α * (u : ℂ)) := by rw [hcancel]
    _ = α * Complex.exp (-α * (u : ℂ)) * S u + -Complex.exp (-α * (u : ℂ)) * S' u := by ring

private lemma entry45ComplexAntideriv_zero (n : ℕ) (α : ℂ) :
    entry45ComplexAntideriv n α 0 = -((n.factorial : ℂ) / α ^ (n + 1)) := by
  unfold entry45ComplexAntideriv
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_mul, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp [div_eq_mul_inv]
  · intro j _ hj0
    simp [zero_pow hj0]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0

private lemma tendsto_sum_zero {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 0)) :
    Tendsto (fun u : ℝ => ∑ i ∈ s, f i u) atTop (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr fun u => ?_
    rw [Finset.sum_insert ha]

private lemma tendsto_entry45ComplexAntideriv_atTop (n : ℕ) {α : ℂ} (hα : 0 < α.re) :
    Tendsto (entry45ComplexAntideriv n α) atTop (𝓝 0) := by
  have hterm : ∀ j ∈ Finset.range (n + 1),
      Tendsto (fun u : ℝ =>
          -Complex.exp (-α * (u : ℂ)) *
            (((n.factorial : ℂ) / (j.factorial : ℂ)) * ((u : ℂ) ^ j / α ^ (n + 1 - j))))
        atTop (𝓝 0) := by
    intro j _
    rw [tendsto_zero_iff_norm_tendsto_zero]
    set c : ℝ := ‖((n.factorial : ℂ) / (j.factorial : ℂ)) / α ^ (n + 1 - j)‖
    have hnorm : ∀ᶠ u : ℝ in atTop,
        ‖-Complex.exp (-α * (u : ℂ)) *
          (((n.factorial : ℂ) / (j.factorial : ℂ)) * ((u : ℂ) ^ j / α ^ (n + 1 - j)))‖ =
          c * (u ^ j * Real.exp (-(α.re * u))) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      have hre : (-α * (u : ℂ)).re = -(α.re * u) := by simp
      calc
        ‖-Complex.exp (-α * (u : ℂ)) *
            (((n.factorial : ℂ) / (j.factorial : ℂ)) * ((u : ℂ) ^ j / α ^ (n + 1 - j)))‖
            = ‖Complex.exp (-α * (u : ℂ))‖ *
                ‖(((n.factorial : ℂ) / (j.factorial : ℂ)) / α ^ (n + 1 - j)) * (u : ℂ) ^ j‖ := by
                rw [norm_mul, norm_neg]
                congr 2
                ring
        _ = Real.exp (-(α.re * u)) * (c * ‖(u : ℂ) ^ j‖) := by
                rw [Complex.norm_exp, hre, norm_mul]
        _ = c * (u ^ j * Real.exp (-(α.re * u))) := by
                rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
                ring
    rw [tendsto_congr' hnorm]
    have h1 : Tendsto (fun u : ℝ => (α.re * u) ^ j * Real.exp (-(α.re * u))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
        (tendsto_id.const_mul_atTop hα)
    have h2 : Tendsto (fun u : ℝ => (c / α.re ^ j) * ((α.re * u) ^ j * Real.exp (-(α.re * u))))
        atTop (𝓝 ((c / α.re ^ j) * 0)) := h1.const_mul _
    rw [mul_zero] at h2
    refine h2.congr fun u => ?_
    have hαj : α.re ^ j ≠ 0 := (pow_pos hα j).ne'
    rw [mul_pow]
    field_simp
  have hsum := tendsto_sum_zero (Finset.range (n + 1)) hterm
  refine hsum.congr fun u => ?_
  unfold entry45ComplexAntideriv
  rw [Finset.mul_sum]

/-- Exact complex Entry 45 moment integral on `(0, ∞)`:
`∫_{v > 0} v^k exp(-2 π (1 - I) v^(1/4)) dv = 4 (4k + 3)! / (2 π (1 - I))^(4k + 4)`. -/
theorem entry45ComplexIntegral_eq (k : ℕ) :
    ∫ v in Set.Ioi (0 : ℝ),
        ((v ^ k : ℝ) : ℂ) * Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ)) =
      4 * ((4 * k + 3).factorial : ℂ) / entry45Alpha ^ (4 * k + 4) := by
  have hcont_rpow : ContinuousWithinAt (fun v : ℝ => v ^ ((1 : ℝ) / 4)) (Set.Ici 0) 0 := by
    have h := Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)
    exact h.continuousWithinAt
  have hcont_ant : Continuous (entry45ComplexAntideriv (4 * k + 3) entry45Alpha) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasDerivAt_entry45ComplexAntideriv (4 * k + 3) entry45Alpha_ne_zero u).continuousAt
  have hcont0 : ContinuousWithinAt (entry45MomentAntideriv k) (Set.Ici 0) 0 := by
    unfold entry45MomentAntideriv
    exact ((hcont_ant.continuousAt.comp_continuousWithinAt hcont_rpow).const_mul (4 : ℂ))
  have hderiv : ∀ v ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (entry45MomentAntideriv k)
        (((v ^ k : ℝ) : ℂ) * Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ))) v := by
    intro v hv
    have hv0 : 0 < v := hv
    have hrpow : HasDerivAt (fun x : ℝ => x ^ ((1 : ℝ) / 4))
        (((1 : ℝ) / 4) * v ^ (((1 : ℝ) / 4) - 1)) v :=
      Real.hasDerivAt_rpow_const (Or.inl hv0.ne')
    have hF := hasDerivAt_entry45ComplexAntideriv (4 * k + 3) entry45Alpha_ne_zero
      (v ^ ((1 : ℝ) / 4))
    have hcomp := (hF.scomp v hrpow).const_mul (4 : ℂ)
    have hfun : entry45MomentAntideriv k =
        fun y : ℝ => 4 * (entry45ComplexAntideriv (4 * k + 3) entry45Alpha ∘
          fun x : ℝ => x ^ ((1 : ℝ) / 4)) y := rfl
    rw [hfun]
    convert hcomp using 1
    have hpow_real : (v ^ ((1 : ℝ) / 4)) ^ (4 * k + 3) * v ^ (((1 : ℝ) / 4) - 1) = v ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv0.le, ← Real.rpow_add hv0, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hpow_c : ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ) ^ (4 * k + 3) *
        ((v ^ (((1 : ℝ) / 4) - 1) : ℝ) : ℂ) = ((v ^ k : ℝ) : ℂ) := by
      exact_mod_cast hpow_real
    rw [Complex.real_smul]
    calc
      ((v ^ k : ℝ) : ℂ) * Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ))
          = ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ) ^ (4 * k + 3) * ((v ^ (((1 : ℝ) / 4) - 1) : ℝ) : ℂ) *
              Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ)) := by rw [hpow_c]
      _ = 4 * ((((1 : ℝ) / 4 * v ^ ((1 : ℝ) / 4 - 1) : ℝ) : ℂ) *
            (((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ) ^ (4 * k + 3) *
              Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ)))) := by
            push_cast
            ring
  have htend : Tendsto (entry45MomentAntideriv k) atTop (𝓝 0) := by
    unfold entry45MomentAntideriv
    have hrpow_top : Tendsto (fun v : ℝ => v ^ ((1 : ℝ) / 4)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    have hF_top := (tendsto_entry45ComplexAntideriv_atTop (4 * k + 3)
      (by rw [entry45Alpha_re]; positivity)).comp hrpow_top
    simpa using hF_top.const_mul (4 : ℂ)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont0 hderiv
      (entry45ComplexIntegrand_integrable k) htend]
  unfold entry45MomentAntideriv
  rw [Real.zero_rpow (by norm_num : ((1 : ℝ) / 4) ≠ 0), entry45ComplexAntideriv_zero]
  ring

/-- **All moments of `entry45Perturb` vanish identically** for every `k : ℕ`:
`∫_{v > 0} v^k * exp(-2π v^(1/4)) * sin(2π v^(1/4)) dv = 0`. -/
theorem entry45Perturb_moment_zero (k : ℕ) :
    ∫ v in Set.Ioi (0 : ℝ), v ^ k * entry45Perturb v = 0 := by
  have him : ∀ v : ℝ,
      (((v ^ k : ℝ) : ℂ) *
        Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ))).im =
      v ^ k * entry45Perturb v := by
    intro v
    set u : ℝ := v ^ ((1 : ℝ) / 4)
    have hexp_eq : -entry45Alpha * (u : ℂ) =
        ((-2 * Real.pi * u : ℝ) : ℂ) + ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
      unfold entry45Alpha
      push_cast
      ring
    have hsplit : ((v ^ k : ℝ) : ℂ) * Complex.exp (-entry45Alpha * (u : ℂ)) =
        (((v ^ k * Real.exp (-2 * Real.pi * u) * Real.cos (2 * Real.pi * u) : ℝ) : ℂ)) +
          (((v ^ k * Real.exp (-2 * Real.pi * u) * Real.sin (2 * Real.pi * u) : ℝ) : ℂ)) *
            Complex.I := by
      rw [hexp_eq, Complex.exp_add, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp]
      push_cast
      ring
    rw [hsplit, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    unfold entry45Perturb
    ring
  have hint_c := entry45ComplexIntegrand_integrable k
  calc
    ∫ v in Set.Ioi (0 : ℝ), v ^ k * entry45Perturb v
        = ∫ v in Set.Ioi (0 : ℝ),
            (((v ^ k : ℝ) : ℂ) *
              Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ))).im := by
          congr 1; funext v; exact (him v).symm
    _ = (∫ v in Set.Ioi (0 : ℝ),
          ((v ^ k : ℝ) : ℂ) *
            Complex.exp (-entry45Alpha * ((v ^ ((1 : ℝ) / 4) : ℝ) : ℂ))).im := by
          exact Complex.imCLM.integral_comp_comm hint_c
    _ = (4 * ((4 * k + 3).factorial : ℂ) / entry45Alpha ^ (4 * k + 4)).im := by
          rw [entry45ComplexIntegral_eq k]
    _ = 0 := by
          have him0 := entry45Alpha_pow_four_mul_im_zero k
          have hreal_den : entry45Alpha ^ (4 * k + 4) =
              ((entry45Alpha ^ (4 * k + 4)).re : ℂ) := by
            apply Complex.ext
            · simp
            · simp [him0]
          rw [hreal_den]
          have hreal_all : (4 * ((4 * k + 3).factorial : ℂ) /
              ((entry45Alpha ^ (4 * k + 4)).re : ℂ)) =
              ((4 * ((4 * k + 3).factorial : ℝ) / (entry45Alpha ^ (4 * k + 4)).re : ℝ) : ℂ) := by
            push_cast
            rfl
          rw [hreal_all, Complex.ofReal_im]

/-- Every perturbed weight `w_ε` with `ε ∈ [-1, 1]` is strictly positive on `(0, ∞)`. -/
theorem entry45PerturbedWeight_pos {ε : ℝ} (hε : ε ∈ Set.Icc (-1 : ℝ) 1) {v : ℝ} (hv : 0 < v) :
    0 < entry45PerturbedWeight ε v := by
  unfold entry45PerturbedWeight
  have habs : |ε| ≤ 1 := abs_le.mpr hε
  have hlt : |entry45Perturb v| < entry45Weight v := entry45Perturb_abs_lt_weight hv
  have hprod : |ε * entry45Perturb v| < entry45Weight v := by
    rw [abs_mul]
    calc
      |ε| * |entry45Perturb v| ≤ 1 * |entry45Perturb v| :=
        mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = |entry45Perturb v| := one_mul _
      _ < entry45Weight v := hlt
  linarith [(abs_lt.mp hprod).1]

/-- Every `w_ε` has the exact same `k`-th Stieltjes moment as `entry45Weight`. -/
theorem entry45PerturbedWeight_moment_eq (ε : ℝ) (k : ℕ) :
    ∫ v in Set.Ioi (0 : ℝ), v ^ k * entry45PerturbedWeight ε v =
      ∫ v in Set.Ioi (0 : ℝ), v ^ k * entry45Weight v := by
  have heq : (fun v : ℝ => v ^ k * entry45PerturbedWeight ε v) =
      fun v : ℝ => v ^ k * entry45Weight v + ε * (v ^ k * entry45Perturb v) := by
    funext v; unfold entry45PerturbedWeight; ring
  rw [heq, integral_add (entry45Weight_moment_integrable k)
      ((entry45Perturb_moment_integrable k).const_mul ε),
    integral_const_mul, entry45Perturb_moment_zero k, mul_zero, add_zero]

/-- Distinct parameters `ε₁ ≠ ε₂` produce distinct weights on `(0, ∞)` (witnessed at `v = 1/256`). -/
theorem entry45PerturbedWeight_ne_of_ne {ε₁ ε₂ : ℝ} (hne : ε₁ ≠ ε₂) :
    ∃ v ∈ Set.Ioi (0 : ℝ), entry45PerturbedWeight ε₁ v ≠ entry45PerturbedWeight ε₂ v := by
  refine ⟨(1 : ℝ) / 256, by norm_num, ?_⟩
  unfold entry45PerturbedWeight entry45Perturb
  have hrpow : ((1 : ℝ) / 256) ^ ((1 : ℝ) / 4) = 1 / 4 := by
    have h1 : ((1 : ℝ) / 256) = ((1 : ℝ) / 4) ^ (4 : ℕ) := by norm_num
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
  rw [hrpow]
  have hsin : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  rw [hsin, mul_one]
  intro heq
  have hexp_ne : Real.exp (-2 * Real.pi * (1 / 4)) ≠ 0 := (Real.exp_pos _).ne'
  have hdiff : (ε₁ - ε₂) * Real.exp (-2 * Real.pi * (1 / 4)) = 0 := by linarith
  exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hexp_ne))

/-- Distinct parameters `ε₁ ≠ ε₂` in `[-1, 1]` induce distinct positive Borel measures on `(0, ∞)`
(strictly separated on the open subinterval `(0, 1/16)` where `sin(2π v^(1/4)) > 0`). -/
theorem entry45PerturbedWeight_measure_ne_of_ne
    {ε₁ ε₂ : ℝ} (h₁ : ε₁ ∈ Set.Icc (-1 : ℝ) 1) (h₂ : ε₂ ∈ Set.Icc (-1 : ℝ) 1)
    (hne : ε₁ ≠ ε₂) :
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun v => ENNReal.ofReal (entry45PerturbedWeight ε₁ v)) ≠
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun v => ENNReal.ofReal (entry45PerturbedWeight ε₂ v)) := by
  intro hmeas
  set S : Set ℝ := Set.Ioo (0 : ℝ) (1 / 16)
  have hS_meas : MeasurableSet S := measurableSet_Ioo
  have hS_sub : S ⊆ Set.Ioi (0 : ℝ) := fun _ hv => hv.1
  have h_eq_set := congrArg (fun μ : Measure ℝ => μ S) hmeas
  rw [withDensity_apply _ hS_meas, withDensity_apply _ hS_meas,
    Measure.restrict_restrict hS_meas, Set.inter_eq_left.mpr hS_sub] at h_eq_set
  have hint1 : IntegrableOn (entry45PerturbedWeight ε₁) S := by
    have h0 := (entry45PerturbedWeight_moment_integrable ε₁ 0).mono_set hS_sub
    simpa [pow_zero, one_mul] using h0
  have hint2 : IntegrableOn (entry45PerturbedWeight ε₂) S := by
    have h0 := (entry45PerturbedWeight_moment_integrable ε₂ 0).mono_set hS_sub
    simpa [pow_zero, one_mul] using h0
  have hnn1 : ∀ v ∈ S, 0 ≤ entry45PerturbedWeight ε₁ v :=
    fun v hv => (entry45PerturbedWeight_pos h₁ hv.1).le
  have hnn2 : ∀ v ∈ S, 0 ≤ entry45PerturbedWeight ε₂ v :=
    fun v hv => (entry45PerturbedWeight_pos h₂ hv.1).le
  have hint_eq : ∫ v in S, entry45PerturbedWeight ε₁ v = ∫ v in S, entry45PerturbedWeight ε₂ v := by
    rw [integral_eq_lintegral_of_nonneg_ae
          (by filter_upwards [ae_restrict_mem hS_meas] with v hv; exact hnn1 v hv)
          hint1.aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae
          (by filter_upwards [ae_restrict_mem hS_meas] with v hv; exact hnn2 v hv)
          hint2.aestronglyMeasurable]
    exact congrArg ENNReal.toReal h_eq_set
  have hpert_int : IntegrableOn entry45Perturb S := by
    have h0 := (entry45Perturb_moment_integrable 0).mono_set hS_sub
    simpa [pow_zero, one_mul] using h0
  have hdiff_zero : (ε₁ - ε₂) * ∫ v in S, entry45Perturb v = 0 := by
    have hsub : ∫ v in S, (entry45PerturbedWeight ε₁ v - entry45PerturbedWeight ε₂ v) = 0 := by
      rw [integral_sub hint1 hint2, hint_eq, sub_self]
    have hfun : (fun v => entry45PerturbedWeight ε₁ v - entry45PerturbedWeight ε₂ v) =
        fun v => (ε₁ - ε₂) * entry45Perturb v := by
      funext v; unfold entry45PerturbedWeight; ring
    rwa [hfun, integral_const_mul] at hsub
  have hpert_pos : ∀ v ∈ S, 0 < entry45Perturb v := by
    intro v hv
    unfold entry45Perturb
    apply mul_pos (Real.exp_pos _)
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos (by positivity) (Real.rpow_pos_of_pos hv.1 _)
    · have hu_lt : v ^ ((1 : ℝ) / 4) < 1 / 2 := by
        have h16 : ((1 : ℝ) / 16) ^ ((1 : ℝ) / 4) = 1 / 2 := by
          have h1 : ((1 : ℝ) / 16) = ((1 : ℝ) / 2) ^ (4 : ℕ) := by norm_num
          rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          norm_num
        rw [← h16]
        exact Real.rpow_lt_rpow hv.1.le hv.2 (by norm_num)
      nlinarith [Real.pi_pos]
  have hvol_pos : 0 < volume S := by
    rw [Real.volume_Ioo]
    norm_num
  have hint_pos : 0 < ∫ v in S, entry45Perturb v := by
    have hstrict := setIntegral_pos_iff_support_of_nonneg_ae
      (by filter_upwards [ae_restrict_mem hS_meas] with v hv; exact (hpert_pos v hv).le) hpert_int
    rw [hstrict]
    have hsub_supp : S ⊆ Function.support entry45Perturb ∩ S :=
      fun v hv => ⟨(hpert_pos v hv).ne', hv⟩
    exact lt_of_lt_of_le hvol_pos (measure_mono hsub_supp)
  exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hdiff_zero).resolve_right hint_pos.ne'))

/-- **Master Theorem — Settling Berndt's Open Remark on Ramanujan's `Notebooks V` Ch. 32 Entry 45:**
For every `ε ∈ [-1, 1]`, `w_ε(v) = entry45Weight v + ε * entry45Perturb v` is strictly positive
on `(0, ∞)`, distinct (both pointwise and as Borel measures) for distinct `ε₁ ≠ ε₂`, has finite
Stieltjes moments of all orders, and produces identical `k`-th Stieltjes moments for every `k : ℕ`.
Thus the Stieltjes moment problem for Entry 45 is unconditionally indeterminate (`indet(S)`). -/
theorem entry45_stieltjes_indeterminate :
    (∀ ε ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Ioi (0 : ℝ), 0 < entry45PerturbedWeight ε v) ∧
    (∀ ε₁ ∈ Set.Icc (-1 : ℝ) 1, ∀ ε₂ ∈ Set.Icc (-1 : ℝ) 1, ε₁ ≠ ε₂ →
      (∃ v ∈ Set.Ioi (0 : ℝ), entry45PerturbedWeight ε₁ v ≠ entry45PerturbedWeight ε₂ v) ∧
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun v => ENNReal.ofReal (entry45PerturbedWeight ε₁ v)) ≠
        (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun v => ENNReal.ofReal (entry45PerturbedWeight ε₂ v))) ∧
    (∀ ε₁ ∈ Set.Icc (-1 : ℝ) 1, ∀ ε₂ ∈ Set.Icc (-1 : ℝ) 1, ∀ k : ℕ,
      ∫ v in Set.Ioi (0 : ℝ), v ^ k * entry45PerturbedWeight ε₁ v =
        ∫ v in Set.Ioi (0 : ℝ), v ^ k * entry45PerturbedWeight ε₂ v) := by
  refine ⟨fun ε hε v hv => entry45PerturbedWeight_pos hε hv, ?_, ?_⟩
  · intro ε₁ h₁ ε₂ h₂ hne
    exact ⟨entry45PerturbedWeight_ne_of_ne hne,
      entry45PerturbedWeight_measure_ne_of_ne h₁ h₂ hne⟩
  · intro ε₁ _ ε₂ _ k
    rw [entry45PerturbedWeight_moment_eq ε₁ k, entry45PerturbedWeight_moment_eq ε₂ k]

end BerndtEntry45

/-! ### 2. Exact Gross CM Hecke Radius Separation (`> 1.7×`) -/

section GrossCMRadii

/-- Elementary Taylor lower bound `e^5 > 128` using the first nine Taylor terms of `exp 5`. -/
theorem exp_five_gt_128 : (128 : ℝ) < Real.exp 5 := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 9
  have hval : (128 : ℝ) < ∑ i ∈ Finset.range 9, (5 : ℝ) ^ i / (i.factorial : ℝ) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  exact lt_of_lt_of_le hval hsum

/-- Elementary lower bound `π √11 > 10`. -/
theorem pi_mul_sqrt_eleven_gt_ten : (10 : ℝ) < Real.pi * Real.sqrt 11 := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hsq : (3.316 : ℝ) < Real.sqrt 11 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  nlinarith

/-- Nome modulus `s_ℓ = exp(-π √ℓ)` at the Gross CM point `τ_ℓ = (1 + i √ℓ) / 2`. -/
def grossS (ℓ : ℝ) : ℝ :=
  Real.exp (-Real.pi * Real.sqrt ℓ)

/-- For every `ℓ ≥ 11`, `s_ℓ = exp(-π √ℓ) < 1 / 16384`. -/
theorem grossS_lt_inv_16384 {ℓ : ℝ} (hℓ : 11 ≤ ℓ) : grossS ℓ < 1 / 16384 := by
  unfold grossS
  have hsqrt : Real.sqrt 11 ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hℓ
  have h10 : (10 : ℝ) < Real.pi * Real.sqrt ℓ := by
    calc
      (10 : ℝ) < Real.pi * Real.sqrt 11 := pi_mul_sqrt_eleven_gt_ten
      _ ≤ Real.pi * Real.sqrt ℓ := mul_le_mul_of_nonneg_left hsqrt Real.pi_pos.le
  have hexp10 : (16384 : ℝ) < Real.exp 10 := by
    have h5 := exp_five_gt_128
    have heq : Real.exp 10 = Real.exp 5 * Real.exp 5 := by
      rw [← Real.exp_add]; norm_num
    rw [heq]
    nlinarith
  have hlt : Real.exp (-Real.pi * Real.sqrt ℓ) < Real.exp (-10) := by
    apply Real.exp_lt_exp.mpr
    linarith
  calc
    Real.exp (-Real.pi * Real.sqrt ℓ) < Real.exp (-10) := hlt
    _ = (Real.exp 10)⁻¹ := Real.exp_neg 10
    _ < (16384 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) hexp10
    _ = 1 / 16384 := by norm_num

/-- Elementary comparison `(n + 1)^3 ≤ 8^n` for all `n : ℕ`. -/
theorem nat_cube_le_eight_pow (n : ℕ) : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 8 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h1 : ((k + 2 : ℕ) : ℝ) ^ 3 ≤ 8 * ((k + 1 : ℕ) : ℝ) ^ 3 := by
      push_cast
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
      have hk3 : (0 : ℝ) ≤ (k : ℝ) ^ 3 := pow_nonneg hk 3
      nlinarith
    calc
      ((k + 2 : ℕ) : ℝ) ^ 3 ≤ 8 * ((k + 1 : ℕ) : ℝ) ^ 3 := h1
      _ ≤ 8 * 8 ^ k := by linarith
      _ = 8 ^ (k + 1) := by ring

/-- Weight-4 Eisenstein series Lambert expansion `E_4(q) = 1 + 240 ∑_{n ≥ 1} n^3 q^n / (1 - q^n)`. -/
def eisensteinE4 (q : ℂ) : ℂ :=
  1 + 240 * ∑' n : ℕ, ((n + 1 : ℂ) ^ 3) * q ^ (n + 1) / (1 - q ^ (n + 1))

private lemma norm_eisensteinE4_term_le {q : ℂ} {s : ℝ} (hs : ‖q‖ ≤ s) (hs1 : s < 1) (n : ℕ) :
    ‖((n + 1 : ℂ) ^ 3) * q ^ (n + 1) / (1 - q ^ (n + 1))‖ ≤
      (s / (1 - s)) * (8 * s) ^ n := by
  have hqn : ‖q ^ (n + 1)‖ ≤ s ^ (n + 1) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg q) hs (n + 1)
  have hs_nn : 0 ≤ s := le_trans (norm_nonneg q) hs
  have hsn : s ^ (n + 1) ≤ s := by
    calc
      s ^ (n + 1) = s * s ^ n := pow_succ' s n
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hs_nn hs1.le) hs_nn
      _ = s := mul_one s
  have hden_ge : 1 - s ≤ ‖1 - q ^ (n + 1)‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) (q ^ (n + 1))
    rw [norm_one] at hrev
    linarith
  have h1ms : 0 < 1 - s := sub_pos.mpr hs1
  have hcube : ‖((n + 1 : ℂ) ^ 3)‖ ≤ 8 ^ n := by
    have hnat : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; rfl
    rw [norm_pow, ← hnat, Complex.norm_natCast]
    exact nat_cube_le_eight_pow n
  rw [norm_div, norm_mul]
  calc
    ‖(n + 1 : ℂ) ^ 3‖ * ‖q ^ (n + 1)‖ / ‖1 - q ^ (n + 1)‖
        ≤ (8 ^ n * s ^ (n + 1)) / (1 - s) := by
          apply div_le_div₀ (by positivity)
          · exact mul_le_mul hcube hqn (norm_nonneg _) (by positivity)
          · exact h1ms
          · exact hden_ge
    _ = (s / (1 - s)) * (8 * s) ^ n := by
          rw [mul_pow, pow_succ']
          ring

/-- Absolute summability of the `E_4` Lambert series for `‖q‖ < 1/8`. -/
theorem summable_eisensteinE4_terms {q : ℂ} (hq : ‖q‖ < 1 / 8) :
    Summable (fun n : ℕ => ((n + 1 : ℂ) ^ 3) * q ^ (n + 1) / (1 - q ^ (n + 1))) := by
  have h8 : 8 * ‖q‖ < 1 := by linarith
  have hgeom : Summable (fun n : ℕ => (‖q‖ / (1 - ‖q‖)) * (8 * ‖q‖) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) h8).mul_left _
  exact Summable.of_norm_bounded hgeom fun n =>
    norm_eisensteinE4_term_le le_rfl (by linarith) n

/-- Exact Lambert-series bound `‖E_4(q) - 1‖ ≤ 240 s / ((1 - s)(1 - 8 s))` for `‖q‖ ≤ s < 1/8`. -/
theorem eisensteinE4_sub_one_norm_le {q : ℂ} {s : ℝ} (hs : ‖q‖ ≤ s) (hs8 : s < 1 / 8) :
    ‖eisensteinE4 q - 1‖ ≤ 240 * s / ((1 - s) * (1 - 8 * s)) := by
  have hs_nn : 0 ≤ s := le_trans (norm_nonneg q) hs
  have hs1 : s < 1 := by linarith
  have h8s : 8 * s < 1 := by linarith
  have hq8 : ‖q‖ < 1 / 8 := lt_of_le_of_lt hs hs8
  have hgeom : Summable (fun n : ℕ => (s / (1 - s)) * (8 * s) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) h8s).mul_left _
  have htsum_bound :
      ‖∑' n : ℕ, ((n + 1 : ℂ) ^ 3) * q ^ (n + 1) / (1 - q ^ (n + 1))‖ ≤
        ∑' n : ℕ, (s / (1 - s)) * (8 * s) ^ n := by
    calc
      ‖∑' n : ℕ, ((n + 1 : ℂ) ^ 3) * q ^ (n + 1) / (1 - q ^ (n + 1))‖
          ≤ ∑' n : ℕ, ‖((n + 1 : ℂ) ^ 3) * q ^ (n + 1) / (1 - q ^ (n + 1))‖ :=
            norm_tsum_le_tsum_norm (summable_eisensteinE4_terms hq8).norm
      _ ≤ ∑' n : ℕ, (s / (1 - s)) * (8 * s) ^ n :=
            Summable.tsum_le_tsum (fun n => norm_eisensteinE4_term_le hs hs1 n)
              (summable_eisensteinE4_terms hq8).norm hgeom
  have hgeom_val :
      (∑' n : ℕ, (s / (1 - s)) * (8 * s) ^ n) = s / ((1 - s) * (1 - 8 * s)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) h8s]
    have h1ms : 1 - s ≠ 0 := by linarith
    have h1m8s : 1 - 8 * s ≠ 0 := by linarith
    field_simp
  unfold eisensteinE4
  rw [add_sub_cancel_left, norm_mul]
  have h240 : ‖(240 : ℂ)‖ = 240 := by norm_num
  rw [h240]
  calc
    240 * ‖∑' n : ℕ, ((n + 1 : ℂ) ^ 3) * q ^ (n + 1) / (1 - q ^ (n + 1))‖
        ≤ 240 * (s / ((1 - s) * (1 - 8 * s))) := by
          rw [← hgeom_val]
          exact mul_le_mul_of_nonneg_left htsum_bound (by norm_num)
    _ = 240 * s / ((1 - s) * (1 - 8 * s)) := by ring

/-- For `‖q‖ < 1 / 16384`, `‖E_4(q) - 1‖ < 1 / 64`. -/
theorem eisensteinE4_sub_one_norm_lt_inv_64 {q : ℂ} (hq : ‖q‖ < 1 / 16384) :
    ‖eisensteinE4 q - 1‖ < 1 / 64 := by
  have hbound := eisensteinE4_sub_one_norm_le le_rfl (by linarith : ‖q‖ < 1 / 8)
  set s : ℝ := ‖q‖
  have hs_nn : 0 ≤ s := norm_nonneg q
  have h1 : 0 < (1 - s) * (1 - 8 * s) := by nlinarith
  have hstrict : 240 * s / ((1 - s) * (1 - 8 * s)) < 1 / 64 := by
    rw [div_lt_iff₀ h1]
    nlinarith
  exact lt_of_le_of_lt hbound hstrict

/-- Consequently `63 / 64 < ‖E_4(q)‖ < 65 / 64` whenever `‖q‖ < 1 / 16384`. -/
theorem eisensteinE4_norm_bounds {q : ℂ} (hq : ‖q‖ < 1 / 16384) :
    63 / 64 < ‖eisensteinE4 q‖ ∧ ‖eisensteinE4 q‖ < 65 / 64 := by
  have h := eisensteinE4_sub_one_norm_lt_inv_64 hq
  constructor
  · have hrev := norm_sub_norm_le (1 : ℂ) (eisensteinE4 q)
    rw [norm_one, norm_sub_rev] at hrev
    linarith
  · have htri : ‖eisensteinE4 q‖ ≤ ‖eisensteinE4 q - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_add_le (eisensteinE4 q - 1) 1
    rw [norm_one] at htri
    linarith

/-- The five Gross CM discriminants `ℓ ∈ {163, 67, 43, 19, 11}` ordered by increasing Borel radius. -/
def grossEll : Fin 5 → ℕ := ![163, 67, 43, 19, 11]

/-- Rodriguez Villegas's exact rational invariants `g_{2, ℓ}` for the five Gross CM curves. -/
def grossG2 : Fin 5 → ℚ := ![8697680, 29480, 3440, 152, 88 / 3]

/-- Upper-half-plane CM point `τ_ℓ = (1 + i √ℓ) / 2`. -/
def grossTau (i : Fin 5) : ℂ :=
  (1 + Complex.I * Real.sqrt (grossEll i)) / 2

/-- Modular nome `q_ℓ = exp(2 π i τ_ℓ)` at the `i`-th Gross CM curve. -/
def grossQ (i : Fin 5) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * grossTau i)

/-- Exact nome modulus `‖q_ℓ‖ = exp(-π √ℓ) = grossS ℓ`. -/
theorem norm_grossQ (i : Fin 5) : ‖grossQ i‖ = grossS (grossEll i) := by
  unfold grossQ grossTau grossS
  rw [Complex.norm_exp]
  congr 1
  have hsimp : 2 * (Real.pi : ℂ) * Complex.I *
      ((1 + Complex.I * ((Real.sqrt (grossEll i) : ℝ) : ℂ)) / 2) =
      ((-Real.pi * Real.sqrt (grossEll i) : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hsimp]
  simp

/-- Every Gross CM nome satisfies `‖q_ℓ‖ < 1 / 16384`. -/
theorem norm_grossQ_lt_inv_16384 (i : Fin 5) : ‖grossQ i‖ < 1 / 16384 := by
  rw [norm_grossQ]
  apply grossS_lt_inv_16384
  fin_cases i <;> simp [grossEll] <;> norm_num

/-- Exact rational lower endpoints for `ρ_ℓ^2 / π^2` from Codex's table. -/
def grossLower : Fin 5 → ℚ :=
  ![21 / 3415040, 21 / 28160, 21 / 5120, 21 / 512, 63 / 512]

/-- Exact rational upper endpoints for `ρ_ℓ^2 / π^2` from Codex's table. -/
def grossUpper : Fin 5 → ℚ :=
  ![13 / 2049024, 13 / 16896, 13 / 3072, 65 / 1536, 65 / 512]

/-- Normalized squared Hecke Borel radius `ρ_ℓ^2 / π^2 = ℓ |E_4(τ_ℓ)| / (3 g_{2, ℓ})`. -/
def grossRadiusSqDivPiSq (i : Fin 5) : ℝ :=
  (grossEll i : ℝ) * ‖eisensteinE4 (grossQ i)‖ / (3 * (grossG2 i : ℝ))

/-- Exact Gross CM Hecke Borel radius `ρ_ℓ = π √(ℓ |E_4(τ_ℓ)| / (3 g_{2, ℓ}))`. -/
def grossRadius (i : Fin 5) : ℝ :=
  Real.pi * Real.sqrt (grossRadiusSqDivPiSq i)

/-- Every `ρ_ℓ^2 / π^2` lies strictly inside Codex's exact rational interval `(lower_i, upper_i)`. -/
theorem grossRadiusSqDivPiSq_mem_Ioo (i : Fin 5) :
    (grossLower i : ℝ) < grossRadiusSqDivPiSq i ∧
      grossRadiusSqDivPiSq i < (grossUpper i : ℝ) := by
  unfold grossRadiusSqDivPiSq
  fin_cases i
  · have hE := eisensteinE4_norm_bounds (norm_grossQ_lt_inv_16384 0)
    simp only [grossLower, grossUpper, grossEll, grossG2]
    push_cast
    constructor <;> linarith
  · have hE := eisensteinE4_norm_bounds (norm_grossQ_lt_inv_16384 1)
    simp only [grossLower, grossUpper, grossEll, grossG2]
    push_cast
    constructor <;> linarith
  · have hE := eisensteinE4_norm_bounds (norm_grossQ_lt_inv_16384 2)
    simp only [grossLower, grossUpper, grossEll, grossG2]
    push_cast
    constructor <;> linarith
  · have hE := eisensteinE4_norm_bounds (norm_grossQ_lt_inv_16384 3)
    simp only [grossLower, grossUpper, grossEll, grossG2]
    push_cast
    constructor <;> linarith
  · have hE := eisensteinE4_norm_bounds (norm_grossQ_lt_inv_16384 4)
    simp only [grossLower, grossUpper, grossEll, grossG2]
    push_cast
    constructor <;> linarith

/-- Every Gross CM Hecke Borel radius is strictly positive. -/
theorem grossRadius_pos (i : Fin 5) : 0 < grossRadius i := by
  unfold grossRadius
  apply mul_pos Real.pi_pos
  apply Real.sqrt_pos.mpr
  have hlow := (grossRadiusSqDivPiSq_mem_Ioo i).1
  have hpos : (0 : ℝ) < (grossLower i : ℝ) := by
    fin_cases i <;> simp [grossLower]
  exact lt_trans hpos hlow

/-- Every consecutive lower/upper endpoint ratio is at least `189 / 65` (attained at `19 → 11`). -/
theorem grossLower_div_grossUpper_ge (i : Fin 4) :
    (189 : ℚ) / 65 ≤ grossLower i.succ / grossUpper i.castSucc := by
  fin_cases i <;>
    simp [grossLower, grossUpper, Fin.succ, Fin.castSucc] <;>
    norm_num

/-- All four consecutive Gross CM Hecke radius ratios strictly exceed `17 / 10 = 1.7`. -/
theorem grossRadius_consecutive_ratio_gt (i : Fin 4) :
    (17 : ℝ) / 10 < grossRadius i.succ / grossRadius i.castSucc := by
  have hpos0 : 0 < grossRadius i.castSucc := grossRadius_pos i.castSucc
  rw [lt_div_iff₀ hpos0]
  have hratio_q : (189 : ℚ) / 65 ≤ grossLower i.succ / grossUpper i.castSucc :=
    grossLower_div_grossUpper_ge i
  have hratio_r : (189 : ℝ) / 65 ≤ (grossLower i.succ : ℝ) / (grossUpper i.castSucc : ℝ) := by
    have hcast : (((189 : ℚ) / 65 : ℚ) : ℝ) ≤
        ((grossLower i.succ / grossUpper i.castSucc : ℚ) : ℝ) := by
      exact_mod_cast hratio_q
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcast
  have h17sq : ((17 : ℝ) / 10) ^ 2 < (189 : ℝ) / 65 := by norm_num
  have hup_pos : (0 : ℝ) < (grossUpper i.castSucc : ℝ) := by
    fin_cases i <;> simp [grossUpper, Fin.castSucc]
  have hsq0 := (grossRadiusSqDivPiSq_mem_Ioo i.castSucc).2
  have hsq1 := (grossRadiusSqDivPiSq_mem_Ioo i.succ).1
  have hsq_nn0 : 0 ≤ grossRadiusSqDivPiSq i.castSucc :=
    le_of_lt (lt_trans (by fin_cases i <;> simp [grossLower, Fin.castSucc])
      (grossRadiusSqDivPiSq_mem_Ioo i.castSucc).1)
  have hsq_nn1 : 0 ≤ grossRadiusSqDivPiSq i.succ :=
    le_of_lt (lt_trans (by fin_cases i <;> simp [grossLower, Fin.succ]) hsq1)
  have hsq_ineq : ((17 : ℝ) / 10) ^ 2 * grossRadiusSqDivPiSq i.castSucc <
      grossRadiusSqDivPiSq i.succ := by
    have hmul : ((17 : ℝ) / 10) ^ 2 * (grossUpper i.castSucc : ℝ) < (grossLower i.succ : ℝ) := by
      have h1 : ((17 : ℝ) / 10) ^ 2 < (grossLower i.succ : ℝ) / (grossUpper i.castSucc : ℝ) :=
        lt_of_lt_of_le h17sq hratio_r
      rwa [lt_div_iff₀ hup_pos] at h1
    calc
      ((17 : ℝ) / 10) ^ 2 * grossRadiusSqDivPiSq i.castSucc
          < ((17 : ℝ) / 10) ^ 2 * (grossUpper i.castSucc : ℝ) :=
            mul_lt_mul_of_pos_left hsq0 (by norm_num)
      _ < (grossLower i.succ : ℝ) := hmul
      _ < grossRadiusSqDivPiSq i.succ := hsq1
  unfold grossRadius
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hlhs_nn : 0 ≤ (17 : ℝ) / 10 * (Real.pi * Real.sqrt (grossRadiusSqDivPiSq i.castSucc)) := by
    positivity
  have hrhs_nn : 0 ≤ Real.pi * Real.sqrt (grossRadiusSqDivPiSq i.succ) := by positivity
  rw [← sq_lt_sq₀ hlhs_nn hrhs_nn]
  calc
    ((17 : ℝ) / 10 * (Real.pi * Real.sqrt (grossRadiusSqDivPiSq i.castSucc))) ^ 2
        = Real.pi ^ 2 * (((17 : ℝ) / 10) ^ 2 * grossRadiusSqDivPiSq i.castSucc) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hsq_nn0]; ring
    _ < Real.pi ^ 2 * grossRadiusSqDivPiSq i.succ :=
          mul_lt_mul_of_pos_left hsq_ineq (sq_pos_of_pos hpi_pos)
    _ = (Real.pi * Real.sqrt (grossRadiusSqDivPiSq i.succ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hsq_nn1]

/-- Strict ordering of the five Gross CM Hecke Borel radii:
`ρ_{163} < ρ_{67} < ρ_{43} < ρ_{19} < ρ_{11}`. -/
theorem grossRadius_strictMono : StrictMono grossRadius := by
  refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
  have hratio := grossRadius_consecutive_ratio_gt i
  have hpos := grossRadius_pos i.castSucc
  rw [lt_div_iff₀ hpos] at hratio
  linarith

/-- Explicit four-step strict inequality chain `ρ_{163} < ρ_{67} < ρ_{43} < ρ_{19} < ρ_{11}`. -/
theorem grossRadius_chain :
    grossRadius 0 < grossRadius 1 ∧
    grossRadius 1 < grossRadius 2 ∧
    grossRadius 2 < grossRadius 3 ∧
    grossRadius 3 < grossRadius 4 :=
  ⟨grossRadius_strictMono (by decide : (0 : Fin 5) < 1),
   grossRadius_strictMono (by decide : (1 : Fin 5) < 2),
   grossRadius_strictMono (by decide : (2 : Fin 5) < 3),
   grossRadius_strictMono (by decide : (3 : Fin 5) < 4)⟩

end GrossCMRadii

/-! ### 3. Abstract Multivariate Natural-Boundary Radius Peeling Engine -/

section MultivariateRadiusPeeling

private lemma finsupp_finset_sum_apply {ι α M : Type*} [AddCommMonoid M]
    (s : Finset ι) (g : ι → α →₀ M) (a : α) :
    (∑ i ∈ s, g i) a = ∑ i ∈ s, g i a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, Finsupp.add_apply, ih]

/-- `DecidableEq`-independent variable-occurrence predicate: `v` appears in `Q` iff some
monomial with nonzero coefficient in `Q` has positive exponent at `v`. -/
def InVars {K σ : Type*} [CommSemiring K] (v : σ) (Q : MvPolynomial σ K) : Prop :=
  ∃ m : σ →₀ ℕ, Q.coeff m ≠ 0 ∧ m v ≠ 0

/-- Equivalence between `InVars v Q` and `v ∈ Q.vars` (for any `DecidableEq`). -/
theorem inVars_iff_mem_vars {K σ : Type*} [CommSemiring K] {v : σ} {Q : MvPolynomial σ K} :
    InVars v Q ↔ v ∈ Q.vars := by
  rw [MvPolynomial.mem_vars_iff_mem_support]
  unfold InVars
  simp only [MvPolynomial.mem_support_iff, Finsupp.mem_support_iff]

/-- Equivalence between `InVars v Q` and `0 < Q.degreeOf v`. -/
theorem inVars_iff_degreeOf_pos {K σ : Type*} [CommSemiring K] {v : σ} {Q : MvPolynomial σ K} :
    InVars v Q ↔ 0 < Q.degreeOf v := by
  rw [inVars_iff_mem_vars, MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  omega

/-- Over a characteristic-zero field, if `v` appears with positive degree in `Q`,
then the partial derivative `∂Q/∂v` is nonzero. -/
theorem mvPoly_pderiv_ne_zero_of_degreeOf_pos
    {K σ : Type*} [Field K] [CharZero K] {Q : MvPolynomial σ K} {v : σ}
    (hdeg : 0 < Q.degreeOf v) :
    MvPolynomial.pderiv v Q ≠ 0 := by
  have hmem : ∃ m ∈ Q.support, m v = Q.degreeOf v := by
    rw [MvPolynomial.degreeOf_eq_sup] at hdeg ⊢
    have hne : Q.support.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hdeg
      simp at hdeg
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup Q.support hne (fun m : σ →₀ ℕ => m v)
    exact ⟨m, hm, hmax.symm⟩
  obtain ⟨m, hm, hmv⟩ := hmem
  set m' : σ →₀ ℕ := m - Finsupp.single v 1
  have hm_eq : m' + Finsupp.single v 1 = m := by
    ext w
    by_cases hw : w = v
    · subst hw
      simp only [m', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp only [m', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h'
      · exact absurd h'.symm hw
      · omega
  intro hzero
  have hcoeff := congrArg (fun P : MvPolynomial σ K => P.coeff m') hzero
  have h0 : (0 : MvPolynomial σ K).coeff m' = 0 := rfl
  rw [h0, MvPolynomial.coeff_pderiv, hm_eq] at hcoeff
  have hQm : Q.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hfac : ((m' v : K) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (m' v)
  exact (mul_ne_zero hQm hfac) hcoeff

/-- Taking a partial derivative never introduces new variables (`InVars`). -/
theorem mvPoly_pderiv_inVars {K σ : Type*} [CommSemiring K]
    {v w : σ} {Q : MvPolynomial σ K} (hw : InVars w (MvPolynomial.pderiv v Q)) :
    InVars w Q := by
  obtain ⟨m, hm, hmw⟩ := hw
  rw [MvPolynomial.coeff_pderiv] at hm
  refine ⟨m + Finsupp.single v 1, left_ne_zero_of_mul hm, ?_⟩
  simp only [Finsupp.add_apply]
  omega

/-- Taking `pderiv v` strictly drops `degreeOf v` whenever `0 < Q.degreeOf v`. -/
theorem mvPoly_pderiv_degreeOf_lt {K σ : Type*} [CommSemiring K]
    {Q : MvPolynomial σ K} {v : σ} (hdeg : 0 < Q.degreeOf v) :
    (MvPolynomial.pderiv v Q).degreeOf v < Q.degreeOf v := by
  rw [MvPolynomial.degreeOf_eq_sup]
  refine (Finset.sup_lt_iff hdeg).mpr fun (m : σ →₀ ℕ) hm => ?_
  have hsupp : (m + Finsupp.single v 1 : σ →₀ ℕ) ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    rw [MvPolynomial.coeff_pderiv] at hm
    exact left_ne_zero_of_mul hm
  have hle : (m + Finsupp.single v 1 : σ →₀ ℕ) v ≤ Q.degreeOf v := by
    rw [MvPolynomial.degreeOf_eq_sup]
    exact Finset.le_sup (f := fun d : σ →₀ ℕ => d v) hsupp
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hle
  omega

/-- Variable-support predicate: every series variable in `Q` from `Fin m` has index `j ≥ k`. -/
def SupportedFrom {K : Type*} [CommSemiring K] (m : ℕ) (ι_E : Type*) (k : Fin m)
    (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) : Prop :=
  ∀ v, InVars v Q → match v.1 with
    | Sum.inl j => k ≤ j
    | Sum.inr _ => True

/-- Variable-support predicate: every series variable in `Q` from `Fin m` has index `j > k`. -/
def SupportedAbove {K : Type*} [CommSemiring K] (m : ℕ) (ι_E : Type*) (k : Fin m)
    (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) : Prop :=
  ∀ v, InVars v Q → match v.1 with
    | Sum.inl j => k < j
    | Sum.inr _ => True

/-- Natural-number tail support predicate: every series variable from `Fin m` has `n ≤ j.val`. -/
def SupportedFromNat {K : Type*} [CommSemiring K] (m : ℕ) (ι_E : Type*) (n : ℕ)
    (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) : Prop :=
  ∀ v, InVars v Q → match v.1 with
    | Sum.inl j => n ≤ j.val
    | Sum.inr _ => True

/-- Jet-order bound at index `k`: every `(Sum.inl k, ν)` appearing in `Q` satisfies `ν ≤ ord`. -/
def OrderLeAt {K : Type*} [CommSemiring K] (m : ℕ) (ι_E : Type*) (k : Fin m) (ord : ℕ)
    (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) : Prop :=
  ∀ ν : ℕ, InVars (Sum.inl k, ν) Q → ν ≤ ord

/-- **Minimal-Order / Minimal-Top-Jet-Degree Separant Nonvanishing Lemma:**
Assume every nonzero relation supported strictly above `k` evaluates nonzero at `(f, E)`.
Then from ANY nonzero relation supported from `k` upward that vanishes on `(f, E)`, there exists
a minimal-order, minimal-top-jet-degree relation `Q` of some order `ord` in `f_k` such that:
- `Q ≠ 0`, `SupportedFrom m ι_E k Q`, `aeval (f, E) Q = 0`;
- `OrderLeAt m ι_E k ord Q` and `0 < Q.degreeOf (Sum.inl k, ord)`;
- the separant `∂Q / ∂Y_{k, ord}` is nonzero AND evaluates nonzero at `(f, E)`! -/
theorem exists_minimal_relation_nonzero_separant
    {K A ι_E : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    {m : ℕ} (f : Fin m → ℕ → A) (E : ι_E → ℕ → A) (k : Fin m)
    (habove : ∀ P : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
      P ≠ 0 → SupportedAbove m ι_E k P →
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E)) P ≠ 0)
    (hex : ∃ Q₀ : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
      Q₀ ≠ 0 ∧ SupportedFrom m ι_E k Q₀ ∧
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E)) Q₀ = 0) :
    ∃ (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) (ord : ℕ),
      Q ≠ 0 ∧
      SupportedFrom m ι_E k Q ∧
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E)) Q = 0 ∧
      OrderLeAt m ι_E k ord Q ∧
      0 < Q.degreeOf (Sum.inl k, ord) ∧
      MvPolynomial.pderiv (Sum.inl k, ord) Q ≠ 0 ∧
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E))
        (MvPolynomial.pderiv (Sum.inl k, ord) Q) ≠ 0 := by
  let eval := MvPolynomial.aeval (R := K) (Function.uncurry (Sum.elim f E))
  -- Step 1: Every valid relation supported from `k` upward has some upper bound `ord` on its `k`-jets.
  have hex_ord : ∃ ord : ℕ, ∃ Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
      Q ≠ 0 ∧ SupportedFrom m ι_E k Q ∧ eval Q = 0 ∧ OrderLeAt m ι_E k ord Q := by
    obtain ⟨Q₀, hne, hsupp, hev⟩ := hex
    refine ⟨Q₀.vars.sup Prod.snd, Q₀, hne, hsupp, hev, fun ν hν => ?_⟩
    exact Finset.le_sup (f := Prod.snd) (inVars_iff_mem_vars.mp hν)
  -- Choose the minimal possible order `ord₀`.
  set ord₀ : ℕ := Nat.find hex_ord
  have hord₀_spec : ∃ Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
      Q ≠ 0 ∧ SupportedFrom m ι_E k Q ∧ eval Q = 0 ∧ OrderLeAt m ι_E k ord₀ Q :=
    Nat.find_spec hex_ord
  have hord₀_min : ∀ ord < ord₀, ∀ Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
      Q ≠ 0 → SupportedFrom m ι_E k Q → eval Q = 0 → ¬ OrderLeAt m ι_E k ord Q := by
    intro ord hlt Q hne hsupp hev hord
    exact Nat.find_min hex_ord hlt ⟨Q, hne, hsupp, hev, hord⟩
  -- Step 2: Among relations of order ≤ ord₀, minimize `degreeOf (Sum.inl k, ord₀)`.
  have hex_deg : ∃ d : ℕ, ∃ Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
      Q ≠ 0 ∧ SupportedFrom m ι_E k Q ∧ eval Q = 0 ∧ OrderLeAt m ι_E k ord₀ Q ∧
      Q.degreeOf (Sum.inl k, ord₀) = d := by
    obtain ⟨Q, hne, hsupp, hev, hord⟩ := hord₀_spec
    exact ⟨Q.degreeOf (Sum.inl k, ord₀), Q, hne, hsupp, hev, hord, rfl⟩
  set d₀ : ℕ := Nat.find hex_deg
  obtain ⟨Q, hQne, hQsupp, hQev, hQord, hQdeg⟩ := Nat.find_spec hex_deg
  -- Step 3: Prove `0 < d₀` (otherwise `Q` has order strictly smaller than `ord₀` or is supported above `k`).
  have hd₀_pos : 0 < d₀ := by
    by_contra hd0
    have hd_zero : Q.degreeOf (Sum.inl k, ord₀) = 0 := by omega
    have hnot_in : ¬ InVars (Sum.inl k, ord₀) Q := by
      rw [inVars_iff_degreeOf_pos]
      omega
    cases hord_eq : ord₀ with
    | zero =>
      -- No `(Sum.inl k, ν)` can appear in `Q` at all!
      have haboveQ : SupportedAbove m ι_E k Q := by
        intro v hv
        have hs := hQsupp v hv
        cases hv1 : v.1 with
        | inr _ => trivial
        | inl j =>
          rw [hv1] at hs
          rcases lt_or_eq_of_le hs with hlt | heq_kj
          · exact hlt
          · exfalso
            subst heq_kj
            have hv_eq : v = (Sum.inl k, v.2) := Prod.ext hv1 rfl
            rw [hv_eq] at hv
            have hle0 : v.2 ≤ 0 := by
              have h := hQord v.2 hv
              omega
            have h0 : v.2 = 0 := Nat.le_zero.mp hle0
            rw [h0] at hv
            rw [hord_eq] at hnot_in
            exact hnot_in hv
      exact habove Q hQne haboveQ hQev
    | succ r =>
      -- Every `(Sum.inl k, ν)` appearing in `Q` has `ν ≤ r < r + 1`, contradicting minimality of `ord₀`.
      have hord_r : OrderLeAt m ι_E k r Q := by
        intro ν hν
        have hle := hQord ν hν
        rw [hord_eq] at hle hnot_in
        by_cases heq : ν = r + 1
        · subst heq; exact absurd hν hnot_in
        · omega
      have hlt_ord : r < ord₀ := by omega
      exact hord₀_min r hlt_ord Q hQne hQsupp hQev hord_r
  -- Step 4: Separant `S := pderiv (Sum.inl k, ord₀) Q` is nonzero and evaluates nonzero!
  have hQdeg_pos : 0 < Q.degreeOf (Sum.inl k, ord₀) := by omega
  set S : MvPolynomial (Sum (Fin m) ι_E × ℕ) K := MvPolynomial.pderiv (Sum.inl k, ord₀) Q
  have hSne : S ≠ 0 := mvPoly_pderiv_ne_zero_of_degreeOf_pos hQdeg_pos
  have hSsupp : SupportedFrom m ι_E k S := fun v hv => hQsupp v (mvPoly_pderiv_inVars hv)
  have hSord : OrderLeAt m ι_E k ord₀ S := fun ν hν => hQord ν (mvPoly_pderiv_inVars hν)
  have hSdeg_lt : S.degreeOf (Sum.inl k, ord₀) < d₀ := by
    dsimp only [S, d₀]
    exact lt_of_lt_of_le (mvPoly_pderiv_degreeOf_lt hQdeg_pos) (le_of_eq hQdeg)
  have hSev : eval S ≠ 0 := by
    intro hSzero
    exact Nat.find_min hex_deg hSdeg_lt ⟨S, hSne, hSsupp, hSzero, hSord, rfl⟩
  exact ⟨Q, ord₀, hQne, hQsupp, hQev, hQord, hQdeg_pos, hSne, hSev⟩

/-- Radius-ordered variable support predicate: every `Sum.inl j` appearing in `Q` has `r k ≤ r j`. -/
def SupportedByRadius {K : Type*} [CommSemiring K] {m : ℕ} {ι_E : Type*}
    (r : Fin m → ℝ) (k : Fin m) (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) : Prop :=
  ∀ v, InVars v Q → match v.1 with
    | Sum.inl j => r k ≤ r j
    | Sum.inr _ => True

/-- **Abstract Multivariate Natural-Boundary Radius Peeling Theorem:**
Given a finite family `f_0, ..., f_{m-1}` with strictly increasing Borel convergence radii
`r_0 < r_1 < ... < r_{m-1}` on top of an already-independent entire-Borel base family `E`:
if every minimal-order relation `Q` involving `f_k` (and only `f_j` with `r_k ≤ r_j` plus `E`)
with nonvanishing separant `∂Q / ∂Y_{k, ord}` implies analytic continuation of `f_k` across its
boundary circle `|s| = r_k`, contradicting its natural boundary, then **all `f_0, ..., f_{m-1}`
and `E` are jointly differentially independent over `K`**. -/
theorem radius_peeling_joint_diff_indep
    {K A ι_E : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    {m : ℕ} (f : Fin m → ℕ → A) (E : ι_E → ℕ → A)
    (r : Fin m → ℝ) (hr : StrictMono r)
    (ContinuableAcrossBoundary : Fin m → Prop)
    (hE : AlgebraicIndependent K (Function.uncurry E))
    (hnat : ∀ k : Fin m, ¬ ContinuableAcrossBoundary k)
    (hvolterra : ∀ (k : Fin m) (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) (ord : ℕ),
      Q ≠ 0 →
      SupportedByRadius r k Q →
      OrderLeAt m ι_E k ord Q →
      0 < Q.degreeOf (Sum.inl k, ord) →
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E)) Q = 0 →
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E))
        (MvPolynomial.pderiv (Sum.inl k, ord) Q) ≠ 0 →
      ContinuableAcrossBoundary k) :
    AlgebraicIndependent K (Function.uncurry (Sum.elim f E)) := by
  let eval := MvPolynomial.aeval (R := K) (Function.uncurry (Sum.elim f E))
  -- Backward induction on `d = 0, 1, ..., m`, proving independence of `{j | m - d ≤ j} ∪ E`.
  have htail : ∀ d : ℕ, d ≤ m →
      ∀ P : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
        P ≠ 0 → SupportedFromNat m ι_E (m - d) P → eval P ≠ 0 := by
    intro d
    induction d with
    | zero =>
      intro _ P hPne hPsupp hPev
      -- Every variable of `P` lies in `Sum.inr ι_E × ℕ`, contradicting `hE`.
      have hvars_inr : ∀ v, InVars v P → ∃ e : ι_E, v.1 = Sum.inr e := by
        intro v hv
        have hs := hPsupp v hv
        cases hv1 : v.1 with
        | inl j =>
          rw [hv1] at hs
          omega
        | inr e => exact ⟨e, rfl⟩
      let injE : ι_E × ℕ → Sum (Fin m) ι_E × ℕ := fun p => (Sum.inr p.1, p.2)
      have hinjE : Function.Injective injE := fun a b h =>
        Prod.ext (Sum.inr.inj (show (injE a).1 = (injE b).1 from congrArg Prod.fst h))
          (show (injE a).2 = (injE b).2 from congrArg Prod.snd h)
      let P_E : MvPolynomial (ι_E × ℕ) K :=
        ∑ u ∈ P.support, MvPolynomial.monomial
          (u.comapDomain injE hinjE.injOn) (P.coeff u)
      have hrename : MvPolynomial.rename injE P_E = P := by
        dsimp [P_E]
        rw [map_sum]
        conv_rhs => rw [P.as_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [MvPolynomial.rename_monomial]
        refine congrArg (fun d => MvPolynomial.monomial d (P.coeff u)) ?_
        ext v
        by_cases huv : u v = 0
        · have hzero : (Finsupp.mapDomain injE (u.comapDomain injE hinjE.injOn)) v = 0 := by
            rw [Finsupp.mapDomain, Finsupp.sum, finsupp_finset_sum_apply]
            refine Finset.sum_eq_zero fun p hp => ?_
            by_cases hvp : injE p = v
            · subst hvp
              rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] at hp
              exact absurd huv hp
            · simp [hvp]
          exact hzero.trans huv.symm
        · have hv_inv : InVars v P := ⟨u, MvPolynomial.mem_support_iff.mp hu, huv⟩
          obtain ⟨e, he⟩ := hvars_inr v hv_inv
          have hv_eq : v = injE (e, v.2) := Prod.ext he rfl
          rw [hv_eq, Finsupp.mapDomain, Finsupp.sum, finsupp_finset_sum_apply]
          have hmem : (e, v.2) ∈ (u.comapDomain injE hinjE.injOn).support := by
            rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]
            rwa [← hv_eq]
          rw [Finset.sum_eq_single (e, v.2)]
          · simp [Finsupp.comapDomain_apply]
          · intro p _ hne
            have hne' : injE p ≠ injE (e, v.2) := fun h => hne (hinjE h)
            simp [hne']
          · intro hnot; exact absurd hmem hnot
      have hPE_ne : P_E ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hrename
        exact hPne hrename.symm
      have hPE_ev : MvPolynomial.aeval (Function.uncurry E) P_E = 0 := by
        have heq : MvPolynomial.aeval (Function.uncurry E) P_E = eval P := by
          rw [← hrename]
          dsimp [eval]
          rw [MvPolynomial.aeval_rename]
          congr 1
        rw [heq]
        exact hPev
      exact hPE_ne (algebraicIndependent_iff.mp hE P_E hPE_ev)
    | succ d ih =>
      intro hdm P hPne hPsupp hPev
      let k : Fin m := ⟨m - (d + 1), by omega⟩
      have habove : ∀ Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K,
          Q ≠ 0 → SupportedAbove m ι_E k Q → eval Q ≠ 0 := by
        intro Q hQne hQabove
        apply ih (by omega) Q hQne
        intro v hv
        have hs := hQabove v hv
        cases hv1 : v.1 with
        | inr _ => trivial
        | inl j =>
          rw [hv1] at hs
          have hlt : k.val < j.val := hs
          dsimp [k] at hlt
          omega
      have hPsupp_k : SupportedFrom m ι_E k P := by
        intro v hv
        have hs := hPsupp v hv
        cases hv1 : v.1 with
        | inr _ => trivial
        | inl j =>
          rw [hv1] at hs
          exact hs
      obtain ⟨Q, ord, hQne, hQsupp, hQev, hQord, hQdeg, _, hSev⟩ :=
        exists_minimal_relation_nonzero_separant f E k habove ⟨P, hPne, hPsupp_k, hPev⟩
      have hQrad : SupportedByRadius r k Q := by
        intro v hv
        have hs := hQsupp v hv
        cases hv1 : v.1 with
        | inr _ => trivial
        | inl j =>
          rw [hv1] at hs
          exact hr.monotone hs
      exact hnat k (hvolterra k Q ord hQne hQrad hQord hQdeg hQev hSev)
  rw [algebraicIndependent_iff]
  intro P hPev
  by_contra hPne
  exact htail m le_rfl P hPne (fun v _ => by cases v.1 <;> simp) hPev

/-- General field-extension transfer: if `Sum.elim f E` is algebraically independent over a
field `K` in a field extension `L`, then `f` is algebraically independent over the generated
intermediate field `K(E)`. -/
theorem algebraicIndependent_intermediateField_adjoin_of_sum
    {K L α β : Type*} [Field K] [Field L] [Algebra K L]
    (f : α → L) (E : β → L)
    (h : AlgebraicIndependent K (Sum.elim f E)) :
    AlgebraicIndependent (IntermediateField.adjoin K (Set.range E)) f := by
  let A_E : Subalgebra K L := Algebra.adjoin K (Set.range E)
  -- Show every element of `K(E)` is a quotient of elements of `K[E]`.
  let fracSub : IntermediateField K L :=
    { carrier := {x : L | ∃ a b : A_E, (b : L) ≠ 0 ∧ x = (a : L) / (b : L)}
      mul_mem' := by
        rintro x y ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
        push_cast; ring
      one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
        push_cast; field_simp
      zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
      inv_mem' := by
        rintro x ⟨a, b, hb, rfl⟩
        by_cases ha : (a : L) = 0
        · refine ⟨0, 1, one_ne_zero, ?_⟩
          simp [ha]
        · refine ⟨b, a, ha, ?_⟩
          rw [inv_div]
      algebraMap_mem' := fun c => ⟨algebraMap K A_E c, 1, one_ne_zero, by simp⟩ }
  have hle : IntermediateField.adjoin K (Set.range E) ≤ fracSub := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨E j, Algebra.subset_adjoin ⟨j, rfl⟩⟩, 1, one_ne_zero, by simp⟩
  -- Now prove `aeval f p = 0 → p = 0` by clearing denominators in `A_E`.
  rw [algebraicIndependent_iff]
  intro p hp
  have hfrac : ∀ m : α →₀ ℕ,
      ∃ a b : A_E, (b : L) ≠ 0 ∧ (p.coeff m : L) = (a : L) / (b : L) :=
    fun m => hle (p.coeff m).2
  choose a b hb hab using hfrac
  let D : A_E := ∏ m ∈ p.support, b m
  have hD_ne : (D : L) ≠ 0 := by
    have hD_prod : (D : L) = ∏ m ∈ p.support, (b m : L) := map_prod A_E.val b p.support
    rw [hD_prod]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => hb m
  have hlift : ∀ m ∈ p.support,
      ∃ q : MvPolynomial β K, MvPolynomial.aeval E q = (D : L) * (p.coeff m : L) := by
    intro m hm
    have hmem : (D : L) * (p.coeff m : L) ∈ A_E := by
      have hD_eq : (D : L) = (b m : L) * ((∏ m' ∈ p.support.erase m, b m' : A_E) : L) := by
        dsimp [D]
        rw [← Finset.mul_prod_erase p.support b hm]
        simp
      rw [hD_eq, hab m]
      have hbm : (b m : L) ≠ 0 := hb m
      have hsimp : (b m : L) * ((∏ m' ∈ p.support.erase m, b m' : A_E) : L) *
          ((a m : L) / (b m : L)) =
          ((a m * ∏ m' ∈ p.support.erase m, b m' : A_E) : L) := by
        push_cast; field_simp
      rw [hsimp]
      exact (a m * ∏ m' ∈ p.support.erase m, b m').2
    have hmem' : (D : L) * (p.coeff m : L) ∈ Algebra.adjoin K (Set.range E) := hmem
    rwa [Algebra.adjoin_range_eq_range_aeval] at hmem'
  let q_fun : (α →₀ ℕ) → MvPolynomial β K := fun m =>
    if hm : m ∈ p.support then Classical.choose (hlift m hm) else 0
  have hq_spec : ∀ m ∈ p.support,
      MvPolynomial.aeval E (q_fun m) = (D : L) * (p.coeff m : L) := by
    intro m hm
    simp only [q_fun, hm, ↓reduceDIte]
    exact Classical.choose_spec (hlift m hm)
  let Q : MvPolynomial (Sum α β) K :=
    ∑ m ∈ p.support, ∑ n ∈ (q_fun m).support,
      MvPolynomial.monomial (m.mapDomain Sum.inl + n.mapDomain Sum.inr) ((q_fun m).coeff n)
  have hQ_ev : MvPolynomial.aeval (Sum.elim f E) Q = 0 := by
    dsimp [Q]
    simp only [map_sum, MvPolynomial.aeval_monomial]
    have hterm : ∀ m ∈ p.support,
        (∑ n ∈ (q_fun m).support,
          algebraMap K L ((q_fun m).coeff n) *
            (m.mapDomain Sum.inl + n.mapDomain Sum.inr).prod
              (fun i k => Sum.elim f E i ^ k)) =
          (D : L) * (p.coeff m : L) * m.prod (fun i k => f i ^ k) := by
      intro m hm
      have hsplit_prod : ∀ n : β →₀ ℕ,
          (m.mapDomain Sum.inl + n.mapDomain Sum.inr).prod (fun i k => Sum.elim f E i ^ k) =
            m.prod (fun i k => f i ^ k) * n.prod (fun j k => E j ^ k) := by
        intro n
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
        congr 1
        · rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
          rfl
        · rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
          rfl
      calc
        ∑ n ∈ (q_fun m).support,
            algebraMap K L ((q_fun m).coeff n) *
              (m.mapDomain Sum.inl + n.mapDomain Sum.inr).prod (fun i k => Sum.elim f E i ^ k)
            = (∑ n ∈ (q_fun m).support,
                algebraMap K L ((q_fun m).coeff n) * n.prod (fun j k => E j ^ k)) *
                m.prod (fun i k => f i ^ k) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [hsplit_prod n]
              ring
        _ = MvPolynomial.aeval E (q_fun m) * m.prod (fun i k => f i ^ k) := by
              rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
              rfl
        _ = (D : L) * (p.coeff m : L) * m.prod (fun i k => f i ^ k) := by
              rw [hq_spec m hm]
    rw [Finset.sum_congr rfl hterm]
    have hfactor : (∑ m ∈ p.support, (D : L) * (p.coeff m : L) * m.prod (fun i k => f i ^ k)) =
        (D : L) * MvPolynomial.aeval f p := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [IntermediateField.algebraMap_apply, mul_assoc, Finsupp.prod]
    rw [hfactor, hp, mul_zero]
  have hQ_zero : Q = 0 := algebraicIndependent_iff.mp h Q hQ_ev
  have hmap_inl_inl : ∀ (r : α →₀ ℕ) (i : α),
      (r.mapDomain (@Sum.inl α β)) (Sum.inl i) = r i := by
    intro r i
    rw [Finsupp.mapDomain, Finsupp.sum, finsupp_finset_sum_apply]
    by_cases hr : i ∈ r.support
    · rw [Finset.sum_eq_single i]
      · simp
      · intro a _ hne; simp [hne]
      · intro hnot; exact absurd hr hnot
    · rw [Finsupp.notMem_support_iff.mp hr]
      refine Finset.sum_eq_zero fun a ha => ?_
      have hne : a ≠ i := fun h => hr (h ▸ ha)
      simp [hne]
  have hmap_inr_inr : ∀ (r : β →₀ ℕ) (j : β),
      (r.mapDomain (@Sum.inr α β)) (Sum.inr j) = r j := by
    intro r j
    rw [Finsupp.mapDomain, Finsupp.sum, finsupp_finset_sum_apply]
    by_cases hr : j ∈ r.support
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hne; simp [hne]
      · intro hnot; exact absurd hr hnot
    · rw [Finsupp.notMem_support_iff.mp hr]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hne : b ≠ j := fun h => hr (h ▸ hb)
      simp [hne]
  have hmap_inl_inr : ∀ (r : α →₀ ℕ) (j : β),
      (r.mapDomain (@Sum.inl α β)) (Sum.inr j) = 0 := by
    intro r j
    rw [Finsupp.mapDomain, Finsupp.sum, finsupp_finset_sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    simp
  have hmap_inr_inl : ∀ (r : β →₀ ℕ) (i : α),
      (r.mapDomain (@Sum.inr α β)) (Sum.inl i) = 0 := by
    intro r i
    rw [Finsupp.mapDomain, Finsupp.sum, finsupp_finset_sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp
  apply MvPolynomial.ext
  intro m
  change p.coeff m = 0
  by_cases hm : m ∈ p.support
  · have hq0 : q_fun m = 0 := by
      ext n
      change (q_fun m).coeff n = 0
      by_cases hn : n ∈ (q_fun m).support
      · have hcoeffQ : Q.coeff (m.mapDomain Sum.inl + n.mapDomain Sum.inr) = (q_fun m).coeff n := by
          dsimp [Q]
          simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
          rw [Finset.sum_eq_single m]
          · rw [Finset.sum_eq_single n]
            · simp
            · intro n' _ hne
              split_ifs with heq
              · exfalso
                apply hne
                ext j
                have hj := congrArg (fun d : Sum α β →₀ ℕ => d (Sum.inr j)) heq
                simp only [Finsupp.add_apply, hmap_inl_inr, hmap_inr_inr, zero_add] at hj
                exact hj
              · rfl
            · intro hnot; exact absurd hn hnot
          · intro m' _ hne
            refine Finset.sum_eq_zero fun n' _ => ?_
            split_ifs with heq
            · exfalso
              apply hne
              ext i
              have hi := congrArg (fun d : Sum α β →₀ ℕ => d (Sum.inl i)) heq
              simp only [Finsupp.add_apply, hmap_inl_inl, hmap_inr_inl, add_zero] at hi
              exact hi
            · rfl
          · intro hnot; exact absurd hm hnot
        have hzero_c : Q.coeff (m.mapDomain Sum.inl + n.mapDomain Sum.inr) = 0 := by
          rw [hQ_zero]; rfl
        rw [← hcoeffQ, hzero_c]
      · exact MvPolynomial.notMem_support_iff.mp hn
    have hDmul : (D : L) * (p.coeff m : L) = 0 := by
      rw [← hq_spec m hm, hq0, map_zero]
    have hpm0 : (p.coeff m : L) = 0 := (mul_eq_zero.mp hDmul).resolve_left hD_ne
    exact Subtype.ext hpm0
  · exact MvPolynomial.notMem_support_iff.mp hm

/-- Corollary over the generated differential base field `K⟨E⟩`: under the radius-peeling
hypotheses of `radius_peeling_joint_diff_indep`, the family `f_0, ..., f_{m-1}` is jointly
differentially independent over `K⟨E⟩`. -/
theorem radius_peeling_over_baseField
    {K L ι_E : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    {m : ℕ} (f : Fin m → ℕ → L) (E : ι_E → ℕ → L)
    (r : Fin m → ℝ) (hr : StrictMono r)
    (ContinuableAcrossBoundary : Fin m → Prop)
    (hE : AlgebraicIndependent K (Function.uncurry E))
    (hnat : ∀ k : Fin m, ¬ ContinuableAcrossBoundary k)
    (hvolterra : ∀ (k : Fin m) (Q : MvPolynomial (Sum (Fin m) ι_E × ℕ) K) (ord : ℕ),
      Q ≠ 0 →
      SupportedByRadius r k Q →
      OrderLeAt m ι_E k ord Q →
      0 < Q.degreeOf (Sum.inl k, ord) →
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E)) Q = 0 →
      MvPolynomial.aeval (Function.uncurry (Sum.elim f E))
        (MvPolynomial.pderiv (Sum.inl k, ord) Q) ≠ 0 →
      ContinuableAcrossBoundary k) :
    AlgebraicIndependent (IntermediateField.adjoin K (Set.range (Function.uncurry E)))
      (Function.uncurry f) := by
  have hjoint := radius_peeling_joint_diff_indep f E r hr ContinuableAcrossBoundary
    hE hnat hvolterra
  let e : (Fin m × ℕ) ⊕ (ι_E × ℕ) ≃ Sum (Fin m) ι_E × ℕ :=
    (Equiv.sumProdDistrib (Fin m) ι_E ℕ).symm
  have hsum : AlgebraicIndependent K (Sum.elim (Function.uncurry f) (Function.uncurry E)) := by
    have hcomp : Function.uncurry (Sum.elim f E) ∘ e =
        Sum.elim (Function.uncurry f) (Function.uncurry E) := by
      funext x
      cases x <;> rfl
    rw [← hcomp]
    exact hjoint.comp e e.injective
  exact algebraicIndependent_intermediateField_adjoin_of_sum
    (Function.uncurry f) (Function.uncurry E) hsum

/-- **Two-Stage 10-Series Gross CM Radius-Peeling Instantiation (`m = 5` on top of `m = 5`):**
Directly feeds our proved `grossRadius_strictMono` (`ρ_{163} < ρ_{67} < ρ_{43} < ρ_{19} < ρ_{11}`)
into two stages of `radius_peeling_joint_diff_indep`:
- Stage 1 peels the 5 signed Gross CM series (radii `ρ_ℓ / 2`) over `K`;
- Stage 2 peels the 5 squared Gross CM series (radii `ρ_ℓ`) on top of the 5 signed series
  (whose `t`-Borel transforms are entire), proving all 10 series jointly differentially
  independent over `K` AND the 5 squared series jointly independent over `K⟨5 signed⟩`! -/
theorem grossCM_ten_series_radius_peeling
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    (signed squared : Fin 5 → ℕ → L)
    (ContSigned ContSquared : Fin 5 → Prop)
    (hnatSigned : ∀ k : Fin 5, ¬ ContSigned k)
    (hnatSquared : ∀ k : Fin 5, ¬ ContSquared k)
    (hvolSigned : ∀ (k : Fin 5) (Q : MvPolynomial (Sum (Fin 5) Empty × ℕ) K) (ord : ℕ),
      Q ≠ 0 →
      SupportedByRadius (fun i : Fin 5 => grossRadius i / 2) k Q →
      OrderLeAt 5 Empty k ord Q →
      0 < Q.degreeOf (Sum.inl k, ord) →
      MvPolynomial.aeval (Function.uncurry (Sum.elim signed Empty.elim)) Q = 0 →
      MvPolynomial.aeval (Function.uncurry (Sum.elim signed Empty.elim))
        (MvPolynomial.pderiv (Sum.inl k, ord) Q) ≠ 0 →
      ContSigned k)
    (hvolSquared : ∀ (k : Fin 5) (Q : MvPolynomial (Sum (Fin 5) (Fin 5) × ℕ) K) (ord : ℕ),
      Q ≠ 0 →
      SupportedByRadius grossRadius k Q →
      OrderLeAt 5 (Fin 5) k ord Q →
      0 < Q.degreeOf (Sum.inl k, ord) →
      MvPolynomial.aeval (Function.uncurry (Sum.elim squared signed)) Q = 0 →
      MvPolynomial.aeval (Function.uncurry (Sum.elim squared signed))
        (MvPolynomial.pderiv (Sum.inl k, ord) Q) ≠ 0 →
      ContSquared k) :
    AlgebraicIndependent K (Function.uncurry (Sum.elim squared signed)) ∧
    AlgebraicIndependent (IntermediateField.adjoin K (Set.range (Function.uncurry signed)))
      (Function.uncurry squared) := by
  have hr_half : StrictMono (fun i : Fin 5 => grossRadius i / 2) := fun i j hij =>
    div_lt_div_of_pos_right (grossRadius_strictMono hij) two_pos
  have hEmpty : AlgebraicIndependent K (Function.uncurry (Empty.elim : Empty → ℕ → L)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    exact MvPolynomial.aeval_injective_iff_of_isEmpty.mpr (algebraMap K L).injective
  have hstage1_sum := radius_peeling_joint_diff_indep signed (Empty.elim : Empty → ℕ → L)
    (fun i => grossRadius i / 2) hr_half ContSigned hEmpty hnatSigned hvolSigned
  have hstage1 : AlgebraicIndependent K (Function.uncurry signed) := by
    let emb : Fin 5 × ℕ → Sum (Fin 5) Empty × ℕ := fun p => (Sum.inl p.1, p.2)
    have hemb_inj : Function.Injective emb := by
      intro p q h
      have h1 : p.1 = q.1 := Sum.inl.inj (show (emb p).1 = (emb q).1 from congrArg Prod.fst h)
      have h2 : p.2 = q.2 := show (emb p).2 = (emb q).2 from congrArg Prod.snd h
      exact Prod.ext h1 h2
    have hcomp : Function.uncurry (Sum.elim signed (Empty.elim : Empty → ℕ → L)) ∘ emb =
        Function.uncurry signed := by
      funext p; rfl
    rw [← hcomp]
    exact hstage1_sum.comp emb hemb_inj
  have hstage2 := radius_peeling_joint_diff_indep squared signed
    grossRadius grossRadius_strictMono ContSquared hstage1 hnatSquared hvolSquared
  have hstage2_field := radius_peeling_over_baseField squared signed
    grossRadius grossRadius_strictMono ContSquared hstage1 hnatSquared hvolSquared
  exact ⟨hstage2, hstage2_field⟩

/-- **Universal Pair Peeling Instantiation (`m = 1` on top of a base series `H`, Corollary C):**
If `H` is differentially transcendental over `K` (e.g. entire `t`-Borel transform) and `H_sq`
satisfies the natural-boundary Volterra peeling barrier over `H`, then `(H_sq, H)` are jointly
differentially independent over `K` and `H_sq` is differentially transcendental over `K⟨H⟩`. -/
theorem universal_pair_radius_peeling
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    (H H_sq : ℕ → L) (r_sq : ℝ)
    (ContSq : Prop) (hnatSq : ¬ ContSq)
    (hH : AlgebraicIndependent K H)
    (hvolSq : ∀ (Q : MvPolynomial (Sum (Fin 1) Unit × ℕ) K) (ord : ℕ),
      Q ≠ 0 →
      OrderLeAt 1 Unit 0 ord Q →
      0 < Q.degreeOf (Sum.inl 0, ord) →
      MvPolynomial.aeval
        (Function.uncurry (Sum.elim (fun _ : Fin 1 => H_sq) (fun _ : Unit => H))) Q = 0 →
      MvPolynomial.aeval
        (Function.uncurry (Sum.elim (fun _ : Fin 1 => H_sq) (fun _ : Unit => H)))
        (MvPolynomial.pderiv (Sum.inl 0, ord) Q) ≠ 0 →
      ContSq) :
    AlgebraicIndependent K
      (Function.uncurry (Sum.elim (fun _ : Fin 1 => H_sq) (fun _ : Unit => H))) ∧
    AlgebraicIndependent (IntermediateField.adjoin K (Set.range H)) H_sq := by
  have hE : AlgebraicIndependent K (Function.uncurry (fun _ : Unit => H)) := by
    let e : Unit × ℕ ≃ ℕ := Equiv.punitProd ℕ
    have hcomp : H ∘ e = Function.uncurry (fun _ : Unit => H) := by
      funext ⟨⟨⟩, n⟩; rfl
    rw [← hcomp]
    exact hH.comp e e.injective
  have hr : StrictMono (fun _ : Fin 1 => r_sq) := fun i j hij => by
    have : i = j := Subsingleton.elim i j
    exact absurd this hij.ne
  have hjoint := radius_peeling_joint_diff_indep
    (fun _ : Fin 1 => H_sq) (fun _ : Unit => H)
    (fun _ : Fin 1 => r_sq) hr (fun _ : Fin 1 => ContSq)
    hE (fun _ => hnatSq)
    (fun k Q ord hQne _ hQord hQdeg hQev hSev => by
      fin_cases k
      exact hvolSq Q ord hQne hQord hQdeg hQev hSev)
  have hfield := radius_peeling_over_baseField
    (fun _ : Fin 1 => H_sq) (fun _ : Unit => H)
    (fun _ : Fin 1 => r_sq) hr (fun _ : Fin 1 => ContSq)
    hE (fun _ => hnatSq)
    (fun k Q ord hQne _ hQord hQdeg hQev hSev => by
      fin_cases k
      exact hvolSq Q ord hQne hQord hQdeg hQev hSev)
  have hrange : Set.range (Function.uncurry (fun _ : Unit => H)) = Set.range H := by
    ext x; simp [Function.uncurry]
  rw [hrange] at hfield
  refine ⟨hjoint, ?_⟩
  let e1 : ℕ ≃ Fin 1 × ℕ := (Equiv.uniqueProd ℕ (Fin 1)).symm
  have hcomp1 : Function.uncurry (fun _ : Fin 1 => H_sq) ∘ e1 = H_sq := by
    funext n; rfl
  rw [← hcomp1]
  exact hfield.comp e1 e1.injective

end MultivariateRadiusPeeling

/-! ### 4. Ramanujan's Lost Notebook p. 343 Hidden Units in `ℤ[⁵√2]^×` (and `ℤ[⁷√2]^×`) -/

section LostNotebookP343Units

/-- Over any commutative ring with `θ^5 = 2`, `(1 + θ^2)^5 = 5 (1 + θ + θ^3)^2`. -/
theorem ln343_fifth_power_eq {R : Type*} [CommRing R] {θ : R} (hθ : θ ^ 5 = 2) :
    (1 + θ ^ 2) ^ 5 = 5 * (1 + θ + θ ^ 3) ^ 2 := by
  have h6 : θ ^ 6 = 2 * θ := by rw [pow_succ, hθ]
  have h8 : θ ^ 8 = 2 * θ ^ 3 := by
    calc θ ^ 8 = θ ^ 5 * θ ^ 3 := by ring
      _ = 2 * θ ^ 3 := by rw [hθ]
  have h10 : θ ^ 10 = 4 := by
    calc θ ^ 10 = (θ ^ 5) ^ 2 := by ring
      _ = 4 := by rw [hθ]; norm_num
  linear_combination 5 * h6 + 5 * h8 + h10

/-- Over any commutative ring with `θ^5 = 2`, `(1 + θ + θ^3)(1 - θ - θ^2 + θ^4) = 1`. -/
theorem ln343_unit_mul_inv {R : Type*} [CommRing R] {θ : R} (hθ : θ ^ 5 = 2) :
    (1 + θ + θ ^ 3) * (1 - θ - θ ^ 2 + θ ^ 4) = 1 := by
  have h7 : θ ^ 7 = 2 * θ ^ 2 := by
    calc θ ^ 7 = θ ^ 5 * θ ^ 2 := by ring
      _ = 2 * θ ^ 2 := by rw [hθ]
  linear_combination h7

/-- `1 - θ - θ^2 + θ^4` is a unit in any commutative ring with `θ^5 = 2`. -/
theorem ln343_isUnit {R : Type*} [CommRing R] {θ : R} (hθ : θ ^ 5 = 2) :
    IsUnit (1 - θ - θ ^ 2 + θ ^ 4) := by
  rw [isUnit_iff_exists_inv']
  exact ⟨1 + θ + θ ^ 3, ln343_unit_mul_inv hθ⟩

/-- `1 + θ + θ^3` is a unit in any commutative ring with `θ^5 = 2`. -/
theorem ln343_inv_isUnit {R : Type*} [CommRing R] {θ : R} (hθ : θ ^ 5 = 2) :
    IsUnit (1 + θ + θ ^ 3) := by
  rw [isUnit_iff_exists_inv]
  exact ⟨1 - θ - θ ^ 2 + θ ^ 4, ln343_unit_mul_inv hθ⟩

/-- Exact real identity for Ramanujan's LN p. 343 radical (`θ = 2^(1/5)`):
`√5 / (1 + 2^(2/5))^(5/2) = 1 - θ - θ^2 + θ^4`. -/
theorem ln343_real_identity :
    let θ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 5)
    Real.sqrt 5 / (1 + (2 : ℝ) ^ ((2 : ℝ) / 5)) ^ ((5 : ℝ) / 2) =
      1 - θ - θ ^ 2 + θ ^ 4 := by
  intro θ
  have hθ_pos : 0 < θ := Real.rpow_pos_of_pos two_pos _
  have hθ5 : θ ^ 5 = 2 := by
    dsimp [θ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hθ2 : θ ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 5) := by
    dsimp [θ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; norm_num
  have hbase_pos : 0 < 1 + θ ^ 2 := by positivity
  have hpow_sqrt : (1 + (2 : ℝ) ^ ((2 : ℝ) / 5)) ^ ((5 : ℝ) / 2) =
      Real.sqrt ((1 + θ ^ 2) ^ 5) := by
    rw [← hθ2, Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + θ ^ 2) 5,
      ← Real.rpow_mul hbase_pos.le]
    congr 1; norm_num
  have hpos_factor : 0 < 1 + θ + θ ^ 3 := by positivity
  have hsqrt_eval : Real.sqrt ((1 + θ ^ 2) ^ 5) = Real.sqrt 5 * (1 + θ + θ ^ 3) := by
    rw [ln343_fifth_power_eq hθ5, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5),
      Real.sqrt_sq hpos_factor.le]
  rw [hpow_sqrt, hsqrt_eval]
  have hmul := ln343_unit_mul_inv hθ5
  have hs5 : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have hf_ne : 1 + θ + θ ^ 3 ≠ 0 := hpos_factor.ne'
  rw [div_eq_iff (mul_ne_zero hs5 hf_ne)]
  calc
    Real.sqrt 5 = Real.sqrt 5 * 1 := (mul_one _).symm
    _ = Real.sqrt 5 * ((1 + θ + θ ^ 3) * (1 - θ - θ ^ 2 + θ ^ 4)) := by rw [hmul]
    _ = (1 - θ - θ ^ 2 + θ ^ 4) * (Real.sqrt 5 * (1 + θ + θ ^ 3)) := by ring

/-- Explicit unit witness inside the ring of integers subring `ℤ[⁵√2] = Algebra.adjoin ℤ {2^(1/5)}`:
Ramanujan's radical `√5 / (1 + 2^(2/5))^(5/2)` equals `1 - θ - θ^2 + θ^4` and is a unit in `ℤ[⁵√2]`. -/
theorem ln343_unit_in_Z_adjoin_fifthRoot2 :
    ∃ u : Algebra.adjoin ℤ ({(2 : ℝ) ^ ((1 : ℝ) / 5)} : Set ℝ),
      IsUnit u ∧
      (u : ℝ) = Real.sqrt 5 / (1 + (2 : ℝ) ^ ((2 : ℝ) / 5)) ^ ((5 : ℝ) / 2) := by
  set θR : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 5)
  let θ : Algebra.adjoin ℤ ({θR} : Set ℝ) :=
    ⟨θR, Algebra.subset_adjoin (Set.mem_singleton θR)⟩
  have hθ5 : θ ^ 5 = 2 := by
    apply Subtype.ext
    have hr : θR ^ 5 = 2 := by
      dsimp [θR]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    change θR ^ 5 = (2 : ℝ)
    exact hr
  refine ⟨1 - θ - θ ^ 2 + θ ^ 4, ln343_isUnit hθ5, ?_⟩
  rw [ln343_real_identity]
  simp [θ, θR]

/-- Bonus (Ramanujan's LN p. 343 Block 2 in `ℤ[⁷√2]^×`): over any commutative ring with `θ^7 = 2`,
all three Block 2 generators are units with explicit integer-polynomial inverses. -/
theorem ln343_block2_seventhRoot2_units {R : Type*} [CommRing R] {θ : R} (hθ : θ ^ 7 = 2) :
    ((θ - 1) * (1 + θ + θ ^ 2 + θ ^ 3 + θ ^ 4 + θ ^ 5 + θ ^ 6) = 1) ∧
    ((1 + 12 * θ + 10 * θ ^ 2 + θ ^ 3 - 4 * θ ^ 4 - 10 * θ ^ 5 - 3 * θ ^ 6) *
      (1689 + 1528 * θ + 1384 * θ ^ 2 + 1255 * θ ^ 3 + 1136 * θ ^ 4 + 1028 * θ ^ 5 +
        932 * θ ^ 6) = 1) ∧
    ((1 - θ ^ 2 - θ ^ 3 + θ ^ 5 + θ ^ 6) *
      (-1 + θ ^ 2 - θ ^ 3 + θ ^ 4 - θ ^ 5 + θ ^ 6) = 1) ∧
    IsUnit (1 + θ + θ ^ 2 + θ ^ 3 + θ ^ 4 + θ ^ 5 + θ ^ 6) ∧
    IsUnit (1689 + 1528 * θ + 1384 * θ ^ 2 + 1255 * θ ^ 3 + 1136 * θ ^ 4 + 1028 * θ ^ 5 +
      932 * θ ^ 6) ∧
    IsUnit (1 - θ ^ 2 - θ ^ 3 + θ ^ 5 + θ ^ 6) := by
  have h8 : θ ^ 8 = 2 * θ := by calc θ ^ 8 = θ ^ 7 * θ := by ring
                                _ = 2 * θ := by rw [hθ]
  have h9 : θ ^ 9 = 2 * θ ^ 2 := by calc θ ^ 9 = θ ^ 7 * θ ^ 2 := by ring
                                    _ = 2 * θ ^ 2 := by rw [hθ]
  have h10 : θ ^ 10 = 2 * θ ^ 3 := by calc θ ^ 10 = θ ^ 7 * θ ^ 3 := by ring
                                      _ = 2 * θ ^ 3 := by rw [hθ]
  have h11 : θ ^ 11 = 2 * θ ^ 4 := by calc θ ^ 11 = θ ^ 7 * θ ^ 4 := by ring
                                      _ = 2 * θ ^ 4 := by rw [hθ]
  have h12 : θ ^ 12 = 2 * θ ^ 5 := by calc θ ^ 12 = θ ^ 7 * θ ^ 5 := by ring
                                      _ = 2 * θ ^ 5 := by rw [hθ]
  have ha : (θ - 1) * (1 + θ + θ ^ 2 + θ ^ 3 + θ ^ 4 + θ ^ 5 + θ ^ 6) = 1 := by
    linear_combination hθ
  have hb : (1 + 12 * θ + 10 * θ ^ 2 + θ ^ 3 - 4 * θ ^ 4 - 10 * θ ^ 5 - 3 * θ ^ 6) *
      (1689 + 1528 * θ + 1384 * θ ^ 2 + 1255 * θ ^ 3 + 1136 * θ ^ 4 + 1028 * θ ^ 5 +
        932 * θ ^ 6) = 1 := by
    linear_combination -844 * hθ - 10898 * h8 - 18305 * h9 - 17416 * h10 - 12404 * h11 - 2796 * h12
  have hc : (1 - θ ^ 2 - θ ^ 3 + θ ^ 5 + θ ^ 6) *
      (-1 + θ ^ 2 - θ ^ 3 + θ ^ 4 - θ ^ 5 + θ ^ 6) = 1 := by
    linear_combination hθ - h9 + h12
  exact ⟨ha, hb, hc,
    isUnit_iff_exists_inv'.mpr ⟨_, ha⟩,
    isUnit_iff_exists_inv'.mpr ⟨_, hb⟩,
    isUnit_iff_exists_inv.mpr ⟨_, hc⟩⟩

end LostNotebookP343Units

end

end CubicTheta.AllD
