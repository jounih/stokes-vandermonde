module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! # Cogentic Analytic & Certification Toolkit

Self-contained, Mathlib-only formalization of four reusable analytic and certification primitives
extracted from Google Research's Cogentic papers (`edge_reconstruction.pdf` and
`bimatrix_nash_equilibrium.pdf`):

1. **Elementary Van der Corput First- and Second-Derivative Oscillatory Integral Bounds**
   (`oscillatory_integral_bound_first_deriv`, `van_der_corput_second_deriv_sharp`,
   `van_der_corput_second_deriv`) from `edge_reconstruction.pdf`, Lemma 4.1(2a).
2. **Multi-Scale Geometric Exponential Filter Bank & Plancherel Spectral Dominance**
   (`filterSymbol_re`, `filterSymbol_im`, `avgFilterSymbol_re_mem_Icc`,
   `multiscale_imag_sq_le`, `multiscale_dissipative_lower_bound`,
   `multiscale_antisymmetric_bound`, `multiscale_filter_spectral_dominance`) from
   `bimatrix_nash_equilibrium.pdf`, Lemma 3.1.
3. **Exact Rational Interval & Grid Certificate Combinators + Collatz–Wielandt Spectral Bound**
   (`RatInterval`, `gridCovers`, `certify_on_grid`, `certify_on_grid_exact`,
   `certify_on_grid_of_check`, `gridCovers_uniformGrid`,
   `collatz_wielandt_rat_upper_bound`, `collatz_wielandt_rat_upper_bound_complex`,
   `collatz_wielandt_rat_pure`) following `bimatrix_nash_equilibrium.pdf`, Appendix A.
4. **Elementary Taylor / Exponential & Logarithmic Rational Bounds**
   (`expTaylor`, `exp_taylor_le_exp`, `exp_le_taylor_add_rem`,
   `exp_quarter_lt`, `exp_quarter_gt`, `exp_half_lt`,
   `log_two_lt_one`, `log_two_lt_three_quarters`, `half_lt_log_two`, `log_three_lt_two`)
   from `edge_reconstruction.pdf`, p. 22.

## Non-Circular Parameter & Constant Schedule

All parameters and constants are fixed in strict topological order with zero circular dependencies:

1. **Section 1 (Oscillatory Integrals):**
   - Inputs: interval `[a, b]` (`a ≤ b`), amplitude bound `M ≥ 0`.
   - First-derivative bound (`lam > 0`): integration by parts with monotone `φ'` cancels one
     boundary term against the total variation of `1 / φ'`, yielding exact constants
     `C₁ = 2 / lam` (amplitude) and `C₂ = 1 / lam` (derivative `L¹` norm).
   - Second-derivative bound (`μ > 0`): choose excision half-width `δ := 1 / √μ`, so the outer
     first-derivative threshold is `lam := μ * δ = √μ`. Combining the middle excision (`2 δ M`)
     with the two outer pieces (`2 * (2 / (μ δ)) M + (1 / (μ δ)) ∫ ‖a₀'‖`) yields the sharp
     constant `(2 + 4) / √μ = 6 / √μ ≤ 8 / √μ` on `M` and `1 / √μ` on `∫ ‖deriv a₀‖`.

2. **Section 2 (Multi-Scale Geometric Filter Bank):**
   - Geometric base `ρ := 64`, decay rates `α_k := 64^{-k}` (`k = 0, ..., K - 1`).
   - Tail geometric series bounds: `∑_{j=0}^{m-1} 64^{-j} < 64 / 63` and
     `∑_{j=1}^m 64^{-j} < 1 / 63`.
   - Adjacent-scale transition bound (`t_m ≤ 1 < 64 t_m`): splitting at `t_m = 1 / 8` yields
     `c_m + c_{m+1} ≤ 1 / 2 + 1 / 8 = 5 / 8`, hence total imaginary sum
     `C ≤ 5 / 8 + 2 / 63 = 331 / 504 < 2 / 3`.
   - Spectral dominance constant `5`: outer regimes use `(64 / 63)^2 = 4096 / 3969 ≤ 5 / 4`;
     interior regime uses `(2 / 3)^2 = 4 / 9 ≤ 5 (K - 1) / (4 K)` for all `K ≥ 2` (and `K = 1`
     gives `y^2 = x (1 - x) ≤ 5 x (1 - x)` directly).
   - Dissipative threshold `K ≥ 10`: gives `1 - 5 / K ≥ 1 / 2`, so
     `dissipativeSymbol K ξ ≥ (1 - 5 / K) x (1 - x) ≥ (1 / 2) x (1 - x) ≥ 0` and
     `4 y^2 ≤ (40 / K) * dissipativeSymbol K ξ`.

3. **Section 3 (Rational Grid & Collatz–Wielandt Certificates):**
   - Grid interval `I₀ = [lo, hi]` (`lo ≤ hi : ℚ`), covering chain `gridCovers`, Lipschitz margin
     `L ≥ 0`, strict target `target : ℚ`.
   - Positive rational witness `v : Fin n → ℚ` (`v i > 0`), rational spectral upper bound `lam : ℚ`,
     entrywise nonnegative matrix `M` -> `|μ| ≤ lam` via the `v`-weighted `ℓ^∞` norm.

4. **Section 4 (Exponential & Logarithmic Rational Bounds):**
   - Truncated Taylor sum `expTaylor n x := ∑_{m < n} x^m / m!` with remainder
     `x^n (n + 1) / (n! * n)` on `[0, 1]` (`n ≥ 1`), evaluated at `n = 4` for `x = 1/4, 1/2, 3/4`.
-/

public section

namespace PakPrimes.CogenticAnalyticToolkit

open Set Filter MeasureTheory

/-! ## Section 1: Elementary Van der Corput Oscillatory Integral Bounds -/

section VanDerCorput

private lemma continuousOn_of_hasDerivAt_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f f' : ℝ → E} (hf : ∀ θ ∈ Icc a b, HasDerivAt f (f' θ) θ) :
    ContinuousOn f (Icc a b) :=
  fun θ hθ => (hf θ hθ).continuousAt.continuousWithinAt

private lemma const_sign_of_abs_ge {a b lam : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hlam : 0 < lam)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_lb : ∀ θ ∈ Icc a b, lam ≤ |g θ|) :
    (∀ θ ∈ Icc a b, lam ≤ g θ) ∨ (∀ θ ∈ Icc a b, g θ ≤ -lam) := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hga : lam ≤ |g a| := hg_lb a ha
  rcases le_or_gt 0 (g a) with hga_pos | hga_neg
  · left
    intro θ hθ
    have hθ_lb := hg_lb θ hθ
    rcases le_or_gt 0 (g θ) with hθ_pos | hθ_neg
    · rwa [abs_of_nonneg hθ_pos] at hθ_lb
    · exfalso
      have hga_gt : 0 < g a := by linarith [abs_of_nonneg hga_pos]
      have h0_mem : (0 : ℝ) ∈ Icc (g θ) (g a) := ⟨le_of_lt hθ_neg, le_of_lt hga_gt⟩
      have hsub : Icc a θ ⊆ Icc a b := Icc_subset_Icc_right hθ.2
      have hcont' : ContinuousOn g (Icc a θ) := hg_cont.mono hsub
      have ⟨c, hc_mem, hgc⟩ := intermediate_value_Icc' hθ.1 hcont' h0_mem
      have hc_lb := hg_lb c (hsub hc_mem)
      rw [hgc, abs_zero] at hc_lb
      linarith
  · right
    intro θ hθ
    have hθ_lb := hg_lb θ hθ
    rcases le_or_gt 0 (g θ) with hθ_pos | hθ_neg
    · exfalso
      have hga_lt : g a < 0 := hga_neg
      have h0_mem : (0 : ℝ) ∈ Icc (g a) (g θ) := ⟨le_of_lt hga_lt, hθ_pos⟩
      have hsub : Icc a θ ⊆ Icc a b := Icc_subset_Icc_right hθ.2
      have hcont' : ContinuousOn g (Icc a θ) := hg_cont.mono hsub
      have ⟨c, hc_mem, hgc⟩ := intermediate_value_Icc hθ.1 hcont' h0_mem
      have hc_lb := hg_lb c (hsub hc_mem)
      rw [hgc, abs_zero] at hc_lb
      linarith
    · rw [abs_of_neg hθ_neg] at hθ_lb
      linarith

private lemma deriv_nonneg_of_monotoneOn {a b : ℝ} {g g' : ℝ → ℝ}
    (hab : a < b)
    (hg : ∀ θ ∈ Icc a b, HasDerivAt g (g' θ) θ)
    (hg'_cont : ContinuousOn g' (Icc a b))
    (hmono : MonotoneOn g (Icc a b)) :
    ∀ θ ∈ Icc a b, 0 ≤ g' θ := by
  have hIoo : ∀ θ ∈ Ioo a b, 0 ≤ g' θ := by
    intro θ hθ
    have hslope := (hg θ (Ioo_subset_Icc_self hθ)).tendsto_slope_zero_right
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), 0 ≤ t⁻¹ • (g (θ + t) - g θ) := by
      have hmem : Ioo 0 (b - θ) ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
        Ioo_mem_nhdsGT (sub_pos.mpr hθ.2)
      filter_upwards [hmem] with t ht
      have hθt : θ + t ∈ Icc a b := ⟨by linarith [hθ.1, ht.1], by linarith [ht.2]⟩
      have hle : g θ ≤ g (θ + t) := hmono (Ioo_subset_Icc_self hθ) hθt (by linarith [ht.1])
      rw [smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht.1)) (sub_nonneg.mpr hle)
    exact ge_of_tendsto hslope hev
  intro θ hθ
  have hcl : θ ∈ closure (Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
    exact hθ
  have hmem := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hlim : Tendsto g' (nhdsWithin θ (Ioo a b)) (nhds (g' θ)) :=
    (hg'_cont θ hθ).mono Ioo_subset_Icc_self
  have hev : ∀ᶠ t in nhdsWithin θ (Ioo a b), 0 ≤ g' t :=
    eventually_nhdsWithin_of_forall hIoo
  exact ge_of_tendsto hlim hev

private lemma deriv_nonpos_of_antitoneOn {a b : ℝ} {g g' : ℝ → ℝ}
    (hab : a < b)
    (hg : ∀ θ ∈ Icc a b, HasDerivAt g (g' θ) θ)
    (hg'_cont : ContinuousOn g' (Icc a b))
    (hanti : AntitoneOn g (Icc a b)) :
    ∀ θ ∈ Icc a b, g' θ ≤ 0 := by
  have hmono : MonotoneOn (fun θ => -g θ) (Icc a b) :=
    fun x hx y hy hxy => neg_le_neg (hanti hx hy hxy)
  have hneg : ∀ θ ∈ Icc a b, HasDerivAt (fun t => -g t) (-g' θ) θ :=
    fun θ hθ => (hg θ hθ).neg
  have hcont : ContinuousOn (fun θ => -g' θ) (Icc a b) := hg'_cont.neg
  intro θ hθ
  have h0 := deriv_nonneg_of_monotoneOn hab hneg hcont hmono θ hθ
  linarith

private lemma norm_exp_I_mul_ofReal (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

/-- **First-Derivative Oscillatory Integration-by-Parts Lemma** (Van der Corput, `k = 1`).
If `φ` is `C²` on `[a, b]` with `φ'` monotone and `|φ' θ| ≥ lam > 0` on `[a, b]`, and `a₀` is
`C¹` on `[a, b]` with `‖a₀ θ‖ ≤ M`, then integration by parts cancels one boundary contribution
against the variation of `1 / φ'`, giving the sharp constant `(2 / lam) * M + (1 / lam) * ∫ ‖a₀'‖`. -/
theorem oscillatory_integral_bound_first_deriv
    {a b lam M : ℝ} {φ : ℝ → ℝ} {a₀ : ℝ → ℂ}
    (hab : a ≤ b) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hφ : ∀ θ ∈ Icc a b, HasDerivAt φ (deriv φ θ) θ)
    (hφ' : ∀ θ ∈ Icc a b, HasDerivAt (deriv φ) (deriv (deriv φ) θ) θ)
    (hφ''_cont : ContinuousOn (deriv (deriv φ)) (Icc a b))
    (hφ'_mono : MonotoneOn (deriv φ) (Icc a b) ∨ AntitoneOn (deriv φ) (Icc a b))
    (hφ'_lb : ∀ θ ∈ Icc a b, lam ≤ |deriv φ θ|)
    (ha₀ : ∀ θ ∈ Icc a b, HasDerivAt a₀ (deriv a₀ θ) θ)
    (ha₀'_cont : ContinuousOn (deriv a₀) (Icc a b))
    (ha₀_bound : ∀ θ ∈ Icc a b, ‖a₀ θ‖ ≤ M) :
    ‖∫ θ in a..b, a₀ θ * Complex.exp (Complex.I * (φ θ : ℂ))‖ ≤
      (2 / lam) * M + (1 / lam) * ∫ θ in a..b, ‖deriv a₀ θ‖ := by
  rcases hab.eq_or_lt with rfl | hab_lt
  · simp only [intervalIntegral.integral_same, norm_zero, mul_zero, add_zero]
    positivity
  have hφ_cont : ContinuousOn φ (Icc a b) := continuousOn_of_hasDerivAt_Icc hφ
  have hφ'_cont : ContinuousOn (deriv φ) (Icc a b) := continuousOn_of_hasDerivAt_Icc hφ'
  have ha₀_cont : ContinuousOn a₀ (Icc a b) := continuousOn_of_hasDerivAt_Icc ha₀
  have hφ'_ne : ∀ θ ∈ Icc a b, deriv φ θ ≠ 0 := by
    intro θ hθ h0
    have h := hφ'_lb θ hθ
    rw [h0, abs_zero] at h
    linarith
  have hdenom_ne : ∀ θ ∈ Icc a b, Complex.I * Complex.ofReal (deriv φ θ) ≠ 0 := by
    intro θ hθ
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hφ'_ne θ hθ))
  let E : ℝ → ℂ := fun θ => Complex.exp (Complex.I * Complex.ofReal (φ θ))
  let g : ℝ → ℂ := fun θ => a₀ θ / (Complex.I * Complex.ofReal (deriv φ θ))
  let g' : ℝ → ℂ := fun θ =>
    deriv a₀ θ / (Complex.I * Complex.ofReal (deriv φ θ)) -
      a₀ θ * Complex.ofReal (deriv (deriv φ) θ) / (Complex.I * Complex.ofReal (deriv φ θ) ^ 2)
  have hE_cont : ContinuousOn E (Icc a b) := by
    refine Continuous.comp_continuousOn Complex.continuous_exp ?_
    exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ_cont)
  have hderiv_gE : ∀ θ ∈ uIcc a b, HasDerivAt (fun t => g t * E t) (g' θ * E θ + a₀ θ * E θ) θ := by
    intro θ hθ
    rw [uIcc_of_le hab] at hθ
    have h1 : HasDerivAt a₀ (deriv a₀ θ) θ := ha₀ θ hθ
    have h2 : HasDerivAt (fun t => Complex.I * Complex.ofReal (deriv φ t))
        (Complex.I * Complex.ofReal (deriv (deriv φ) θ)) θ :=
      ((hφ' θ hθ).ofReal_comp).const_mul Complex.I
    have hg_deriv : HasDerivAt g (g' θ) θ := by
      have hdiv := h1.div h2 (hdenom_ne θ hθ)
      refine hdiv.congr_deriv ?_
      have hne1 : Complex.I ≠ 0 := Complex.I_ne_zero
      have hne2 : Complex.ofReal (deriv φ θ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_ne θ hθ)
      dsimp [g']
      field_simp [hne1, hne2]
    have hE_deriv : HasDerivAt E (Complex.I * Complex.ofReal (deriv φ θ) * E θ) θ := by
      have hcomp := (((hφ θ hθ).ofReal_comp).const_mul Complex.I).cexp
      refine hcomp.congr_deriv ?_
      dsimp [E]
      ring
    have hmul := hg_deriv.mul hE_deriv
    refine hmul.congr_deriv ?_
    have hne1 : Complex.I ≠ 0 := Complex.I_ne_zero
    have hne2 : Complex.ofReal (deriv φ θ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_ne θ hθ)
    dsimp [g]
    field_simp [hne1, hne2]
  have hg'_cont : ContinuousOn g' (Icc a b) := by
    have hIφ'_cont : ContinuousOn (fun θ => Complex.I * Complex.ofReal (deriv φ θ)) (Icc a b) :=
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ'_cont)
    have hIφ'2_cont : ContinuousOn (fun θ => Complex.I * Complex.ofReal (deriv φ θ) ^ 2) (Icc a b) :=
      continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hφ'_cont).pow 2)
    have h1 : ContinuousOn (fun θ => deriv a₀ θ / (Complex.I * Complex.ofReal (deriv φ θ))) (Icc a b) :=
      ha₀'_cont.div hIφ'_cont hdenom_ne
    have h2 : ContinuousOn
        (fun θ => a₀ θ * Complex.ofReal (deriv (deriv φ) θ) / (Complex.I * Complex.ofReal (deriv φ θ) ^ 2)) (Icc a b) := by
      refine (ha₀_cont.mul (Complex.continuous_ofReal.comp_continuousOn hφ''_cont)).div
        hIφ'2_cont ?_
      intro θ hθ
      exact mul_ne_zero Complex.I_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hφ'_ne θ hθ)))
    exact h1.sub h2
  have hint_g'E : IntervalIntegrable (fun θ => g' θ * E θ) volume a b :=
    (hg'_cont.mul hE_cont).intervalIntegrable_of_Icc hab
  have hint_aE : IntervalIntegrable (fun θ => a₀ θ * E θ) volume a b :=
    (ha₀_cont.mul hE_cont).intervalIntegrable_of_Icc hab
  have hFTC : ∫ θ in a..b, (g' θ * E θ + a₀ θ * E θ) = g b * E b - g a * E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_gE (hint_g'E.add hint_aE)
  have hIBP : ∫ θ in a..b, a₀ θ * E θ = (g b * E b - g a * E a) - ∫ θ in a..b, g' θ * E θ := by
    rw [intervalIntegral.integral_add hint_g'E hint_aE] at hFTC
    exact eq_sub_of_add_eq' hFTC
  have hnorm_IBP :
      ‖∫ θ in a..b, a₀ θ * E θ‖ ≤
        ‖g b * E b‖ + ‖g a * E a‖ + ∫ θ in a..b, ‖g' θ * E θ‖ := by
    rw [hIBP]
    calc ‖(g b * E b - g a * E a) - ∫ θ in a..b, g' θ * E θ‖
        ≤ ‖g b * E b - g a * E a‖ + ‖∫ θ in a..b, g' θ * E θ‖ := norm_sub_le _ _
      _ ≤ (‖g b * E b‖ + ‖g a * E a‖) + ‖∫ θ in a..b, g' θ * E θ‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ ‖g b * E b‖ + ‖g a * E a‖ + ∫ θ in a..b, ‖g' θ * E θ‖ := by
          gcongr
          exact intervalIntegral.norm_integral_le_integral_norm hab
  have hnorm_gE : ∀ θ ∈ Icc a b, ‖g θ * E θ‖ ≤ M / |deriv φ θ| := by
    intro θ hθ
    have hE1 : ‖E θ‖ = 1 := norm_exp_I_mul_ofReal (φ θ)
    rw [norm_mul, hE1, mul_one]
    dsimp [g]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (ha₀_bound θ hθ) (abs_nonneg _)
  have hnorm_g'E : ∀ θ ∈ Icc a b,
      ‖g' θ * E θ‖ ≤ (1 / lam) * ‖deriv a₀ θ‖ + M * (|deriv (deriv φ) θ| / (deriv φ θ) ^ 2) := by
    intro θ hθ
    have hE1 : ‖E θ‖ = 1 := norm_exp_I_mul_ofReal (φ θ)
    rw [norm_mul, hE1, mul_one]
    dsimp [g']
    calc ‖deriv a₀ θ / (Complex.I * Complex.ofReal (deriv φ θ)) -
            a₀ θ * Complex.ofReal (deriv (deriv φ) θ) / (Complex.I * Complex.ofReal (deriv φ θ) ^ 2)‖
        ≤ ‖deriv a₀ θ / (Complex.I * Complex.ofReal (deriv φ θ))‖ +
            ‖a₀ θ * Complex.ofReal (deriv (deriv φ) θ) / (Complex.I * Complex.ofReal (deriv φ θ) ^ 2)‖ :=
          norm_sub_le _ _
      _ = ‖deriv a₀ θ‖ / |deriv φ θ| +
            ‖a₀ θ‖ * |deriv (deriv φ) θ| / (deriv φ θ) ^ 2 := by
          simp only [norm_div, norm_mul, norm_pow, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ (1 / lam) * ‖deriv a₀ θ‖ + M * (|deriv (deriv φ) θ| / (deriv φ θ) ^ 2) := by
          have h1 : ‖deriv a₀ θ‖ / |deriv φ θ| ≤ (1 / lam) * ‖deriv a₀ θ‖ := by
            rw [one_div, inv_mul_eq_div]
            exact div_le_div_of_nonneg_left (norm_nonneg _) hlam (hφ'_lb θ hθ)
          have h2 : ‖a₀ θ‖ * |deriv (deriv φ) θ| / (deriv φ θ) ^ 2 ≤
              M * (|deriv (deriv φ) θ| / (deriv φ θ) ^ 2) := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right (ha₀_bound θ hθ)
              (div_nonneg (abs_nonneg _) (sq_nonneg _))
          exact add_le_add h1 h2
  have hint_norm_g'E : IntervalIntegrable (fun θ => ‖g' θ * E θ‖) volume a b :=
    (hg'_cont.mul hE_cont).norm.intervalIntegrable_of_Icc hab
  have hint_norm_a₀' : IntervalIntegrable (fun θ => ‖deriv a₀ θ‖) volume a b :=
    ha₀'_cont.norm.intervalIntegrable_of_Icc hab
  have hint_var : IntervalIntegrable (fun θ => |deriv (deriv φ) θ| / (deriv φ θ) ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
    exact hφ''_cont.abs.div (hφ'_cont.pow 2) (fun θ hθ => pow_ne_zero 2 (hφ'_ne θ hθ))
  have hint_bound :
      ∫ θ in a..b, ‖g' θ * E θ‖ ≤
        (1 / lam) * (∫ θ in a..b, ‖deriv a₀ θ‖) +
          M * ∫ θ in a..b, |deriv (deriv φ) θ| / (deriv φ θ) ^ 2 := by
    have hle := intervalIntegral.integral_mono_on hab hint_norm_g'E
      ((hint_norm_a₀'.const_mul (1 / lam)).add (hint_var.const_mul M)) hnorm_g'E
    rw [intervalIntegral.integral_add (hint_norm_a₀'.const_mul _) (hint_var.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hle
    exact hle
  -- Fundamental Theorem of Calculus for `∫ φ'' / (φ')^2 = (φ' a)⁻¹ - (φ' b)⁻¹`.
  have hFTC_inv :
      ∫ θ in a..b, deriv (deriv φ) θ / (deriv φ θ) ^ 2 = (deriv φ a)⁻¹ - (deriv φ b)⁻¹ := by
    have hderiv_inv : ∀ θ ∈ uIcc a b,
        HasDerivAt (fun t => -(deriv φ t)⁻¹) (deriv (deriv φ) θ / (deriv φ θ) ^ 2) θ := by
      intro θ hθ
      rw [uIcc_of_le hab] at hθ
      have h := ((hφ' θ hθ).inv (hφ'_ne θ hθ)).neg
      refine h.congr_deriv ?_
      ring
    have hint_inv : IntervalIntegrable (fun θ => deriv (deriv φ) θ / (deriv φ θ) ^ 2) volume a b :=
      (hφ''_cont.div (hφ'_cont.pow 2) (fun θ hθ => pow_ne_zero 2 (hφ'_ne θ hθ))).intervalIntegrable_of_Icc hab
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_inv hint_inv
    linarith
  have hsign_φ' := const_sign_of_abs_ge hab hlam hφ'_cont hφ'_lb
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb_mem : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hM_comb :
      M / |deriv φ b| + M / |deriv φ a| +
          M * ∫ θ in a..b, |deriv (deriv φ) θ| / (deriv φ θ) ^ 2 ≤ (2 / lam) * M := by
    rcases hφ'_mono with hmono | hanti
    · have hφ''_nn : ∀ θ ∈ Icc a b, 0 ≤ deriv (deriv φ) θ :=
        deriv_nonneg_of_monotoneOn hab_lt hφ' hφ''_cont hmono
      have hvar_eq :
          ∫ θ in a..b, |deriv (deriv φ) θ| / (deriv φ θ) ^ 2 = (deriv φ a)⁻¹ - (deriv φ b)⁻¹ := by
        rw [← hFTC_inv]
        refine intervalIntegral.integral_congr (fun θ hθ => ?_)
        rw [uIcc_of_le hab] at hθ
        rw [abs_of_nonneg (hφ''_nn θ hθ)]
      rw [hvar_eq]
      rcases hsign_φ' with hpos | hneg
      · have hpa : lam ≤ deriv φ a := hpos a ha_mem
        have hpb : lam ≤ deriv φ b := hpos b hb_mem
        rw [abs_of_pos (lt_of_lt_of_le hlam hpa), abs_of_pos (lt_of_lt_of_le hlam hpb)]
        have hsimpl : M / deriv φ b + M / deriv φ a + M * ((deriv φ a)⁻¹ - (deriv φ b)⁻¹) =
            (2 / deriv φ a) * M := by ring
        rw [hsimpl]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hlam hpa) hM
      · have hna : deriv φ a ≤ -lam := hneg a ha_mem
        have hnb : deriv φ b ≤ -lam := hneg b hb_mem
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        have hsimpl : M / (-deriv φ b) + M / (-deriv φ a) + M * ((deriv φ a)⁻¹ - (deriv φ b)⁻¹) =
            (2 / (-deriv φ b)) * M := by ring
        rw [hsimpl]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hlam (by linarith)) hM
    · have hφ''_np : ∀ θ ∈ Icc a b, deriv (deriv φ) θ ≤ 0 :=
        deriv_nonpos_of_antitoneOn hab_lt hφ' hφ''_cont hanti
      have hvar_eq :
          ∫ θ in a..b, |deriv (deriv φ) θ| / (deriv φ θ) ^ 2 = (deriv φ b)⁻¹ - (deriv φ a)⁻¹ := by
        have hneg_int : ∫ θ in a..b, |deriv (deriv φ) θ| / (deriv φ θ) ^ 2 =
            -(∫ θ in a..b, deriv (deriv φ) θ / (deriv φ θ) ^ 2) := by
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr (fun θ hθ => ?_)
          rw [uIcc_of_le hab] at hθ
          rw [abs_of_nonpos (hφ''_np θ hθ), neg_div]
        rw [hneg_int, hFTC_inv]
        ring
      rw [hvar_eq]
      rcases hsign_φ' with hpos | hneg
      · have hpa : lam ≤ deriv φ a := hpos a ha_mem
        have hpb : lam ≤ deriv φ b := hpos b hb_mem
        rw [abs_of_pos (lt_of_lt_of_le hlam hpa), abs_of_pos (lt_of_lt_of_le hlam hpb)]
        have hsimpl : M / deriv φ b + M / deriv φ a + M * ((deriv φ b)⁻¹ - (deriv φ a)⁻¹) =
            (2 / deriv φ b) * M := by ring
        rw [hsimpl]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hlam hpb) hM
      · have hna : deriv φ a ≤ -lam := hneg a ha_mem
        have hnb : deriv φ b ≤ -lam := hneg b hb_mem
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        have hsimpl : M / (-deriv φ b) + M / (-deriv φ a) + M * ((deriv φ b)⁻¹ - (deriv φ a)⁻¹) =
            (2 / (-deriv φ a)) * M := by ring
        rw [hsimpl]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hlam (by linarith)) hM
  calc ‖∫ θ in a..b, a₀ θ * E θ‖
      ≤ ‖g b * E b‖ + ‖g a * E a‖ + ∫ θ in a..b, ‖g' θ * E θ‖ := hnorm_IBP
    _ ≤ M / |deriv φ b| + M / |deriv φ a| +
          ((1 / lam) * (∫ θ in a..b, ‖deriv a₀ θ‖) +
            M * ∫ θ in a..b, |deriv (deriv φ) θ| / (deriv φ θ) ^ 2) := by
        linarith [hnorm_gE b hb_mem, hnorm_gE a ha_mem, hint_bound]
    _ = (M / |deriv φ b| + M / |deriv φ a| +
          M * ∫ θ in a..b, |deriv (deriv φ) θ| / (deriv φ θ) ^ 2) +
          (1 / lam) * ∫ θ in a..b, ‖deriv a₀ θ‖ := by ring
    _ ≤ (2 / lam) * M + (1 / lam) * ∫ θ in a..b, ‖deriv a₀ θ‖ := by linarith

private lemma linear_lower_bound_of_deriv_ge {a b μ : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Icc a b, HasDerivAt g (g' θ) θ)
    (hg'_ge : ∀ θ ∈ Icc a b, μ ≤ g' θ) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → μ * (y - x) ≤ g y - g x := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · simp
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hcont : ContinuousOn g (Icc x y) := (continuousOn_of_hasDerivAt_Icc hg).mono hsub
  have hdiff : ∀ t ∈ Ioo x y, HasDerivAt g (g' t) t :=
    fun t ht => hg t (hsub (Ioo_subset_Icc_self ht))
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope g g' hlt hcont hdiff
  have hξ_ge : μ ≤ g' ξ := hg'_ge ξ (hsub (Ioo_subset_Icc_self hξ_mem))
  have hpos : 0 < y - x := sub_pos.mpr hlt
  rw [hξ_eq, le_div_iff₀ hpos] at hξ_ge
  exact hξ_ge

private lemma exists_center_abs_deriv_ge {a b μ : ℝ} {g g' : ℝ → ℝ}
    (hab : a ≤ b) (hμ : 0 < μ)
    (hg : ∀ θ ∈ Icc a b, HasDerivAt g (g' θ) θ)
    (hg'_cont : ContinuousOn g' (Icc a b))
    (hg'_lb : ∀ θ ∈ Icc a b, μ ≤ |g' θ|) :
    (MonotoneOn g (Icc a b) ∨ AntitoneOn g (Icc a b)) ∧
      ∃ c ∈ Icc a b, ∀ θ ∈ Icc a b, μ * |θ - c| ≤ |g θ| := by
  have hg_cont : ContinuousOn g (Icc a b) := continuousOn_of_hasDerivAt_Icc hg
  have hsign := const_sign_of_abs_ge hab hμ hg'_cont hg'_lb
  rcases hsign with hpos | hneg
  · have hlin := linear_lower_bound_of_deriv_ge hg hpos
    have hmono : MonotoneOn g (Icc a b) := by
      intro x hx y hy hxy
      have := hlin x hx y hy hxy
      have hnn : 0 ≤ μ * (y - x) := mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hxy)
      linarith
    refine ⟨Or.inl hmono, ?_⟩
    by_cases hga : 0 ≤ g a
    · refine ⟨a, left_mem_Icc.mpr hab, fun θ hθ => ?_⟩
      have h1 := hlin a (left_mem_Icc.mpr hab) θ hθ hθ.1
      have hgθ : 0 ≤ g θ := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hθ.1)]
      rw [abs_of_nonneg (sub_nonneg.mpr hθ.1), abs_of_nonneg hgθ]
      linarith
    · push Not at hga
      by_cases hgb : g b ≤ 0
      · refine ⟨b, right_mem_Icc.mpr hab, fun θ hθ => ?_⟩
        have h1 := hlin θ hθ b (right_mem_Icc.mpr hab) hθ.2
        have hgθ : g θ ≤ 0 := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hθ.2)]
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hθ.2), abs_of_nonpos hgθ]
        linarith
      · push Not at hgb
        have h0_mem : (0 : ℝ) ∈ Icc (g a) (g b) := ⟨le_of_lt hga, le_of_lt hgb⟩
        obtain ⟨c, hc_mem, hgc⟩ := intermediate_value_Icc hab hg_cont h0_mem
        refine ⟨c, hc_mem, fun θ hθ => ?_⟩
        rcases le_total c θ with hcθ | hθc
        · have h1 := hlin c hc_mem θ hθ hcθ
          rw [hgc, sub_zero] at h1
          have hgθ : 0 ≤ g θ := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hcθ)]
          rw [abs_of_nonneg (sub_nonneg.mpr hcθ), abs_of_nonneg hgθ]
          exact h1
        · have h1 := hlin θ hθ c hc_mem hθc
          rw [hgc, zero_sub] at h1
          have hgθ : g θ ≤ 0 := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hθc)]
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hθc), abs_of_nonpos hgθ]
          exact h1
  · have hneg' : ∀ θ ∈ Icc a b, μ ≤ -g' θ := fun θ hθ => by linarith [hneg θ hθ]
    have hg_neg : ∀ θ ∈ Icc a b, HasDerivAt (fun t => -g t) (-g' θ) θ :=
      fun θ hθ => (hg θ hθ).neg
    have hlin := linear_lower_bound_of_deriv_ge hg_neg hneg'
    have hanti : AntitoneOn g (Icc a b) := by
      intro x hx y hy hxy
      have := hlin x hx y hy hxy
      have hnn : 0 ≤ μ * (y - x) := mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hxy)
      linarith
    refine ⟨Or.inr hanti, ?_⟩
    by_cases hga : g a ≤ 0
    · refine ⟨a, left_mem_Icc.mpr hab, fun θ hθ => ?_⟩
      have h1 := hlin a (left_mem_Icc.mpr hab) θ hθ hθ.1
      have hgθ : g θ ≤ 0 := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hθ.1)]
      rw [abs_of_nonneg (sub_nonneg.mpr hθ.1), abs_of_nonpos hgθ]
      linarith
    · push Not at hga
      by_cases hgb : 0 ≤ g b
      · refine ⟨b, right_mem_Icc.mpr hab, fun θ hθ => ?_⟩
        have h1 := hlin θ hθ b (right_mem_Icc.mpr hab) hθ.2
        have hgθ : 0 ≤ g θ := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hθ.2)]
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hθ.2), abs_of_nonneg hgθ]
        linarith
      · push Not at hgb
        have h0_mem : (0 : ℝ) ∈ Icc (g b) (g a) := ⟨le_of_lt hgb, le_of_lt hga⟩
        obtain ⟨c, hc_mem, hgc⟩ := intermediate_value_Icc' hab hg_cont h0_mem
        refine ⟨c, hc_mem, fun θ hθ => ?_⟩
        rcases le_total c θ with hcθ | hθc
        · have h1 := hlin c hc_mem θ hθ hcθ
          rw [hgc, neg_zero, sub_zero] at h1
          have hgθ : g θ ≤ 0 := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hcθ)]
          rw [abs_of_nonneg (sub_nonneg.mpr hcθ), abs_of_nonpos hgθ]
          exact h1
        · have h1 := hlin θ hθ c hc_mem hθc
          rw [hgc, neg_zero, zero_sub, neg_neg] at h1
          have hgθ : 0 ≤ g θ := by linarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr hθc)]
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hθc), abs_of_nonneg hgθ]
          exact h1

/-- **Sharp Second-Derivative Van der Corput Oscillatory Integral Bound** (constant `6 / √μ`).
With excision half-width `δ = 1 / √μ`, the middle interval contributes at most `2 M / √μ` and
the two outer intervals together contribute at most `4 M / √μ + (1 / √μ) ∫ ‖deriv a₀‖`. -/
theorem van_der_corput_second_deriv_sharp
    {a b μ M : ℝ} {φ : ℝ → ℝ} {a₀ : ℝ → ℂ}
    (hab : a ≤ b) (hμ : 0 < μ) (hM : 0 ≤ M)
    (hφ : ∀ θ ∈ Icc a b, HasDerivAt φ (deriv φ θ) θ)
    (hφ' : ∀ θ ∈ Icc a b, HasDerivAt (deriv φ) (deriv (deriv φ) θ) θ)
    (hφ''_cont : ContinuousOn (deriv (deriv φ)) (Icc a b))
    (hφ''_lb : ∀ θ ∈ Icc a b, μ ≤ |deriv (deriv φ) θ|)
    (ha₀ : ∀ θ ∈ Icc a b, HasDerivAt a₀ (deriv a₀ θ) θ)
    (ha₀'_cont : ContinuousOn (deriv a₀) (Icc a b))
    (ha₀_bound : ∀ θ ∈ Icc a b, ‖a₀ θ‖ ≤ M) :
    ‖∫ θ in a..b, a₀ θ * Complex.exp (Complex.I * (φ θ : ℂ))‖ ≤
      (6 / Real.sqrt μ) * M + (1 / Real.sqrt μ) * ∫ θ in a..b, ‖deriv a₀ θ‖ := by
  obtain ⟨hmono, c, hc_mem, hc_lb⟩ :=
    exists_center_abs_deriv_ge hab hμ hφ' hφ''_cont hφ''_lb
  set s := Real.sqrt μ
  have hs : 0 < s := Real.sqrt_pos.mpr hμ
  set δ := 1 / s
  have hδ : 0 < δ := div_pos one_pos hs
  have hμδ : μ * δ = s := by
    dsimp [δ, s]
    rw [mul_one_div, Real.div_sqrt]
  set u := max a (c - δ)
  set v := min b (c + δ)
  have hau : a ≤ u := le_max_left _ _
  have huc : u ≤ c := max_le hc_mem.1 (by linarith)
  have hcv : c ≤ v := le_min hc_mem.2 (by linarith)
  have hvb : v ≤ b := min_le_left _ _
  have huv : u ≤ v := le_trans huc hcv
  have hsub_au : Icc a u ⊆ Icc a b := Icc_subset_Icc_right (le_trans huv hvb)
  have hsub_uv : Icc u v ⊆ Icc a b := Icc_subset_Icc hau hvb
  have hsub_vb : Icc v b ⊆ Icc a b := Icc_subset_Icc_left (le_trans hau huv)
  let F : ℝ → ℂ := fun θ => a₀ θ * Complex.exp (Complex.I * (φ θ : ℂ))
  have hF_cont : ContinuousOn F (Icc a b) := by
    refine (continuousOn_of_hasDerivAt_Icc ha₀).mul ?_
    refine Continuous.comp_continuousOn Complex.continuous_exp ?_
    exact continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_of_hasDerivAt_Icc hφ))
  have hint_au : IntervalIntegrable F volume a u :=
    (hF_cont.mono hsub_au).intervalIntegrable_of_Icc hau
  have hint_uv : IntervalIntegrable F volume u v :=
    (hF_cont.mono hsub_uv).intervalIntegrable_of_Icc huv
  have hint_vb : IntervalIntegrable F volume v b :=
    (hF_cont.mono hsub_vb).intervalIntegrable_of_Icc hvb
  have hsplit : ∫ θ in a..b, F θ =
      (∫ θ in a..u, F θ) + (∫ θ in u..v, F θ) + (∫ θ in v..b, F θ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint_au hint_uv,
      intervalIntegral.integral_add_adjacent_intervals (hint_au.trans hint_uv) hint_vb]
  have htri : ‖∫ θ in a..b, F θ‖ ≤
      ‖∫ θ in a..u, F θ‖ + ‖∫ θ in u..v, F θ‖ + ‖∫ θ in v..b, F θ‖ := by
    rw [hsplit]
    linarith [norm_add_le ((∫ θ in a..u, F θ) + ∫ θ in u..v, F θ) (∫ θ in v..b, F θ),
      norm_add_le (∫ θ in a..u, F θ) (∫ θ in u..v, F θ)]
  -- Middle piece `[u, v]`: trivial bound `2 * δ * M = (2 / √μ) * M`.
  have hmid : ‖∫ θ in u..v, F θ‖ ≤ (2 / s) * M := by
    have hbd : ∀ θ ∈ uIoc u v, ‖F θ‖ ≤ M := by
      intro θ hθ
      rw [uIoc_of_le huv] at hθ
      have hθ_ab : θ ∈ Icc a b := hsub_uv ⟨le_of_lt hθ.1, hθ.2⟩
      dsimp [F]
      rw [norm_mul, norm_exp_I_mul_ofReal, mul_one]
      exact ha₀_bound θ hθ_ab
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hlen : |v - u| ≤ 2 * δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr huv)]
      have hv_le : v ≤ c + δ := min_le_right _ _
      have hu_ge : c - δ ≤ u := le_max_right _ _
      linarith
    calc ‖∫ θ in u..v, F θ‖ ≤ M * |v - u| := h1
      _ ≤ M * (2 * δ) := mul_le_mul_of_nonneg_left hlen hM
      _ = (2 / s) * M := by dsimp [δ]; ring
  -- Left piece `[a, u]`: apply first-derivative bound with `lam = √μ`.
  have hleft : ‖∫ θ in a..u, F θ‖ ≤ (2 / s) * M + (1 / s) * ∫ θ in a..u, ‖deriv a₀ θ‖ := by
    rcases hau.eq_or_lt with hau_eq | hau_lt
    · rw [← hau_eq, intervalIntegral.integral_same, intervalIntegral.integral_same,
        norm_zero, mul_zero, add_zero]
      positivity
    · have hu_eq : u = c - δ := by
        dsimp [u] at hau_lt ⊢
        rcases le_total a (c - δ) with h | h
        · exact max_eq_right h
        · exfalso; rw [max_eq_left h] at hau_lt; exact lt_irrefl a hau_lt
      have hmono_au : MonotoneOn (deriv φ) (Icc a u) ∨ AntitoneOn (deriv φ) (Icc a u) :=
        hmono.imp (fun h => h.mono hsub_au) (fun h => h.mono hsub_au)
      have hlb_au : ∀ θ ∈ Icc a u, s ≤ |deriv φ θ| := by
        intro θ hθ
        have h1 := hc_lb θ (hsub_au hθ)
        have hdist : δ ≤ |θ - c| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hθ.2, huc])]
          linarith [hθ.2, hu_eq]
        calc s = μ * δ := hμδ.symm
          _ ≤ μ * |θ - c| := mul_le_mul_of_nonneg_left hdist (le_of_lt hμ)
          _ ≤ |deriv φ θ| := h1
      exact oscillatory_integral_bound_first_deriv hau hs hM
        (fun θ hθ => hφ θ (hsub_au hθ))
        (fun θ hθ => hφ' θ (hsub_au hθ))
        (hφ''_cont.mono hsub_au) hmono_au hlb_au
        (fun θ hθ => ha₀ θ (hsub_au hθ))
        (ha₀'_cont.mono hsub_au)
        (fun θ hθ => ha₀_bound θ (hsub_au hθ))
  -- Right piece `[v, b]`: apply first-derivative bound with `lam = √μ`.
  have hright : ‖∫ θ in v..b, F θ‖ ≤ (2 / s) * M + (1 / s) * ∫ θ in v..b, ‖deriv a₀ θ‖ := by
    rcases hvb.eq_or_lt with hvb_eq | hvb_lt
    · rw [hvb_eq, intervalIntegral.integral_same, intervalIntegral.integral_same,
        norm_zero, mul_zero, add_zero]
      positivity
    · have hv_eq : v = c + δ := by
        dsimp [v] at hvb_lt ⊢
        rcases le_total b (c + δ) with h | h
        · exfalso; rw [min_eq_left h] at hvb_lt; exact lt_irrefl b hvb_lt
        · exact min_eq_right h
      have hmono_vb : MonotoneOn (deriv φ) (Icc v b) ∨ AntitoneOn (deriv φ) (Icc v b) :=
        hmono.imp (fun h => h.mono hsub_vb) (fun h => h.mono hsub_vb)
      have hlb_vb : ∀ θ ∈ Icc v b, s ≤ |deriv φ θ| := by
        intro θ hθ
        have h1 := hc_lb θ (hsub_vb hθ)
        have hdist : δ ≤ |θ - c| := by
          rw [abs_of_nonneg (by linarith [hθ.1, hcv])]
          linarith [hθ.1, hv_eq]
        calc s = μ * δ := hμδ.symm
          _ ≤ μ * |θ - c| := mul_le_mul_of_nonneg_left hdist (le_of_lt hμ)
          _ ≤ |deriv φ θ| := h1
      exact oscillatory_integral_bound_first_deriv hvb hs hM
        (fun θ hθ => hφ θ (hsub_vb hθ))
        (fun θ hθ => hφ' θ (hsub_vb hθ))
        (hφ''_cont.mono hsub_vb) hmono_vb hlb_vb
        (fun θ hθ => ha₀ θ (hsub_vb hθ))
        (ha₀'_cont.mono hsub_vb)
        (fun θ hθ => ha₀_bound θ (hsub_vb hθ))
  -- Recombine derivative `L¹` norms: `∫_a^u + ∫_v^b ≤ ∫_a^b`.
  have hda_au : IntervalIntegrable (fun θ => ‖deriv a₀ θ‖) volume a u :=
    (ha₀'_cont.norm.mono hsub_au).intervalIntegrable_of_Icc hau
  have hda_uv : IntervalIntegrable (fun θ => ‖deriv a₀ θ‖) volume u v :=
    (ha₀'_cont.norm.mono hsub_uv).intervalIntegrable_of_Icc huv
  have hda_vb : IntervalIntegrable (fun θ => ‖deriv a₀ θ‖) volume v b :=
    (ha₀'_cont.norm.mono hsub_vb).intervalIntegrable_of_Icc hvb
  have hda_mid_nn : 0 ≤ ∫ θ in u..v, ‖deriv a₀ θ‖ :=
    intervalIntegral.integral_nonneg huv (fun _ _ => norm_nonneg _)
  have hda_sum :
      (∫ θ in a..u, ‖deriv a₀ θ‖) + (∫ θ in v..b, ‖deriv a₀ θ‖) ≤
        ∫ θ in a..b, ‖deriv a₀ θ‖ := by
    have heq : (∫ θ in a..u, ‖deriv a₀ θ‖) + (∫ θ in u..v, ‖deriv a₀ θ‖) +
        (∫ θ in v..b, ‖deriv a₀ θ‖) = ∫ θ in a..b, ‖deriv a₀ θ‖ := by
      rw [intervalIntegral.integral_add_adjacent_intervals hda_au hda_uv,
        intervalIntegral.integral_add_adjacent_intervals (hda_au.trans hda_uv) hda_vb]
    linarith
  have hda_scaled :
      (1 / s) * (∫ θ in a..u, ‖deriv a₀ θ‖) + (1 / s) * (∫ θ in v..b, ‖deriv a₀ θ‖) ≤
        (1 / s) * ∫ θ in a..b, ‖deriv a₀ θ‖ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hda_sum (div_nonneg zero_le_one (le_of_lt hs))
  calc ‖∫ θ in a..b, F θ‖
      ≤ ‖∫ θ in a..u, F θ‖ + ‖∫ θ in u..v, F θ‖ + ‖∫ θ in v..b, F θ‖ := htri
    _ ≤ ((2 / s) * M + (1 / s) * ∫ θ in a..u, ‖deriv a₀ θ‖) +
          (2 / s) * M +
          ((2 / s) * M + (1 / s) * ∫ θ in v..b, ‖deriv a₀ θ‖) := by linarith
    _ = (6 / s) * M +
          ((1 / s) * (∫ θ in a..u, ‖deriv a₀ θ‖) + (1 / s) * (∫ θ in v..b, ‖deriv a₀ θ‖)) := by
        ring
    _ ≤ (6 / s) * M + (1 / s) * ∫ θ in a..b, ‖deriv a₀ θ‖ := by linarith

/-- **Second-Derivative Van der Corput Oscillatory Integral Bound** (`edge_reconstruction.pdf`,
Lemma 4.1(2a)). Follows immediately from `van_der_corput_second_deriv_sharp` since `6 ≤ 8`. -/
theorem van_der_corput_second_deriv
    {a b μ M : ℝ} {φ : ℝ → ℝ} {a₀ : ℝ → ℂ}
    (hab : a ≤ b) (hμ : 0 < μ) (hM : 0 ≤ M)
    (hφ : ∀ θ ∈ Icc a b, HasDerivAt φ (deriv φ θ) θ)
    (hφ' : ∀ θ ∈ Icc a b, HasDerivAt (deriv φ) (deriv (deriv φ) θ) θ)
    (hφ''_cont : ContinuousOn (deriv (deriv φ)) (Icc a b))
    (hφ''_lb : ∀ θ ∈ Icc a b, μ ≤ |deriv (deriv φ) θ|)
    (ha₀ : ∀ θ ∈ Icc a b, HasDerivAt a₀ (deriv a₀ θ) θ)
    (ha₀'_cont : ContinuousOn (deriv a₀) (Icc a b))
    (ha₀_bound : ∀ θ ∈ Icc a b, ‖a₀ θ‖ ≤ M) :
    ‖∫ θ in a..b, a₀ θ * Complex.exp (Complex.I * (φ θ : ℂ))‖ ≤
      (8 / Real.sqrt μ) * M + (1 / Real.sqrt μ) * ∫ θ in a..b, ‖deriv a₀ θ‖ := by
  have hsharp := van_der_corput_second_deriv_sharp hab hμ hM hφ hφ' hφ''_cont hφ''_lb
    ha₀ ha₀'_cont ha₀_bound
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have h68 : (6 / Real.sqrt μ) * M ≤ (8 / Real.sqrt μ) * M :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) (le_of_lt hs)) hM
  linarith

end VanDerCorput

/-! ## Section 2: Multi-Scale Geometric Exponential Filter Bank & Spectral Dominance -/

section MultiScaleFilterBank

/-- Geometric decay rate `α_k = 64^{-k}` of the `k`-th exponential filter scale. -/
@[expose] noncomputable def decayRate (k : ℕ) : ℝ := (64 : ℝ) ^ (-(k : ℤ))

/-- Fourier symbol `H_k(ξ) = (1 + i ξ / α_k)⁻¹` of the `k`-th exponential filter. -/
@[expose] noncomputable def filterSymbol (k : ℕ) (ξ : ℝ) : ℂ :=
  (1 + Complex.I * ((ξ / decayRate k : ℝ) : ℂ))⁻¹

/-- Averaged Fourier symbol `H̄_K(ξ) = K⁻¹ ∑_{k < K} H_k(ξ)` of the `K`-scale filter bank. -/
@[expose] noncomputable def avgFilterSymbol (K : ℕ) (ξ : ℝ) : ℂ :=
  (K : ℂ)⁻¹ * ∑ k ∈ Finset.range K, filterSymbol k ξ

/-- Dissipative Plancherel symbol `Re(H̄_K(ξ)) - |H̄_K(ξ)|^2`. -/
@[expose] noncomputable def dissipativeSymbol (K : ℕ) (ξ : ℝ) : ℝ :=
  (avgFilterSymbol K ξ).re - Complex.normSq (avgFilterSymbol K ξ)

/-- Distance-to-boundary weight `min (k + 1) (K - k)` for scale `k` in a `K`-scale bank. -/
@[expose] def edgeWeight (K k : ℕ) : ℕ := min (k + 1) (K - k)

theorem decayRate_pos (k : ℕ) : 0 < decayRate k := by
  dsimp [decayRate]
  positivity

theorem decayRate_eq_inv_pow (k : ℕ) : decayRate k = ((64 : ℝ) ^ k)⁻¹ := by
  dsimp [decayRate]
  rw [zpow_neg, zpow_natCast]

theorem edgeWeight_pos {K k : ℕ} (hk : k < K) : 0 < edgeWeight K k := by
  dsimp [edgeWeight]
  exact lt_min (Nat.succ_pos k) (Nat.sub_pos_of_lt hk)

theorem edgeWeight_le_split_prod {K m : ℕ} (hm : m + 1 < K) :
    edgeWeight (K - 1) m * (K / 2) ≤ (m + 1) * (K - 1 - m) := by
  dsimp [edgeWeight]
  have hsum : (m + 1) + (K - 1 - m) = K := by omega
  rcases le_total (m + 1) (K - 1 - m) with hle | hge
  · rw [min_eq_left hle]
    have hbig : K / 2 ≤ K - 1 - m := by omega
    exact Nat.mul_le_mul_left (m + 1) hbig
  · rw [min_eq_right hge]
    have hbig : K / 2 ≤ m + 1 := by omega
    calc (K - 1 - m) * (K / 2) ≤ (K - 1 - m) * (m + 1) := Nat.mul_le_mul_left _ hbig
      _ = (m + 1) * (K - 1 - m) := Nat.mul_comm _ _

/-- Exact real part of `filterSymbol k ξ`: `1 / (1 + (ξ / α_k)^2)`. -/
theorem filterSymbol_re (k : ℕ) (ξ : ℝ) :
    (filterSymbol k ξ).re = 1 / (1 + (ξ / decayRate k) ^ 2) := by
  dsimp [filterSymbol]
  set t : ℝ := ξ / decayRate k
  have hre : (1 + Complex.I * (t : ℂ)).re = 1 := by simp
  have him : (1 + Complex.I * (t : ℂ)).im = t := by simp
  have hns : Complex.normSq (1 + Complex.I * (t : ℂ)) = 1 + t ^ 2 := by
    rw [Complex.normSq_apply, hre, him]
    ring
  rw [Complex.inv_re, hre, hns]

/-- Exact imaginary part of `filterSymbol k ξ`: `-(ξ / α_k) / (1 + (ξ / α_k)^2)`. -/
theorem filterSymbol_im (k : ℕ) (ξ : ℝ) :
    (filterSymbol k ξ).im = -(ξ / decayRate k) / (1 + (ξ / decayRate k) ^ 2) := by
  dsimp [filterSymbol]
  set t : ℝ := ξ / decayRate k
  have hre : (1 + Complex.I * (t : ℂ)).re = 1 := by simp
  have him : (1 + Complex.I * (t : ℂ)).im = t := by simp
  have hns : Complex.normSq (1 + Complex.I * (t : ℂ)) = 1 + t ^ 2 := by
    rw [Complex.normSq_apply, hre, him]
    ring
  rw [Complex.inv_im, him, hns]

private lemma avgFilterSymbol_re_eq (K : ℕ) (ξ : ℝ) :
    (avgFilterSymbol K ξ).re =
      (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, 1 / (1 + (ξ / decayRate k) ^ 2) := by
  dsimp [avgFilterSymbol]
  have hinv : ((K : ℂ)⁻¹) = (((K : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hinv, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => filterSymbol_re k ξ)

private lemma avgFilterSymbol_im_eq (K : ℕ) (ξ : ℝ) :
    (avgFilterSymbol K ξ).im =
      (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, -(ξ / decayRate k) / (1 + (ξ / decayRate k) ^ 2) := by
  dsimp [avgFilterSymbol]
  have hinv : ((K : ℂ)⁻¹) = (((K : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hinv, Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => filterSymbol_im k ξ)

/-- For every `K ≥ 1` and `ξ : ℝ`, `Re(H̄_K(ξ)) ∈ [0, 1]`. -/
theorem avgFilterSymbol_re_mem_Icc {K : ℕ} (hK : 1 ≤ K) (ξ : ℝ) :
    0 ≤ (avgFilterSymbol K ξ).re ∧ (avgFilterSymbol K ξ).re ≤ 1 := by
  rw [avgFilterSymbol_re_eq]
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  constructor
  · refine mul_nonneg (inv_nonneg.mpr (le_of_lt hKpos)) ?_
    exact Finset.sum_nonneg (fun k _ => by positivity)
  · have hsum_le : ∑ k ∈ Finset.range K, (1 : ℝ) / (1 + (ξ / decayRate k) ^ 2) ≤ (K : ℝ) := by
      calc ∑ k ∈ Finset.range K, (1 : ℝ) / (1 + (ξ / decayRate k) ^ 2)
          ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [div_le_one (by positivity)]
            linarith [sq_nonneg (ξ / decayRate k)]
        _ = (K : ℝ) := by simp
    calc (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, (1 : ℝ) / (1 + (ξ / decayRate k) ^ 2)
        ≤ (K : ℝ)⁻¹ * (K : ℝ) := mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (le_of_lt hKpos))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hKpos)

private lemma geom_sum_inv64_lt (m : ℕ) :
    ∑ j ∈ Finset.range m, ((64 : ℝ)⁻¹) ^ j ≤ 64 / 63 := by
  have hr : (64 : ℝ)⁻¹ ≠ 1 := by norm_num
  rw [geom_sum_eq hr]
  have hdiv : (((64 : ℝ)⁻¹) ^ m - 1) / ((64 : ℝ)⁻¹ - 1) = (64 / 63 : ℝ) * (1 - ((64 : ℝ)⁻¹) ^ m) := by
    ring
  rw [hdiv]
  have hpow : 0 ≤ ((64 : ℝ)⁻¹) ^ m := by positivity
  linarith

private lemma geom_sum_inv64_shift_lt (m : ℕ) :
    ∑ j ∈ Finset.range m, ((64 : ℝ)⁻¹) ^ (j + 1) ≤ 1 / 63 := by
  have hpull : ∑ j ∈ Finset.range m, ((64 : ℝ)⁻¹) ^ (j + 1) =
      (64 : ℝ)⁻¹ * ∑ j ∈ Finset.range m, ((64 : ℝ)⁻¹) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_succ']
  rw [hpull]
  have h := geom_sum_inv64_lt m
  linarith

private lemma lorentz_im_le_half (t : ℝ) : t / (1 + t ^ 2) ≤ 1 / 2 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg (t - 1)]

private lemma lorentz_im_le_self {t : ℝ} (ht : 0 ≤ t) : t / (1 + t ^ 2) ≤ t := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith [sq_nonneg t]

private lemma lorentz_im_le_inv {t : ℝ} (ht : 0 < t) : t / (1 + t ^ 2) ≤ t⁻¹ := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [inv_eq_one_div, div_le_div_iff₀ hpos ht]
  nlinarith

/-- Core multi-scale spectral dominance inequality, valid for ALL `K ≥ 1` and `ξ : ℝ`. -/
theorem multiscale_imag_sq_le_of_pos {K : ℕ} (hK : 1 ≤ K) (ξ : ℝ) :
    (avgFilterSymbol K ξ).im ^ 2 ≤
      (5 / (K : ℝ)) * (avgFilterSymbol K ξ).re * (1 - (avgFilterSymbol K ξ).re) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  let t : ℕ → ℝ := fun k => |ξ| * (64 : ℝ) ^ k
  have ht_eq : ∀ k, |ξ / decayRate k| = t k := by
    intro k
    rw [abs_div, abs_of_pos (decayRate_pos k), decayRate_eq_inv_pow, div_inv_eq_mul]
  have ht_sq : ∀ k, (ξ / decayRate k) ^ 2 = (t k) ^ 2 := by
    intro k
    rw [← sq_abs, ht_eq k]
  have ht_nn : ∀ k, 0 ≤ t k := fun k => by dsimp [t]; positivity
  let a : ℕ → ℝ := fun k => 1 / (1 + (t k) ^ 2)
  let b : ℕ → ℝ := fun k => (t k) ^ 2 / (1 + (t k) ^ 2)
  let c : ℕ → ℝ := fun k => t k / (1 + (t k) ^ 2)
  let A : ℝ := ∑ k ∈ Finset.range K, a k
  let B : ℝ := ∑ k ∈ Finset.range K, b k
  let C : ℝ := ∑ k ∈ Finset.range K, c k
  have hx_eq : (avgFilterSymbol K ξ).re = (K : ℝ)⁻¹ * A := by
    rw [avgFilterSymbol_re_eq]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    dsimp [a]
    rw [ht_sq k]
  have h1mx_eq : 1 - (avgFilterSymbol K ξ).re = (K : ℝ)⁻¹ * B := by
    rw [hx_eq]
    have hAB : A + B = (K : ℝ) := by
      dsimp [A, B, a, b]
      rw [← Finset.sum_add_distrib]
      have h1 : ∀ k, (1 : ℝ) / (1 + (t k) ^ 2) + (t k) ^ 2 / (1 + (t k) ^ 2) = 1 := by
        intro k
        have hpos : (1 : ℝ) + (t k) ^ 2 ≠ 0 := by positivity
        field_simp [hpos]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hK_mul : (K : ℝ)⁻¹ * (K : ℝ) = 1 := inv_mul_cancel₀ hKne
    nlinarith
  have hy_abs_le : |(avgFilterSymbol K ξ).im| ≤ (K : ℝ)⁻¹ * C := by
    rw [avgFilterSymbol_im_eq, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hKpos))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (le_of_lt hKpos))
    calc |∑ k ∈ Finset.range K, -(ξ / decayRate k) / (1 + (ξ / decayRate k) ^ 2)|
        ≤ ∑ k ∈ Finset.range K, |-(ξ / decayRate k) / (1 + (ξ / decayRate k) ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = C := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [abs_div, abs_neg, ht_eq k, ht_sq k, abs_of_pos (by positivity)]
  have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun k _ => div_nonneg (ht_nn k) (by positivity))
  have hkey : (K : ℝ) * C ^ 2 ≤ 5 * (A * B) := by
    -- Handle `ξ = 0` immediately.
    by_cases hξ0 : ξ = 0
    · have hC0 : C = 0 := by
        dsimp [C, c, t]
        simp [hξ0]
      have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun k _ => by dsimp [a]; positivity)
      have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun k _ => by dsimp [b]; positivity)
      rw [hC0]
      nlinarith
    have hξ_pos : 0 < |ξ| := abs_pos.mpr hξ0
    have ht_pos : ∀ k, 0 < t k := fun k => by dsimp [t]; positivity
    have ht_mono : ∀ {i j}, i ≤ j → t i ≤ t j := by
      intro i j hij
      dsimp [t]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) (le_of_lt hξ_pos)
    -- Case 1: All scales satisfy `t_k ≤ 1`.
    by_cases hcase1 : t (K - 1) ≤ 1
    · have hA_lb : (K : ℝ) / 2 ≤ A := by
        have hsum : ∑ _k ∈ Finset.range K, (1 / 2 : ℝ) ≤ A := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have htk1 : t k ≤ 1 := le_trans (ht_mono (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk))) hcase1
          have hsq : (t k) ^ 2 ≤ 1 := by nlinarith [ht_nn k]
          dsimp [a]
          rw [one_div, one_div]
          exact inv_anti₀ (by positivity) (by linarith)
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
        linarith
      have hB_lb : (t (K - 1)) ^ 2 / 2 ≤ B := by
        have hmem : K - 1 ∈ Finset.range K := Finset.mem_range.mpr (by omega)
        have hsingle : b (K - 1) ≤ B :=
          Finset.single_le_sum (fun k _ => by dsimp [b]; positivity) hmem
        have hsq : (t (K - 1)) ^ 2 ≤ 1 := by nlinarith [ht_nn (K - 1)]
        have hlb : (t (K - 1)) ^ 2 / 2 ≤ b (K - 1) := by
          dsimp [b]
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
        exact le_trans hlb hsingle
      have hC_ub : C ≤ (64 / 63) * t (K - 1) := by
        have h1 : C ≤ ∑ k ∈ Finset.range K, t (K - 1) * ((64 : ℝ)⁻¹) ^ (K - 1 - k) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk' : k ≤ K - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)
          have hck : c k ≤ t k := lorentz_im_le_self (ht_nn k)
          have htk_eq : t k = t (K - 1) * ((64 : ℝ)⁻¹) ^ (K - 1 - k) := by
            have hpow : (64 : ℝ) ^ k = (64 : ℝ) ^ (K - 1) * ((64 : ℝ)⁻¹) ^ (K - 1 - k) := by
              rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (by positivity), ← pow_add]
              congr 1
              omega
            dsimp [t]
            rw [mul_assoc, ← hpow]
          linarith
        have h2 : ∑ k ∈ Finset.range K, ((64 : ℝ)⁻¹) ^ (K - 1 - k) =
            ∑ j ∈ Finset.range K, ((64 : ℝ)⁻¹) ^ j := by
          rw [← Finset.sum_range_reflect (fun j => ((64 : ℝ)⁻¹) ^ j) K]
        rw [← Finset.mul_sum, h2] at h1
        calc C ≤ t (K - 1) * ∑ j ∈ Finset.range K, ((64 : ℝ)⁻¹) ^ j := h1
          _ ≤ t (K - 1) * (64 / 63) := mul_le_mul_of_nonneg_left (geom_sum_inv64_lt K) (ht_nn _)
          _ = (64 / 63) * t (K - 1) := mul_comm _ _
      have hC2 : C ^ 2 ≤ (64 / 63 : ℝ) ^ 2 * (t (K - 1)) ^ 2 := by
        nlinarith [hC_nn, ht_nn (K - 1)]
      have hAB : (K : ℝ) / 4 * (t (K - 1)) ^ 2 ≤ A * B := by
        have h := mul_le_mul hA_lb hB_lb (by positivity) (le_trans (by positivity) hA_lb)
        linarith
      nlinarith [sq_nonneg (t (K - 1)), hKpos]
    -- Case 2: All scales satisfy `1 ≤ t_k`.
    · push Not at hcase1
      by_cases hcase2 : 1 ≤ t 0
      · have hB_lb : (K : ℝ) / 2 ≤ B := by
          have hsum : ∑ _k ∈ Finset.range K, (1 / 2 : ℝ) ≤ B := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            have htk1 : 1 ≤ t k := le_trans hcase2 (ht_mono (Nat.zero_le k))
            have hsq : 1 ≤ (t k) ^ 2 := by nlinarith
            dsimp [b]
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            linarith
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
          linarith
        have hA_lb : (t 0)⁻¹ ^ 2 / 2 ≤ A := by
          have hmem : 0 ∈ Finset.range K := Finset.mem_range.mpr (by omega)
          have hsingle : a 0 ≤ A :=
            Finset.single_le_sum (fun k _ => by dsimp [a]; positivity) hmem
          have hsq : 1 ≤ (t 0) ^ 2 := by nlinarith
          have hlb : (t 0)⁻¹ ^ 2 / 2 ≤ a 0 := by
            dsimp [a]
            have hne : t 0 ≠ 0 := ne_of_gt (ht_pos 0)
            rw [inv_pow, div_eq_mul_inv, one_div, ← mul_inv,
              inv_le_inv₀ (by positivity) (by positivity)]
            linarith
          exact le_trans hlb hsingle
        have hC_ub : C ≤ (64 / 63) * (t 0)⁻¹ := by
          have h1 : C ≤ ∑ k ∈ Finset.range K, (t 0)⁻¹ * ((64 : ℝ)⁻¹) ^ k := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            have hck : c k ≤ (t k)⁻¹ := lorentz_im_le_inv (ht_pos k)
            have htk_inv : (t k)⁻¹ = (t 0)⁻¹ * ((64 : ℝ)⁻¹) ^ k := by
              dsimp [t]
              rw [pow_zero, mul_one, mul_inv, inv_pow, mul_comm]
            linarith
          rw [← Finset.mul_sum] at h1
          calc C ≤ (t 0)⁻¹ * ∑ k ∈ Finset.range K, ((64 : ℝ)⁻¹) ^ k := h1
            _ ≤ (t 0)⁻¹ * (64 / 63) :=
              mul_le_mul_of_nonneg_left (geom_sum_inv64_lt K) (inv_nonneg.mpr (ht_nn 0))
            _ = (64 / 63) * (t 0)⁻¹ := mul_comm _ _
        have hC2 : C ^ 2 ≤ (64 / 63 : ℝ) ^ 2 * (t 0)⁻¹ ^ 2 := by
          nlinarith [hC_nn, inv_nonneg.mpr (ht_nn 0)]
        have hAB : (K : ℝ) / 4 * (t 0)⁻¹ ^ 2 ≤ A * B := by
          have h := mul_le_mul hA_lb hB_lb (by positivity) (le_trans (by positivity) hA_lb)
          linarith
        nlinarith [sq_nonneg ((t 0)⁻¹), hKpos]
      -- Case 3: Transition lies strictly inside `{0, ..., K - 1}` (`t 0 < 1 < t (K - 1)`).
      · push Not at hcase2
        have hK2 : 2 ≤ K := by
          by_contra hlt
          have hK1 : K = 1 := by omega
          subst hK1
          simp only [Nat.sub_self] at hcase1
          linarith
        -- Pick the largest `m < K` with `t m ≤ 1`.
        let S : Finset ℕ := (Finset.range K).filter (fun k => t k ≤ 1)
        have h0S : 0 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_of_lt hcase2⟩
        have hSne : S.Nonempty := ⟨0, h0S⟩
        let m : ℕ := S.max' hSne
        have hmS : m ∈ S := Finset.max'_mem S hSne
        have hm_lt : m < K := Finset.mem_range.mp (Finset.mem_filter.mp hmS).1
        have htm_le : t m ≤ 1 := (Finset.mem_filter.mp hmS).2
        have hm_ne_last : m ≠ K - 1 := by
          intro hEq
          rw [hEq] at htm_le
          linarith
        have hm1_lt : m + 1 < K := by omega
        have htm1_gt : 1 < t (m + 1) := by
          by_contra hle
          push Not at hle
          have hm1S : m + 1 ∈ S :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm1_lt, hle⟩
          have := Finset.le_max' S (m + 1) hm1S
          omega
        -- Lower bound `A ≥ (m + 1) / 2`.
        have hA_lb : ((m + 1 : ℕ) : ℝ) / 2 ≤ A := by
          have hsub : Finset.range (m + 1) ⊆ Finset.range K :=
            Finset.range_mono (by omega)
          have h1 : ∑ k ∈ Finset.range (m + 1), a k ≤ A :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by dsimp [a]; positivity)
          have h2 : ∑ _k ∈ Finset.range (m + 1), (1 / 2 : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), a k := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have htk1 : t k ≤ 1 := le_trans (ht_mono hkm) htm_le
            have hsq : (t k) ^ 2 ≤ 1 := by nlinarith [ht_nn k]
            dsimp [a]
            rw [one_div, one_div]
            exact inv_anti₀ (by positivity) (by linarith)
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
          linarith
        -- Lower bound `B ≥ (K - 1 - m) / 2`.
        have hB_lb : ((K - 1 - m : ℕ) : ℝ) / 2 ≤ B := by
          have hsub : Finset.Ico (m + 1) K ⊆ Finset.range K := by
            intro k hk
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
          have h1 : ∑ k ∈ Finset.Ico (m + 1) K, b k ≤ B :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by dsimp [b]; positivity)
          have h2 : ∑ _k ∈ Finset.Ico (m + 1) K, (1 / 2 : ℝ) ≤ ∑ k ∈ Finset.Ico (m + 1) K, b k := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have hkm : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
            have htk1 : 1 ≤ t k := le_trans (le_of_lt htm1_gt) (ht_mono hkm)
            have hsq : 1 ≤ (t k) ^ 2 := by nlinarith
            dsimp [b]
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            linarith
          simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
          have hcard : K - (m + 1) = K - 1 - m := by omega
          rw [hcard] at h2
          linarith
        -- Product lower bound: `A * B ≥ (K - 1) / 4`.
        have hAB_lb : ((K : ℝ) - 1) / 4 ≤ A * B := by
          set p : ℝ := ((m + 1 : ℕ) : ℝ)
          set q : ℝ := ((K - 1 - m : ℕ) : ℝ)
          have hp1 : 1 ≤ p := by dsimp [p]; exact_mod_cast Nat.succ_pos m
          have hq1 : 1 ≤ q := by dsimp [q]; exact_mod_cast (show 1 ≤ K - 1 - m by omega)
          have hpq : p + q = (K : ℝ) := by
            dsimp [p, q]
            exact_mod_cast (show (m + 1) + (K - 1 - m) = K by omega)
          have hprod : (K : ℝ) - 1 ≤ p * q := by nlinarith
          have hmul := mul_le_mul hA_lb hB_lb (by positivity) (le_trans (by positivity) hA_lb)
          linarith
        -- Upper bound `C ≤ 2 / 3` by splitting into `k < m`, `{m, m + 1}`, and `k ≥ m + 2`.
        have hC_split : C = (∑ k ∈ Finset.range m, c k) + (c m + c (m + 1)) +
            (∑ k ∈ Finset.Ico (m + 2) K, c k) := by
          dsimp [C]
          have h1 : ∑ k ∈ Finset.range K, c k =
              (∑ k ∈ Finset.range (m + 2), c k) + ∑ k ∈ Finset.Ico (m + 2) K, c k := by
            rw [← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range]
            exact (Finset.sum_Ico_consecutive c (Nat.zero_le (m + 2)) (by omega)).symm
          rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
          ring
        have hC_left : ∑ k ∈ Finset.range m, c k ≤ 1 / 63 := by
          have h1 : ∑ k ∈ Finset.range m, c k ≤
              ∑ k ∈ Finset.range m, ((64 : ℝ)⁻¹) ^ (m - k) := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have hkm : k < m := Finset.mem_range.mp hk
            have hck : c k ≤ t k := lorentz_im_le_self (ht_nn k)
            have htk_eq : t k = t m * ((64 : ℝ)⁻¹) ^ (m - k) := by
              have hpow : (64 : ℝ) ^ k = (64 : ℝ) ^ m * ((64 : ℝ)⁻¹) ^ (m - k) := by
                rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (by positivity), ← pow_add]
                congr 1
                omega
              dsimp [t]
              rw [mul_assoc, ← hpow]
            have hle : t m * ((64 : ℝ)⁻¹) ^ (m - k) ≤ ((64 : ℝ)⁻¹) ^ (m - k) := by
              calc t m * ((64 : ℝ)⁻¹) ^ (m - k)
                  ≤ 1 * ((64 : ℝ)⁻¹) ^ (m - k) := mul_le_mul_of_nonneg_right htm_le (by positivity)
                _ = ((64 : ℝ)⁻¹) ^ (m - k) := one_mul _
            linarith
          have h2 : ∑ k ∈ Finset.range m, ((64 : ℝ)⁻¹) ^ (m - k) =
              ∑ j ∈ Finset.range m, ((64 : ℝ)⁻¹) ^ (j + 1) := by
            have href := Finset.sum_range_reflect (fun j => ((64 : ℝ)⁻¹) ^ (j + 1)) m
            rw [← href]
            refine Finset.sum_congr rfl (fun k hk => ?_)
            have hkm : k < m := Finset.mem_range.mp hk
            congr 1
            omega
          rw [h2] at h1
          exact le_trans h1 (geom_sum_inv64_shift_lt m)
        have hC_pair : c m + c (m + 1) ≤ 5 / 8 := by
          have htm1_eq : t (m + 1) = 64 * t m := by
            dsimp [t]
            rw [pow_succ]
            ring
          rcases le_total (t m) (1 / 8) with hle | hge
          · have hcm : c m ≤ 1 / 8 := le_trans (lorentz_im_le_self (ht_nn m)) hle
            have hcm1 : c (m + 1) ≤ 1 / 2 := lorentz_im_le_half (t (m + 1))
            linarith
          · have hcm : c m ≤ 1 / 2 := lorentz_im_le_half (t m)
            have hcm1 : c (m + 1) ≤ 1 / 8 := by
              have h1 := lorentz_im_le_inv (ht_pos (m + 1))
              have h8 : (8 : ℝ) ≤ t (m + 1) := by linarith
              have h2 : (t (m + 1))⁻¹ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h8
              linarith
            linarith
        have hC_right : ∑ k ∈ Finset.Ico (m + 2) K, c k ≤ 1 / 63 := by
          have h1 : ∑ k ∈ Finset.Ico (m + 2) K, c k ≤
              ∑ k ∈ Finset.Ico (m + 2) K, ((64 : ℝ)⁻¹) ^ (k - (m + 1)) := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have hk_ge : m + 2 ≤ k := (Finset.mem_Ico.mp hk).1
            have hck : c k ≤ (t k)⁻¹ := lorentz_im_le_inv (ht_pos k)
            have htk_eq : t k = t (m + 1) * (64 : ℝ) ^ (k - (m + 1)) := by
              dsimp [t]
              rw [mul_assoc, ← pow_add]
              congr 2
              omega
            have htk_ge : (64 : ℝ) ^ (k - (m + 1)) ≤ t k := by
              rw [htk_eq]
              have hpow_pos : (0 : ℝ) < (64 : ℝ) ^ (k - (m + 1)) := by positivity
              nlinarith
            have hinv_le : (t k)⁻¹ ≤ ((64 : ℝ)⁻¹) ^ (k - (m + 1)) := by
              rw [inv_pow]
              exact inv_anti₀ (by positivity) htk_ge
            linarith
          have h2 : ∑ k ∈ Finset.Ico (m + 2) K, ((64 : ℝ)⁻¹) ^ (k - (m + 1)) =
              ∑ j ∈ Finset.range (K - (m + 2)), ((64 : ℝ)⁻¹) ^ (j + 1) := by
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            congr 1
            omega
          rw [h2] at h1
          exact le_trans h1 (geom_sum_inv64_shift_lt (K - (m + 2)))
        have hC_ub : C ≤ 2 / 3 := by linarith
        have hC2 : C ^ 2 ≤ 4 / 9 := by nlinarith [hC_nn]
        have hK2_real : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
        nlinarith [hKpos, hAB_lb, hC2]
  -- Convert `K * C^2 ≤ 5 * (A * B)` back to `y^2 ≤ (5 / K) * x * (1 - x)`.
  rw [h1mx_eq, hx_eq]
  have hy2 : (avgFilterSymbol K ξ).im ^ 2 ≤ ((K : ℝ)⁻¹ * C) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (avgFilterSymbol K ξ).im, hy_abs_le]
  have hscale : ((K : ℝ)⁻¹ * C) ^ 2 ≤ (5 / (K : ℝ)) * ((K : ℝ)⁻¹ * A) * ((K : ℝ)⁻¹ * B) := by
    have hKinv3 : (0 : ℝ) < (K : ℝ)⁻¹ ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hkey (le_of_lt hKinv3)
    have hlhs : (K : ℝ)⁻¹ ^ 3 * ((K : ℝ) * C ^ 2) = ((K : ℝ)⁻¹ * C) ^ 2 := by
      field_simp [hKne]
    have hrhs : (K : ℝ)⁻¹ ^ 3 * (5 * (A * B)) =
        (5 / (K : ℝ)) * ((K : ℝ)⁻¹ * A) * ((K : ℝ)⁻¹ * B) := by
      field_simp [hKne]
    linarith
  exact le_trans hy2 hscale

/-- **Imaginary-Part Spectral Dominance** (`bimatrix_nash_equilibrium.pdf`, Lemma 3.1):
for all `K ≥ 10` and `ξ : ℝ`, `Im(H̄_K(ξ))^2 ≤ (5 / K) Re(H̄_K(ξ)) (1 - Re(H̄_K(ξ)))`. -/
theorem multiscale_imag_sq_le {K : ℕ} (hK : 10 ≤ K) (ξ : ℝ) :
    (avgFilterSymbol K ξ).im ^ 2 ≤
      (5 / (K : ℝ)) * (avgFilterSymbol K ξ).re * (1 - (avgFilterSymbol K ξ).re) :=
  multiscale_imag_sq_le_of_pos (by omega) ξ

/-- **Dissipative Symbol Lower Bound** (`bimatrix_nash_equilibrium.pdf`, Lemma 3.1):
for all `K ≥ 10` and `ξ : ℝ`,
`dissipativeSymbol K ξ ≥ (1 - 5 / K) x (1 - x) ≥ (1 / 2) x (1 - x) ≥ 0`. -/
theorem multiscale_dissipative_lower_bound {K : ℕ} (hK : 10 ≤ K) (ξ : ℝ) :
    (1 - 5 / (K : ℝ)) * (avgFilterSymbol K ξ).re * (1 - (avgFilterSymbol K ξ).re) ≤
        dissipativeSymbol K ξ ∧
      (1 / 2 : ℝ) * (avgFilterSymbol K ξ).re * (1 - (avgFilterSymbol K ξ).re) ≤
        (1 - 5 / (K : ℝ)) * (avgFilterSymbol K ξ).re * (1 - (avgFilterSymbol K ξ).re) ∧
      0 ≤ (1 / 2 : ℝ) * (avgFilterSymbol K ξ).re * (1 - (avgFilterSymbol K ξ).re) := by
  set x := (avgFilterSymbol K ξ).re
  set y := (avgFilterSymbol K ξ).im
  have hx : 0 ≤ x ∧ x ≤ 1 := avgFilterSymbol_re_mem_Icc (by omega) ξ
  have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have him := multiscale_imag_sq_le hK ξ
  have hdiss : dissipativeSymbol K ξ = x * (1 - x) - y ^ 2 := by
    dsimp [dissipativeSymbol, x, y]
    rw [Complex.normSq_apply]
    ring
  have hK10 : (10 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hhalf : (1 / 2 : ℝ) ≤ 1 - 5 / (K : ℝ) := by
    have h5 : 5 / (K : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiss]
    linarith
  · have h := mul_le_mul_of_nonneg_right hhalf hxx
    linarith
  · linarith

/-- **Antisymmetric-vs-Dissipative Plancherel Bound** (`bimatrix_nash_equilibrium.pdf`, Lemma 3.1):
for all `K ≥ 10` and `ξ : ℝ`, `4 * Im(H̄_K(ξ))^2 ≤ (40 / K) * dissipativeSymbol K ξ`. -/
theorem multiscale_antisymmetric_bound {K : ℕ} (hK : 10 ≤ K) (ξ : ℝ) :
    4 * (avgFilterSymbol K ξ).im ^ 2 ≤ (40 / (K : ℝ)) * dissipativeSymbol K ξ := by
  set x := (avgFilterSymbol K ξ).re
  have him := multiscale_imag_sq_le hK ξ
  have ⟨hd1, hd2, _⟩ := multiscale_dissipative_lower_bound hK ξ
  have hd : (1 / 2 : ℝ) * x * (1 - x) ≤ dissipativeSymbol K ξ := le_trans hd2 hd1
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have h40_nn : (0 : ℝ) ≤ 40 / (K : ℝ) := by positivity
  calc 4 * (avgFilterSymbol K ξ).im ^ 2
      ≤ 4 * ((5 / (K : ℝ)) * x * (1 - x)) := by linarith
    _ = (40 / (K : ℝ)) * ((1 / 2 : ℝ) * x * (1 - x)) := by ring
    _ ≤ (40 / (K : ℝ)) * dissipativeSymbol K ξ := mul_le_mul_of_nonneg_left hd h40_nn

/-- **Master Multi-Scale Spectral Dominance Theorem** bundling all three Lemma 3.1 bounds
for `K ≥ 10` and every frequency `ξ : ℝ`. -/
theorem multiscale_filter_spectral_dominance {K : ℕ} (hK : 10 ≤ K) (ξ : ℝ) :
    let x := (avgFilterSymbol K ξ).re
    let y := (avgFilterSymbol K ξ).im
    (0 ≤ x ∧ x ≤ 1) ∧
      y ^ 2 ≤ (5 / (K : ℝ)) * x * (1 - x) ∧
      (1 / 2 : ℝ) * x * (1 - x) ≤ dissipativeSymbol K ξ ∧
      4 * y ^ 2 ≤ (40 / (K : ℝ)) * dissipativeSymbol K ξ := by
  dsimp only
  have ⟨hd1, hd2, _⟩ := multiscale_dissipative_lower_bound hK ξ
  exact ⟨avgFilterSymbol_re_mem_Icc (by omega) ξ,
    multiscale_imag_sq_le hK ξ,
    le_trans hd2 hd1,
    multiscale_antisymmetric_bound hK ξ⟩

end MultiScaleFilterBank

/-! ## Section 3: Exact Rational Interval & Grid Certificate Combinators + Collatz–Wielandt -/

section RationalCertificates

/-- A closed rational interval `[lo, hi]` with kernel-verified endpoint ordering `lo ≤ hi`. -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
  hle : lo ≤ hi
  deriving DecidableEq, Repr

/-- Membership of a real number `x` in the closed rational interval `I`. -/
@[expose] def memRatInterval (I : RatInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- Decidable adjacency-chain coverage predicate from rational endpoint `a` to `b`. -/
@[expose] def gridCoversFrom (a b : ℚ) : List RatInterval → Prop
  | [] => False
  | [I] => I.lo ≤ a ∧ b ≤ I.hi
  | I :: J :: rest => I.lo ≤ a ∧ gridCoversFrom I.hi b (J :: rest)

instance instDecidableGridCoversFrom (a b : ℚ) : (grid : List RatInterval) →
    Decidable (gridCoversFrom a b grid)
  | [] => isFalse id
  | [_I] => instDecidableAnd
  | I :: J :: rest =>
    letI := instDecidableGridCoversFrom I.hi b (J :: rest)
    instDecidableAnd

/-- Decidable predicate certifying that a finite list of rational intervals covers `I₀`. -/
@[expose] def gridCovers (I₀ : RatInterval) (grid : List RatInterval) : Prop :=
  gridCoversFrom I₀.lo I₀.hi grid

instance instDecidableGridCovers (I₀ : RatInterval) (grid : List RatInterval) :
    Decidable (gridCovers I₀ grid) :=
  instDecidableGridCoversFrom I₀.lo I₀.hi grid

private lemma mem_of_gridCoversFrom {a b : ℚ} {grid : List RatInterval}
    (hcov : gridCoversFrom a b grid) {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    ∃ I ∈ grid, memRatInterval I x := by
  induction grid generalizing a with
  | nil => exact False.elim hcov
  | cons I rest ih =>
    cases rest with
    | nil =>
      rcases hcov with ⟨hlo, hhi⟩
      refine ⟨I, List.mem_cons_self, ?_, ?_⟩
      · exact le_trans (by exact_mod_cast hlo) ha
      · exact le_trans hb (by exact_mod_cast hhi)
    | cons J tail =>
      rcases hcov with ⟨hlo, hrest⟩
      rcases le_total x (I.hi : ℝ) with hle | hge
      · exact ⟨I, List.mem_cons_self, le_trans (by exact_mod_cast hlo) ha, hle⟩
      · obtain ⟨K, hKmem, hKx⟩ := ih hrest hge
        exact ⟨K, List.mem_cons_of_mem I hKmem, hKx⟩

/-- Any point `x ∈ I₀` lies in at least one subinterval of any covering rational grid. -/
theorem mem_of_gridCovers {I₀ : RatInterval} {grid : List RatInterval}
    (hcov : gridCovers I₀ grid) {x : ℝ} (hx : memRatInterval I₀ x) :
    ∃ I ∈ grid, memRatInterval I x :=
  mem_of_gridCoversFrom hcov hx.1 hx.2

/-- **Lipschitz / Margin Grid Certificate Combinator**:
if `grid` covers `I₀`, and on each subinterval `I ∈ grid` the function `f` satisfies
`f x ≤ u I + L * (I.hi - I.lo)` with rational check `u I + L * (I.hi - I.lo) < target`,
then `f x < target` on all of `I₀`. -/
theorem certify_on_grid {I₀ : RatInterval} {grid : List RatInterval}
    {f : ℝ → ℝ} (u : RatInterval → ℚ) (L target : ℚ)
    (hcov : gridCovers I₀ grid)
    (hlocal : ∀ I ∈ grid, ∀ x, memRatInterval I x →
      f x ≤ (u I : ℝ) + (L : ℝ) * ((I.hi : ℝ) - (I.lo : ℝ)))
    (hcheck : ∀ I ∈ grid, u I + L * (I.hi - I.lo) < target) :
    ∀ x, memRatInterval I₀ x → f x < (target : ℝ) := by
  intro x hx
  obtain ⟨I, hImem, hIx⟩ := mem_of_gridCovers hcov hx
  have h1 := hlocal I hImem x hIx
  have h2 : (u I : ℝ) + (L : ℝ) * ((I.hi : ℝ) - (I.lo : ℝ)) < (target : ℝ) := by
    exact_mod_cast hcheck I hImem
  exact lt_of_le_of_lt h1 h2

/-- **Exact Rational Grid Certificate Combinator** (zero-margin special case `L = 0`). -/
theorem certify_on_grid_exact {I₀ : RatInterval} {grid : List RatInterval}
    {f : ℝ → ℝ} (u : RatInterval → ℚ) (target : ℚ)
    (hcov : gridCovers I₀ grid)
    (hlocal : ∀ I ∈ grid, ∀ x, memRatInterval I x → f x ≤ (u I : ℝ))
    (hcheck : ∀ I ∈ grid, u I < target) :
    ∀ x, memRatInterval I₀ x → f x < (target : ℝ) := by
  refine certify_on_grid u 0 target hcov ?_ ?_
  · intro I hI x hx
    simpa using hlocal I hI x hx
  · intro I hI
    simpa using hcheck I hI

/-- Purely computable boolean certificate checker for a list of `(interval, upper_bound)` pairs. -/
@[expose] def checkGridCert (I₀ : RatInterval) (cells : List (RatInterval × ℚ))
    (L target : ℚ) : Bool :=
  decide (gridCovers I₀ (cells.map Prod.fst)) &&
    cells.all (fun p => decide (p.2 + L * (p.1.hi - p.1.lo) < target))

/-- Soundness of the computable boolean grid certificate checker `checkGridCert` (checked purely
in the Lean kernel via `decide` / `rfl`). -/
theorem certify_on_grid_of_check {I₀ : RatInterval} {cells : List (RatInterval × ℚ)}
    {f : ℝ → ℝ} {L target : ℚ}
    (hcert : checkGridCert I₀ cells L target = true)
    (hlocal : ∀ p ∈ cells, ∀ x, memRatInterval p.1 x →
      f x ≤ (p.2 : ℝ) + (L : ℝ) * ((p.1.hi : ℝ) - (p.1.lo : ℝ))) :
    ∀ x, memRatInterval I₀ x → f x < (target : ℝ) := by
  dsimp [checkGridCert] at hcert
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcert
  rcases hcert with ⟨hcov, hall⟩
  intro x hx
  obtain ⟨I, hImem, hIx⟩ := mem_of_gridCovers hcov hx
  rw [List.mem_map] at hImem
  obtain ⟨p, hpmem, rfl⟩ := hImem
  have h1 := hlocal p hpmem x hIx
  have h2q : p.2 + L * (p.1.hi - p.1.lo) < target := of_decide_eq_true (hall p hpmem)
  have h2 : (p.2 : ℝ) + (L : ℝ) * ((p.1.hi : ℝ) - (p.1.lo : ℝ)) < (target : ℝ) := by
    exact_mod_cast h2q
  exact lt_of_le_of_lt h1 h2

/-- Construct a uniform `n`-cell rational grid subdividing `I₀`. -/
@[expose] def uniformGrid (I₀ : RatInterval) (n : ℕ) (_hn : 0 < n) : List RatInterval :=
  let h : ℚ := (I₀.hi - I₀.lo) / (n : ℚ)
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr I₀.hle) (by exact_mod_cast Nat.zero_le n)
  (List.range n).map fun (k : ℕ) =>
    { lo := I₀.lo + (k : ℚ) * h
      hi := I₀.lo + ((k + 1 : ℕ) : ℚ) * h
      hle := by
        have hstep : (k : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_succ k
        linarith [mul_le_mul_of_nonneg_right hstep hh] }

private lemma gridCoversFrom_uniform_aux (a h : ℚ) (hh : 0 ≤ h) :
    ∀ m (k : ℕ), 0 < m →
      gridCoversFrom (a + (k : ℚ) * h) (a + ((k + m : ℕ) : ℚ) * h)
        ((List.range m).map fun (j : ℕ) =>
          { lo := a + ((k + j : ℕ) : ℚ) * h
            hi := a + ((k + j + 1 : ℕ) : ℚ) * h
            hle := by
              have hstep : ((k + j : ℕ) : ℚ) ≤ ((k + j + 1 : ℕ) : ℚ) := by
                exact_mod_cast Nat.le_succ (k + j)
              linarith [mul_le_mul_of_nonneg_right hstep hh] }) := by
  intro m
  induction m with
  | zero => intro _ hm; exact absurd hm (lt_irrefl 0)
  | succ m ih =>
    intro k _
    cases m with
    | zero =>
      simp [gridCoversFrom]
    | succ m' =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hcons :
          ((List.range (m' + 1)).map
            ((fun (j : ℕ) =>
              ({ lo := a + ((k + j : ℕ) : ℚ) * h
                 hi := a + ((k + j + 1 : ℕ) : ℚ) * h
                 hle := by
                   have hstep : ((k + j : ℕ) : ℚ) ≤ ((k + j + 1 : ℕ) : ℚ) := by
                     exact_mod_cast Nat.le_succ (k + j)
                   linarith [mul_le_mul_of_nonneg_right hstep hh] } : RatInterval)) ∘
              Nat.succ)) =
          ((List.range (m' + 1)).map fun (j : ℕ) =>
            { lo := a + ((k + 1 + j : ℕ) : ℚ) * h
              hi := a + ((k + 1 + j + 1 : ℕ) : ℚ) * h
              hle := by
                have hstep : ((k + 1 + j : ℕ) : ℚ) ≤ ((k + 1 + j + 1 : ℕ) : ℚ) := by
                  exact_mod_cast Nat.le_succ (k + 1 + j)
                linarith [mul_le_mul_of_nonneg_right hstep hh] }) := by
        refine List.map_congr_left (fun j _ => ?_)
        simp only [Function.comp_apply, RatInterval.mk.injEq]
        constructor <;> congr 2 <;> norm_cast <;> omega
      rw [hcons]
      have hne : ((List.range (m' + 1)).map fun (j : ℕ) =>
            ({ lo := a + ((k + 1 + j : ℕ) : ℚ) * h
               hi := a + ((k + 1 + j + 1 : ℕ) : ℚ) * h
               hle := by
                 have hstep : ((k + 1 + j : ℕ) : ℚ) ≤ ((k + 1 + j + 1 : ℕ) : ℚ) := by
                   exact_mod_cast Nat.le_succ (k + 1 + j)
                 linarith [mul_le_mul_of_nonneg_right hstep hh] } : RatInterval)) ≠ [] := by
        simp
      have hrec := ih (k + 1) (Nat.succ_pos m')
      have hkm : k + (m' + 1 + 1) = k + 1 + (m' + 1) := by omega
      rw [hkm]
      cases hL : ((List.range (m' + 1)).map fun (j : ℕ) =>
            ({ lo := a + ((k + 1 + j : ℕ) : ℚ) * h
               hi := a + ((k + 1 + j + 1 : ℕ) : ℚ) * h
               hle := by
                 have hstep : ((k + 1 + j : ℕ) : ℚ) ≤ ((k + 1 + j + 1 : ℕ) : ℚ) := by
                   exact_mod_cast Nat.le_succ (k + 1 + j)
                 linarith [mul_le_mul_of_nonneg_right hstep hh] } : RatInterval)) with
      | nil => exact absurd hL hne
      | cons J rest =>
        rw [hL] at hrec
        dsimp [gridCoversFrom]
        refine ⟨by simp, ?_⟩
        simpa [Nat.add_zero] using hrec

/-- Every uniform `n`-cell rational grid covers `I₀`. -/
theorem gridCovers_uniformGrid (I₀ : RatInterval) (n : ℕ) (hn : 0 < n) :
    gridCovers I₀ (uniformGrid I₀ n hn) := by
  dsimp [gridCovers, uniformGrid]
  set h : ℚ := (I₀.hi - I₀.lo) / (n : ℚ)
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr I₀.hle) (by exact_mod_cast Nat.zero_le n)
  have haux := gridCoversFrom_uniform_aux I₀.lo h hh n 0 hn
  have hlo : I₀.lo + ((0 : ℕ) : ℚ) * h = I₀.lo := by simp
  have hhi : I₀.lo + ((0 + n : ℕ) : ℚ) * h = I₀.hi := by
    have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    dsimp [h]
    simp [mul_div_cancel₀ _ hn_ne]
  rw [hlo, hhi] at haux
  convert haux using 2
  funext j
  simp [h]

/-- **Collatz–Wielandt Rational Perron Spectral Bound** (real eigenvalues):
for any entrywise nonnegative `n × n` real matrix `M`, positive rational witness `v : Fin n → ℚ`,
and rational upper bound `lam : ℚ` satisfying `M v ≤ lam • v` entrywise, EVERY real eigenvalue `μ`
with a nonzero eigenvector `x` (not even requiring nonnegativity of `x`) satisfies `|μ| ≤ lam`. -/
theorem collatz_wielandt_rat_upper_bound {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℚ) (lam : ℚ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hv : ∀ i, (0 : ℚ) < v i)
    (hcert : ∀ i, ∑ j, M i j * (v j : ℝ) ≤ (lam : ℝ) * (v i : ℝ))
    {μ : ℝ} {x : Fin n → ℝ} (hx : x ≠ 0) (heig : M.mulVec x = μ • x) :
    |μ| ≤ (lam : ℝ) := by
  have hex : ∃ k : Fin n, x k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx (funext hall)
  obtain ⟨k₀, hk₀⟩ := hex
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨k₀, Finset.mem_univ k₀⟩
  let r : Fin n → ℝ := fun i => |x i| / (v i : ℝ)
  obtain ⟨i₀, _, hi₀_max⟩ := Finset.exists_max_image Finset.univ r huniv
  have hv_pos : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hR_pos : 0 < r i₀ := by
    have hk₀_pos : 0 < r k₀ := div_pos (abs_pos.mpr hk₀) (hv_pos k₀)
    exact lt_of_lt_of_le hk₀_pos (hi₀_max k₀ (Finset.mem_univ k₀))
  have hx_bound : ∀ j : Fin n, |x j| ≤ r i₀ * (v j : ℝ) := by
    intro j
    have hj := hi₀_max j (Finset.mem_univ j)
    dsimp [r] at hj
    exact (div_le_iff₀ (hv_pos j)).mp hj
  have hrow : ∑ j, M i₀ j * x j = μ * x i₀ := by
    have := congr_fun heig i₀
    simpa [Matrix.mulVec, dotProduct] using this
  have hxi₀_eq : |x i₀| = r i₀ * (v i₀ : ℝ) := by
    dsimp [r]
    exact (div_mul_cancel₀ _ (ne_of_gt (hv_pos i₀))).symm
  have hxi₀_pos : 0 < |x i₀| := by
    rw [hxi₀_eq]
    exact mul_pos hR_pos (hv_pos i₀)
  have hchain : |μ| * |x i₀| ≤ (lam : ℝ) * |x i₀| := by
    calc |μ| * |x i₀|
        = |μ * x i₀| := (abs_mul μ (x i₀)).symm
      _ = |∑ j, M i₀ j * x j| := by rw [hrow]
      _ ≤ ∑ j, |M i₀ j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, M i₀ j * |x j| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (hM i₀ j)]
      _ ≤ ∑ j, M i₀ j * (r i₀ * (v j : ℝ)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left (hx_bound j) (hM i₀ j)
      _ = r i₀ * ∑ j, M i₀ j * (v j : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ r i₀ * ((lam : ℝ) * (v i₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left (hcert i₀) (le_of_lt hR_pos)
      _ = (lam : ℝ) * (r i₀ * (v i₀ : ℝ)) := by ring
      _ = (lam : ℝ) * |x i₀| := by rw [← hxi₀_eq]
  exact le_of_mul_le_mul_right hchain hxi₀_pos

/-- **Collatz–Wielandt Rational Perron Spectral Bound** (complex eigenvalues):
the identical `v`-weighted `ℓ^∞` certificate bounds `‖μ‖ ≤ lam` for every complex eigenvalue `μ`
of a nonnegative real matrix `M`. -/
theorem collatz_wielandt_rat_upper_bound_complex {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℚ) (lam : ℚ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hv : ∀ i, (0 : ℚ) < v i)
    (hcert : ∀ i, ∑ j, M i j * (v j : ℝ) ≤ (lam : ℝ) * (v i : ℝ))
    {μ : ℂ} {x : Fin n → ℂ} (hx : x ≠ 0)
    (heig : ∀ i, ∑ j, (M i j : ℂ) * x j = μ * x i) :
    ‖μ‖ ≤ (lam : ℝ) := by
  have hex : ∃ k : Fin n, x k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx (funext hall)
  obtain ⟨k₀, hk₀⟩ := hex
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨k₀, Finset.mem_univ k₀⟩
  let r : Fin n → ℝ := fun i => ‖x i‖ / (v i : ℝ)
  obtain ⟨i₀, _, hi₀_max⟩ := Finset.exists_max_image Finset.univ r huniv
  have hv_pos : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hR_pos : 0 < r i₀ := by
    have hk₀_pos : 0 < r k₀ := div_pos (norm_pos_iff.mpr hk₀) (hv_pos k₀)
    exact lt_of_lt_of_le hk₀_pos (hi₀_max k₀ (Finset.mem_univ k₀))
  have hx_bound : ∀ j : Fin n, ‖x j‖ ≤ r i₀ * (v j : ℝ) := by
    intro j
    have hj := hi₀_max j (Finset.mem_univ j)
    dsimp [r] at hj
    exact (div_le_iff₀ (hv_pos j)).mp hj
  have hxi₀_eq : ‖x i₀‖ = r i₀ * (v i₀ : ℝ) := by
    dsimp [r]
    exact (div_mul_cancel₀ _ (ne_of_gt (hv_pos i₀))).symm
  have hxi₀_pos : 0 < ‖x i₀‖ := by
    rw [hxi₀_eq]
    exact mul_pos hR_pos (hv_pos i₀)
  have hchain : ‖μ‖ * ‖x i₀‖ ≤ (lam : ℝ) * ‖x i₀‖ := by
    calc ‖μ‖ * ‖x i₀‖
        = ‖μ * x i₀‖ := (norm_mul μ (x i₀)).symm
      _ = ‖∑ j, (M i₀ j : ℂ) * x j‖ := by rw [heig i₀]
      _ ≤ ∑ j, ‖(M i₀ j : ℂ) * x j‖ := norm_sum_le _ _
      _ = ∑ j, M i₀ j * ‖x j‖ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hM i₀ j)]
      _ ≤ ∑ j, M i₀ j * (r i₀ * (v j : ℝ)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left (hx_bound j) (hM i₀ j)
      _ = r i₀ * ∑ j, M i₀ j * (v j : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ r i₀ * ((lam : ℝ) * (v i₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left (hcert i₀) (le_of_lt hR_pos)
      _ = (lam : ℝ) * (r i₀ * (v i₀ : ℝ)) := by ring
      _ = (lam : ℝ) * ‖x i₀‖ := by rw [← hxi₀_eq]
  exact le_of_mul_le_mul_right hchain hxi₀_pos

private def finArgMaxAux {n : ℕ} (f : Fin (n + 1) → ℚ) :
    ∀ k : ℕ, k ≤ n → Fin (n + 1)
  | 0, _ => ⟨0, Nat.succ_pos n⟩
  | k + 1, hk =>
    let best := finArgMaxAux f k (Nat.le_of_succ_le hk)
    let cur : Fin (n + 1) := ⟨k + 1, Nat.lt_succ_of_le hk⟩
    if f best ≤ f cur then cur else best

private lemma finArgMaxAux_spec {n : ℕ} (f : Fin (n + 1) → ℚ) :
    ∀ (k : ℕ) (hk : k ≤ n) (j : Fin (n + 1)), j.val ≤ k → f j ≤ f (finArgMaxAux f k hk)
  | 0, _, j, hj => by
    have hj0 : j = ⟨0, Nat.succ_pos n⟩ := Fin.ext (Nat.eq_zero_of_le_zero hj)
    rw [hj0]
    exact le_rfl
  | k + 1, hk, j, hj => by
    dsimp [finArgMaxAux]
    set best := finArgMaxAux f k (Nat.le_of_succ_le hk)
    set cur : Fin (n + 1) := ⟨k + 1, Nat.lt_succ_of_le hk⟩
    by_cases hle : f best ≤ f cur
    · simp only [hle, ↓reduceIte]
      rcases Nat.eq_or_lt_of_le hj with hjeq | hjlt
      · have : j = cur := Fin.ext hjeq
        rw [this]
      · exact le_trans (finArgMaxAux_spec f k (Nat.le_of_succ_le hk) j (Nat.lt_succ_iff.mp hjlt)) hle
    · simp only [hle, ↓reduceIte]
      rcases Nat.eq_or_lt_of_le hj with hjeq | hjlt
      · have : j = cur := Fin.ext hjeq
        rw [this]
        exact le_of_not_ge hle
      · exact finArgMaxAux_spec f k (Nat.le_of_succ_le hk) j (Nat.lt_succ_iff.mp hjlt)

/-- **Purely Algebraic / Constructive Rational Collatz–Wielandt Bound** (explicit index Witness
over `ℚ`, avoiding `Classical.choice`). -/
theorem collatz_wielandt_rat_pure {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (v : Fin (n + 1) → ℚ) (lam : ℚ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hv : ∀ i, 0 < v i)
    (hcert : ∀ i, ∑ j, M i j * v j ≤ lam * v i)
    {μ : ℚ} {x : Fin (n + 1) → ℚ} (k₀ : Fin (n + 1)) (hk₀ : x k₀ ≠ 0)
    (heig : ∀ i, ∑ j, M i j * x j = μ * x i) :
    |μ| ≤ lam := by
  let r : Fin (n + 1) → ℚ := fun i => |x i| / v i
  let i₀ : Fin (n + 1) := finArgMaxAux r n le_rfl
  have hi₀_max : ∀ j : Fin (n + 1), r j ≤ r i₀ :=
    fun j => finArgMaxAux_spec r n le_rfl j (Nat.le_of_lt_succ j.isLt)
  have hR_pos : 0 < r i₀ := by
    have hk₀_pos : 0 < r k₀ := div_pos (abs_pos.mpr hk₀) (hv k₀)
    exact lt_of_lt_of_le hk₀_pos (hi₀_max k₀)
  have hx_bound : ∀ j : Fin (n + 1), |x j| ≤ r i₀ * v j :=
    fun j => (div_le_iff₀ (hv j)).mp (hi₀_max j)
  have hxi₀_eq : |x i₀| = r i₀ * v i₀ :=
    (div_mul_cancel₀ _ (ne_of_gt (hv i₀))).symm
  have hxi₀_pos : 0 < |x i₀| := by
    rw [hxi₀_eq]
    exact mul_pos hR_pos (hv i₀)
  have hchain : |μ| * |x i₀| ≤ lam * |x i₀| := by
    calc |μ| * |x i₀|
        = |μ * x i₀| := (abs_mul μ (x i₀)).symm
      _ = |∑ j, M i₀ j * x j| := by rw [heig i₀]
      _ ≤ ∑ j, |M i₀ j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, M i₀ j * |x j| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (hM i₀ j)]
      _ ≤ ∑ j, M i₀ j * (r i₀ * v j) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left (hx_bound j) (hM i₀ j)
      _ = r i₀ * ∑ j, M i₀ j * v j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ r i₀ * (lam * v i₀) := mul_le_mul_of_nonneg_left (hcert i₀) (le_of_lt hR_pos)
      _ = lam * (r i₀ * v i₀) := by ring
      _ = lam * |x i₀| := by rw [← hxi₀_eq]
  exact le_of_mul_le_mul_right hchain hxi₀_pos

end RationalCertificates

/-! ## Section 4: Elementary Taylor / Exponential & Logarithmic Rational Bounds -/

section ElementaryBounds

/-- Truncated exponential Taylor sum `∑_{m < n} x^m / m!`. -/
@[expose] noncomputable def expTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)

/-- Lower Taylor sandwich for `Real.exp x` when `x ≥ 0`. -/
theorem exp_taylor_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    expTaylor n x ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx n

/-- Upper Taylor-plus-remainder sandwich for `Real.exp x` on `[0, 1]` (`n ≥ 1`). -/
theorem exp_le_taylor_add_rem {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp x ≤ expTaylor n x + x ^ n * ((n : ℝ) + 1) / ((n.factorial : ℝ) * (n : ℝ)) :=
  Real.exp_bound' hx0 hx1 hn

/-- Rational upper bound `exp(1 / 4) < 31 / 24` (`edge_reconstruction.pdf`, p. 22). -/
theorem exp_quarter_lt : Real.exp (1 / 4 : ℝ) < 31 / 24 := by
  have h := exp_le_taylor_add_rem (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  dsimp [expTaylor] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Rational lower bound `493 / 384 ≤ exp(1 / 4)`. -/
theorem exp_quarter_gt : (493 / 384 : ℝ) ≤ Real.exp (1 / 4 : ℝ) := by
  have h := exp_taylor_le_exp (x := (1 / 4 : ℝ)) (by norm_num) 4
  dsimp [expTaylor] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Rational upper bound `exp(1 / 2) < 5 / 3`. -/
theorem exp_half_lt : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
  have h := exp_le_taylor_add_rem (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  dsimp [expTaylor] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Rational upper bound `log 2 < 1`. -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := exp_taylor_le_exp (x := (1 : ℝ)) (by norm_num) 3
  dsimp [expTaylor] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Rational lower bound `1 / 2 < log 2`. -/
theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [exp_half_lt]

/-- Sharper rational upper bound `log 2 < 3 / 4`. -/
theorem log_two_lt_three_quarters : Real.log 2 < 3 / 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := exp_taylor_le_exp (x := (3 / 4 : ℝ)) (by norm_num) 4
  dsimp [expTaylor] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Rational upper bound `log 3 < 2`. -/
theorem log_three_lt_two : Real.log 3 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have h := exp_taylor_le_exp (x := (1 : ℝ)) (by norm_num) 3
    dsimp [expTaylor] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [h2]
  nlinarith

end ElementaryBounds

end PakPrimes.CogenticAnalyticToolkit
