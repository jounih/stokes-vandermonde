module

public import PakPrimes.BranchPointStokes
public import PakPrimes.FalseThetaDichotomy
public import PakPrimes.QuasipolynomialEulerParity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp

/-! # Unconditional Differential Transcendence of the Fishburn Series & All Torus Knots `T(p, q)`

End-to-end Tier-1 Lean 4 formalization (fully proved, strictly
`[propext, Classical.choice, Quot.sound]`) resolving:

1. **General Half-Integer Abel-Convolution → `BranchPointStokesData` Engine (`abelConv`,
   `abelConv_branchPointStokesData`, `eulerSeries_algebraicIndependent_of_meromorphicBorel`)**:
   Converts ANY positive-ray simple-pole meromorphic Borel kernel `ψ` (`MeromorphicBorelData ψ ω res`)
   via the smooth Abel-convolution transform
   `A_ψ(z) = (2 z / π) ∫_0^{π/2} sin²φ · ψ(z sin²φ) dφ`
   into a genuine `α = 1/2` branch-point Stokes comb (`BranchPointStokesData (formalSeries A_ψ) (1/2) ω c`)
   with `c_m = 2 i √(π ω_m) r_m ≠ 0`, proving unconditional differential transcendence over `ℂ(t)`
   of the formal Gevrey-1 Euler series `E_ψ(t) = ∑_k ((2k+1)! / (2^{2k+1} (k!)²)) ψ^{(k)}(0) t^k`.
2. **All Torus Knots `T(p, q)` (`gcd(p, q) = 1`, `p, q ≥ 2`)**:
   Constructs the exact Hikami / Lawrence–Zagier generating kernel `sin(p s) sin(q s) / sin(p q s)`,
   its removable-singularity-cleared Borel transform `torusKnotBorel p q` with genuine simple poles
   at `(π n / (2 p q))²` for all `n ≥ 1` with `p ∤ n` and `q ∤ n`, and proves unconditional
   differential transcendence over `ℂ(t)` of BOTH `torusKnotEulerSeries p q` and the alternating
   perturbative WRT series `torusKnotPerturbativeSeries p q` for ALL coprime `p, q ≥ 2`, with
   explicit specializations to Trefoil / Fishburn `T(2, 3)`, Cinquefoil `T(2, 5)`, `T(3, 4)`, `T(3, 5)`.
3. **Bostan–Di Vizio–Raschel Open Problem (AJM §2.2.6) — Literal Fishburn Formal Power Series**:
   Defines the literal divergent Fishburn OGF `P(x) = ∑_{m ≥ 0} ∏_{j=1}^m (1 - (1 - x)^j) ∈ ℂ[[x]]`,
   proves the pure-algebra differential-transcendence transfer along Zagier's substitution
   `x = 1 - exp(-24 t)`, proves Zagier's formal identity `P(1 - exp(-24 t)) = exp(t) * E(t)`
   unconditionally via Zagier's two-variable `q`-difference identity and shifted Euler–Maclaurin,
   and concludes `AlgebraicIndependent ℂ (seriesCoordinates fishburnSeries)`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.FishburnTorusKnots

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
  PakPrimes.BranchPointStokes PakPrimes.MockThetaAndHurwitz PakPrimes.FalseThetaDichotomy
  PakPrimes.PrimeNome PakPrimes.QuasipolynomialEulerParity
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Wallis Sine-Power Integral & Smooth Half-Integer Abel Convolution (`abelConv`) -/

/-- Exact Wallis even sine-power integral:
`(2 / π) ∫_0^{π/2} sin^{2k+2}(φ) dφ = (2k+1)! / (2^{2k+1} · k! · (k+1)!)`. -/
lemma wallis_sin_even_integral (k : ℕ) :
    (2 / Real.pi) * (∫ φ in (0 : ℝ)..(Real.pi / 2), Real.sin φ ^ (2 * k + 2)) =
      ((2 * k + 1).factorial : ℝ) /
        ((2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  induction k with
  | zero =>
    have h2 := integral_sin_pow (a := (0 : ℝ)) (b := Real.pi / 2) 0
    simp only [Nat.cast_zero, zero_add, pow_zero, pow_one, Real.sin_zero, Real.cos_pi_div_two,
      mul_zero, zero_mul, sub_zero, zero_div, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, mul_one] at h2
    rw [h2]
    norm_num
    field_simp [hpi]
  | succ k ih =>
    have hstep := integral_sin_pow (a := (0 : ℝ)) (b := Real.pi / 2) (2 * k + 2)
    have hsin0 : Real.sin 0 ^ (2 * k + 2 + 1) = 0 := by
      rw [Real.sin_zero, zero_pow (by omega)]
    have hcos_pi : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    rw [hsin0, hcos_pi, zero_mul, mul_zero, sub_self, zero_div, zero_add] at hstep
    rw [show 2 * (k + 1) + 2 = 2 * k + 2 + 2 by omega, hstep]
    rw [mul_left_comm (2 / Real.pi), ih]
    have hfac1 : (2 * (k + 1) + 1).factorial = (2 * k + 3) * ((2 * k + 2) * (2 * k + 1).factorial) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    have hfac2 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
    have hfac3 : (k + 1 + 1).factorial = (k + 2) * (k + 1).factorial := Nat.factorial_succ (k + 1)
    rw [hfac1, hfac3, show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
    push_cast
    have hf0 : (k.factorial : ℝ) ≠ 0 := by positivity
    have hf1 : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
    have h2p : (2 : ℝ) ^ (2 * k + 1) ≠ 0 := by positivity
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    have h2k4 : ((2 * k + 2 : ℕ) : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hf0, hf1, h2p, hk2, h2k4]
    rw [hfac2]
    push_cast
    ring

/-- Smooth half-integer Abel convolution transform of a Borel kernel `ψ`:
`abelConv ψ z = (2 z / π) ∫_0^{π/2} sin²φ · ψ(z · sin²φ) dφ`.
Its Taylor coefficients multiply `ψ^{(k)}(0)` by `(2k+1)! / (2^{2k+1} (k!)²)`. -/
@[expose] def abelConv (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((2 / Real.pi : ℝ) : ℂ) * z *
    ∫ φ in (0 : ℝ)..(Real.pi / 2), ((Real.sin φ ^ 2 : ℝ) : ℂ) * ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z)

/-- Auxiliary smooth kernel `abelConvCore ψ z = (2 / π) ∫_0^{π/2} sin²φ · ψ(z · sin²φ) dφ`,
satisfying `abelConv ψ z = z * abelConvCore ψ z`. -/
private def abelConvCore (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((2 / Real.pi : ℝ) : ℂ) *
    ∫ φ in (0 : ℝ)..(Real.pi / 2), ((Real.sin φ ^ 2 : ℝ) : ℂ) * ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z)

private lemma abelConv_eq_mul_core (ψ : ℂ → ℂ) (z : ℂ) :
    abelConv ψ z = z * abelConvCore ψ z := by
  unfold abelConv abelConvCore; ring

private lemma abelConvCore_hasDerivAt_gen {U : Set ℂ} (hU : Domain U)
    {ψ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ U) (m : ℕ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    HasDerivAt
      (fun z : ℂ => ((2 / Real.pi : ℝ) : ℂ) *
        ∫ φ in (0 : ℝ)..(Real.pi / 2),
          ((Real.sin φ ^ (2 * m + 2) : ℝ) : ℂ) * iteratedDeriv m ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z))
      (((2 / Real.pi : ℝ) : ℂ) *
        ∫ φ in (0 : ℝ)..(Real.pi / 2),
          ((Real.sin φ ^ (2 * (m + 1) + 2) : ℝ) : ℂ) *
            iteratedDeriv (m + 1) ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z₀))
      z₀ := by
  have hψm : AnalyticOnNhd ℂ (iteratedDeriv m ψ) U := by
    clear hz₀
    induction m generalizing ψ with
    | zero => simpa using hψ
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ']
      exact ih hψ.deriv z hz
  have hψm1 : AnalyticOnNhd ℂ (iteratedDeriv (m + 1) ψ) U := by
    intro z hz; rw [iteratedDeriv_succ]; exact hψm.deriv z hz
  let F : ℂ → ℝ → ℂ := fun z φ =>
    ((Real.sin φ ^ (2 * m + 2) : ℝ) : ℂ) * iteratedDeriv m ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z)
  let F' : ℂ → ℝ → ℂ := fun z φ =>
    ((Real.sin φ ^ (2 * (m + 1) + 2) : ℝ) : ℂ) * iteratedDeriv (m + 1) ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z)
  let S : Set (ℂ × ℝ) := U ×ˢ Icc (0 : ℝ) (Real.pi / 2)
  have hmap_cont : Continuous (fun p : ℂ × ℝ => ((Real.sin p.2 ^ 2 : ℝ) : ℂ) * p.1) :=
    (Complex.continuous_ofReal.comp ((Real.continuous_sin.comp continuous_snd).pow 2)).mul continuous_fst
  have hm_maps : MapsTo (fun p : ℂ × ℝ => ((Real.sin p.2 ^ 2 : ℝ) : ℂ) * p.1) S U := fun p hp =>
    hU.star p.1 hp.1 (Real.sin p.2 ^ 2) ⟨sq_nonneg _, Real.sin_sq_le_one p.2⟩
  have hF_cont : ContinuousOn F.uncurry S :=
    (Complex.continuous_ofReal.comp ((Real.continuous_sin.comp continuous_snd).pow (2 * m + 2))).continuousOn.mul
      (hψm.continuousOn.comp hmap_cont.continuousOn hm_maps)
  have hF'_cont : ContinuousOn F'.uncurry S :=
    (Complex.continuous_ofReal.comp
      ((Real.continuous_sin.comp continuous_snd).pow (2 * (m + 1) + 2))).continuousOn.mul
      (hψm1.continuousOn.comp hmap_cont.continuousOn hm_maps)
  have hderivAt : ∀ (z : ℂ), z ∈ U → ∀ (φ : ℝ), φ ∈ Icc (0 : ℝ) (Real.pi / 2) →
      HasDerivAt (F · φ) (F' z φ) z := fun z hz φ _ => by
    have hmemU : ((Real.sin φ ^ 2 : ℝ) : ℂ) * z ∈ U :=
      hU.star z hz (Real.sin φ ^ 2) ⟨sq_nonneg _, Real.sin_sq_le_one φ⟩
    have hd1 : HasDerivAt (fun w : ℂ => ((Real.sin φ ^ 2 : ℝ) : ℂ) * w)
        ((Real.sin φ ^ 2 : ℝ) : ℂ) z :=
      ((hasDerivAt_id z).const_mul ((Real.sin φ ^ 2 : ℝ) : ℂ)).congr_deriv (mul_one _)
    have hd2 : HasDerivAt (iteratedDeriv m ψ) (iteratedDeriv (m + 1) ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z))
        (((Real.sin φ ^ 2 : ℝ) : ℂ) * z) := by
      rw [iteratedDeriv_succ]
      exact (hψm _ hmemU).differentiableAt.hasDerivAt
    have hcomp := (hd2.comp z hd1).const_mul ((Real.sin φ ^ (2 * m + 2) : ℝ) : ℂ)
    refine hcomp.congr_deriv ?_
    dsimp only [F']
    have hpow : Real.sin φ ^ (2 * (m + 1) + 2) = Real.sin φ ^ (2 * m + 2) * Real.sin φ ^ 2 := by
      rw [← pow_add, show 2 * (m + 1) + 2 = 2 * m + 2 + 2 by omega]
    rw [hpow, Complex.ofReal_mul]
    ring
  have hfderiv : HasFDerivAt (fun z : ℂ => ∫ φ in Ioc (0 : ℝ) (Real.pi / 2), F z φ)
      (∫ φ in Ioc (0 : ℝ) (Real.pi / 2), fderiv ℂ (F · φ) z₀) z₀ := by
    refine hasFDerivAt_integral_of_continuousOn_fderiv (𝕜 := ℂ) (F := F)
      (hU.isOpen.mem_nhds hz₀) isCompact_Icc measurableSet_Ioc (by simp) Ioc_subset_Icc_self hF_cont
      (fun φ hφ y hy => (hderivAt y hy φ hφ).differentiableAt.differentiableWithinAt) ?_
    refine ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp_continuousOn hF'_cont).congr fun p hp => ?_
    apply ContinuousLinearMap.ext; intro y
    rw [fderiv_eq_deriv_mul, (hderivAt p.1 hp.1 p.2 hp.2).deriv]
    rfl
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := (half_pos Real.pi_pos).le
  have hder : HasDerivAt (fun z : ℂ => ∫ φ in (0 : ℝ)..(Real.pi / 2), F z φ)
      (∫ φ in (0 : ℝ)..(Real.pi / 2), F' z₀ φ) z₀ := by
    have h1 := hfderiv.hasDerivAt
    have hfun : (fun z : ℂ => ∫ φ in Ioc (0 : ℝ) (Real.pi / 2), F z φ) =
        fun z : ℂ => ∫ φ in (0 : ℝ)..(Real.pi / 2), F z φ := by
      funext z; exact (intervalIntegral.integral_of_le hpi2).symm
    rw [hfun] at h1
    refine h1.congr_deriv ?_
    have hclm_eval : (∫ φ in Ioc (0 : ℝ) (Real.pi / 2), fderiv ℂ (F · φ) z₀) 1 =
        ∫ φ in Ioc (0 : ℝ) (Real.pi / 2), (fderiv ℂ (F · φ) z₀) 1 := by
      have hint_clm : IntegrableOn (fun φ : ℝ => fderiv ℂ (F · φ) z₀) (Ioc 0 (Real.pi / 2)) volume := by
        have hcont_clm : ContinuousOn (fun φ : ℝ => fderiv ℂ (F · φ) z₀) (Icc 0 (Real.pi / 2)) := by
          have h1' := ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp_continuousOn hF'_cont).comp
            (continuous_const.prodMk continuous_id).continuousOn (fun φ hφ => ⟨hz₀, hφ⟩)
          refine h1'.congr fun φ hφ => ?_
          apply ContinuousLinearMap.ext; intro y
          rw [fderiv_eq_deriv_mul, (hderivAt z₀ hz₀ φ hφ).deriv]
          rfl
        exact (hcont_clm.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      exact ContinuousLinearMap.integral_apply hint_clm (1 : ℂ)
    rw [hclm_eval, intervalIntegral.integral_of_le hpi2]
    refine setIntegral_congr_fun measurableSet_Ioc fun φ hφ => ?_
    rw [fderiv_eq_deriv_mul, (hderivAt z₀ hz₀ φ (Ioc_subset_Icc_self hφ)).deriv, mul_one]
  exact hder.const_mul (((2 / Real.pi : ℝ) : ℂ))

/-- Analyticity of `abelConv ψ` on any star-shaped open domain `U` where `ψ` is analytic. -/
lemma abelConv_analyticOn {U : Set ℂ} (hU : Domain U)
    {ψ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ U) :
    AnalyticOnNhd ℂ (abelConv ψ) U := by
  have hcore_diff : DifferentiableOn ℂ (abelConvCore ψ) U := fun z hz => by
    have hd := abelConvCore_hasDerivAt_gen hU hψ 0 hz
    simp only [mul_zero, zero_add, iteratedDeriv_zero] at hd
    exact hd.differentiableAt.differentiableWithinAt
  have hcore_an : AnalyticOnNhd ℂ (abelConvCore ψ) U := hcore_diff.analyticOnNhd hU.isOpen
  have heq : abelConv ψ = fun z => z * abelConvCore ψ z := funext (abelConv_eq_mul_core ψ)
  rw [heq]
  exact analyticOnNhd_id.mul hcore_an

/-- Exact `m`-th derivative of `abelConvCore ψ` on a star-shaped domain `U`. -/
private lemma iteratedDeriv_abelConvCore_eq {U : Set ℂ} (hU : Domain U)
    {ψ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ U) (m : ℕ) :
    ∀ z ∈ U, iteratedDeriv m (abelConvCore ψ) z =
      ((2 / Real.pi : ℝ) : ℂ) *
        ∫ φ in (0 : ℝ)..(Real.pi / 2),
          ((Real.sin φ ^ (2 * m + 2) : ℝ) : ℂ) * iteratedDeriv m ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * z) := by
  induction m with
  | zero =>
    intro z _
    simp [abelConvCore]
  | succ m ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (abelConvCore ψ) =ᶠ[𝓝 z]
        fun w : ℂ => ((2 / Real.pi : ℝ) : ℂ) *
          ∫ φ in (0 : ℝ)..(Real.pi / 2),
            ((Real.sin φ ^ (2 * m + 2) : ℝ) : ℂ) * iteratedDeriv m ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * w) := by
      filter_upwards [hU.isOpen.mem_nhds hz] with w hw
      exact ih w hw
    rw [hev.deriv_eq]
    exact (abelConvCore_hasDerivAt_gen hU hψ m hz).deriv

/-- Exact Taylor derivatives of `abelConv ψ` at `0`:
`abelConv ψ 0 = 0`, and `(abelConv ψ)^{(k+1)}(0) = ((2k+1)! / (2^{2k+1} (k!)²)) · ψ^{(k)}(0)`. -/
lemma abelConv_iteratedDeriv_zero {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ 0) :
    abelConv ψ 0 = 0 ∧
    ∀ k : ℕ, iteratedDeriv (k + 1) (abelConv ψ) 0 =
      (((2 * k + 1).factorial : ℂ) / ((2 : ℂ) ^ (2 * k + 1) * (k.factorial : ℂ) ^ 2)) *
        iteratedDeriv k ψ 0 := by
  refine ⟨by simp [abelConv], fun k => ?_⟩
  obtain ⟨r, hr_pos, hball⟩ := Metric.eventually_nhds_iff.mp hψ.eventually_analyticAt
  let U : Set ℂ := Metric.ball (0 : ℂ) r
  have hU : Domain U := by
    refine ⟨Metric.isOpen_ball, fun z hz t ht => ?_⟩
    simp only [U, Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.1] at hz ⊢
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
  have hψU : AnalyticOnNhd ℂ ψ U := fun z hz => hball (by simpa [U] using hz)
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hr_pos
  have hcore_an : AnalyticAt ℂ (abelConvCore ψ) 0 := by
    have hdiff : DifferentiableOn ℂ (abelConvCore ψ) U := fun z hz => by
      have hd := abelConvCore_hasDerivAt_gen hU hψU 0 hz
      simp only [mul_zero, zero_add, iteratedDeriv_zero] at hd
      exact hd.differentiableAt.differentiableWithinAt
    exact (hdiff.analyticOnNhd hU.isOpen) 0 h0U
  have heq : abelConv ψ = fun z => id z * abelConvCore ψ z := funext (abelConv_eq_mul_core ψ)
  rw [heq, iteratedDeriv_fun_mul (analyticAt_id.contDiffAt) hcore_an.contDiffAt]
  have hterm : ∀ i ∈ Finset.range (k + 2),
      ((k + 1).choose i : ℂ) * iteratedDeriv i (id : ℂ → ℂ) 0 *
        iteratedDeriv (k + 1 - i) (abelConvCore ψ) 0 =
      if i = 1 then ((k + 1 : ℕ) : ℂ) * iteratedDeriv k (abelConvCore ψ) 0 else 0 := by
    intro i _
    have hid : iteratedDeriv i (id : ℂ → ℂ) (0 : ℂ) = if i = 1 then 1 else 0 := by
      rcases i with _ | _ | i
      · simp
      · simp
      · rw [iteratedDeriv_succ', show deriv (id : ℂ → ℂ) = fun _ => (1 : ℂ) by funext _; simp]
        rw [iteratedDeriv_succ', show deriv (fun _ : ℂ => (1 : ℂ)) = fun _ => (0 : ℂ) by funext _; simp]
        simp
    rw [hid]
    split_ifs with hi
    · subst hi; simp [Nat.choose_one_right]
    · simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  have h1mem : 1 ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
  simp only [h1mem, ↓reduceIte]
  rw [iteratedDeriv_abelConvCore_eq hU hψU k 0 h0U]
  simp only [mul_zero]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  have hwallis : (((2 / Real.pi : ℝ) : ℂ) *
      ((∫ φ in (0 : ℝ)..(Real.pi / 2), Real.sin φ ^ (2 * k + 2) : ℝ) : ℂ)) =
      ((((2 * k + 1).factorial : ℝ) /
        ((2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) * ((k + 1).factorial : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, wallis_sin_even_integral k]
  calc ((k + 1 : ℕ) : ℂ) *
        (((2 / Real.pi : ℝ) : ℂ) *
          (((∫ φ in (0 : ℝ)..(Real.pi / 2), Real.sin φ ^ (2 * k + 2) : ℝ) : ℂ) * iteratedDeriv k ψ 0))
      = ((k + 1 : ℕ) : ℂ) *
          ((((2 / Real.pi : ℝ) : ℂ) *
            ((∫ φ in (0 : ℝ)..(Real.pi / 2), Real.sin φ ^ (2 * k + 2) : ℝ) : ℂ)) *
            iteratedDeriv k ψ 0) := by ring
    _ = ((k + 1 : ℕ) : ℂ) *
          (((((2 * k + 1).factorial : ℝ) /
            ((2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) * ((k + 1).factorial : ℝ)) : ℝ) : ℂ) *
            iteratedDeriv k ψ 0) := by rw [hwallis]
    _ = (((2 * k + 1).factorial : ℂ) / ((2 : ℂ) ^ (2 * k + 1) * (k.factorial : ℂ) ^ 2)) *
          iteratedDeriv k ψ 0 := by
        push_cast
        have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have hf0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        have hf1 : ((k + 1).factorial : ℂ) = ((k + 1 : ℕ) : ℂ) * (k.factorial : ℂ) := by
          rw [Nat.factorial_succ]; push_cast; rfl
        have h2p : (2 : ℂ) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [hf1]
        field_simp [hk1, hf0, h2p]
        push_cast
        ring

/-- Exponential-type preservation under `abelConv`:
`ExpType (Minor.pull d ψ) → ExpType (Minor.pull d (abelConv ψ))`. -/
lemma abelConv_expType {ψ : ℂ → ℂ} {d : ℂ} (h : ExpType (Minor.pull d ψ)) :
    ExpType (Minor.pull d (abelConv ψ)) := by
  obtain ⟨C, D, hC, hD, hbd⟩ := h
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨0, 0, le_rfl, le_rfl, fun v _ => by simp [Minor.pull]⟩
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  refine ⟨‖d‖ * C, D + 1, by positivity, by positivity, fun v hv => ?_⟩
  unfold Minor.pull abelConv
  have hpull_eq : d * (((2 / Real.pi : ℝ) : ℂ) * (d * (v : ℂ)) *
        ∫ φ in (0 : ℝ)..(Real.pi / 2),
          ((Real.sin φ ^ 2 : ℝ) : ℂ) * ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * (d * (v : ℂ)))) =
      d * (((2 / Real.pi : ℝ) : ℂ) * (v : ℂ) *
        ∫ φ in (0 : ℝ)..(Real.pi / 2),
          ((Real.sin φ ^ 2 : ℝ) : ℂ) * (Minor.pull d ψ (Real.sin φ ^ 2 * v))) := by
    have hin : (fun φ : ℝ => ((Real.sin φ ^ 2 : ℝ) : ℂ) * Minor.pull d ψ (Real.sin φ ^ 2 * v)) =
        fun φ : ℝ => d * (((Real.sin φ ^ 2 : ℝ) : ℂ) * ψ (((Real.sin φ ^ 2 : ℝ) : ℂ) * (d * (v : ℂ)))) := by
      funext φ; unfold Minor.pull; push_cast; ring
    rw [hin, intervalIntegral.integral_const_mul]; ring
  rw [hpull_eq, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2 / Real.pi), Real.norm_of_nonneg hv]
  have hint_le : ‖∫ φ in (0 : ℝ)..(Real.pi / 2),
        ((Real.sin φ ^ 2 : ℝ) : ℂ) * Minor.pull d ψ (Real.sin φ ^ 2 * v)‖ ≤
      (Real.pi / 2) * (C * Real.exp (D * v)) := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := Real.pi / 2)
      (C := C * Real.exp (D * v)) (f := fun φ : ℝ =>
        ((Real.sin φ ^ 2 : ℝ) : ℂ) * Minor.pull d ψ (Real.sin φ ^ 2 * v)) fun φ _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      have harg_nn : 0 ≤ Real.sin φ ^ 2 * v := mul_nonneg (sq_nonneg _) hv
      have harg_le : Real.sin φ ^ 2 * v ≤ v := mul_le_of_le_one_left hv (Real.sin_sq_le_one φ)
      calc Real.sin φ ^ 2 * ‖Minor.pull d ψ (Real.sin φ ^ 2 * v)‖
          ≤ 1 * (C * Real.exp (D * (Real.sin φ ^ 2 * v))) :=
            mul_le_mul (Real.sin_sq_le_one φ) (hbd _ harg_nn) (norm_nonneg _) zero_le_one
        _ ≤ C * Real.exp (D * v) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left harg_le hD)) hC
    simpa [mul_comm, sub_zero, abs_of_pos (half_pos Real.pi_pos)] using hconst
  have hv_exp : v * Real.exp (D * v) ≤ Real.exp ((D + 1) * v) := by
    rw [add_mul, one_mul, Real.exp_add, mul_comm (Real.exp (D * v))]
    exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp v]) (Real.exp_pos _).le
  have hpi_cancel : (2 / Real.pi) * (Real.pi / 2) = 1 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi]
  calc ‖d‖ * (2 / Real.pi * v * ‖∫ φ in (0 : ℝ)..(Real.pi / 2), _‖)
      ≤ ‖d‖ * (2 / Real.pi * v * ((Real.pi / 2) * (C * Real.exp (D * v)))) := by gcongr
    _ = ‖d‖ * C * ((2 / Real.pi * (Real.pi / 2)) * (v * Real.exp (D * v))) := by ring
    _ = ‖d‖ * C * (v * Real.exp (D * v)) := by rw [hpi_cancel, one_mul]
    _ ≤ ‖d‖ * C * Real.exp ((D + 1) * v) := by gcongr

/-- Gevrey-1 Euler formal power series associated to a meromorphic Borel kernel `ψ`:
`eulerSeriesOf ψ = ∑_{k ≥ 0} ((2k+1)! / (2^{2k+1} (k!)²)) ψ^{(k)}(0) X^k`. -/
@[expose] def eulerSeriesOf (ψ : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k =>
    (((2 * k + 1).factorial : ℂ) / ((2 : ℂ) ^ (2 * k + 1) * (k.factorial : ℂ) ^ 2)) *
      iteratedDeriv k ψ 0

/-- Exact shift identity `formalSeries (abelConv ψ) = X^2 * eulerSeriesOf ψ`. -/
theorem formalSeries_abelConv_eq {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ 0) :
    formalSeries (abelConv ψ) = PowerSeries.X ^ 2 * eulerSeriesOf ψ := by
  obtain ⟨h0, hsucc⟩ := abelConv_iteratedDeriv_zero hψ
  ext n
  rcases n with _ | _ | k
  · simp [formalSeries, PowerSeries.coeff_X_pow_mul']
  · simp [formalSeries, h0, PowerSeries.coeff_X_pow_mul']
  · simp only [formalSeries, PowerSeries.coeff_mk]
    rw [show k + 1 + 1 = k + 2 by omega, PowerSeries.coeff_X_pow_mul]
    simpa [eulerSeriesOf] using hsucc k

/-! ### 2. Complex Inverse-Square-Root Laplace Transform & Lateral Factorization of `abelConv` -/

private lemma integrableOn_rpow_neg_half_mul_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℝ => w ^ (-(1 / 2 : ℝ)) * Real.exp (-r * w)) (Ioi (0 : ℝ)) volume := by
  have h1 : IntegrableOn (fun w : ℝ => w ^ (-(1 / 2 : ℝ)) * Real.exp (-r * w))
      (Ioc (0 : ℝ) 1) volume := by
    have hdom : IntegrableOn (fun w : ℝ => w ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) volume := by
      have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
        (r := -(1 / 2 : ℝ)) (by norm_num)
      exact hi.1
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (Set.mem_Ioc.mp hw).1.ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
      have hw0 : 0 < w := hw.1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hw0 _).le (Real.exp_pos _).le)]
      have hexp : Real.exp (-r * w) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_le_of_le_one_right (Real.rpow_pos_of_pos hw0 _).le hexp
  have h2 : IntegrableOn (fun w : ℝ => w ^ (-(1 / 2 : ℝ)) * Real.exp (-r * w))
      (Ioi (1 : ℝ)) volume := by
    have hdom : IntegrableOn (fun w : ℝ => Real.exp (-r * w)) (Ioi (1 : ℝ)) volume :=
      integrableOn_exp_mul_Ioi (by linarith) 1
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (lt_trans zero_lt_one hw).ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hw1 : 1 ≤ w := le_of_lt hw
      have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hw0 _).le (Real.exp_pos _).le)]
      have hrp : w ^ (-(1 / 2 : ℝ)) ≤ 1 := by
        calc w ^ (-(1 / 2 : ℝ)) ≤ w ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
          _ = 1 := Real.rpow_zero w
      exact mul_le_of_le_one_left (Real.exp_pos _).le hrp
  have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hunion]
  exact h1.union h2

private lemma integrableOn_rpow_half_mul_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℝ => w ^ (1 / 2 : ℝ) * Real.exp (-r * w)) (Ioi (0 : ℝ)) volume := by
  have h1 : IntegrableOn (fun w : ℝ => w ^ (1 / 2 : ℝ) * Real.exp (-r * w))
      (Ioc (0 : ℝ) 1) volume := by
    have hdom : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) volume :=
      integrableOn_const (by simp)
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (Set.mem_Ioc.mp hw).1.ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
      have hw0 : 0 < w := hw.1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hw0 _).le (Real.exp_pos _).le)]
      have hrp : w ^ (1 / 2 : ℝ) ≤ 1 :=
        Real.rpow_le_one hw0.le hw.2 (by norm_num)
      have hexp : Real.exp (-r * w) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc w ^ (1 / 2 : ℝ) * Real.exp (-r * w)
          ≤ 1 * 1 := mul_le_mul hrp hexp (Real.exp_pos _).le zero_le_one
        _ = 1 := mul_one 1
  have h2 : IntegrableOn (fun w : ℝ => w ^ (1 / 2 : ℝ) * Real.exp (-r * w))
      (Ioi (1 : ℝ)) volume := by
    have hdom : IntegrableOn (fun w : ℝ => (2 / r) * Real.exp (-(r / 2) * w)) (Ioi (1 : ℝ)) volume :=
      (integrableOn_exp_mul_Ioi (by linarith) 1).const_mul (2 / r)
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (lt_trans zero_lt_one hw).ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hw1 : 1 ≤ w := le_of_lt hw
      have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hw0 _).le (Real.exp_pos _).le)]
      have hrp : w ^ (1 / 2 : ℝ) ≤ w := by
        calc w ^ (1 / 2 : ℝ) ≤ w ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
          _ = w := Real.rpow_one w
      have hsplit : Real.exp (-r * w) = Real.exp (-((r / 2) * w)) * Real.exp (-(r / 2) * w) := by
        rw [← Real.exp_add]; congr 1; ring
      have hlin : (r / 2) * w * Real.exp (-((r / 2) * w)) ≤ 1 := by
        have hex : (r / 2) * w ≤ Real.exp ((r / 2) * w) := by linarith [Real.add_one_le_exp ((r / 2) * w)]
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        exact hex
      have hw_le : w * Real.exp (-((r / 2) * w)) ≤ 2 / r := by
        calc w * Real.exp (-((r / 2) * w))
            = (2 / r) * ((r / 2) * w * Real.exp (-((r / 2) * w))) := by field_simp [hr.ne']
          _ ≤ (2 / r) * 1 := mul_le_mul_of_nonneg_left hlin (by positivity)
          _ = 2 / r := mul_one _
      calc w ^ (1 / 2 : ℝ) * Real.exp (-r * w)
          ≤ w * Real.exp (-r * w) := mul_le_mul_of_nonneg_right hrp (Real.exp_pos _).le
        _ = (w * Real.exp (-((r / 2) * w))) * Real.exp (-(r / 2) * w) := by rw [hsplit]; ring
        _ ≤ (2 / r) * Real.exp (-(r / 2) * w) := mul_le_mul_of_nonneg_right hw_le (Real.exp_pos _).le
  have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hunion]
  exact h1.union h2

/-- Exact complex Laplace transform of `w^{-1/2}` on the right half-plane `Re(p) > 0`:
`∫_0^∞ e^{-p w} w^{-1/2} dw = √π · p^{-1/2}`. -/
lemma complexLaplace_inv_sqrt {p : ℂ} (hp : 0 < p.re) :
    ∫ w in Ioi (0 : ℝ), Complex.exp (-p * (w : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * p ^ (-(1 / 2 : ℝ) : ℂ) := by
  let U : Set ℂ := {q : ℂ | 0 < q.re}
  let L : ℂ → ℂ := fun q =>
    ∫ w in Ioi (0 : ℝ), Complex.exp (-q * (w : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let R : ℂ → ℂ := fun q => ((Real.sqrt Real.pi : ℝ) : ℂ) * q ^ (-(1 / 2 : ℝ) : ℂ)
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_pre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hL_diff : DifferentiableOn ℂ L U := by
    intro q₀ hq₀
    have hq₀' : 0 < q₀.re := hq₀
    have hr₀ : 0 < q₀.re / 2 := half_pos hq₀'
    let s : Set ℂ := {q : ℂ | q₀.re / 2 < q.re}
    have hs_mem : s ∈ 𝓝 q₀ := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [s]; linarith)
    let F : ℂ → ℝ → ℂ := fun q w =>
      Complex.exp (-q * (w : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    let F' : ℂ → ℝ → ℂ := fun q w =>
      -(w : ℂ) * Complex.exp (-q * (w : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    let bound : ℝ → ℝ := fun w => w ^ (1 / 2 : ℝ) * Real.exp (-(q₀.re / 2) * w)
    have hmeas : ∀ q : ℂ, AEStronglyMeasurable (F q) (volume.restrict (Ioi (0 : ℝ))) := fun q => by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul ?_
      exact Complex.continuous_ofReal.continuousOn.comp
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (Set.mem_Ioi.mp hw).ne')
        (Set.mapsTo_univ _ _)
    have hF_int : Integrable (F q₀) (volume.restrict (Ioi (0 : ℝ))) := by
      refine (integrableOn_rpow_neg_half_mul_exp hq₀').mono' (hmeas q₀) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      rw [norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_pos_of_pos hw _).le]
      have hre : (-q₀ * (w : ℂ)).re = -q₀.re * w := by simp
      rw [hre, mul_comm]
    have hF'_meas : AEStronglyMeasurable (F' q₀) (volume.restrict (Ioi (0 : ℝ))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ((Complex.continuous_ofReal.neg.continuousOn).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul ?_
      exact Complex.continuous_ofReal.continuousOn.comp
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (Set.mem_Ioi.mp hw).ne')
        (Set.mapsTo_univ _ _)
    have hbound : ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))), ∀ q ∈ s, ‖F' q w‖ ≤ bound w := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw q hq
      have hw0 : 0 < w := hw
      dsimp only [F', bound]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hw0.le,
        Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hw0 _).le]
      have hre : (-q * (w : ℂ)).re = -q.re * w := by simp
      rw [hre]
      have hrp : w * w ^ (-(1 / 2 : ℝ)) = w ^ (1 / 2 : ℝ) := by
        calc w * w ^ (-(1 / 2 : ℝ)) = w ^ (1 : ℝ) * w ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
          _ = w ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := (Real.rpow_add hw0 _ _).symm
          _ = w ^ (1 / 2 : ℝ) := by norm_num
      have hexp : Real.exp (-q.re * w) ≤ Real.exp (-(q₀.re / 2) * w) :=
        Real.exp_le_exp.mpr (by nlinarith [Set.mem_ofPred_eq.mp hq])
      calc w * Real.exp (-q.re * w) * w ^ (-(1 / 2 : ℝ))
          = (w * w ^ (-(1 / 2 : ℝ))) * Real.exp (-q.re * w) := by ring
        _ = w ^ (1 / 2 : ℝ) * Real.exp (-q.re * w) := by rw [hrp]
        _ ≤ w ^ (1 / 2 : ℝ) * Real.exp (-(q₀.re / 2) * w) :=
            mul_le_mul_of_nonneg_left hexp (Real.rpow_pos_of_pos hw0 _).le
    have hdiff : ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))), ∀ q ∈ s, HasDerivAt (F · w) (F' q w) q := by
      filter_upwards with w q _
      have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-z * (w : ℂ)))
          (Complex.exp (-q * (w : ℂ)) * (-(w : ℂ))) q := by
        simpa using ((hasDerivAt_id q).neg.mul_const (w : ℂ)).cexp
      have h2 := h1.mul_const ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      exact h2.congr_deriv (by dsimp only [F']; ring)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_mem (.of_forall hmeas)
      hF_int hF'_meas hbound (integrableOn_rpow_half_mul_exp hr₀) hdiff).2.differentiableAt.differentiableWithinAt
  have hR_diff : DifferentiableOn ℂ R U := fun q hq => by
    have hcp : HasDerivAt (fun z : ℂ => z ^ (-(1 / 2 : ℝ) : ℂ))
        ((-(1 / 2 : ℝ) : ℂ) * q ^ ((-(1 / 2 : ℝ) : ℂ) - 1) * 1) q :=
      (hasDerivAt_id q).cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl hq))
    exact (hcp.const_mul ((Real.sqrt Real.pi : ℝ) : ℂ)).differentiableAt.differentiableWithinAt
  have hL_an : AnalyticOnNhd ℂ L U := hL_diff.analyticOnNhd hU_open
  have hR_an : AnalyticOnNhd ℂ R U := hR_diff.analyticOnNhd hU_open
  have hreal : ∀ x : ℝ, 0 < x → L (x : ℂ) = R (x : ℂ) := fun x hx => by
    dsimp only [L, R]
    have hcast : (fun w : ℝ => Complex.exp (-(x : ℂ) * (w : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
        fun w : ℝ => ((w ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(x * w)) : ℝ) : ℂ) := by
      funext w
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      have hneg : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
      rw [hneg]; push_cast; ring
    rw [hcast, integral_complex_ofReal, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hx,
      Real.Gamma_one_half_eq]
    have hrp : (1 / x) ^ (1 / 2 : ℝ) = x ^ (-(1 / 2 : ℝ)) := by
      rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]
    rw [hrp, Complex.ofReal_mul, mul_comm, Complex.ofReal_cpow hx.le]
    norm_cast
  have h1U : (1 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), L z = R z := by
    rw [Filter.frequently_iff]
    intro V hV
    rw [mem_nhdsWithin] at hV
    obtain ⟨W, hW_open, h1W, hWV⟩ := hV
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hW_open 1 h1W
    let z : ℂ := ((1 + δ / 2 : ℝ) : ℂ)
    refine ⟨z, hWV ⟨hball ?_, ?_⟩, hreal (1 + δ / 2) (by linarith)⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsub : z - (1 : ℂ) = ((δ / 2 : ℝ) : ℂ) := by dsimp [z]; push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · intro h0
      have hre := congrArg Complex.re h0
      simp [z] at hre
      linarith
  exact hL_an.eqOn_of_preconnected_of_frequently_eq hR_an hU_pre h1U hfreq hp

/-- Exact principal square root along a ray `e^{i σ}` (`|σ| < π/2`). -/
private lemma cpow_half_exp_mul {σ t : ℝ} (hσ : |σ| < Real.pi / 2) (ht : 0 < t) :
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

/-- Exact negative principal square root along `u * e^{i σ}` (`u > 0`, `|σ| < π/2`). -/
private lemma cpow_neg_half_mul_exp {σ u : ℝ} (hσ : |σ| < Real.pi / 2) (hu : 0 < u) :
    ((u : ℂ) * Complex.exp (I * (σ : ℂ))) ^ (-(1 / 2 : ℝ) : ℂ) =
      ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-I * ((σ / 2 : ℝ) : ℂ)) := by
  have hne : (u : ℂ) * Complex.exp (I * (σ : ℂ)) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne') (Complex.exp_ne_zero _)
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log ((u : ℂ) * Complex.exp (I * (σ : ℂ))) = (Real.log u : ℂ) + I * (σ : ℂ) := by
    have hexp : Complex.exp ((Real.log u : ℂ) + I * (σ : ℂ)) = (u : ℂ) * Complex.exp (I * (σ : ℂ)) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hu]
    rw [← hexp, Complex.log_exp]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_zero, one_mul, zero_add]
      linarith [abs_lt.mp hσ, Real.pi_pos]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_zero, one_mul, zero_add]
      linarith [abs_lt.mp hσ, Real.pi_pos]
  rw [hlog, add_mul, Complex.exp_add]
  congr 1
  · rw [Real.rpow_def_of_pos hu, Complex.ofReal_exp]
    congr 1; push_cast; ring
  · congr 1; push_cast; ring

/-- Exact real convolution identity `Minor.pull d (abelConv ψ) v = borelProduct F2 F1 v` for `v > 0`. -/
private lemma abelConv_pull_eq_borelProduct (ψ : ℂ → ℂ) (d : ℂ) {v : ℝ} (hv : 0 < v) :
    Minor.pull d (abelConv ψ) v =
      borelProduct
        (fun t : ℝ => (d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * ψ (d * (t : ℂ)))
        (fun w : ℝ => (d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        v := by
  let g : ℝ → ℝ := fun φ => v * Real.sin φ ^ 2
  let H : ℝ → ℂ := fun t =>
    ((d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * ψ (d * (t : ℂ))) *
      ((d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * (((v - t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
  have hImg : g '' Ioo (0 : ℝ) (Real.pi / 2) = Ioo (0 : ℝ) v := by
    ext t
    simp only [Set.mem_image, Set.mem_Ioo, g]
    constructor
    · rintro ⟨φ, ⟨hφ0, hφ1⟩, rfl⟩
      have hsin_pos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
      have hcos_pos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ1⟩
      have hlt1 : Real.sin φ ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hcos_pos]
      exact ⟨mul_pos hv (sq_pos_of_pos hsin_pos), by nlinarith⟩
    · rintro ⟨ht0, htv⟩
      let s : ℝ := Real.sqrt (t / v)
      have hs_pos : 0 < s := Real.sqrt_pos.mpr (div_pos ht0 hv)
      have hs_lt1 : s < 1 := by
        have hlt : t / v < 1 := (div_lt_one hv).mpr htv
        have : Real.sqrt (t / v) < Real.sqrt 1 := Real.sqrt_lt_sqrt (div_pos ht0 hv).le hlt
        simpa [s] using this
      refine ⟨Real.arcsin s, ⟨Real.arcsin_pos.mpr hs_pos, ?_⟩, ?_⟩
      · exact Real.arcsin_lt_pi_div_two.mpr hs_lt1
      · rw [Real.sin_arcsin (by linarith) hs_lt1.le, Real.sq_sqrt (div_pos ht0 hv).le]
        field_simp [hv.ne']
  have hInj : Set.InjOn g (Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro a ha b hb hab
    have hsin_a : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, Real.pi_pos])
    have hsin_b : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [hb.2, Real.pi_pos])
    have hsq : Real.sin a ^ 2 = Real.sin b ^ 2 := mul_left_cancel₀ hv.ne' hab
    have hsin_eq : Real.sin a = Real.sin b := by nlinarith
    exact Real.injOn_sin ⟨by linarith [ha.1, Real.pi_pos], ha.2.le⟩
      ⟨by linarith [hb.1, Real.pi_pos], hb.2.le⟩ hsin_eq
  have hDeriv : ∀ φ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt g (2 * v * Real.sin φ * Real.cos φ) (Ioo (0 : ℝ) (Real.pi / 2)) φ := fun φ _ => by
    have hd := ((Real.hasDerivAt_sin φ).pow 2).const_mul v
    convert hd.hasDerivWithinAt using 1
    ring
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hDeriv hInj H
  rw [hImg] at hcov
  have hborel_eq : borelProduct
      (fun t : ℝ => (d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * ψ (d * (t : ℂ)))
      (fun w : ℝ => (d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) v =
      ∫ t in Ioo (0 : ℝ) v, H t := by
    unfold borelProduct
    rw [intervalIntegral.integral_of_le hv.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hborel_eq, hcov]
  unfold Minor.pull abelConv
  rw [intervalIntegral.integral_of_le (half_pos Real.pi_pos).le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
  have hsin_pos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])
  have hcos_pos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
  have hderiv_nn : 0 ≤ 2 * v * Real.sin φ * Real.cos φ := by positivity
  rw [abs_of_nonneg hderiv_nn, Complex.real_smul]
  dsimp only [H, g]
  have hsub_cos : v - v * Real.sin φ ^ 2 = v * Real.cos φ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hsq1 : Real.sqrt (v * Real.sin φ ^ 2) = Real.sqrt v * Real.sin φ := by
    rw [Real.sqrt_mul hv.le, Real.sqrt_sq hsin_pos.le]
  have hrp2 : (v - v * Real.sin φ ^ 2) ^ (-(1 / 2 : ℝ)) = (Real.sqrt v * Real.cos φ)⁻¹ := by
    rw [hsub_cos, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul hv.le, Real.sqrt_sq hcos_pos.le]
  rw [hsq1, hrp2]
  have hsv : ((Real.sqrt v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hcp : Complex.cos (φ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact Complex.ofReal_ne_zero.mpr hcos_pos.ne'
  have hpi_sq : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  have harg : d * ((v : ℂ) * Complex.sin (φ : ℂ) ^ 2) = Complex.sin (φ : ℂ) ^ 2 * (d * (v : ℂ)) := by ring
  rw [harg]
  field_simp [hsv, hsp, hcp, hpi_ne]
  rw [hpi_sq]
  ring

/-- Ray Laplace integral `H_ray ψ d u = (1 / √π) ∫_0^∞ e^{-u d t} d (d t)^{1/2} ψ(d t) dt`. -/
@[expose] def halfRayLaplace (ψ : ℂ → ℂ) (d : ℂ) (u : ℝ) : ℂ :=
  ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in Ioi (0 : ℝ),
      Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d * (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ))

/-- Exact lateral factorization: along any ray `d = e^{i σ}` (`|σ| < π/2`) on which `ψ` is
continuous and has `ExpType`, for sufficiently large `u > 0`:
`(Minor.mk 0 (abelConv ψ)).value d u = u^{-1/2} · halfRayLaplace ψ d u`. -/
lemma abelConv_value_eq_rpow_mul_halfRay {ψ : ℂ → ℂ} {σ : ℝ} (hσ : |σ| < Real.pi / 2)
    (hcont : ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0))
    (hexp : ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ)) :
    ∀ᶠ u : ℝ in atTop,
      (Minor.mk 0 (abelConv ψ)).value (Complex.exp (I * (σ : ℂ))) (u : ℂ) =
        ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * halfRayLaplace ψ (Complex.exp (I * (σ : ℂ))) u := by
  let d : ℂ := Complex.exp (I * (σ : ℂ))
  have hd_re : 0 < d.re := by
    dsimp only [d]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hσ)
  obtain ⟨C, D, hC, hD, hbd⟩ := hexp
  let F1 : ℝ → ℂ := fun w => (d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let F2 : ℝ → ℂ := fun t => (d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * ψ (d * (t : ℂ))
  filter_upwards [eventually_gt_atTop (max 0 ((D + 1) / d.re))] with u hu
  have hu_pos : 0 < u := lt_of_le_of_lt (le_max_left _ _) hu
  have hud_re : D + 1 < ((u : ℂ) * d).re := by
    have h1 : (D + 1) / d.re < u := lt_of_le_of_lt (le_max_right _ _) hu
    have h2 : D + 1 < u * d.re := (div_lt_iff₀ hd_re).mp h1
    simpa [Complex.mul_re] using h2
  have hud_pos : 0 < ((u : ℂ) * d).re := by linarith
  have hF1_int : IntegrableOn (damped ((u : ℂ) * d) F1) (Ioi (0 : ℝ)) volume := by
    have hdom : IntegrableOn (fun w : ℝ =>
        ‖d / ((Real.sqrt Real.pi : ℝ) : ℂ)‖ * (w ^ (-(1 / 2 : ℝ)) * Real.exp (-((u : ℂ) * d).re * w)))
        (Ioi (0 : ℝ)) volume :=
      (integrableOn_rpow_neg_half_mul_exp hud_pos).const_mul _
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul ?_
      exact continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (Set.mem_Ioi.mp hw).ne')
        (Set.mapsTo_univ _ _))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      rw [damped_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hw _).le]
      exact le_of_eq (by ring)
  have hF2_int : IntegrableOn (damped ((u : ℂ) * d) F2) (Ioi (0 : ℝ)) volume := by
    have hF2_eq : ∀ t : ℝ, F2 t = ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * ((Real.sqrt t : ℝ) : ℂ) * Minor.pull d ψ t :=
      fun t => by dsimp only [F2, Minor.pull]; ring
    have hdom : IntegrableOn (fun t : ℝ =>
        (C / Real.sqrt Real.pi) * (t ^ (1 / 2 : ℝ) * Real.exp (-(((u : ℂ) * d).re - D) * t)))
        (Ioi (0 : ℝ)) volume :=
      (integrableOn_rpow_half_mul_exp (by linarith)).const_mul _
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      have hF2_cont : ContinuousOn F2 (Ioi 0) := by
        rw [show F2 = fun t => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * ((Real.sqrt t : ℝ) : ℂ) * Minor.pull d ψ t from
          funext hF2_eq]
        exact (continuousOn_const.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn).mul hcont
      exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul hF2_cont
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [damped_norm, hF2_eq, norm_mul, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sqrt_eq_rpow t]
      have hbt := hbd t ht0.le
      have hrp_nn : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
      calc Real.exp (-((u : ℂ) * d).re * t) * ((Real.sqrt Real.pi)⁻¹ * t ^ (1 / 2 : ℝ) * ‖Minor.pull d ψ t‖)
          ≤ Real.exp (-((u : ℂ) * d).re * t) * ((Real.sqrt Real.pi)⁻¹ * t ^ (1 / 2 : ℝ) * (C * Real.exp (D * t))) := by
            gcongr
        _ = (C / Real.sqrt Real.pi) * (t ^ (1 / 2 : ℝ) * (Real.exp (-((u : ℂ) * d).re * t) * Real.exp (D * t))) := by
            rw [div_eq_mul_inv]; ring
        _ = (C / Real.sqrt Real.pi) * (t ^ (1 / 2 : ℝ) * Real.exp (-(((u : ℂ) * d).re - D) * t)) := by
            rw [← Real.exp_add]; congr 3; ring
  have hval_eq : (Minor.mk 0 (abelConv ψ)).value d (u : ℂ) = complexLaplace (borelProduct F2 F1) ((u : ℂ) * d) := by
    simp only [Minor.value, zero_add, complexLaplace]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    simp only [damped]
    rw [abelConv_pull_eq_borelProduct ψ d hv]
  rw [hval_eq, complexLaplace_product hF2_int hF1_int]
  have hL1 : complexLaplace F1 ((u : ℂ) * d) =
      ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) := by
    unfold complexLaplace damped F1
    have hpull : (fun w : ℝ => Complex.exp (-((u : ℂ) * d) * (w : ℂ)) *
          ((d / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) =
        fun w : ℝ => (d / ((Real.sqrt Real.pi : ℝ) : ℂ)) *
          (Complex.exp (-((u : ℂ) * d) * (w : ℂ)) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
      funext w; ring
    rw [hpull, integral_const_mul, complexLaplace_inv_sqrt hud_pos]
    have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    rw [cpow_neg_half_mul_exp hσ hu_pos]
    have hexp_mul : d * Complex.exp (-I * ((σ / 2 : ℝ) : ℂ)) = Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) := by
      dsimp only [d]; rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc d / ((Real.sqrt Real.pi : ℝ) : ℂ) *
          (((Real.sqrt Real.pi : ℝ) : ℂ) * (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-I * ((σ / 2 : ℝ) : ℂ))))
        = ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (d * Complex.exp (-I * ((σ / 2 : ℝ) : ℂ))) := by
          field_simp [hsp]
      _ = ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) := by
          rw [hexp_mul]
  rw [hL1]
  unfold complexLaplace damped F2 halfRayLaplace
  rw [mul_comm _ (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * _), mul_assoc]
  congr 1
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  dsimp only [d]
  rw [cpow_half_exp_mul hσ ht]
  have harg1 : -(↑u * Complex.exp (I * ↑σ)) * ↑t = -↑u * (Complex.exp (I * ↑σ) * ↑t) := by ring
  rw [harg1]; ring

/-! ### 3. Slit-Origin Triangle Cauchy–Goursat Theorem (`triIntegral_eq_zero_of_analyticOn_pos`) -/

private lemma mem_closedTri_of_le {R m x t : ℝ} (hx : x ∈ Icc 0 R) (ht : t ∈ Icc (-m) m) :
    (x : ℂ) * (1 + I * (t : ℂ)) ∈ closedTri R m := by
  have hre : ((x : ℂ) * (1 + I * (t : ℂ))).re = x := by simp [Complex.mul_re]
  have him : ((x : ℂ) * (1 + I * (t : ℂ))).im = x * t := by simp [Complex.mul_im]
  refine ⟨by rw [hre]; exact hx.1, by rw [hre]; exact hx.2, ?_⟩
  rw [hre, him, abs_mul, abs_of_nonneg hx.1, mul_comm m x]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) hx.1

/-- **Slit-Origin Triangle Cauchy–Goursat Theorem**:
If `F` is continuous on `closedTri R m` and analytic on an open set `U` containing
`{z ∈ closedTri R m | 0 < z.re}` (allowing an endpoint branch point at `z = 0`), then
`triIntegral F R m = 0`. -/
lemma triIntegral_eq_zero_of_analyticOn_pos {F : ℂ → ℂ} {R m : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hm : 0 < m) (hU : IsOpen U)
    (hsub : {z ∈ closedTri R m | 0 < z.re} ⊆ U)
    (hF_an : AnalyticOnNhd ℂ F U)
    (hF_cont : ContinuousOn F (closedTri R m)) :
    triIntegral F R m = 0 := by
  have hm_le : -m ≤ m := by linarith
  -- Step 1: For every δ ∈ (0, R), triIntegral F R m = triIntegral F δ m by FTC on [δ, R]
  have htrap : ∀ δ : ℝ, 0 < δ → δ < R → triIntegral F R m = triIntegral F δ m := fun δ hδ hδR => by
    let H (x t : ℝ) : ℂ := (x : ℂ) * F ((x : ℂ) * (1 + I * (t : ℂ)))
    let Hx (x t : ℝ) : ℂ :=
      F ((x : ℂ) * (1 + I * (t : ℂ))) +
        (x : ℂ) * (1 + I * (t : ℂ)) * deriv F ((x : ℂ) * (1 + I * (t : ℂ)))
    let Φ (x : ℝ) : ℂ := I * ∫ t in (-m)..m, H x t
    have hmap_cont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (1 + I * (p.2 : ℂ))) :=
      (Complex.continuous_ofReal.comp continuous_fst).mul
        (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
    have hS_open : IsOpen {p : ℝ × ℝ | (p.1 : ℂ) * (1 + I * (p.2 : ℂ)) ∈ U} :=
      hU.preimage hmap_cont
    have hΦ_deriv : ∀ x₀ ∈ Icc δ R, HasDerivAt Φ
        ((1 + I * (m : ℂ)) * F ((x₀ : ℂ) * (1 + I * (m : ℂ))) -
          (1 - I * (m : ℂ)) * F ((x₀ : ℂ) * (1 - I * (m : ℂ)))) x₀ := fun x₀ hx₀ => by
      have hprod_sub : ({x₀} : Set ℝ) ×ˢ uIcc (-m) m ⊆
          {p : ℝ × ℝ | (p.1 : ℂ) * (1 + I * (p.2 : ℂ)) ∈ U} := by
        rintro ⟨x, t⟩ ⟨hx, ht⟩
        rw [Set.mem_singleton_iff] at hx
        dsimp only at hx ⊢
        rw [hx]
        rw [uIcc_of_le hm_le] at ht
        refine hsub ⟨mem_closedTri_of_le ⟨by linarith [hx₀.1], hx₀.2⟩ ht, ?_⟩
        simp [Complex.mul_re]; linarith [hx₀.1]
      obtain ⟨u, v, hu_open, _, hx₀u, hv_sub, huv_sub⟩ :=
        generalized_tube_lemma isCompact_singleton isCompact_uIcc hS_open hprod_sub
      obtain ⟨r₀, hr₀_pos, hr₀_ball⟩ :=
        Metric.nhds_basis_closedBall.mem_iff.mp (hu_open.mem_nhds (hx₀u (Set.mem_singleton x₀)))
      have hbox_sub : ∀ p ∈ Metric.closedBall x₀ r₀ ×ˢ uIcc (-m) m,
          (p.1 : ℂ) * (1 + I * (p.2 : ℂ)) ∈ U :=
        fun _ hp => huv_sub ⟨hr₀_ball hp.1, hv_sub hp.2⟩
      have hF_cont_box : ContinuousOn (fun p : ℝ × ℝ => F ((p.1 : ℂ) * (1 + I * (p.2 : ℂ))))
          (Metric.closedBall x₀ r₀ ×ˢ uIcc (-m) m) :=
        hF_an.continuousOn.comp hmap_cont.continuousOn hbox_sub
      have hdF_cont_box : ContinuousOn (fun p : ℝ × ℝ => deriv F ((p.1 : ℂ) * (1 + I * (p.2 : ℂ))))
          (Metric.closedBall x₀ r₀ ×ˢ uIcc (-m) m) :=
        hF_an.deriv.continuousOn.comp hmap_cont.continuousOn hbox_sub
      have hHx_cont : ContinuousOn Hx.uncurry (Metric.closedBall x₀ r₀ ×ˢ uIcc (-m) m) :=
        hF_cont_box.add (hmap_cont.continuousOn.mul hdF_cont_box)
      obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ r₀).prod isCompact_uIcc).exists_bound_of_continuousOn hHx_cont
      have hH_cont_on : ∀ x ∈ Metric.closedBall x₀ r₀, ContinuousOn (H x) (uIcc (-m) m) := fun x hx =>
        continuousOn_const.mul (hF_cont_box.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => ⟨hx, ht⟩))
      have hHx_cont_x₀ : ContinuousOn (Hx x₀) (uIcc (-m) m) :=
        hHx_cont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => ⟨Metric.mem_closedBall_self hr₀_pos.le, ht⟩)
      have h_int_deriv : HasDerivAt (fun x => ∫ t in (-m)..m, H x t) (∫ t in (-m)..m, Hx x₀ t) x₀ := by
        refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
          (F := H) (F' := Hx) (x₀ := x₀) (s := Metric.ball x₀ r₀) (bound := fun _ => B)
          (Metric.ball_mem_nhds x₀ hr₀_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
        · filter_upwards [Metric.ball_mem_nhds x₀ hr₀_pos] with x hx
          exact ((hH_cont_on x (Metric.ball_subset_closedBall hx)).aestronglyMeasurable
            measurableSet_uIcc).mono_measure (Measure.restrict_mono uIoc_subset_uIcc le_rfl)
        · exact (hH_cont_on x₀ (Metric.mem_closedBall_self hr₀_pos.le)).intervalIntegrable
        · exact (hHx_cont_x₀.aestronglyMeasurable measurableSet_uIcc).mono_measure
            (Measure.restrict_mono uIoc_subset_uIcc le_rfl)
        · filter_upwards with t ht x hx
          exact hB (x, t) ⟨Metric.ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩
        · filter_upwards with t ht x hx
          have hmemU : (x : ℂ) * (1 + I * (t : ℂ)) ∈ U :=
            hbox_sub (x, t) ⟨Metric.ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩
          have hd_arg : HasDerivAt (fun s : ℝ => (s : ℂ) * (1 + I * (t : ℂ))) (1 + I * (t : ℂ)) x := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (1 + I * (t : ℂ))
          have hd_F : HasDerivAt F (deriv F ((x : ℂ) * (1 + I * (t : ℂ))))
              ((x : ℂ) * (1 + I * (t : ℂ))) := (hF_an _ hmemU).differentiableAt.hasDerivAt
          have hd_comp : HasDerivAt (fun s : ℝ => F ((s : ℂ) * (1 + I * (t : ℂ))))
              (deriv F ((x : ℂ) * (1 + I * (t : ℂ))) * (1 + I * (t : ℂ))) x :=
            hd_F.comp x hd_arg
          have hd_x : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) x := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (1 : ℂ)
          exact (hd_x.mul hd_comp).congr_deriv (by dsimp only [Hx]; ring)
      have h_ftc_t : I * (∫ t in (-m)..m, Hx x₀ t) =
          (1 + I * (m : ℂ)) * F ((x₀ : ℂ) * (1 + I * (m : ℂ))) -
            (1 - I * (m : ℂ)) * F ((x₀ : ℂ) * (1 - I * (m : ℂ))) := by
        rw [← intervalIntegral.integral_const_mul]
        let K (t : ℝ) : ℂ := (1 + I * (t : ℂ)) * F ((x₀ : ℂ) * (1 + I * (t : ℂ)))
        have hK_deriv : ∀ t ∈ uIcc (-m) m, HasDerivAt K (I * Hx x₀ t) t := fun t ht => by
          have hmemU : (x₀ : ℂ) * (1 + I * (t : ℂ)) ∈ U :=
            hbox_sub (x₀, t) ⟨Metric.mem_closedBall_self hr₀_pos.le, ht⟩
          have hd_lin : HasDerivAt (fun s : ℝ => (1 : ℂ) + I * (s : ℂ)) I t := by
            simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul I).const_add (1 : ℂ)
          have hd_arg : HasDerivAt (fun s : ℝ => (x₀ : ℂ) * (1 + I * (s : ℂ))) ((x₀ : ℂ) * I) t :=
            hd_lin.const_mul (x₀ : ℂ)
          have hd_F : HasDerivAt F (deriv F ((x₀ : ℂ) * (1 + I * (t : ℂ))))
              ((x₀ : ℂ) * (1 + I * (t : ℂ))) := (hF_an _ hmemU).differentiableAt.hasDerivAt
          exact (hd_lin.mul (hd_F.comp t hd_arg)).congr_deriv (by dsimp only [Hx, Function.comp_apply]; ring)
        have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hK_deriv
          (continuousOn_const.mul hHx_cont_x₀).intervalIntegrable
        rw [hev]
        dsimp only [K]
        simp only [Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg]
      simpa only [Φ, h_ftc_t] using h_int_deriv.const_mul I
    have hcont_p : ContinuousOn (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R) :=
      continuousOn_const.mul (hF_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
        fun x hx => mem_closedTri_of_le hx ⟨hm_le, le_rfl⟩)
    have hcont_m : ContinuousOn (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R) := by
      refine continuousOn_const.mul (hF_cont.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
        fun x hx => ?_)
      have heq : (x : ℂ) * (1 - I * (m : ℂ)) = (x : ℂ) * (1 + I * ((-m : ℝ) : ℂ)) := by push_cast; ring
      rw [heq]; exact mem_closedTri_of_le hx ⟨le_rfl, hm_le⟩
    have hΦ_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hΦ_deriv x (by simpa [uIcc_of_le hδR.le] using hx))
      ((hcont_p.mono (Icc_subset_Icc hδ.le le_rfl)).intervalIntegrable_of_Icc hδR.le |>.sub
        ((hcont_m.mono (Icc_subset_Icc hδ.le le_rfl)).intervalIntegrable_of_Icc hδR.le))
    have hΦ_eval : ∀ r : ℝ, 0 < r → Φ r = I * (∫ y in (-m * r)..(m * r), F ((r : ℂ) + (y : ℂ) * I)) :=
      fun r _ => by
        dsimp only [Φ, H]; congr 1
        have heq : (fun t : ℝ => (r : ℂ) * F ((r : ℂ) * (1 + I * (t : ℂ)))) =
            fun t : ℝ => r • F ((r : ℂ) + ((r * t : ℝ) : ℂ) * I) := by
          funext t; rw [Complex.real_smul]; congr 2; push_cast; ring
        rw [heq, intervalIntegral.integral_smul]
        have hcomp := intervalIntegral.smul_integral_comp_mul_left
          (fun y : ℝ => F ((r : ℂ) + (y : ℂ) * I)) r (a := -m) (b := m)
        simpa [show r * -m = -m * r by ring, show r * m = m * r by ring] using hcomp
    rw [intervalIntegral.integral_sub
      ((hcont_p.mono (Icc_subset_Icc hδ.le le_rfl)).intervalIntegrable_of_Icc hδR.le)
      ((hcont_m.mono (Icc_subset_Icc hδ.le le_rfl)).intervalIntegrable_of_Icc hδR.le),
      hΦ_eval R hR, hΦ_eval δ hδ] at hΦ_ftc
    have hsplit_p := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hcont_p.mono (Icc_subset_Icc le_rfl hδR.le)).intervalIntegrable_of_Icc hδ.le)
      ((hcont_p.mono (Icc_subset_Icc hδ.le le_rfl)).intervalIntegrable_of_Icc hδR.le)).symm
    have hsplit_m := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hcont_m.mono (Icc_subset_Icc le_rfl hδR.le)).intervalIntegrable_of_Icc hδ.le)
      ((hcont_m.mono (Icc_subset_Icc hδ.le le_rfl)).intervalIntegrable_of_Icc hδR.le)).symm
    unfold triIntegral
    rw [hsplit_p, hsplit_m]
    linear_combination -hΦ_ftc
  -- Step 2: Bound triIntegral F δ m ≤ C * δ → 0 as δ → 0⁺
  have hcomp : IsCompact (closedTri R m) := by
    have hclosed : IsClosed (closedTri R m) := by
      have h1 : IsClosed {z : ℂ | 0 ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
      have h2 : IsClosed {z : ℂ | z.re ≤ R} := isClosed_le Complex.continuous_re continuous_const
      have h3 : IsClosed {z : ℂ | |z.im| ≤ m * z.re} :=
        isClosed_le (continuous_abs.comp Complex.continuous_im) (continuous_const.mul Complex.continuous_re)
      have heq : closedTri R m = {z : ℂ | 0 ≤ z.re} ∩ ({z : ℂ | z.re ≤ R} ∩ {z : ℂ | |z.im| ≤ m * z.re}) := by
        ext z; simp [closedTri]
      rw [heq]
      exact h1.inter (h2.inter h3)
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨R + m * R, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    have hre_abs : |z.re| = z.re := abs_of_nonneg hz.1
    have him_le : |z.im| ≤ m * R := hz.2.2.trans (mul_le_mul_of_nonneg_left hz.2.1 hm.le)
    linarith [hz.2.1]
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hF_cont
  have hB_nn : 0 ≤ B := le_trans (norm_nonneg (F 0)) (hB 0 ⟨le_rfl, hR.le, by simp⟩)
  have hbound_δ : ∀ δ : ℝ, 0 < δ → δ < R →
      ‖triIntegral F δ m‖ ≤ (2 * ‖(1 : ℂ) + I * (m : ℂ)‖ + 2 * m) * B * δ := fun δ hδ hδR => by
    unfold triIntegral
    have h1 : ‖∫ x in (0 : ℝ)..δ, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))‖ ≤
        ‖(1 : ℂ) + I * (m : ℂ)‖ * B * δ := by
      have hnorm_eq : ‖(1 : ℂ) - I * (m : ℂ)‖ = ‖(1 : ℂ) + I * (m : ℂ)‖ := by
        have hconj : starRingEnd ℂ ((1 : ℂ) + I * (m : ℂ)) = (1 : ℂ) - I * (m : ℂ) := by simp; ring
        rw [← hconj, RCLike.norm_conj]
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := δ)
        (f := fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ))))
        (C := ‖(1 : ℂ) + I * (m : ℂ)‖ * B) fun x hx => by
          rw [uIoc_of_le hδ.le] at hx
          rw [norm_mul, hnorm_eq]
          have hmem : (x : ℂ) * (1 - I * (m : ℂ)) ∈ closedTri R m := by
            have heq : (x : ℂ) * (1 - I * (m : ℂ)) = (x : ℂ) * (1 + I * ((-m : ℝ) : ℂ)) := by push_cast; ring
            rw [heq]; exact mem_closedTri_of_le ⟨hx.1.le, hx.2.trans hδR.le⟩ ⟨le_rfl, hm_le⟩
          exact mul_le_mul_of_nonneg_left (hB _ hmem) (norm_nonneg _)
      simpa [sub_zero, abs_of_pos hδ] using hle
    have h2 : ‖I * ∫ y in (-m * δ)..(m * δ), F ((δ : ℂ) + (y : ℂ) * I)‖ ≤ 2 * m * B * δ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := -m * δ) (b := m * δ)
        (f := fun y : ℝ => F ((δ : ℂ) + (y : ℂ) * I)) (C := B) fun y hy => by
          rw [uIoc_of_le (by nlinarith)] at hy
          have hmem : (δ : ℂ) + (y : ℂ) * I ∈ closedTri R m := by
            refine ⟨by simp; linarith, by simp; linarith, ?_⟩
            simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.add_re,
              Complex.mul_re, sub_zero]
            exact abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
          exact hB _ hmem
      have habs : |m * δ - -m * δ| = 2 * m * δ := by
        rw [show m * δ - -m * δ = 2 * m * δ by ring, abs_of_pos (by positivity)]
      rw [habs] at hle; linarith
    have h3 : ‖∫ x in (0 : ℝ)..δ, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))‖ ≤
        ‖(1 : ℂ) + I * (m : ℂ)‖ * B * δ := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := δ)
        (f := fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))))
        (C := ‖(1 : ℂ) + I * (m : ℂ)‖ * B) fun x hx => by
          rw [uIoc_of_le hδ.le] at hx
          rw [norm_mul]
          have hmem : (x : ℂ) * (1 + I * (m : ℂ)) ∈ closedTri R m :=
            mem_closedTri_of_le ⟨hx.1.le, hx.2.trans hδR.le⟩ ⟨hm_le, le_rfl⟩
          exact mul_le_mul_of_nonneg_left (hB _ hmem) (norm_nonneg _)
      simpa [sub_zero, abs_of_pos hδ] using hle
    have htri : ‖((∫ x in (0 : ℝ)..δ, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) +
          I * ∫ y in (-m * δ)..(m * δ), F ((δ : ℂ) + (y : ℂ) * I)) -
          ∫ x in (0 : ℝ)..δ, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))‖ ≤
        ‖∫ x in (0 : ℝ)..δ, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))‖ +
        ‖I * ∫ y in (-m * δ)..(m * δ), F ((δ : ℂ) + (y : ℂ) * I)‖ +
        ‖∫ x in (0 : ℝ)..δ, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    linarith
  have hnorm0 : ‖triIntegral F R m‖ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    let K : ℝ := (2 * ‖(1 : ℂ) + I * (m : ℂ)‖ + 2 * m) * B + 1
    have hK_pos : 0 < K := by positivity
    let δ : ℝ := min (R / 2) (‖triIntegral F R m‖ / (2 * K))
    have hδ_pos : 0 < δ := lt_min (half_pos hR) (by positivity)
    have hδ_lt_R : δ < R := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hR)
    have hδ_le : δ ≤ ‖triIntegral F R m‖ / (2 * K) := min_le_right _ _
    have hle := hbound_δ δ hδ_pos hδ_lt_R
    rw [← htrap δ hδ_pos hδ_lt_R] at hle
    have hstrict : (2 * ‖(1 : ℂ) + I * (m : ℂ)‖ + 2 * m) * B * δ < ‖triIntegral F R m‖ := by
      calc (2 * ‖(1 : ℂ) + I * (m : ℂ)‖ + 2 * m) * B * δ
          ≤ K * δ := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hδ_pos.le
        _ ≤ K * (‖triIntegral F R m‖ / (2 * K)) := mul_le_mul_of_nonneg_left hδ_le hK_pos.le
        _ = ‖triIntegral F R m‖ / 2 := by field_simp [hK_pos.ne']
        _ < ‖triIntegral F R m‖ := half_lt_self hpos
    linarith
  exact norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))

/-! ### 4. Half-Integer `BranchPointStokesData` Assembly & Pure-Algebra `X^2 * E ↔ E` Transfer -/

private def ε₀A {ψ ω res} (h : MeromorphicBorelData ψ ω res) : ℝ := min h.ε (ω 0 / 2)

private lemma ε₀A_pos {ψ ω res} (h : MeromorphicBorelData ψ ω res) : 0 < ε₀A h :=
  lt_min h.hε_pos (half_pos h.ω_pos)

private lemma ε₀A_lt_ω {ψ ω res} (h : MeromorphicBorelData ψ ω res) (m : ℕ) : ε₀A h < ω m :=
  lt_of_le_of_lt (min_le_right _ _)
    (lt_of_lt_of_le (half_lt_self h.ω_pos) (h.ω_mono.monotone (Nat.zero_le m)))

private def dPlusA {ψ ω res} (h : MeromorphicBorelData ψ ω res) : ℂ :=
  Complex.exp (I * (h.θ : ℂ))

private def dMinusA {ψ ω res} (h : MeromorphicBorelData ψ ω res) : ℂ :=
  Complex.exp (I * ((-h.θ : ℝ) : ℂ))

private lemma dMinusA_eq {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    dMinusA h = Complex.exp (-I * (h.θ : ℂ)) := by
  unfold dMinusA; congr 1; push_cast; ring

private lemma dPlusA_re {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dPlusA h).re = Real.cos h.θ := by
  unfold dPlusA
  rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re]

private lemma dPlusA_im {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dPlusA h).im = Real.sin h.θ := by
  unfold dPlusA
  rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_im]

private lemma dMinusA_re {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dMinusA h).re = Real.cos h.θ := by
  unfold dMinusA
  rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

private lemma dMinusA_im {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (dMinusA h).im = -Real.sin h.θ := by
  unfold dMinusA
  rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private lemma cos_pos_θA {ψ ω res} (h : MeromorphicBorelData ψ ω res) : 0 < Real.cos h.θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hθ₀_lt⟩

private lemma sin_pos_θA {ψ ω res} (h : MeromorphicBorelData ψ ω res) : 0 < Real.sin h.θ :=
  Real.sin_pos_of_pos_of_lt_pi h.hθ_pos (by linarith [h.hθ_lt, h.hθ₀_lt, Real.pi_pos])

private lemma tan_lt_tanA {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    Real.tan h.θ < Real.tan h.θ₀ :=
  Real.strictMonoOn_tan ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hθ₀_lt⟩
    ⟨by linarith [h.hθ_pos, h.hθ_lt, Real.pi_pos], h.hθ₀_lt⟩ h.hθ_lt

private def wedgePlusA (θ₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < Real.tan θ₀ * z.re}

private def wedgeMinusA (θ₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -(Real.tan θ₀ * z.re) < z.im}

private lemma wedgePlusA_domain {θ₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgePlusA θ₀ ε) := by
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

private lemma wedgeMinusA_domain {θ₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgeMinusA θ₀ ε) := by
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

private lemma isPreconnected_of_star {U : Set ℂ} (hU : Domain U) (h0 : (0 : ℂ) ∈ U) :
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

private lemma wedgePlusA_containsRay {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    ContainsRay (wedgePlusA h.θ₀ (ε₀A h)) (dPlusA h) := fun v hv => by
  rcases eq_or_lt_of_le hv with rfl | hv0
  · left; simp [ε₀A_pos h]
  · right
    have hre : (dPlusA h * (v : ℂ)).re = Real.cos h.θ * v := by simp [dPlusA_re h, Complex.mul_re]
    have him : (dPlusA h * (v : ℂ)).im = Real.sin h.θ * v := by simp [dPlusA_im h, Complex.mul_im]
    refine ⟨by rw [hre]; exact mul_pos (cos_pos_θA h) hv0,
            by rw [him]; exact mul_pos (sin_pos_θA h) hv0, ?_⟩
    rw [hre, him]
    have htan : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θA h).ne']
    rw [htan]
    nlinarith [tan_lt_tanA h, mul_pos (cos_pos_θA h) hv0]

private lemma wedgeMinusA_containsRay {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    ContainsRay (wedgeMinusA h.θ₀ (ε₀A h)) (dMinusA h) := fun v hv => by
  rcases eq_or_lt_of_le hv with rfl | hv0
  · left; simp [ε₀A_pos h]
  · right
    have hre : (dMinusA h * (v : ℂ)).re = Real.cos h.θ * v := by simp [dMinusA_re h, Complex.mul_re]
    have him : (dMinusA h * (v : ℂ)).im = -(Real.sin h.θ * v) := by simp [dMinusA_im h, Complex.mul_im]
    refine ⟨by rw [hre]; exact mul_pos (cos_pos_θA h) hv0,
            by rw [him]; exact neg_lt_zero.mpr (mul_pos (sin_pos_θA h) hv0), ?_⟩
    rw [hre, him]
    have htan : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θA h).ne']
    rw [htan]
    nlinarith [tan_lt_tanA h, mul_pos (cos_pos_θA h) hv0]

private lemma wedgePlusA_subset_punctured {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    wedgePlusA h.θ₀ (ε₀A h) ⊆ puncturedWedge h.θ₀ h.ε ω := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball] at hball ⊢
      exact hball.trans_le (min_le_left _ _)
    · right
      exact ⟨hre, by rw [abs_of_pos him]; exact hlt⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).le] at hball
      linarith [ε₀A_lt_ω h m]
    · simp at him

private lemma wedgeMinusA_subset_punctured {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    wedgeMinusA h.θ₀ (ε₀A h) ⊆ puncturedWedge h.θ₀ h.ε ω := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball] at hball ⊢
      exact hball.trans_le (min_le_left _ _)
    · right
      exact ⟨hre, by rw [abs_of_neg him]; linarith⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).le] at hball
      linarith [ε₀A_lt_ω h m]
    · simp at him

/-- The Abel-convolution minor `aAbel ψ = ⟨0, abelConv ψ⟩`. -/
private def aAbel (ψ : ℂ → ℂ) : Minor := ⟨0, abelConv ψ⟩

private lemma aAbel_toSeries (ψ : ℂ → ℂ) : (aAbel ψ).toSeries = formalSeries (abelConv ψ) := rfl

private lemma aAbel_good_plus {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (aAbel ψ).Good (wedgePlusA h.θ₀ (ε₀A h)) (dPlusA h) :=
  ⟨abelConv_analyticOn (wedgePlusA_domain (ε₀A_pos h)) (h.analyticOn.mono (wedgePlusA_subset_punctured h)),
   abelConv_expType h.expType_plus⟩

private lemma aAbel_good_minus {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    (aAbel ψ).Good (wedgeMinusA h.θ₀ (ε₀A h)) (dMinusA h) :=
  ⟨abelConv_analyticOn (wedgeMinusA_domain (ε₀A_pos h)) (h.analyticOn.mono (wedgeMinusA_subset_punctured h)),
   abelConv_expType (by rw [dMinusA_eq h]; exact h.expType_minus)⟩

/-- General `HasAsympExp` for all derivatives of a `Good` minor's lateral Laplace sum. -/
private lemma minor_value_hasAsympExp (a : Minor) {U : Set ℂ} {d : ℂ}
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
    have hCu : C / u ≤ max C 0 := by
      calc C / u ≤ max C 0 / u := div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ max C 0 / 1 := div_le_div_of_nonneg_left (le_max_right _ _) zero_lt_one hu1
        _ = max C 0 := div_one _
    have hC0 : 0 ≤ C := by
      have hnn := norm_nonneg ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom)
      have h0 : 0 ≤ C / u := hnn.trans hu
      exact (div_nonneg_iff.mp h0).resolve_right (fun h => by linarith) |>.1
    rw [max_eq_left hC0] at hCu
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

/-- Pure-`Minor` Borel transfer for any `a : Minor` that is `Good` on two connected star-shaped
domains `(Up, dp)` and `(Um, dm)` (exact `PolyBorelExpr` mechanism). -/
private def polyMinorA (q : Polynomial ℂ) : Minor :=
  ⟨q.coeff 0, fun z : ℂ =>
    ∑ m ∈ Finset.range q.natDegree, (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m⟩

private lemma polyMinorA_toSeries (q : Polynomial ℂ) :
    (polyMinorA q).toSeries = (q : PowerSeries ℂ) := by
  ext n
  cases n with
  | zero => simp [polyMinorA, Minor.toSeries]
  | succ k =>
    simp only [polyMinorA, Minor.toSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe]
    have hcd : ∀ m ∈ Finset.range q.natDegree,
        ContDiffAt ℂ k (fun z : ℂ => (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) 0 :=
      fun _ _ => (analyticAt_const.mul (analyticAt_id.pow _)).contDiffAt
    rw [iteratedDeriv_fun_sum hcd]
    have hterm : ∀ m ∈ Finset.range q.natDegree,
        iteratedDeriv k (fun z : ℂ => (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) 0 =
          if m = k then q.coeff (k + 1) else 0 := fun m _ => by
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      by_cases hkm : m = k
      · subst hkm
        simp only [↓reduceIte]
        have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        field_simp [hfac]
      · simp [hkm, Ne.symm hkm]
    rw [Finset.sum_congr rfl hterm]
    by_cases hk : k < q.natDegree
    · rw [Finset.sum_ite_eq']; simp [Finset.mem_range.mpr hk]
    · have hnot : k ∉ Finset.range q.natDegree := by simpa [Finset.mem_range] using hk
      rw [Finset.sum_ite_eq', ite_eq_right_iff.mpr fun hmem => absurd hmem hnot]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

private lemma polyMinorA_good (q : Polynomial ℂ) (U : Set ℂ) (d : ℂ) :
    (polyMinorA q).Good U d := by
  refine ⟨fun z _ => by
    dsimp only [polyMinorA]
    exact Finset.analyticAt_fun_sum _ fun m _ =>
      (analyticAt_const (𝕜 := ℂ)).mul ((analyticAt_id (𝕜 := ℂ)).pow m), ?_⟩
  refine ⟨∑ m ∈ Finset.range q.natDegree, ‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖, 1,
    Finset.sum_nonneg fun _ _ => by positivity, zero_le_one, fun v hv => ?_⟩
  rw [Minor.pull]
  dsimp only [polyMinorA]
  rw [Finset.mul_sum, one_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [mul_pow, norm_mul, norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  have hpow : v ^ m / (m.factorial : ℝ) ≤ Real.exp v := Real.pow_div_factorial_le_exp v hv m
  calc ‖d‖ * (‖q.coeff (m + 1)‖ / (m.factorial : ℝ) * (‖d‖ ^ m * v ^ m))
      = (‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖) * (v ^ m / (m.factorial : ℝ)) := by rw [pow_succ']; ring
    _ ≤ (‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖) * Real.exp v :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

private lemma polyMinorA_value (q : Polynomial ℂ) {d p : ℂ} (hp : 0 < (p * d).re) :
    (polyMinorA q).value d p = q.eval p⁻¹ := by
  have hpd0 : p * d ≠ 0 := fun h0 => by simp [h0] at hp
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hpd0
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hpd0
  unfold Minor.value polyMinorA complexLaplace
  dsimp only
  have heq : (fun v : ℝ => damped (p * d)
      (Minor.pull d fun z => ∑ m ∈ Finset.range q.natDegree,
        (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) v) =
      fun v : ℝ => ∑ m ∈ Finset.range q.natDegree,
        (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
          (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m) := by
    funext v; simp only [damped, Minor.pull, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mul_pow, pow_succ']; ring
  rw [heq]
  have hi_term : ∀ m ∈ Finset.range q.natDegree,
      IntegrableOn (fun v : ℝ => (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
        (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m)) (Ioi 0) := fun m _ => by
    refine Integrable.const_mul ?_ _
    refine ((integrableOn_exp_mul_Ioi (show -((p * d).re / 2) < 0 by linarith) 0).const_mul
      ((m.factorial : ℝ) / ((p * d).re / 2) ^ m)).mono'
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.pow m)).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.le]
    have hre2 : (-(p * d) * (v : ℂ)).re = -(p * d).re * v := by simp [Complex.mul_re]; ring
    rw [hre2]
    have hpow := Real.pow_div_factorial_le_exp ((p * d).re / 2 * v) (by positivity) m
    have h1 : 0 < ((p * d).re / 2) ^ m := pow_pos (by positivity) m
    have h2 : 0 < (m.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvm : v ^ m ≤ ((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp ((p * d).re / 2 * v) := by
      calc v ^ m ≤ (Real.exp ((p * d).re / 2 * v) * m.factorial) / ((p * d).re / 2) ^ m :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc Real.exp (-(p * d).re * v) * v ^ m
        ≤ Real.exp (-(p * d).re * v) *
            (((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp ((p * d).re / 2 * v)) :=
          mul_le_mul_of_nonneg_left hvm (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp (-((p * d).re / 2) * v) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  rw [MeasureTheory.integral_finsetSum _ hi_term]
  have hsum_eq : ∑ m ∈ Finset.range q.natDegree,
      ∫ v in Ioi (0 : ℝ), (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
        (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m) =
      ∑ m ∈ Finset.range q.natDegree, q.coeff (m + 1) * p⁻¹ ^ (m + 1) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, Minor.complexLaplace_monomial m hp, mul_pow, inv_pow]
    have hm_ne : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    field_simp [hm_ne, hd0, hp0]
  rw [hsum_eq, Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  ring

private inductive PolyBorelExprA where
  | poly (q : Polynomial ℂ)
  | leaf
  | add (e f : PolyBorelExprA)
  | mul (e f : PolyBorelExprA)
  | jet (e : PolyBorelExprA)

private def PolyBorelExprA.residual (a : Minor) : PolyBorelExprA → Minor
  | .poly q => polyMinorA q
  | .leaf => a
  | .add e f => (e.residual a).plus (f.residual a)
  | .mul e f => (e.residual a).times (f.residual a)
  | .jet e => (e.residual a).jet

private def PolyBorelExprA.eval (a : Minor) (d : ℂ) : PolyBorelExprA → ℂ → ℂ
  | .poly q => fun p => q.eval p⁻¹
  | .leaf => a.value d
  | .add e f => fun p => e.eval a d p + f.eval a d p
  | .mul e f => fun p => e.eval a d p * f.eval a d p
  | .jet e => fun p => deriv (e.eval a d) p

private def PolyBorelExprA.ofBorel : BorelExpr → PolyBorelExprA
  | .const c => .poly (Polynomial.C c)
  | .leaf => .leaf
  | .add e f => .add (ofBorel e) (ofBorel f)
  | .mul e f => .mul (ofBorel e) (ofBorel f)
  | .jet e => .jet (ofBorel e)

private lemma PolyBorelExprA.ofBorel_eval (e : BorelExpr) (a : Minor) (d : ℂ) :
    (ofBorel e).eval a d = e.eval a d := by
  induction e with
  | const c => funext p; simp [ofBorel, eval, BorelExpr.eval]
  | leaf => rfl
  | add e f he hf => funext p; simp [ofBorel, eval, BorelExpr.eval, he, hf]
  | mul e f he hf => funext p; simp [ofBorel, eval, BorelExpr.eval, he, hf]
  | jet e he => funext p; simp [ofBorel, eval, BorelExpr.eval, he]

private lemma PolyBorelExprA.ofBorel_jetIter (j : ℕ) :
    ofBorel (Nat.iterate BorelExpr.jet j BorelExpr.leaf) = Nat.iterate .jet j .leaf := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ofBorel, ih]

private lemma PolyBorelExprA.represents (e : PolyBorelExprA) {U : Set ℂ} {d : ℂ} (hU : Domain U)
    (ray : ContainsRay U d) {a : Minor} (ha : a.Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[BorelStokesVandermonde.far d] (e.residual a).value d := by
  induction e with
  | poly q =>
    refine ⟨polyMinorA_good q U d, ?_⟩
    filter_upwards [eventually_bound_far d 0] with p hp
    exact (polyMinorA_value q hp).symm
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

private lemma PolyBorelExprA.exists_of_mvPoly {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    ∃ e : PolyBorelExprA,
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d →
        (e.residual a).toSeries =
          MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (fun j : Fin (r + 1) => d_u^[j.val] a.toSeries) Q) ∧
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d → 0 < d.re →
        ∀ᶠ u : ℝ in atTop,
          e.eval a d (u : ℂ) =
            MvPolynomial.eval
              (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => a.value d (t : ℂ)) u)
              (evalU Q (u : ℂ)⁻¹)) := by
  induction Q using MvPolynomial.induction_on with
  | C q =>
    refine ⟨.poly q, fun _ _ _ _ _ _ => by simp [residual, polyMinorA_toSeries],
      fun _ _ _ _ _ _ _ => .of_forall fun u => by simp [eval, evalU]⟩
  | add Q₁ Q₂ h₁ h₂ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    obtain ⟨e₂, hs₂, he₂⟩ := h₂
    refine ⟨.add e₁ e₂, fun U d a hU ray ha => ?_, fun U d a hU ray ha hd => ?_⟩
    · have hg₁ := (e₁.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      have hg₂ := (e₂.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      rw [residual, Minor.toSeries_plus hg₁ hg₂, hs₁ U d a hU ray ha, hs₂ U d a hU ray ha, MvPolynomial.eval₂_add]
    · filter_upwards [he₁ U d a hU ray ha hd, he₂ U d a hU ray ha hd] with u hu₁ hu₂
      simp [eval, evalU, hu₁, hu₂]
  | mul_X Q₁ j h₁ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    let ej : PolyBorelExprA := Nat.iterate PolyBorelExprA.jet j.val PolyBorelExprA.leaf
    refine ⟨.mul e₁ ej, fun U d a hU ray ha => ?_, fun U d a hU ray ha hd => ?_⟩
    · have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
      have hg₁ := (e₁.represents hU ray ha).1.1 0 h0
      have hgj := (ej.represents hU ray ha).1.1 0 h0
      rw [residual, Minor.toSeries_times hg₁ hgj, hs₁ U d a hU ray ha]
      have hj_ser : ∀ k : ℕ, ((Nat.iterate PolyBorelExprA.jet k PolyBorelExprA.leaf).residual a).toSeries =
          d_u^[k] a.toSeries := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          have hgk := ((Nat.iterate PolyBorelExprA.jet k PolyBorelExprA.leaf).represents hU ray ha).1.1 0 h0
          rw [Function.iterate_succ_apply' PolyBorelExprA.jet k PolyBorelExprA.leaf,
            Function.iterate_succ_apply' d_u k a.toSeries]
          exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
      rw [hj_ser j.val, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    · have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU ray ha hd j.val).1
      filter_upwards [he₁ U d a hU ray ha hd, hjet_eq] with u hu₁ huj
      have heval_eq : ej.eval a d (u : ℂ) =
          (Nat.iterate BorelExpr.jet j.val BorelExpr.leaf).eval a d (u : ℂ) := by
        dsimp only [ej]; rw [← ofBorel_jetIter, ofBorel_eval]
      simp only [eval, evalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hu₁ ⊢
      rw [heval_eq, hu₁, huj]

private lemma analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroA {U : Set ℂ} {f : ℂ → ℂ}
    (hpre : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) : Set.EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz
    simpa [smul_eq_mul] using hz
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
    rw [Finset.sum_congr rfl hterm]
    simp
  have hzero := hderiv n
  rw [hdn] at hzero
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) hzero

private def revPolyA (N : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k)

private def maxUDegA {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) : ℕ :=
  P.support.sup fun α => (P.coeff α).natDegree

private lemma natDegree_le_maxUDegA {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (α : Fin (r + 1) →₀ ℕ) : (P.coeff α).natDegree ≤ maxUDegA P := by
  by_cases hα : α ∈ P.support
  · exact Finset.le_sup (f := fun β => (P.coeff β).natDegree) hα
  · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.natDegree_zero]; exact Nat.zero_le _

private def revMvPolyA {r : ℕ} (N : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (revPolyA N (P.coeff α))

private lemma revPolyA_eval_inv {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N)
    {u : ℂ} (hu : u ≠ 0) : (revPolyA N p).eval u⁻¹ = u⁻¹ ^ N * p.eval u := by
  have hsum := Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_rhs => rw [hsum]
  change Polynomial.evalRingHom u⁻¹ (revPolyA N p) = u⁻¹ ^ N * Polynomial.evalRingHom u _
  simp only [revPolyA, map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    map_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have heq : u⁻¹ ^ (N - k) = u⁻¹ ^ N * u ^ k := by
    calc u⁻¹ ^ (N - k) = u⁻¹ ^ (N - k) * (u⁻¹ ^ k * u ^ k) := by
          rw [← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
      _ = (u⁻¹ ^ (N - k) * u⁻¹ ^ k) * u ^ k := by ring
      _ = u⁻¹ ^ N * u ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_le]
  rw [heq]; ring

private lemma evalU_revMvPolyA {r N : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hN : ∀ α, (P.coeff α).natDegree ≤ N) {u : ℂ} (hu : u ≠ 0) :
    evalU (revMvPolyA N P) u⁻¹ = (u⁻¹ ^ N) • evalU P u := by
  classical
  ext α
  rw [evalU, evalU, MvPolynomial.coeff_map, MvPolynomial.coeff_smul, MvPolynomial.coeff_map,
    Polynomial.coe_evalRingHom, Polynomial.coe_evalRingHom, smul_eq_mul]
  unfold revMvPolyA
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp only [↓reduceIte]; exact revPolyA_eval_inv (P.coeff α) (hN α) hu
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.eval_zero, mul_zero]
    have h0 : (∑ x ∈ P.support, if x = α then revPolyA N (P.coeff x) else 0) = 0 :=
      Finset.sum_eq_zero fun β hβ => by simp [show β ≠ α from fun h => hα (h ▸ hβ)]
    rw [h0, Polynomial.eval_zero]

private lemma single_mul_polyToLaurentA {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N) :
    HahnSeries.single (N : ℤ) (1 : ℂ) * polyToLaurent p =
      (((revPolyA N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hsum := Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_lhs => rw [hsum]
  have halg : ∀ c : ℂ, algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := HahnSeries.ofPowerSeries_C
  have hu_pow : ∀ k : ℕ, uLaurent ^ k = HahnSeries.single (-(k : ℤ)) (1 : ℂ) := fun k => by
    induction k with
    | zero => simp [uLaurent]
    | succ k ih =>
      rw [pow_succ, ih, uLaurent, HahnSeries.single_mul_single, one_mul]
      rw [show -(k : ℤ) + (-1 : ℤ) = -((k + 1 : ℕ) : ℤ) by omega]
  have hL : HahnSeries.single (N : ℤ) (1 : ℂ) *
      polyToLaurent (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k) =
      ∑ k ∈ Finset.range (N + 1), HahnSeries.single (N : ℤ) (1 : ℂ) *
        (HahnSeries.C (p.coeff k) * uLaurent ^ k) := by
    simp only [polyToLaurent, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul,
      map_pow, Polynomial.aeval_C, Polynomial.aeval_X, halg, Finset.mul_sum]
  have hR : (((revPolyA N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ∑ k ∈ Finset.range (N + 1),
        HahnSeries.C (p.coeff k) * ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) := by
    unfold revPolyA
    change HahnSeries.ofPowerSeries ℤ ℂ
      (Polynomial.coeToPowerSeries.ringHom
        (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k))) = _
    simp only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, HahnSeries.ofPowerSeries_C, Polynomial.coe_X]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hu_pow k]
  have hX : ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) =
      HahnSeries.single ((N - k : ℕ) : ℤ) (1 : ℂ) := by
    rw [← PowerSeries.coe_pow, HahnSeries.ofPowerSeries_X_pow]
  rw [hX, ← mul_assoc, mul_comm (HahnSeries.single (N : ℤ) 1) (HahnSeries.C (p.coeff k)),
    mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (N : ℤ) + -(k : ℤ) = ((N - k : ℕ) : ℤ) by omega, HahnSeries.C_apply,
    HahnSeries.single_mul_single]

private lemma abelConv_borel_transfer {ψ ω res} (h : MeromorphicBorelData ψ ω res)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries (abelConv ψ)) P = 0) :
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (aAbel ψ).value (dPlusA h) (t : ℂ)) u)
        (evalU P (u : ℂ)) = 0) ∧
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (aAbel ψ).value (dMinusA h) (t : ℂ)) u)
        (evalU P (u : ℂ)) = 0) := by
  let N := maxUDegA P
  let Q := revMvPolyA N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDegA P
  have hQ0 : MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
      (fun j : Fin (r + 1) => d_u^[j.val] (formalSeries (abelConv ψ))) Q = 0 := by
    have hlink : HahnSeries.single (N : ℤ) (1 : ℂ) * formalEvalPoly (formalSeries (abelConv ψ)) P =
        ((MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
          (fun j : Fin (r + 1) => d_u^[j.val] (formalSeries (abelConv ψ))) Q : PowerSeries ℂ) : LaurentSeries ℂ) := by
      have hP_sum := MvPolynomial.as_sum P
      conv_lhs => arg 2; unfold formalEvalPoly; rw [hP_sum]
      unfold Q revMvPolyA
      rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
      simp_rw [MvPolynomial.eval₂_monomial]
      change ∑ α ∈ P.support, HahnSeries.single (N : ℤ) 1 *
          (polyToLaurent (P.coeff α) * α.prod fun i e =>
            ((d_u^[i.val] (formalSeries (abelConv ψ)) : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
        HahnSeries.ofPowerSeries ℤ ℂ
          (∑ α ∈ P.support, Polynomial.coeToPowerSeries.ringHom (revPolyA N (P.coeff α)) *
            α.prod fun i e => (d_u^[i.val] (formalSeries (abelConv ψ))) ^ e)
      rw [map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hpow_eq : (α.prod fun i e => ((d_u^[i.val] (formalSeries (abelConv ψ)) : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
          ((α.prod fun i e => (d_u^[i.val] (formalSeries (abelConv ψ))) ^ e : PowerSeries ℂ) : LaurentSeries ℂ) := by
        simp only [Finsupp.prod, map_prod, map_pow]
      rw [hpow_eq, ← mul_assoc, single_mul_polyToLaurentA (P.coeff α) (hNP α), map_mul,
        Polynomial.coeToPowerSeries.ringHom_apply]
    rw [hP, mul_zero] at hlink
    exact HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (hlink.symm.trans (map_zero _).symm)
  let Up := wedgePlusA h.θ₀ (ε₀A h)
  let Um := wedgeMinusA h.θ₀ (ε₀A h)
  have hUp_dom : Domain Up := wedgePlusA_domain (ε₀A_pos h)
  have hUm_dom : Domain Um := wedgeMinusA_domain (ε₀A_pos h)
  have hrayP : ContainsRay Up (dPlusA h) := wedgePlusA_containsRay h
  have hrayM : ContainsRay Um (dMinusA h) := wedgeMinusA_containsRay h
  have hgoodP : (aAbel ψ).Good Up (dPlusA h) := aAbel_good_plus h
  have hgoodM : (aAbel ψ).Good Um (dMinusA h) := aAbel_good_minus h
  have hreP : 0 < (dPlusA h).re := by rw [dPlusA_re h]; exact cos_pos_θA h
  have hreM : 0 < (dMinusA h).re := by rw [dMinusA_re h]; exact cos_pos_θA h
  obtain ⟨e, hs, he⟩ := PolyBorelExprA.exists_of_mvPoly Q
  have hres_series : (e.residual (aAbel ψ)).toSeries = 0 := by
    rw [hs Up (dPlusA h) (aAbel ψ) hUp_dom hrayP hgoodP, aAbel_toSeries, hQ0]
  have hatom : (e.residual (aAbel ψ)).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series; simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual (aAbel ψ)).density 0 = 0 := fun k => by
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series; simpa [Minor.toSeries] using this
  have h0P : (0 : ℂ) ∈ Up := by simpa using hrayP 0 le_rfl
  have h0M : (0 : ℂ) ∈ Um := by simpa using hrayM 0 le_rfl
  have hplus_dens : Set.EqOn (e.residual (aAbel ψ)).density 0 Up :=
    analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroA (isPreconnected_of_star hUp_dom h0P) h0P
      (e.represents hUp_dom hrayP hgoodP).1.1 hderiv_zero
  have hminus_dens : Set.EqOn (e.residual (aAbel ψ)).density 0 Um :=
    analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroA (isPreconnected_of_star hUm_dom h0M) h0M
      (e.represents hUm_dom hrayM hgoodM).1.1 hderiv_zero
  have ht_far : ∀ {d : ℂ}, 0 < d.re → Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far d) :=
    fun {d} hd => by
      rw [BorelStokesVandermonde.far, tendsto_comap_iff]
      have heq : ((fun p : ℂ => (p * d).re) ∘ fun u : ℝ => (u : ℂ)) = fun u : ℝ => u * d.re := by
        funext u; simp [Complex.mul_re]
      rw [heq]; exact tendsto_id.atTop_mul_const hd
  constructor
  · have hrep := (ht_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
    filter_upwards [hrep, he Up (dPlusA h) (aAbel ψ) hUp_dom hrayP hgoodP hreP,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aAbel ψ).value (dPlusA h) (t : ℂ)) u)
        (evalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      simp [damped, Minor.pull, hplus_dens (hrayP v hv.le)]
    rw [show Q = revMvPolyA N P from rfl, evalU_revMvPolyA P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))
  · have hrep := (ht_far hreM).eventually (e.represents hUm_dom hrayM hgoodM).2
    filter_upwards [hrep, he Um (dMinusA h) (aAbel ψ) hUm_dom hrayM hgoodM hreM,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aAbel ψ).value (dMinusA h) (t : ℂ)) u)
        (evalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      simp [damped, Minor.pull, hminus_dens (hrayM v hv.le)]
    rw [show Q = revMvPolyA N P from rfl, evalU_revMvPolyA P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))

/-! #### 4B. Differentiated Ray Laplace Integrals & Half-Integer Stokes Jump -/

private def halfRayDeriv (ψ : ℂ → ℂ) (d : ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in Ioi (0 : ℝ),
      (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
        (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ))

private lemma integrableOn_rpow_nat_add_half_mul_exp (j : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t)) (Ioi (0 : ℝ)) volume := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t))
      (Ioc (0 : ℝ) 1) volume := by
    have hdom : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) volume :=
      integrableOn_const (by simp)
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (Set.mem_Ioc.mp ht).1.ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (Real.exp_pos _).le)]
      have hrp : t ^ ((j : ℝ) + 1 / 2) ≤ 1 := Real.rpow_le_one ht0.le ht.2 (by positivity)
      have hexp : Real.exp (-r * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t) ≤ 1 * 1 :=
            mul_le_mul hrp hexp (Real.exp_pos _).le zero_le_one
        _ = 1 := mul_one 1
  have h2 : IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t))
      (Ioi (1 : ℝ)) volume := by
    have hdom : IntegrableOn (fun t : ℝ =>
        (((j + 1).factorial : ℝ) / (r / 2) ^ (j + 1)) * Real.exp (-(r / 2) * t))
        (Ioi (1 : ℝ)) volume :=
      (integrableOn_exp_mul_Ioi (by linarith) 1).const_mul _
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (lt_trans zero_lt_one ht).ne').mul ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (Real.exp_pos _).le)]
      have hrp : t ^ ((j : ℝ) + 1 / 2) ≤ t ^ (j + 1) := by
        calc t ^ ((j : ℝ) + 1 / 2) ≤ t ^ ((j + 1 : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le ht1 (by push_cast; linarith)
          _ = t ^ (j + 1) := Real.rpow_natCast t (j + 1)
      have hterm := Real.pow_div_factorial_le_exp ((r / 2) * t) (by positivity) (j + 1)
      have hfac : (0 : ℝ) < ((j + 1).factorial : ℝ) := by positivity
      have hrp2 : (0 : ℝ) < (r / 2) ^ (j + 1) := by positivity
      rw [mul_pow, div_le_iff₀ hfac] at hterm
      have hpow_le : t ^ (j + 1) * Real.exp (-((r / 2) * t)) ≤
          ((j + 1).factorial : ℝ) / (r / 2) ^ (j + 1) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hrp2]
        nlinarith
      have hsplit : Real.exp (-r * t) = Real.exp (-((r / 2) * t)) * Real.exp (-(r / 2) * t) := by
        rw [← Real.exp_add]; congr 1; ring
      calc t ^ ((j : ℝ) + 1 / 2) * Real.exp (-r * t)
          ≤ t ^ (j + 1) * Real.exp (-r * t) := mul_le_mul_of_nonneg_right hrp (Real.exp_pos _).le
        _ = (t ^ (j + 1) * Real.exp (-((r / 2) * t))) * Real.exp (-(r / 2) * t) := by rw [hsplit]; ring
        _ ≤ (((j + 1).factorial : ℝ) / (r / 2) ^ (j + 1)) * Real.exp (-(r / 2) * t) :=
            mul_le_mul_of_nonneg_right hpow_le (Real.exp_pos _).le
  have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hunion]
  exact h1.union h2

private lemma halfRayDeriv_integrable {ψ : ℂ → ℂ} {σ : ℝ} (hσ : |σ| < Real.pi / 2)
    (hcont : ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0))
    {C D : ℝ} (_hC : 0 ≤ C) (hbd : ∀ t ≥ 0, ‖Minor.pull (Complex.exp (I * (σ : ℂ))) ψ t‖ ≤ C * Real.exp (D * t))
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
    (integrableOn_rpow_nat_add_half_mul_exp j (by linarith)).const_mul C
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have heq : EqOn (fun t : ℝ =>
        (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
          (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ)))
        (fun t : ℝ =>
          (-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) *
            (Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ)) * Minor.pull d ψ t)
        (Ioi 0) := fun t ht => by
      dsimp only [d, Minor.pull]; rw [cpow_half_exp_mul hσ ht]; ring
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
      dsimp only [d, Minor.pull]; rw [cpow_half_exp_mul hσ ht0]; ring
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

private lemma iteratedDeriv_halfRayLaplace_eq {ψ : ℂ → ℂ} {σ : ℝ} (hσ : |σ| < Real.pi / 2)
    (hcont : ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0))
    (hexp : ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ)) (j : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (halfRayLaplace ψ (Complex.exp (I * (σ : ℂ)))) u =
        halfRayDeriv ψ (Complex.exp (I * (σ : ℂ))) j u := by
  let d : ℂ := Complex.exp (I * (σ : ℂ))
  have hcos : 0 < Real.cos σ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hσ)
  obtain ⟨C, D, hC, hD, hbd⟩ := hexp
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.norm_exp_ofReal_mul_I σ
  have hd_re : d.re = Real.cos σ := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.exp_ofReal_mul_I_re σ
  have hstep : ∀ (k : ℕ) {u₀ : ℝ}, (D + 1) / Real.cos σ < u₀ →
      HasDerivAt (halfRayDeriv ψ d k) (halfRayDeriv ψ d (k + 1) u₀) u₀ := fun k {u₀} hu₀ => by
    have hu₀_cos : D + 1 < u₀ * Real.cos σ := (div_lt_iff₀ hcos).mp hu₀
    let r₀ : ℝ := (D + 1 / 2) / Real.cos σ
    have hr₀_lt : r₀ < u₀ := by
      dsimp only [r₀]; rw [div_lt_iff₀ hcos]; linarith
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
      have hu_cos : D < u * Real.cos σ := by
        have h1 : D + 1 / 2 < u * Real.cos σ := (div_lt_iff₀ hcos).mp hu
        linarith
      exact (halfRayDeriv_integrable hσ hcont hC hbd k hu_cos).aestronglyMeasurable
    have hF_int : Integrable (F u₀) (volume.restrict (Ioi (0 : ℝ))) :=
      halfRayDeriv_integrable hσ hcont hC hbd k (by linarith)
    have hF'_meas : AEStronglyMeasurable (F' u₀) (volume.restrict (Ioi (0 : ℝ))) :=
      (halfRayDeriv_integrable hσ hcont hC hbd (k + 1) (by linarith)).aestronglyMeasurable
    have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ u ∈ s, ‖F' u t‖ ≤ bound t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht u hu
      have ht0 : 0 < t := ht
      have hu_cos : D + 1 / 2 < u * Real.cos σ := (div_lt_iff₀ hcos).mp hu
      have hrew : F' u t = (-(d * (t : ℂ))) ^ (k + 1) * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) *
          Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * Minor.pull d ψ t := by
        dsimp only [F', d, Minor.pull]; rw [cpow_half_exp_mul hσ ht0]; ring
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
    have hint_der := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
      hbound ((integrableOn_rpow_nat_add_half_mul_exp (k + 1) (by norm_num)).const_mul C) hdiff).2
    exact hint_der.const_mul (((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹)
  -- Induction on j for u > (D + 1) / cos σ
  have hall : ∀ k : ℕ, ∀ u : ℝ, (D + 1) / Real.cos σ < u →
      iteratedDeriv k (halfRayLaplace ψ d) u = halfRayDeriv ψ d k u := fun k => by
    induction k with
    | zero => intro u _; simp [halfRayLaplace, halfRayDeriv]
    | succ k ih =>
      intro u hu
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (halfRayLaplace ψ d) =ᶠ[𝓝 u] halfRayDeriv ψ d k :=
        Filter.eventually_of_mem (Ioi_mem_nhds hu) fun x hx => ih x hx
      rw [hev.deriv_eq, (hstep k hu).deriv]
  filter_upwards [eventually_gt_atTop ((D + 1) / Real.cos σ)] with u hu
  exact hall j u hu

/-- Along a flanking ray `σ` with `|σ| < π/2`, `halfRayLaplace` is eventually `ContDiffAt ℝ j`
and its `j`-th derivative equals `halfRayDeriv`. -/
private lemma contDiffAt_halfRayLaplace {ψ : ℂ → ℂ} {σ : ℝ} (hσ : |σ| < Real.pi / 2)
    (hcont : ContinuousOn (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ) (Ioi 0))
    (hexp : ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) ψ)) (j : ℕ) :
    ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ j (halfRayLaplace ψ (Complex.exp (I * (σ : ℂ)))) u := by
  let d : ℂ := Complex.exp (I * (σ : ℂ))
  have hcos : 0 < Real.cos σ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hσ)
  obtain ⟨C, D, hC, _, hbd⟩ := hexp
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.norm_exp_ofReal_mul_I σ
  have hd_re : d.re = Real.cos σ := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.exp_ofReal_mul_I_re σ
  let R₀ : ℝ := (D + 1) / Real.cos σ
  have hstep : ∀ (k : ℕ) {u₀ : ℝ}, R₀ < u₀ →
      HasDerivAt (halfRayDeriv ψ d k) (halfRayDeriv ψ d (k + 1) u₀) u₀ := fun k {u₀} hu₀ => by
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
      exact (halfRayDeriv_integrable hσ hcont hC hbd k (by linarith)).aestronglyMeasurable
    have hF_int : Integrable (F u₀) (volume.restrict (Ioi (0 : ℝ))) :=
      halfRayDeriv_integrable hσ hcont hC hbd k (by linarith)
    have hF'_meas : AEStronglyMeasurable (F' u₀) (volume.restrict (Ioi (0 : ℝ))) :=
      (halfRayDeriv_integrable hσ hcont hC hbd (k + 1) (by linarith)).aestronglyMeasurable
    have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ u ∈ s, ‖F' u t‖ ≤ bound t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht u hu
      have ht0 : 0 < t := ht
      have hu_cos : D + 1 / 2 < u * Real.cos σ := (div_lt_iff₀ hcos).mp hu
      have hrew : F' u t = (-(d * (t : ℂ))) ^ (k + 1) * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) *
          Complex.exp (I * ((σ / 2 : ℝ) : ℂ)) * ((Real.sqrt t : ℝ) : ℂ) * Minor.pull d ψ t := by
        dsimp only [F', d, Minor.pull]; rw [cpow_half_exp_mul hσ ht0]; ring
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
      hbound ((integrableOn_rpow_nat_add_half_mul_exp (k + 1) (by norm_num)).const_mul C) hdiff).2.const_mul _
  have hcd : ∀ m k : ℕ, ∀ u : ℝ, R₀ < u → ContDiffAt ℝ m (halfRayDeriv ψ d k) u := by
    intro m
    induction m with
    | zero =>
      intro k u hu
      exact contDiffAt_zero.mpr ⟨Ioi R₀, Ioi_mem_nhds hu,
        fun y hy => (hstep k hy).continuousAt.continuousWithinAt⟩
    | succ m ih =>
      intro k u hu
      rw [Nat.cast_add, Nat.cast_one, contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (halfRayDeriv ψ d (k + 1) y),
        ⟨Ioi R₀, Ioi_mem_nhds hu, fun y hy => (hstep k hy).hasFDerivAt⟩, ?_⟩
      · exact (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)).contDiff.contDiffAt.comp u
          (ih (k + 1) u hu)
  have h0eq : halfRayLaplace ψ d = halfRayDeriv ψ d 0 := by
    funext u; simp [halfRayLaplace, halfRayDeriv]
  rw [h0eq]
  filter_upwards [eventually_gt_atTop R₀] with u hu
  exact hcd j 0 u hu

/-- Half-integer Stokes residue amplitude `c_m = 2 i √(π ω_m) r_m`. -/
@[expose] def halfStokesCoeff (ω : ℕ → ℝ) (res : ℕ → ℂ) (m : ℕ) : ℂ :=
  2 * I * ((Real.sqrt (Real.pi * ω m) : ℝ) : ℂ) * res m

private lemma continuousAt_cpow_half_zero :
    ContinuousAt (fun z : ℂ => z ^ ((1 / 2 : ℝ) : ℂ)) 0 := by
  rw [ContinuousAt, Complex.zero_cpow (by norm_num : ((1 / 2 : ℝ) : ℂ) ≠ 0),
    tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : (fun z : ℂ => ‖z ^ ((1 / 2 : ℝ) : ℂ)‖) = fun z : ℂ => ‖z‖ ^ (1 / 2 : ℝ) := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp
    · rw [Complex.norm_cpow_of_ne_zero hz]; simp
  rw [hnorm]
  have h0 : (0 : ℝ) = ‖(0 : ℂ)‖ ^ (1 / 2 : ℝ) := by simp
  rw [h0]
  exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.tendsto).comp
    continuous_norm.continuousAt.tendsto

private lemma continuousOn_cpow_half_re_nonneg :
    ContinuousOn (fun z : ℂ => z ^ ((1 / 2 : ℝ) : ℂ)) {z : ℂ | 0 ≤ z.re} := by
  intro z hz
  change 0 ≤ z.re at hz
  by_cases hz0 : z = 0
  · subst hz0; exact continuousAt_cpow_half_zero.continuousWithinAt
  · have hslit : z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      rcases eq_or_lt_of_le hz with hre0 | hre_pos
      · right
        intro him0
        exact hz0 (Complex.ext hre0.symm him0)
      · exact Or.inl hre_pos
    exact ((hasDerivAt_id z).cpow_const hslit).continuousAt.continuousWithinAt

private def TriBdIntegrableA (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R

private lemma triBdIntegrableA_of_continuousOn {F : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntegrableA F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma triIntegral_addA {F G : ℂ → ℂ} {R m : ℝ}
    (hF : TriBdIntegrableA F R m) (hG : TriBdIntegrableA G R m) :
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
    intervalIntegral.integral_add hF.2.2 hG.2.2]
  ring

private lemma triIntegral_const_mulA (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) := funext fun _ => by ring
  have h3 : (fun x : ℝ => (1 + I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) := funext fun _ => by ring
  rw [h1, h3]
  simp_rw [intervalIntegral.integral_const_mul]
  ring

private lemma triIntegral_sumA {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntegrableA (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert a s ha ih =>
    have ha_int : TriBdIntegrableA (F a) R m := hF a (Finset.mem_insert_self a s)
    have hs_int : ∀ i ∈ s, TriBdIntegrableA (F i) R m :=
      fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hsum_int : TriBdIntegrableA (fun z => ∑ i ∈ s, F i z) R m := by
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
    rw [hpt, triIntegral_addA ha_int hsum_int, ih hs_int, Finset.sum_insert ha]

private lemma triIntegral_congrA {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
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

private lemma poleSub_analyticOn_cutOpenA {ψ ω res} (h : MeromorphicBorelData ψ ω res) (n : ℕ) :
    let Sn (z : ℂ) : ℂ := ∑ k ∈ Finset.range (n + 1), res k / (z - (ω k : ℂ))
    let Pset : Set ℂ := (fun k : ℕ => (ω k : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      by classical exact if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => ψ w - Sn w) else ψ z - Sn z
    AnalyticOnNhd ℂ ψn (borelWedge h.θ₀ (ε₀A h) ∩ {z : ℂ | z.re < ω (n + 1)}) := by
  classical
  intro Sn Pset ψn
  let Un : Set ℂ := borelWedge h.θ₀ (ε₀A h) ∩ {z : ℂ | z.re < ω (n + 1)}
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

private lemma halfRayDeriv_stokes_jump {ψ ω res} (h : MeromorphicBorelData ψ ω res) (n j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖halfRayDeriv ψ (dMinusA h) j u - halfRayDeriv ψ (dPlusA h) j u -
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
  have hcos : 0 < Real.cos h.θ := cos_pos_θA h
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
  -- Step 1: Exact triangle residue formula for G u z
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
    let Un : Set ℂ := borelWedge h.θ₀ (ε₀A h) ∩ {z : ℂ | z.re < ω (n + 1)}
    have hUn_open : IsOpen Un :=
      (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im)
          (continuous_const.mul Complex.continuous_re)))).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hψn_an : AnalyticOnNhd ℂ ψn Un := poleSub_analyticOn_cutOpenA h n
    have htri_sub_Un : closedTri R mθ ⊆ Un := by
      intro z hz
      refine ⟨?_, lt_of_le_of_lt hz.2.1 (hR_lt_ω (n + 1) le_rfl)⟩
      rcases eq_or_lt_of_le hz.1 with hre0 | hre_pos
      · left
        have him0 : z.im = 0 := abs_nonpos_iff.mp (by simpa [← hre0] using hz.2.2)
        have hz0 : z = 0 := Complex.ext hre0.symm him0
        simpa [hz0, Metric.mem_ball, dist_zero_right] using ε₀A_pos h
      · right
        exact ⟨hre_pos, lt_of_le_of_lt hz.2.2 (mul_lt_mul_of_pos_right (tan_lt_tanA h) hre_pos)⟩
    have hpref_cont : ContinuousOn (pref u) (closedTri R mθ) := by
      have hsub_re : closedTri R mθ ⊆ {z : ℂ | 0 ≤ z.re} := fun z hz => hz.1
      exact (((continuousOn_const.mul (continuous_id.neg.pow j).continuousOn).mul
        (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (continuousOn_cpow_half_re_nonneg.mono hsub_re))
    have hpref_diff_slit : DifferentiableOn ℂ (pref u) Complex.slitPlane := by
      intro z hz
      have hcp : DifferentiableAt ℂ (fun w : ℂ => w ^ ((1 / 2 : ℝ) : ℂ)) z :=
        ((hasDerivAt_id z).cpow_const hz).differentiableAt
      exact ((((differentiableAt_const _).mul (differentiableAt_id.neg.pow j)).mul
        ((differentiableAt_const _).mul differentiableAt_id).cexp).mul hcp).differentiableWithinAt
    have hpref_an_slit : AnalyticOnNhd ℂ (pref u) Complex.slitPlane :=
      hpref_diff_slit.analyticOnNhd Complex.isOpen_slitPlane
    -- Part A: triIntegral (pref u * ψn) = 0
    have htri_ψn : triIntegral (fun z => pref u z * ψn z) R mθ = 0 := by
      refine triIntegral_eq_zero_of_analyticOn_pos hR_pos hm_pos (hUn_open.inter Complex.isOpen_slitPlane)
        (fun z hz => ⟨htri_sub_Un hz.1, Complex.mem_slitPlane_iff.mpr (Or.inl hz.2)⟩)
        (fun z hz => (hpref_an_slit z hz.2).mul (hψn_an z hz.1))
        (hpref_cont.mul (hψn_an.continuousOn.mono htri_sub_Un))
    -- Part B: for each k < n + 1, triIntegral (pref u * (res k / (z - ω k))) = exact residue
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
          have hne0 : (0 : ℂ) ≠ (ω k : ℂ) := by
            intro h0; exact (hω_pos k).ne' (by exact_mod_cast h0.symm)
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
        rw [triIntegral_const_mulA, triIntegral_inv_sub (hω_pos k) (hω_lt_R k hk_le) hm_pos]
      have h_slope_int : TriBdIntegrableA (dslope gk (ω k : ℂ)) R mθ := by
        refine triBdIntegrableA_of_continuousOn hR_pos.le hm_pos.le
          (hslope_cont_tri.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx => ?_)
          (hslope_cont_tri.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
            fun y hy => ⟨by simp [hR_pos.le], by simp, by
              rw [show -mθ * R = -(mθ * R) by ring] at hy; simpa [R, mθ] using abs_le.mpr hy⟩)
          (hslope_cont_tri.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx =>
            mem_closedTri_of_le hx ⟨by linarith, le_rfl⟩)
        have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by push_cast; ring
        rw [heq]; exact mem_closedTri_of_le hx ⟨le_rfl, by linarith⟩
      have h_inv_int : TriBdIntegrableA (fun z => gk (ω k : ℂ) * (z - (ω k : ℂ))⁻¹) R mθ :=
        triBdIntegrableA_of_continuousOn hR_pos.le hm_pos.le
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
        rw [dslope_of_ne gk hz, slope_def_field]
        dsimp only [termK, gk]
        field_simp [hsub]; ring
      rw [triIntegral_congrA (G := fun z => dslope gk (ω k : ℂ) z + gk (ω k : ℂ) * (z - (ω k : ℂ))⁻¹)
            hR_pos.le hm_pos.le
            (fun x _ => h_pt _ (h_avoid.1 x k))
            (fun y _ => h_pt _ (h_avoid.2.2 y k))
            (fun x _ => h_pt _ (h_avoid.2.1 x k)),
          triIntegral_addA h_slope_int h_inv_int, htri_slope, zero_add, htri_inv]
      -- Simplify gk (ω k) * (2 * π * I) = halfStokesCoeff ω res k * (-ω k)^j * exp (-ω k * u)
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
    have h_Fψ_int : TriBdIntegrableA (fun z => pref u z * ψn z) R mθ := by
      have hcont_all : ContinuousOn (fun z => pref u z * ψn z) (closedTri R mθ) :=
        hpref_cont.mul (hψn_an.continuousOn.mono htri_sub_Un)
      refine triBdIntegrableA_of_continuousOn hR_pos.le hm_pos.le
        (hcont_all.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx => ?_)
        (hcont_all.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
          fun y hy => ⟨by simp [hR_pos.le], by simp, by
            rw [show -mθ * R = -(mθ * R) by ring] at hy; simpa [R, mθ] using abs_le.mpr hy⟩)
        (hcont_all.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun x hx =>
          mem_closedTri_of_le hx ⟨by linarith, le_rfl⟩)
      have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by push_cast; ring
      rw [heq]; exact mem_closedTri_of_le hx ⟨le_rfl, by linarith⟩
    have h_term_int : ∀ k ∈ Finset.range (n + 1), TriBdIntegrableA (termK k) R mθ := fun k _ => by
      refine triBdIntegrableA_of_continuousOn hR_pos.le hm_pos.le
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
          mem_closedTri_of_le hx ⟨by linarith, le_rfl⟩).mul
          (Continuous.continuousOn (continuous_const.div
            ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const)
            fun x h0 => h_avoid.2.1 x k (sub_eq_zero.mp h0))))
      have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by push_cast; ring
      dsimp only [Pi.mul_apply]; rw [heq]; exact mem_closedTri_of_le hx ⟨le_rfl, by linarith⟩
    have h_sum_int : TriBdIntegrableA (fun z => ∑ k ∈ Finset.range (n + 1), termK k z) R mθ := by
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
    rw [triIntegral_congrA (G := fun z => pref u z * ψn z + ∑ k ∈ Finset.range (n + 1), termK k z)
          hR_pos.le hm_pos.le
          (fun x _ => h_pt_G _ fun ⟨k, _, hk⟩ => h_avoid.1 x k hk.symm)
          (fun y _ => h_pt_G _ fun ⟨k, _, hk⟩ => h_avoid.2.2 y k hk.symm)
          (fun x _ => h_pt_G _ fun ⟨k, _, hk⟩ => h_avoid.2.1 x k hk.symm),
        triIntegral_addA h_Fψ_int h_sum_int, htri_ψn, zero_add,
        triIntegral_sumA _ _ R mθ h_term_int]
    exact Finset.sum_congr rfl h_pole_term
  -- Step 2: Ray tail bounds for ±θ
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
    obtain ⟨Cexp, Dexp, hCexp, hDexp, hbd⟩ := hexp
    have hbase : IntegrableOn (fun t : ℝ => t ^ ((j : ℝ) + 1 / 2) * Real.exp (-(1 / 2 : ℝ) * t)) (Ioi 0) volume :=
      integrableOn_rpow_nat_add_half_mul_exp j (by norm_num)
    let Ij : ℝ := ∫ t in Ioi (0 : ℝ), t ^ ((j : ℝ) + 1 / 2) * Real.exp (-(1 / 2 : ℝ) * t)
    let K : ℝ := (Real.sqrt Real.pi)⁻¹ * Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Ij
    refine ⟨K, ?_⟩
    filter_upwards [eventually_gt_atTop ((Dexp + 1) / Real.cos h.θ)] with u hu
    have hu_re : Dexp + 1 < u * Real.cos h.θ := (div_lt_iff₀ hcos).mp hu
    have hF_int0 : IntegrableOn (fun t : ℝ => d * G u (d * (t : ℂ))) (Ioi 0) volume := by
      have hbase_int : IntegrableOn (fun t : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
          ((-(d * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (d * (t : ℂ))) * d *
            (d * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (d * (t : ℂ)))) (Ioi 0) volume :=
        (halfRayDeriv_integrable hσ hcont hCexp hbd j (by rw [hcos_eq]; linarith)).const_mul _
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
        dsimp only [G, pref, d, Minor.pull]; rw [cpow_half_exp_mul hσ ht0]; ring
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
  have hcontP : ContinuousOn (Minor.pull (dPlusA h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgePlusA_subset_punctured h (wedgePlusA_containsRay h t (le_of_lt ht)))
  have hcontM : ContinuousOn (Minor.pull (dMinusA h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgeMinusA_subset_punctured h (wedgeMinusA_containsRay h t (le_of_lt ht)))
  have hexpM : ExpType (Minor.pull (dMinusA h) ψ) := by rw [dMinusA_eq h]; exact h.expType_minus
  obtain ⟨Kp, hKp⟩ := htail_bound h.θ hθ_abs rfl hcontP h.expType_plus
  obtain ⟨Km, hKm⟩ := htail_bound (-h.θ) hnegθ_abs (Real.cos_neg h.θ) hcontM hexpM
  -- Step 3: Vertical edge bound on [-mθ * R, mθ * R]
  have h_vert_sub : ∀ y ∈ Icc (-mθ * R) (mθ * R), (R : ℂ) + (y : ℂ) * I ∈ puncturedWedge h.θ₀ h.ε ω := by
    intro y hy
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add]
      rw [show -mθ * R = -(mθ * R) by ring] at hy
      exact ⟨hR_pos, lt_of_le_of_lt (abs_le.mpr hy) (mul_lt_mul_of_pos_right (tan_lt_tanA h) hR_pos)⟩
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
          dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, _root_.zpow_neg, zpow_two]
          have hc := hcos.ne'; have hid := Real.sin_sq_add_cos_sq h.θ
          field_simp [hc]; linarith
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
    calc ‖∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I)‖
        ≤ _ := hle
      _ = Kv * Real.exp (-R * u) := by dsimp only [Kv]; ring
  -- Step 4: Combine triangle identity + ray tails + vertical cut
  obtain ⟨Cp, Dp, hCp, _, hbdp⟩ := h.expType_plus
  obtain ⟨Cm, Dm, hCm, _, hbdm⟩ := hexpM
  refine ⟨Kv + Km + Kp, ?_⟩
  filter_upwards [hKp, hKm,
    eventually_gt_atTop (max (Dp / Real.cos h.θ) (Dm / Real.cos h.θ))] with u hkp hkm hu_max
  have hup : Dp < u * Real.cos h.θ := (div_lt_iff₀ hcos).mp (lt_of_le_of_lt (le_max_left _ _) hu_max)
  have hum : Dm < u * Real.cos h.θ := (div_lt_iff₀ hcos).mp (lt_of_le_of_lt (le_max_right _ _) hu_max)
  have hintP : IntegrableOn (fun t : ℝ => dPlusA h * G u (dPlusA h * (t : ℂ))) (Ioi 0) volume := by
    have hbaseP : IntegrableOn (fun t : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
        ((-(dPlusA h * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (dPlusA h * (t : ℂ))) * dPlusA h *
          (dPlusA h * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (dPlusA h * (t : ℂ)))) (Ioi 0) volume :=
      (halfRayDeriv_integrable hθ_abs hcontP hCp hbdp j hup).const_mul _
    refine hbaseP.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only [G, pref]; ring
  have hintM : IntegrableOn (fun t : ℝ => dMinusA h * G u (dMinusA h * (t : ℂ))) (Ioi 0) volume := by
    have hbaseM : IntegrableOn (fun t : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
        ((-(dMinusA h * (t : ℂ))) ^ j * Complex.exp (-(u : ℂ) * (dMinusA h * (t : ℂ))) * dMinusA h *
          (dMinusA h * (t : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) * ψ (dMinusA h * (t : ℂ)))) (Ioi 0) volume :=
      (halfRayDeriv_integrable hnegθ_abs hcontM hCm hbdm j (by rwa [Real.cos_neg])).const_mul _
    refine hbaseM.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only [G, pref]; ring
  have hhrP : halfRayDeriv ψ (dPlusA h) j u = ∫ t in Ioi (0 : ℝ), dPlusA h * G u (dPlusA h * (t : ℂ)) := by
    unfold halfRayDeriv; rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only [G, pref]; ring
  have hhrM : halfRayDeriv ψ (dMinusA h) j u = ∫ t in Ioi (0 : ℝ), dMinusA h * G u (dMinusA h * (t : ℂ)) := by
    unfold halfRayDeriv; rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only [G, pref]; ring
  have hsplitP : (∫ t in (0 : ℝ)..v₀, dPlusA h * G u (dPlusA h * (t : ℂ))) +
      (∫ t in Ioi v₀, dPlusA h * G u (dPlusA h * (t : ℂ))) =
      ∫ t in Ioi (0 : ℝ), dPlusA h * G u (dPlusA h * (t : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintP (hintP.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hsplitM : (∫ t in (0 : ℝ)..v₀, dMinusA h * G u (dMinusA h * (t : ℂ))) +
      (∫ t in Ioi v₀, dMinusA h * G u (dMinusA h * (t : ℂ))) =
      ∫ t in Ioi (0 : ℝ), dMinusA h * G u (dMinusA h * (t : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintM (hintM.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hdP_mul : (1 + I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dPlusA h := by
    have hdP : dPlusA h = (Real.cos h.θ : ℂ) + (Real.sin h.θ : ℂ) * I := by
      unfold dPlusA; rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hdP]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
    field_simp [hc]
  have hdM_mul : (1 - I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dMinusA h := by
    have hdM : dMinusA h = (Real.cos h.θ : ℂ) - (Real.sin h.θ : ℂ) * I := by
      unfold dMinusA; rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]; ring
    rw [hdM]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
    field_simp [hc]
  have hcovP : ∫ t in (0 : ℝ)..v₀, dPlusA h * G u (dPlusA h * (t : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 + I * (mθ : ℂ)) * G u ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun t : ℝ => dPlusA h * G u (dPlusA h * (t : ℂ))) hcos.ne' (a := 0) (b := R)
    have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) * G u ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dPlusA h * G u (dPlusA h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 + I * (mθ : ℂ)) = dPlusA h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
        rw [hdP_mul]; push_cast; ring
      rw [harg, Complex.real_smul, hdP_mul]; push_cast; ring
    rw [heq, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne', one_smul, zero_div]
  have hcovM : ∫ t in (0 : ℝ)..v₀, dMinusA h * G u (dMinusA h * (t : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 - I * (mθ : ℂ)) * G u ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun t : ℝ => dMinusA h * G u (dMinusA h * (t : ℂ))) hcos.ne' (a := 0) (b := R)
    have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) * G u ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dMinusA h * G u (dMinusA h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 - I * (mθ : ℂ)) = dMinusA h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
        rw [hdM_mul]; push_cast; ring
      rw [harg, Complex.real_smul, hdM_mul]; push_cast; ring
    rw [heq, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne', one_smul, zero_div]
  have hdiff : halfRayDeriv ψ (dMinusA h) j u - halfRayDeriv ψ (dPlusA h) j u -
      ∑ k ∈ Finset.range (n + 1),
        halfStokesCoeff ω res k * (-(ω k : ℂ)) ^ j * Complex.exp (-(ω k : ℂ) * (u : ℂ)) =
      (∫ t in Ioi v₀, dMinusA h * G u (dMinusA h * (t : ℂ))) -
      (∫ t in Ioi v₀, dPlusA h * G u (dPlusA h * (t : ℂ))) -
      I * (∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I)) := by
    rw [← htri_G u, hhrM, hhrP, ← hsplitM, ← hsplitP, hcovM, hcovP]
    unfold triIntegral; ring
  rw [hdiff]
  have htri_ineq : ‖(∫ t in Ioi v₀, dMinusA h * G u (dMinusA h * (t : ℂ))) -
        (∫ t in Ioi v₀, dPlusA h * G u (dPlusA h * (t : ℂ))) -
        I * (∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I))‖ ≤
      ‖∫ t in Ioi v₀, dMinusA h * G u (dMinusA h * (t : ℂ))‖ +
      ‖∫ t in Ioi v₀, dPlusA h * G u (dPlusA h * (t : ℂ))‖ +
      ‖I * (∫ y in (-mθ * R)..(mθ * R), G u ((R : ℂ) + (y : ℂ) * I))‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hv := h_vert_bd u
  have hkp' : ‖∫ t in Ioi v₀, dPlusA h * G u (dPlusA h * (t : ℂ))‖ ≤ Kp * Real.exp (-R * u) := hkp
  have hkm' : ‖∫ t in Ioi v₀, dMinusA h * G u (dMinusA h * (t : ℂ))‖ ≤ Km * Real.exp (-R * u) := hkm
  dsimp only [R] at hv hkp' hkm' ⊢
  linarith

private lemma abelConv_stokes_jump {ψ ω res} (h : MeromorphicBorelData ψ ω res) (n j : ℕ) :
    ∃ R' : ℝ, ω n < R' ∧ ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aAbel ψ).value (dMinusA h) (t : ℂ)) u -
        iteratedDeriv j (fun t : ℝ => (aAbel ψ).value (dPlusA h) (t : ℂ)) u -
        ∑ k ∈ Finset.range (n + 1),
          halfStokesCoeff ω res k * iteratedDeriv j (branchMode (1 / 2) (ω k : ℂ)) u‖ ≤
        C * Real.exp (-R' * u) := by
  let R' : ℝ := (ω n + ω (n + 1)) / 2
  have hR'_gt : ω n < R' := by have := h.ω_mono (Nat.lt_succ_self n); dsimp only [R']; linarith
  refine ⟨R', hR'_gt, ?_⟩
  have hθ_abs : |h.θ| < Real.pi / 2 := abs_lt.mpr ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hθ₀_lt⟩
  have hnegθ_abs : |-h.θ| < Real.pi / 2 := by simpa [abs_neg] using hθ_abs
  have hcontP : ContinuousOn (Minor.pull (dPlusA h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgePlusA_subset_punctured h (wedgePlusA_containsRay h t (le_of_lt ht)))
  have hcontM : ContinuousOn (Minor.pull (dMinusA h) ψ) (Ioi 0) :=
    continuousOn_const.mul (h.analyticOn.continuousOn.comp
      (continuous_const.mul Complex.continuous_ofReal).continuousOn fun t ht =>
        wedgeMinusA_subset_punctured h (wedgeMinusA_containsRay h t (le_of_lt ht)))
  have hexpM : ExpType (Minor.pull (dMinusA h) ψ) := by rw [dMinusA_eq h]; exact h.expType_minus
  -- Express g_neg - g_pos - ∑ c_k branchMode (1/2) (ω k) as branchMode (1/2) 0 * H eventually
  let gPos : ℝ → ℂ := fun t => (aAbel ψ).value (dPlusA h) (t : ℂ)
  let gNeg : ℝ → ℂ := fun t => (aAbel ψ).value (dMinusA h) (t : ℂ)
  let w : ℝ → ℂ := branchMode (1 / 2) 0
  let H : ℝ → ℂ := fun t =>
    halfRayLaplace ψ (dMinusA h) t - halfRayLaplace ψ (dPlusA h) t -
      ∑ k ∈ Finset.range (n + 1), halfStokesCoeff ω res k * Complex.exp (-(ω k : ℂ) * (t : ℂ))
  have hw_eq : ∀ t : ℝ, w t = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := fun t => by
    simp [w, branchMode]
  have hw_cd : ∀ t : ℝ, 0 < t → ContDiffAt ℝ j w t := fun t ht => by
    have hrp : ContDiffAt ℝ j (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) t :=
      Real.contDiffAt_rpow_const (Or.inl ht.ne')
    have hEq : w = fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := funext hw_eq
    rw [hEq]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp t hrp
  have hexp_cd : ∀ k : ℕ, ∀ t : ℝ, ContDiffAt ℝ j (fun x : ℝ => Complex.exp (-(ω k : ℂ) * (x : ℂ))) t :=
    fun k t => (Complex.contDiff_exp.comp
      (contDiff_const.mul Complex.ofRealCLM.contDiff)).contDiffAt
  have hbm_cd : ∀ k : ℕ, ∀ t : ℝ, 0 < t → ContDiffAt ℝ j (branchMode (1 / 2) (ω k : ℂ)) t :=
    fun k t ht => by
      have heq : branchMode (1 / 2) (ω k : ℂ) = fun x => w x * Complex.exp (-(ω k : ℂ) * (x : ℂ)) :=
        funext fun x => by simp [branchMode, w]
      rw [heq]; exact (hw_cd t ht).mul (hexp_cd k t)
  have hvalP := abelConv_value_eq_rpow_mul_halfRay hθ_abs hcontP h.expType_plus
  have hvalM := abelConv_value_eq_rpow_mul_halfRay hnegθ_abs hcontM hexpM
  have hcdP := contDiffAt_halfRayLaplace hθ_abs hcontP h.expType_plus j
  have hcdM := contDiffAt_halfRayLaplace hnegθ_abs hcontM hexpM j
  -- Collect Stokes jump bounds for H^(i) for all i ≤ j
  choose C_i hC_i using fun i : Fin (j + 1) => halfRayDeriv_stokes_jump h n i.val
  have h_all_jump := Filter.eventually_all.mpr hC_i
  have h_all_hrP := Filter.eventually_all.mpr fun i : Fin (j + 1) =>
    iteratedDeriv_halfRayLaplace_eq hθ_abs hcontP h.expType_plus i.val
  have h_all_hrM := Filter.eventually_all.mpr fun i : Fin (j + 1) =>
    iteratedDeriv_halfRayLaplace_eq hnegθ_abs hcontM hexpM i.val
  -- Uniform bound on ‖iteratedDeriv i w u‖ for u ≥ 1
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
    have hdeg : (P_branch (1 / 2) 0 i).natDegree < i + 1 :=
      Nat.lt_succ_of_le (P_branch_natDegree_le (1 / 2) 0 i)
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
  -- Collect eventually-true events on neighborhoods
  let Ctot : ℝ := ∑ i : Fin (j + 1), (j.choose i.val : ℝ) * Bw i.val * max (C_i ⟨j - i.val, by omega⟩) 0
  refine ⟨Ctot, ?_⟩
  have hnhdsP : ∀ᶠ u : ℝ in atTop, gPos =ᶠ[𝓝 u] fun t => w t * halfRayLaplace ψ (dPlusA h) t := by
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hvalP
    filter_upwards [eventually_gt_atTop U₀] with u hu
    filter_upwards [Ioi_mem_nhds hu] with t ht
    rw [hw_eq t]; exact hU₀ t (le_of_lt ht)
  have hnhdsM : ∀ᶠ u : ℝ in atTop, gNeg =ᶠ[𝓝 u] fun t => w t * halfRayLaplace ψ (dMinusA h) t := by
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
        halfRayDeriv ψ (dMinusA h) i u - halfRayDeriv ψ (dPlusA h) i u -
          ∑ k ∈ Finset.range (n + 1),
            halfStokesCoeff ω res k * (-(ω k : ℂ)) ^ i * Complex.exp (-(ω k : ℂ) * (u : ℂ)) := fun i hi => by
    have hcdM_i : ContDiffAt ℝ i (halfRayLaplace ψ (dMinusA h)) u := hcdMu.of_le (Nat.cast_le.mpr hi)
    have hcdP_i : ContDiffAt ℝ i (halfRayLaplace ψ (dPlusA h)) u := hcdPu.of_le (Nat.cast_le.mpr hi)
    have hexp_i : ∀ k : ℕ, ContDiffAt ℝ i (fun x : ℝ => Complex.exp (-(ω k : ℂ) * (x : ℂ))) u :=
      fun k => (hexp_cd k u).of_le (Nat.cast_le.mpr hi)
    have hcd_sum_e : ContDiffAt ℝ i
        (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), halfStokesCoeff ω res k * Complex.exp (-(ω k : ℂ) * (x : ℂ))) u :=
      ContDiffAt.sum fun k _ => contDiffAt_const.mul (hexp_i k)
    dsimp only [H]
    rw [iteratedDeriv_fun_sub (hcdM_i.sub hcdP_i) hcd_sum_e,
      iteratedDeriv_fun_sub hcdM_i hcdP_i]
    dsimp only [dMinusA, dPlusA]
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
        dsimp only [Ctot]; rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring

/-- **Half-Integer `BranchPointStokesData` Builder**:
Any positive-ray simple-pole meromorphic Borel kernel `ψ` (`MeromorphicBorelData ψ ω res`)
induces a complete `BranchPointStokesData (formalSeries (abelConv ψ)) (1/2) ω (halfStokesCoeff ω res)`. -/
def abelConv_branchPointStokesData {ψ ω res} (h : MeromorphicBorelData ψ ω res) :
    BranchPointStokesData (formalSeries (abelConv ψ)) (1 / 2) ω (halfStokesCoeff ω res) where
  ω_pos := h.ω_pos
  ω_mono := h.ω_mono
  c_ne_zero := fun m => by
    unfold halfStokesCoeff
    have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    have hsq : ((Real.sqrt (Real.pi * ω m) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hωm)).ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hsq) (h.res_ne_zero m)
  g_pos := fun t => (aAbel ψ).value (dPlusA h) (t : ℂ)
  g_neg := fun t => (aAbel ψ).value (dMinusA h) (t : ℂ)
  g_pos_asymp := fun j =>
    minor_value_hasAsympExp (aAbel ψ) (wedgePlusA_domain (ε₀A_pos h)) (wedgePlusA_containsRay h)
      (aAbel_good_plus h) (by rw [dPlusA_re h]; exact cos_pos_θA h) j
  g_neg_asymp := fun j =>
    minor_value_hasAsympExp (aAbel ψ) (wedgeMinusA_domain (ε₀A_pos h)) (wedgeMinusA_containsRay h)
      (aAbel_good_minus h) (by rw [dMinusA_re h]; exact cos_pos_θA h) j
  borel_transfer := fun P hP => abelConv_borel_transfer h P hP
  stokes_jump := fun n j => abelConv_stokes_jump h n j

/-- Unconditional `ℂ[u]` non-autonomous differential transcendence of `formalSeries (abelConv ψ)`. -/
theorem abelConv_no_ade {ψ ω res} (h : MeromorphicBorelData ψ ω res)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries (abelConv ψ)) P = 0) : P = 0 :=
  branchPoint_stokes_vandermonde_no_ade (abelConv_branchPointStokesData h) P hP

/-! #### 4C. Pure-Algebra Transfer `formalEvalPoly (X^2 * E) P = 0 → P = 0` ⇒ `AlgebraicIndependent ℂ (seriesCoordinates E)` -/

/-- Coefficient-wise `Polynomial.derivative` on `MvPolynomial ℕ (Polynomial ℂ)`. -/
private def coeffDeriv (A : MvPolynomial ℕ (Polynomial ℂ)) : MvPolynomial ℕ (Polynomial ℂ) :=
  ∑ m ∈ A.support, MvPolynomial.monomial m (Polynomial.derivative (A.coeff m))

private lemma coeffDeriv_coeff (A : MvPolynomial ℕ (Polynomial ℂ)) (m : ℕ →₀ ℕ) :
    (coeffDeriv A).coeff m = Polynomial.derivative (A.coeff m) := by
  classical
  unfold coeffDeriv
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ A.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [hb]
    · intro hnot; exact absurd hm hnot
  · rw [Finset.sum_eq_zero (fun b hb => by simp [show b ≠ m from fun h => hm (h ▸ hb)]),
      MvPolynomial.notMem_support_iff.mp hm, map_zero]

private lemma coeffDeriv_C (p : Polynomial ℂ) :
    coeffDeriv (MvPolynomial.C p) = MvPolynomial.C (Polynomial.derivative p) := by
  apply MvPolynomial.ext; intro m
  rw [coeffDeriv_coeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs
  · rfl
  · simp

private lemma coeffDeriv_add (A B : MvPolynomial ℕ (Polynomial ℂ)) :
    coeffDeriv (A + B) = coeffDeriv A + coeffDeriv B := by
  apply MvPolynomial.ext; intro m
  simp only [coeffDeriv_coeff, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, map_add]

private lemma coeffDeriv_mul_X (A : MvPolynomial ℕ (Polynomial ℂ)) (i : ℕ) :
    coeffDeriv (A * MvPolynomial.X i) = coeffDeriv A * MvPolynomial.X i := by
  classical
  apply MvPolynomial.ext; intro m
  rw [coeffDeriv_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs
  · exact (coeffDeriv_coeff A _).symm
  · simp

private lemma coeffDeriv_vars_subset (A : MvPolynomial ℕ (Polynomial ℂ)) :
    (coeffDeriv A).vars ⊆ A.vars := by
  intro k hk
  rw [MvPolynomial.mem_vars_iff_mem_support] at hk ⊢
  obtain ⟨m, hm, hkm⟩ := hk
  refine ⟨m, ?_, hkm⟩
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [coeffDeriv_coeff] at hm
  intro h0; rw [h0, map_zero] at hm; exact hm rfl

private lemma vars_pderiv_subset' {R : Type*} [CommSemiring R] (m : ℕ) (A : MvPolynomial ℕ R) :
    (MvPolynomial.pderiv m A).vars ⊆ A.vars := by
  intro k hk
  rw [MvPolynomial.mem_vars_iff_mem_support] at hk ⊢
  obtain ⟨d, hd, hkd⟩ := hk
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hd
  refine ⟨d + Finsupp.single m 1, MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hd), ?_⟩
  rw [Finsupp.mem_support_iff] at hkd ⊢
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega

/-- Formal derivation `d_u = -X^2 d/dX` lifted to polynomials in `X` and `Y_0, Y_1, ...`. -/
private def dXOp (A : MvPolynomial ℕ (Polynomial ℂ)) : MvPolynomial ℕ (Polynomial ℂ) :=
  MvPolynomial.C (-Polynomial.X ^ 2) * coeffDeriv A +
    ∑ k ∈ A.vars, MvPolynomial.pderiv k A * MvPolynomial.X (k + 1)

/-- Triangular polynomial representation of `W_j = X^{2j+2} * (d/dX)^j E` in terms of `X` and `d_u^[k] (X^2 * E)`. -/
private def toXJet : ℕ → MvPolynomial ℕ (Polynomial ℂ)
  | 0 => MvPolynomial.X 0
  | j + 1 => -dXOp (toXJet j) - MvPolynomial.C (Polynomial.C ((2 * j + 2 : ℕ) : ℂ) * Polynomial.X) * toXJet j

private lemma d_u_eq_neg_X_sq_mul_deriv (f : PowerSeries ℂ) :
    d_u f = -(PowerSeries.X ^ 2 * PowerSeries.derivative f) := by
  ext n
  unfold d_u
  rcases n with _ | _ | k
  · simp [pow_two, mul_assoc]
  · simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul, pow_two, mul_assoc]
  · simp [pow_two, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]

private lemma d_u_add (f g : PowerSeries ℂ) : d_u (f + g) = d_u f + d_u g := by
  rw [d_u_eq_neg_X_sq_mul_deriv, d_u_eq_neg_X_sq_mul_deriv, d_u_eq_neg_X_sq_mul_deriv, map_add]
  ring

private lemma d_u_mul (f g : PowerSeries ℂ) : d_u (f * g) = d_u f * g + f * d_u g := by
  rw [d_u_eq_neg_X_sq_mul_deriv, d_u_eq_neg_X_sq_mul_deriv, d_u_eq_neg_X_sq_mul_deriv,
    Derivation.leibniz]
  simp only [smul_eq_mul]; ring

private lemma d_u_pow (f : PowerSeries ℂ) (k : ℕ) :
    d_u (f ^ k) = (k : ℂ) • (f ^ (k - 1) * d_u f) := by
  induction k with
  | zero =>
    rw [pow_zero, d_u_eq_neg_X_sq_mul_deriv, Derivation.map_one_eq_zero, mul_zero, neg_zero]
    simp
  | succ k ih =>
    rw [pow_succ, d_u_mul, ih]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, PowerSeries.smul_eq_C_mul]
      push_cast; simp only [map_add, map_natCast, map_one, pow_succ]
      ring

private lemma d_u_coe_poly (p : Polynomial ℂ) :
    d_u (p : PowerSeries ℂ) = -(PowerSeries.X ^ 2 * ((Polynomial.derivative p : Polynomial ℂ) : PowerSeries ℂ)) := by
  rw [d_u_eq_neg_X_sq_mul_deriv]
  congr 2
  ext n
  rw [PowerSeries.coeff_derivative, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_derivative]

private lemma dXOp_eq_of_vars_subset (B : MvPolynomial ℕ (Polynomial ℂ)) (s : Finset ℕ) (hs : B.vars ⊆ s) :
    dXOp B = MvPolynomial.C (-Polynomial.X ^ 2) * coeffDeriv B +
      ∑ k ∈ s, MvPolynomial.pderiv k B * MvPolynomial.X (k + 1) := by
  unfold dXOp; congr 1
  refine Finset.sum_subset hs fun k _ hk => ?_
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hk, zero_mul]

private lemma dXOp_add (A B : MvPolynomial ℕ (Polynomial ℂ)) :
    dXOp (A + B) = dXOp A + dXOp B := by
  let s := (A + B).vars ∪ A.vars ∪ B.vars
  have hsAB : (A + B).vars ⊆ s := Finset.subset_union_left.trans Finset.subset_union_left
  have hsA : A.vars ⊆ s := Finset.subset_union_right.trans Finset.subset_union_left
  have hsB : B.vars ⊆ s := Finset.subset_union_right
  rw [dXOp_eq_of_vars_subset (A + B) s hsAB, dXOp_eq_of_vars_subset A s hsA, dXOp_eq_of_vars_subset B s hsB,
    coeffDeriv_add, mul_add]
  have hsum : ∑ k ∈ s, MvPolynomial.pderiv k (A + B) * MvPolynomial.X (k + 1) =
      (∑ k ∈ s, MvPolynomial.pderiv k A * MvPolynomial.X (k + 1)) +
      (∑ k ∈ s, MvPolynomial.pderiv k B * MvPolynomial.X (k + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [map_add, add_mul]
  rw [hsum]; abel

private lemma evalX_dXOp (S : PowerSeries ℂ) (A : MvPolynomial ℕ (Polynomial ℂ)) :
    d_u (MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun k => d_u^[k] S) A) =
      MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun k => d_u^[k] S) (dXOp A) := by
  classical
  induction A using MvPolynomial.induction_on with
  | C p =>
    have hvars : (MvPolynomial.C p : MvPolynomial ℕ (Polynomial ℂ)).vars = ∅ := MvPolynomial.vars_C
    unfold dXOp
    rw [hvars, Finset.sum_empty, add_zero, coeffDeriv_C, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, map_neg, map_pow,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_X]
    simpa [neg_mul] using d_u_coe_poly p
  | add A B hA hB =>
    rw [map_add, d_u_add, hA, hB, dXOp_add, map_add]
  | mul_X A i hA =>
    let s := insert i ((A * MvPolynomial.X i).vars ∪ A.vars)
    have hsAX : (A * MvPolynomial.X i).vars ⊆ s := Finset.subset_union_left.trans (Finset.subset_insert _ _)
    have hsA : A.vars ⊆ s := Finset.subset_union_right.trans (Finset.subset_insert _ _)
    have hi_s : i ∈ s := Finset.mem_insert_self _ _
    have hd_mulX : dXOp (A * MvPolynomial.X i) = dXOp A * MvPolynomial.X i + A * MvPolynomial.X (i + 1) := by
      rw [dXOp_eq_of_vars_subset (A * MvPolynomial.X i) s hsAX, dXOp_eq_of_vars_subset A s hsA,
        coeffDeriv_mul_X, ← mul_assoc, add_mul, Finset.sum_mul]
      have hsum : ∑ k ∈ s, MvPolynomial.pderiv k (A * MvPolynomial.X i) * MvPolynomial.X (k + 1) =
          (∑ k ∈ s, MvPolynomial.pderiv k A * MvPolynomial.X (k + 1) * MvPolynomial.X i) +
            A * MvPolynomial.X (i + 1) := by
        have hstep : ∀ k ∈ s, MvPolynomial.pderiv k (A * MvPolynomial.X i) * MvPolynomial.X (k + 1) =
            MvPolynomial.pderiv k A * MvPolynomial.X (k + 1) * MvPolynomial.X i +
              (if k = i then A * MvPolynomial.X (i + 1) else 0) := fun k _ => by
          rw [Derivation.leibniz, MvPolynomial.pderiv_X]
          simp only [smul_eq_mul, Pi.single_apply]
          by_cases hki : k = i
          · subst hki; simp; ring
          · have hik : i ≠ k := Ne.symm hki; simp [hki, hik]; ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite_eq' s i,
          ite_eq_left_iff.mpr fun h => absurd hi_s h]
      rw [hsum]; ring
    rw [map_mul, d_u_mul, hA, hd_mulX, map_add, map_mul, map_mul,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Function.iterate_succ_apply' d_u i S]

private lemma evalX_toXJet (E : PowerSeries ℂ) (j : ℕ) :
    MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun k => d_u^[k] (PowerSeries.X ^ 2 * E)) (toXJet j) =
      PowerSeries.X ^ (2 * j + 2) * seriesJet E j := by
  induction j with
  | zero => simp [toXJet, seriesJet]
  | succ j ih =>
    simp only [toXJet, map_sub, map_neg, map_mul, MvPolynomial.eval₂Hom_C]
    rw [← evalX_dXOp, ih, d_u_mul]
    have hpow : d_u (PowerSeries.X ^ (2 * j + 2)) =
        -((2 * j + 2 : ℕ) : ℂ) • (PowerSeries.X ^ (2 * j + 3)) := by
      rw [d_u_pow, d_u_eq_neg_X_sq_mul_deriv, PowerSeries.derivative_X, mul_one]
      have hsub : 2 * j + 2 - 1 = 2 * j + 1 := by omega
      rw [hsub, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
      have hexp : (PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 1) * (-(PowerSeries.X : PowerSeries ℂ) ^ 2) =
          -((PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 3)) := by
        rw [mul_neg, ← pow_add]
      rw [hexp, map_neg]; ring
    have hder : d_u (seriesJet E j) = -(PowerSeries.X ^ 2 * seriesJet E (j + 1)) := by
      dsimp only [seriesJet]; rw [d_u_eq_neg_X_sq_mul_deriv, Function.iterate_succ_apply']
    rw [hpow, hder, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X,
      PowerSeries.smul_eq_C_mul]
    have h1 : (PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 2) * -(PowerSeries.X ^ 2 * seriesJet E (j + 1)) =
        -(PowerSeries.X ^ (2 * (j + 1) + 2) * seriesJet E (j + 1)) := by
      rw [mul_neg, ← mul_assoc, ← pow_add, show 2 * j + 2 + 2 = 2 * (j + 1) + 2 by omega]
    have h2 : (PowerSeries.X : PowerSeries ℂ) ^ (2 * j + 3) = PowerSeries.X * PowerSeries.X ^ (2 * j + 2) := by
      rw [← pow_succ']
    rw [h1, h2]
    push_cast
    simp only [map_neg, map_add, map_mul, map_natCast, map_ofNat]
    ring

private lemma toXJet_triangular (j : ℕ) :
    ∃ R : MvPolynomial ℕ (Polynomial ℂ),
      (∀ k ∈ R.vars, k < j) ∧
      toXJet j = MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X j + R := by
  induction j with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simp [toXJet]
  | succ j ih =>
    obtain ⟨R, hR_vars, hR_eq⟩ := ih
    let dR := dXOp R
    have hdR_vars : ∀ k ∈ dR.vars, k < j + 1 := by
      intro k hk
      unfold dR dXOp at hk
      rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hk) with h1 | h2
      · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h1) with hc | hd
        · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
        · exact Nat.lt_succ_of_lt (hR_vars k (coeffDeriv_vars_subset R hd))
      · obtain ⟨m, hm, hk_m⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ h2)
        rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk_m) with hm1 | hm2
        · exact Nat.lt_succ_of_lt (hR_vars k (vars_pderiv_subset' m R hm1))
        · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hm2
          subst hm2; exact Nat.succ_lt_succ (hR_vars m hm)
    have hd_lead : dXOp (MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X j) =
        MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X (j + 1) := by
      unfold dXOp
      rw [coeffDeriv_mul_X, coeffDeriv_C, Polynomial.derivative_C, map_zero, zero_mul, mul_zero, zero_add]
      have hvars_sub : (MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X j).vars ⊆ {j} := by
        refine (MvPolynomial.vars_mul _ _).trans ?_
        rw [MvPolynomial.vars_C, MvPolynomial.vars_X, Finset.empty_union]
      rw [Finset.sum_subset hvars_sub (fun k _ hk => by
        rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hk, zero_mul]),
        Finset.sum_singleton, Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero,
        MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one]
    have hd_add_toX : dXOp (toXJet j) =
        MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) * MvPolynomial.X (j + 1) + dR := by
      rw [hR_eq, dXOp_add, hd_lead]
    let R' : MvPolynomial ℕ (Polynomial ℂ) :=
      -dR - MvPolynomial.C (Polynomial.C ((2 * j + 2 : ℕ) : ℂ) * Polynomial.X) * toXJet j
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
    · dsimp only [toXJet, R']
      rw [hd_add_toX]
      have hpow : (MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ (j + 1))) : MvPolynomial ℕ (Polynomial ℂ)) =
          -MvPolynomial.C (Polynomial.C ((-1 : ℂ) ^ j)) := by
        rw [pow_succ, mul_neg_one, map_neg, map_neg]
      rw [hpow]; ring

private lemma toXJet_vars_le (j : ℕ) : ∀ k ∈ (toXJet j).vars, k ≤ j := by
  obtain ⟨R, hR_vars, hR_eq⟩ := toXJet_triangular j
  intro k hk
  rw [hR_eq] at hk
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hk) with h1 | h2
  · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h1) with hc | hx
    · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx; subst hx; exact le_rfl
  · exact le_of_lt (hR_vars k h2)

private lemma eval_congr_vars {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R}
    {f g : σ → R} (h : ∀ i ∈ p.vars, f i = g i) :
    MvPolynomial.eval f p = MvPolynomial.eval g p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩)]

private lemma eval₂Hom_congr_vars {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {p : MvPolynomial σ R} {f g : σ → S} (h : ∀ i ∈ p.vars, f i = g i) :
    MvPolynomial.eval₂Hom φ f p = MvPolynomial.eval₂Hom φ g p := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩)]

/-- **Pure-Algebra Transfer (`X^2 * E ↔ E`)**:
If `S = X^2 * E` satisfies no nonzero `ℂ[u]`-ADE (`formalEvalPoly S P = 0 → P = 0`), then
`E` is differentially transcendental over `ℂ(X)` (`AlgebraicIndependent ℂ (seriesCoordinates E)`). -/
theorem algebraicIndependent_of_X_sq_mul_no_ade {E : PowerSeries ℂ}
    (hno : ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)),
      formalEvalPoly (PowerSeries.X ^ 2 * E) P = 0 → P = 0) :
    AlgebraicIndependent ℂ (seriesCoordinates E) := by
  classical
  rw [algebraicIndependent_iff]
  intro Q hQ
  let r : ℕ := Q.vars.sup id
  have hr_bound : ∀ i ∈ Q.vars, i ≤ r := fun i hi => Finset.le_sup (f := id) hi
  let M : ℕ := (2 * r + 2) * Q.totalDegree
  let S : PowerSeries ℂ := PowerSeries.X ^ 2 * E
  let proj : ℕ → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun k =>
    if hk : k < r + 1 then MvPolynomial.X ⟨k, hk⟩ else 0
  let jetFin (j : ℕ) : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.aeval proj (toXJet j)
  let evS := MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun i : Fin (r + 1) => d_u^[i.val] S)
  let evS_nat := MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun k : ℕ => d_u^[k] S)
  have hjetFin_eval_S : ∀ j ≤ r, evS (jetFin j) = PowerSeries.X ^ (2 * j + 2) * seriesJet E j := by
    intro j hj
    have hcomp : ∀ p : MvPolynomial ℕ (Polynomial ℂ),
        evS (MvPolynomial.aeval proj p) =
          MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom (fun k => evS (proj k)) p := fun p => by
      induction p using MvPolynomial.induction_on with
      | C c => simp [evS]
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | mul_X a k ha => rw [map_mul, map_mul, map_mul, ha, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
    rw [show jetFin j = MvPolynomial.aeval proj (toXJet j) from rfl, hcomp, ← evalX_toXJet E j]
    refine eval₂Hom_congr_vars _ fun k hk => ?_
    have hk_lt : k < r + 1 := Nat.lt_succ_of_le ((toXJet_vars_le j k hk).trans hj)
    dsimp only [proj, evS]
    split_ifs
    simp [S]
  have hjetFin_eval_C : ∀ j ≤ r, ∀ (x : ℂ) (y : Fin (r + 1) → ℂ),
      MvPolynomial.eval y (evalU (jetFin j) x) =
        MvPolynomial.eval (fun k => if hk : k < r + 1 then y ⟨k, hk⟩ else 0)
          (MvPolynomial.map (Polynomial.evalRingHom x) (toXJet j)) := by
    intro j hj x y
    have hcomp : ∀ p : MvPolynomial ℕ (Polynomial ℂ),
        MvPolynomial.eval y (evalU (MvPolynomial.aeval proj p) x) =
          MvPolynomial.eval (fun k => MvPolynomial.eval y (evalU (proj k) x))
            (MvPolynomial.map (Polynomial.evalRingHom x) p) := fun p => by
      induction p using MvPolynomial.induction_on with
      | C c => simp [evalU]
      | add a b ha hb => simp only [evalU, map_add] at ha hb ⊢; rw [ha, hb]
      | mul_X a k ha =>
        simp only [evalU, map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.eval_X] at ha ⊢
        rw [ha]
    rw [show jetFin j = MvPolynomial.aeval proj (toXJet j) from rfl, hcomp]
    refine eval_congr_vars fun k hk => ?_
    have hk_lt : k < r + 1 :=
      Nat.lt_succ_of_le ((toXJet_vars_le j k (MvPolynomial.vars_map _ _ hk)).trans hj)
    dsimp only [proj, evalU]
    split_ifs
    simp
  let wt (m : ℕ →₀ ℕ) : ℕ := m.sum fun i e => match i with | 0 => 0 | j + 1 => (2 * j + 2) * e
  have hwt_le : ∀ m ∈ Q.support, wt m ≤ M := fun m hm => by
    have hdeg : (m.sum fun _ e => e) ≤ Q.totalDegree := MvPolynomial.le_totalDegree hm
    have hterm : ∀ i ∈ m.support, (match i with | 0 => 0 | j + 1 => (2 * j + 2) * m i) ≤ (2 * r + 2) * m i := by
      intro i hi
      have hi_le : i ≤ r := hr_bound i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩)
      cases i with
      | zero => simp
      | succ j => exact Nat.mul_le_mul_right (m (j + 1)) (by omega)
    calc wt m = ∑ i ∈ m.support, match i with | 0 => 0 | j + 1 => (2 * j + 2) * m i := rfl
      _ ≤ ∑ i ∈ m.support, (2 * r + 2) * m i := Finset.sum_le_sum hterm
      _ = (2 * r + 2) * ∑ i ∈ m.support, m i := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * r + 2) * Q.totalDegree := Nat.mul_le_mul_left _ hdeg
  let monP (m : ℕ →₀ ℕ) : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.C (Polynomial.C (Q.coeff m) * Polynomial.X ^ (M - wt m + m 0)) *
      m.prod fun i e => match i with | 0 => 1 | j + 1 => jetFin j ^ e
  let P_X : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := ∑ m ∈ Q.support, monP m
  have hPX_eval_S : evS P_X = 0 := by
    have heq : evS P_X = PowerSeries.X ^ M * MvPolynomial.aeval (seriesCoordinates E) Q := by
      dsimp only [P_X]
      rw [map_sum]
      conv_rhs => rw [MvPolynomial.as_sum Q, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      dsimp only [monP]
      rw [map_mul, MvPolynomial.eval₂Hom_C, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
        Finsupp.prod, map_prod, MvPolynomial.aeval_monomial, PowerSeries.algebraMap_apply]
      have hprod : (∏ i ∈ m.support, evS (match i with | 0 => 1 | j + 1 => jetFin j ^ m i)) =
          PowerSeries.X ^ (wt m) * ∏ i ∈ m.support, match i with
            | 0 => (1 : PowerSeries ℂ)
            | j + 1 => seriesJet E j ^ m (j + 1) := by
        have hstep : ∀ i ∈ m.support,
            evS (match i with | 0 => 1 | j + 1 => jetFin j ^ m i) =
            PowerSeries.X ^ (match i with | 0 => 0 | j + 1 => (2 * j + 2) * m (j + 1)) *
              (match i with | 0 => (1 : PowerSeries ℂ) | j + 1 => seriesJet E j ^ m (j + 1)) := by
          intro i hi
          cases i with
          | zero => simp
          | succ j =>
            have hj_le : j ≤ r := Nat.le_of_lt (Nat.lt_of_succ_le (hr_bound (j + 1)
              ((MvPolynomial.mem_vars_iff_mem_support (j + 1)).mpr ⟨m, hm, hi⟩)))
            rw [map_pow, hjetFin_eval_S j hj_le, mul_pow, ← pow_mul]
        rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        congr 2; exact Finset.sum_congr rfl fun i _ => by cases i <;> rfl
      rw [hprod]
      have hsplit_Q : (m.prod fun i e => seriesCoordinates E i ^ e) =
          PowerSeries.X ^ (m 0) * ∏ i ∈ m.support, match i with
            | 0 => (1 : PowerSeries ℂ)
            | j + 1 => seriesJet E j ^ m (j + 1) := by
        unfold Finsupp.prod
        by_cases h0 : (0 : ℕ) ∈ m.support
        · rw [← Finset.mul_prod_erase m.support _ h0, ← Finset.mul_prod_erase m.support _ h0]
          simp only [seriesCoordinates, one_mul]
          congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          cases i with
          | zero => exact absurd rfl (Finset.mem_erase.mp hi).1
          | succ j => rfl
        · have hm0 : m 0 = 0 := Finsupp.notMem_support_iff.mp h0
          rw [hm0, pow_zero, one_mul]
          refine Finset.prod_congr rfl fun i hi => ?_
          cases i with
          | zero => exact absurd hi h0
          | succ j => rfl
      rw [hsplit_Q]
      have hexp : (PowerSeries.X : PowerSeries ℂ) ^ (M - wt m + m 0) * PowerSeries.X ^ (wt m) =
          PowerSeries.X ^ M * PowerSeries.X ^ (m 0) := by
        rw [← pow_add, ← pow_add, show M - wt m + m 0 + wt m = M + m 0 by have := hwt_le m hm; omega]
      calc (PowerSeries.C (Q.coeff m) * PowerSeries.X ^ (M - wt m + m 0)) *
            (PowerSeries.X ^ wt m * ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => seriesJet E j ^ m (j + 1))
          = PowerSeries.C (Q.coeff m) * (PowerSeries.X ^ (M - wt m + m 0) * PowerSeries.X ^ wt m) *
              ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => seriesJet E j ^ m (j + 1) := by ring
        _ = PowerSeries.C (Q.coeff m) * (PowerSeries.X ^ M * PowerSeries.X ^ m 0) *
              ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => seriesJet E j ^ m (j + 1) := by rw [hexp]
        _ = PowerSeries.X ^ M * (PowerSeries.C (Q.coeff m) *
              (PowerSeries.X ^ m 0 * ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => seriesJet E j ^ m (j + 1))) := by ring
    rw [heq, hQ, mul_zero]
  let N := maxUDegA P_X
  let P_u : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := revMvPolyA N P_X
  have hNP : ∀ α, (P_X.coeff α).natDegree ≤ N := natDegree_le_maxUDegA P_X
  have hrev_inv : ∀ p : Polynomial ℂ, p.natDegree ≤ N → revPolyA N (revPolyA N p) = p := fun p hp => by
    ext k
    have hcoeff : ∀ (q : Polynomial ℂ) (m : ℕ),
        (revPolyA N q).coeff m = if m ≤ N then q.coeff (N - m) else 0 := fun q m => by
      have hsc : (revPolyA N q).coeff m =
          ∑ i ∈ Finset.range (N + 1), (Polynomial.C (q.coeff i) * Polynomial.X ^ (N - i)).coeff m := by
        unfold revPolyA
        simpa only [Polynomial.lcoeff_apply] using
          map_sum (Polynomial.lcoeff ℂ m) (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ (N - i)) (Finset.range (N + 1))
      rw [hsc]
      simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hm : m ≤ N
      · rw [ite_eq_left_iff.mpr fun h => absurd hm h, Finset.sum_eq_single (N - m)]
        · have heq : N - (N - m) = m := by omega
          simp [heq]
        · intro i hi hne
          have hi_le : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hne' : m ≠ N - i := by omega
          simp [hne']
        · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
      · rw [ite_eq_right_iff.mpr fun h => absurd h hm]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi_le : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hne' : m ≠ N - i := by omega
        simp [hne']
    rw [hcoeff, hcoeff]
    by_cases hk : k ≤ N
    · have h1 : N - k ≤ N := by omega
      have h2 : N - (N - k) = k := by omega
      simp [hk, h1, h2]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hk]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hcoeff_Pu : ∀ α, P_u.coeff α = revPolyA N (P_X.coeff α) := fun α => by
    dsimp only [P_u, revMvPolyA]
    rw [MvPolynomial.coeff_sum]; simp_rw [MvPolynomial.coeff_monomial]
    by_cases hmem : α ∈ P_X.support
    · rw [Finset.sum_eq_single α]
      · simp
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hmem hnot
    · have h0 : (∑ x ∈ P_X.support, if x = α then revPolyA N (P_X.coeff x) else 0) = 0 :=
        Finset.sum_eq_zero fun β hβ => by simp [show β ≠ α from fun h => hmem (h ▸ hβ)]
      rw [h0, MvPolynomial.notMem_support_iff.mp hmem]
      unfold revPolyA; simp
  have hPu_deg : ∀ α, (P_u.coeff α).natDegree ≤ N := fun α => by
    rw [hcoeff_Pu α]; unfold revPolyA
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_X_pow_le _).trans (Nat.sub_le N k))
  have hPu_zero : formalEvalPoly S P_u = 0 := by
    have hlink : HahnSeries.single (N : ℤ) (1 : ℂ) * formalEvalPoly S P_u =
        ((evS P_X : PowerSeries ℂ) : LaurentSeries ℂ) := by
      have hP_sum := MvPolynomial.as_sum P_u
      conv_lhs => arg 2; unfold formalEvalPoly; rw [hP_sum]
      rw [MvPolynomial.eval₂_sum, Finset.mul_sum]
      have hPX_rev : P_X = revMvPolyA N P_u := by
        apply MvPolynomial.ext; intro α
        have hrhs : (revMvPolyA N P_u).coeff α = ∑ x ∈ P_u.support, if x = α then revPolyA N (P_u.coeff x) else 0 := by
          unfold revMvPolyA
          rw [MvPolynomial.coeff_sum]
          simp_rw [MvPolynomial.coeff_monomial]
        rw [hrhs]
        by_cases hα : α ∈ P_u.support
        · rw [Finset.sum_eq_single α]
          · simp only [↓reduceIte, hcoeff_Pu α]; exact (hrev_inv _ (hNP α)).symm
          · intro β _ hβα; simp [hβα]
          · intro hnot; exact absurd hα hnot
        · have h0 : (∑ x ∈ P_u.support, if x = α then revPolyA N (P_u.coeff x) else 0) = 0 :=
            Finset.sum_eq_zero fun β hβ => by simp [show β ≠ α from fun h => hα (h ▸ hβ)]
          rw [h0]
          have hPu0 : revPolyA N (P_X.coeff α) = 0 := by
            rw [← hcoeff_Pu α]; exact MvPolynomial.notMem_support_iff.mp hα
          have h2 := congrArg (revPolyA N) hPu0
          rw [hrev_inv _ (hNP α)] at h2
          exact h2.trans (by unfold revPolyA; simp)
      conv_rhs => rw [hPX_rev]; unfold revMvPolyA; rw [map_sum]
      simp_rw [MvPolynomial.eval₂_monomial]
      change ∑ α ∈ P_u.support, HahnSeries.single (N : ℤ) 1 *
          (polyToLaurent (P_u.coeff α) * α.prod fun i e => ((d_u^[i.val] S : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
        HahnSeries.ofPowerSeries ℤ ℂ
          (∑ α ∈ P_u.support, evS (MvPolynomial.monomial α (revPolyA N (P_u.coeff α))))
      rw [map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hev_mon : evS (MvPolynomial.monomial α (revPolyA N (P_u.coeff α))) =
          Polynomial.coeToPowerSeries.ringHom (revPolyA N (P_u.coeff α)) *
            α.prod fun i e => (d_u^[i.val] S) ^ e :=
        MvPolynomial.eval₂_monomial _ _
      rw [hev_mon]
      have hpow_eq : (α.prod fun i e => ((d_u^[i.val] S : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
          ((α.prod fun i e => (d_u^[i.val] S) ^ e : PowerSeries ℂ) : LaurentSeries ℂ) := by
        simp only [Finsupp.prod, map_prod, map_pow]
      rw [hpow_eq, ← mul_assoc, single_mul_polyToLaurentA (P_u.coeff α) (hPu_deg α), map_mul,
        Polynomial.coeToPowerSeries.ringHom_apply]
    rw [hPX_eval_S, map_zero] at hlink
    have hunit : HahnSeries.single (-(N : ℤ)) (1 : ℂ) * HahnSeries.single (N : ℤ) (1 : ℂ) = 1 := by
      rw [HahnSeries.single_mul_single, neg_add_cancel, one_mul]; rfl
    calc formalEvalPoly S P_u = 1 * formalEvalPoly S P_u := (one_mul _).symm
      _ = HahnSeries.single (-(N : ℤ)) 1 * (HahnSeries.single (N : ℤ) 1 * formalEvalPoly S P_u) := by
            rw [← mul_assoc, hunit]
      _ = 0 := by rw [hlink, mul_zero]
  have hPu_eq0 : P_u = 0 := hno P_u hPu_zero
  have hPX_eq0 : P_X = 0 := by
    apply MvPolynomial.ext; intro α
    have hα : revPolyA N (P_X.coeff α) = 0 := by rw [← hcoeff_Pu α, hPu_eq0]; rfl
    have h2 := congrArg (revPolyA N) hα
    rw [hrev_inv _ (hNP α)] at h2
    exact h2.trans (by unfold revPolyA; simp)
  have hinf_ne0 : ({c : ℂ | c ≠ 0} : Set ℂ).Infinite := by
    have : ({c : ℂ | c ≠ 0} : Set ℂ) = Set.univ \ {0} := by ext c; simp
    rw [this]; exact Set.infinite_univ.sdiff (Set.finite_singleton 0)
  refine MvPolynomial.funext_set (fun i => if i = 0 then {c : ℂ | c ≠ 0} else Set.univ)
    (fun i => by split_ifs; exact hinf_ne0; exact Set.infinite_univ) fun z hz => ?_
  have hz0 : z 0 ≠ 0 := by simpa using hz 0 (Set.mem_univ 0)
  have hsolve : ∀ n : ℕ, ∃ y : ℕ → ℂ, ∀ j < n,
      MvPolynomial.eval y (MvPolynomial.map (Polynomial.evalRingHom (z 0)) (toXJet j)) =
        (z 0) ^ (2 * j + 2) * z (j + 1) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => 0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨Rm, hRm_vars, hRm_eq⟩ := toXJet_triangular m
      let y_val : ℂ := ((-1 : ℂ) ^ m)⁻¹ *
        ((z 0) ^ (2 * m + 2) * z (m + 1) - MvPolynomial.eval y (MvPolynomial.map (Polynomial.evalRingHom (z 0)) Rm))
      refine ⟨Function.update y m y_val, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | hjeq
      · have hcongr : MvPolynomial.eval (Function.update y m y_val)
              (MvPolynomial.map (Polynomial.evalRingHom (z 0)) (toXJet j)) =
            MvPolynomial.eval y (MvPolynomial.map (Polynomial.evalRingHom (z 0)) (toXJet j)) :=
          eval_congr_vars fun k hk =>
            Function.update_of_ne (ne_of_lt (lt_of_le_of_lt
              (toXJet_vars_le j k (MvPolynomial.vars_map _ _ hk)) hlt)) _ _
        rw [hcongr]; exact hy j hlt
      · rw [hjeq, hRm_eq, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
          map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Polynomial.coe_evalRingHom, Polynomial.eval_C, Function.update_self]
        have hRm_congr : MvPolynomial.eval (Function.update y m y_val)
              (MvPolynomial.map (Polynomial.evalRingHom (z 0)) Rm) =
            MvPolynomial.eval y (MvPolynomial.map (Polynomial.evalRingHom (z 0)) Rm) :=
          eval_congr_vars fun k hk =>
            Function.update_of_ne (ne_of_lt (hRm_vars k (MvPolynomial.vars_map _ _ hk))) _ _
        rw [hRm_congr]
        have hsign : (-1 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
        dsimp only [y_val]
        rw [← mul_assoc, mul_inv_cancel₀ hsign, one_mul, sub_add_cancel]
  obtain ⟨yfull, hyfull⟩ := hsolve (r + 1)
  let yfin : Fin (r + 1) → ℂ := fun i => yfull i.val
  have hy_jet : ∀ j ≤ r, MvPolynomial.eval yfin (evalU (jetFin j) (z 0)) = (z 0) ^ (2 * j + 2) * z (j + 1) := by
    intro j hj
    rw [hjetFin_eval_C j hj (z 0) yfin]
    have hcongr : MvPolynomial.eval (fun k => if hk : k < r + 1 then yfin ⟨k, hk⟩ else 0)
          (MvPolynomial.map (Polynomial.evalRingHom (z 0)) (toXJet j)) =
        MvPolynomial.eval yfull (MvPolynomial.map (Polynomial.evalRingHom (z 0)) (toXJet j)) :=
      eval_congr_vars fun k hk => by
        have hk_lt : k < r + 1 := Nat.lt_succ_of_le ((toXJet_vars_le j k (MvPolynomial.vars_map _ _ hk)).trans hj)
        simp [yfin, hk_lt]
    rw [hcongr]; exact hyfull j (Nat.lt_succ_of_le hj)
  have heval0 : MvPolynomial.eval yfin (evalU P_X (z 0)) = 0 := by rw [hPX_eq0, evalU, map_zero, map_zero]
  have heval_Q : MvPolynomial.eval yfin (evalU P_X (z 0)) = (z 0) ^ M * MvPolynomial.eval z Q := by
    dsimp only [P_X, evalU]
    rw [map_sum, map_sum]
    conv_rhs => rw [MvPolynomial.as_sum Q, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    dsimp only [monP]
    rw [map_mul, MvPolynomial.map_C, map_mul, MvPolynomial.eval_C, Polynomial.coe_evalRingHom,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Finsupp.prod, map_prod, map_prod, MvPolynomial.eval_monomial]
    have hprod : (∏ i ∈ m.support, MvPolynomial.eval yfin
          (MvPolynomial.map (Polynomial.evalRingHom (z 0)) (match i with | 0 => 1 | j + 1 => jetFin j ^ m i))) =
        (z 0) ^ wt m * ∏ i ∈ m.support, match i with | 0 => (1 : ℂ) | j + 1 => z (j + 1) ^ m (j + 1) := by
      have hstep : ∀ i ∈ m.support,
          MvPolynomial.eval yfin (MvPolynomial.map (Polynomial.evalRingHom (z 0))
            (match i with | 0 => 1 | j + 1 => jetFin j ^ m i)) =
          (z 0) ^ (match i with | 0 => 0 | j + 1 => (2 * j + 2) * m (j + 1)) *
            (match i with | 0 => (1 : ℂ) | j + 1 => z (j + 1) ^ m (j + 1)) := fun i hi => by
        cases i with
        | zero => simp
        | succ j =>
          have hj_le : j ≤ r := Nat.le_of_lt (Nat.lt_of_succ_le (hr_bound (j + 1)
            ((MvPolynomial.mem_vars_iff_mem_support (j + 1)).mpr ⟨m, hm, hi⟩)))
          rw [map_pow, map_pow]
          change (MvPolynomial.eval yfin (evalU (jetFin j) (z 0))) ^ m (j + 1) = _
          rw [hy_jet j hj_le, mul_pow, ← pow_mul]
      rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      congr 2; exact Finset.sum_congr rfl fun i _ => by cases i <;> rfl
    rw [hprod]
    have hsplit_z : (m.prod fun i e => z i ^ e) =
        (z 0) ^ m 0 * ∏ i ∈ m.support, match i with | 0 => (1 : ℂ) | j + 1 => z (j + 1) ^ m (j + 1) := by
      unfold Finsupp.prod
      by_cases h0 : (0 : ℕ) ∈ m.support
      · rw [← Finset.mul_prod_erase m.support _ h0, ← Finset.mul_prod_erase m.support _ h0, one_mul]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        cases i with
        | zero => exact absurd rfl (Finset.mem_erase.mp hi).1
        | succ j => rfl
      · rw [Finsupp.notMem_support_iff.mp h0, pow_zero, one_mul]
        refine Finset.prod_congr rfl fun i hi => ?_
        cases i with
        | zero => exact absurd hi h0
        | succ j => rfl
    rw [hsplit_z]
    have hexp : (z 0) ^ (M - wt m + m 0) * (z 0) ^ wt m = (z 0) ^ M * (z 0) ^ m 0 := by
      rw [← pow_add, ← pow_add, show M - wt m + m 0 + wt m = M + m 0 by have := hwt_le m hm; omega]
    calc (Q.coeff m * (z 0) ^ (M - wt m + m 0)) *
          ((z 0) ^ wt m * ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => z (j + 1) ^ m (j + 1))
        = Q.coeff m * ((z 0) ^ (M - wt m + m 0) * (z 0) ^ wt m) *
            ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => z (j + 1) ^ m (j + 1) := by ring
      _ = Q.coeff m * ((z 0) ^ M * (z 0) ^ m 0) *
            ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => z (j + 1) ^ m (j + 1) := by rw [hexp]
      _ = (z 0) ^ M * (Q.coeff m * ((z 0) ^ m 0 *
            ∏ i ∈ m.support, match i with | 0 => 1 | j + 1 => z (j + 1) ^ m (j + 1))) := by ring
  rw [heval_Q] at heval0
  exact (mul_eq_zero.mp heval0).resolve_left (pow_ne_zero M hz0)

/-- **Master Unconditional Half-Integer Borel-Euler Differential Transcendence Theorem**:
For ANY positive-ray simple-pole meromorphic Borel kernel `ψ` (`MeromorphicBorelData ψ ω res`),
the formal Gevrey-1 Euler series `eulerSeriesOf ψ ∈ ℂ[[t]]` is unconditionally differentially
transcendental over `ℂ(t)` (`AlgebraicIndependent ℂ (seriesCoordinates (eulerSeriesOf ψ))`). -/
theorem eulerSeries_algebraicIndependent_of_meromorphicBorel {ψ ω res}
    (h : MeromorphicBorelData ψ ω res) :
    AlgebraicIndependent ℂ (seriesCoordinates (eulerSeriesOf ψ)) := by
  refine algebraicIndependent_of_X_sq_mul_no_ade fun P hP => ?_
  have h0_mem : (0 : ℂ) ∈ puncturedWedge h.θ₀ h.ε ω :=
    ⟨Or.inl (by simp [h.hε_pos]), by
      rintro ⟨m, hm⟩
      dsimp only at hm
      exact (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).ne'
        (by exact_mod_cast hm)⟩
  rw [← formalSeries_abelConv_eq (h.analyticOn 0 h0_mem)] at hP
  exact abelConv_no_ade h P hP

/-! ### 5. General Torus Knots `T(p, q)` (`2 ≤ p`, `2 ≤ q`, `Nat.Coprime p q`) & Fishburn Euler Series -/

/-! #### 5A. Entire Even-Sinc Kernel `sinSqrt z = sin(√z) / √z` -/

/-- Entire even-sinc function `sinSqrt z = sinhSqrt (-z)` satisfying `s * sinSqrt (s^2) = sin s`. -/
@[expose] def sinSqrt (z : ℂ) : ℂ := sinhSqrt (-z)

lemma sinSqrt_analyticAt (z : ℂ) : AnalyticAt ℂ sinSqrt z :=
  (sinhSqrt_analyticAt (-z)).comp analyticAt_id.neg

lemma sinSqrt_differentiable : Differentiable ℂ sinSqrt := fun z =>
  (sinSqrt_analyticAt z).differentiableAt

lemma sinSqrt_zero : sinSqrt 0 = 1 := by simp [sinSqrt, sinhSqrt_zero]

/-- Exact trigonometric identity `s * sinSqrt (s^2) = Complex.sin s` for all `s : ℂ`. -/
theorem mul_sinSqrt_sq (s : ℂ) : s * sinSqrt (s ^ 2) = Complex.sin s := by
  have h := mul_sinhSqrt_sq (s * I)
  have hsq : (s * I) ^ 2 = -(s ^ 2) := by rw [mul_pow, Complex.I_sq]; ring
  rw [hsq, Complex.sinh_mul_I] at h
  have heq : (s * sinSqrt (s ^ 2)) * I = Complex.sin s * I := by
    unfold sinSqrt; linear_combination h
  exact mul_right_cancel₀ Complex.I_ne_zero heq

lemma deriv_sinSqrt_sq (s : ℂ) :
    2 * s ^ 2 * deriv sinSqrt (s ^ 2) + sinSqrt (s ^ 2) = Complex.cos s := by
  have h1 : HasDerivAt (fun w : ℂ => w * sinSqrt (w ^ 2))
      (1 * sinSqrt (s ^ 2) + s * (deriv sinSqrt (s ^ 2) * (2 * s))) s := by
    have hd1 : HasDerivAt sinSqrt (deriv sinSqrt (s ^ 2)) (s ^ 2) :=
      (sinSqrt_differentiable (s ^ 2)).hasDerivAt
    have hd2 : HasDerivAt (fun w : ℂ => w ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    exact (hasDerivAt_id s).mul (HasDerivAt.comp (h := fun w : ℂ => w ^ 2) (h₂ := sinSqrt) s hd1 hd2)
  have h2 : HasDerivAt (fun w : ℂ => w * sinSqrt (w ^ 2)) (Complex.cos s) s := by
    rw [show (fun w : ℂ => w * sinSqrt (w ^ 2)) = Complex.sin from funext mul_sinSqrt_sq]
    exact Complex.hasDerivAt_sin s
  linear_combination h1.unique h2

lemma sinSqrt_eq_zero_iff (z : ℂ) :
    sinSqrt z = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ z = ((Real.pi * (n : ℝ)) ^ 2 : ℝ) := by
  constructor
  · intro hz
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = z := by
      by_cases hz0 : z = 0
      · exact ⟨0, by simp [hz0]⟩
      · refine ⟨Complex.exp (Complex.log z / 2), ?_⟩
        rw [sq, ← Complex.exp_add, add_halves, Complex.exp_log hz0]
    subst hs
    have hs_ne : s ≠ 0 := by intro h0; subst h0; simp [sinSqrt_zero] at hz
    have hsin0 : Complex.sin s = 0 := by rw [← mul_sinSqrt_sq, hz, mul_zero]
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin0
    have hk_ne : k ≠ 0 := by intro h0; subst h0; apply hs_ne; simpa using hk
    refine ⟨k.natAbs, Int.natAbs_pos.mpr hk_ne, ?_⟩
    rw [hk]
    have hsqC : (k : ℂ) ^ 2 = (k.natAbs : ℂ) ^ 2 := by
      have hZ : (k : ℤ) ^ 2 = ((k.natAbs : ℤ) ^ 2) := (Int.natAbs_sq k).symm
      have hC := congrArg (Int.cast : ℤ → ℂ) hZ
      simpa only [Int.cast_pow, Int.cast_natCast] using hC
    push_cast; rw [mul_pow, hsqC]; ring
  · rintro ⟨n, hn, rfl⟩
    let r : ℝ := Real.pi * (n : ℝ)
    have hr_pos : 0 < r := mul_pos Real.pi_pos (Nat.cast_pos.mpr hn)
    have hmul := mul_sinSqrt_sq (r : ℂ)
    have hsin0 : Complex.sin (r : ℂ) = 0 := by
      rw [← Complex.ofReal_sin, Real.sin_eq_zero_iff.mpr ⟨(n : ℤ), by dsimp only [r]; push_cast; ring⟩,
        Complex.ofReal_zero]
    rw [hsin0] at hmul
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
    have hsq : ((r : ℂ) ^ 2) = (((Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) := by dsimp only [r]; push_cast; ring
    rw [← hsq]
    exact (mul_eq_zero.mp hmul).resolve_left hrC

lemma deriv_sinSqrt_at_zero_val {n : ℕ} (hn : 1 ≤ n) :
    deriv sinSqrt (((Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) =
      (-1 : ℂ) ^ n / (2 * ((Real.pi * (n : ℝ)) ^ 2 : ℂ)) := by
  let r : ℝ := Real.pi * (n : ℝ)
  have hr_pos : 0 < r := mul_pos Real.pi_pos (Nat.cast_pos.mpr hn)
  have hd := deriv_sinSqrt_sq (r : ℂ)
  have hsq : ((r : ℂ) ^ 2) = (((Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) := by dsimp only [r]; push_cast; ring
  have h0 : sinSqrt ((r : ℂ) ^ 2) = 0 := by
    rw [hsq]; exact (sinSqrt_eq_zero_iff _).mpr ⟨n, hn, rfl⟩
  have hcos : Complex.cos (r : ℂ) = (-1 : ℂ) ^ n := by
    rw [← Complex.ofReal_cos]
    have hr_eq : r = (n : ℝ) * Real.pi := mul_comm Real.pi (n : ℝ)
    rw [hr_eq, Real.cos_nat_mul_pi]; push_cast; rfl
  rw [h0, add_zero, hcos, hsq] at hd
  have hden : (2 : ℂ) * ((Real.pi * (n : ℝ)) ^ 2 : ℂ) ≠ 0 := by
    have : 0 < 2 * (Real.pi * (n : ℝ)) ^ 2 := by positivity
    exact_mod_cast this.ne'
  rw [eq_div_iff hden]
  push_cast at hd ⊢
  linear_combination hd

lemma deriv_sinSqrt_at_zero_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    deriv sinSqrt (((Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) ≠ 0 := by
  rw [deriv_sinSqrt_at_zero_val hn]
  refine div_ne_zero (pow_ne_zero n (by norm_num)) ?_
  have : 0 < 2 * (Real.pi * (n : ℝ)) ^ 2 := by positivity
  exact_mod_cast this.ne'

/-! #### 5B. General Torus Knot `T(p, q)` Borel Kernel, Poles, and `MeromorphicBorelData` -/

/-- Removable-singularity-cleared Borel kernel `φ_{p,q}(z)` for the torus knot `T(p, q)`, satisfying
`s * torusKnotBorel p q (s^2) = sin(p s) sin(q s) / sin(p q s)` away from poles. -/
@[expose] def torusKnotBorel (p q : ℕ) (z : ℂ) : ℂ :=
  if sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * z) = 0 then
    deriv (fun w => sinSqrt ((p : ℂ) ^ 2 * w) * sinSqrt ((q : ℂ) ^ 2 * w)) z /
      deriv (fun w => sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * w)) z
  else
    (sinSqrt ((p : ℂ) ^ 2 * z) * sinSqrt ((q : ℂ) ^ 2 * z)) /
      sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * z)

/-- Rescaled Borel kernel `ψ_{p,q}(z) = 2 * φ_{p,q}(4 z)` whose `eulerSeriesOf` matches
`∑_k (T_k^{(p,q)} / k!) X^k` identically. -/
@[expose] def torusKnotPsi (p q : ℕ) (z : ℂ) : ℂ :=
  2 * torusKnotBorel p q (4 * z)

/-- Active simple-pole index sequence for `T(p, q)`: the strictly increasing enumeration of all
integers `n ≥ 1` with `p ∤ n` and `q ∤ n`. -/
@[expose] def torusKnotPoleIndex (p q : ℕ) : ℕ → ℕ :=
  Nat.nth (fun n => 1 ≤ n ∧ ¬ p ∣ n ∧ ¬ q ∣ n)

/-- Simple-pole frequencies `ω_m = (π * n_m / (2 p q))^2` of `torusKnotPsi p q`. -/
@[expose] def torusKnotFreq (p q : ℕ) (m : ℕ) : ℝ :=
  (Real.pi * (torusKnotPoleIndex p q m : ℝ) / (2 * ((p * q : ℕ) : ℝ))) ^ 2

/-- Exact nonzero simple-pole residue of `torusKnotPsi p q` at `torusKnotFreq p q m`. -/
@[expose] def torusKnotRes (p q : ℕ) (m : ℕ) : ℂ :=
  2 * (sinSqrt ((p : ℂ) ^ 2 * (4 * (torusKnotFreq p q m : ℂ))) *
        sinSqrt ((q : ℂ) ^ 2 * (4 * (torusKnotFreq p q m : ℂ)))) /
    (4 * (((p * q : ℕ) : ℂ) ^ 2 * deriv sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * (4 * (torusKnotFreq p q m : ℂ)))))

private lemma torusKnot_active_infinite {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ ¬ p ∣ n ∧ ¬ q ∣ n} := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => k * (p * q) + 1)
    (fun a b hab => by
      have hpq : 0 < p * q := by positivity
      have h1 : a * (p * q) = b * (p * q) := Nat.add_right_cancel hab
      exact Nat.eq_of_mul_eq_mul_right hpq h1)
    fun k => ?_
  refine ⟨by omega, ?_, ?_⟩
  · intro hd
    have hmod : (k * (p * q) + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hd
    have hmod1 : (k * (p * q) + 1) % p = 1 % p := by
      rw [show k * (p * q) + 1 = p * (k * q) + 1 by ring, Nat.mul_add_mod]
    rw [hmod1, Nat.mod_eq_of_lt (by omega)] at hmod
    exact Nat.one_ne_zero hmod
  · intro hd
    have hmod : (k * (p * q) + 1) % q = 0 := Nat.mod_eq_zero_of_dvd hd
    have hmod1 : (k * (p * q) + 1) % q = 1 % q := by
      rw [show k * (p * q) + 1 = q * (k * p) + 1 by ring, Nat.mul_add_mod]
    rw [hmod1, Nat.mod_eq_of_lt (by omega)] at hmod
    exact Nat.one_ne_zero hmod

private lemma torusKnotPoleIndex_spec {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (m : ℕ) :
    1 ≤ torusKnotPoleIndex p q m ∧ ¬ p ∣ torusKnotPoleIndex p q m ∧ ¬ q ∣ torusKnotPoleIndex p q m :=
  Nat.nth_mem_of_infinite (torusKnot_active_infinite hp hq) m

private lemma torusKnotPoleIndex_strictMono {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StrictMono (torusKnotPoleIndex p q) :=
  Nat.nth_strictMono (torusKnot_active_infinite hp hq)

private lemma torusKnotFreq_strictMono {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StrictMono (torusKnotFreq p q) := fun a b hab => by
  unfold torusKnotFreq
  have hpq : (0 : ℝ) < 2 * ((p * q : ℕ) : ℝ) := by positivity
  have h1 : (torusKnotPoleIndex p q a : ℝ) < (torusKnotPoleIndex p q b : ℝ) :=
    Nat.cast_lt.mpr (torusKnotPoleIndex_strictMono hp hq hab)
  have hlt : Real.pi * (torusKnotPoleIndex p q a : ℝ) / (2 * ((p * q : ℕ) : ℝ)) <
      Real.pi * (torusKnotPoleIndex p q b : ℝ) / (2 * ((p * q : ℕ) : ℝ)) :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h1 Real.pi_pos) hpq
  have hnn : 0 ≤ Real.pi * (torusKnotPoleIndex p q a : ℝ) / (2 * ((p * q : ℕ) : ℝ)) := by positivity
  exact sq_lt_sq' (by linarith) hlt

private lemma torusKnotFreq_pos {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (m : ℕ) :
    0 < torusKnotFreq p q m := by
  unfold torusKnotFreq
  have h1 : 1 ≤ torusKnotPoleIndex p q m := (torusKnotPoleIndex_spec hp hq m).1
  have : (0 : ℝ) < (torusKnotPoleIndex p q m : ℝ) := Nat.cast_pos.mpr h1
  have : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by positivity
  positivity

private lemma torusKnotDen_zero_iff {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (z : ℂ) :
    sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * z) = 0 ↔
      ∃ n : ℕ, 1 ≤ n ∧ z = ((Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ) := by
  rw [sinSqrt_eq_zero_iff]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpqC : (((p * q : ℕ) : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by positivity))
  constructor
  · rintro ⟨n, hn, heq⟩
    refine ⟨n, hn, ?_⟩
    apply mul_left_cancel₀ hpqC
    rw [heq]; push_cast; field_simp [hp0, hq0]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n, hn, ?_⟩
    push_cast; field_simp [hp0, hq0]

private lemma torusKnotNum_zero_at_den_zero {p q n : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    sinSqrt ((p : ℂ) ^ 2 * ((Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ)) *
      sinSqrt ((q : ℂ) ^ 2 * ((Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ)) = 0 ↔
    (p ∣ n ∨ q ∣ n) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have harg_p : (p : ℂ) ^ 2 * (((Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) =
      (((Real.pi * (n : ℝ) / (q : ℝ)) ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp [hp0, hq0]
  have harg_q : (q : ℂ) ^ 2 * (((Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) =
      (((Real.pi * (n : ℝ) / (p : ℝ)) ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp [hp0, hq0]
  rw [mul_eq_zero, harg_p, harg_q, sinSqrt_eq_zero_iff, sinSqrt_eq_zero_iff]
  have hdiv_iff : ∀ (d : ℕ), 2 ≤ d →
      ((∃ k : ℕ, 1 ≤ k ∧ ((((Real.pi * (n : ℝ) / (d : ℝ)) ^ 2 : ℝ) : ℂ) = ((Real.pi * (k : ℝ)) ^ 2 : ℝ))) ↔
        d ∣ n) := fun d hd => by
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    constructor
    · rintro ⟨k, _, hk⟩
      have hreal : (Real.pi * (n : ℝ) / (d : ℝ)) ^ 2 = (Real.pi * (k : ℝ)) ^ 2 := by exact_mod_cast hk
      have hpos1 : 0 ≤ Real.pi * (n : ℝ) / (d : ℝ) := by positivity
      have hpos2 : 0 ≤ Real.pi * (k : ℝ) := by positivity
      have heq1 : Real.pi * (n : ℝ) / (d : ℝ) = Real.pi * (k : ℝ) := by nlinarith
      have heq2 : (n : ℝ) = (d : ℝ) * (k : ℝ) := by
        have h1 : Real.pi * (n : ℝ) = Real.pi * ((d : ℝ) * (k : ℝ)) := by
          have := (div_eq_iff hd0).mp heq1; linarith
        exact mul_left_cancel₀ Real.pi_ne_zero h1
      have hnat : n = d * k := by exact_mod_cast heq2
      exact ⟨k, hnat⟩
    · rintro ⟨k, rfl⟩
      have hk1 : 1 ≤ k := by
        by_contra hk0; have : k = 0 := by omega
        subst this; simp at hn
      refine ⟨k, hk1, ?_⟩
      push_cast; field_simp [hdC]
  rw [hdiv_iff q hq, hdiv_iff p hp, or_comm]

private lemma torusKnotBorel_analyticAt_of_removable {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (z₀ : ℂ)
    (hgood : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → ¬ q ∣ n →
      z₀ ≠ ((Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ)) :
    AnalyticAt ℂ (torusKnotBorel p q) z₀ := by
  let num : ℂ → ℂ := fun w => sinSqrt ((p : ℂ) ^ 2 * w) * sinSqrt ((q : ℂ) ^ 2 * w)
  let den : ℂ → ℂ := fun w => sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * w)
  have hnum_an : ∀ w : ℂ, AnalyticAt ℂ num w := fun w =>
    ((sinSqrt_analyticAt _).comp (analyticAt_const.mul analyticAt_id)).mul
      ((sinSqrt_analyticAt _).comp (analyticAt_const.mul analyticAt_id))
  have hden_an : ∀ w : ℂ, AnalyticAt ℂ den w := fun w =>
    (sinSqrt_analyticAt _).comp (analyticAt_const.mul analyticAt_id)
  by_cases hden0 : den z₀ = 0
  · obtain ⟨n, hn, hz₀_eq⟩ := (torusKnotDen_zero_iff hp hq z₀).mp hden0
    have hdvd : p ∣ n ∨ q ∣ n := by
      by_contra hnot; push Not at hnot
      exact hgood n hn hnot.1 hnot.2 hz₀_eq
    have hnum0 : num z₀ = 0 := by
      rw [hz₀_eq]; exact (torusKnotNum_zero_at_den_zero hp hq hn).mpr hdvd
    have hderiv_den : deriv den z₀ ≠ 0 := by
      have hhd : HasDerivAt den (deriv sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * z₀) * (((p * q : ℕ) : ℂ) ^ 2)) z₀ := by
        have hlin : HasDerivAt (fun w : ℂ => (((p * q : ℕ) : ℂ) ^ 2) * w) (((p * q : ℕ) : ℂ) ^ 2) z₀ := by
          simpa using (hasDerivAt_id z₀).const_mul (((p * q : ℕ) : ℂ) ^ 2)
        exact ((sinSqrt_differentiable _).hasDerivAt).comp z₀ hlin
      rw [hhd.deriv]
      have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpqC : (((p * q : ℕ) : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by positivity))
      have harg : (((p * q : ℕ) : ℂ) ^ 2) * z₀ = (((Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) := by
        rw [hz₀_eq]; push_cast; field_simp [hp0, hq0]
      rw [harg]
      exact mul_ne_zero (deriv_sinSqrt_at_zero_ne_zero hn) hpqC
    have hdn_an : AnalyticAt ℂ (dslope num z₀) z₀ :=
      ((Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 z₀)).mpr
        (fun w _ => (hnum_an w).differentiableAt.differentiableWithinAt)).analyticAt Filter.univ_mem
    have hdd_an : AnalyticAt ℂ (dslope den z₀) z₀ :=
      ((Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 z₀)).mpr
        (fun w _ => (hden_an w).differentiableAt.differentiableWithinAt)).analyticAt Filter.univ_mem
    have hdd_ne : dslope den z₀ z₀ ≠ 0 := by rw [dslope_same]; exact hderiv_den
    have hquot_an : AnalyticAt ℂ (fun w => dslope num z₀ w / dslope den z₀ w) z₀ :=
      hdn_an.div hdd_an hdd_ne
    have hloc_ne : ∀ᶠ w in 𝓝 z₀, dslope den z₀ w ≠ 0 :=
      hdd_an.continuousAt.eventually_ne hdd_ne
    refine hquot_an.congr ?_
    filter_upwards [hloc_ne] with w hw
    by_cases hw0 : w = z₀
    · subst hw0
      simp only [torusKnotBorel, dslope_same]
      rw [ite_eq_left_iff.mpr fun h => absurd hden0 h]
    · have hden_w_ne : den w ≠ 0 := by
        intro h0
        apply hw
        rw [dslope_of_ne den hw0, slope_def_field, h0, hden0, sub_self, zero_div]
      simp only [torusKnotBorel]
      rw [ite_eq_right_iff.mpr fun h => absurd h hden_w_ne]
      rw [dslope_of_ne num hw0, dslope_of_ne den hw0, slope_def_field, slope_def_field, hnum0, hden0,
        sub_zero, sub_zero]
      have hsub_ne : w - z₀ ≠ 0 := sub_ne_zero.mpr hw0
      dsimp only [num, den]
      field_simp [hsub_ne]
  · have hloc_ne : ∀ᶠ w in 𝓝 z₀, den w ≠ 0 := (hden_an z₀).continuousAt.eventually_ne hden0
    refine ((hnum_an z₀).div (hden_an z₀) hden0).congr ?_
    filter_upwards [hloc_ne] with w hw
    simp only [torusKnotBorel]
    rw [ite_eq_right_iff.mpr fun h => absurd h hw]
    rfl

private lemma torusKnotBorel_eq_trig {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {s : ℂ}
    (hs : s ≠ 0) (hden : Complex.sin (((p * q : ℕ) : ℂ) * s) ≠ 0) :
    s * torusKnotBorel p q (s ^ 2) =
      Complex.sin ((p : ℂ) * s) * Complex.sin ((q : ℂ) * s) / Complex.sin (((p * q : ℕ) : ℂ) * s) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpqC : ((p * q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  have hsin_pq := mul_sinSqrt_sq (((p * q : ℕ) : ℂ) * s)
  have hsin_p := mul_sinSqrt_sq ((p : ℂ) * s)
  have hsin_q := mul_sinSqrt_sq ((q : ℂ) * s)
  have hden_ne : sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * s ^ 2) ≠ 0 := by
    intro h0; apply hden
    rw [← hsin_pq, mul_pow, h0, mul_zero]
  unfold torusKnotBorel
  rw [ite_eq_right_iff.mpr fun h => absurd h hden_ne]
  rw [← hsin_p, ← hsin_q, ← hsin_pq, mul_pow, mul_pow, mul_pow]
  have hpq_mul : ((p * q : ℕ) : ℂ) = (p : ℂ) * (q : ℂ) := by push_cast; ring
  rw [hpq_mul] at hden_ne ⊢
  field_simp [hs, hpC, hqC, hden_ne]

private lemma norm_csin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have h2 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have he1 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have he2 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  calc ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ / 2
      ≤ (‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖) / 2 :=
        div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by linarith
    _ = Real.exp |w.im| := by ring

private lemma quarter_exp_le_norm_csin {w : ℂ} (hw : 1 ≤ |w.im|) :
    (1 / 4 : ℝ) * Real.exp |w.im| ≤ ‖Complex.sin w‖ := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have h1 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have h2 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have habs_diff : |Real.exp w.im - Real.exp (-w.im)| = Real.exp |w.im| - Real.exp (-|w.im|) := by
    rcases le_or_gt 0 w.im with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))]
    · rw [abs_of_neg h, neg_neg, abs_of_neg (sub_neg.mpr (Real.exp_lt_exp.mpr (by linarith))), neg_sub]
  have hrev : Real.exp |w.im| - Real.exp (-|w.im|) ≤ ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ := by
    rw [← habs_diff, ← h1, ← h2]
    exact abs_norm_sub_norm_le _ _
  have hhalf : Real.exp (-|w.im|) ≤ (1 / 2 : ℝ) * Real.exp |w.im| := by
    have h2x : (2 : ℝ) ≤ Real.exp (2 * |w.im|) := by
      have hlin := Real.add_one_le_exp (2 * |w.im|)
      linarith
    have hprod : Real.exp (-|w.im|) * Real.exp (2 * |w.im|) = Real.exp |w.im| := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [Real.exp_pos (-|w.im|)]
  linarith

private lemma torusKnotPsi_expType_ray {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (σ : ℝ)
    (hσ0 : σ ≠ 0) (hσ : |σ| < Real.pi / 2) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (torusKnotPsi p q)) := by
  let d : ℂ := Complex.exp (I * (σ : ℂ))
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.norm_exp_ofReal_mul_I σ
  have hsin_ne : Real.sin (σ / 2) ≠ 0 := by
    have hlt : |σ / 2| < Real.pi / 4 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    have hne : σ / 2 ≠ 0 := div_ne_zero hσ0 (by norm_num)
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : Real.sin (σ / 2) < 0 := by
        have := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [(abs_lt.mp hlt).1, Real.pi_pos])
        rw [Real.sin_neg] at this; linarith
      exact this.ne
    · exact (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [(abs_lt.mp hlt).2, Real.pi_pos])).ne'
  have habs_sin : 0 < |Real.sin (σ / 2)| := abs_pos.mpr hsin_ne
  -- Threshold v₁ so that for v ≥ v₁, p * q * |s.im| ≥ 1
  let v₁ : ℝ := (1 / (2 * ((p * q : ℕ) : ℝ) * |Real.sin (σ / 2)|)) ^ 2 + 1
  have hv₁_pos : 0 < v₁ := by positivity
  -- On [0, v₁], Minor.pull d (torusKnotPsi p q) is continuous, hence bounded
  have hcont_seg : ContinuousOn (Minor.pull d (torusKnotPsi p q)) (Icc 0 v₁) := by
    refine continuousOn_const.mul (continuousOn_const.mul ?_)
    have hcomp_cont : ∀ v ∈ Icc (0 : ℝ) v₁, AnalyticAt ℂ (torusKnotBorel p q) (4 * (d * (v : ℂ))) := by
      intro v hv
      refine torusKnotBorel_analyticAt_of_removable hp hq (4 * (d * (v : ℂ))) fun n hn _ _ heq => ?_
      have him := congrArg Complex.im heq
      have hd_im : d.im = Real.sin σ := by
        dsimp only [d]; rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]; exact Complex.exp_ofReal_mul_I_im σ
      have him_lhs : (4 * (d * (v : ℂ))).im = 4 * Real.sin σ * v := by
        simp [Complex.mul_im, hd_im]; ring
      have him_rhs : ((((Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ)).im = 0 :=
        Complex.ofReal_im _
      rw [him_lhs, him_rhs] at him
      have hsinσ_ne : Real.sin σ ≠ 0 := by
        rcases lt_or_gt_of_ne hσ0 with hneg | hpos
        · have := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [(abs_lt.mp hσ).1, Real.pi_pos])
          rw [Real.sin_neg] at this; exact (by linarith : Real.sin σ < 0).ne
        · exact (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [(abs_lt.mp hσ).2, Real.pi_pos])).ne'
      have hv0 : v = 0 := by
        have : (4 * Real.sin σ) * v = 0 := him
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hsinσ_ne)
      subst hv0
      simp only [Complex.ofReal_zero, mul_zero] at heq
      have hpos_rhs : (0 : ℝ) < (Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 := by
        have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        have : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by positivity
        positivity
      exact hpos_rhs.ne (by exact_mod_cast heq)
    intro v hv
    exact ((hcomp_cont v hv).continuousAt.comp (f := fun t : ℝ => 4 * (d * (t : ℂ)))
      ((continuous_const.mul (continuous_const.mul Complex.continuous_ofReal)).continuousAt)).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_seg
  refine ⟨max M₀ (8 * ((p * q : ℕ) : ℝ)), 0, le_trans (by positivity) (le_max_right _ _), le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hvv : v ≤ v₁
  · exact (hM₀ v ⟨hv, hvv⟩).trans (le_max_left _ _)
  · push Not at hvv
    have hv_pos : 0 < v := lt_trans hv₁_pos hvv
    let s : ℂ := ((2 * Real.sqrt v : ℝ) : ℂ) * Complex.exp (I * ((σ / 2 : ℝ) : ℂ))
    have hs_sq : s ^ 2 = 4 * (d * (v : ℂ)) := by
      dsimp only [s, d]
      rw [mul_pow, ← Complex.exp_nat_mul]
      have hsq_r : ((2 * Real.sqrt v : ℝ) : ℂ) ^ 2 = 4 * (v : ℂ) := by
        rw [← Complex.ofReal_pow, mul_pow, Real.sq_sqrt hv_pos.le]; push_cast; ring
      have hexp_eq : (2 : ℕ) * (I * ((σ / 2 : ℝ) : ℂ)) = I * (σ : ℂ) := by push_cast; ring
      rw [hsq_r, hexp_eq]; ring
    have hs_im : |s.im| = 2 * Real.sqrt v * |Real.sin (σ / 2)| := by
      have him : s.im = 2 * Real.sqrt v * Real.sin (σ / 2) := by
        dsimp only [s]
        rw [show I * ((σ / 2 : ℝ) : ℂ) = ((σ / 2 : ℝ) : ℂ) * I by ring,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im]
        ring
      rw [him, abs_mul, abs_of_nonneg (by positivity)]
    have hsqrt_gt : 1 / (2 * ((p * q : ℕ) : ℝ) * |Real.sin (σ / 2)|) < Real.sqrt v := by
      have hsq_lt : (1 / (2 * ((p * q : ℕ) : ℝ) * |Real.sin (σ / 2)|)) ^ 2 < v := by dsimp only [v₁] at hvv; linarith
      exact (Real.lt_sqrt (by positivity)).mpr hsq_lt
    have hpq_im_ge : 1 ≤ |(((p * q : ℕ) : ℂ) * s).im| := by
      have him_eq : |(((p * q : ℕ) : ℂ) * s).im| = ((p * q : ℕ) : ℝ) * |s.im| := by
        simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
          abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (p * q))]
      rw [him_eq, hs_im]
      have hpos_den : 0 < 2 * ((p * q : ℕ) : ℝ) * |Real.sin (σ / 2)| := by positivity
      have := (div_lt_iff₀ hpos_den).mp hsqrt_gt
      linarith
    have hsin_pq_ge : (1 / 4 : ℝ) * Real.exp (((p * q : ℕ) : ℝ) * |s.im|) ≤
        ‖Complex.sin (((p * q : ℕ) : ℂ) * s)‖ := by
      have him_eq : |(((p * q : ℕ) : ℂ) * s).im| = ((p * q : ℕ) : ℝ) * |s.im| := by
        simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
          abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (p * q))]
      rw [← him_eq]; exact quarter_exp_le_norm_csin hpq_im_ge
    have hsin_pq_ne : Complex.sin (((p * q : ℕ) : ℂ) * s) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hsin_pq_ge
      linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 4) (Real.exp_pos (((p * q : ℕ) : ℝ) * |s.im|))]
    have hs_im_pos : 0 < |s.im| := by rw [hs_im]; positivity
    have hs_norm_ge : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hs_ne : s ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hs_im_pos hs_norm_ge)
    have htrig := torusKnotBorel_eq_trig hp hq hs_ne hsin_pq_ne
    have hval : torusKnotBorel p q (4 * (d * (v : ℂ))) =
        Complex.sin ((p : ℂ) * s) * Complex.sin ((q : ℂ) * s) / (s * Complex.sin (((p * q : ℕ) : ℂ) * s)) := by
      rw [← hs_sq]
      apply mul_left_cancel₀ hs_ne
      rw [htrig]; field_simp [hs_ne, hsin_pq_ne]
    unfold Minor.pull torusKnotPsi
    rw [hval, norm_mul, hd_norm, one_mul, norm_mul, Complex.norm_ofNat, norm_div, norm_mul, norm_mul]
    have hsin_p : ‖Complex.sin ((p : ℂ) * s)‖ ≤ Real.exp ((p : ℝ) * |s.im|) := by
      have him : |((p : ℂ) * s).im| = (p : ℝ) * |s.im| := by
        simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
          abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p)]
      rw [← him]; exact norm_csin_le_exp _
    have hsin_q : ‖Complex.sin ((q : ℂ) * s)‖ ≤ Real.exp ((q : ℝ) * |s.im|) := by
      have him : |((q : ℂ) * s).im| = (q : ℝ) * |s.im| := by
        simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
          abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q)]
      rw [← him]; exact norm_csin_le_exp _
    have hpq_ge : (p : ℝ) + (q : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
      have hnat : p + q ≤ p * q := by nlinarith
      exact_mod_cast hnat
    have hexp_ratio : Real.exp ((p : ℝ) * |s.im|) * Real.exp ((q : ℝ) * |s.im|) ≤
        Real.exp (((p * q : ℕ) : ℝ) * |s.im|) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    have hs_lower : 1 / ((p * q : ℕ) : ℝ) ≤ ‖s‖ := by
      have him_eq : |(((p * q : ℕ) : ℂ) * s).im| = ((p * q : ℕ) : ℝ) * |s.im| := by
        simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
          abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (p * q))]
      rw [him_eq] at hpq_im_ge
      have hpq_pos : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by positivity
      calc 1 / ((p * q : ℕ) : ℝ) ≤ |s.im| := (div_le_iff₀' hpq_pos).mpr hpq_im_ge
        _ ≤ ‖s‖ := hs_norm_ge
    have hden_lower : (1 / (4 * ((p * q : ℕ) : ℝ))) * Real.exp (((p * q : ℕ) : ℝ) * |s.im|) ≤
        ‖s‖ * ‖Complex.sin (((p * q : ℕ) : ℂ) * s)‖ := by
      calc (1 / (4 * ((p * q : ℕ) : ℝ))) * Real.exp (((p * q : ℕ) : ℝ) * |s.im|)
          = (1 / ((p * q : ℕ) : ℝ)) * ((1 / 4 : ℝ) * Real.exp (((p * q : ℕ) : ℝ) * |s.im|)) := by ring
        _ ≤ ‖s‖ * ‖Complex.sin (((p * q : ℕ) : ℂ) * s)‖ :=
            mul_le_mul hs_lower hsin_pq_ge (by positivity) (norm_nonneg _)
    have hden_pos : 0 < (1 / (4 * ((p * q : ℕ) : ℝ))) * Real.exp (((p * q : ℕ) : ℝ) * |s.im|) := by positivity
    have hbd : 2 * (‖Complex.sin ((p : ℂ) * s)‖ * ‖Complex.sin ((q : ℂ) * s)‖ /
        (‖s‖ * ‖Complex.sin (((p * q : ℕ) : ℂ) * s)‖)) ≤ 8 * ((p * q : ℕ) : ℝ) := by
      have h1 : ‖Complex.sin ((p : ℂ) * s)‖ * ‖Complex.sin ((q : ℂ) * s)‖ /
          (‖s‖ * ‖Complex.sin (((p * q : ℕ) : ℂ) * s)‖) ≤
          Real.exp (((p * q : ℕ) : ℝ) * |s.im|) /
            ((1 / (4 * ((p * q : ℕ) : ℝ))) * Real.exp (((p * q : ℕ) : ℝ) * |s.im|)) :=
        div_le_div₀ (Real.exp_pos _).le
          ((mul_le_mul hsin_p hsin_q (norm_nonneg _) (Real.exp_pos _).le).trans hexp_ratio)
          hden_pos hden_lower
      have hsimp : Real.exp (((p * q : ℕ) : ℝ) * |s.im|) /
          ((1 / (4 * ((p * q : ℕ) : ℝ))) * Real.exp (((p * q : ℕ) : ℝ) * |s.im|)) = 4 * ((p * q : ℕ) : ℝ) := by
        have he : Real.exp (((p * q : ℕ) : ℝ) * |s.im|) ≠ 0 := (Real.exp_pos _).ne'
        have hpq0 : ((p * q : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [he, hpq0]
      linarith
    exact hbd.trans (le_max_right _ _)

/-- **Complete `MeromorphicBorelData` for ALL Torus Knots `T(p, q)` (`2 ≤ p`, `2 ≤ q`)**:
`torusKnotPsi p q` is meromorphic on `borelWedge (π/3) ε` with simple poles at
`ω_m = (π n_m / (2 p q))^2` (where `n_m` enumerates `{n ≥ 1 | p ∤ n ∧ q ∤ n}`) and
bounded flanking-ray `ExpType` along `e^{± i π/4}`. -/
def torusKnot_meromorphicBorelData {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    MeromorphicBorelData (torusKnotPsi p q) (torusKnotFreq p q) (torusKnotRes p q) where
  θ₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := (Real.pi / (2 * ((p * q : ℕ) : ℝ))) ^ 2 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hθ₀_lt := by linarith [Real.pi_pos]
  hε_pos := by
    have : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by positivity
    positivity
  ω_pos := torusKnotFreq_pos hp hq 0
  ω_mono := torusKnotFreq_strictMono hp hq
  res_ne_zero := fun m => by
    unfold torusKnotRes
    have hspec := torusKnotPoleIndex_spec hp hq m
    let nm := torusKnotPoleIndex p q m
    have h4w : 4 * (torusKnotFreq p q m : ℂ) = (((Real.pi * (nm : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      unfold torusKnotFreq; dsimp only [nm]; push_cast; ring
    have hnum_ne : sinSqrt ((p : ℂ) ^ 2 * (4 * (torusKnotFreq p q m : ℂ))) *
        sinSqrt ((q : ℂ) ^ 2 * (4 * (torusKnotFreq p q m : ℂ))) ≠ 0 := by
      rw [h4w]
      intro h0
      rcases (torusKnotNum_zero_at_den_zero hp hq hspec.1).mp h0 with hp_d | hq_d
      · exact hspec.2.1 hp_d
      · exact hspec.2.2 hq_d
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpqC : (((p * q : ℕ) : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by positivity))
    have harg_den : (((p * q : ℕ) : ℂ) ^ 2) * (4 * (torusKnotFreq p q m : ℂ)) =
        (((Real.pi * (nm : ℝ)) ^ 2 : ℝ) : ℂ) := by
      rw [h4w]; push_cast; field_simp [hp0, hq0]
    rw [harg_den]
    exact div_ne_zero (mul_ne_zero two_ne_zero hnum_ne)
      (mul_ne_zero (by norm_num) (mul_ne_zero hpqC (deriv_sinSqrt_at_zero_ne_zero hspec.1)))
  analyticOn := fun z hz => by
    unfold torusKnotPsi
    refine analyticAt_const.mul ((torusKnotBorel_analyticAt_of_removable hp hq (4 * z) ?_).comp
      (analyticAt_const.mul analyticAt_id))
    intro n hn hpn hqn heq
    -- Then n is in the active pole set, so n = torusKnotPoleIndex p q m for some m!
    let P_act : ℕ → Prop := fun k => 1 ≤ k ∧ ¬ p ∣ k ∧ ¬ q ∣ k
    have hmem : P_act n := ⟨hn, hpn, hqn⟩
    let m : ℕ := Nat.count P_act n
    have hnm : torusKnotPoleIndex p q m = n := Nat.nth_count hmem
    have hz_eq : z = (torusKnotFreq p q m : ℂ) := by
      apply mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0)
      rw [heq]; unfold torusKnotFreq; rw [hnm]; push_cast; ring
    exact hz.2 ⟨m, hz_eq.symm⟩
  simple_pole := fun m => by
    let ωm : ℂ := (torusKnotFreq p q m : ℂ)
    let nm : ℕ := torusKnotPoleIndex p q m
    have hspec := torusKnotPoleIndex_spec hp hq m
    let num4 : ℂ → ℂ := fun w => 2 * (sinSqrt ((p : ℂ) ^ 2 * (4 * w)) * sinSqrt ((q : ℂ) ^ 2 * (4 * w)))
    let den4 : ℂ → ℂ := fun w => sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * (4 * w))
    have h4w : 4 * ωm = (((Real.pi * (nm : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      dsimp only [ωm, nm]; unfold torusKnotFreq; push_cast; ring
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpqC : (((p * q : ℕ) : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by positivity))
    have harg_den : (((p * q : ℕ) : ℂ) ^ 2) * (4 * ωm) = (((Real.pi * (nm : ℝ)) ^ 2 : ℝ) : ℂ) := by
      rw [h4w]; push_cast; field_simp [hp0, hq0]
    have hden0 : den4 ωm = 0 := by
      dsimp only [den4]; rw [harg_den]; exact (sinSqrt_eq_zero_iff _).mpr ⟨nm, hspec.1, rfl⟩
    have hden_deriv : HasDerivAt den4
        (4 * (((p * q : ℕ) : ℂ) ^ 2 * deriv sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * (4 * ωm)))) ωm := by
      have hlin : HasDerivAt (fun w : ℂ => (((p * q : ℕ) : ℂ) ^ 2) * (4 * w))
          ((((p * q : ℕ) : ℂ) ^ 2) * 4) ωm := by
        have h4 : HasDerivAt (fun w : ℂ => (4 : ℂ) * w) 4 ωm := by simpa using (hasDerivAt_id ωm).const_mul (4 : ℂ)
        exact h4.const_mul _
      exact (((sinSqrt_differentiable _).hasDerivAt).comp ωm hlin).congr_deriv (by ring)
    have hden_deriv_ne : 4 * (((p * q : ℕ) : ℂ) ^ 2 * deriv sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * (4 * ωm))) ≠ 0 := by
      rw [harg_den]
      exact mul_ne_zero (by norm_num) (mul_ne_zero hpqC (deriv_sinSqrt_at_zero_ne_zero hspec.1))
    have hnum_cont : ContinuousAt num4 ωm :=
      (continuousAt_const.mul
        (((sinSqrt_differentiable.continuous.comp (continuous_const.mul (continuous_const.mul continuous_id))).continuousAt).mul
          ((sinSqrt_differentiable.continuous.comp (continuous_const.mul (continuous_const.mul continuous_id))).continuousAt)))
    have hslope_tend : Tendsto (fun w => den4 w / (w - ωm)) (𝓝[≠] ωm)
        (𝓝 (4 * (((p * q : ℕ) : ℂ) ^ 2 * deriv sinSqrt (((p * q : ℕ) : ℂ) ^ 2 * (4 * ωm))))) := by
      have h := hasDerivAt_iff_tendsto_slope.mp hden_deriv
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [slope_def_field, hden0, sub_zero]
    have hquot_tend : Tendsto (fun w => num4 w / (den4 w / (w - ωm))) (𝓝[≠] ωm) (𝓝 (torusKnotRes p q m)) :=
      (hnum_cont.continuousWithinAt.tendsto).div hslope_tend hden_deriv_ne
    have hden_ne_punc : ∀ᶠ w in 𝓝[≠] ωm, den4 w ≠ 0 := by
      have h1 := hslope_tend.eventually_ne hden_deriv_ne
      filter_upwards [h1, self_mem_nhdsWithin] with w hw hne h0
      rw [h0, zero_div] at hw; exact hw rfl
    refine hquot_tend.congr' ?_
    filter_upwards [hden_ne_punc, self_mem_nhdsWithin] with w hw_den hw_ne
    have hsub : w - ωm ≠ 0 := sub_ne_zero.mpr hw_ne
    dsimp only [torusKnotPsi, torusKnotBorel, num4, den4] at hw_den ⊢
    rw [ite_eq_right_iff.mpr fun h => absurd h hw_den]
    dsimp only [ωm]
    field_simp [hsub, hw_den]
  expType_plus := torusKnotPsi_expType_ray hp hq (Real.pi / 4) (by positivity) (by
    rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos])
  expType_minus := by
    have heq : Complex.exp (-I * ((Real.pi / 4 : ℝ) : ℂ)) = Complex.exp (I * ((-(Real.pi / 4) : ℝ) : ℂ)) := by
      congr 1; push_cast; ring
    rw [heq]
    exact torusKnotPsi_expType_ray hp hq (-(Real.pi / 4)) (by linarith [Real.pi_pos]) (by
      rw [abs_neg, abs_of_pos (by positivity)]; linarith [Real.pi_pos])

/-! #### 5C. Explicit Torus Knot Taylor Coefficients, Euler & Perturbative WRT Series, and Specializations -/

/-- Exact `(2k+1)`-st Taylor coefficient `T_k^{(p,q)}` of the torus knot generating function
`F_{p,q}(s) = sin(p s) sin(q s) / sin(p q s) = ∑_{k ≥ 0} T_k^{(p,q)} s^{2k+1} / (2k+1)!`. -/
@[expose] def torusKnotCoeff (p q k : ℕ) : ℂ :=
  (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ)) * iteratedDeriv k (torusKnotBorel p q) 0

/-- Formal Gevrey-1 Euler series `E_{p,q}(t) = ∑_{k ≥ 0} (T_k^{(p,q)} / k!) t^k ∈ ℂ[[t]]`
for the torus knot `T(p, q)`. -/
@[expose] def torusKnotEulerSeries (p q : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => torusKnotCoeff p q k / (k.factorial : ℂ)

/-- Alternating Lawrence–Zagier / Hikami perturbative WRT formal power series
`E_{p,q}(-t) = ∑_{k ≥ 0} ((-1)^k T_k^{(p,q)} / k!) t^k ∈ ℂ[[t]]` for the torus knot `T(p, q)`. -/
@[expose] def torusKnotPerturbativeSeries (p q : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => (-1 : ℂ) ^ k * torusKnotCoeff p q k / (k.factorial : ℂ)

/-- Fishburn / Trefoil `T(2, 3)` Euler formal power series `E(t) = ∑_{k ≥ 0} (T_k / k!) t^k`,
where `sin(2 s) / (2 cos(3 s)) = ∑_{k ≥ 0} T_k s^{2k+1} / (2k+1)!`. -/
@[expose] def fishburnEulerSeries : PowerSeries ℂ := torusKnotEulerSeries 2 3

private lemma analyticAt_iteratedDeriv' {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (k : ℕ) :
    AnalyticAt ℂ (iteratedDeriv k f) z := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

private lemma iteratedDeriv_comp_const_mul {f : ℂ → ℂ} (c : ℂ) (k : ℕ) :
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
      filter_upwards [hev] with w hw
      exact ih w hw
    rw [hloc.deriv_eq]
    have hder : HasDerivAt (fun w => c ^ k * iteratedDeriv k f (c * w))
        (c ^ k * (iteratedDeriv (k + 1) f (c * z) * c)) z := by
      have h1 : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f (c * z)) (c * z) := by
        rw [iteratedDeriv_succ]
        exact (analyticAt_iteratedDeriv' hf k).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun w => c * w) c z := by simpa using (hasDerivAt_id z).const_mul c
      exact (h1.comp z h2).const_mul (c ^ k)
    rw [hder.deriv, pow_succ]; ring

private lemma eulerSeriesOf_torusKnotPsi {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    eulerSeriesOf (torusKnotPsi p q) = torusKnotEulerSeries p q := by
  have han0 : AnalyticAt ℂ (torusKnotBorel p q) 0 := by
    refine torusKnotBorel_analyticAt_of_removable hp hq 0 fun n hn _ _ heq => ?_
    have hpos : (0 : ℝ) < (Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 := by
      have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by positivity
      positivity
    exact hpos.ne (by exact_mod_cast heq)
  ext k
  simp only [eulerSeriesOf, torusKnotEulerSeries, torusKnotCoeff, PowerSeries.coeff_mk]
  have hcomp : AnalyticAt ℂ (fun w => torusKnotBorel p q (4 * w)) 0 :=
    (by simpa using han0 : AnalyticAt ℂ (torusKnotBorel p q) (4 * 0)).comp (analyticAt_const.mul analyticAt_id)
  have hpsi_eq : iteratedDeriv k (torusKnotPsi p q) 0 =
      (2 : ℂ) * ((4 : ℂ) ^ k * iteratedDeriv k (torusKnotBorel p q) 0) := by
    change iteratedDeriv k (fun w : ℂ => (2 : ℂ) * torusKnotBorel p q (4 * w)) 0 = _
    rw [iteratedDeriv_const_mul (2 : ℂ) hcomp.contDiffAt,
      iteratedDeriv_comp_const_mul (4 : ℂ) k 0 (by simpa using han0), mul_zero]
  rw [hpsi_eq]
  have hpow4 : (2 : ℂ) * (4 : ℂ) ^ k = (2 : ℂ) ^ (2 * k + 1) := by
    rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ']
  have h2p : (2 : ℂ) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [show (2 : ℂ) * ((4 : ℂ) ^ k * iteratedDeriv k (torusKnotBorel p q) 0) =
      (2 : ℂ) ^ (2 * k + 1) * iteratedDeriv k (torusKnotBorel p q) 0 from by rw [← mul_assoc, hpow4] ]
  field_simp [h2p, hfac]

private lemma iteratedDeriv_odd_mul_sq (k : ℕ) :
    ∀ {g : ℂ → ℂ}, AnalyticAt ℂ g 0 →
      iteratedDeriv (2 * k + 1) (fun s => s * g (s ^ 2)) 0 =
        (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ)) * iteratedDeriv k g 0 := by
  induction k with
  | zero =>
    intro g hg
    simp only [mul_zero, zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, div_one,
      iteratedDeriv_one, iteratedDeriv_zero, one_mul]
    have hg0 : AnalyticAt ℂ g ((0 : ℂ) ^ 2) := by simpa using hg
    have hder : HasDerivAt (fun s : ℂ => s * g (s ^ 2)) (1 * g ((0 : ℂ) ^ 2) + 0 * (deriv g ((0 : ℂ) ^ 2) * (2 * 0))) 0 := by
      have hd1 : HasDerivAt g (deriv g ((0 : ℂ) ^ 2)) ((0 : ℂ) ^ 2) := hg0.differentiableAt.hasDerivAt
      have hd2 : HasDerivAt (fun s : ℂ => s ^ 2) (2 * 0) 0 := by simpa using hasDerivAt_pow 2 (0 : ℂ)
      exact (hasDerivAt_id (0 : ℂ)).mul (HasDerivAt.comp (h := fun s : ℂ => s ^ 2) (h₂ := g) 0 hd1 hd2)
    simpa using hder.deriv
  | succ k ih =>
    intro g hg
    let h : ℂ → ℂ := dslope g 0
    have hh_an : AnalyticAt ℂ h 0 := by
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hg.eventually_analyticAt
      exact ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 hr)).mpr
        (fun w hw => (hball (Metric.mem_ball.mp hw)).differentiableAt.differentiableWithinAt)).analyticAt
        (Metric.ball_mem_nhds 0 hr)
    have hdecomp_g : ∀ z : ℂ, g z = g 0 + z * h z := fun z => by
      have := sub_smul_dslope g 0 z
      simpa [h, sub_zero, smul_eq_mul] using eq_add_of_sub_eq' this.symm
    have hder_g : iteratedDeriv (k + 1) g 0 = ((k + 1 : ℕ) : ℂ) * iteratedDeriv k h 0 := by
      rw [show g = fun z => g 0 + z * h z from funext hdecomp_g]
      have hcd1 : ContDiffAt ℂ (k + 1) (fun _ : ℂ => g 0) 0 := contDiffAt_const
      have hcd2 : ContDiffAt ℂ (k + 1) (fun z : ℂ => z * h z) 0 :=
        (analyticAt_id.mul hh_an).contDiffAt
      have hconst0 : iteratedDeriv (k + 1) (fun _ : ℂ => g 0) 0 = 0 := by
        rw [iteratedDeriv_succ']; simp
      rw [iteratedDeriv_fun_add hcd1 hcd2, hconst0, zero_add,
        iteratedDeriv_fun_mul (f := fun z : ℂ => z) (g := h) analyticAt_id.contDiffAt hh_an.contDiffAt]
      have hterm : ∀ i ∈ Finset.range (k + 1 + 1),
          ((k + 1).choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z) 0 * iteratedDeriv (k + 1 - i) h 0 =
            if i = 1 then ((k + 1 : ℕ) : ℂ) * iteratedDeriv k h 0 else 0 := fun i _ => by
        have hid : (fun z : ℂ => z) = fun z : ℂ => z ^ 1 := funext fun z => (pow_one z).symm
        rw [hid, iteratedDeriv_fun_pow_zero]
        split_ifs with hi1
        · subst hi1; simp [Nat.choose_one_right]
        · simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (k + 1 + 1)) 1]
      simp [show 1 < k + 1 + 1 by omega]
    have hdecomp_s : (fun s : ℂ => s * g (s ^ 2)) =
        fun s : ℂ => (g 0 * s) + s ^ 2 * (s * h (s ^ 2)) := funext fun s => by
      rw [hdecomp_g (s ^ 2)]; ring
    have hh_sq_an : AnalyticAt ℂ (fun s : ℂ => h (s ^ 2)) 0 :=
      AnalyticAt.comp (g := h) (f := fun s : ℂ => s ^ 2) (by simpa using hh_an) (analyticAt_id.pow 2)
    have hcdA : ContDiffAt ℂ (2 * (k + 1) + 1) (fun s : ℂ => g 0 * s) 0 :=
      (analyticAt_const.mul analyticAt_id).contDiffAt
    have hcdB : ContDiffAt ℂ (2 * (k + 1) + 1) (fun s : ℂ => s ^ 2 * (s * h (s ^ 2))) 0 :=
      ((analyticAt_id.pow 2).mul (analyticAt_id.mul hh_sq_an)).contDiffAt
    have hlin0 : iteratedDeriv (2 * (k + 1) + 1) (fun s : ℂ => g 0 * s) 0 = 0 := by
      rw [iteratedDeriv_const_mul (f := fun s : ℂ => s) (g 0) analyticAt_id.contDiffAt,
        show (fun s : ℂ => s) = fun s : ℂ => s ^ 1 from funext fun s => (pow_one s).symm,
        iteratedDeriv_fun_pow_zero]
      simp
    rw [hdecomp_s, iteratedDeriv_fun_add hcdA hcdB, hlin0, zero_add,
      iteratedDeriv_fun_mul (f := fun s : ℂ => s ^ 2) (g := fun s : ℂ => s * h (s ^ 2))
        (analyticAt_id.pow 2).contDiffAt (analyticAt_id.mul hh_sq_an).contDiffAt]
    have hterm : ∀ i ∈ Finset.range (2 * (k + 1) + 1 + 1),
        ((2 * (k + 1) + 1).choose i : ℂ) * iteratedDeriv i (fun s : ℂ => s ^ 2) 0 *
          iteratedDeriv (2 * (k + 1) + 1 - i) (fun s : ℂ => s * h (s ^ 2)) 0 =
          if i = 2 then ((2 * (k + 1) + 1).choose 2 : ℂ) * (2 : ℂ) *
            iteratedDeriv (2 * k + 1) (fun s : ℂ => s * h (s ^ 2)) 0 else 0 := fun i _ => by
      rw [iteratedDeriv_fun_pow_zero]
      split_ifs with hi2
      · subst hi2
        have hsub : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
        rw [hsub]; simp
      · simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (2 * (k + 1) + 1 + 1)) 2]
    have h2mem : 2 ∈ Finset.range (2 * (k + 1) + 1 + 1) := Finset.mem_range.mpr (by omega)
    rw [ite_eq_left_iff.mpr fun h => absurd h2mem h, ih hh_an, hder_g]
    have hchoose : ((2 * (k + 1) + 1).choose 2 : ℂ) * 2 = ((2 * k + 3 : ℕ) : ℂ) * ((2 * k + 2 : ℕ) : ℂ) := by
      have hnat : (2 * (k + 1) + 1).choose 2 * 2 = (2 * k + 3) * (2 * k + 2) := by
        rw [Nat.choose_two_right]
        have h1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
        have h2 : 2 * k + 3 - 1 = 2 * k + 2 := by omega
        rw [h1, h2]
        have hdvd : 2 ∣ (2 * k + 3) * (2 * k + 2) := ⟨(2 * k + 3) * (k + 1), by ring⟩
        exact Nat.div_mul_cancel hdvd
      exact_mod_cast hnat
    have hfac1 : ((2 * (k + 1) + 1).factorial : ℂ) =
        ((2 * k + 3 : ℕ) : ℂ) * ((2 * k + 2 : ℕ) : ℂ) * ((2 * k + 1).factorial : ℂ) := by
      have hnat : (2 * (k + 1) + 1).factorial = (2 * k + 3) * (2 * k + 2) * (2 * k + 1).factorial := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, Nat.factorial_succ,
          show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ]; ring
      exact_mod_cast hnat
    have hfac2 : ((k + 1).factorial : ℂ) = ((k + 1 : ℕ) : ℂ) * (k.factorial : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; rfl
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    rw [hchoose, hfac1, hfac2]
    field_simp [hk0, hk1]

/-- Exact match between `torusKnotCoeff p q k` and the `(2k+1)`-st Taylor coefficient of
`s ↦ s * torusKnotBorel p q (s^2) = sin(p s) sin(q s) / sin(p q s)` at `s = 0`. -/
theorem torusKnotCoeff_eq_iteratedDeriv {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (k : ℕ) :
    torusKnotCoeff p q k = iteratedDeriv (2 * k + 1) (fun s => s * torusKnotBorel p q (s ^ 2)) 0 := by
  have han0 : AnalyticAt ℂ (torusKnotBorel p q) 0 := by
    refine torusKnotBorel_analyticAt_of_removable hp hq 0 fun n hn _ _ heq => ?_
    have hpos : (0 : ℝ) < (Real.pi * (n : ℝ) / ((p * q : ℕ) : ℝ)) ^ 2 := by
      have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by positivity
      positivity
    exact hpos.ne (by exact_mod_cast heq)
  exact (iteratedDeriv_odd_mul_sq k han0).symm

/-- Exact trefoil / Fishburn trigonometric kernel identity:
`s * torusKnotBorel 2 3 (s^2) = sin(2 s) / (2 cos(3 s))` near `s = 0` (for all `s` with `cos(3 s) ≠ 0`). -/
theorem trefoil_kernel_eq_fishburn_trig {s : ℂ} (hcos : Complex.cos (3 * s) ≠ 0) :
    s * torusKnotBorel 2 3 (s ^ 2) = Complex.sin (2 * s) / (2 * Complex.cos (3 * s)) := by
  by_cases hsin3 : Complex.sin (3 * s) = 0
  · -- At removable points `sin(3 s) = 0, cos(3 s) ≠ 0`, both sides agree by continuity
    have hcontL : ContinuousAt (fun w : ℂ => w * torusKnotBorel 2 3 (w ^ 2)) s := by
      have han : AnalyticAt ℂ (torusKnotBorel 2 3) (s ^ 2) := by
        refine torusKnotBorel_analyticAt_of_removable (by omega) (by omega) (s ^ 2) fun n hn h2 h3 heq => ?_
        obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin3
        have hs_eq : s = (k : ℂ) * Real.pi / 3 := by linear_combination hk / 3
        rw [hs_eq] at heq
        have hsq : ((k : ℂ) * Real.pi / 3) ^ 2 = (((Real.pi * (n : ℝ) / 6) ^ 2 : ℝ) : ℂ) := by
          simpa using heq
        have hreal : ((k : ℝ) * Real.pi / 3) ^ 2 = (Real.pi * (n : ℝ) / 6) ^ 2 := by exact_mod_cast hsq
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have h4k : 4 * (k : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
          have hpi2 : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 hpi
          have : ((k : ℝ) / 3) ^ 2 = ((n : ℝ) / 6) ^ 2 :=
            mul_left_cancel₀ hpi2 (by linarith : Real.pi ^ 2 * ((k : ℝ) / 3) ^ 2 = Real.pi ^ 2 * ((n : ℝ) / 6) ^ 2)
          linarith
        have hnat : (2 * k.natAbs) ^ 2 = n ^ 2 := by
          have hkabs : (k.natAbs : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
            have : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
            rw [this, sq_abs]
          have : ((2 * k.natAbs : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by push_cast; linarith
          exact_mod_cast this
        have h2n : 2 * k.natAbs = n := Nat.pow_left_injective (by norm_num : 2 ≠ 0) hnat
        exact h2 ⟨k.natAbs, h2n.symm⟩
      exact continuousAt_id.mul (han.continuousAt.comp (f := fun w : ℂ => w ^ 2) (continuousAt_id.pow 2))
    have hcontR : ContinuousAt (fun w : ℂ => Complex.sin (2 * w) / (2 * Complex.cos (3 * w))) s :=
      (Complex.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.div
        (continuousAt_const.mul ((Complex.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt))
        (mul_ne_zero two_ne_zero hcos)
    have hcos_ev : ∀ᶠ w in 𝓝[≠] s, Complex.cos (3 * w) ≠ 0 :=
      nhdsWithin_le_nhds ((Complex.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt.eventually_ne hcos)
    have hsin_ev : ∀ᶠ w in 𝓝[≠] s, Complex.sin (3 * w) ≠ 0 := by
      have hderiv : HasDerivAt (fun w : ℂ => Complex.sin (3 * w)) (3 * Complex.cos (3 * s)) s := by
        have hlin : HasDerivAt (fun w : ℂ => (3 : ℂ) * w) 3 s := by simpa using (hasDerivAt_id s).const_mul (3 : ℂ)
        exact ((Complex.hasDerivAt_sin (3 * s)).comp s hlin).congr_deriv (by ring)
      have hne_d : (3 : ℂ) * Complex.cos (3 * s) ≠ 0 := mul_ne_zero (by norm_num) hcos
      have hslope := (hasDerivAt_iff_tendsto_slope.mp hderiv).eventually_ne hne_d
      filter_upwards [hslope, self_mem_nhdsWithin] with w hw hne h0
      rw [slope_def_field, h0, hsin3, sub_self, zero_div] at hw; exact hw rfl
    have hne0_ev : ∀ᶠ w in 𝓝[≠] s, w ≠ 0 := by
      by_cases hs0 : s = 0
      · subst hs0; exact self_mem_nhdsWithin
      · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hs0)
    have heq_punc : ∀ᶠ w in 𝓝[≠] s,
        w * torusKnotBorel 2 3 (w ^ 2) = Complex.sin (2 * w) / (2 * Complex.cos (3 * w)) := by
      filter_upwards [hcos_ev, hsin_ev, hne0_ev] with w hcw hsw hw0
      have hsin6 : Complex.sin (6 * w) = 2 * Complex.sin (3 * w) * Complex.cos (3 * w) := by
        rw [show (6 : ℂ) * w = 2 * (3 * w) by ring, Complex.sin_two_mul]
      have hsin6_ne : Complex.sin (((2 * 3 : ℕ) : ℂ) * w) ≠ 0 := by
        push_cast; rw [hsin6]
        exact mul_ne_zero (mul_ne_zero two_ne_zero hsw) hcw
      rw [torusKnotBorel_eq_trig (by omega) (by omega) hw0 hsin6_ne]
      push_cast
      rw [hsin6]
      have hden1 : 2 * Complex.sin (3 * w) * Complex.cos (3 * w) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero hsw) hcw
      have hden2 : 2 * Complex.cos (3 * w) ≠ 0 := mul_ne_zero two_ne_zero hcw
      rw [div_eq_div_iff hden1 hden2]; ring
    have hL : Tendsto (fun w : ℂ => w * torusKnotBorel 2 3 (w ^ 2)) (𝓝[≠] s) (𝓝 (s * torusKnotBorel 2 3 (s ^ 2))) :=
      hcontL.continuousWithinAt.tendsto
    have hR : Tendsto (fun w : ℂ => Complex.sin (2 * w) / (2 * Complex.cos (3 * w))) (𝓝[≠] s)
        (𝓝 (Complex.sin (2 * s) / (2 * Complex.cos (3 * s)))) :=
      hcontR.continuousWithinAt.tendsto
    exact tendsto_nhds_unique hL (hR.congr' (heq_punc.mono fun _ h => h.symm))
  · have hs0 : s ≠ 0 := by intro h0; subst h0; simp at hsin3
    have hsin6 : Complex.sin (6 * s) = 2 * Complex.sin (3 * s) * Complex.cos (3 * s) := by
      rw [show (6 : ℂ) * s = 2 * (3 * s) by ring, Complex.sin_two_mul]
    have hsin6_ne : Complex.sin (((2 * 3 : ℕ) : ℂ) * s) ≠ 0 := by
      push_cast; rw [hsin6]
      exact mul_ne_zero (mul_ne_zero two_ne_zero hsin3) hcos
    rw [torusKnotBorel_eq_trig (by omega) (by omega) hs0 hsin6_ne]
    push_cast
    rw [hsin6]
    have hden1 : 2 * Complex.sin (3 * s) * Complex.cos (3 * s) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hsin3) hcos
    have hden2 : 2 * Complex.cos (3 * s) ≠ 0 := mul_ne_zero two_ne_zero hcos
    rw [div_eq_div_iff hden1 hden2]; ring

/-- Exact Fishburn generating-function coefficient identity:
`torusKnotCoeff 2 3 k = iteratedDeriv (2 * k + 1) (fun s => sin(2 s) / (2 cos(3 s))) 0`. -/
theorem fishburnEulerCoeff_eq_trig (k : ℕ) :
    torusKnotCoeff 2 3 k =
      iteratedDeriv (2 * k + 1) (fun s : ℂ => Complex.sin (2 * s) / (2 * Complex.cos (3 * s))) 0 := by
  rw [torusKnotCoeff_eq_iteratedDeriv (by omega) (by omega) k]
  have hloc : (fun s : ℂ => s * torusKnotBorel 2 3 (s ^ 2)) =ᶠ[𝓝 (0 : ℂ)]
      fun s : ℂ => Complex.sin (2 * s) / (2 * Complex.cos (3 * s)) := by
    have hcos_ne : ∀ᶠ s in 𝓝 (0 : ℂ), Complex.cos (3 * s) ≠ 0 :=
      (Complex.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt.eventually_ne (by simp)
    filter_upwards [hcos_ne] with s hs
    exact trefoil_kernel_eq_fishburn_trig hs
  exact hloc.iteratedDeriv_eq (2 * k + 1)

/-! #### 5D. Sign-Flip Ring Automorphism `X ↦ -X` & Unconditional Torus Knot Theorems -/

/-- Sign-flip ring automorphism `F(X) ↦ F(-X)` on `PowerSeries ℂ`. -/
@[expose] def scaleNegPS : PowerSeries ℂ →+* PowerSeries ℂ :=
  PowerSeries.rescale (-1 : ℂ)

private lemma scaleNegPS_coeff (F : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (scaleNegPS F) = (-1 : ℂ) ^ k * PowerSeries.coeff k F :=
  PowerSeries.coeff_rescale F (-1 : ℂ) k

private lemma scaleNegPS_C (c : ℂ) : scaleNegPS (PowerSeries.C c) = PowerSeries.C c := by
  ext k; cases k <;> simp [scaleNegPS_coeff]

private lemma scaleNegPS_X : scaleNegPS (PowerSeries.X : PowerSeries ℂ) = -PowerSeries.X := by
  ext k
  rw [scaleNegPS_coeff, map_neg, PowerSeries.coeff_X]
  split_ifs with hk
  · subst hk; simp
  · simp

private lemma scaleNegPS_deriv (F : PowerSeries ℂ) :
    PowerSeries.derivative (scaleNegPS F) = -scaleNegPS (PowerSeries.derivative F) := by
  ext k
  simp only [scaleNegPS_coeff, PowerSeries.coeff_derivative, map_neg, pow_succ]
  ring

private lemma scaleNegPS_seriesJet (F : PowerSeries ℂ) (j : ℕ) :
    seriesJet (scaleNegPS F) j = (-1 : ℂ) ^ j • scaleNegPS (seriesJet F j) := by
  induction j with
  | zero => simp [seriesJet]
  | succ j ih =>
    dsimp only [seriesJet] at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Derivation.map_smul_of_tower, scaleNegPS_deriv, smul_neg, PowerSeries.smul_eq_C_mul,
      PowerSeries.smul_eq_C_mul, pow_succ, mul_neg_one, map_neg]
    ring

private lemma scaleNegPS_injective : Function.Injective scaleNegPS := by
  intro F G h
  ext k
  have hk := congrArg (PowerSeries.coeff k) h
  rw [scaleNegPS_coeff, scaleNegPS_coeff] at hk
  exact mul_left_cancel₀ (pow_ne_zero k (by norm_num)) hk

/-- Sign-flip invariance of differential transcendence: `F(t)` is D-transcendental over `ℂ(t)`
implies `F(-t)` is D-transcendental over `ℂ(t)`. -/
theorem algebraicIndependent_scaleNegPS {F : PowerSeries ℂ}
    (hF : AlgebraicIndependent ℂ (seriesCoordinates F)) :
    AlgebraicIndependent ℂ (seriesCoordinates (scaleNegPS F)) := by
  rw [algebraicIndependent_iff] at hF ⊢
  intro Q hQ
  let signVar : ℕ → MvPolynomial ℕ ℂ := fun i => match i with
    | 0 => -MvPolynomial.X 0
    | j + 1 => MvPolynomial.C ((-1 : ℂ) ^ j) * MvPolynomial.X (j + 1)
  have hmap : ∀ P : MvPolynomial ℕ ℂ,
      MvPolynomial.aeval (seriesCoordinates (scaleNegPS F)) P =
        scaleNegPS (MvPolynomial.aeval (seriesCoordinates F) (MvPolynomial.bind₁ signVar P)) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => simp [scaleNegPS_C]
    | add A B hA hB => rw [map_add, map_add, map_add, map_add, hA, hB]
    | mul_X A i hA =>
      rw [map_mul, map_mul, map_mul, map_mul, hA, MvPolynomial.aeval_X, MvPolynomial.bind₁_X_right]
      congr 1
      cases i with
      | zero =>
        simp only [signVar, seriesCoordinates, map_neg, MvPolynomial.aeval_X, scaleNegPS_X, neg_neg]
      | succ j =>
        simp only [signVar, seriesCoordinates, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
          PowerSeries.algebraMap_apply, scaleNegPS_C, scaleNegPS_seriesJet, PowerSeries.smul_eq_C_mul]
        rfl
  rw [hmap Q] at hQ
  have hbind0 : MvPolynomial.aeval (seriesCoordinates F) (MvPolynomial.bind₁ signVar Q) = 0 :=
    scaleNegPS_injective (hQ.trans (map_zero scaleNegPS).symm)
  have hQbind : MvPolynomial.bind₁ signVar Q = 0 := hF _ hbind0
  have hinv : MvPolynomial.bind₁ signVar (MvPolynomial.bind₁ signVar Q) = Q := by
    rw [MvPolynomial.bind₁_bind₁]
    have hcomp : (fun i => MvPolynomial.bind₁ signVar (signVar i)) = MvPolynomial.X := by
      funext i
      cases i with
      | zero => simp [signVar]
      | succ j =>
        dsimp only [signVar]
        rw [map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
        dsimp only [signVar]
        rw [← mul_assoc, ← map_mul, ← mul_pow]
        norm_num
    rw [hcomp, MvPolynomial.bind₁_X_left]; rfl
  rw [← hinv, hQbind, map_zero]

/-- **Flagship Unconditional Theorem (All Torus Knots `T(p, q)` — Euler Formal Series)**:
For ALL integers `p, q ≥ 2` (in particular all coprime pairs `(p, q)` defining torus knots `T(p, q)`),
the formal Gevrey-1 Euler series `torusKnotEulerSeries p q ∈ ℂ[[t]]` is **unconditionally
differentially transcendental over `ℂ(t)`**. -/
theorem torusKnotEulerSeries_algebraicIndependent {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    AlgebraicIndependent ℂ (seriesCoordinates (torusKnotEulerSeries p q)) := by
  rw [← eulerSeriesOf_torusKnotPsi hp hq]
  exact eulerSeries_algebraicIndependent_of_meromorphicBorel (torusKnot_meromorphicBorelData hp hq)

/-- **Flagship Unconditional Theorem (All Torus Knots `T(p, q)` — Perturbative WRT Series)**:
For ALL integers `p, q ≥ 2`, the alternating Lawrence–Zagier / Hikami perturbative WRT formal
power series `torusKnotPerturbativeSeries p q ∈ ℂ[[t]]` is **unconditionally differentially
transcendental over `ℂ(t)`**. -/
theorem torusKnotPerturbativeSeries_algebraicIndependent {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    AlgebraicIndependent ℂ (seriesCoordinates (torusKnotPerturbativeSeries p q)) := by
  have heq : torusKnotPerturbativeSeries p q = scaleNegPS (torusKnotEulerSeries p q) := by
    ext k; simp [torusKnotPerturbativeSeries, torusKnotEulerSeries, scaleNegPS_coeff, mul_div_assoc]
  rw [heq]
  exact algebraicIndependent_scaleNegPS (torusKnotEulerSeries_algebraicIndependent hp hq)

/-- **Unconditional Specialization — Fishburn / Trefoil Knot `T(2, 3)` Euler Series**:
`E(t) = ∑_{k ≥ 0} (T_k / k!) t^k` (where `sin(2 s) / (2 cos(3 s)) = ∑ T_k s^{2k+1} / (2k+1)!`)
is unconditionally differentially transcendental over `ℂ(t)`. -/
theorem fishburnEulerSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates fishburnEulerSeries) :=
  torusKnotEulerSeries_algebraicIndependent (p := 2) (q := 3) (by omega) (by omega)

/-- **Unconditional Specialization — Cinquefoil Knot `T(2, 5)` Euler Series**. -/
theorem cinquefoilEulerSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (torusKnotEulerSeries 2 5)) :=
  torusKnotEulerSeries_algebraicIndependent (p := 2) (q := 5) (by omega) (by omega)

/-- **Unconditional Specialization — Torus Knot `T(3, 4)` Euler Series**
(composite coprime pair including active `gcd(m, 12) = 2` poles). -/
theorem torus34EulerSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (torusKnotEulerSeries 3 4)) :=
  torusKnotEulerSeries_algebraicIndependent (p := 3) (q := 4) (by omega) (by omega)

/-- **Unconditional Specialization — Torus Knot `T(3, 5)` Euler Series**. -/
theorem torus35EulerSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (torusKnotEulerSeries 3 5)) :=
  torusKnotEulerSeries_algebraicIndependent (p := 3) (q := 5) (by omega) (by omega)

/-! ### 6. Bostan–Di Vizio–Raschel Open Problem (AJM §2.2.6): Literal Fishburn OGF `P(x)` -/

/-! #### 6A. Literal Fishburn Formal Power Series `P(x) = ∑_{m ≥ 0} ∏_{j=1}^m (1 - (1 - x)^j)` -/

/-- The `m`-th finite product summand `∏_{j=1}^m (1 - (1 - X)^j) ∈ ℂ[[X]]` of the Fishburn OGF. -/
@[expose] def fishburnTerm (m : ℕ) : PowerSeries ℂ :=
  ∏ j ∈ Finset.range m, (1 - (1 - PowerSeries.X) ^ (j + 1))

lemma X_pow_dvd_fishburnTerm (m : ℕ) : PowerSeries.X ^ m ∣ fishburnTerm m := by
  induction m with
  | zero => simp [fishburnTerm]
  | succ m ih =>
    unfold fishburnTerm at ih ⊢
    rw [Finset.prod_range_succ, pow_succ]
    refine mul_dvd_mul ih ?_
    rw [PowerSeries.X_dvd_iff]
    simp

lemma fishburnTerm_coeff_eq_zero_of_lt {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (fishburnTerm m) = 0 := by
  obtain ⟨g, hg⟩ := X_pow_dvd_fishburnTerm m
  rw [hg, PowerSeries.coeff_X_pow_mul']
  simp [not_le.mpr h]

/-- **Literal Fishburn Ordinary Generating Function**
`P(x) = ∑_{m=0}^∞ ∏_{j=1}^m (1 - (1 - x)^j) ∈ ℂ[[x]]` (Bostan–Di Vizio–Raschel, AJM §2.2.6;
Zagier 2001). Because `X^m ∣ fishburnTerm m`, the `n`-th coefficient is given exactly by the finite
sum over `m ≤ n` (agreeing with the infinite sum at every order `n`). -/
@[expose] def fishburnSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (fishburnTerm m)

/-- At every order `n`, the `n`-th coefficient of `fishburnSeries` agrees with every truncation
`∑_{m < M} [X^n] ∏_{j=1}^m (1 - (1 - X)^j)` with `M > n`. -/
theorem fishburnSeries_coeff_eq_sum {n M : ℕ} (hM : n < M) :
    PowerSeries.coeff n fishburnSeries =
      ∑ m ∈ Finset.range M, PowerSeries.coeff n (fishburnTerm m) := by
  simp only [fishburnSeries, PowerSeries.coeff_mk]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hM)) ?_
  intro m hm hnot
  have hlt : n < m := by
    rw [Finset.mem_range] at hm hnot
    omega
  exact fishburnTerm_coeff_eq_zero_of_lt hlt

lemma fishburnSeries_coeff_zero : PowerSeries.coeff 0 fishburnSeries = 1 := by
  simp [fishburnSeries, fishburnTerm]

lemma fishburnSeries_coeff_one : PowerSeries.coeff 1 fishburnSeries = 1 := by
  simp [fishburnSeries, fishburnTerm, Finset.sum_range_succ]

lemma fishburnSeries_coeff_two : PowerSeries.coeff 2 fishburnSeries = 2 := by
  have h0 : PowerSeries.coeff 2 (fishburnTerm 0) = 0 := by simp [fishburnTerm]
  have h1 : PowerSeries.coeff 2 (fishburnTerm 1) = 0 := by
    simp [fishburnTerm, PowerSeries.coeff_X]
  have h2 : PowerSeries.coeff 2 (fishburnTerm 2) = 2 := by
    have hprod : fishburnTerm 2 = PowerSeries.C 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by
      have h12 : fishburnTerm 2 = PowerSeries.X * (1 - (1 - PowerSeries.X) ^ 2) := by
        simp [fishburnTerm, Finset.prod_range_succ]
      rw [h12, show (PowerSeries.C (2 : ℂ) : PowerSeries ℂ) = 2 from map_ofNat _ 2]
      ring
    rw [hprod, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
    norm_num
  simp only [fishburnSeries, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add, h0, h1, h2]

/-! #### 6B. Pure-Algebra Differential-Transcendence Transfer along Zagier's Substitution -/

/-- Zagier's formal change of variables `x(t) = 1 - exp(-24 t) ∈ ℂ[[t]]`. -/
@[expose] def zagierSubst : PowerSeries ℂ :=
  1 - PowerSeries.rescale (-24 : ℂ) (PowerSeries.exp ℂ)

lemma zagierSubst_constantCoeff : PowerSeries.constantCoeff zagierSubst = 0 := by
  rw [zagierSubst, map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp

lemma zagierSubst_hasSubst : PowerSeries.HasSubst zagierSubst :=
  PowerSeries.HasSubst.of_constantCoeff_zero zagierSubst_constantCoeff

lemma zagierSubst_coeff_one : PowerSeries.coeff 1 zagierSubst = 24 := by
  simp [zagierSubst, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

lemma derivative_rescale_exp (c : ℂ) :
    PowerSeries.derivative (PowerSeries.rescale c (PowerSeries.exp ℂ)) =
      c • PowerSeries.rescale c (PowerSeries.exp ℂ) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    map_smul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, smul_eq_mul]
  simp only [map_div₀, map_one, map_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, map_mul, map_add, pow_succ]
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hn, hfac]

lemma derivative_zagierSubst :
    PowerSeries.derivative zagierSubst =
      (24 : ℂ) • PowerSeries.rescale (-24 : ℂ) (PowerSeries.exp ℂ) := by
  unfold zagierSubst
  rw [map_sub, Derivation.map_one_eq_zero, zero_sub, derivative_rescale_exp, ← neg_smul]
  norm_num

private lemma X_pow_dvd_pow_of_constantCoeff_zero {g : PowerSeries ℂ}
    (hg0 : PowerSeries.constantCoeff g = 0) (d : ℕ) :
    PowerSeries.X ^ d ∣ g ^ d :=
  pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hg0) d

private lemma coeff_pow_diag_of_constantCoeff_zero {g : PowerSeries ℂ}
    (hg0 : PowerSeries.constantCoeff g = 0) (d : ℕ) :
    PowerSeries.coeff d (g ^ d) = (PowerSeries.coeff 1 g) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_eq_single d]
    · rw [ih, show d + 1 - d = 1 by omega]
    · intro k hk hkd
      have hk_le : k ≤ d + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rcases lt_or_gt_of_ne hkd with hlt | hgt
      · obtain ⟨q, hq⟩ := X_pow_dvd_pow_of_constantCoeff_zero hg0 d
        rw [hq, PowerSeries.coeff_X_pow_mul']
        simp [not_le.mpr hlt]
      · have hk_eq : k = d + 1 := by omega
        subst hk_eq
        simp [PowerSeries.coeff_zero_eq_constantCoeff, hg0]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-- Substitution `f ↦ f.subst g` is injective on `ℂ[[X]]` whenever `g(0) = 0` and `g'(0) ≠ 0`. -/
lemma subst_injective_of_coeff_one_ne_zero {g : PowerSeries ℂ}
    (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g ≠ 0) :
    Function.Injective (PowerSeries.subst (R := ℂ) g) := by
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg0
  intro f₁ f₂ hEq
  suffices h0 : ∀ f : PowerSeries ℂ, f.subst g = 0 → f = 0 by
    apply sub_eq_zero.mp
    apply h0
    rw [PowerSeries.subst_sub hgs, hEq, sub_self]
  intro f hf
  by_contra hne
  have hex : ∃ n : ℕ, PowerSeries.coeff n f ≠ 0 := by
    by_contra! hall
    exact hne (PowerSeries.ext fun n => by simpa using hall n)
  classical
  let n := Nat.find hex
  have hn_ne : PowerSeries.coeff n f ≠ 0 := Nat.find_spec hex
  have hcoeff_n : PowerSeries.coeff n (f.subst g) =
      PowerSeries.coeff n f * (PowerSeries.coeff 1 g) ^ n := by
    rw [PowerSeries.coeff_subst' hgs]
    rw [finsum_eq_single _ n]
    · rw [coeff_pow_diag_of_constantCoeff_zero hg0 n, smul_eq_mul]
    · intro d hdn
      rcases lt_or_gt_of_ne hdn with hlt | hgt
      · have h0 : PowerSeries.coeff d f = 0 := not_not.mp (Nat.find_min hex hlt)
        simp [h0]
      · obtain ⟨q, hq⟩ := X_pow_dvd_pow_of_constantCoeff_zero hg0 d
        rw [hq, PowerSeries.coeff_X_pow_mul']
        simp [not_le.mpr hgt]
  have hzero : PowerSeries.coeff n (f.subst g) = 0 := by rw [hf, map_zero]
  rw [hcoeff_n] at hzero
  exact mul_ne_zero hn_ne (pow_ne_zero n hg1) hzero

private abbrev PS := PowerSeries ℂ
private abbrev FracPS := FractionRing PS
private abbrev embPS : PS →ₐ[ℂ] FracPS := IsScalarTower.toAlgHom ℂ PS FracPS
private abbrev genPS {ι : Type} (v : ι → PS) : IntermediateField ℂ FracPS :=
  IntermediateField.adjoin ℂ (Set.range fun i => embPS (v i))

private lemma mem_eval_ps' {ι : Type} (v : ι → PS) (P : MvPolynomial ι ℂ) :
    embPS (MvPolynomial.aeval v P) ∈ genPS v := by
  rw [MvPolynomial.comp_aeval_apply]
  induction P using MvPolynomial.induction_on with
  | C r => simp only [MvPolynomial.aeval_C]; exact (genPS v).algebraMap_mem r
  | add P Q hP hQ => simpa only [map_add] using (genPS v).add_mem hP hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.aeval_X] using
      (genPS v).mul_mem hP (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i))

private lemma poly_deriv_mem_ps' {ι : Type} (v : ι → PS)
    (h : ∀ i, embPS (PowerSeries.derivative (v i)) ∈ genPS v) (P : MvPolynomial ι ℂ) :
    embPS (PowerSeries.derivative (MvPolynomial.aeval v P)) ∈ genPS v := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simpa only [map_add] using (genPS v).add_mem hP hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, map_add]
    exact (genPS v).add_mem ((genPS v).mul_mem (mem_eval_ps' v P) (h i))
      ((genPS v).mul_mem (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)) hP)

private lemma deriv_mem_ps' {ι : Type} (v : ι → PS)
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
  exact (genPS v).div_mem ((genPS v).sub_mem (poly_deriv_mem_ps' v h P)
    ((genPS v).mul_mem hf (poly_deriv_mem_ps' v h Q))) (mem_eval_ps' v Q)

private lemma chain_ps' {ι : Type} [Fintype ι] (v : ι → PS) (P : MvPolynomial ι ℂ) :
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

private lemma regular_relation_ps' {v : ℕ → PS} (hn : ¬ AlgebraicIndependent ℂ v) :
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

private lemma not_independent_in_gen_ps' {ι : Type} [Fintype ι] (v : ι → PS)
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

/-- **Pure-Algebra Differential-Transcendence Transfer along Zagier's Substitution**:
For ANY formal power series `P ∈ ℂ[[x]]` satisfying Zagier's formal identity
`P.subst (1 - exp(-24 t)) = exp(t) * fishburnEulerSeries`, `P` is differentially transcendental
over `ℂ(x)`. -/
theorem fishburnSeries_algebraicIndependent_of_zagier_identity
    (hZagier : fishburnSeries.subst zagierSubst = PowerSeries.exp ℂ * fishburnEulerSeries) :
    AlgebraicIndependent ℂ (seriesCoordinates fishburnSeries) := by
  by_contra hdep
  let σ : PS →ₐ[ℂ] PS := PowerSeries.substAlgHom zagierSubst_hasSubst
  have hσ_inj : Function.Injective σ := by
    rw [show (⇑σ) = PowerSeries.subst (R := ℂ) zagierSubst from PowerSeries.coe_substAlgHom zagierSubst_hasSubst]
    exact subst_injective_of_coeff_one_ne_zero zagierSubst_constantCoeff (by rw [zagierSubst_coeff_one]; norm_num)
  let y : ℕ → PS := fun i => σ (seriesCoordinates fishburnSeries i)
  have hy_dep : ¬ AlgebraicIndependent ℂ y := by
    intro hind
    exact hdep ((σ.algebraicIndependent_iff hσ_inj).mp hind)
  obtain ⟨n, Q, hQ, hS⟩ := regular_relation_ps' hy_dep
  have hσ_eq : ∀ f : PS, σ f = f.subst zagierSubst := fun f => by
    change PowerSeries.substAlgHom zagierSubst_hasSubst f = f.subst zagierSubst
    rw [PowerSeries.coe_substAlgHom]
  have hy0 : y 0 = zagierSubst := by
    change σ PowerSeries.X = zagierSubst
    rw [hσ_eq, PowerSeries.subst_X zagierSubst_hasSubst]
  have hy_succ_deriv : ∀ k : ℕ,
      PowerSeries.derivative (y (k + 1)) = y (k + 2) * PowerSeries.derivative zagierSubst := fun k => by
    change PowerSeries.derivative (σ (seriesJet fishburnSeries k)) =
      σ (seriesJet fishburnSeries (k + 1)) * PowerSeries.derivative zagierSubst
    rw [hσ_eq, hσ_eq, PowerSeries.derivative_subst zagierSubst_hasSubst]
    congr 1
    simp [seriesJet, Function.iterate_succ_apply']
  have hdz_ne : PowerSeries.derivative zagierSubst ≠ 0 := by
    intro h0
    have hc := congrArg (PowerSeries.coeff 0) h0
    rw [derivative_zagierSubst, map_smul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at hc
    simp at hc
  have hn_pos : 0 < n := by
    by_contra! hh
    obtain rfl := Nat.eq_zero_of_le_zero hh
    have hvan : ∑ i : Fin 1, MvPolynomial.aeval (fun j : Fin 1 => y j.val) (MvPolynomial.pderiv i Q) *
        PowerSeries.derivative (y i.val) = 0 := by
      rw [← chain_ps', hQ, map_zero]
    simp only [Fin.sum_univ_one, Fin.val_zero, hy0] at hvan
    exact hS ((mul_eq_zero.mp hvan).resolve_right hdz_ne)
  -- Generators of our differential subfield `K ⊆ FractionRing (PowerSeries ℂ)`:
  -- `v 0 = X`, `v 1 = exp(X)`, `v (k + 2) = y k` for `k ≤ n`.
  let v : Fin (n + 3) → PS := fun i =>
    match i.val with
    | 0 => PowerSeries.X
    | 1 => PowerSeries.exp ℂ
    | k + 2 => y k
  have hv_mem : ∀ i : Fin (n + 3), embPS (v i) ∈ genPS v := fun i =>
    IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)
  have hX_mem : embPS PowerSeries.X ∈ genPS v := hv_mem ⟨0, by omega⟩
  have hexp_mem : embPS (PowerSeries.exp ℂ) ∈ genPS v := hv_mem ⟨1, by omega⟩
  have hy_mem : ∀ k : ℕ, k ≤ n → embPS (y k) ∈ genPS v := fun k hk => by
    simpa [v] using hv_mem ⟨k + 2, by omega⟩
  have hexp_ne : (PowerSeries.exp ℂ : PS) ≠ 0 := (PowerSeries.isUnit_exp ℂ).ne_zero
  have hexp_emb_ne : embPS (PowerSeries.exp ℂ) ≠ 0 :=
    (map_ne_zero_iff embPS (IsFractionRing.injective PS FracPS)).mpr hexp_ne
  have hdz_mem : embPS (PowerSeries.derivative zagierSubst) ∈ genPS v := by
    have hinv_eq : PowerSeries.rescale (-24 : ℂ) (PowerSeries.exp ℂ) * (PowerSeries.exp ℂ) ^ 24 = 1 := by
      rw [PowerSeries.exp_pow_eq_rescale_exp 24, PowerSeries.exp_mul_exp_eq_exp_add]
      norm_num
    have hmul := congrArg embPS hinv_eq
    rw [map_mul, map_pow, map_one] at hmul
    have hpow_ne : embPS (PowerSeries.exp ℂ) ^ 24 ≠ 0 := pow_ne_zero 24 hexp_emb_ne
    have hneg24 : embPS (PowerSeries.rescale (-24 : ℂ) (PowerSeries.exp ℂ)) =
        (embPS (PowerSeries.exp ℂ) ^ 24)⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    rw [derivative_zagierSubst, map_smul, hneg24, Algebra.smul_def]
    exact (genPS v).mul_mem ((genPS v).algebraMap_mem 24)
      ((genPS v).inv_mem ((genPS v).pow_mem hexp_mem 24))
  -- Closure of `genPS v` under `PowerSeries.derivative` on all generators `v i`:
  have hlow_y : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      embPS (PowerSeries.derivative (y i.val)) ∈ genPS v := by
    intro i hi
    rcases i with ⟨k, hk⟩
    cases k with
    | zero =>
      rw [hy0]; exact hdz_mem
    | succ m =>
      have hm_le : m + 2 ≤ n := by
        have hne : m + 1 ≠ n := fun h => hi (Fin.ext h)
        omega
      rw [hy_succ_deriv m, map_mul]
      exact (genPS v).mul_mem (hy_mem (m + 2) hm_le) hdz_mem
  have hlast_y : embPS (PowerSeries.derivative (y n)) ∈ genPS v := by
    let yFin : Fin (n + 1) → PS := fun i => y i.val
    let w : Fin (n + 1) → PS := fun i => MvPolynomial.aeval yFin (MvPolynomial.pderiv i Q)
    have hvan : ∑ i : Fin (n + 1), w i * PowerSeries.derivative (yFin i) = 0 := by
      rw [← chain_ps', hQ, map_zero]
    let s := Fin.last n
    let a : PS := ∑ j ∈ Finset.univ.erase s, w j * PowerSeries.derivative (yFin j)
    have hgen_sub : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
        embPS (MvPolynomial.aeval yFin P) ∈ genPS v := fun P => by
      induction P using MvPolynomial.induction_on with
      | C r => simp only [MvPolynomial.aeval_C]; exact (genPS v).algebraMap_mem r
      | add A B hA hB => simpa only [map_add] using (genPS v).add_mem hA hB
      | mul_X A i hA =>
        simpa only [map_mul, MvPolynomial.aeval_X] using
          (genPS v).mul_mem hA (hy_mem i.val (Nat.lt_succ_iff.mp i.isLt))
    have ha_mem : embPS a ∈ genPS v := by
      dsimp only [a]
      rw [map_sum]
      exact (genPS v).sum_mem fun j hj => by
        rw [map_mul]
        exact (genPS v).mul_mem (hgen_sub _) (hlow_y j (Finset.mem_erase.mp hj).1)
    have hws_ne : embPS (w s) ≠ 0 :=
      (map_ne_zero_iff embPS (IsFractionRing.injective PS FracPS)).mpr hS
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at hvan
    change w s * PowerSeries.derivative (y n) + a = 0 at hvan
    have hm := congrArg embPS hvan
    simp only [map_zero, map_add, map_mul] at hm
    have heq : embPS (PowerSeries.derivative (y n)) = -embPS a / embPS (w s) := by
      apply (eq_div_iff hws_ne).mpr
      linear_combination hm
    rw [heq]
    exact (genPS v).div_mem ((genPS v).neg_mem ha_mem) (hgen_sub _)
  have hv_deriv : ∀ i : Fin (n + 3), embPS (PowerSeries.derivative (v i)) ∈ genPS v := by
    intro i
    rcases i with ⟨m, hm⟩
    rcases m with _ | _ | k
    · change embPS (PowerSeries.derivative PowerSeries.X) ∈ genPS v; simp
    · change embPS (PowerSeries.derivative (PowerSeries.exp ℂ)) ∈ genPS v
      rw [PowerSeries.derivative_exp]; exact hexp_mem
    · change embPS (PowerSeries.derivative (y k)) ∈ genPS v
      have hk_le : k ≤ n := by omega
      by_cases hkn : k = n
      · subst hkn; exact hlast_y
      · exact hlow_y ⟨k, by omega⟩ (fun h => hkn (congrArg Fin.val h))
  -- Now `fishburnEulerSeries = y 1 / exp(X)` lies in `genPS v`, so all its derivatives do too!
  have hE_mem : embPS fishburnEulerSeries ∈ genPS v := by
    have hy1 : y 1 = PowerSeries.exp ℂ * fishburnEulerSeries := by
      change σ fishburnSeries = PowerSeries.exp ℂ * fishburnEulerSeries
      rw [hσ_eq, hZagier]
    have hm := congrArg embPS hy1
    rw [map_mul] at hm
    have hEq : embPS fishburnEulerSeries = embPS (y 1) / embPS (PowerSeries.exp ℂ) := by
      apply (eq_div_iff hexp_emb_ne).mpr
      rw [mul_comm]; exact hm.symm
    rw [hEq]
    exact (genPS v).div_mem (hy_mem 1 hn_pos) hexp_mem
  apply not_independent_in_gen_ps' v (seriesCoordinates fishburnEulerSeries) _
    fishburnEulerSeries_algebraicIndependent
  intro i
  cases i with
  | zero => exact hX_mem
  | succ j =>
    change embPS (seriesJet fishburnEulerSeries j) ∈ genPS v
    induction j with
    | zero => exact hE_mem
    | succ j ih =>
      simpa only [seriesJet, Function.iterate_succ_apply'] using deriv_mem_ps' v hv_deriv ih

/-! #### 6C. Unconditional Proof of Zagier's Formal Identity (`P(1 - exp(-24 t)) = exp(t) * E(t)`) -/

private lemma hasAsympExp_sub {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hg : HasAsympExp g T) :
    HasAsympExp (fun u => f u - g u) (S - T) := by
  have hneg : HasAsympExp (fun u => (-1 : ℂ) * g u) (PowerSeries.C (-1 : ℂ) * T) :=
    (HasAsympExp.const (-1 : ℂ)).mul hg
  have hadd := hf.add hneg
  have hfn : (fun u => f u + (-1 : ℂ) * g u) = fun u => f u - g u := funext fun u => by ring
  have hps : S + PowerSeries.C (-1 : ℂ) * T = S - T := by
    rw [map_neg, map_one, neg_one_mul, sub_eq_add_neg]
  rwa [hfn, hps] at hadd

private lemma hasAsympExp_const_mul (c : ℂ) {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp f S) :
    HasAsympExp (fun u => c * f u) (PowerSeries.C c * S) :=
  (HasAsympExp.const c).mul hf

private lemma hasAsympExp_congr {f g : ℝ → ℂ} {S : PowerSeries ℂ}
    (hfg : f =ᶠ[atTop] g) (hf : HasAsympExp f S) :
    HasAsympExp g S := by
  intro M
  obtain ⟨C, hC⟩ := hf M
  refine ⟨C, ?_⟩
  filter_upwards [hfg, hC] with u hu hbd
  rwa [← hu]

private lemma hasAsympExp_unique {f : ℝ → ℂ} {S₁ S₂ : PowerSeries ℂ}
    (h₁ : HasAsympExp f S₁) (h₂ : HasAsympExp f S₂) : S₁ = S₂ := by
  have hsub : HasAsympExp (fun _ : ℝ => (0 : ℂ)) (S₁ - S₂) := by
    simpa only [sub_self] using hasAsympExp_sub h₁ h₂
  have h0 : S₁ - S₂ = 0 := hsub.eq_zero_of_flat fun M =>
    ⟨0, Filter.Eventually.of_forall fun u => by simp⟩
  exact sub_eq_zero.mp h0

private lemma hasAsympExp_exp_div (c : ℂ) :
    HasAsympExp (fun u : ℝ => Complex.exp (c / (u : ℂ)))
      (PowerSeries.rescale c (PowerSeries.exp ℂ)) := by
  intro M
  rcases eq_zero_or_pos M with rfl | hM
  · refine ⟨Real.exp ‖c‖, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
    calc ‖Complex.exp (c / (u : ℂ))‖
        = Real.exp (c / (u : ℂ)).re := Complex.norm_exp _
      _ ≤ Real.exp ‖c / (u : ℂ)‖ := Real.exp_le_exp.mpr (Complex.re_le_norm _)
      _ ≤ Real.exp ‖c‖ := by
          apply Real.exp_le_exp.mpr
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          exact div_le_self (norm_nonneg c) hu
  · refine ⟨‖c‖ ^ M * ((M.succ : ℝ) * (M.factorial * M : ℝ)⁻¹), ?_⟩
    filter_upwards [eventually_ge_atTop (max ‖c‖ 1)] with u hu
    have hu1 : 1 ≤ u := le_trans (le_max_right _ _) hu
    have huc : ‖c‖ ≤ u := le_trans (le_max_left _ _) hu
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hnorm : ‖c / (u : ℂ)‖ = ‖c‖ / u := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
    have hle1 : ‖c / (u : ℂ)‖ ≤ 1 := by
      rw [hnorm]; exact (div_le_one hu_pos).mpr huc
    have hbd := Complex.exp_bound hle1 hM
    have hsum : ∑ m ∈ Finset.range M, PowerSeries.coeff m (PowerSeries.rescale c (PowerSeries.exp ℂ)) *
          ((u : ℂ)⁻¹ ^ m) =
        ∑ m ∈ Finset.range M, (c / (u : ℂ)) ^ m / (m.factorial : ℂ) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, one_div, map_inv₀, map_natCast,
        div_eq_mul_inv, div_eq_mul_inv, mul_pow]
      ring
    rw [hsum]
    refine hbd.trans_eq ?_
    rw [hnorm, div_pow]
    ring

/-! ##### 6C.2. Elementary Real-Variable Proof of Zagier's `q`-Difference Asymptotic Identity -/

private def qPoch (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 - a * q ^ j)

private def qPochLim (z q : ℝ) : ℝ :=
  ⨅ n : ℕ, qPoch (z * q) q n

private lemma qPoch_zero (a q : ℝ) : qPoch a q 0 = 1 := by simp [qPoch]

private lemma qPoch_succ (a q : ℝ) (n : ℕ) :
    qPoch a q (n + 1) = qPoch a q n * (1 - a * q ^ n) := by
  simp [qPoch, Finset.prod_range_succ]

private lemma qPoch_succ' (a q : ℝ) (n : ℕ) :
    qPoch a q (n + 1) = (1 - a) * qPoch (a * q) q n := by
  unfold qPoch
  rw [Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pow_succ']; ring

private lemma real_prod_le_prod {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hga : 0 ≤ g a := hfa.trans (hfg a (Finset.mem_insert_self a s))
    have hfs : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      hfs hga

private lemma real_prod_le_one {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := by
  simpa using real_prod_le_prod s hf0 hf1

private lemma qPoch_nonneg {a q : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) : 0 ≤ qPoch a q n := by
  refine Finset.prod_nonneg fun j _ => ?_
  have h1 : a * q ^ j ≤ 1 * 1 := mul_le_mul ha1 (pow_le_one₀ hq0 hq1) (pow_nonneg hq0 j) zero_le_one
  linarith

private lemma qPoch_le_one {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) : qPoch a q n ≤ 1 := by
  refine real_prod_le_one _ (fun j _ => ?_) (fun j _ => ?_)
  · have h1 : a * q ^ j ≤ 1 * 1 := mul_le_mul ha1 (pow_le_one₀ hq0 hq1) (pow_nonneg hq0 j) zero_le_one
    linarith
  · have : 0 ≤ a * q ^ j := mul_nonneg ha0 (pow_nonneg hq0 j)
    linarith

private lemma qPoch_antitone {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Antitone (qPoch a q) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [qPoch_succ]
  have h1 : 1 - a * q ^ n ≤ 1 := by nlinarith [pow_nonneg hq0 n]
  exact mul_le_of_le_one_right (qPoch_nonneg ha0 ha1 hq0 hq1 n) h1

private lemma qPoch_tendsto_lim {z q : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Tendsto (fun n => qPoch (z * q) q n) atTop (𝓝 (qPochLim z q)) := by
  have haz0 : 0 ≤ z * q := mul_nonneg hz0 hq0
  have haz1 : z * q ≤ 1 := by nlinarith
  exact tendsto_atTop_ciInf (qPoch_antitone haz0 haz1 hq0 hq1)
    ⟨0, by rintro _ ⟨n, rfl⟩; exact qPoch_nonneg haz0 haz1 hq0 hq1 n⟩

private lemma qPochLim_nonneg {z q : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ qPochLim z q :=
  ge_of_tendsto (qPoch_tendsto_lim hz0 hz1 hq0 hq1)
    (Filter.Eventually.of_forall fun n => qPoch_nonneg (mul_nonneg hz0 hq0) (by nlinarith) hq0 hq1 n)

private lemma qPochLim_le_qPoch {z q : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) : qPochLim z q ≤ qPoch (z * q) q n := by
  have haz0 : 0 ≤ z * q := mul_nonneg hz0 hq0
  have haz1 : z * q ≤ 1 := by nlinarith
  exact ciInf_le ⟨0, by rintro _ ⟨m, rfl⟩; exact qPoch_nonneg haz0 haz1 hq0 hq1 m⟩ n

private lemma one_sub_prod_le_sum {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (k : ℕ) :
    1 - ∏ j ∈ Finset.range k, (1 - a j) ≤ ∑ j ∈ Finset.range k, a j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hprod_nn : 0 ≤ ∏ j ∈ Finset.range k, (1 - a j) :=
      Finset.prod_nonneg fun j _ => by linarith [(ha j).2]
    have hprod_le : ∏ j ∈ Finset.range k, (1 - a j) ≤ 1 :=
      real_prod_le_one _ (fun j _ => by linarith [(ha j).2]) (fun j _ => by linarith [(ha j).1])
    have hak0 : 0 ≤ a k := (ha k).1
    nlinarith

private lemma qPoch_add (a q : ℝ) (n k : ℕ) :
    qPoch a q (n + k) = qPoch a q n * ∏ j ∈ Finset.range k, (1 - a * q ^ (n + j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, qPoch_succ, ih, Finset.prod_range_succ, mul_assoc]

private lemma qPoch_sub_lim_le {z q : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) :
    qPoch (z * q) q n - qPochLim z q ≤ qPoch (z * q) q n * (z * q ^ (n + 1) / (1 - q)) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have haz0 : 0 ≤ z * q := mul_nonneg hz0 hq0
  have haz1 : z * q ≤ 1 := by nlinarith
  have hlim : Tendsto (fun k => qPoch (z * q) q n - qPoch (z * q) q (n + k)) atTop
      (𝓝 (qPoch (z * q) q n - qPochLim z q)) :=
    tendsto_const_nhds.sub
      (((qPoch_tendsto_lim hz0 hz1 hq0 hq1.le).comp (tendsto_add_atTop_nat n)).congr fun k => by
        simp only [Function.comp_apply, add_comm k n])
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
  rw [qPoch_add]
  have hfac : qPoch (z * q) q n - qPoch (z * q) q n * ∏ j ∈ Finset.range k, (1 - z * q * q ^ (n + j)) =
      qPoch (z * q) q n * (1 - ∏ j ∈ Finset.range k, (1 - z * q * q ^ (n + j))) := by ring
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ (qPoch_nonneg haz0 haz1 hq0 hq1.le n)
  have h1 := one_sub_prod_le_sum (a := fun j => z * q * q ^ (n + j)) (fun j => by
    refine ⟨by positivity, ?_⟩
    have : q ^ (n + j) ≤ 1 := pow_le_one₀ hq0 hq1.le
    nlinarith) k
  refine h1.trans ?_
  have hsum_eq : ∑ j ∈ Finset.range k, z * q * q ^ (n + j) =
      z * q ^ (n + 1) * ∑ j ∈ Finset.range k, q ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, pow_succ]; ring
  rw [hsum_eq, geom_sum_eq hq1.ne]
  have hnum : (q ^ k - 1) / (q - 1) = (1 - q ^ k) / (1 - q) := by
    have hqne : q - 1 ≠ 0 := by linarith
    have hqne' : 1 - q ≠ 0 := by linarith
    field_simp [hqne, hqne']; ring
  rw [hnum]
  have hle : (1 - q ^ k) / (1 - q) ≤ 1 / (1 - q) :=
    div_le_div_of_nonneg_right (by linarith [pow_nonneg hq0 k]) h1q.le
  calc z * q ^ (n + 1) * ((1 - q ^ k) / (1 - q))
      ≤ z * q ^ (n + 1) * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = z * q ^ (n + 1) / (1 - q) := by ring

private lemma prod_one_sub_le_exp_neg_sum {a : ℕ → ℝ} (ha : ∀ j, a j ≤ 1) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - a j) ≤ Real.exp (- ∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, neg_add, Real.exp_add]
    have h1 : 1 - a i ≤ Real.exp (-a i) := by linarith [Real.add_one_le_exp (-a i)]
    have hnn : 0 ≤ 1 - a i := by linarith [ha i]
    have hprod_nn : 0 ≤ ∏ j ∈ s, (1 - a j) := Finset.prod_nonneg fun j _ => by linarith [ha j]
    exact mul_le_mul h1 ih hprod_nn (Real.exp_pos _).le

private lemma qPochLim_one_le_exp {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    qPochLim 1 q ≤ Real.exp (-q / (1 - q)) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hlim_sum : Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M, q ^ (j + 1)) atTop (𝓝 (q / (1 - q))) := by
    have hgeom := (summable_geometric_of_lt_one hq0 hq1).hasSum.mul_left q
    have htsum : q * ∑' j : ℕ, q ^ j = q / (1 - q) := by
      rw [tsum_geometric_of_lt_one hq0 hq1]; ring
    rw [htsum] at hgeom
    refine hgeom.tendsto_sum_nat.congr fun M => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ']
  have hlim_exp : Tendsto (fun M : ℕ => Real.exp (- ∑ j ∈ Finset.range M, q ^ (j + 1))) atTop
      (𝓝 (Real.exp (-q / (1 - q)))) := by
    rw [show -q / (1 - q) = -(q / (1 - q)) by ring]
    exact Real.continuous_exp.continuousAt.tendsto.comp hlim_sum.neg
  refine ge_of_tendsto hlim_exp (Filter.Eventually.of_forall fun M => ?_)
  have hle := qPochLim_le_qPoch zero_le_one le_rfl hq0 hq1.le M
  have hprod : qPoch (1 * q) q M = ∏ j ∈ Finset.range M, (1 - q ^ (j + 1)) := by
    unfold qPoch
    refine Finset.prod_congr rfl fun j _ => by rw [one_mul, pow_succ']
  rw [hprod] at hle
  exact hle.trans (prod_one_sub_le_exp_neg_sum (fun j => pow_le_one₀ hq0 hq1.le) (Finset.range M))

private lemma prod_sub_prod_eq_sum (a b : ℕ → ℝ) (M : ℕ) :
    (∏ j ∈ Finset.range M, a j) - (∏ j ∈ Finset.range M, b j) =
      ∑ k ∈ Finset.range M,
        (∏ j ∈ Finset.range k, a j) * (a k - b k) * (∏ j ∈ Finset.Ico (k + 1) M, b j) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    have hsplit : (∏ j ∈ Finset.range M, a j) * a M - (∏ j ∈ Finset.range M, b j) * b M =
        ((∏ j ∈ Finset.range M, a j) - (∏ j ∈ Finset.range M, b j)) * b M +
          (∏ j ∈ Finset.range M, a j) * (a M - b M) := by ring
    rw [hsplit, ih, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkM : k + 1 ≤ M := Finset.mem_range.mp hk
      rw [Finset.prod_Ico_succ_top hkM]
      ring
    · simp

private lemma qPochLim_sub_one_div_le {z q : ℝ} (hz_lo : 1 / 2 ≤ z) (hz_lt : z < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ (qPochLim z q - qPochLim 1 q) / (1 - z) ∧
      (qPochLim z q - qPochLim 1 q) / (1 - z) ≤
        (q / (1 - q)) * Real.exp (1 / 2 - q / (2 * (1 - q))) := by
  have h1z : 0 < 1 - z := sub_pos.mpr hz_lt
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hz0 : 0 ≤ z := by linarith
  have hlim_L : Tendsto (fun M : ℕ => (qPoch (z * q) q M - qPoch (1 * q) q M) / (1 - z)) atTop
      (𝓝 ((qPochLim z q - qPochLim 1 q) / (1 - z))) :=
    ((qPoch_tendsto_lim hz0 hz_lt.le hq0.le hq1.le).sub
      (qPoch_tendsto_lim zero_le_one le_rfl hq0.le hq1.le)).div_const (1 - z)
  have hlim_sum : Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M, q ^ (j + 1)) atTop (𝓝 (q / (1 - q))) := by
    have hgeom := (summable_geometric_of_lt_one hq0.le hq1).hasSum.mul_left q
    have htsum : q * ∑' j : ℕ, q ^ j = q / (1 - q) := by
      rw [tsum_geometric_of_lt_one hq0.le hq1]; ring
    rw [htsum] at hgeom
    refine hgeom.tendsto_sum_nat.congr fun M => Finset.sum_congr rfl fun j _ => by rw [pow_succ']
  have hlim_R : Tendsto (fun M : ℕ =>
        (∑ k ∈ Finset.range M, q ^ (k + 1)) *
          Real.exp (1 / 2 - (1 / 2) * ∑ j ∈ Finset.range M, q ^ (j + 1))) atTop
      (𝓝 ((q / (1 - q)) * Real.exp (1 / 2 - q / (2 * (1 - q))))) := by
    have h1 : 1 / 2 - (1 / 2) * (q / (1 - q)) = 1 / 2 - q / (2 * (1 - q)) := by
      field_simp [h1q.ne']
    rw [← h1]
    exact hlim_sum.mul (Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim_sum)))
  have hterm_eq : ∀ M : ℕ,
      (qPoch (z * q) q M - qPoch (1 * q) q M) / (1 - z) =
        ∑ k ∈ Finset.range M,
          q ^ (k + 1) * (∏ j ∈ Finset.range k, (1 - z * q ^ (j + 1))) *
            (∏ j ∈ Finset.Ico (k + 1) M, (1 - q ^ (j + 1))) := fun M => by
    have hA : qPoch (z * q) q M = ∏ j ∈ Finset.range M, (1 - z * q ^ (j + 1)) := by
      unfold qPoch; exact Finset.prod_congr rfl fun j _ => by rw [pow_succ']; ring
    have hB : qPoch (1 * q) q M = ∏ j ∈ Finset.range M, (1 - q ^ (j + 1)) := by
      unfold qPoch; exact Finset.prod_congr rfl fun j _ => by rw [one_mul, pow_succ']
    rw [hA, hB, prod_sub_prod_eq_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsub : (1 - z * q ^ (k + 1)) - (1 - q ^ (k + 1)) = (1 - z) * q ^ (k + 1) := by ring
    rw [hsub]
    field_simp [h1z.ne']
  constructor
  · refine ge_of_tendsto hlim_L (Filter.Eventually.of_forall fun M => ?_)
    rw [hterm_eq M]
    refine Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (pow_nonneg hq0.le _) ?_) ?_
    · refine Finset.prod_nonneg fun j _ => ?_
      have : z * q ^ (j + 1) ≤ 1 * 1 := mul_le_mul hz_lt.le (pow_le_one₀ hq0.le hq1.le) (pow_nonneg hq0.le _) zero_le_one
      linarith
    · refine Finset.prod_nonneg fun j _ => by linarith [pow_le_one₀ hq0.le hq1.le (n := j + 1)]
  · refine le_of_tendsto_of_tendsto hlim_L hlim_R (Filter.Eventually.of_forall fun M => ?_)
    dsimp only
    rw [hterm_eq M, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkM : k < M := Finset.mem_range.mp hk
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0.le _)
    have hp1 : ∏ j ∈ Finset.range k, (1 - z * q ^ (j + 1)) ≤
        ∏ j ∈ Finset.range k, (1 - (1 / 2) * q ^ (j + 1)) := by
      refine real_prod_le_prod _ (fun j _ => ?_) (fun j _ => ?_)
      · have : z * q ^ (j + 1) ≤ 1 * 1 := mul_le_mul hz_lt.le (pow_le_one₀ hq0.le hq1.le) (pow_nonneg hq0.le _) zero_le_one
        linarith
      · nlinarith [pow_nonneg hq0.le (j + 1)]
    have hp2 : ∏ j ∈ Finset.Ico (k + 1) M, (1 - q ^ (j + 1)) ≤
        ∏ j ∈ Finset.Ico (k + 1) M, (1 - (1 / 2) * q ^ (j + 1)) := by
      refine real_prod_le_prod _ (fun j _ => by linarith [pow_le_one₀ hq0.le hq1.le (n := j + 1)])
        (fun j _ => by nlinarith [pow_nonneg hq0.le (j + 1)])
    have hp1_exp := prod_one_sub_le_exp_neg_sum (a := fun j => (1 / 2) * q ^ (j + 1))
      (fun j => by nlinarith [pow_le_one₀ hq0.le hq1.le (n := j + 1)]) (Finset.range k)
    have hp2_exp := prod_one_sub_le_exp_neg_sum (a := fun j => (1 / 2) * q ^ (j + 1))
      (fun j => by nlinarith [pow_le_one₀ hq0.le hq1.le (n := j + 1)]) (Finset.Ico (k + 1) M)
    have hnn2 : 0 ≤ ∏ j ∈ Finset.Ico (k + 1) M, (1 - q ^ (j + 1)) :=
      Finset.prod_nonneg fun j _ => by linarith [pow_le_one₀ hq0.le hq1.le (n := j + 1)]
    have hmul : (∏ j ∈ Finset.range k, (1 - z * q ^ (j + 1))) *
          (∏ j ∈ Finset.Ico (k + 1) M, (1 - q ^ (j + 1))) ≤
        Real.exp (- ∑ j ∈ Finset.range k, (1 / 2) * q ^ (j + 1)) *
          Real.exp (- ∑ j ∈ Finset.Ico (k + 1) M, (1 / 2) * q ^ (j + 1)) :=
      mul_le_mul (hp1.trans hp1_exp) (hp2.trans hp2_exp) hnn2 (Real.exp_pos _).le
    refine hmul.trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsum_split : ∑ j ∈ Finset.range M, q ^ (j + 1) =
        (∑ j ∈ Finset.range k, q ^ (j + 1)) + q ^ (k + 1) +
          (∑ j ∈ Finset.Ico (k + 1) M, q ^ (j + 1)) := by
      have h1 := Finset.sum_range_add_sum_Ico (f := fun j => q ^ (j + 1)) (Nat.succ_le_of_lt hkM)
      rw [Finset.sum_range_succ] at h1
      exact h1.symm
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum_split]
    have hqk_le : q ^ (k + 1) ≤ 1 := pow_le_one₀ hq0.le hq1.le
    linarith

private lemma two_dvd_pent (n : ℕ) : 2 ∣ n * (3 * n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * (3 * (k + k) + 1), by ring⟩
  · exact ⟨(2 * k + 1) * (3 * k + 2), by ring⟩

private lemma two_dvd_pent_alt (n : ℕ) : 2 ∣ n * (3 * n + 5) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * (3 * (k + k) + 5), by ring⟩
  · exact ⟨(2 * k + 1) * (3 * k + 4), by ring⟩

private lemma pent_step (n : ℕ) :
    n * (3 * n + 1) / 2 + (3 * n + 2) = (n + 1) * (3 * (n + 1) + 1) / 2 := by
  have h1 := Nat.div_mul_cancel (two_dvd_pent n)
  have h2 := Nat.div_mul_cancel (two_dvd_pent (n + 1))
  nlinarith

private lemma pent_alt_eq (n : ℕ) :
    n * (3 * n + 1) / 2 + (2 * n + 1) = n * (3 * n + 5) / 2 + 1 := by
  have h1 := Nat.div_mul_cancel (two_dvd_pent n)
  have h2 := Nat.div_mul_cancel (two_dvd_pent_alt n)
  nlinarith

private lemma pent_sq_one (n : ℕ) :
    24 * (n * (3 * n + 1) / 2) + 1 = (6 * n + 1) ^ 2 := by
  have h1 := Nat.div_mul_cancel (two_dvd_pent n)
  nlinarith

private lemma pent_sq_five (n : ℕ) :
    24 * (n * (3 * n + 5) / 2 + 1) + 1 = (6 * n + 5) ^ 2 := by
  have h2 := Nat.div_mul_cancel (two_dvd_pent_alt n)
  nlinarith

private def qZagierS (q z : ℝ) : ℝ :=
  (1 - z) * ∑' n : ℕ, qPoch (z * q) q n * z ^ n

private def qZagierR (q z : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * z ^ (3 * n) * q ^ (n * (3 * n + 1) / 2) * (1 - z ^ 2 * q ^ (2 * n + 1))

private def qZagierG (q z : ℝ) : ℝ :=
  ∑' n : ℕ, (qPoch (z * q) q n - qPochLim z q) * z ^ n

private def qZagierF (q : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n *
    (((6 * n + 1 : ℕ) : ℝ) * q ^ (n * (3 * n + 1) / 2) -
      ((6 * n + 5 : ℕ) : ℝ) * q ^ (n * (3 * n + 5) / 2 + 1))

private lemma summable_qPoch_mul_pow {a q z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun n : ℕ => qPoch a q n * z ^ n) := by
  refine (summable_geometric_of_lt_one hz0 hz1).of_nonneg_of_le
    (fun n => mul_nonneg (qPoch_nonneg ha0 ha1 hq0 hq1 n) (pow_nonneg hz0 n)) (fun n => ?_)
  exact mul_le_of_le_one_left (pow_nonneg hz0 n) (qPoch_le_one ha0 ha1 hq0 hq1 n)

private lemma qZagierS_rec {q z : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    qZagierS q z = 1 - z ^ 2 * q - z ^ 3 * q ^ 2 * qZagierS q (z * q) := by
  have haz0 : 0 ≤ z * q := mul_nonneg hz0 hq0
  have haz1 : z * q < 1 := by nlinarith
  have hS1 : Summable (fun n : ℕ => qPoch (z * q) q n * z ^ n) :=
    summable_qPoch_mul_pow haz0 haz1.le hq0 hq1.le hz0 hz1
  have hS_shift : Summable (fun m : ℕ => qPoch (z * q) q (m + 1) * z ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr hS1
  have hS_mulz : Summable (fun m : ℕ => qPoch (z * q) q m * z ^ (m + 1)) := by
    have := hS1.mul_right z
    exact this.congr fun m => by rw [pow_succ]; ring
  have hstep1 : qZagierS q z =
      1 + ∑' m : ℕ, (qPoch (z * q) q (m + 1) - qPoch (z * q) q m) * z ^ (m + 1) := by
    unfold qZagierS
    rw [sub_mul, one_mul, ← tsum_mul_left]
    conv_lhs => arg 1; rw [hS1.tsum_eq_zero_add, qPoch_zero, pow_zero, mul_one]
    have hmul_eq : (fun m : ℕ => z * (qPoch (z * q) q m * z ^ m)) =
        fun m => qPoch (z * q) q m * z ^ (m + 1) := funext fun m => by rw [pow_succ]; ring
    rw [hmul_eq, add_sub_assoc, ← hS_shift.tsum_sub hS_mulz]
    congr 1; apply tsum_congr; intro m; ring
  have hdiff : ∀ m : ℕ,
      (qPoch (z * q) q (m + 1) - qPoch (z * q) q m) * z ^ (m + 1) =
        -(z ^ 2 * q) * (qPoch (z * q) q m * (z * q) ^ m) := fun m => by
    rw [qPoch_succ, mul_pow]; ring
  have hS2 : Summable (fun m : ℕ => qPoch (z * q) q m * (z * q) ^ m) :=
    summable_qPoch_mul_pow haz0 haz1.le hq0 hq1.le haz0 haz1
  rw [hstep1]
  simp_rw [hdiff]
  rw [tsum_mul_left, hS2.tsum_eq_zero_add, qPoch_zero, pow_zero, mul_one]
  have htail : (fun k : ℕ => qPoch (z * q) q (k + 1) * (z * q) ^ (k + 1)) =
      fun k => (z * q * (1 - z * q)) * (qPoch (z * q * q) q k * (z * q) ^ k) := funext fun k => by
    rw [qPoch_succ', pow_succ]; ring
  rw [htail, tsum_mul_left]
  unfold qZagierS
  ring

private lemma qZagierS_iter {q z : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (N : ℕ) :
    qZagierS q z =
      (∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * z ^ (3 * n) * q ^ (n * (3 * n + 1) / 2) * (1 - z ^ 2 * q ^ (2 * n + 1))) +
      (-1 : ℝ) ^ N * z ^ (3 * N) * q ^ (N * (3 * N + 1) / 2) * qZagierS q (z * q ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    have hzn0 : 0 ≤ z * q ^ N := mul_nonneg hz0 (pow_nonneg hq0 N)
    have hzn1 : z * q ^ N < 1 := by
      have : q ^ N ≤ 1 := pow_le_one₀ hq0 hq1.le
      nlinarith
    rw [qZagierS_rec hq0 hq1 hzn0 hzn1]
    have hqstep := pent_step N
    have h1 : (z * q ^ N) ^ 2 * q = z ^ 2 * q ^ (2 * N + 1) := by
      rw [mul_pow, ← pow_mul, mul_assoc, ← pow_succ]; congr 2; ring
    have h2 : (z * q ^ N) ^ 3 * q ^ 2 = z ^ 3 * q ^ (3 * N + 2) := by
      rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]; congr 2; ring
    have h3 : z * q ^ N * q = z * q ^ (N + 1) := by rw [mul_assoc, ← pow_succ]
    rw [h1, h2, h3]
    have hpow_z : z ^ (3 * (N + 1)) = z ^ (3 * N) * z ^ 3 := by
      rw [show 3 * (N + 1) = 3 * N + 3 by omega, pow_add]
    have hpow_q : q ^ ((N + 1) * (3 * (N + 1) + 1) / 2) = q ^ (N * (3 * N + 1) / 2) * q ^ (3 * N + 2) := by
      rw [← hqstep, pow_add]
    rw [pow_succ (-1 : ℝ) N, hpow_z, hpow_q]
    ring

private lemma qZagierS_abs_le_one {q z : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    |qZagierS q z| ≤ 1 := by
  have haz0 : 0 ≤ z * q := mul_nonneg hz0 hq0
  have haz1 : z * q ≤ 1 := by nlinarith
  have hS : Summable (fun n : ℕ => qPoch (z * q) q n * z ^ n) :=
    summable_qPoch_mul_pow haz0 haz1 hq0 hq1.le hz0 hz1
  have hge0 : 0 ≤ qZagierS q z := by
    unfold qZagierS
    exact mul_nonneg (by linarith) (tsum_nonneg fun n => mul_nonneg (qPoch_nonneg haz0 haz1 hq0 hq1.le n) (pow_nonneg hz0 n))
  have hle1 : qZagierS q z ≤ 1 := by
    unfold qZagierS
    have hle : ∑' n : ℕ, qPoch (z * q) q n * z ^ n ≤ ∑' n : ℕ, z ^ n :=
      hS.tsum_le_tsum (fun n => mul_le_of_le_one_left (pow_nonneg hz0 n) (qPoch_le_one haz0 haz1 hq0 hq1.le n))
        (summable_geometric_of_lt_one hz0 hz1)
    rw [tsum_geometric_of_lt_one hz0 hz1] at hle
    have h1z : 0 < 1 - z := sub_pos.mpr hz1
    calc (1 - z) * ∑' n : ℕ, qPoch (z * q) q n * z ^ n
        ≤ (1 - z) * (1 - z)⁻¹ := mul_le_mul_of_nonneg_left hle h1z.le
      _ = 1 := mul_inv_cancel₀ h1z.ne'
  rw [abs_of_nonneg hge0]; exact hle1

private lemma summable_pow_pent_mul {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * A ^ n * q ^ (n * (3 * n + 1) / 2)) := by
  have hpow_ge : ∀ n : ℕ, n * n ≤ n * (3 * n + 1) / 2 := fun n => by
    have h1 := Nat.div_mul_cancel (two_dvd_pent n)
    nlinarith
  have htend : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  have hpos_r : 0 < (1 / 4 : ℝ) / (A + 1) := by positivity
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hpos_r))
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (summable_nat_add_iff N₀).mp ?_
  refine (hgeom.comp_injective (add_left_injective N₀)).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  set n := k + N₀
  have hqn : q ^ n < (1 / 4 : ℝ) / (A + 1) := hN₀ n (Nat.le_add_left N₀ k)
  have hq_nn : q ^ (n * (3 * n + 1) / 2) ≤ (q ^ n) ^ n := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hq0.le hq1.le (hpow_ge n)
  have hAq : A * q ^ n ≤ 1 / 4 := by
    have h1 : A * q ^ n ≤ (A + 1) * ((1 / 4 : ℝ) / (A + 1)) :=
      mul_le_mul (by linarith) hqn.le (pow_nonneg hq0.le n) (by positivity)
    have h2 : (A + 1) * ((1 / 4 : ℝ) / (A + 1)) = 1 / 4 := by field_simp [(by positivity : A + 1 ≠ 0)]
    linarith
  have hn_le : ((n : ℝ) + 1) ≤ (2 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ m ihm =>
      push_cast
      have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      rw [pow_succ]; linarith
  calc ((n : ℝ) + 1) * A ^ n * q ^ (n * (3 * n + 1) / 2)
      ≤ (2 : ℝ) ^ n * A ^ n * (q ^ n) ^ n := by
        gcongr
    _ = (2 * (A * q ^ n)) ^ n := by rw [mul_pow, mul_pow]; ring
    _ ≤ (2 * (1 / 4 : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    _ = (1 / 2 : ℝ) ^ n := by norm_num

private lemma qZagierS_eq_R {q z : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    qZagierS q z = qZagierR q z := by
  have hR_sum : Summable (fun n : ℕ =>
      (-1 : ℝ) ^ n * z ^ (3 * n) * q ^ (n * (3 * n + 1) / 2) * (1 - z ^ 2 * q ^ (2 * n + 1))) := by
    refine Summable.of_norm_bounded (g := fun n => 2 * (((n : ℝ) + 1) * 1 ^ n * q ^ (n * (3 * n + 1) / 2)))
      ((summable_pow_pent_mul hq0 hq1 1 zero_le_one).mul_left 2) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hz0, abs_pow, abs_of_nonneg hq0.le]
    have hz3 : z ^ (3 * n) ≤ 1 := pow_le_one₀ hz0 hz1.le
    have h1m : |1 - z ^ 2 * q ^ (2 * n + 1)| ≤ 2 := by
      have : 0 ≤ z ^ 2 * q ^ (2 * n + 1) := by positivity
      have : z ^ 2 * q ^ (2 * n + 1) ≤ 1 :=
        (mul_le_mul (pow_le_one₀ hz0 hz1.le) (pow_le_one₀ hq0.le hq1.le) (pow_nonneg hq0.le _) zero_le_one).trans_eq (mul_one 1)
      rw [abs_le]; constructor <;> linarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [mul_one]
    have hq_nn : 0 ≤ q ^ (n * (3 * n + 1) / 2) := pow_nonneg hq0.le _
    calc z ^ (3 * n) * q ^ (n * (3 * n + 1) / 2) * |1 - z ^ 2 * q ^ (2 * n + 1)|
        ≤ 1 * q ^ (n * (3 * n + 1) / 2) * 2 := by gcongr
      _ ≤ 2 * (((n : ℝ) + 1) * q ^ (n * (3 * n + 1) / 2)) := by nlinarith
  have hrem : Tendsto (fun N : ℕ =>
      (-1 : ℝ) ^ N * z ^ (3 * N) * q ^ (N * (3 * N + 1) / 2) * qZagierS q (z * q ^ N)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N => q ^ N) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hz0, abs_pow, abs_of_nonneg hq0.le]
    have hz3 : z ^ (3 * N) ≤ 1 := pow_le_one₀ hz0 hz1.le
    have hS_le : |qZagierS q (z * q ^ N)| ≤ 1 :=
      qZagierS_abs_le_one hq0.le hq1 (mul_nonneg hz0 (pow_nonneg hq0.le N))
        (by have : q ^ N ≤ 1 := pow_le_one₀ hq0.le hq1.le; nlinarith)
    have hq_le : q ^ (N * (3 * N + 1) / 2) ≤ q ^ N := by
      refine pow_le_pow_of_le_one hq0.le hq1.le ?_
      have h1 := Nat.div_mul_cancel (two_dvd_pent N)
      cases N with
      | zero => simp
      | succ m => nlinarith
    calc z ^ (3 * N) * q ^ (N * (3 * N + 1) / 2) * |qZagierS q (z * q ^ N)|
        ≤ 1 * q ^ N * 1 := mul_le_mul (mul_le_mul hz3 hq_le (pow_nonneg hq0.le _) zero_le_one) hS_le
            (abs_nonneg _) (by positivity)
      _ = q ^ N := by ring
  have hlim : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * z ^ (3 * n) * q ^ (n * (3 * n + 1) / 2) * (1 - z ^ 2 * q ^ (2 * n + 1))) +
      (-1 : ℝ) ^ N * z ^ (3 * N) * q ^ (N * (3 * N + 1) / 2) * qZagierS q (z * q ^ N)) atTop
      (𝓝 (qZagierR q z + 0)) := hR_sum.hasSum.tendsto_sum_nat.add hrem
  rw [add_zero] at hlim
  exact tendsto_nhds_unique (tendsto_const_nhds (x := qZagierS q z))
    (hlim.congr fun N => (qZagierS_iter hq0.le hq1 hz0 hz1 N).symm)

private lemma qZagierS_eq_lim_add_G {q z : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    qZagierS q z = qPochLim z q + (1 - z) * qZagierG q z := by
  have haz0 : 0 ≤ z * q := mul_nonneg hz0 hq0
  have haz1 : z * q ≤ 1 := by nlinarith
  have h1 : Summable (fun n : ℕ => qPoch (z * q) q n * z ^ n) :=
    summable_qPoch_mul_pow haz0 haz1 hq0 hq1.le hz0 hz1
  have h2 : Summable (fun n : ℕ => qPochLim z q * z ^ n) :=
    (summable_geometric_of_lt_one hz0 hz1).mul_left _
  have hG : qZagierG q z = (∑' n : ℕ, qPoch (z * q) q n * z ^ n) - ∑' n : ℕ, qPochLim z q * z ^ n := by
    unfold qZagierG
    rw [← h1.tsum_sub h2]
    exact tsum_congr fun n => by ring
  rw [hG, tsum_mul_left, tsum_geometric_of_lt_one hz0 hz1]
  unfold qZagierS
  have h1z : 1 - z ≠ 0 := by linarith
  field_simp [h1z]; ring

private lemma continuousOn_qPochLim {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ContinuousOn (fun z => qPochLim z q) (Icc 0 1) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hunif : TendstoUniformlyOn (fun n z => qPoch (z * q) q n) (fun z => qPochLim z q) atTop (Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htend : Tendsto (fun n : ℕ => q ^ (n + 1) / (1 - q)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).comp (tendsto_add_atTop_nat 1)).div_const (1 - q)
    filter_upwards [htend.eventually (gt_mem_nhds hε)] with n hn z hz
    rw [Real.dist_eq, abs_sub_comm]
    have hge : 0 ≤ qPoch (z * q) q n - qPochLim z q :=
      sub_nonneg.mpr (qPochLim_le_qPoch hz.1 hz.2 hq0.le hq1.le n)
    rw [abs_of_nonneg hge]
    have hz0 : 0 ≤ z := hz.1
    have hle := qPoch_sub_lim_le hz.1 hz.2 hq0.le hq1 n
    have hp_le : qPoch (z * q) q n ≤ 1 := qPoch_le_one (mul_nonneg hz.1 hq0.le) (by nlinarith [hz.2]) hq0.le hq1.le n
    have hzq_le : z * q ^ (n + 1) / (1 - q) ≤ q ^ (n + 1) / (1 - q) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg hq0.le _) hz.2) h1q.le
    calc qPoch (z * q) q n - qPochLim z q
        ≤ qPoch (z * q) q n * (z * q ^ (n + 1) / (1 - q)) := hle
      _ ≤ 1 * (q ^ (n + 1) / (1 - q)) := mul_le_mul hp_le hzq_le (by positivity) zero_le_one
      _ < ε := by linarith
  refine hunif.continuousOn (Filter.Frequently.of_forall fun n => ?_)
  unfold qPoch
  exact (by fun_prop : Continuous fun z : ℝ => ∏ j ∈ Finset.range n, (1 - z * q * q ^ j)).continuousOn

private lemma continuousOn_qZagierG {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ContinuousOn (qZagierG q) (Icc 0 1) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hu : Summable (fun n : ℕ => q ^ (n + 1) / (1 - q)) :=
    (((summable_geometric_of_lt_one hq0.le hq1).mul_left q).div_const (1 - q)).congr
      fun n => by rw [pow_succ']
  refine continuousOn_tsum (fun n => ?_) hu (fun n z hz => ?_)
  · have h1 : ContinuousOn (fun z : ℝ => qPoch (z * q) q n) (Icc 0 1) := by
      unfold qPoch
      exact (by fun_prop : Continuous fun z : ℝ => ∏ j ∈ Finset.range n, (1 - z * q * q ^ j)).continuousOn
    exact (h1.sub (continuousOn_qPochLim hq0 hq1)).mul (continuous_pow n).continuousOn
  · have hz0 : 0 ≤ z := hz.1
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hz.1]
    have hge : 0 ≤ qPoch (z * q) q n - qPochLim z q :=
      sub_nonneg.mpr (qPochLim_le_qPoch hz.1 hz.2 hq0.le hq1.le n)
    rw [abs_of_nonneg hge]
    have hle := qPoch_sub_lim_le hz.1 hz.2 hq0.le hq1 n
    have hp_le : qPoch (z * q) q n ≤ 1 := qPoch_le_one (mul_nonneg hz.1 hq0.le) (by nlinarith [hz.2]) hq0.le hq1.le n
    have hzq_le : z * q ^ (n + 1) / (1 - q) ≤ q ^ (n + 1) / (1 - q) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg hq0.le _) hz.2) h1q.le
    have hp_nn : 0 ≤ qPoch (z * q) q n := qPoch_nonneg (mul_nonneg hz0 hq0.le) (by nlinarith [hz.2]) hq0.le hq1.le n
    calc (qPoch (z * q) q n - qPochLim z q) * z ^ n
        ≤ (qPoch (z * q) q n * (z * q ^ (n + 1) / (1 - q))) * 1 :=
          mul_le_mul hle (pow_le_one₀ hz.1 hz.2) (pow_nonneg hz.1 n) (mul_nonneg hp_nn (by positivity))
      _ ≤ 1 * (q ^ (n + 1) / (1 - q)) * 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hp_le hzq_le (by positivity) zero_le_one) zero_le_one
      _ = q ^ (n + 1) / (1 - q) := by ring

private lemma hasDerivAt_qZagierR_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (qZagierR q)
      (∑' n : ℕ, (-1 : ℝ) ^ n *
        ((3 * n : ℝ) * q ^ (n * (3 * n + 1) / 2) -
          ((3 * n + 2 : ℕ) : ℝ) * q ^ (n * (3 * n + 5) / 2 + 1))) 1 := by
  let g : ℕ → ℝ → ℝ := fun n z =>
    (-1 : ℝ) ^ n * z ^ (3 * n) * q ^ (n * (3 * n + 1) / 2) * (1 - z ^ 2 * q ^ (2 * n + 1))
  let g' : ℕ → ℝ → ℝ := fun n z =>
    (-1 : ℝ) ^ n * q ^ (n * (3 * n + 1) / 2) *
      ((3 * n : ℝ) * z ^ (3 * n - 1) - ((3 * n + 2 : ℕ) : ℝ) * z ^ (3 * n + 1) * q ^ (2 * n + 1))
  have hg_deriv : ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball (1 : ℝ) 1 → HasDerivAt (g n) (g' n y) y := by
    intro n y _
    have hsplit : g n = fun z => (-1 : ℝ) ^ n * q ^ (n * (3 * n + 1) / 2) *
        (z ^ (3 * n) - q ^ (2 * n + 1) * z ^ (3 * n + 2)) := funext fun z => by
      dsimp only [g]; rw [pow_add]; ring
    rw [hsplit]
    have hd1 : HasDerivAt (fun z : ℝ => z ^ (3 * n)) ((3 * n : ℝ) * y ^ (3 * n - 1)) y := by
      simpa [Nat.cast_mul] using hasDerivAt_pow (3 * n) y
    have hd2 : HasDerivAt (fun z : ℝ => q ^ (2 * n + 1) * z ^ (3 * n + 2))
        (q ^ (2 * n + 1) * (((3 * n + 2 : ℕ) : ℝ) * y ^ (3 * n + 1))) y := by
      have h := hasDerivAt_pow (3 * n + 2) y
      simpa using h.const_mul (q ^ (2 * n + 1))
    refine ((hd1.sub hd2).const_mul ((-1 : ℝ) ^ n * q ^ (n * (3 * n + 1) / 2))).congr_deriv ?_
    dsimp only [g']; ring
  let u : ℕ → ℝ := fun n => 12 * (((n : ℝ) + 1) * (8 : ℝ) ^ n * q ^ (n * (3 * n + 1) / 2))
  have hu : Summable u := (summable_pow_pent_mul hq0 hq1 8 (by norm_num)).mul_left 12
  have hbd : ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball (1 : ℝ) 1 → ‖g' n y‖ ≤ u n := fun n y hy => by
    have hy2 : |y| ≤ 2 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_lt.mp hy
      rw [abs_le]; constructor <;> linarith
    dsimp only [g', u]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hq0.le]
    have hpow1 : |y ^ (3 * n - 1)| ≤ (8 : ℝ) ^ n := by
      rw [abs_pow]
      calc |y| ^ (3 * n - 1) ≤ 2 ^ (3 * n - 1) := pow_le_pow_left₀ (abs_nonneg y) hy2 _
        _ ≤ 2 ^ (3 * n) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
        _ = (8 : ℝ) ^ n := by rw [pow_mul]; norm_num
    have hpow2 : |y ^ (3 * n + 1)| ≤ 2 * (8 : ℝ) ^ n := by
      rw [abs_pow]
      calc |y| ^ (3 * n + 1) ≤ 2 ^ (3 * n + 1) := pow_le_pow_left₀ (abs_nonneg y) hy2 _
        _ = 2 * 2 ^ (3 * n) := by rw [pow_succ']
        _ = 2 * (8 : ℝ) ^ n := by rw [pow_mul]; norm_num
    have hq2n : |q ^ (2 * n + 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg hq0.le]; exact pow_le_one₀ hq0.le hq1.le
    have hinner : |(3 * n : ℝ) * y ^ (3 * n - 1) - ((3 * n + 2 : ℕ) : ℝ) * y ^ (3 * n + 1) * q ^ (2 * n + 1)| ≤
        12 * ((n : ℝ) + 1) * (8 : ℝ) ^ n := by
      calc |(3 * n : ℝ) * y ^ (3 * n - 1) - ((3 * n + 2 : ℕ) : ℝ) * y ^ (3 * n + 1) * q ^ (2 * n + 1)|
          ≤ |(3 * n : ℝ) * y ^ (3 * n - 1)| + |((3 * n + 2 : ℕ) : ℝ) * y ^ (3 * n + 1) * q ^ (2 * n + 1)| :=
            abs_sub _ _
        _ = (3 * n : ℝ) * |y ^ (3 * n - 1)| + ((3 * n + 2 : ℕ) : ℝ) * |y ^ (3 * n + 1)| * |q ^ (2 * n + 1)| := by
            simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * n),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((3 * n + 2 : ℕ) : ℝ))]
        _ ≤ (3 * n : ℝ) * (8 : ℝ) ^ n + ((3 * n + 2 : ℕ) : ℝ) * (2 * (8 : ℝ) ^ n) * 1 := by
            gcongr
        _ ≤ 12 * ((n : ℝ) + 1) * (8 : ℝ) ^ n := by
            push_cast; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) n, Nat.cast_nonneg (α := ℝ) n]
    calc q ^ (n * (3 * n + 1) / 2) *
          |(3 * n : ℝ) * y ^ (3 * n - 1) - ((3 * n + 2 : ℕ) : ℝ) * y ^ (3 * n + 1) * q ^ (2 * n + 1)|
        ≤ q ^ (n * (3 * n + 1) / 2) * (12 * ((n : ℝ) + 1) * (8 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hinner (pow_nonneg hq0.le _)
      _ = 12 * (((n : ℝ) + 1) * (8 : ℝ) ^ n * q ^ (n * (3 * n + 1) / 2)) := by ring
  have hg1 : Summable (fun n => g n 1) := by
    refine Summable.of_norm_bounded (g := fun n => 2 * (((n : ℝ) + 1) * 1 ^ n * q ^ (n * (3 * n + 1) / 2)))
      ((summable_pow_pent_mul hq0 hq1 1 zero_le_one).mul_left 2) fun n => ?_
    dsimp only [g]
    rw [Real.norm_eq_abs, one_pow, one_pow, mul_one, one_mul, abs_mul, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg hq0.le]
    have h1m : |1 - q ^ (2 * n + 1)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [pow_nonneg hq0.le (2 * n + 1), pow_le_one₀ hq0.le hq1.le (n := 2 * n + 1)]
    simp only [mul_one]
    nlinarith [pow_nonneg hq0.le (n * (3 * n + 1) / 2), Nat.cast_nonneg (α := ℝ) n]
  have htsum := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (1 : ℝ) 1).isPreconnected hg_deriv hbd (Metric.mem_ball_self zero_lt_one) hg1
    (Metric.mem_ball_self zero_lt_one)
  refine htsum.congr_deriv ?_
  refine tsum_congr fun n => ?_
  dsimp only [g']
  rw [one_pow, one_pow, mul_one, mul_one, ← pent_alt_eq n, pow_add]
  ring

private lemma zagier_q_approx {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    |qZagierG q 1 + (1 / 2) * qZagierF q| ≤
      (1 / 2) * Real.exp (-q / (1 - q)) +
        (q / (1 - q)) * Real.exp (1 / 2 - q / (2 * (1 - q))) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hderivR := hasDerivAt_qZagierR_one hq0 hq1
  set R' := ∑' n : ℕ, (-1 : ℝ) ^ n *
    ((3 * n : ℝ) * q ^ (n * (3 * n + 1) / 2) -
      ((3 * n + 2 : ℕ) : ℝ) * q ^ (n * (3 * n + 5) / 2 + 1))
  -- Step 1: Euler's pentagonal number theorem `qPochLim 1 q = qZagierR q 1` by taking `z → 1⁻`
  have hid_lt : Tendsto (fun z : ℝ => z) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hsub_icc : ∀ᶠ z in 𝓝[<] (1 : ℝ), z ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hwithin_icc : Tendsto (fun z : ℝ => z) (𝓝[<] 1) (𝓝[Icc 0 1] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hid_lt hsub_icc
  have hG1 : Tendsto (qZagierG q) (𝓝[<] 1) (𝓝 (qZagierG q 1)) :=
    ((continuousOn_qZagierG hq0 hq1).continuousWithinAt ⟨zero_le_one, le_rfl⟩).tendsto.comp hwithin_icc
  have hlim_L : Tendsto (fun z => qPochLim z q + (1 - z) * qZagierG q z) (𝓝[<] 1) (𝓝 (qPochLim 1 q)) := by
    have hL1 : Tendsto (fun z => qPochLim z q) (𝓝[<] 1) (𝓝 (qPochLim 1 q)) :=
      ((continuousOn_qPochLim hq0 hq1).continuousWithinAt ⟨zero_le_one, le_rfl⟩).tendsto.comp hwithin_icc
    have h1z : Tendsto (fun z : ℝ => 1 - z) (𝓝[<] 1) (𝓝 0) := by
      simpa using (tendsto_const_nhds.sub hid_lt : Tendsto (fun z : ℝ => 1 - z) (𝓝[<] 1) (𝓝 (1 - 1)))
    simpa using hL1.add (h1z.mul hG1)
  have hlim_R : Tendsto (qZagierR q) (𝓝[<] 1) (𝓝 (qZagierR q 1)) :=
    hderivR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hEq_lt : ∀ᶠ z in 𝓝[<] (1 : ℝ), qPochLim z q + (1 - z) * qZagierG q z = qZagierR q z := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with z hz
    rw [← qZagierS_eq_lim_add_G hq0.le hq1 hz.1.le hz.2, qZagierS_eq_R hq0 hq1 hz.1.le hz.2]
  have hPent : qPochLim 1 q = qZagierR q 1 :=
    tendsto_nhds_unique hlim_L (hlim_R.congr' (hEq_lt.mono fun _ h => h.symm))
  -- Step 2: Send `z → 1⁻` in `|G(z) - (R(z) - R(1)) / (1 - z)| = (qPochLim z q - qPochLim 1 q) / (1 - z)`
  have hR_slope : Tendsto (fun z : ℝ => (qZagierR q z - qZagierR q 1) / (1 - z)) (𝓝[<] 1) (𝓝 (-R')) := by
    have hsl := (hasDerivAt_iff_tendsto_slope.mp hderivR).mono_left
      (nhdsWithin_mono (1 : ℝ) fun z hz => Set.mem_compl_singleton_iff.mpr (Set.mem_Iio.mp hz).ne)
    have hneg := hsl.neg
    refine hneg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : z < 1)
    rw [slope_def_field]
    have hne1 : z - 1 ≠ 0 := by linarith
    have hne2 : 1 - z ≠ 0 := by linarith
    field_simp [hne1, hne2]; ring
  have hquot_lim : Tendsto (fun z : ℝ => |qZagierG q z - (qZagierR q z - qZagierR q 1) / (1 - z)|)
      (𝓝[<] 1) (𝓝 |qZagierG q 1 + R'|) := by
    have h1 := (hG1.sub hR_slope).abs
    simpa [sub_neg_eq_add] using h1
  have hGR_bound : |qZagierG q 1 + R'| ≤ (q / (1 - q)) * Real.exp (1 / 2 - q / (2 * (1 - q))) := by
    refine le_of_tendsto hquot_lim ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with z hz
    have h1z : 0 < 1 - z := sub_pos.mpr hz.2
    have hEq := qZagierS_eq_lim_add_G hq0.le hq1 (by linarith [hz.1]) hz.2
    rw [qZagierS_eq_R hq0 hq1 (by linarith [hz.1]) hz.2] at hEq
    have hdiff : qZagierG q z - (qZagierR q z - qZagierR q 1) / (1 - z) =
        -((qPochLim z q - qPochLim 1 q) / (1 - z)) := by
      rw [← hPent, hEq]
      field_simp [h1z.ne']; ring
    rw [hdiff, abs_neg]
    have hbd := qPochLim_sub_one_div_le hz.1.le hz.2 hq0 hq1
    rw [abs_of_nonneg hbd.1]
    exact hbd.2
  -- Step 3: Combine `R' + (1/2) * R(1) = (1/2) * qZagierF q` with `R(1) = qPochLim 1 q ≤ exp(-q/(1-q))`
  have hsum_R1 : Summable (fun n : ℕ =>
      (-1 : ℝ) ^ n * (1 : ℝ) ^ (3 * n) * q ^ (n * (3 * n + 1) / 2) * (1 - (1 : ℝ) ^ 2 * q ^ (2 * n + 1))) := by
    refine Summable.of_norm_bounded (g := fun n => 2 * (((n : ℝ) + 1) * 1 ^ n * q ^ (n * (3 * n + 1) / 2)))
      ((summable_pow_pent_mul hq0 hq1 1 zero_le_one).mul_left 2) fun n => ?_
    rw [Real.norm_eq_abs, one_pow, one_pow, mul_one, one_mul, abs_mul, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg hq0.le]
    have h1m : |1 - q ^ (2 * n + 1)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [pow_nonneg hq0.le (2 * n + 1), pow_le_one₀ hq0.le hq1.le (n := 2 * n + 1)]
    simp only [mul_one]
    nlinarith [pow_nonneg hq0.le (n * (3 * n + 1) / 2), Nat.cast_nonneg (α := ℝ) n]
  have hsum_R' : Summable (fun n : ℕ => (-1 : ℝ) ^ n *
      ((3 * n : ℝ) * q ^ (n * (3 * n + 1) / 2) -
        ((3 * n + 2 : ℕ) : ℝ) * q ^ (n * (3 * n + 5) / 2 + 1))) := by
    refine Summable.of_norm_bounded (g := fun n => 6 * (((n : ℝ) + 1) * 1 ^ n * q ^ (n * (3 * n + 1) / 2)))
      ((summable_pow_pent_mul hq0 hq1 1 zero_le_one).mul_left 6) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, mul_one]
    have hq_alt : q ^ (n * (3 * n + 5) / 2 + 1) ≤ q ^ (n * (3 * n + 1) / 2) := by
      rw [← pent_alt_eq n, pow_add]
      exact mul_le_of_le_one_right (pow_nonneg hq0.le _) (pow_le_one₀ hq0.le hq1.le)
    calc |(3 * n : ℝ) * q ^ (n * (3 * n + 1) / 2) - ((3 * n + 2 : ℕ) : ℝ) * q ^ (n * (3 * n + 5) / 2 + 1)|
        ≤ |(3 * n : ℝ) * q ^ (n * (3 * n + 1) / 2)| + |((3 * n + 2 : ℕ) : ℝ) * q ^ (n * (3 * n + 5) / 2 + 1)| :=
          abs_sub _ _
      _ = (3 * n : ℝ) * q ^ (n * (3 * n + 1) / 2) + ((3 * n + 2 : ℕ) : ℝ) * q ^ (n * (3 * n + 5) / 2 + 1) := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ (3 * n : ℝ) * q ^ (n * (3 * n + 1) / 2) + ((3 * n + 2 : ℕ) : ℝ) * q ^ (n * (3 * n + 1) / 2) := by
          gcongr
      _ ≤ 6 * (((n : ℝ) + 1) * q ^ (n * (3 * n + 1) / 2)) := by
          push_cast; nlinarith [pow_nonneg hq0.le (n * (3 * n + 1) / 2), Nat.cast_nonneg (α := ℝ) n]
  have hF_eq : (1 / 2 : ℝ) * qZagierF q = R' + (1 / 2) * qZagierR q 1 := by
    dsimp only [qZagierF, R', qZagierR]
    rw [← tsum_mul_left, ← tsum_mul_left, ← hsum_R'.tsum_add (hsum_R1.mul_left (1 / 2))]
    refine tsum_congr fun n => ?_
    rw [one_pow, one_pow, mul_one, one_mul, ← pent_alt_eq n, pow_add]
    push_cast; ring
  have hdecomp : qZagierG q 1 + (1 / 2) * qZagierF q = (qZagierG q 1 + R') + (1 / 2) * qPochLim 1 q := by
    rw [hF_eq, hPent]; ring
  rw [hdecomp]
  calc |(qZagierG q 1 + R') + (1 / 2) * qPochLim 1 q|
      ≤ |qZagierG q 1 + R'| + |(1 / 2) * qPochLim 1 q| := abs_add_le _ _
    _ = |qZagierG q 1 + R'| + (1 / 2) * qPochLim 1 q := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) (qPochLim_nonneg zero_le_one le_rfl hq0.le hq1.le))]
    _ ≤ (q / (1 - q)) * Real.exp (1 / 2 - q / (2 * (1 - q))) + (1 / 2) * Real.exp (-q / (1 - q)) :=
        add_le_add hGR_bound (mul_le_mul_of_nonneg_left (qPochLim_one_le_exp hq0.le hq1) (by norm_num))
    _ = (1 / 2) * Real.exp (-q / (1 - q)) + (q / (1 - q)) * Real.exp (1 / 2 - q / (2 * (1 - q))) := by ring

/-! ##### 6C.3. Asymptotic Expansion of the Fishburn `q`-Sum at `q = exp(-24 / u)` -/

private lemma one_sub_exp_neg_ge_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hpos : 0 < 1 + x := by linarith
  have hexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ hpos h1
  have h2 : x / 2 ≤ x / (1 + x) := by
    rw [div_le_div_iff₀ (by norm_num) hpos]; nlinarith
  have h3 : x / (1 + x) = 1 - (1 + x)⁻¹ := by field_simp [hpos.ne']; ring
  linarith

private lemma one_sub_exp_neg_le {x : ℝ} : 1 - Real.exp (-x) ≤ x := by
  linarith [Real.add_one_le_exp (-x)]

private def fishburnQ (u : ℝ) : ℂ :=
  ((qZagierG (Real.exp (-24 / u)) 1 : ℝ) : ℂ)

private lemma hasAsympExp_qPoch_exp (n : ℕ) :
    HasAsympExp (fun u : ℝ => ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) n : ℝ) : ℂ))
      ((fishburnTerm n).subst zagierSubst) := by
  induction n with
  | zero =>
    have hL : (fun u : ℝ => ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) 0 : ℝ) : ℂ)) =
        fun _ => (1 : ℂ) := funext fun _ => by simp [qPoch]
    have hR : (fishburnTerm 0).subst zagierSubst = PowerSeries.C (1 : ℂ) := by
      simp [fishburnTerm, ← PowerSeries.coe_substAlgHom zagierSubst_hasSubst]
    rw [hL, hR]
    exact HasAsympExp.const 1
  | succ n ih =>
    have hL : (fun u : ℝ => ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) (n + 1) : ℝ) : ℂ)) =
        fun u : ℝ => ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) n : ℝ) : ℂ) *
          (1 - Complex.exp ((-((24 * (n + 1) : ℕ) : ℝ) : ℂ) / (u : ℂ))) := funext fun u => by
      rw [qPoch_succ]
      push_cast
      congr 2
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; ring
    have hR : (fishburnTerm (n + 1)).subst zagierSubst =
        (fishburnTerm n).subst zagierSubst *
          (PowerSeries.C 1 - PowerSeries.rescale (-((24 * (n + 1) : ℕ) : ℝ) : ℂ) (PowerSeries.exp ℂ)) := by
      unfold fishburnTerm
      rw [Finset.prod_range_succ, PowerSeries.subst_mul zagierSubst_hasSubst]
      congr 1
      rw [PowerSeries.subst_sub zagierSubst_hasSubst, PowerSeries.subst_pow zagierSubst_hasSubst,
        PowerSeries.subst_sub zagierSubst_hasSubst, PowerSeries.subst_X zagierSubst_hasSubst]
      have h1 : (1 : PowerSeries ℂ).subst zagierSubst = 1 := by
        rw [← PowerSeries.coe_substAlgHom zagierSubst_hasSubst, map_one]
      rw [h1, show (1 - zagierSubst : PowerSeries ℂ) = PowerSeries.rescale (-24 : ℂ) (PowerSeries.exp ℂ) by
            unfold zagierSubst; ring]
      have hpow : (PowerSeries.rescale (-24 : ℂ) (PowerSeries.exp ℂ)) ^ (n + 1) =
          PowerSeries.rescale (-((24 * (n + 1) : ℕ) : ℝ) : ℂ) (PowerSeries.exp ℂ) := by
        rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
        congr 1; push_cast; ring
      rw [hpow, map_one]
    rw [hL, hR]
    exact ih.mul (hasAsympExp_sub (HasAsympExp.const 1) (hasAsympExp_exp_div _))

private lemma fishburnQ_hasAsympExp :
    HasAsympExp fishburnQ (fishburnSeries.subst zagierSubst) := by
  intro M
  let N : ℕ := M + 2
  have hfin : ∀ K : ℕ, HasAsympExp
      (fun u : ℝ => ∑ n ∈ Finset.range K, ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) n : ℝ) : ℂ))
      (∑ n ∈ Finset.range K, (fishburnTerm n).subst zagierSubst) := by
    intro K
    induction K with
    | zero =>
      simpa using HasAsympExp.const (0 : ℂ)
    | succ K ihK =>
      have hL : (fun u : ℝ => ∑ n ∈ Finset.range (K + 1),
            ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) n : ℝ) : ℂ)) =
          fun u => (∑ n ∈ Finset.range K,
            ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) n : ℝ) : ℂ)) +
            ((qPoch (Real.exp (-24 / u)) (Real.exp (-24 / u)) K : ℝ) : ℂ) :=
        funext fun u => Finset.sum_range_succ _ K
      rw [hL, Finset.sum_range_succ]
      exact ihK.add (hasAsympExp_qPoch_exp K)
  -- First `M` coefficients of `∑_{n < N} (fishburnTerm n).subst zagierSubst` equal those of `fishburnSeries.subst zagierSubst`:
  have hcoeff_eq : ∀ k ∈ Finset.range M,
      PowerSeries.coeff k (∑ n ∈ Finset.range N, (fishburnTerm n).subst zagierSubst) =
        PowerSeries.coeff k (fishburnSeries.subst zagierSubst) := fun k hk => by
    have hkM : k < M := Finset.mem_range.mp hk
    have hsum_subst : ∑ n ∈ Finset.range N, (fishburnTerm n).subst zagierSubst =
        (∑ n ∈ Finset.range N, fishburnTerm n).subst zagierSubst := by
      simp only [← PowerSeries.coe_substAlgHom zagierSubst_hasSubst, map_sum]
    rw [hsum_subst, PowerSeries.coeff_subst' zagierSubst_hasSubst,
      PowerSeries.coeff_subst' zagierSubst_hasSubst]
    refine finsum_congr fun d => ?_
    by_cases hdk : d ≤ k
    · have hdN : d < N := by omega
      rw [map_sum, fishburnSeries_coeff_eq_sum hdN]
    · obtain ⟨q, hq⟩ := X_pow_dvd_pow_of_constantCoeff_zero zagierSubst_constantCoeff d
      rw [hq, PowerSeries.coeff_X_pow_mul']
      simp [show ¬ d ≤ k by omega]
  obtain ⟨C₀, hC₀⟩ := hfin N M
  -- Exponential decay of `N * qPochLim 1 q`:
  have hlim_exp : HasAsympExp (fun u : ℝ => ((N : ℝ) * qPochLim 1 (Real.exp (-24 / u)) : ℂ)) 0 := by
    refine HasAsympExp.zero_of_exp_decay (δ := Real.exp (-1) / 24) (by positivity) (A := 0) (C := (N : ℝ)) ?_
    filter_upwards [eventually_ge_atTop (24 : ℝ)] with u hu
    have hu_pos : 0 < u := by linarith
    set q := Real.exp (-24 / u)
    have hq0 : 0 < q := Real.exp_pos _
    have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hu_pos)
    have h1q_le : 1 - q ≤ 24 / u := by
      have := one_sub_exp_neg_le (x := 24 / u)
      simpa [q, neg_div] using this
    have hq_ge : Real.exp (-1) ≤ q := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_le_neg_iff]
      exact (div_le_one hu_pos).mpr hu
    have hquot : (Real.exp (-1) / 24) * u ≤ q / (1 - q) := by
      have h1q_pos : 0 < 1 - q := sub_pos.mpr hq1
      rw [le_div_iff₀ h1q_pos]
      have hmul : (1 - q) * u ≤ 24 := by
        have := mul_le_mul_of_nonneg_right h1q_le hu_pos.le
        rwa [div_mul_cancel₀ _ hu_pos.ne'] at this
      calc (Real.exp (-1) / 24) * u * (1 - q)
          = Real.exp (-1) * ((1 - q) * u / 24) := by ring
        _ ≤ Real.exp (-1) * (24 / 24) := mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hmul (by norm_num)) (Real.exp_pos _).le
        _ = Real.exp (-1) := by norm_num
        _ ≤ q := hq_ge
    have hnn : 0 ≤ (N : ℝ) * qPochLim 1 q :=
      mul_nonneg (Nat.cast_nonneg N) (qPochLim_nonneg zero_le_one le_rfl hq0.le hq1.le)
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, pow_zero, mul_one]
    calc (N : ℝ) * qPochLim 1 q
        ≤ (N : ℝ) * Real.exp (-q / (1 - q)) :=
          mul_le_mul_of_nonneg_left (qPochLim_one_le_exp hq0.le hq1) (Nat.cast_nonneg N)
      _ ≤ (N : ℝ) * Real.exp (-(Real.exp (-1) / 24) * u) := by
          gcongr
          rw [neg_div]; linarith
  obtain ⟨C₁, hC₁⟩ := hlim_exp M
  -- Tail bound for `∑_{n ≥ N} (qPoch q q n - qPochLim 1 q)`:
  let C₂ : ℝ := (24 : ℝ) ^ N * (N.factorial : ℝ) / 144
  refine ⟨C₀ + C₁ + C₂, ?_⟩
  filter_upwards [hC₀, hC₁, eventually_ge_atTop (24 : ℝ)] with u h0 h1 hu
  have hu_pos : 0 < u := by linarith
  set q := Real.exp (-24 / u)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hu_pos)
  have h1q_pos : 0 < 1 - q := sub_pos.mpr hq1
  have hG_summ : Summable (fun n : ℕ => qPoch (1 * q) q n - qPochLim 1 q) := by
    have hdom : Summable (fun n : ℕ => q ^ (n + 1) / (1 - q)) :=
      (((summable_geometric_of_lt_one hq0.le hq1).mul_left q).div_const (1 - q)).congr
        fun n => by rw [pow_succ']
    refine hdom.of_nonneg_of_le (fun n => sub_nonneg.mpr (qPochLim_le_qPoch zero_le_one le_rfl hq0.le hq1.le n))
      fun n => ?_
    have hle := qPoch_sub_lim_le zero_le_one le_rfl hq0.le hq1 n
    have hp_le := qPoch_le_one (mul_nonneg zero_le_one hq0.le) (by linarith) hq0.le hq1.le n
    simpa [one_mul] using hle.trans (mul_le_of_le_one_left (by positivity) hp_le)
  have hsplit : qZagierG q 1 =
      (∑ n ∈ Finset.range N, qPoch q q n) - (N : ℝ) * qPochLim 1 q +
        ∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) := by
    unfold qZagierG
    simp only [one_pow, mul_one]
    rw [← hG_summ.sum_add_tsum_nat_add N, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    simp only [one_mul]
  have htail_le : 0 ≤ ∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) ∧
      ∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) ≤ C₂ / u ^ M := by
    have htail_summ : Summable (fun k : ℕ => qPoch (1 * q) q (k + N) - qPochLim 1 q) :=
      (summable_nat_add_iff N).mpr hG_summ
    constructor
    · exact tsum_nonneg fun k => sub_nonneg.mpr (qPochLim_le_qPoch zero_le_one le_rfl hq0.le hq1.le _)
    · have hqN_le : qPoch q q N ≤ (24 : ℝ) ^ N * (N.factorial : ℝ) / u ^ N := by
        unfold qPoch
        have h1 : ∏ j ∈ Finset.range N, (1 - q * q ^ j) ≤
            ∏ j ∈ Finset.range N, ((24 : ℝ) * ((j + 1 : ℕ) : ℝ) / u) := by
          refine real_prod_le_prod _ (fun j _ => by
            have : q * q ^ j ≤ 1 := (mul_le_mul hq1.le (pow_le_one₀ hq0.le hq1.le) (pow_nonneg hq0.le j) zero_le_one).trans_eq (mul_one 1)
            linarith) fun j _ => ?_
          have hpow : q * q ^ j = Real.exp (-((24 * (j + 1 : ℕ) : ℝ) / u)) := by
            dsimp only [q]; rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
          rw [hpow]
          exact one_sub_exp_neg_le
        refine h1.trans_eq ?_
        rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          Finset.prod_const, Finset.card_range]
        have hfac : (∏ x ∈ Finset.range N, ((x + 1 : ℕ) : ℝ)) = (N.factorial : ℝ) := by
          norm_cast
          induction N with
          | zero => simp
          | succ m ihm => rw [Finset.prod_range_succ, ihm, Nat.factorial_succ]; ring
        rw [hfac]
      have h1q_ge : 12 / u ≤ 1 - q := by
        have h := one_sub_exp_neg_ge_half (x := 24 / u) (by positivity) ((div_le_one hu_pos).mpr hu)
        have h2 : (24 / u) / 2 = 12 / u := by ring
        simpa [q, neg_div, h2] using h
      have h1q_inv : (1 - q)⁻¹ ≤ u / 12 := by
        have := inv_anti₀ (by positivity : 0 < 12 / u) h1q_ge
        simpa [inv_div] using this
      have hqN_nn : 0 ≤ qPoch q q N := qPoch_nonneg hq0.le hq1.le hq0.le hq1.le N
      have hdom : Summable (fun k : ℕ => (qPoch q q N / (1 - q)) * q ^ k) :=
        (summable_geometric_of_lt_one hq0.le hq1).mul_left _
      have hle_sum : ∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) ≤
          ∑' k : ℕ, (qPoch q q N / (1 - q)) * q ^ k := by
        refine htail_summ.tsum_le_tsum (fun k => ?_) hdom
        have h1 := qPoch_sub_lim_le zero_le_one le_rfl hq0.le hq1 (k + N)
        have h2 : qPoch (1 * q) q (k + N) ≤ qPoch q q N := by
          rw [one_mul]; exact qPoch_antitone hq0.le hq1.le hq0.le hq1.le (Nat.le_add_left N k)
        have h3 : q ^ (k + N + 1) ≤ q ^ k :=
          pow_le_pow_of_le_one hq0.le hq1.le (by omega)
        calc qPoch (1 * q) q (k + N) - qPochLim 1 q
            ≤ qPoch (1 * q) q (k + N) * (1 * q ^ (k + N + 1) / (1 - q)) := h1
          _ ≤ qPoch q q N * (1 * q ^ k / (1 - q)) := by gcongr
          _ = (qPoch q q N / (1 - q)) * q ^ k := by ring
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1] at hle_sum
      refine hle_sum.trans ?_
      calc qPoch q q N / (1 - q) * (1 - q)⁻¹
          = qPoch q q N * ((1 - q)⁻¹) ^ 2 := by rw [div_eq_mul_inv, sq]; ring
        _ ≤ ((24 : ℝ) ^ N * (N.factorial : ℝ) / u ^ N) * (u / 12) ^ 2 :=
            mul_le_mul hqN_le (pow_le_pow_left₀ (inv_nonneg.mpr h1q_pos.le) h1q_inv 2) (by positivity) (by positivity)
        _ = C₂ / u ^ M := by
            dsimp only [C₂, N]
            rw [pow_add]
            field_simp [hu_pos.ne']
            ring
  have hsum_same : ∑ k ∈ Finset.range M, PowerSeries.coeff k (fishburnSeries.subst zagierSubst) * ((u : ℂ)⁻¹ ^ k) =
      ∑ k ∈ Finset.range M, PowerSeries.coeff k (∑ n ∈ Finset.range N, (fishburnTerm n).subst zagierSubst) *
        ((u : ℂ)⁻¹ ^ k) :=
    Finset.sum_congr rfl fun k hk => by rw [hcoeff_eq k hk]
  rw [hsum_same]
  unfold fishburnQ
  rw [hsplit]
  simp only [map_zero, zero_mul, Finset.sum_const_zero, sub_zero] at h1
  have hcast_split : (((∑ n ∈ Finset.range N, qPoch q q n) - (N : ℝ) * qPochLim 1 q +
        ∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) : ℝ) : ℂ) =
      (∑ n ∈ Finset.range N, ((qPoch q q n : ℝ) : ℂ)) - ((N : ℝ) * qPochLim 1 q : ℂ) +
        ((∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hcast_split]
  have hrearr :
      ((∑ n ∈ Finset.range N, ((qPoch q q n : ℝ) : ℂ)) - ((N : ℝ) * qPochLim 1 q : ℂ) +
          ((∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) : ℝ) : ℂ)) -
        ∑ k ∈ Finset.range M, PowerSeries.coeff k (∑ n ∈ Finset.range N, (fishburnTerm n).subst zagierSubst) *
          ((u : ℂ)⁻¹ ^ k) =
      ((∑ n ∈ Finset.range N, ((qPoch q q n : ℝ) : ℂ)) -
        ∑ k ∈ Finset.range M, PowerSeries.coeff k (∑ n ∈ Finset.range N, (fishburnTerm n).subst zagierSubst) *
          ((u : ℂ)⁻¹ ^ k)) -
      ((N : ℝ) * qPochLim 1 q : ℂ) +
      ((∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) : ℝ) : ℂ) := by ring
  rw [hrearr]
  calc ‖((∑ n ∈ Finset.range N, ((qPoch q q n : ℝ) : ℂ)) - _) - _ + _‖
      ≤ ‖((∑ n ∈ Finset.range N, ((qPoch q q n : ℝ) : ℂ)) - _) - _‖ +
          ‖((∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖(∑ n ∈ Finset.range N, ((qPoch q q n : ℝ) : ℂ)) - _‖ + ‖((N : ℝ) * qPochLim 1 q : ℂ)‖ +
          ‖((∑' k : ℕ, (qPoch (1 * q) q (k + N) - qPochLim 1 q) : ℝ) : ℂ)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ C₀ / u ^ M + C₁ / u ^ M + C₂ / u ^ M := by
        refine add_le_add (add_le_add h0 h1) ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htail_le.1]
        exact htail_le.2
    _ = (C₀ + C₁ + C₂) / u ^ M := by ring

/-! ##### 6C.4. Bernoulli Generating Function & Shifted Euler–Maclaurin on `y e^{-y²}` -/

private def hGauss (y : ℝ) : ℂ :=
  (y : ℂ) * Complex.exp (-(y : ℂ) ^ 2)

private lemma hGauss_iteratedDeriv_poly (r : ℕ) :
    ∃ P : Polynomial ℂ, ∀ x : ℝ,
      iteratedDeriv r hGauss x = P.eval (x : ℂ) * Complex.exp (-(x : ℂ) ^ 2) := by
  induction r with
  | zero =>
    exact ⟨Polynomial.X, fun x => by simp [hGauss]⟩
  | succ r ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨Polynomial.derivative P - 2 * Polynomial.X * P, fun x => ?_⟩
    rw [iteratedDeriv_succ, show iteratedDeriv r hGauss = fun y : ℝ => P.eval (y : ℂ) * Complex.exp (-(y : ℂ) ^ 2)
      from funext hP]
    have hdP : HasDerivAt (fun y : ℝ => P.eval (y : ℂ)) ((Polynomial.derivative P).eval (x : ℂ)) x := by
      have h1 : HasDerivAt (fun z : ℂ => P.eval z) ((Polynomial.derivative P).eval (x : ℂ)) (x : ℂ) :=
        P.hasDerivAt (x : ℂ)
      simpa using h1.comp_ofReal
    have hdE : HasDerivAt (fun y : ℝ => Complex.exp (-(y : ℂ) ^ 2))
        (Complex.exp (-(x : ℂ) ^ 2) * (-2 * (x : ℂ))) x := by
      have hsq : HasDerivAt (fun y : ℝ => -(y : ℂ) ^ 2) (-2 * (x : ℂ)) x := by
        have h1 : HasDerivAt (fun z : ℂ => -z ^ 2) (-(2 * (x : ℂ))) (x : ℂ) := by
          simpa using (hasDerivAt_pow 2 (x : ℂ)).fun_neg
        exact (h1.comp_ofReal).congr_deriv (by ring)
      exact hsq.cexp
    rw [(hdP.fun_mul hdE).deriv]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    ring

private lemma hGauss_expDecaySmooth : PakPrimes.DivisorAndMacMahon.ExpDecaySmooth hGauss := by
  refine ⟨?_, fun r => ?_⟩
  · unfold hGauss
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (-(y : ℂ) ^ 2)) :=
      (Complex.contDiff_exp.comp (contDiff_id.pow 2).neg).comp h1
    exact h1.mul h2
  · obtain ⟨P, hP⟩ := hGauss_iteratedDeriv_poly r
    let C : ℝ := Real.exp 1 * ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * (k.factorial : ℝ)
    refine ⟨C, 1, by positivity, zero_lt_one, fun x hx => ?_⟩
    rw [hP x, norm_mul]
    have hexp_norm : ‖Complex.exp (-(x : ℂ) ^ 2)‖ = Real.exp (-(x ^ 2)) := by
      rw [Complex.norm_exp]; congr 1
      have : (-(x : ℂ) ^ 2) = ((-(x ^ 2) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [hexp_norm]
    have hquad : Real.exp (-(x ^ 2)) ≤ Real.exp 1 * Real.exp (-x) * Real.exp (-x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (x - 1)]
    have hpoly : ‖P.eval (x : ℂ)‖ * Real.exp (-x) ≤
        ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * (k.factorial : ℝ) := by
      rw [Polynomial.eval_eq_sum_range]
      refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hfac := Real.pow_div_factorial_le_exp x hx k
      have hmul := mul_le_mul_of_nonneg_right hfac (Real.exp_pos (-x)).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
      have hpos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
      calc x ^ k * Real.exp (-x)
          = (x ^ k / (k.factorial : ℝ) * Real.exp (-x)) * (k.factorial : ℝ) := by field_simp [hpos.ne']
        _ ≤ 1 * (k.factorial : ℝ) := mul_le_mul_of_nonneg_right hmul hpos.le
        _ = (k.factorial : ℝ) := one_mul _
    calc ‖P.eval (x : ℂ)‖ * Real.exp (-(x ^ 2))
        ≤ ‖P.eval (x : ℂ)‖ * (Real.exp 1 * Real.exp (-x) * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left hquad (norm_nonneg _)
      _ = Real.exp 1 * (‖P.eval (x : ℂ)‖ * Real.exp (-x)) * Real.exp (-x) := by ring
      _ ≤ Real.exp 1 * (∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * (k.factorial : ℝ)) *
            Real.exp (-1 * x) := by
          rw [neg_one_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos 1).le) (Real.exp_pos (-x)).le

private lemma iteratedDeriv_ofReal_comp_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => F (y : ℂ)) x = iteratedDeriv n F (x : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun y : ℝ => F (y : ℂ)) = fun y : ℝ => iteratedDeriv n F (y : ℂ) :=
      funext ih
    rw [hfun]
    have hd : Differentiable ℂ (iteratedDeriv n F) :=
      (hF.contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv n
        (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))
    exact ((hd (x : ℂ)).hasDerivAt.comp_ofReal).deriv

private lemma hGauss_iteratedDeriv_even (k : ℕ) :
    iteratedDeriv (2 * k) hGauss 0 = 0 := by
  let F : ℂ → ℂ := fun z => z * Complex.exp (-z ^ 2)
  have hF : Differentiable ℂ F := differentiable_id.mul (Complex.differentiable_exp.comp (differentiable_id.pow 2).neg)
  have hEq : iteratedDeriv (2 * k) hGauss 0 = iteratedDeriv (2 * k) F 0 :=
    iteratedDeriv_ofReal_comp_entire hF (2 * k) 0
  rw [hEq]
  have hodd : (fun z : ℂ => F (-z)) = fun z => -F z := funext fun z => by dsimp only [F]; ring_nf
  have h1 := iteratedDeriv_comp_neg (2 * k) F (0 : ℂ)
  rw [hodd, neg_zero] at h1
  have hneg : iteratedDeriv (2 * k) (fun z => -F z) 0 = -iteratedDeriv (2 * k) F 0 := by
    simp [iteratedDeriv_fun_neg]
  rw [hneg] at h1
  have hpow : (-1 : ℂ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  rw [hpow, one_smul] at h1
  have h2 : (2 : ℂ) * iteratedDeriv (2 * k) F 0 = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private lemma hGauss_iteratedDeriv_odd (k : ℕ) :
    iteratedDeriv (2 * k + 1) hGauss 0 =
      (-1 : ℂ) ^ k * (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ)) := by
  let F : ℂ → ℂ := fun z => z * Complex.exp (-z ^ 2)
  have hF : Differentiable ℂ F := differentiable_id.mul (Complex.differentiable_exp.comp (differentiable_id.pow 2).neg)
  have hEq : iteratedDeriv (2 * k + 1) hGauss 0 = iteratedDeriv (2 * k + 1) F 0 :=
    iteratedDeriv_ofReal_comp_entire hF (2 * k + 1) 0
  rw [hEq]
  have hg : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-w)) 0 :=
    (Complex.differentiable_exp.comp differentiable_neg).analyticAt 0
  have hodd := iteratedDeriv_odd_mul_sq k hg
  have hder : iteratedDeriv k (fun w : ℂ => Complex.exp (-w)) 0 = (-1 : ℂ) ^ k := by
    have h1 := iteratedDeriv_comp_neg k Complex.exp (0 : ℂ)
    rw [neg_zero] at h1
    have hexp_d : ∀ m : ℕ, iteratedDeriv m Complex.exp 0 = 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [iteratedDeriv_succ', Complex.deriv_exp]; exact ihm
    rw [hexp_d k, smul_eq_mul, mul_one] at h1
    exact h1
  rw [hder] at hodd
  simpa [F, mul_comm] using hodd

/-- Exact Bernoulli-polynomial-to-`torusKnotCoeff 2 3` identity, proved purely algebraically in
`PowerSeries ℂ` from Mathlib's `Polynomial.bernoulli_generating_function`. -/
private lemma bernoulli_fishburn_coeff_eq (k : ℕ) :
    -(1 / 2 : ℂ) * ((12 : ℂ) ^ (2 * k + 1)) *
        (emTermShift ((1 / 12 : ℚ) : ℝ) hGauss (2 * k + 1) -
         emTermShift ((5 / 12 : ℚ) : ℝ) hGauss (2 * k + 1) -
         emTermShift ((7 / 12 : ℚ) : ℝ) hGauss (2 * k + 1) +
         emTermShift ((11 / 12 : ℚ) : ℝ) hGauss (2 * k + 1)) =
      torusKnotCoeff 2 3 k / (k.factorial : ℂ) := by
  let Bps (q : ℚ) : PowerSeries ℂ :=
    PowerSeries.mk fun n => Polynomial.aeval (q : ℂ) ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n)
  let Bcomb : PowerSeries ℂ := Bps (1 / 12) - Bps (5 / 12) - Bps (7 / 12) + Bps (11 / 12)
  let E (a : ℂ) : PowerSeries ℂ := PowerSeries.rescale a (PowerSeries.exp ℂ)
  have hBgen : ∀ q : ℚ, Bps q * (PowerSeries.exp ℂ - 1) = PowerSeries.X * E (q : ℂ) := fun q =>
    Polynomial.bernoulli_generating_function (q : ℂ)
  have hBcomb_mul : Bcomb * (PowerSeries.exp ℂ - 1) =
      PowerSeries.X * (E (1 / 12 : ℂ) - E (5 / 12 : ℂ) - E (7 / 12 : ℂ) + E (11 / 12 : ℂ)) := by
    dsimp only [Bcomb]
    have h1 := hBgen (1 / 12)
    have h5 := hBgen (5 / 12)
    have h7 := hBgen (7 / 12)
    have h11 := hBgen (11 / 12)
    push_cast at h1 h5 h7 h11
    linear_combination h1 - h5 - h7 + h11
  -- Rescale by `12 * I` and factor `E(12 I) - 1` and `E(I) - E(5I) - E(7I) + E(11I)`:
  have hres := congrArg (PowerSeries.rescale (12 * Complex.I)) hBcomb_mul
  have hres_E : ∀ a : ℂ, PowerSeries.rescale (12 * Complex.I) (E a) = E (12 * Complex.I * a) := fun a => by
    dsimp only [E]; rw [PowerSeries.rescale_rescale]; congr 1; ring
  have hres_X : PowerSeries.rescale (12 * Complex.I) (PowerSeries.X : PowerSeries ℂ) =
      PowerSeries.C (12 * Complex.I) * PowerSeries.X := by
    ext n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    split_ifs with h
    · subst h; simp
    · simp
  simp only [map_mul, map_sub, map_add, map_one] at hres
  rw [hres_X] at hres
  have hE12 : PowerSeries.rescale (12 * Complex.I) (PowerSeries.exp ℂ) = E (12 * Complex.I) := rfl
  rw [hE12, hres_E, hres_E, hres_E, hres_E] at hres
  have h1a : 12 * Complex.I * (1 / 12 : ℂ) = Complex.I := by ring
  have h5a : 12 * Complex.I * (5 / 12 : ℂ) = 5 * Complex.I := by ring
  have h7a : 12 * Complex.I * (7 / 12 : ℂ) = 7 * Complex.I := by ring
  have h11a : 12 * Complex.I * (11 / 12 : ℂ) = 11 * Complex.I := by ring
  rw [h1a, h5a, h7a, h11a] at hres
  have hE_mul : ∀ a b : ℂ, E a * E b = E (a + b) := fun a b => PowerSeries.exp_mul_exp_eq_exp_add a b
  have hE_zero : E 0 = 1 := by
    ext n; simp [E, PowerSeries.coeff_one]
  have hfacL : E (12 * Complex.I) - 1 =
      (E (6 * Complex.I) * (E (3 * Complex.I) - E (-3 * Complex.I))) *
        (E (3 * Complex.I) + E (-3 * Complex.I)) := by
    symm
    calc (E (6 * Complex.I) * (E (3 * Complex.I) - E (-3 * Complex.I))) *
          (E (3 * Complex.I) + E (-3 * Complex.I))
        = E (6 * Complex.I) * (E (3 * Complex.I) * E (3 * Complex.I) - E (-3 * Complex.I) * E (-3 * Complex.I)) := by ring
      _ = E (6 * Complex.I) * (E (6 * Complex.I) - E (-6 * Complex.I)) := by
          rw [hE_mul, hE_mul, show 3 * Complex.I + 3 * Complex.I = 6 * Complex.I by ring,
            show -3 * Complex.I + -3 * Complex.I = -6 * Complex.I by ring]
      _ = E (6 * Complex.I) * E (6 * Complex.I) - E (6 * Complex.I) * E (-6 * Complex.I) := by ring
      _ = E (12 * Complex.I) - 1 := by
          rw [hE_mul, hE_mul, show 6 * Complex.I + 6 * Complex.I = 12 * Complex.I by ring,
            show 6 * Complex.I + -6 * Complex.I = 0 by ring, hE_zero]
  have hfacR : E Complex.I - E (5 * Complex.I) - E (7 * Complex.I) + E (11 * Complex.I) =
      (E (6 * Complex.I) * (E (3 * Complex.I) - E (-3 * Complex.I))) *
        (E (2 * Complex.I) - E (-2 * Complex.I)) := by
    symm
    calc (E (6 * Complex.I) * (E (3 * Complex.I) - E (-3 * Complex.I))) *
          (E (2 * Complex.I) - E (-2 * Complex.I))
        = E (6 * Complex.I) * (E (3 * Complex.I) * E (2 * Complex.I) - E (3 * Complex.I) * E (-2 * Complex.I) -
            E (-3 * Complex.I) * E (2 * Complex.I) + E (-3 * Complex.I) * E (-2 * Complex.I)) := by ring
      _ = E (6 * Complex.I) * (E (5 * Complex.I) - E Complex.I - E (-Complex.I) + E (-5 * Complex.I)) := by
          rw [hE_mul, hE_mul, hE_mul, hE_mul,
            show 3 * Complex.I + 2 * Complex.I = 5 * Complex.I by ring,
            show 3 * Complex.I + -2 * Complex.I = Complex.I by ring,
            show -3 * Complex.I + 2 * Complex.I = -Complex.I by ring,
            show -3 * Complex.I + -2 * Complex.I = -5 * Complex.I by ring]
      _ = E (6 * Complex.I) * E (5 * Complex.I) - E (6 * Complex.I) * E Complex.I -
          E (6 * Complex.I) * E (-Complex.I) + E (6 * Complex.I) * E (-5 * Complex.I) := by ring
      _ = E Complex.I - E (5 * Complex.I) - E (7 * Complex.I) + E (11 * Complex.I) := by
          rw [hE_mul, hE_mul, hE_mul, hE_mul,
            show 6 * Complex.I + 5 * Complex.I = 11 * Complex.I by ring,
            show 6 * Complex.I + Complex.I = 7 * Complex.I by ring,
            show 6 * Complex.I + -Complex.I = 5 * Complex.I by ring,
            show 6 * Complex.I + -5 * Complex.I = Complex.I by ring]
          ring
  have hfactor_ne : E (6 * Complex.I) * (E (3 * Complex.I) - E (-3 * Complex.I)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h0
      have hc := congrArg (PowerSeries.coeff 0) h0
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at hc
      simp at hc
    · intro h0
      have hc := congrArg (PowerSeries.coeff 1) h0
      simp only [E, map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, pow_one,
        Nat.factorial_one, Nat.cast_one, div_one, map_one, mul_one, map_zero] at hc
      have : (6 : ℂ) * Complex.I = 0 := by linear_combination hc
      exact mul_ne_zero (by norm_num) Complex.I_ne_zero this
  have hcancel1 : PowerSeries.rescale (12 * Complex.I) Bcomb * (E (3 * Complex.I) + E (-3 * Complex.I)) =
      PowerSeries.C (12 * Complex.I) * PowerSeries.X * (E (2 * Complex.I) - E (-2 * Complex.I)) := by
    rw [hfacL, hfacR] at hres
    have hmul : (E (6 * Complex.I) * (E (3 * Complex.I) - E (-3 * Complex.I))) *
        (PowerSeries.rescale (12 * Complex.I) Bcomb * (E (3 * Complex.I) + E (-3 * Complex.I))) =
      (E (6 * Complex.I) * (E (3 * Complex.I) - E (-3 * Complex.I))) *
        (PowerSeries.C (12 * Complex.I) * PowerSeries.X * (E (2 * Complex.I) - E (-2 * Complex.I))) := by
      linear_combination hres
    exact mul_left_cancel₀ hfactor_ne hmul
  -- Compare with the Taylor series `Tps` of `sin(2s) / (2 cos(3s))`:
  let fT : ℂ → ℂ := fun s => Complex.sin (2 * s) / (2 * Complex.cos (3 * s))
  let Tps : PowerSeries ℂ := PowerSeries.mk fun n => iteratedDeriv n fT 0 / (n.factorial : ℂ)
  have hfT_an : AnalyticAt ℂ fT 0 := by
    have hnum : AnalyticAt ℂ (fun s : ℂ => Complex.sin (2 * s)) 0 :=
      (Complex.differentiable_sin.comp (differentiable_const (2 : ℂ) |>.mul differentiable_id)).analyticAt 0
    have hden : AnalyticAt ℂ (fun s : ℂ => 2 * Complex.cos (3 * s)) 0 :=
      (differentiable_const (2 : ℂ) |>.mul
        (Complex.differentiable_cos.comp (differentiable_const (3 : ℂ) |>.mul differentiable_id))).analyticAt 0
    exact hnum.div hden (by simp)
  have hT_mul : Tps * (E (3 * Complex.I) + E (-3 * Complex.I)) =
      PowerSeries.C (1 / (2 * Complex.I)) * (E (2 * Complex.I) - E (-2 * Complex.I)) := by
    have hexp_d : ∀ m : ℕ, iteratedDeriv m Complex.exp 0 = 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm => rw [iteratedDeriv_succ', Complex.deriv_exp]; exact ihm
    have hE_deriv : ∀ (a : ℂ) (m : ℕ),
        iteratedDeriv m (fun s : ℂ => Complex.exp (a * s)) 0 = a ^ m := fun a m => by
      have h1 := iteratedDeriv_comp_const_mul (f := Complex.exp) a m (0 : ℂ)
        (by simpa using Complex.differentiable_exp.analyticAt 0)
      rw [mul_zero, hexp_d m, mul_one] at h1
      exact h1
    have hcd_exp : ∀ a : ℂ, ContDiffAt ℂ (⊤ : ℕ∞) (fun s : ℂ => Complex.exp (a * s)) 0 := fun a =>
      (Complex.differentiable_exp.comp (differentiable_const a |>.mul differentiable_id)).contDiff.contDiffAt
    have hcos_d : ∀ m : ℕ, iteratedDeriv m (fun s : ℂ => 2 * Complex.cos (3 * s)) 0 =
        (3 * Complex.I) ^ m + (-3 * Complex.I) ^ m := fun m => by
      have hfun : (fun s : ℂ => 2 * Complex.cos (3 * s)) =
          fun s => Complex.exp ((3 * Complex.I) * s) + Complex.exp ((-3 * Complex.I) * s) := funext fun s => by
        rw [Complex.cos]; ring_nf
      rw [hfun, iteratedDeriv_fun_add (f := fun s : ℂ => Complex.exp (3 * Complex.I * s))
        (g := fun s : ℂ => Complex.exp (-3 * Complex.I * s))
        ((hcd_exp _).of_le (WithTop.coe_le_coe.mpr le_top))
        ((hcd_exp _).of_le (WithTop.coe_le_coe.mpr le_top)), hE_deriv, hE_deriv]
    have hsin_d : ∀ m : ℕ, iteratedDeriv m (fun s : ℂ => Complex.sin (2 * s)) 0 =
        (1 / (2 * Complex.I)) * ((2 * Complex.I) ^ m - (-2 * Complex.I) ^ m) := fun m => by
      have hfun : (fun s : ℂ => Complex.sin (2 * s)) =
          fun s => (1 / (2 * Complex.I)) * (Complex.exp ((2 * Complex.I) * s) - Complex.exp ((-2 * Complex.I) * s)) :=
        funext fun s => by
          rw [Complex.sin]
          have h2I : 2 * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
          have heq1 : (-(2 * s) * Complex.I) = (-2 * Complex.I) * s := by ring
          have heq2 : (2 * s * Complex.I) = (2 * Complex.I) * s := by ring
          rw [heq1, heq2]; field_simp [h2I]; rw [Complex.I_sq]; ring
      rw [hfun, iteratedDeriv_const_mul (f := fun s : ℂ => Complex.exp (2 * Complex.I * s) - Complex.exp (-2 * Complex.I * s))
        (1 / (2 * Complex.I)) (((hcd_exp _).sub (hcd_exp _)).of_le (WithTop.coe_le_coe.mpr le_top)),
        iteratedDeriv_fun_sub (f := fun s : ℂ => Complex.exp (2 * Complex.I * s))
          (g := fun s : ℂ => Complex.exp (-2 * Complex.I * s))
          ((hcd_exp _).of_le (WithTop.coe_le_coe.mpr le_top))
          ((hcd_exp _).of_le (WithTop.coe_le_coe.mpr le_top)), hE_deriv, hE_deriv]
    have hprod_eq : (fun s : ℂ => fT s * (2 * Complex.cos (3 * s))) =ᶠ[𝓝 0] fun s => Complex.sin (2 * s) := by
      have hcos0 : ContinuousAt (fun s : ℂ => 2 * Complex.cos (3 * s)) 0 := by fun_prop
      filter_upwards [hcos0.eventually_ne (by simp : (2 : ℂ) * Complex.cos (3 * 0) ≠ 0)] with s hs
      exact div_mul_cancel₀ _ hs
    ext n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_C_mul]
    have hleib := iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ)) (f := fT)
      (g := fun s : ℂ => 2 * Complex.cos (3 * s)) hfT_an.contDiffAt
      ((differentiable_const (2 : ℂ) |>.mul
        (Complex.differentiable_cos.comp (differentiable_const (3 : ℂ) |>.mul differentiable_id))).analyticAt 0).contDiffAt
    have hcongr : iteratedDeriv n (fun s : ℂ => fT s * (2 * Complex.cos (3 * s))) 0 =
        iteratedDeriv n (fun s : ℂ => Complex.sin (2 * s)) 0 :=
      Filter.EventuallyEq.iteratedDeriv_eq n hprod_eq
    rw [hcongr, hsin_d] at hleib
    have hfac_n : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hsum_eq : ∑ i ∈ Finset.range (n + 1),
          PowerSeries.coeff i Tps * PowerSeries.coeff (n - i) (E (3 * Complex.I) + E (-3 * Complex.I)) =
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) * iteratedDeriv i fT 0 *
            iteratedDeriv (n - i) (fun s : ℂ => 2 * Complex.cos (3 * s)) 0) / (n.factorial : ℂ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp only [Tps, E, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
        map_div₀, map_one, map_natCast, hcos_d]
      have hch := congrArg (fun m : ℕ => (m : ℂ)) (Nat.choose_mul_factorial_mul_factorial hi_le)
      push_cast at hch
      have hfi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      have hfni : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - i)
      field_simp [hfac_n, hfi, hfni]
      linear_combination -(iteratedDeriv i fT 0 * ((3 * Complex.I) ^ (n - i) + (-3 * Complex.I) ^ (n - i))) * hch
    rw [hsum_eq, ← hleib]
    simp only [E, map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_div₀, map_one, map_natCast]
    field_simp [hfac_n]
  have hcos_ne : E (3 * Complex.I) + E (-3 * Complex.I) ≠ 0 := by
    intro h0
    have hc := congrArg (PowerSeries.coeff 0) h0
    rw [map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at hc
    simp at hc
  have hB_eq_T : PowerSeries.rescale (12 * Complex.I) Bcomb =
      PowerSeries.C (-24 : ℂ) * PowerSeries.X * Tps := by
    refine mul_right_cancel₀ hcos_ne ?_
    rw [hcancel1, mul_assoc, mul_assoc, hT_mul]
    have hcoeff_id : PowerSeries.C (-24 : ℂ) * PowerSeries.X * (PowerSeries.C (1 / (2 * Complex.I)) *
        (E (2 * Complex.I) - E (-2 * Complex.I))) =
        PowerSeries.C (-24 * (1 / (2 * Complex.I))) * (PowerSeries.X * (E (2 * Complex.I) - E (-2 * Complex.I))) := by
      rw [map_mul]; ring
    rw [hcoeff_id]
    have h24 : (-24 : ℂ) * (1 / (2 * Complex.I)) = 12 * Complex.I := by
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp [hI]; rw [Complex.I_sq]; ring
    rw [h24]
  -- Extract coefficient `2 * k + 2` from `hB_eq_T`:
  have hcoeff := congrArg (PowerSeries.coeff (2 * k + 2)) hB_eq_T
  rw [PowerSeries.coeff_rescale, mul_assoc, PowerSeries.coeff_C_mul,
    show 2 * k + 2 = (2 * k + 1) + 1 by omega, PowerSeries.coeff_succ_X_mul] at hcoeff
  have hBps_coeff : ∀ q : ℚ, PowerSeries.coeff (2 * k + 2) (Bps q) =
      ((bernoulliFun (2 * k + 2) (q : ℝ) : ℝ) : ℂ) / ((2 * k + 2).factorial : ℂ) := fun q => by
    simp only [Bps, PowerSeries.coeff_mk, Algebra.smul_def, map_mul, bernoulliFun]
    have heval : Polynomial.aeval (q : ℂ) (Polynomial.bernoulli (2 * k + 2)) =
        ((Polynomial.eval (q : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k + 2))) : ℝ) : ℂ) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      have hmap : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.bernoulli (2 * k + 2)) =
          Polynomial.map (algebraMap ℝ ℂ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k + 2))) := by
        rw [Polynomial.map_map]; rfl
      have hqC : (q : ℂ) = algebraMap ℝ ℂ (q : ℝ) := by simp
      rw [hmap, hqC, Polynomial.eval_map_apply]
      rfl
    rw [heval, AlgHom.commutes, one_div, map_inv₀, map_natCast, div_eq_mul_inv, mul_comm]
  have hLHS_coeff : PowerSeries.coeff (2 * k + 2) Bcomb =
      (((bernoulliFun (2 * k + 2) ((1 / 12 : ℚ) : ℝ) : ℝ) : ℂ) -
       ((bernoulliFun (2 * k + 2) ((5 / 12 : ℚ) : ℝ) : ℝ) : ℂ) -
       ((bernoulliFun (2 * k + 2) ((7 / 12 : ℚ) : ℝ) : ℝ) : ℂ) +
       ((bernoulliFun (2 * k + 2) ((11 / 12 : ℚ) : ℝ) : ℝ) : ℂ)) / ((2 * k + 2).factorial : ℂ) := by
    simp only [Bcomb, map_add, map_sub, hBps_coeff]
    ring
  have hRHS_coeff : PowerSeries.coeff (2 * k + 1) Tps = torusKnotCoeff 2 3 k / ((2 * k + 1).factorial : ℂ) := by
    simp only [Tps, PowerSeries.coeff_mk, fT, fishburnEulerCoeff_eq_trig]
  rw [show (2 * k + 1) + 1 = 2 * k + 2 by omega] at hcoeff
  rw [hLHS_coeff, hRHS_coeff] at hcoeff
  have hpowI : (12 * Complex.I) ^ (2 * k + 2) = (-1 : ℂ) ^ (k + 1) * (12 : ℂ) ^ (2 * k + 2) := by
    rw [mul_pow, show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul Complex.I, Complex.I_sq]; ring
  rw [hpowI] at hcoeff
  -- Substitute `hcoeff` into the target expression:
  simp only [emTermShift, hGauss_iteratedDeriv_odd k, show 2 * k + 1 + 1 = 2 * k + 2 by omega]
  have hfac1 : ((2 * k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfac2 : ((2 * k + 2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfack : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hpow12 : (12 : ℂ) ^ (2 * k + 2) = 12 * (12 : ℂ) ^ (2 * k + 1) := by rw [pow_succ']
  have hneg_pow : (-1 : ℂ) ^ (k + 1) = -((-1 : ℂ) ^ k) := by rw [pow_succ]; ring
  rw [hpow12, hneg_pow] at hcoeff
  have hB_simp : (12 : ℂ) ^ (2 * k + 1) * (-1 : ℂ) ^ k *
      ((((bernoulliFun (2 * k + 2) ((1 / 12 : ℚ) : ℝ) : ℝ) : ℂ) -
        ((bernoulliFun (2 * k + 2) ((5 / 12 : ℚ) : ℝ) : ℝ) : ℂ) -
        ((bernoulliFun (2 * k + 2) ((7 / 12 : ℚ) : ℝ) : ℝ) : ℂ) +
        ((bernoulliFun (2 * k + 2) ((11 / 12 : ℚ) : ℝ) : ℝ) : ℂ)) / ((2 * k + 2).factorial : ℂ)) =
      2 * (torusKnotCoeff 2 3 k / ((2 * k + 1).factorial : ℂ)) := by
    linear_combination -hcoeff / 12
  calc -(1 / 2 : ℂ) * (12 : ℂ) ^ (2 * k + 1) *
        (-(((bernoulliFun (2 * k + 2) ((1 / 12 : ℚ) : ℝ) : ℝ) : ℂ) / ((2 * k + 2).factorial : ℂ)) *
            ((-1 : ℂ) ^ k * (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ))) -
         -(((bernoulliFun (2 * k + 2) ((5 / 12 : ℚ) : ℝ) : ℝ) : ℂ) / ((2 * k + 2).factorial : ℂ)) *
            ((-1 : ℂ) ^ k * (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ))) -
         -(((bernoulliFun (2 * k + 2) ((7 / 12 : ℚ) : ℝ) : ℝ) : ℂ) / ((2 * k + 2).factorial : ℂ)) *
            ((-1 : ℂ) ^ k * (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ))) +
         -(((bernoulliFun (2 * k + 2) ((11 / 12 : ℚ) : ℝ) : ℝ) : ℂ) / ((2 * k + 2).factorial : ℂ)) *
            ((-1 : ℂ) ^ k * (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ))))
      = (1 / 2 : ℂ) * ((12 : ℂ) ^ (2 * k + 1) * (-1 : ℂ) ^ k *
          ((((bernoulliFun (2 * k + 2) ((1 / 12 : ℚ) : ℝ) : ℝ) : ℂ) -
            ((bernoulliFun (2 * k + 2) ((5 / 12 : ℚ) : ℝ) : ℝ) : ℂ) -
            ((bernoulliFun (2 * k + 2) ((7 / 12 : ℚ) : ℝ) : ℝ) : ℂ) +
            ((bernoulliFun (2 * k + 2) ((11 / 12 : ℚ) : ℝ) : ℝ) : ℂ)) / ((2 * k + 2).factorial : ℂ))) *
          (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ)) := by ring
    _ = (1 / 2 : ℂ) * (2 * (torusKnotCoeff 2 3 k / ((2 * k + 1).factorial : ℂ))) *
          (((2 * k + 1).factorial : ℂ) / (k.factorial : ℂ)) := by rw [hB_simp]
    _ = torusKnotCoeff 2 3 k / (k.factorial : ℂ) := by field_simp [hfac1, hfack]

private lemma falseTheta_hasAsympExp :
    HasAsympExp
      (fun u : ℝ => -(1 / 2 : ℂ) * Complex.exp (-(1 : ℂ) / (u : ℂ)) *
        ((qZagierF (Real.exp (-24 / u)) : ℝ) : ℂ))
      fishburnEulerSeries := by
  let Scomb (v : ℝ) : ℂ :=
    sumScaleShift ((1 / 12 : ℚ) : ℝ) hGauss v -
    sumScaleShift ((5 / 12 : ℚ) : ℝ) hGauss v -
    sumScaleShift ((7 / 12 : ℚ) : ℝ) hGauss v +
    sumScaleShift ((11 / 12 : ℚ) : ℝ) hGauss v
  let Ecomb : PowerSeries ℂ :=
    emSeriesShift ((1 / 12 : ℚ) : ℝ) hGauss -
    emSeriesShift ((5 / 12 : ℚ) : ℝ) hGauss -
    emSeriesShift ((7 / 12 : ℚ) : ℝ) hGauss +
    emSeriesShift ((11 / 12 : ℚ) : ℝ) hGauss
  have hEM1 := sumScaleShift_hasAsympExp (q := (1 / 12 : ℚ)) (by norm_num) (by norm_num) hGauss_expDecaySmooth
  have hEM5 := sumScaleShift_hasAsympExp (q := (5 / 12 : ℚ)) (by norm_num) (by norm_num) hGauss_expDecaySmooth
  have hEM7 := sumScaleShift_hasAsympExp (q := (7 / 12 : ℚ)) (by norm_num) (by norm_num) hGauss_expDecaySmooth
  have hEM11 := sumScaleShift_hasAsympExp (q := (11 / 12 : ℚ)) (by norm_num) (by norm_num) hGauss_expDecaySmooth
  have hScomb : HasAsympExp Scomb Ecomb := by
    have h1 := (hasAsympExp_sub (hasAsympExp_sub hEM1 hEM5) hEM7).add hEM11
    refine hasAsympExp_congr (Filter.Eventually.of_forall fun v => ?_) h1
    dsimp only [Scomb]; ring
  -- Pointwise identity for `u > 0`:
  -- `-(1/2) * exp(-1/u) * qZagierF(exp(-24/u)) = -(√u / 2) * Scomb(√u / 12)`:
  have hpt : ∀ {u : ℝ}, 0 < u →
      -(1 / 2 : ℂ) * Complex.exp (-(1 : ℂ) / (u : ℂ)) * ((qZagierF (Real.exp (-24 / u)) : ℝ) : ℂ) =
        -((Real.sqrt u : ℂ) / 2) * Scomb (Real.sqrt u / 12) := by
    intro u hu
    have hsq_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
    have hsq_sq : (Real.sqrt u : ℂ) ^ 2 = (u : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hu.le]
    have hterm_id : ∀ (a : ℕ) (k : ℕ),
        (Real.sqrt u : ℂ) * hGauss (((k : ℝ) + ((a : ℚ) / 12 : ℚ)) / (Real.sqrt u / 12)) =
          ((12 * k + a : ℕ) : ℂ) * Complex.exp (-(((12 * k + a : ℕ) : ℂ) ^ 2) / (u : ℂ)) := fun a k => by
      unfold hGauss
      have harg : (((k : ℝ) + ((a : ℚ) / 12 : ℚ)) / (Real.sqrt u / 12) : ℝ) =
          ((12 * k + a : ℕ) : ℝ) / Real.sqrt u := by
        push_cast; field_simp [hsq_pos.ne']
      rw [harg]
      push_cast
      have hsq_ne : (Real.sqrt u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq_pos.ne'
      rw [div_pow, hsq_sq, ← neg_div]
      field_simp [hsq_ne]
    -- Each of the 4 shifted sums is summable:
    have hsum_shift : ∀ (q : ℚ), 0 < (q : ℝ) →
        Summable (fun k : ℕ => hGauss (((k : ℝ) + (q : ℝ)) / (Real.sqrt u / 12))) := fun q hq => by
      obtain ⟨C, c, hC, hc, hbd⟩ := hGauss_expDecaySmooth.2 0
      have hv : 0 < Real.sqrt u / 12 := by positivity
      have hlt : Real.exp (-c / (Real.sqrt u / 12)) < 1 :=
        Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hv)
      refine ((summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left C).of_norm_bounded fun k => ?_
      have h0 : ‖hGauss (((k : ℝ) + (q : ℝ)) / (Real.sqrt u / 12))‖ ≤
          C * Real.exp (-c * (((k : ℝ) + (q : ℝ)) / (Real.sqrt u / 12))) := by
        simpa [iteratedDeriv_zero] using hbd _ (by positivity)
      refine h0.trans (mul_le_mul_of_nonneg_left ?_ hC)
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have : (k : ℝ) / (Real.sqrt u / 12) ≤ ((k : ℝ) + (q : ℝ)) / (Real.sqrt u / 12) :=
        div_le_div_of_nonneg_right (by linarith) hv.le
      calc -c * (((k : ℝ) + (q : ℝ)) / (Real.sqrt u / 12))
          ≤ -c * ((k : ℝ) / (Real.sqrt u / 12)) := mul_le_mul_of_nonpos_left this (by linarith)
        _ = (k : ℝ) * (-c / (Real.sqrt u / 12)) := by ring
    have hs1 := (hsum_shift (1 / 12) (by norm_num)).mul_left (Real.sqrt u : ℂ)
    have hs5 := (hsum_shift (5 / 12) (by norm_num)).mul_left (Real.sqrt u : ℂ)
    have hs7 := (hsum_shift (7 / 12) (by norm_num)).mul_left (Real.sqrt u : ℂ)
    have hs11 := (hsum_shift (11 / 12) (by norm_num)).mul_left (Real.sqrt u : ℂ)
    have hScomb_eq : (Real.sqrt u : ℂ) * Scomb (Real.sqrt u / 12) =
        ∑' k : ℕ,
          (((12 * k + 1 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 1 : ℕ) : ℂ) ^ 2) / (u : ℂ)) -
           ((12 * k + 5 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 5 : ℕ) : ℂ) ^ 2) / (u : ℂ)) -
           ((12 * k + 7 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 7 : ℕ) : ℂ) ^ 2) / (u : ℂ)) +
           ((12 * k + 11 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 11 : ℕ) : ℂ) ^ 2) / (u : ℂ))) := by
      dsimp only [Scomb, sumScaleShift]
      rw [mul_add, mul_sub, mul_sub, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
        ← hs1.tsum_sub hs5, ← (hs1.sub hs5).tsum_sub hs7, ← ((hs1.sub hs5).sub hs7).tsum_add hs11]
      refine tsum_congr fun k => ?_
      have h1 : ((1 / 12 : ℚ) : ℝ) = (((1 : ℕ) : ℚ) / 12 : ℚ) := by norm_num
      have h5 : ((5 / 12 : ℚ) : ℝ) = (((5 : ℕ) : ℚ) / 12 : ℚ) := by norm_num
      have h7 : ((7 / 12 : ℚ) : ℝ) = (((7 : ℕ) : ℚ) / 12 : ℚ) := by norm_num
      have h11 : ((11 / 12 : ℚ) : ℝ) = (((11 : ℕ) : ℚ) / 12 : ℚ) := by norm_num
      rw [h1, h5, h7, h11, hterm_id 1 k, hterm_id 5 k, hterm_id 7 k, hterm_id 11 k]
    -- Pair even (`2k`) and odd (`2k + 1`) terms of `qZagierF(exp(-24/u))`:
    let fF : ℕ → ℂ := fun n =>
      (-1 : ℂ) ^ n *
        (((6 * n + 1 : ℕ) : ℂ) * Complex.exp (-(((6 * n + 1 : ℕ) : ℂ) ^ 2) / (u : ℂ)) -
         ((6 * n + 5 : ℕ) : ℂ) * Complex.exp (-(((6 * n + 5 : ℕ) : ℂ) ^ 2) / (u : ℂ)))
    have hF_term : ∀ n : ℕ,
        Complex.exp (-(1 : ℂ) / (u : ℂ)) *
          (((-1 : ℝ) ^ n * (((6 * n + 1 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2) -
            ((6 * n + 5 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 5) / 2 + 1)) : ℝ) : ℂ) =
          fF n := fun n => by
      dsimp only [fF]
      have hE1 : Complex.exp (-(1 : ℂ) / (u : ℂ)) * (Complex.exp ((-24 : ℂ) / (u : ℂ))) ^ (n * (3 * n + 1) / 2) =
          Complex.exp (-(((6 * n + 1 : ℕ) : ℂ) ^ 2) / (u : ℂ)) := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        have hp1 := congrArg (fun m : ℕ => (m : ℂ)) (pent_sq_one n)
        push_cast at hp1 ⊢
        have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
        field_simp [huC]; linear_combination -hp1
      have hE5 : Complex.exp (-(1 : ℂ) / (u : ℂ)) * (Complex.exp ((-24 : ℂ) / (u : ℂ))) ^ (n * (3 * n + 5) / 2 + 1) =
          Complex.exp (-(((6 * n + 5 : ℕ) : ℂ) ^ 2) / (u : ℂ)) := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        have hp5 := congrArg (fun m : ℕ => (m : ℂ)) (pent_sq_five n)
        push_cast at hp5 ⊢
        have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
        field_simp [huC]; linear_combination -hp5
      have hcast : (((Real.exp (-24 / u) : ℝ) : ℂ)) = Complex.exp ((-24 : ℂ) / (u : ℂ)) := by
        rw [Complex.ofReal_exp]; push_cast; rfl
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
        Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_natCast, hcast]
      calc Complex.exp (-(1 : ℂ) / (u : ℂ)) *
            ((-1 : ℂ) ^ n * (((6 * n + 1 : ℕ) : ℂ) * Complex.exp ((-24 : ℂ) / (u : ℂ)) ^ (n * (3 * n + 1) / 2) -
              ((6 * n + 5 : ℕ) : ℂ) * Complex.exp ((-24 : ℂ) / (u : ℂ)) ^ (n * (3 * n + 5) / 2 + 1)))
          = (-1 : ℂ) ^ n *
              (((6 * n + 1 : ℕ) : ℂ) * (Complex.exp (-(1 : ℂ) / (u : ℂ)) * Complex.exp ((-24 : ℂ) / (u : ℂ)) ^ (n * (3 * n + 1) / 2)) -
               ((6 * n + 5 : ℕ) : ℂ) * (Complex.exp (-(1 : ℂ) / (u : ℂ)) * Complex.exp ((-24 : ℂ) / (u : ℂ)) ^ (n * (3 * n + 5) / 2 + 1))) := by ring
        _ = (-1 : ℂ) ^ n * (((6 * n + 1 : ℕ) : ℂ) * Complex.exp (-(((6 * n + 1 : ℕ) : ℂ) ^ 2) / (u : ℂ)) -
              ((6 * n + 5 : ℕ) : ℂ) * Complex.exp (-(((6 * n + 5 : ℕ) : ℂ) ^ 2) / (u : ℂ))) := by
            rw [hE1, hE5]
    have hfF_summ : Summable fF := by
      have hq0 : 0 < Real.exp (-24 / u) := Real.exp_pos _
      have hq1 : Real.exp (-24 / u) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hu)
      refine Summable.of_norm_bounded (g := fun n => 12 * (((n : ℝ) + 1) * 1 ^ n * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2)))
        ((summable_pow_pent_mul hq0 hq1 1 zero_le_one).mul_left 12) fun n => ?_
      have hre_neg : (-(1 : ℂ) / (u : ℂ)).re = -(1 / u) := by
        have h1 : (-(1 : ℂ) / (u : ℂ)) = ((-(1 / u) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.ofReal_re]
      rw [← hF_term n, norm_mul, Complex.norm_exp, hre_neg]
      have hexp1 : Real.exp (-(1 / u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [div_pos one_pos hu])
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, mul_one]
      have hq_alt : (Real.exp (-24 / u)) ^ (n * (3 * n + 5) / 2 + 1) ≤ (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2) := by
        rw [← pent_alt_eq n, pow_add]
        exact mul_le_of_le_one_right (pow_nonneg hq0.le _) (pow_le_one₀ hq0.le hq1.le)
      have habs : |((6 * n + 1 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2) -
            ((6 * n + 5 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 5) / 2 + 1)| ≤
          12 * (((n : ℝ) + 1) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2)) := by
        calc |((6 * n + 1 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2) -
                ((6 * n + 5 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 5) / 2 + 1)|
            ≤ |((6 * n + 1 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2)| +
              |((6 * n + 5 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 5) / 2 + 1)| := abs_sub _ _
          _ = ((6 * n + 1 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2) +
              ((6 * n + 5 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 5) / 2 + 1) := by
              rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
          _ ≤ ((6 * n + 1 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2) +
              ((6 * n + 5 : ℕ) : ℝ) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2) := by gcongr
          _ ≤ 12 * (((n : ℝ) + 1) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2)) := by
              push_cast; nlinarith [pow_nonneg hq0.le (n * (3 * n + 1) / 2), Nat.cast_nonneg (α := ℝ) n]
      calc Real.exp (-(1 / u)) * |_ - _| ≤ 1 * |_ - _| := mul_le_mul_of_nonneg_right hexp1 (abs_nonneg _)
        _ = |_ - _| := one_mul _
        _ ≤ 12 * (((n : ℝ) + 1) * (Real.exp (-24 / u)) ^ (n * (3 * n + 1) / 2)) := habs
    have hF_tsum : Complex.exp (-(1 : ℂ) / (u : ℂ)) * ((qZagierF (Real.exp (-24 / u)) : ℝ) : ℂ) = ∑' n : ℕ, fF n := by
      unfold qZagierF
      rw [Complex.ofReal_tsum, ← tsum_mul_left]
      exact tsum_congr hF_term
    have hpair : ∑' n : ℕ, fF n = ∑' k : ℕ, (fF (2 * k) + fF (2 * k + 1)) := by
      have hev : Summable (fun k : ℕ => fF (2 * k)) := hfF_summ.comp_injective (fun a b h => by omega)
      have hod : Summable (fun k : ℕ => fF (2 * k + 1)) := hfF_summ.comp_injective (fun a b h => by omega)
      have h2N : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (2 * N), fF n) atTop (𝓝 (∑' n : ℕ, fF n)) :=
        hfF_summ.hasSum.tendsto_sum_nat.comp
          (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩)
      have hsum_eq : ∀ N : ℕ, ∑ n ∈ Finset.range (2 * N), fF n =
          ∑ k ∈ Finset.range N, (fF (2 * k) + fF (2 * k + 1)) := by
        intro N
        induction N with
        | zero => simp
        | succ m ihm =>
          rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ, ihm, add_assoc]
      exact tendsto_nhds_unique (h2N.congr hsum_eq) (hev.add hod).hasSum.tendsto_sum_nat
    have hpair_eq : ∀ k : ℕ, fF (2 * k) + fF (2 * k + 1) =
        ((12 * k + 1 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 1 : ℕ) : ℂ) ^ 2) / (u : ℂ)) -
        ((12 * k + 5 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 5 : ℕ) : ℂ) ^ 2) / (u : ℂ)) -
        ((12 * k + 7 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 7 : ℕ) : ℂ) ^ 2) / (u : ℂ)) +
        ((12 * k + 11 : ℕ) : ℂ) * Complex.exp (-(((12 * k + 11 : ℕ) : ℂ) ^ 2) / (u : ℂ)) := fun k => by
      dsimp only [fF]
      have hev : (-1 : ℂ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
      have hod : (-1 : ℂ) ^ (2 * k + 1) = -1 := by rw [pow_succ, hev]; norm_num
      rw [hev, hod, show 6 * (2 * k) + 1 = 12 * k + 1 by omega,
        show 6 * (2 * k) + 5 = 12 * k + 5 by omega,
        show 6 * (2 * k + 1) + 1 = 12 * k + 7 by omega,
        show 6 * (2 * k + 1) + 5 = 12 * k + 11 by omega]
      ring
    rw [mul_assoc, hF_tsum, hpair, tsum_congr hpair_eq, ← hScomb_eq]
    ring
  -- Substitute `v = √u / 12` into `hScomb`:
  intro M
  obtain ⟨C, hC⟩ := hScomb (2 * M + 1)
  have hv_top : Tendsto (fun u : ℝ => Real.sqrt u / 12) atTop atTop :=
    (Real.tendsto_sqrt_atTop).atTop_div_const (by norm_num)
  refine ⟨max C 0 * (12 : ℝ) ^ (2 * M + 1) / 2, ?_⟩
  filter_upwards [hv_top.eventually hC, eventually_gt_atTop (0 : ℝ)] with u hCu hu
  rw [hpt hu]
  have hsq_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hsq_sq : (Real.sqrt u : ℂ) ^ 2 = (u : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hu.le]
  have hsum_convert :
      ∑ k ∈ Finset.range M, PowerSeries.coeff k fishburnEulerSeries * ((u : ℂ)⁻¹ ^ k) =
        -((Real.sqrt u : ℂ) / 2) *
          ∑ r ∈ Finset.range (2 * M + 1),
            PowerSeries.coeff r Ecomb * (((Real.sqrt u / 12 : ℝ) : ℂ)⁻¹ ^ r) := by
    have heven0 : ∀ j : ℕ, PowerSeries.coeff (2 * j) Ecomb = 0 := fun j => by
      simp only [Ecomb, map_add, map_sub, emSeriesShift, PowerSeries.coeff_mk, emTermShift,
        hGauss_iteratedDeriv_even j, mul_zero, sub_self, add_zero]
    have hsplit_even : ∀ K : ℕ,
        ∑ r ∈ Finset.range (2 * K),
            PowerSeries.coeff r Ecomb * (((Real.sqrt u / 12 : ℝ) : ℂ)⁻¹ ^ r) =
          ∑ k ∈ Finset.range K,
            PowerSeries.coeff (2 * k + 1) Ecomb * (((Real.sqrt u / 12 : ℝ) : ℂ)⁻¹ ^ (2 * k + 1)) := by
      intro K
      induction K with
      | zero => simp
      | succ m ihm =>
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
          heven0 m, zero_mul, add_zero, ihm, Finset.sum_range_succ]
    have hsplit_eo : ∑ r ∈ Finset.range (2 * M + 1),
          PowerSeries.coeff r Ecomb * (((Real.sqrt u / 12 : ℝ) : ℂ)⁻¹ ^ r) =
        ∑ k ∈ Finset.range M,
          PowerSeries.coeff (2 * k + 1) Ecomb * (((Real.sqrt u / 12 : ℝ) : ℂ)⁻¹ ^ (2 * k + 1)) := by
      rw [Finset.sum_range_succ, heven0 M, zero_mul, add_zero, hsplit_even M]
    rw [hsplit_eo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcoeff_k : PowerSeries.coeff k fishburnEulerSeries = torusKnotCoeff 2 3 k / (k.factorial : ℂ) := by
      simp [fishburnEulerSeries, torusKnotEulerSeries]
    rw [hcoeff_k, ← bernoulli_fishburn_coeff_eq k]
    have hE_odd : PowerSeries.coeff (2 * k + 1) Ecomb =
        emTermShift ((1 / 12 : ℚ) : ℝ) hGauss (2 * k + 1) -
        emTermShift ((5 / 12 : ℚ) : ℝ) hGauss (2 * k + 1) -
        emTermShift ((7 / 12 : ℚ) : ℝ) hGauss (2 * k + 1) +
        emTermShift ((11 / 12 : ℚ) : ℝ) hGauss (2 * k + 1) := by
      simp [Ecomb, emSeriesShift]
    rw [hE_odd]
    have hinv_pow : (((Real.sqrt u / 12 : ℝ) : ℂ)⁻¹ ^ (2 * k + 1)) =
        (12 : ℂ) ^ (2 * k + 1) * (Real.sqrt u : ℂ)⁻¹ * ((u : ℂ)⁻¹ ^ k) := by
      push_cast
      rw [inv_div, div_pow, pow_succ (Real.sqrt u : ℂ), pow_mul (Real.sqrt u : ℂ), hsq_sq, inv_pow]
      have hsq_ne : (Real.sqrt u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq_pos.ne'
      have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
      field_simp [hsq_ne, hu_ne]
    rw [hinv_pow]
    have hsq_ne : (Real.sqrt u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq_pos.ne'
    field_simp [hsq_ne]
  rw [hsum_convert, ← mul_sub, norm_mul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsq_pos, Complex.norm_ofNat]
  have hCu' : ‖Scomb (Real.sqrt u / 12) -
        ∑ r ∈ Finset.range (2 * M + 1),
          PowerSeries.coeff r Ecomb * (((Real.sqrt u / 12 : ℝ) : ℂ)⁻¹ ^ r)‖ ≤
      max C 0 / (Real.sqrt u / 12) ^ (2 * M + 1) :=
    hCu.trans (div_le_div_of_nonneg_right (le_max_left C 0) (by positivity))
  calc Real.sqrt u / 2 * ‖Scomb (Real.sqrt u / 12) - _‖
      ≤ Real.sqrt u / 2 * (max C 0 / (Real.sqrt u / 12) ^ (2 * M + 1)) :=
        mul_le_mul_of_nonneg_left hCu' (by positivity)
    _ = (max C 0 * (12 : ℝ) ^ (2 * M + 1) / 2) / u ^ M := by
        rw [div_pow, pow_succ (Real.sqrt u), pow_mul (Real.sqrt u), Real.sq_sqrt hu.le]
        field_simp [hsq_pos.ne', hu.ne']

/-- **Zagier's Formal Identity (2001, Theorem 3) — 100% Unconditional**:
`fishburnSeries.subst (1 - exp(-24 t)) = exp(t) * fishburnEulerSeries` in `ℂ[[t]]`. -/
theorem zagier_formal_identity :
    fishburnSeries.subst zagierSubst = PowerSeries.exp ℂ * fishburnEulerSeries := by
  have hRHS_asymp : HasAsympExp (fun u : ℝ => -(1 / 2 : ℂ) * ((qZagierF (Real.exp (-24 / u)) : ℝ) : ℂ))
      (PowerSeries.exp ℂ * fishburnEulerSeries) := by
    have h1 : HasAsympExp (fun u : ℝ => Complex.exp ((1 : ℂ) / (u : ℂ))) (PowerSeries.exp ℂ) := by
      simpa using hasAsympExp_exp_div (1 : ℂ)
    have hmul := h1.mul falseTheta_hasAsympExp
    refine hasAsympExp_congr (Filter.Eventually.of_forall fun u => ?_) hmul
    have hexp : Complex.exp ((1 : ℂ) / (u : ℂ)) * Complex.exp (-(1 : ℂ) / (u : ℂ)) = 1 := by
      rw [← Complex.exp_add, show (1 : ℂ) / (u : ℂ) + -(1 : ℂ) / (u : ℂ) = 0 by ring, Complex.exp_zero]
    linear_combination (-(1 / 2 : ℂ) * ((qZagierF (Real.exp (-24 / u)) : ℝ) : ℂ)) * hexp
  have hdiff_zero : HasAsympExp
      (fun u : ℝ => fishburnQ u - (-(1 / 2 : ℂ) * ((qZagierF (Real.exp (-24 / u)) : ℝ) : ℂ))) 0 := by
    refine HasAsympExp.zero_of_exp_decay (δ := Real.exp (-1) / 48) (by positivity) (A := 1)
      (C := (1 / 2 : ℝ) + Real.exp (1 / 2) / 12) ?_
    filter_upwards [eventually_ge_atTop (24 : ℝ)] with u hu
    have hu_pos : 0 < u := by linarith
    set q := Real.exp (-24 / u)
    have hq0 : 0 < q := Real.exp_pos _
    have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hu_pos)
    have h1q_pos : 0 < 1 - q := sub_pos.mpr hq1
    have h1q_le : 1 - q ≤ 24 / u := by
      simpa [q, neg_div] using one_sub_exp_neg_le (x := 24 / u)
    have h1q_ge : 12 / u ≤ 1 - q := by
      have h := one_sub_exp_neg_ge_half (x := 24 / u) (by positivity) ((div_le_one hu_pos).mpr hu)
      have h2 : (24 / u) / 2 = 12 / u := by ring
      simpa [q, neg_div, h2] using h
    have hq_ge : Real.exp (-1) ≤ q := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_le_neg_iff]; exact (div_le_one hu_pos).mpr hu
    have hquot_ge : (Real.exp (-1) / 24) * u ≤ q / (1 - q) := by
      rw [le_div_iff₀ h1q_pos]
      have hmul : (1 - q) * u ≤ 24 := by
        have := mul_le_mul_of_nonneg_right h1q_le hu_pos.le
        rwa [div_mul_cancel₀ _ hu_pos.ne'] at this
      calc (Real.exp (-1) / 24) * u * (1 - q)
          = Real.exp (-1) * ((1 - q) * u / 24) := by ring
        _ ≤ Real.exp (-1) * (24 / 24) := mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hmul (by norm_num)) (Real.exp_pos _).le
        _ = Real.exp (-1) := by norm_num
        _ ≤ q := hq_ge
    have hquot_le : q / (1 - q) ≤ u / 12 := by
      rw [div_le_div_iff₀ h1q_pos (by norm_num)]
      have hmul : 12 ≤ (1 - q) * u := by
        have := mul_le_mul_of_nonneg_right h1q_ge hu_pos.le
        rwa [div_mul_cancel₀ _ hu_pos.ne'] at this
      nlinarith [hq1.le]
    have heq_sub : fishburnQ u - (-(1 / 2 : ℂ) * ((qZagierF q : ℝ) : ℂ)) =
        (((qZagierG q 1 + (1 / 2) * qZagierF q : ℝ) : ℂ)) := by
      unfold fishburnQ; push_cast; ring
    rw [heq_sub, Complex.norm_real, Real.norm_eq_abs, pow_one]
    refine (zagier_q_approx hq0 hq1).trans ?_
    have hexp1 : Real.exp (-q / (1 - q)) ≤ Real.exp (-(Real.exp (-1) / 48) * u) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      have : 0 ≤ (Real.exp (-1) / 48) * u := by positivity
      linarith
    have hexp2 : Real.exp (1 / 2 - q / (2 * (1 - q))) ≤ Real.exp (1 / 2) * Real.exp (-(Real.exp (-1) / 48) * u) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hdiv2 : q / (2 * (1 - q)) = (q / (1 - q)) / 2 := by field_simp [h1q_pos.ne']
      rw [hdiv2]; linarith
    have hu1 : (1 : ℝ) ≤ u := by linarith
    calc (1 / 2) * Real.exp (-q / (1 - q)) + (q / (1 - q)) * Real.exp (1 / 2 - q / (2 * (1 - q)))
        ≤ (1 / 2) * (u * Real.exp (-(Real.exp (-1) / 48) * u)) +
            (u / 12) * (Real.exp (1 / 2) * Real.exp (-(Real.exp (-1) / 48) * u)) := by
          refine add_le_add ?_ (mul_le_mul hquot_le hexp2 (Real.exp_pos _).le (by positivity))
          have : Real.exp (-q / (1 - q)) ≤ u * Real.exp (-(Real.exp (-1) / 48) * u) :=
            hexp1.trans (le_mul_of_one_le_left (Real.exp_pos _).le hu1)
          linarith
      _ = ((1 / 2 : ℝ) + Real.exp (1 / 2) / 12) * u * Real.exp (-(Real.exp (-1) / 48) * u) := by ring
  have hQ_rhs : HasAsympExp fishburnQ (PowerSeries.exp ℂ * fishburnEulerSeries) := by
    have h := hdiff_zero.add hRHS_asymp
    rw [zero_add] at h
    exact hasAsympExp_congr (Filter.Eventually.of_forall fun u => by ring) h
  exact hasAsympExp_unique fishburnQ_hasAsympExp hQ_rhs

/-- **Flagship Unconditional Resolution of Bostan–Di Vizio–Raschel (AJM §2.2.6)**:
The literal divergent Fishburn ordinary generating function
`fishburnSeries = ∑_{m=0}^∞ ∏_{j=1}^m (1 - (1 - x)^j) ∈ ℂ[[x]]`
is **unconditionally differentially transcendental over `ℂ(x)`** (satisfies no nonzero algebraic
differential equation over `ℂ[x]` in `PowerSeries ℂ`). -/
theorem fishburnSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates fishburnSeries) :=
  fishburnSeries_algebraicIndependent_of_zagier_identity zagier_formal_identity

end
end PakPrimes.FishburnTorusKnots
