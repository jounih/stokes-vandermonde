module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.MockModularWeightOne
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.Trigonometric

/-! # Ramanujan Mock Theta Mordell Integrals & Zagier's Hurwitz Class-Number Shadow

End-to-end Tier-1 Lean 4 formalization of:
1. **General Bounded-Kernel Laplace & Mordell D-Transcendence Engine** (`laplaceTransform`,
   `laplaceTransform_hasAsympExp`, `mordellIntegral`, `mordellIntegral_eq_half_laplace`,
   `mordellIntegral_no_rat_ade`):
   Connects any Borel kernel `φ` satisfying `HigherOrderBorelData` (along any ray `θ₀`) that is
   analytic at `0`, continuous and uniformly bounded on `[0, ∞)` to all-orders Watson's Lemma
   (`HasAsympExp` for every `iteratedDeriv j`) and unconditional differential transcendence over
   `ℂ(u)` for both the Laplace transform `∫_0^∞ e^{-u t} φ(t) dt` and the Mordell integral
   `∫_0^∞ e^{-u x^2} x φ(x^2) dx`.
2. **Entire Even-Cosh Engine (`coshSqrt`)**:
   Constructs `coshSqrt z = ∑' n, z^n / (2n)!` satisfying `coshSqrt (w^2) = Complex.cosh w`,
   characterizes all zeros of `coshSqrt`, `2 * coshSqrt - 1`, and `2 * coshSqrt + 1` strictly along
   the negative real ray `θ₀ = π`, proves nonzero simple-pole residues, and establishes flanking-ray
   `ExpType` bounds on `e^{i (π ± π/3)}`.
3. **Three Unconditional Mock Theta & Mordell D-Transcendence Witnesses**:
   - **Classical Zwegers–Mordell integral** `∫_0^∞ e^{-u x^2} (x / cosh x) dx` (`mordellCosh_no_rat_ade`),
   - **Ramanujan's 3rd-order mock theta `ω(q)` Mordell integral**
     `∫_0^∞ e^{-u x^2} (x cosh(x/2) / cosh(3x/2)) dx` (`mockThetaOmega_no_rat_ade`),
   - **Ramanujan's 3rd-order mock theta `f(q)` Mordell integral**
     `∫_0^∞ e^{-u x^2} (x sinh(x) / sinh(3x/2)) dx` (`mockThetaF_no_rat_ade`).
4. **Zagier's Hurwitz Class-Number Shadow `ϑ₃(τ) - 1 = 2 ∑_{k ≥ 1} q^{k²}`**:
   Instantiates `HigherOrderBorelData` and proves unconditional differential transcendence over
   `ℂ(u)` for the split Eichler integral of `ϑ₃(τ) - 1` (`hurwitzThetaShadow_no_rat_ade`).
5. **Modular D-Algebraic Controls (Modular vs. Mock Dichotomy)**:
   Proves that `u ↦ e^{-u}` and the nonlinear geometric/theta-mode kernel `u ↦ (1 - e^{-u})⁻¹`
   ARE differentially algebraic over `ℂ` and `ℂ(u)` (`expNeg_is_d_algebraic`,
   `geometricKernel_is_d_algebraic`).
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.MockThetaAndHurwitz

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
open PakPrimes.MockModularWeightOne
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. General Bounded-Kernel Laplace Watson's Lemma & Mordell Integral Engine -/

/-- Exact Laplace transform `L_φ(u) = ∫_0^∞ e^{-u ξ} φ(ξ) dξ` for `u > 0`. -/
@[expose] def laplaceTransform (φ : ℂ → ℂ) (u : ℝ) : ℂ :=
  ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ)

/-- Exact Mordell-type Gaussian integral `M_φ(u) = ∫_0^∞ e^{-u x^2} x φ(x^2) dx`. -/
@[expose] def mordellIntegral (φ : ℂ → ℂ) (u : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) * φ ((x : ℂ) ^ 2)

private lemma integrableOn_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (S : Set ℝ)
    (h : ∀ k ∈ s, IntegrableOn (f k) S volume) :
    IntegrableOn (fun ξ => ∑ k ∈ s, f k ξ) S volume := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

private lemma integral_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (S : Set ℝ)
    (h : ∀ k ∈ s, IntegrableOn (f k) S volume) :
    ∫ ξ in S, (∑ k ∈ s, f k ξ) = ∑ k ∈ s, ∫ ξ in S, f k ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := integrableOn_finset_sum' s f S fun k hk => h k (Finset.mem_insert_of_mem hk)
    rw [integral_add h1 h2, ih fun k hk => h k (Finset.mem_insert_of_mem hk)]

private lemma pow_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (m : ℕ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ξ ^ m * Real.exp (-a * ξ) ≤ (m.factorial : ℝ) / a ^ m := by
  have hterm : (a * ξ) ^ m / (m.factorial : ℝ) ≤ Real.exp (a * ξ) :=
    Real.pow_div_factorial_le_exp (a * ξ) (mul_nonneg ha.le hξ) m
  have hpos_fac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hpos_pow : 0 < a ^ m := pow_pos ha m
  have hpos_exp : 0 < Real.exp (a * ξ) := Real.exp_pos _
  rw [mul_pow, div_le_iff₀ hpos_fac] at hterm
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hpos_exp hpos_pow]
  nlinarith

private lemma integrableOn_pow_mul_exp_neg_Ioi (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun ξ : ℝ => ξ ^ m * Real.exp (-a * ξ)) (Set.Ioi (0 : ℝ)) volume := by
  have h2 : IntegrableOn (fun ξ : ℝ => ((m.factorial : ℝ) / (a / 2) ^ m) * Real.exp (-(a / 2) * ξ))
      (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_exp_mul_Ioi (by linarith : -(a / 2) < 0) 0).const_mul _
  refine h2.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hξ0 : 0 ≤ ξ := le_of_lt hξ
  rw [Real.norm_of_nonneg (by positivity)]
  have hsplit : Real.exp (-a * ξ) = Real.exp (-(a / 2) * ξ) * Real.exp (-(a / 2) * ξ) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_mul_exp_neg_le (by linarith) m hξ0) (Real.exp_pos _).le

private lemma tendsto_pow_mul_exp_neg_atTop (m : ℕ) {u : ℝ} (hu : 0 < u) :
    Filter.Tendsto (fun ξ : ℝ => ξ ^ m * Real.exp (-u * ξ)) Filter.atTop (𝓝 0) := by
  have hle : ∀ᶠ ξ : ℝ in Filter.atTop, 0 ≤ ξ ^ m * Real.exp (-u * ξ) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with ξ hξ; positivity
  have hge : ∀ᶠ ξ : ℝ in Filter.atTop,
      ξ ^ m * Real.exp (-u * ξ) ≤ ((m.factorial : ℝ) / (u / 2) ^ m) * Real.exp (-(u / 2) * ξ) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with ξ hξ
    have hsplit : Real.exp (-u * ξ) = Real.exp (-(u / 2) * ξ) * Real.exp (-(u / 2) * ξ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (pow_mul_exp_neg_le (by linarith) m hξ) (Real.exp_pos _).le
  have htop : Filter.Tendsto (fun ξ : ℝ => ((m.factorial : ℝ) / (u / 2) ^ m) * Real.exp (-(u / 2) * ξ))
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun ξ : ℝ => -(u / 2) * ξ) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul ((m.factorial : ℝ) / (u / 2) ^ m)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop hle hge

private lemma integral_pow_mul_exp_neg_Ioi (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ ξ in Set.Ioi (0 : ℝ), ξ ^ m * Real.exp (-u * ξ) = (m.factorial : ℝ) / u ^ (m + 1) := by
  induction m with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one]
    rw [integral_exp_mul_Ioi (a := -u) (by linarith) 0]
    simp [div_eq_mul_inv]
  | succ m ih =>
    let F : ℝ → ℝ := fun ξ => -(ξ ^ (m + 1) / u) * Real.exp (-u * ξ)
    let F' : ℝ → ℝ := fun ξ =>
      ξ ^ (m + 1) * Real.exp (-u * ξ) - (((m + 1 : ℕ) : ℝ) / u) * (ξ ^ m * Real.exp (-u * ξ))
    have hderiv : ∀ ξ ∈ Set.Ici (0 : ℝ), HasDerivAt F (F' ξ) ξ := fun ξ _ => by
      have h1 : HasDerivAt (fun t : ℝ => -(t ^ (m + 1) / u))
          (-(((m + 1 : ℕ) : ℝ) * ξ ^ m / u)) ξ :=
        ((hasDerivAt_pow (m + 1) ξ).div_const u).neg
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-u * t))
          (Real.exp (-u * ξ) * (-u)) ξ := by
        simpa using ((hasDerivAt_id ξ).const_mul (-u)).exp
      have hmul := h1.mul h2
      convert hmul using 1
      dsimp only [F']
      field_simp [hu.ne']
      ring
    have hF_lim : Filter.Tendsto F Filter.atTop (𝓝 0) := by
      have h := (tendsto_pow_mul_exp_neg_atTop (m + 1) hu).const_mul (-(1 / u))
      simpa only [mul_zero] using h.congr fun ξ => by dsimp only [F]; ring
    have hF'_int : IntegrableOn F' (Set.Ioi (0 : ℝ)) :=
      (integrableOn_pow_mul_exp_neg_Ioi (m + 1) hu).sub
        ((integrableOn_pow_mul_exp_neg_Ioi m hu).const_mul _)
    have h0 := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hF'_int hF_lim
    have hF0 : F 0 = 0 := by simp [F]
    rw [hF0, sub_zero] at h0
    have hsub : ∫ ξ in Set.Ioi (0 : ℝ), F' ξ =
        (∫ ξ in Set.Ioi (0 : ℝ), ξ ^ (m + 1) * Real.exp (-u * ξ)) -
          (((m + 1 : ℕ) : ℝ) / u) * ∫ ξ in Set.Ioi (0 : ℝ), ξ ^ m * Real.exp (-u * ξ) := by
      dsimp only [F']
      rw [integral_sub (integrableOn_pow_mul_exp_neg_Ioi (m + 1) hu)
        ((integrableOn_pow_mul_exp_neg_Ioi m hu).const_mul _), integral_const_mul]
    rw [hsub] at h0
    have heq : ∫ ξ in Set.Ioi (0 : ℝ), ξ ^ (m + 1) * Real.exp (-u * ξ) =
        (((m + 1 : ℕ) : ℝ) / u) * ∫ ξ in Set.Ioi (0 : ℝ), ξ ^ m * Real.exp (-u * ξ) :=
      sub_eq_zero.mp h0
    rw [heq, ih, Nat.factorial_succ]
    push_cast
    rw [pow_succ, pow_succ]
    field_simp [hu.ne']
    ring

private lemma integral_pow_mul_cexp_neg_Ioi (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ ξ in Set.Ioi (0 : ℝ), (ξ : ℂ) ^ m * Complex.exp (-(u : ℂ) * (ξ : ℂ)) =
      (m.factorial : ℂ) / (u : ℂ) ^ (m + 1) := by
  have hcast : (fun ξ : ℝ => (ξ : ℂ) ^ m * Complex.exp (-(u : ℂ) * (ξ : ℂ))) =
      fun ξ : ℝ => ((ξ ^ m * Real.exp (-u * ξ) : ℝ) : ℂ) := by
    funext ξ
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
    congr 2; push_cast; ring
  rw [hcast, integral_complex_ofReal, integral_pow_mul_exp_neg_Ioi m hu]
  push_cast; rfl

/-- `j`-th differentiated Laplace integral `∫_0^∞ (-ξ)^j e^{-u ξ} φ(ξ) dξ`. -/
private def laplaceDerivGen (φ : ℂ → ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  ∫ ξ in Set.Ioi (0 : ℝ), (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ)

private lemma laplaceDerivGen_integrable {φ : ℂ → ℂ} {M : ℝ}
    (hcont : ContinuousOn (fun ξ : ℝ => φ (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖φ (ξ : ℂ)‖ ≤ M)
    (j : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ))
      (Set.Ioi (0 : ℝ)) volume := by
  have hdom : IntegrableOn (fun ξ : ℝ => M * (ξ ^ j * Real.exp (-u * ξ)))
      (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_pow_mul_exp_neg_Ioi j hu).const_mul M
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((by fun_prop : ContinuousOn (fun ξ : ℝ => (-(ξ : ℂ)) ^ j *
        Complex.exp (-(u : ℂ) * (ξ : ℂ))) (Set.Ioi 0)).mul
      (hcont.mono Set.Ioi_subset_Ici_self))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ξ hξ => ?_)
    have hξ0 : 0 ≤ ξ := (Set.mem_Ioi.mp hξ).le
    rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hξ0,
      Complex.norm_exp]
    have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
    rw [hre]
    calc ξ ^ j * Real.exp (-u * ξ) * ‖φ (ξ : ℂ)‖
        ≤ ξ ^ j * Real.exp (-u * ξ) * M :=
          mul_le_mul_of_nonneg_left (hbd ξ hξ0) (by positivity)
      _ = M * (ξ ^ j * Real.exp (-u * ξ)) := by ring

private lemma laplaceDerivGen_hasDerivAt {φ : ℂ → ℂ} {M : ℝ}
    (hcont : ContinuousOn (fun ξ : ℝ => φ (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖φ (ξ : ℂ)‖ ≤ M)
    (j : ℕ) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    HasDerivAt (laplaceDerivGen φ j) (laplaceDerivGen φ (j + 1) u₀) u₀ := by
  let F : ℝ → ℝ → ℂ := fun u ξ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ)
  let F' : ℝ → ℝ → ℂ := fun u ξ =>
    (-(ξ : ℂ)) ^ (j + 1) * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ)
  let bound : ℝ → ℝ := fun ξ => M * (ξ ^ (j + 1) * Real.exp (-(u₀ / 2) * ξ))
  have hs : Set.Ioi (u₀ / 2) ∈ 𝓝 u₀ := Ioi_mem_nhds (by linarith)
  have hF_meas : ∀ᶠ u in 𝓝 u₀,
      AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall fun u =>
      (((by fun_prop : ContinuousOn (fun ξ : ℝ => (-(ξ : ℂ)) ^ j *
          Complex.exp (-(u : ℂ) * (ξ : ℂ))) (Set.Ioi 0)).mul
        (hcont.mono Set.Ioi_subset_Ici_self))).aestronglyMeasurable measurableSet_Ioi
  have hF_int : Integrable (F u₀) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    laplaceDerivGen_integrable hcont hbd j hu₀
  have hF'_meas : AEStronglyMeasurable (F' u₀) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (laplaceDerivGen_integrable hcont hbd (j + 1) hu₀).aestronglyMeasurable
  have h_bound : ∀ᵐ ξ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ u ∈ Set.Ioi (u₀ / 2), ‖F' u ξ‖ ≤ bound ξ := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ξ hξ u hu => ?_)
    have hξ0 : 0 ≤ ξ := (Set.mem_Ioi.mp hξ).le
    have hu_gt : u₀ / 2 < u := Set.mem_Ioi.mp hu
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hξ0,
      Complex.norm_exp]
    have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
    rw [hre]
    have hexp : Real.exp (-u * ξ) ≤ Real.exp (-(u₀ / 2) * ξ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hφ := hbd ξ hξ0
    calc ξ ^ (j + 1) * Real.exp (-u * ξ) * ‖φ (ξ : ℂ)‖
        ≤ ξ ^ (j + 1) * Real.exp (-(u₀ / 2) * ξ) * M := by gcongr
      _ = M * (ξ ^ (j + 1) * Real.exp (-(u₀ / 2) * ξ)) := by ring
  have h_int_bound : Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrableOn_pow_mul_exp_neg_Ioi (j + 1) (by positivity)).const_mul M
  have h_diff : ∀ᵐ ξ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ u ∈ Set.Ioi (u₀ / 2), HasDerivAt (F · ξ) (F' u ξ) u := by
    refine Filter.Eventually.of_forall fun ξ u _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * (ξ : ℂ)))
        (Complex.exp (-(u : ℂ) * (ξ : ℂ)) * (-(ξ : ℂ))) u := by
      have ha : HasDerivAt (fun t : ℝ => -(t : ℂ) * (ξ : ℂ)) (-(ξ : ℂ)) u := by
        simpa using (((hasDerivAt_id u).ofReal_comp).neg).mul_const (ξ : ℂ)
      exact ha.cexp
    have h2 := (h1.const_mul ((-(ξ : ℂ)) ^ j)).mul_const (φ (ξ : ℂ))
    convert h2 using 1
    dsimp only [F']
    rw [pow_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound h_int_bound h_diff).2

private lemma iteratedDeriv_laplaceTransform_eq {φ : ℂ → ℂ} {M : ℝ}
    (hcont : ContinuousOn (fun ξ : ℝ => φ (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖φ (ξ : ℂ)‖ ≤ M)
    (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (laplaceTransform φ) u = laplaceDerivGen φ j u := by
  induction j generalizing u with
  | zero => simp [laplaceDerivGen, laplaceTransform]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (laplaceTransform φ) =ᶠ[𝓝 u] laplaceDerivGen φ j :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) fun x hx => ih hx
    rw [hev.deriv_eq, (laplaceDerivGen_hasDerivAt hcont hbd j hu).deriv]

private lemma coeff_iter_d_u_formalSeries (φ : ℂ → ℂ) (j n : ℕ) :
    PowerSeries.coeff n (d_u^[j] (formalSeries φ)) =
      if n < j + 1 then 0
      else (-1 : ℂ) ^ j * (((n - 1).factorial : ℂ) / ((n - j - 1).factorial : ℂ)) *
        iteratedDeriv (n - j - 1) φ 0 := by
  induction j generalizing n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, zero_add, pow_zero, one_mul, Nat.sub_zero]
    rcases n with _ | k
    · simp [formalSeries]
    · have hk : ¬ (k + 1 < 1) := by omega
      have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      simp [hk, formalSeries, div_self hfac]
  | succ j ih =>
    rw [Function.iterate_succ_apply', d_u, map_neg]
    rcases n with _ | _ | k
    · simp [PowerSeries.coeff_mul, PowerSeries.coeff_X_pow]
    · simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, PowerSeries.coeff_X_pow]
    · have hcoeff : PowerSeries.coeff (k + 2) (PowerSeries.X ^ 2 *
          PowerSeries.derivative (d_u^[j] (formalSeries φ))) =
          ((k + 1 : ℕ) : ℂ) * PowerSeries.coeff (k + 1) (d_u^[j] (formalSeries φ)) := by
        rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_derivative]
        push_cast; ring
      rw [hcoeff, ih (k + 1)]
      by_cases hk : k + 2 < j + 1 + 1
      · have hk' : k + 1 < j + 1 := by omega
        simp [hk, hk']
      · have hk' : ¬ (k + 1 < j + 1) := by omega
        simp only [hk, hk', ↓reduceIte]
        have hsub1 : k + 2 - 1 = k + 1 := by omega
        have hsub2 : k + 1 - 1 = k := by omega
        have hsub3 : k + 2 - (j + 1) - 1 = k + 1 - j - 1 := by omega
        rw [hsub1, hsub2, hsub3, Nat.factorial_succ k, pow_succ]
        push_cast; ring

private lemma bounded_analytic_taylor_global_bound {φ : ℂ → ℂ} {M : ℝ}
    (hana : AnalyticAt ℂ φ 0) (hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖φ (ξ : ℂ)‖ ≤ M) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 ≤ ξ →
      ‖φ (ξ : ℂ) - ∑ k ∈ Finset.range K,
        ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0‖ ≤ C * ξ ^ K := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hbd 0 le_rfl)
  obtain ⟨Q, hQa, hQeq⟩ := hana.exists_eventuallyEq_sum_add_pow_mul K
  have hQbd : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Q z‖ ≤ ‖Q 0‖ + 1 := by
    have hcont : Filter.Tendsto (fun z => ‖Q z‖) (𝓝 0) (𝓝 ‖Q 0‖) :=
      (hQa.continuousAt.norm).tendsto
    exact hcont.eventually (Iic_mem_nhds (by linarith))
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (hQeq.and hQbd)
  let S_tail : ℝ := M / δ ^ K +
    ∑ k ∈ Finset.range K, ‖iteratedDeriv k φ 0‖ / ((k.factorial : ℝ) * δ ^ (K - k))
  have hS_tail : 0 ≤ S_tail := add_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => by positivity)
  refine ⟨max (‖Q 0‖ + 1) S_tail, le_trans (by positivity) (le_max_left _ _), fun ξ hξ => ?_⟩
  by_cases hlt : ξ < δ
  · have hmem : dist (ξ : ℂ) 0 < δ := by
      simpa [dist_eq_norm, Complex.norm_real, Real.norm_of_nonneg hξ] using hlt
    obtain ⟨heq, hq⟩ := hδ hmem
    have hsub : φ (ξ : ℂ) -
        ∑ k ∈ Finset.range K,
          ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0 =
        (ξ : ℂ) ^ K * Q (ξ : ℂ) := by
      rw [heq]
      simp only [smul_eq_mul, add_sub_cancel_left]
    rw [hsub, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hξ]
    calc ξ ^ K * ‖Q (ξ : ℂ)‖
        ≤ ξ ^ K * (‖Q 0‖ + 1) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (‖Q 0‖ + 1) * ξ ^ K := by ring
      _ ≤ max (‖Q 0‖ + 1) S_tail * ξ ^ K :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push Not at hlt
    have h1 : ‖φ (ξ : ℂ)‖ ≤ (M / δ ^ K) * ξ ^ K := by
      have hratio : (1 : ℝ) ≤ ξ ^ K / δ ^ K := by
        rw [one_le_div (pow_pos hδ_pos K)]
        exact pow_le_pow_left₀ hδ_pos.le hlt K
      calc ‖φ (ξ : ℂ)‖ ≤ M := hbd ξ hξ
        _ = M * 1 := by ring
        _ ≤ M * (ξ ^ K / δ ^ K) := mul_le_mul_of_nonneg_left hratio hM0
        _ = (M / δ ^ K) * ξ ^ K := by ring
    have h2 : ‖∑ k ∈ Finset.range K,
          ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0‖ ≤
        (∑ k ∈ Finset.range K,
          ‖iteratedDeriv k φ 0‖ / ((k.factorial : ℝ) * δ ^ (K - k))) * ξ ^ K := by
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      have hk_lt : k < K := Finset.mem_range.mp hk
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hξ,
        Complex.norm_natCast]
      have hpow : ξ ^ k ≤ ξ ^ K / δ ^ (K - k) := by
        rw [le_div_iff₀ (pow_pos hδ_pos _)]
        calc ξ ^ k * δ ^ (K - k) ≤ ξ ^ k * ξ ^ (K - k) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ_pos.le hlt _) (by positivity)
          _ = ξ ^ (k + (K - k)) := (pow_add _ _ _).symm
          _ = ξ ^ K := by rw [Nat.add_sub_of_le hk_lt.le]
      calc ξ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k φ 0‖
          ≤ (ξ ^ K / δ ^ (K - k)) / (k.factorial : ℝ) * ‖iteratedDeriv k φ 0‖ := by gcongr
        _ = ‖iteratedDeriv k φ 0‖ / ((k.factorial : ℝ) * δ ^ (K - k)) * ξ ^ K := by ring
    calc ‖φ (ξ : ℂ) -
            ∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0‖
        ≤ ‖φ (ξ : ℂ)‖ +
            ‖∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0‖ :=
          norm_sub_le _ _
      _ ≤ (M / δ ^ K) * ξ ^ K +
            (∑ k ∈ Finset.range K,
              ‖iteratedDeriv k φ 0‖ / ((k.factorial : ℝ) * δ ^ (K - k))) * ξ ^ K :=
          add_le_add h1 h2
      _ = S_tail * ξ ^ K := by dsimp only [S_tail]; ring
      _ ≤ max (‖Q 0‖ + 1) S_tail * ξ ^ K :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **All-Orders Watson's Lemma for Bounded Analytic Borel Kernels**:
If `φ` is analytic at `0`, continuous on `[0, ∞)`, and uniformly bounded on `[0, ∞)`, then for
every derivative order `j`, `iteratedDeriv j (laplaceTransform φ)` has the exact all-orders
`1/u` asymptotic expansion `d_u^[j] (formalSeries φ)`. -/
theorem laplaceTransform_hasAsympExp {φ : ℂ → ℂ} {M : ℝ}
    (hana : AnalyticAt ℂ φ 0)
    (hcont : ContinuousOn (fun ξ : ℝ => φ (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖φ (ξ : ℂ)‖ ≤ M) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (laplaceTransform φ)) (d_u^[j] (formalSeries φ)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hbd 0 le_rfl)
  intro N
  by_cases hNj : N ≤ j + 1
  · refine ⟨M * (j.factorial : ℝ), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u hu
    have hu_pos : 0 < u := by linarith
    have hsum0 : ∑ k ∈ Finset.range N,
        PowerSeries.coeff k (d_u^[j] (formalSeries φ)) * ((u : ℂ)⁻¹ ^ k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkj : k < j + 1 := lt_of_lt_of_le (Finset.mem_range.mp hk) hNj
      rw [coeff_iter_d_u_formalSeries, ite_eq_left_iff.mpr (fun h => absurd hkj h), zero_mul]
    rw [hsum0, sub_zero, iteratedDeriv_laplaceTransform_eq hcont hbd j hu_pos, laplaceDerivGen]
    have hdom : IntegrableOn (fun ξ : ℝ => M * (ξ ^ j * Real.exp (-u * ξ)))
        (Set.Ioi (0 : ℝ)) volume :=
      (integrableOn_pow_mul_exp_neg_Ioi j hu_pos).const_mul M
    have hnorm : ‖∫ ξ in Set.Ioi (0 : ℝ),
        (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ)‖ ≤
        ∫ ξ in Set.Ioi (0 : ℝ), M * (ξ ^ j * Real.exp (-u * ξ)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on (laplaceDerivGen_integrable hcont hbd j hu_pos).norm hdom
        measurableSet_Ioi fun ξ hξ => ?_
      have hξ0 : 0 ≤ ξ := le_of_lt hξ
      rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hξ0,
        Complex.norm_exp]
      have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
      rw [hre]
      calc ξ ^ j * Real.exp (-u * ξ) * ‖φ (ξ : ℂ)‖
          ≤ ξ ^ j * Real.exp (-u * ξ) * M :=
            mul_le_mul_of_nonneg_left (hbd ξ hξ0) (by positivity)
        _ = M * (ξ ^ j * Real.exp (-u * ξ)) := by ring
    rw [integral_const_mul, integral_pow_mul_exp_neg_Ioi j hu_pos] at hnorm
    have hupow : u ^ N ≤ u ^ (j + 1) := pow_le_pow_right₀ (by linarith) hNj
    refine hnorm.trans ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hupow
  · push Not at hNj
    let K : ℕ := N - j - 1
    obtain ⟨C, hC0, hC⟩ := bounded_analytic_taylor_global_bound hana hbd K
    refine ⟨C * ((j + K).factorial : ℝ), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u hu1
    have hu : 0 < u := by linarith
    rw [iteratedDeriv_laplaceTransform_eq hcont hbd j hu, laplaceDerivGen]
    let T : ℝ → ℂ := fun ξ =>
      ∑ k ∈ Finset.range K,
        (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
          (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0)
    have hT_int_each : ∀ k ∈ Finset.range K,
        IntegrableOn (fun ξ : ℝ =>
          (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0))
          (Set.Ioi (0 : ℝ)) volume := by
      intro k _
      have hdom : IntegrableOn (fun ξ : ℝ =>
          (‖iteratedDeriv k φ 0‖ / (k.factorial : ℝ)) * (ξ ^ (j + k) * Real.exp (-u * ξ)))
          (Set.Ioi (0 : ℝ)) volume :=
        (integrableOn_pow_mul_exp_neg_Ioi (j + k) hu).const_mul _
      refine hdom.mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
      have hξ0 : 0 ≤ ξ := le_of_lt hξ
      rw [norm_mul, norm_mul, norm_mul, norm_div, norm_pow, norm_pow, norm_neg,
        Complex.norm_real, Real.norm_of_nonneg hξ0, Complex.norm_exp, Complex.norm_natCast]
      have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
      rw [hre, pow_add]
      exact le_of_eq (by ring)
    have hsum_eq : ∑ n ∈ Finset.range N,
        PowerSeries.coeff n (d_u^[j] (formalSeries φ)) * ((u : ℂ)⁻¹ ^ n) =
        ∫ ξ in Set.Ioi (0 : ℝ), T ξ := by
      have hsplit : ∑ n ∈ Finset.range N,
          PowerSeries.coeff n (d_u^[j] (formalSeries φ)) * ((u : ℂ)⁻¹ ^ n) =
          ∑ k ∈ Finset.range K,
            PowerSeries.coeff (k + j + 1) (d_u^[j] (formalSeries φ)) *
              ((u : ℂ)⁻¹ ^ (k + j + 1)) := by
        have hrange : N = (j + 1) + K := by omega
        rw [hrange, Finset.sum_range_add]
        have hzero : ∑ n ∈ Finset.range (j + 1),
            PowerSeries.coeff n (d_u^[j] (formalSeries φ)) * ((u : ℂ)⁻¹ ^ n) = 0 := by
          refine Finset.sum_eq_zero fun n hn => ?_
          rw [coeff_iter_d_u_formalSeries,
            ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_range.mp hn) h), zero_mul]
        rw [hzero, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hidx : j + 1 + k = k + j + 1 := by omega
        rw [hidx]
      rw [hsplit]
      rw [show (∫ ξ in Set.Ioi (0 : ℝ), T ξ) =
          ∑ k ∈ Finset.range K, ∫ ξ in Set.Ioi (0 : ℝ),
            (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
              (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0) from
        integral_finset_sum' (Finset.range K) _ (Set.Ioi 0) hT_int_each]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hnot : ¬ (k + j + 1 < j + 1) := by omega
      rw [coeff_iter_d_u_formalSeries, ite_eq_right_iff.mpr (fun h => absurd h hnot)]
      have hs1 : k + j + 1 - 1 = k + j := by omega
      have hs2 : k + j + 1 - j - 1 = k := by omega
      rw [hs1, hs2]
      have hrew : (fun ξ : ℝ =>
          (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0)) =
          fun ξ : ℝ => ((-1 : ℂ) ^ j * (iteratedDeriv k φ 0 / (k.factorial : ℂ))) *
            ((ξ : ℂ) ^ (k + j) * Complex.exp (-(u : ℂ) * (ξ : ℂ))) := by
        ext ξ
        rw [show (-(ξ : ℂ)) ^ j = (-1 : ℂ) ^ j * (ξ : ℂ) ^ j by
          rw [← mul_pow]; ring_nf]
        rw [pow_add]
        ring
      rw [hrew, integral_const_mul, integral_pow_mul_cexp_neg_Ioi (k + j) hu]
      have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
      have hfac_ne : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      rw [inv_pow]
      field_simp [hu_ne, hfac_ne]
    rw [hsum_eq]
    have hT_int : IntegrableOn T (Set.Ioi (0 : ℝ)) volume :=
      integrableOn_finset_sum' (Finset.range K) _ (Set.Ioi 0) hT_int_each
    rw [← integral_sub (laplaceDerivGen_integrable hcont hbd j hu) hT_int]
    have hdom : IntegrableOn (fun ξ : ℝ => C * (ξ ^ (j + K) * Real.exp (-u * ξ)))
        (Set.Ioi (0 : ℝ)) volume :=
      (integrableOn_pow_mul_exp_neg_Ioi (j + K) hu).const_mul C
    have hbd_int : ‖∫ ξ in Set.Ioi (0 : ℝ),
        ((-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ) - T ξ)‖ ≤
        ∫ ξ in Set.Ioi (0 : ℝ), C * (ξ ^ (j + K) * Real.exp (-u * ξ)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on ((laplaceDerivGen_integrable hcont hbd j hu).sub hT_int).norm hdom
        measurableSet_Ioi fun ξ hξ => ?_
      have hξ0 : 0 ≤ ξ := le_of_lt hξ
      have hfactor : (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * φ (ξ : ℂ) - T ξ =
          (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (φ (ξ : ℂ) - ∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0) := by
        dsimp only [T]
        rw [← Finset.mul_sum, mul_sub]
      rw [hfactor, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg hξ0, Complex.norm_exp]
      have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
      rw [hre]
      calc ξ ^ j * Real.exp (-u * ξ) *
            ‖φ (ξ : ℂ) - ∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k φ 0‖
          ≤ ξ ^ j * Real.exp (-u * ξ) * (C * ξ ^ K) :=
            mul_le_mul_of_nonneg_left (hC ξ hξ0) (by positivity)
        _ = C * (ξ ^ (j + K) * Real.exp (-u * ξ)) := by rw [pow_add]; ring
    refine hbd_int.trans_eq ?_
    rw [integral_const_mul, integral_pow_mul_exp_neg_Ioi (j + K) hu, ← mul_div_assoc]
    congr 2
    have : j + K + 1 = N := by omega
    rw [this]

/-- **General Bounded-Kernel Laplace D-Transcendence over `ℂ(u)`**:
Any Borel kernel `φ` with `HigherOrderBorelData` that is analytic at `0`, continuous and uniformly
bounded on `[0, ∞)` has a Laplace transform `laplaceTransform φ` satisfying NO nonzero rational
differential equation over `ℂ(u)`. -/
theorem laplaceTransform_no_rat_ade
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ} {M : ℝ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    (hana : AnalyticAt ℂ φ 0)
    (hcont : ContinuousOn (fun ξ : ℝ => φ (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖φ (ξ : ℂ)‖ ≤ M)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (laplaceTransform φ) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  no_rat_ade_of_higher_order_borel h (laplaceTransform_hasAsympExp hana hcont hbd) P hP

/-- Scaling `HigherOrderBorelData` by a nonzero complex constant `c ≠ 0`. -/
def HigherOrderBorelData.const_mul
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp) (c : ℂ) (hc : c ≠ 0) :
    HigherOrderBorelData (fun z => c * φ z) θ₀ ω ord (fun m s => c * pp m s) where
  α₀ := h.α₀
  θ := h.θ
  ε := h.ε
  hθ_pos := h.hθ_pos
  hθ_lt := h.hθ_lt
  hα₀_lt := h.hα₀_lt
  hε_pos := h.hε_pos
  ω_pos := h.ω_pos
  ω_mono := h.ω_mono
  ord_pos := h.ord_pos
  pp_lead_ne_zero := fun m => mul_ne_zero hc (h.pp_lead_ne_zero m)
  analyticOn := fun z hz => analyticAt_const.mul (h.analyticOn z hz)
  pole_principalPart := fun m => by
    obtain ⟨L, hL⟩ := h.pole_principalPart m
    refine ⟨c * L, ?_⟩
    have hrew : (fun z : ℂ => c * φ z - ∑ s ∈ Finset.Icc 1 (ord m),
        c * pp m s / (z - Complex.exp (I * (θ₀ : ℂ)) * (ω m : ℂ)) ^ s) =
        fun z : ℂ => c * (φ z - ∑ s ∈ Finset.Icc 1 (ord m),
          pp m s / (z - Complex.exp (I * (θ₀ : ℂ)) * (ω m : ℂ)) ^ s) := by
      funext z
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => by ring
    rw [hrew]
    exact hL.const_mul c
  expType_plus := by
    obtain ⟨C, B, hC, hB, hbd⟩ := h.expType_plus
    refine ⟨‖c‖ * C, B, mul_nonneg (norm_nonneg c) hC, hB, fun u hu => ?_⟩
    have hpull : Minor.pull (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))) (fun z => c * φ z) u =
        c * Minor.pull (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))) φ u := by
      simp [Minor.pull]; ring
    rw [hpull, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd u hu) (norm_nonneg c)
  expType_minus := by
    obtain ⟨C, B, hC, hB, hbd⟩ := h.expType_minus
    refine ⟨‖c‖ * C, B, mul_nonneg (norm_nonneg c) hC, hB, fun u hu => ?_⟩
    have hpull : Minor.pull (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))) (fun z => c * φ z) u =
        c * Minor.pull (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))) φ u := by
      simp [Minor.pull]; ring
    rw [hpull, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd u hu) (norm_nonneg c)

/-- Exact quadratic substitution `t = x^2` linking `mordellIntegral φ u` to
`(1/2) * laplaceTransform φ u = laplaceTransform ((1/2) * φ ·) u` for all `u : ℝ`. -/
theorem mordellIntegral_eq_half_laplace (φ : ℂ → ℂ) (u : ℝ) :
    mordellIntegral φ u = (1 / 2 : ℂ) * laplaceTransform φ u := by
  unfold mordellIntegral laplaceTransform
  have hImg : (fun x : ℝ => x ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; positivity
    · intro ht
      refine ⟨Real.sqrt t, Real.sqrt_pos.mpr ht, Real.sq_sqrt ht.le⟩
  have hInj : Set.InjOn (fun x : ℝ => x ^ 2) (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := le_of_lt hx
    have hy0 : 0 ≤ y := le_of_lt hy
    have hsq : Real.sqrt (x ^ 2) = Real.sqrt (y ^ 2) := congrArg Real.sqrt hxy
    rwa [Real.sqrt_sq hx0, Real.sqrt_sq hy0] at hsq
  have hDeriv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * x) (Set.Ioi 0) x :=
    fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hDeriv hInj
    (fun t : ℝ => Complex.exp (-(u : ℂ) * (t : ℂ)) * φ (t : ℂ))
  rw [hImg] at hcov
  rw [hcov, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 ≤ 2 * x := by linarith [Set.mem_Ioi.mp hx]
  rw [abs_of_nonneg hx0, Complex.real_smul]
  push_cast
  ring

/-- **General Mordell-Integral D-Transcendence over `ℂ(u)`**:
Transfers differential transcendence from `laplaceTransform` directly to the Mordell integral
`mordellIntegral φ u = ∫_0^∞ e^{-u x^2} x φ(x^2) dx`. -/
theorem mordellIntegral_no_rat_ade
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ} {M : ℝ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    (hana : AnalyticAt ℂ φ 0)
    (hcont : ContinuousOn (fun ξ : ℝ => φ (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖φ (ξ : ℂ)‖ ≤ M)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (mordellIntegral φ) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have heq : mordellIntegral φ = laplaceTransform (fun z => (1 / 2 : ℂ) * φ z) := by
    funext u
    rw [mordellIntegral_eq_half_laplace φ u, laplaceTransform, laplaceTransform,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => by ring
  rw [heq] at hP
  refine laplaceTransform_no_rat_ade (HigherOrderBorelData.const_mul h (1 / 2 : ℂ) (by norm_num))
    (analyticAt_const.mul hana) (continuousOn_const.mul hcont) (M := (1 / 2) * M) (fun ξ hξ => ?_) P hP
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left (hbd ξ hξ) (by norm_num)

/-! ### 2. Entire Even-Cosh Engine `coshSqrt(z) = ∑ z^n / (2n)!` -/

/-- Entire function `C(z) = ∑_{n ≥ 0} z^n / (2n)!`, satisfying `C(w^2) = cosh w` for all `w ∈ ℂ`. -/
@[expose] def coshSqrt (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((2 * n).factorial : ℂ)

private lemma coshSqrt_term_norm_le (R : ℝ) (n : ℕ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖z ^ n / ((2 * n).factorial : ℂ)‖ ≤ R ^ n / (n.factorial : ℝ) := by
  have hzR : ‖z‖ ≤ R := (by simpa [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < R).le
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have hfac : (n.factorial : ℝ) ≤ ((2 * n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n)
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  calc ‖z‖ ^ n / ((2 * n).factorial : ℝ)
      ≤ R ^ n / ((2 * n).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzR n) (by positivity)
    _ ≤ R ^ n / (n.factorial : ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg (le_trans (norm_nonneg z) hzR) n) hpos hfac

lemma coshSqrt_differentiable : Differentiable ℂ coshSqrt := by
  intro z₀
  let R : ℝ := ‖z₀‖ + 1
  have hdiffOn : DifferentiableOn ℂ coshSqrt (Metric.ball (0 : ℂ) R) :=
    Complex.differentiableOn_tsum_of_summable_norm (Real.summable_pow_div_factorial R)
      (fun n => (differentiableOn_pow n).div_const _) Metric.isOpen_ball
      (fun n z hz => coshSqrt_term_norm_le R n hz)
  have hz₀ : z₀ ∈ Metric.ball (0 : ℂ) R := by
    simp [Metric.mem_ball, dist_zero_right, R]
  exact hdiffOn.differentiableAt (Metric.isOpen_ball.mem_nhds hz₀)

lemma coshSqrt_analyticAt (z₀ : ℂ) : AnalyticAt ℂ coshSqrt z₀ :=
  (coshSqrt_differentiable.differentiableOn.analyticOnNhd isOpen_univ) z₀ (Set.mem_univ z₀)

/-- Exact identity `coshSqrt (w^2) = cosh w` for all `w ∈ ℂ`. -/
theorem coshSqrt_sq (w : ℂ) : coshSqrt (w ^ 2) = Complex.cosh w := by
  rw [Complex.cosh, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have h1 : Summable (fun k : ℕ => w ^ k / (k.factorial : ℂ)) := by
    refine Summable.of_norm ?_
    simpa [norm_div, norm_pow, Complex.norm_natCast] using Real.summable_pow_div_factorial ‖w‖
  have h2 : Summable (fun k : ℕ => (-w) ^ k / (k.factorial : ℂ)) := by
    refine Summable.of_norm ?_
    simpa [norm_div, norm_pow, norm_neg, Complex.norm_natCast] using
      Real.summable_pow_div_factorial ‖w‖
  rw [← h1.tsum_add h2, ← tsum_div_const]
  unfold coshSqrt
  symm
  refine tsum_eq_tsum_of_ne_zero_bij (fun n => 2 * n.1) ?_ ?_ ?_
  · intro a b hab
    exact Subtype.ext (by dsimp at hab; omega)
  · intro k hk
    have hk' : (w ^ k / (k.factorial : ℂ) + (-w) ^ k / (k.factorial : ℂ)) / 2 ≠ 0 := hk
    have hkeven : k % 2 = 0 := by
      by_contra hodd
      have hmod : k % 2 = 1 := by omega
      have hneg : (-w) ^ k = -(w ^ k) := by
        rw [neg_pow, Odd.neg_one_pow (Nat.odd_iff.mpr hmod)]; ring
      have h0 : (w ^ k / (k.factorial : ℂ) + (-w) ^ k / (k.factorial : ℂ)) / 2 = 0 := by
        rw [hneg]; ring
      exact hk' h0
    have hne : (w ^ 2) ^ (k / 2) / ((2 * (k / 2)).factorial : ℂ) ≠ 0 := by
      intro h0
      apply hk'
      have hk2 : 2 * (k / 2) = k := by omega
      rw [← pow_mul, hk2] at h0
      have hev : (-w) ^ k = w ^ k := by
        rw [neg_pow, Even.neg_one_pow (Nat.even_iff.mpr hkeven), one_mul]
      rw [hev]
      calc (w ^ k / (k.factorial : ℂ) + w ^ k / (k.factorial : ℂ)) / 2
          = w ^ k / (k.factorial : ℂ) := by ring
        _ = 0 := h0
    exact ⟨⟨k / 2, hne⟩, by dsimp; omega⟩
  · intro n
    have hev : (-w) ^ (2 * n.1) = w ^ (2 * n.1) := by
      rw [neg_pow, Even.neg_one_pow ⟨n.1, by omega⟩, one_mul]
    rw [hev, ← pow_mul]
    ring

private lemma hasDerivAt_complex_cosh (w : ℂ) : HasDerivAt Complex.cosh (Complex.sinh w) w := by
  have h1 : HasDerivAt Complex.exp (Complex.exp w) w := Complex.hasDerivAt_exp w
  have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-z)) (-Complex.exp (-w)) w := by
    simpa using (hasDerivAt_id w).neg.cexp
  have h3 := (h1.add h2).div_const 2
  convert h3 using 1
  · funext z; rw [Complex.cosh]; rfl
  · rw [Complex.sinh]; ring

lemma deriv_coshSqrt_sq (w : ℂ) : 2 * w * deriv coshSqrt (w ^ 2) = Complex.sinh w := by
  have h1 : HasDerivAt (fun z : ℂ => coshSqrt (z ^ 2)) (deriv coshSqrt (w ^ 2) * (2 * w)) w := by
    have hd1 : HasDerivAt coshSqrt (deriv coshSqrt (w ^ 2)) (w ^ 2) :=
      (coshSqrt_differentiable (w ^ 2)).hasDerivAt
    have hd2 : HasDerivAt (fun z : ℂ => z ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    exact HasDerivAt.comp (h := fun z : ℂ => z ^ 2) (h₂ := coshSqrt) w hd1 hd2
  have h2 : HasDerivAt (fun z : ℂ => coshSqrt (z ^ 2)) (Complex.sinh w) w := by
    have heq : (fun z : ℂ => coshSqrt (z ^ 2)) = Complex.cosh := funext coshSqrt_sq
    rw [heq]
    exact hasDerivAt_complex_cosh w
  have hu := h1.unique h2
  linear_combination hu

lemma exists_sq_eq (z : ℂ) : ∃ w : ℂ, w ^ 2 = z := by
  refine ⟨(Real.sqrt ‖z‖ : ℂ) * Complex.exp (I * ((Complex.arg z / 2 : ℝ) : ℂ)), ?_⟩
  rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg z), ← Complex.exp_nat_mul]
  have harg : ((2 : ℕ) : ℂ) * (I * ((Complex.arg z / 2 : ℝ) : ℂ)) = (Complex.arg z : ℂ) * I := by
    push_cast; ring
  rw [harg]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- General simple-pole residue limit lemma for `N(z) / D(z)` at a simple zero `z₀` of `D`. -/
private lemma simple_pole_tendsto_of_analytic {N D : ℂ → ℂ} {z₀ : ℂ}
    (hN : AnalyticAt ℂ N z₀) (hD : AnalyticAt ℂ D z₀)
    (hD0 : D z₀ = 0) (hD' : deriv D z₀ ≠ 0) :
    ∃ L : ℂ, Filter.Tendsto (fun z : ℂ => N z / D z - (N z₀ / deriv D z₀) / (z - z₀))
      (𝓝[≠] z₀) (𝓝 L) := by
  have hdD_an : AnalyticAt ℂ (dslope D z₀) z₀ := hD.dslope z₀
  have hdD_val : dslope D z₀ z₀ = deriv D z₀ := dslope_same D z₀
  let F : ℂ → ℂ := fun z => N z * deriv D z₀ - N z₀ * dslope D z₀ z
  have hF_an : AnalyticAt ℂ F z₀ :=
    (hN.mul analyticAt_const).sub (analyticAt_const.mul hdD_an)
  have hF0 : F z₀ = 0 := by simp [F]
  have hdF_an : AnalyticAt ℂ (dslope F z₀) z₀ := hF_an.dslope z₀
  let G : ℂ → ℂ := fun z => dslope F z₀ z / (deriv D z₀ * dslope D z₀ z)
  have hG_cont : ContinuousAt G z₀ :=
    hdF_an.continuousAt.div (continuousAt_const.mul hdD_an.continuousAt)
      (mul_ne_zero hD' (hdD_val.symm ▸ hD'))
  refine ⟨G z₀, hG_cont.tendsto.mono_left nhdsWithin_le_nhds |>.congr' ?_⟩
  have hne_ev : ∀ᶠ z in 𝓝 z₀, dslope D z₀ z ≠ 0 :=
    hdD_an.continuousAt.eventually_ne (hdD_val.symm ▸ hD')
  filter_upwards [nhdsWithin_le_nhds hne_ev, self_mem_nhdsWithin] with z hdz hz_ne
  have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
  have hDz : D z = (z - z₀) * dslope D z₀ z := by
    have := sub_smul_dslope D z₀ z
    rw [hD0, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hFz : F z = (z - z₀) * dslope F z₀ z := by
    have := sub_smul_dslope F z₀ z
    rw [hF0, sub_zero, smul_eq_mul] at this
    exact this.symm
  dsimp only [G]
  rw [hDz]
  field_simp [hsub, hdz, hD']
  dsimp only [F] at hFz
  linear_combination -hFz

private lemma exp_I_pi : Complex.exp (I * (Real.pi : ℂ)) = -1 := by
  rw [mul_comm]; exact Complex.exp_pi_mul_I

private lemma exp_neg_I_pi : Complex.exp (-I * (Real.pi : ℂ)) = -1 := by
  rw [neg_mul, Complex.exp_neg, exp_I_pi]; norm_num

private lemma norm_exp_I_real (t : ℝ) : ‖Complex.exp (I * (t : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I t

private lemma real_one_le_cosh (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hsq : 0 ≤ (Real.exp x - 1) ^ 2 := sq_nonneg _
  have hpos : 0 < Real.exp x := Real.exp_pos x
  nlinarith

private lemma real_cosh_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.cosh a ≤ Real.cosh b := by
  rw [Real.cosh_eq, Real.cosh_eq]
  have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have h2 : Real.exp (-a - b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : Real.exp (-b) = Real.exp a * Real.exp (-a - b) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-a) = Real.exp b * Real.exp (-a - b) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h3, h4]
  nlinarith [Real.exp_pos a, Real.exp_pos b]

private lemma real_sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have h2 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

private lemma real_sinh_mono {a b : ℝ} (hab : a ≤ b) : Real.sinh a ≤ Real.sinh b := by
  rw [Real.sinh_eq, Real.sinh_eq]
  have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have h2 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Lower bound `|cosh w| ≥ sinh (Re w)` for all `w ∈ ℂ`. -/
private lemma sinh_re_le_norm_cosh (w : ℂ) :
    Real.sinh w.re ≤ ‖Complex.cosh w‖ := by
  rw [Complex.cosh, norm_div, Complex.norm_ofNat, Real.sinh_eq]
  have h1 : ‖Complex.exp w‖ - ‖Complex.exp (-w)‖ ≤ ‖Complex.exp w + Complex.exp (-w)‖ := by
    have htri := norm_sub_le (Complex.exp w + Complex.exp (-w)) (Complex.exp (-w))
    rw [add_sub_cancel_right] at htri
    linarith
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h1
  linarith

/-- On a ray `d * v` (`v ≥ 0`) with `d = e^{i(π ± π/3)}`, `w = √v e^{∓ i π/3}` satisfies
`w^2 = d * v` and `Re w = (1/2) √v`. -/
private lemma exists_sqrt_on_flank_ray (s : ℝ) (hs : s = 1 ∨ s = -1) {v : ℝ} (hv : 0 ≤ v) :
    ∃ w : ℂ, w ^ 2 = Complex.exp (I * ((Real.pi + s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ) ∧
      w.re = (1 / 2) * Real.sqrt v ∧ ‖w‖ = Real.sqrt v := by
  let φ : ℝ := -s * (Real.pi / 3)
  let w : ℂ := (Real.sqrt v : ℂ) * Complex.exp (I * (φ : ℂ))
  refine ⟨w, ?_, ?_, ?_⟩
  · dsimp only [w]
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hv, ← Complex.exp_nat_mul]
    rw [mul_comm (v : ℂ)]
    congr 1
    rw [Complex.exp_eq_exp_iff_exists_int]
    rcases hs with rfl | rfl
    · refine ⟨-1, ?_⟩
      dsimp only [φ]; push_cast; ring
    · refine ⟨0, ?_⟩
      dsimp only [φ]; push_cast; ring
  · dsimp only [w, φ]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      mul_comm I, Complex.exp_ofReal_mul_I_re]
    rcases hs with rfl | rfl
    · rw [show -(1 : ℝ) * (Real.pi / 3) = -(Real.pi / 3) by ring, Real.cos_neg, Real.cos_pi_div_three]
      ring
    · rw [show -(-1 : ℝ) * (Real.pi / 3) = Real.pi / 3 by ring, Real.cos_pi_div_three]
      ring
  · dsimp only [w]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v),
      norm_exp_I_real, mul_one]

/-- Uniform `ExpType` helper for `N(z) / D(z)` on flanking rays `e^{i (π ± π/3)}` when
`D` is continuous, nowhere zero on the ray, `‖D (d * v)‖ ≥ 1` for `v ≥ 16`, and
`‖N (d * v)‖ ≤ A * exp (B * v)` for `v ≥ 0`. -/
private lemma expType_div_of_flank_bound {N D : ℂ → ℂ} {d : ℂ} (hd : ‖d‖ = 1)
    (hD_cont : Continuous (fun v : ℝ => D (d * (v : ℂ))))
    (hD_ne : ∀ v : ℝ, 0 ≤ v → D (d * (v : ℂ)) ≠ 0)
    (hD_far : ∀ v : ℝ, 16 ≤ v → 1 ≤ ‖D (d * (v : ℂ))‖)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hN_bd : ∀ v : ℝ, 0 ≤ v → ‖N (d * (v : ℂ))‖ ≤ A * Real.exp (B * v)) :
    ExpType (Minor.pull d (fun z => N z / D z)) := by
  have hcomp : IsCompact (Set.Icc (0 : ℝ) 16) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) 16).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨v₀, hv₀_mem, hv₀_min⟩ :=
    hcomp.exists_isMinOn hne (continuous_norm.comp hD_cont).continuousOn
  have hm_pos : 0 < ‖D (d * (v₀ : ℂ))‖ := norm_pos_iff.mpr (hD_ne v₀ hv₀_mem.1)
  let c : ℝ := min 1 ‖D (d * (v₀ : ℂ))‖
  have hc_pos : 0 < c := lt_min one_pos hm_pos
  have hD_ge : ∀ v : ℝ, 0 ≤ v → c ≤ ‖D (d * (v : ℂ))‖ := by
    intro v hv
    by_cases hv16 : v ≤ 16
    · exact le_trans (min_le_right _ _) (hv₀_min ⟨hv, hv16⟩)
    · push Not at hv16
      exact le_trans (min_le_left _ _) (hD_far v hv16.le)
  refine ⟨A / c, B, by positivity, hB, fun v hv => ?_⟩
  rw [Minor.pull, norm_mul, hd, one_mul, norm_div]
  calc ‖N (d * (v : ℂ))‖ / ‖D (d * (v : ℂ))‖
      ≤ (A * Real.exp (B * v)) / c :=
        div_le_div₀ (by positivity) (hN_bd v hv) hc_pos (hD_ge v hv)
    _ = (A / c) * Real.exp (B * v) := by ring

private lemma real_sinh_two_gt_two : (2 : ℝ) < Real.sinh 2 := by
  rw [Real.sinh_eq]
  have he1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 3
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have he2 : (25 / 4 : ℝ) ≤ Real.exp 2 := by
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hneg : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-! ### 3. Three Unconditional Mock Theta & Mordell D-Transcendence Theorems -/

/-! #### 3A. Classical Zwegers–Mordell Integral `∫_0^∞ e^{-u x^2} (x / cosh x) dx` -/

/-- Classical Zwegers–Mordell Borel kernel `φ_cosh(z) = 1 / cosh(√z) = (coshSqrt z)⁻¹`. -/
@[expose] def mordellCoshBorel (z : ℂ) : ℂ := (coshSqrt z)⁻¹

/-- Pole frequencies `ω_k = π^2 (k + 1/2)^2` of `1 / cosh(√z)` along `θ₀ = π`. -/
@[expose] def mordellCoshFreq (k : ℕ) : ℝ := (Real.pi * ((k : ℝ) + 1 / 2)) ^ 2

/-- Classical Zwegers–Mordell integral `∫_0^∞ e^{-u x^2} (x / cosh x) dx`. -/
@[expose] def mordellCoshIntegral (u : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) / Complex.cosh (x : ℂ)

lemma mordellCoshIntegral_eq (u : ℝ) :
    mordellCoshIntegral u = mordellIntegral mordellCoshBorel u := by
  unfold mordellCoshIntegral mordellIntegral mordellCoshBorel
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [coshSqrt_sq, div_eq_mul_inv]

private lemma coshSqrt_eq_zero_iff (z : ℂ) :
    coshSqrt z = 0 ↔ ∃ k : ℕ, z = -(mordellCoshFreq k : ℂ) := by
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := exists_sq_eq z
    rw [coshSqrt_sq, Complex.cosh] at hz
    have hsum : Complex.exp w + Complex.exp (-w) = 0 := by
      have := congrArg (· * 2) hz; simpa using this
    have hexp2 : Complex.exp (2 * w) = Complex.exp (I * (Real.pi : ℂ)) := by
      rw [exp_I_pi, show 2 * w = w + w by ring, Complex.exp_add]
      have hprod : Complex.exp w * Complex.exp (-w) = 1 := by
        rw [← Complex.exp_add]; simp
      linear_combination (Complex.exp w) * hsum - hprod
    rw [Complex.exp_eq_exp_iff_exists_int] at hexp2
    obtain ⟨j, hj⟩ := hexp2
    have hw : w = I * (Real.pi * ((j : ℂ) + 1 / 2)) := by
      linear_combination hj / 2
    have hsq : w ^ 2 = -((Real.pi * ((j : ℝ) + 1 / 2)) ^ 2 : ℝ) := by
      rw [hw]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    by_cases hj0 : 0 ≤ j
    · refine ⟨j.toNat, ?_⟩
      rw [hsq, mordellCoshFreq]
      have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hj0
      rw [hcast]
    · push Not at hj0
      refine ⟨(-j - 1).toNat, ?_⟩
      rw [hsq, mordellCoshFreq]
      have hcast : (((-j - 1).toNat : ℕ) : ℝ) = -(j : ℝ) - 1 := by
        have : (0 : ℤ) ≤ -j - 1 := by omega
        exact_mod_cast Int.toNat_of_nonneg this
      rw [hcast]
      have hreal : (Real.pi * ((j : ℝ) + 1 / 2)) ^ 2 = (Real.pi * (-(j : ℝ) - 1 + 1 / 2)) ^ 2 := by
        ring
      rw [hreal]
  · rintro ⟨k, rfl⟩
    let r : ℝ := Real.pi * ((k : ℝ) + 1 / 2)
    have hsq : (I * (r : ℂ)) ^ 2 = -(mordellCoshFreq k : ℂ) := by
      rw [mordellCoshFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [← hsq, coshSqrt_sq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, Complex.ofReal_eq_zero]
    dsimp only [r]
    exact Real.cos_eq_zero_iff.mpr ⟨(k : ℤ), by push_cast; ring⟩

private lemma deriv_coshSqrt_mordellCoshFreq (k : ℕ) :
    deriv coshSqrt (-(mordellCoshFreq k : ℂ)) ≠ 0 := by
  let r : ℝ := Real.pi * ((k : ℝ) + 1 / 2)
  have hsq : (I * (r : ℂ)) ^ 2 = -(mordellCoshFreq k : ℂ) := by
    rw [mordellCoshFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hd := deriv_coshSqrt_sq (I * (r : ℂ))
  rw [hsq] at hd
  intro h0
  rw [h0, mul_zero] at hd
  have hsinh : Complex.sinh (I * (r : ℂ)) = (Real.sin r : ℂ) * I := by
    rw [show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.sinh_mul_I, Complex.ofReal_sin]
  rw [hsinh] at hd
  have hsin0 : Real.sin r = 0 := by
    have : (Real.sin r : ℂ) = 0 := (mul_eq_zero.mp hd.symm).resolve_right Complex.I_ne_zero
    exact Complex.ofReal_eq_zero.mp this
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin0
  have hpi : (m : ℝ) = (k : ℝ) + 1 / 2 := by
    have : (m : ℝ) * Real.pi = Real.pi * ((k : ℝ) + 1 / 2) := hm
    nlinarith [Real.pi_pos]
  have hint : 2 * m = 2 * (k : ℤ) + 1 := by
    have : ((2 * m : ℤ) : ℝ) = ((2 * (k : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-- Concrete `HigherOrderBorelData` witness for the classical Zwegers–Mordell kernel
`1 / cosh(√z)` along `θ₀ = π`. -/
def mordellCosh_borelData :
    HigherOrderBorelData mordellCoshBorel Real.pi mordellCoshFreq (fun _ => 1)
      (fun k s => if s = 1 then (deriv coshSqrt (-(mordellCoshFreq k : ℂ)))⁻¹ else 0) where
  α₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by unfold mordellCoshFreq; positivity
  ω_mono := fun a b hab => by
    unfold mordellCoshFreq
    have hlt : (a : ℝ) < b := by exact_mod_cast hab
    have hlt' : Real.pi * ((a : ℝ) + 1 / 2) < Real.pi * ((b : ℝ) + 1 / 2) :=
      mul_lt_mul_of_pos_left (by linarith) Real.pi_pos
    have hpos : 0 < Real.pi * ((a : ℝ) + 1 / 2) := by positivity
    nlinarith
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun k => by
    simpa using inv_ne_zero (deriv_coshSqrt_mordellCoshFreq k)
  analyticOn := by
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hz' := hz.2
    rw [exp_neg_I_pi] at hz'
    have hne : coshSqrt z ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := (coshSqrt_eq_zero_iff z).mp h0
      exact hz' ⟨k, by rw [hk]; ring⟩
    exact (coshSqrt_analyticAt z).inv hne
  pole_principalPart := fun k => by
    have hpole : Complex.exp (I * (Real.pi : ℂ)) * (mordellCoshFreq k : ℂ) =
        -(mordellCoshFreq k : ℂ) := by rw [exp_I_pi]; ring
    rw [hpole]
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one]
    have hzero : coshSqrt (-(mordellCoshFreq k : ℂ)) = 0 :=
      (coshSqrt_eq_zero_iff _).mpr ⟨k, rfl⟩
    have hlim := simple_pole_tendsto_of_analytic (N := fun _ => (1 : ℂ))
      analyticAt_const (coshSqrt_analyticAt _) hzero (deriv_coshSqrt_mordellCoshFreq k)
    simpa [mordellCoshBorel, one_div] using hlim
  expType_plus := by
    have hfun : mordellCoshBorel = fun z => (1 : ℂ) / coshSqrt z := funext fun z => by
      simp [mordellCoshBorel, one_div]
    rw [hfun]
    refine expType_div_of_flank_bound (norm_exp_I_real _)
      (coshSqrt_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num)
      (fun v _ => by simp)
    · obtain ⟨k, hk⟩ := (coshSqrt_eq_zero_iff _).mp h0
      have him := congrArg Complex.im hk
      have hpos : 0 < mordellCoshFreq k := by unfold mordellCoshFreq; positivity
      have hv_ne : v ≠ 0 := by
        intro hv0; rw [hv0, Complex.ofReal_zero, mul_zero] at hk
        exact hpos.ne' (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hk.symm))
      have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        mul_comm I, Complex.exp_ofReal_mul_I_im, add_comm Real.pi (Real.pi / 3),
        Real.sin_add_pi, Real.sin_pi_div_three] at him
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero] at him
      have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_ray 1 (Or.inl rfl) (by linarith : 0 ≤ v)
      rw [show Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
        simpa using hw_sq.symm, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith)
        linarith
      have hs : Real.sinh 2 ≤ Real.sinh w.re := real_sinh_mono hge2
      linarith [real_sinh_two_gt_two, sinh_re_le_norm_cosh w]
  expType_minus := by
    have hfun : mordellCoshBorel = fun z => (1 : ℂ) / coshSqrt z := funext fun z => by
      simp [mordellCoshBorel, one_div]
    rw [hfun]
    refine expType_div_of_flank_bound (norm_exp_I_real _)
      (coshSqrt_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num)
      (fun v _ => by simp)
    · obtain ⟨k, hk⟩ := (coshSqrt_eq_zero_iff _).mp h0
      have him := congrArg Complex.im hk
      have hpos : 0 < mordellCoshFreq k := by unfold mordellCoshFreq; positivity
      have hv_ne : v ≠ 0 := by
        intro hv0; rw [hv0, Complex.ofReal_zero, mul_zero] at hk
        exact hpos.ne' (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hk.symm))
      have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        mul_comm I, Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub, Real.sin_pi_div_three] at him
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero] at him
      have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_ray (-1) (Or.inr rfl) (by linarith : 0 ≤ v)
      rw [show Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
        have : Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
        rw [← this]; exact hw_sq.symm, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith)
        linarith
      have hs : Real.sinh 2 ≤ Real.sinh w.re := real_sinh_mono hge2
      linarith [real_sinh_two_gt_two, sinh_re_le_norm_cosh w]

private lemma mordellCoshBorel_real_bound (ξ : ℝ) (hξ : 0 ≤ ξ) :
    ‖mordellCoshBorel (ξ : ℂ)‖ ≤ 1 := by
  unfold mordellCoshBorel
  have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
  rw [← hsq, coshSqrt_sq, ← Complex.ofReal_cosh, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.cosh_pos _).le]
  exact inv_le_one_of_one_le₀ (real_one_le_cosh _)

private lemma mordellCoshBorel_cont :
    ContinuousOn (fun ξ : ℝ => mordellCoshBorel (ξ : ℂ)) (Set.Ici 0) := by
  intro ξ hξ
  have hne : coshSqrt (ξ : ℂ) ≠ 0 := by
    have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
    rw [← hsq, coshSqrt_sq, ← Complex.ofReal_cosh]
    exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  exact ((coshSqrt_analyticAt (ξ : ℂ)).inv hne).continuousAt.comp
    Complex.continuous_ofReal.continuousAt |>.continuousWithinAt

/-- **Theorem A (Classical Zwegers–Mordell Integral D-Transcendence over `ℂ(u)`)**:
The Mordell integral `∫_0^∞ e^{-u x^2} (x / cosh x) dx` satisfies NO nonzero rational-coefficient
differential equation over `ℂ(u)`. -/
theorem mordellCosh_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val mordellCoshIntegral u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (mordellIntegral mordellCoshBorel) u)
        (evalRatU P (u : ℂ)) = 0 := by
    simpa only [show mordellCoshIntegral = mordellIntegral mordellCoshBorel from
      funext mordellCoshIntegral_eq] using hP
  have hana0 : AnalyticAt ℂ mordellCoshBorel 0 := by
    have h0 : coshSqrt 0 ≠ 0 := by
      have hsq : coshSqrt ((0 : ℂ) ^ 2) = Complex.cosh 0 := coshSqrt_sq 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.cosh_zero] at hsq
      rw [hsq]; exact one_ne_zero
    exact (coshSqrt_analyticAt 0).inv h0
  exact mordellIntegral_no_rat_ade mordellCosh_borelData hana0 mordellCoshBorel_cont
    mordellCoshBorel_real_bound P hP'

/-! #### 3B. Ramanujan's 3rd-Order Mock Theta `ω(q)` Mordell Integral -/

/-- Borel kernel of Ramanujan's 3rd-order mock theta `ω(q)`:
`g_ω(z) = (2 cosh(√z) - 1)⁻¹`, satisfying `g_ω(x^2) = cosh(x/2) / cosh(3x/2)`. -/
@[expose] def mockThetaOmegaBorel (z : ℂ) : ℂ := (2 * coshSqrt z - 1)⁻¹

/-- Strictly increasing sequence `1, 5, 7, 11, 13, 17, ...` (`n ≡ ±1 mod 6`). -/
@[expose] def coprimeSixSeq (k : ℕ) : ℕ := 6 * (k / 2) + if k % 2 = 0 then 1 else 5

/-- Pole frequencies `ω_k = (π n_k / 3)^2` (`n_k ≡ ±1 mod 6`) of `g_ω(z)`. -/
@[expose] def mockThetaOmegaFreq (k : ℕ) : ℝ := (Real.pi * (coprimeSixSeq k : ℝ) / 3) ^ 2

/-- Ramanujan's 3rd-order mock theta `ω(q)` Mordell integral
`∫_0^∞ e^{-u x^2} (x cosh(x/2) / cosh(3x/2)) dx`. -/
@[expose] def mockThetaOmegaMordell (u : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) *
    Complex.cosh ((x : ℂ) / 2) / Complex.cosh (3 * (x : ℂ) / 2)

private lemma cosh_triple_identity (a : ℂ) :
    Complex.cosh (3 * a) = Complex.cosh a * (2 * Complex.cosh (2 * a) - 1) := by
  rw [Complex.cosh, Complex.cosh, Complex.cosh]
  have h1 : Complex.exp (3 * a) = Complex.exp a ^ 3 := by
    rw [← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : Complex.exp (-(3 * a)) = Complex.exp (-a) ^ 3 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Complex.exp (2 * a) = Complex.exp a ^ 2 := by
    rw [← Complex.exp_nat_mul]; push_cast; rfl
  have h4 : Complex.exp (-(2 * a)) = Complex.exp (-a) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hprod : Complex.exp a * Complex.exp (-a) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [h1, h2, h3, h4]
  linear_combination -(Complex.exp a + Complex.exp (-a)) / 2 * hprod

lemma mockThetaOmegaMordell_eq (u : ℝ) :
    mockThetaOmegaMordell u = mordellIntegral mockThetaOmegaBorel u := by
  unfold mockThetaOmegaMordell mordellIntegral mockThetaOmegaBorel
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [coshSqrt_sq]
  have h3 : 3 * (x : ℂ) / 2 = 3 * ((x : ℂ) / 2) := by ring
  have h2 : 2 * ((x : ℂ) / 2) = (x : ℂ) := by ring
  rw [h3, cosh_triple_identity, h2]
  have hc : Complex.cosh ((x : ℂ) / 2) ≠ 0 := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cosh]
    exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  field_simp [hc]

private lemma coprimeSixSeq_strictMono : StrictMono coprimeSixSeq := by
  intro a b hab
  unfold coprimeSixSeq
  split_ifs <;> omega

private lemma coprimeSixSeq_pos (k : ℕ) : 0 < coprimeSixSeq k := by
  unfold coprimeSixSeq; split_ifs <;> omega

private lemma coprimeSixSeq_mod_three (k : ℕ) : coprimeSixSeq k % 3 ≠ 0 := by
  unfold coprimeSixSeq; split_ifs <;> omega

private lemma exists_coprimeSixSeq_of_mod_six (m : ℤ) (hm : m % 6 = 1 ∨ m % 6 = 5) :
    ∃ k : ℕ, (coprimeSixSeq k : ℤ) = |m| := by
  have hnat : m.natAbs % 6 = 1 ∨ m.natAbs % 6 = 5 := by omega
  rcases hnat with h1 | h5
  · refine ⟨2 * (m.natAbs / 6), ?_⟩
    unfold coprimeSixSeq
    have hdiv : (2 * (m.natAbs / 6)) / 2 = m.natAbs / 6 := by omega
    have hmod : (2 * (m.natAbs / 6)) % 2 = 0 := by omega
    rw [hdiv, hmod, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    have hnat_eq : 6 * (m.natAbs / 6) + 1 = m.natAbs := by omega
    rw [hnat_eq, Int.natCast_natAbs]
  · refine ⟨2 * (m.natAbs / 6) + 1, ?_⟩
    unfold coprimeSixSeq
    have hdiv : (2 * (m.natAbs / 6) + 1) / 2 = m.natAbs / 6 := by omega
    have hmod : (2 * (m.natAbs / 6) + 1) % 2 = 1 := by omega
    rw [hdiv, hmod, ite_eq_right_iff.mpr (fun h => by omega)]
    have hnat_eq : 6 * (m.natAbs / 6) + 5 = m.natAbs := by omega
    rw [hnat_eq, Int.natCast_natAbs]

private lemma two_coshSqrt_sub_one_eq_zero_iff (z : ℂ) :
    2 * coshSqrt z - 1 = 0 ↔ ∃ k : ℕ, z = -(mockThetaOmegaFreq k : ℂ) := by
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := exists_sq_eq z
    rw [coshSqrt_sq, Complex.cosh] at hz
    have hsum : Complex.exp w + Complex.exp (-w) = 1 := by linear_combination hz
    have hprod : Complex.exp w * Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
    have hquad : Complex.exp w ^ 2 - Complex.exp w + 1 = 0 := by
      linear_combination Complex.exp w * hsum - hprod
    let ζ : ℂ := Complex.exp (I * ((Real.pi / 3 : ℝ) : ℂ))
    have hζ_sum : ζ + ζ⁻¹ = 1 := by
      dsimp only [ζ]
      rw [← Complex.exp_neg]
      have h1 : Complex.exp (I * ((Real.pi / 3 : ℝ) : ℂ)) +
          Complex.exp (-(I * ((Real.pi / 3 : ℝ) : ℂ))) =
          2 * Complex.cos ((Real.pi / 3 : ℝ) : ℂ) := by
        rw [Complex.cos]
        have he1 : I * ((Real.pi / 3 : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) * I := by ring
        rw [he1, ← neg_mul]; ring
      rw [h1, ← Complex.ofReal_cos, Real.cos_pi_div_three]
      push_cast; ring
    have hζ_prod : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ (Complex.exp_ne_zero _)
    have hfac : (Complex.exp w - ζ) * (Complex.exp w - ζ⁻¹) = 0 := by
      linear_combination hquad - Complex.exp w * hζ_sum + hζ_prod
    rcases mul_eq_zero.mp hfac with hL | hR
    · have hexp : Complex.exp w = Complex.exp (I * ((Real.pi / 3 : ℝ) : ℂ)) := sub_eq_zero.mp hL
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨j, hj⟩ := hexp
      let m : ℤ := 6 * j + 1
      have hw : w = I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ) := by
        dsimp only [m]; rw [hj]; push_cast; ring
      obtain ⟨k, hk⟩ := exists_coprimeSixSeq_of_mod_six m (Or.inl (by omega))
      refine ⟨k, ?_⟩
      rw [hw, mockThetaOmegaFreq]
      have hsq_m : ((coprimeSixSeq k : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by
        have h1 : (coprimeSixSeq k : ℝ) = |(m : ℝ)| := by exact_mod_cast hk
        rw [h1, sq_abs]
      have hsq_mC : (coprimeSixSeq k : ℂ) ^ 2 = (m : ℂ) ^ 2 := by exact_mod_cast hsq_m
      have hLHS : (I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ)) ^ 2 = -((Real.pi : ℂ) * (m : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast
      linear_combination -(Real.pi : ℂ) ^ 2 / 9 * hsq_mC.symm
    · have hexp : Complex.exp w = Complex.exp (-(I * ((Real.pi / 3 : ℝ) : ℂ))) := by
        rw [Complex.exp_neg]; exact sub_eq_zero.mp hR
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨j, hj⟩ := hexp
      let m : ℤ := 6 * j - 1
      have hw : w = I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ) := by
        dsimp only [m]; rw [hj]; push_cast; ring
      obtain ⟨k, hk⟩ := exists_coprimeSixSeq_of_mod_six m (Or.inr (by omega))
      refine ⟨k, ?_⟩
      rw [hw, mockThetaOmegaFreq]
      have hsq_m : ((coprimeSixSeq k : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by
        have h1 : (coprimeSixSeq k : ℝ) = |(m : ℝ)| := by exact_mod_cast hk
        rw [h1, sq_abs]
      have hsq_mC : (coprimeSixSeq k : ℂ) ^ 2 = (m : ℂ) ^ 2 := by exact_mod_cast hsq_m
      have hLHS : (I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ)) ^ 2 = -((Real.pi : ℂ) * (m : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast
      linear_combination -(Real.pi : ℂ) ^ 2 / 9 * hsq_mC.symm
  · rintro ⟨k, rfl⟩
    let r : ℝ := Real.pi * (coprimeSixSeq k : ℝ) / 3
    have hsq : (I * (r : ℂ)) ^ 2 = -(mockThetaOmegaFreq k : ℂ) := by
      rw [mockThetaOmegaFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [← hsq, coshSqrt_sq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I,
      ← Complex.ofReal_cos]
    have hcos : Real.cos r = 1 / 2 := by
      dsimp only [r, coprimeSixSeq]
      split_ifs with hmod
      · rw [show Real.pi * ((6 * (k / 2) + 1 : ℕ) : ℝ) / 3 =
            Real.pi / 3 + ((k / 2 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
        rw [Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_three]
      · rw [show Real.pi * ((6 * (k / 2) + 5 : ℕ) : ℝ) / 3 =
            -(Real.pi / 3) + ((k / 2 + 1 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
        rw [Real.cos_add_nat_mul_two_pi, Real.cos_neg, Real.cos_pi_div_three]
    rw [hcos]; push_cast; ring

private lemma deriv_two_coshSqrt_sub_one_ne_zero (k : ℕ) :
    deriv (fun z => 2 * coshSqrt z - 1) (-(mockThetaOmegaFreq k : ℂ)) ≠ 0 := by
  let z₀ : ℂ := -(mockThetaOmegaFreq k : ℂ)
  have hd_eq : deriv (fun z => 2 * coshSqrt z - 1) z₀ = 2 * deriv coshSqrt z₀ :=
    (((coshSqrt_differentiable z₀).hasDerivAt.const_mul (2 : ℂ)).sub_const (1 : ℂ)).deriv
  rw [hd_eq]
  refine mul_ne_zero (by norm_num) ?_
  let r : ℝ := Real.pi * (coprimeSixSeq k : ℝ) / 3
  have hsq : (I * (r : ℂ)) ^ 2 = z₀ := by
    dsimp only [z₀, r]; rw [mockThetaOmegaFreq]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hd := deriv_coshSqrt_sq (I * (r : ℂ))
  rw [hsq] at hd
  intro h0
  rw [h0, mul_zero] at hd
  have hsinh : Complex.sinh (I * (r : ℂ)) = (Real.sin r : ℂ) * I := by
    rw [show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.sinh_mul_I, Complex.ofReal_sin]
  rw [hsinh] at hd
  have hsin0 : Real.sin r = 0 := by
    have : (Real.sin r : ℂ) = 0 := (mul_eq_zero.mp hd.symm).resolve_right Complex.I_ne_zero
    exact Complex.ofReal_eq_zero.mp this
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin0
  have h3m : 3 * m = (coprimeSixSeq k : ℤ) := by
    have : (m : ℝ) * Real.pi = Real.pi * (coprimeSixSeq k : ℝ) / 3 := hm
    have hreal : ((3 * m : ℤ) : ℝ) = ((coprimeSixSeq k : ℤ) : ℝ) := by
      push_cast; nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  have hmod := coprimeSixSeq_mod_three k
  omega

/-- Concrete `HigherOrderBorelData` witness for Ramanujan's 3rd-order mock theta `ω(q)`
Borel kernel `(2 cosh(√z) - 1)⁻¹` along `θ₀ = π`. -/
def mockThetaOmega_borelData :
    HigherOrderBorelData mockThetaOmegaBorel Real.pi mockThetaOmegaFreq (fun _ => 1)
      (fun k s => if s = 1 then
        (deriv (fun z => 2 * coshSqrt z - 1) (-(mockThetaOmegaFreq k : ℂ)))⁻¹ else 0) where
  α₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by
    unfold mockThetaOmegaFreq
    have := coprimeSixSeq_pos 0
    positivity
  ω_mono := fun a b hab => by
    unfold mockThetaOmegaFreq
    have hlt : (coprimeSixSeq a : ℝ) < (coprimeSixSeq b : ℝ) := by
      exact_mod_cast coprimeSixSeq_strictMono hab
    have hlt' : Real.pi * (coprimeSixSeq a : ℝ) / 3 < Real.pi * (coprimeSixSeq b : ℝ) / 3 := by
      have : Real.pi * (coprimeSixSeq a : ℝ) < Real.pi * (coprimeSixSeq b : ℝ) :=
        mul_lt_mul_of_pos_left hlt Real.pi_pos
      linarith
    have hpos : 0 < Real.pi * (coprimeSixSeq a : ℝ) / 3 := by
      have := coprimeSixSeq_pos a; positivity
    nlinarith
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun k => by
    simpa using inv_ne_zero (deriv_two_coshSqrt_sub_one_ne_zero k)
  analyticOn := by
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hz' := hz.2
    rw [exp_neg_I_pi] at hz'
    have hne : 2 * coshSqrt z - 1 ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := (two_coshSqrt_sub_one_eq_zero_iff z).mp h0
      exact hz' ⟨k, by rw [hk]; ring⟩
    exact ((analyticAt_const.mul (coshSqrt_analyticAt z)).sub analyticAt_const).inv hne
  pole_principalPart := fun k => by
    have hpole : Complex.exp (I * (Real.pi : ℂ)) * (mockThetaOmegaFreq k : ℂ) =
        -(mockThetaOmegaFreq k : ℂ) := by rw [exp_I_pi]; ring
    rw [hpole]
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one]
    have hzero : 2 * coshSqrt (-(mockThetaOmegaFreq k : ℂ)) - 1 = 0 :=
      (two_coshSqrt_sub_one_eq_zero_iff _).mpr ⟨k, rfl⟩
    have hD_an : AnalyticAt ℂ (fun z => 2 * coshSqrt z - 1) (-(mockThetaOmegaFreq k : ℂ)) :=
      (analyticAt_const.mul (coshSqrt_analyticAt _)).sub analyticAt_const
    have hlim := simple_pole_tendsto_of_analytic (N := fun _ => (1 : ℂ)) analyticAt_const hD_an hzero
      (deriv_two_coshSqrt_sub_one_ne_zero k)
    simpa [mockThetaOmegaBorel, one_div] using hlim
  expType_plus := by
    have hfun : mockThetaOmegaBorel = fun z => (1 : ℂ) / (2 * coshSqrt z - 1) := funext fun z => by
      simp [mockThetaOmegaBorel, one_div]
    rw [hfun]
    refine expType_div_of_flank_bound (norm_exp_I_real _)
      (((continuous_const.mul coshSqrt_differentiable.continuous).sub continuous_const).comp
        (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num)
      (fun v _ => by simp)
    · obtain ⟨k, hk⟩ := (two_coshSqrt_sub_one_eq_zero_iff _).mp h0
      have him := congrArg Complex.im hk
      have hpos : 0 < mockThetaOmegaFreq k := by
        unfold mockThetaOmegaFreq; have := coprimeSixSeq_pos k; positivity
      have hv_ne : v ≠ 0 := by
        intro hv0; rw [hv0, Complex.ofReal_zero, mul_zero] at hk
        exact hpos.ne' (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hk.symm))
      have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        mul_comm I, Complex.exp_ofReal_mul_I_im, add_comm Real.pi (Real.pi / 3),
        Real.sin_add_pi, Real.sin_pi_div_three] at him
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero] at him
      have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_ray 1 (Or.inl rfl) (by linarith : 0 ≤ v)
      rw [show Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
        simpa using hw_sq.symm, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith)
        linarith
      have htri := norm_add_le (2 * Complex.cosh w - 1) (1 : ℂ)
      rw [sub_add_cancel, norm_mul, Complex.norm_ofNat, norm_one] at htri
      have hs : Real.sinh 2 ≤ Real.sinh w.re := real_sinh_mono hge2
      linarith [real_sinh_two_gt_two, sinh_re_le_norm_cosh w]
  expType_minus := by
    have hfun : mockThetaOmegaBorel = fun z => (1 : ℂ) / (2 * coshSqrt z - 1) := funext fun z => by
      simp [mockThetaOmegaBorel, one_div]
    rw [hfun]
    refine expType_div_of_flank_bound (norm_exp_I_real _)
      (((continuous_const.mul coshSqrt_differentiable.continuous).sub continuous_const).comp
        (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num)
      (fun v _ => by simp)
    · obtain ⟨k, hk⟩ := (two_coshSqrt_sub_one_eq_zero_iff _).mp h0
      have him := congrArg Complex.im hk
      have hpos : 0 < mockThetaOmegaFreq k := by
        unfold mockThetaOmegaFreq; have := coprimeSixSeq_pos k; positivity
      have hv_ne : v ≠ 0 := by
        intro hv0; rw [hv0, Complex.ofReal_zero, mul_zero] at hk
        exact hpos.ne' (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hk.symm))
      have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        mul_comm I, Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub, Real.sin_pi_div_three] at him
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero] at him
      have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_ray (-1) (Or.inr rfl) (by linarith : 0 ≤ v)
      rw [show Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
        have : Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
        rw [← this]; exact hw_sq.symm, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith)
        linarith
      have htri := norm_add_le (2 * Complex.cosh w - 1) (1 : ℂ)
      rw [sub_add_cancel, norm_mul, Complex.norm_ofNat, norm_one] at htri
      have hs : Real.sinh 2 ≤ Real.sinh w.re := real_sinh_mono hge2
      linarith [real_sinh_two_gt_two, sinh_re_le_norm_cosh w]

private lemma mockThetaOmegaBorel_real_bound (ξ : ℝ) (hξ : 0 ≤ ξ) :
    ‖mockThetaOmegaBorel (ξ : ℂ)‖ ≤ 1 := by
  unfold mockThetaOmegaBorel
  have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
  rw [← hsq, coshSqrt_sq, ← Complex.ofReal_cosh, norm_inv]
  have hge : (1 : ℝ) ≤ 2 * Real.cosh (Real.sqrt ξ) - 1 := by linarith [real_one_le_cosh (Real.sqrt ξ)]
  have hcast : (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) - 1 = ((2 * Real.cosh (Real.sqrt ξ) - 1 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  exact inv_le_one_of_one_le₀ hge

private lemma mockThetaOmegaBorel_cont :
    ContinuousOn (fun ξ : ℝ => mockThetaOmegaBorel (ξ : ℂ)) (Set.Ici 0) := by
  intro ξ hξ
  have hne : 2 * coshSqrt (ξ : ℂ) - 1 ≠ 0 := by
    have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
    rw [← hsq, coshSqrt_sq, ← Complex.ofReal_cosh]
    have hcast : (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) - 1 = ((2 * Real.cosh (Real.sqrt ξ) - 1 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr (by linarith [real_one_le_cosh (Real.sqrt ξ)])
  exact (((analyticAt_const.mul (coshSqrt_analyticAt (ξ : ℂ))).sub analyticAt_const).inv hne).continuousAt.comp
    Complex.continuous_ofReal.continuousAt |>.continuousWithinAt

/-- **Theorem B (Ramanujan's 3rd-Order Mock Theta `ω(q)` Mordell Integral D-Transcendence over `ℂ(u)`)**:
The exact `ω(q)` Mordell integral `∫_0^∞ e^{-u x^2} (x cosh(x/2) / cosh(3x/2)) dx` satisfies NO
nonzero rational-coefficient differential equation over `ℂ(u)`. -/
theorem mockThetaOmega_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val mockThetaOmegaMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (mordellIntegral mockThetaOmegaBorel) u)
        (evalRatU P (u : ℂ)) = 0 := by
    simpa only [show mockThetaOmegaMordell = mordellIntegral mockThetaOmegaBorel from
      funext mockThetaOmegaMordell_eq] using hP
  have hana0 : AnalyticAt ℂ mockThetaOmegaBorel 0 := by
    have h0 : 2 * coshSqrt 0 - 1 ≠ 0 := by
      have : coshSqrt ((0 : ℂ) ^ 2) = Complex.cosh 0 := coshSqrt_sq 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.cosh_zero] at this
      rw [this]; norm_num
    exact ((analyticAt_const.mul (coshSqrt_analyticAt 0)).sub analyticAt_const).inv h0
  exact mordellIntegral_no_rat_ade mockThetaOmega_borelData hana0 mockThetaOmegaBorel_cont
    mockThetaOmegaBorel_real_bound P hP'

/-! #### 3C. Ramanujan's 3rd-Order Mock Theta `f(q)` Mordell Integral -/

/-- Borel kernel of Ramanujan's 3rd-order mock theta `f(q)`:
`g_f(z) = 2 cosh(√z / 2) / (2 cosh(√z) + 1)`, satisfying `g_f(x^2) = sinh(x) / sinh(3x/2)`. -/
@[expose] def mockThetaFBorel (z : ℂ) : ℂ := 2 * coshSqrt (z / 4) / (2 * coshSqrt z + 1)

/-- Strictly increasing sequence `1, 2, 4, 5, 7, 8, ...` (`3 ∤ k_m`). -/
@[expose] def coprimeThreeSeq (m : ℕ) : ℕ := 3 * (m / 2) + if m % 2 = 0 then 1 else 2

/-- Pole frequencies `ω_m = (2 π k_m / 3)^2` (`3 ∤ k_m`) of `g_f(z)`. -/
@[expose] def mockThetaFFreq (m : ℕ) : ℝ := (2 * Real.pi * (coprimeThreeSeq m : ℝ) / 3) ^ 2

/-- Ramanujan's 3rd-order mock theta `f(q)` Mordell integral
`∫_0^∞ e^{-u x^2} (x sinh(x) / sinh(3x/2)) dx`. -/
@[expose] def mockThetaFMordell (u : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) *
    Complex.sinh (x : ℂ) / Complex.sinh (3 * (x : ℂ) / 2)

private lemma sinh_double_triple_identity (a : ℂ) :
    Complex.sinh (2 * a) = Complex.sinh a * (2 * Complex.cosh a) ∧
    Complex.sinh (3 * a) = Complex.sinh a * (2 * Complex.cosh (2 * a) + 1) := by
  have h1 : Complex.exp (3 * a) = Complex.exp a ^ 3 := by
    rw [← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : Complex.exp (-(3 * a)) = Complex.exp (-a) ^ 3 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Complex.exp (2 * a) = Complex.exp a ^ 2 := by
    rw [← Complex.exp_nat_mul]; push_cast; rfl
  have h4 : Complex.exp (-(2 * a)) = Complex.exp (-a) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hprod : Complex.exp a * Complex.exp (-a) = 1 := by
    rw [← Complex.exp_add]; simp
  constructor
  · rw [Complex.sinh, Complex.sinh, Complex.cosh, h3, h4]; ring
  · rw [Complex.sinh, Complex.sinh, Complex.cosh, h1, h2, h3, h4]
    linear_combination (Complex.exp a - Complex.exp (-a)) / 2 * hprod

lemma mockThetaFMordell_eq (u : ℝ) :
    mockThetaFMordell u = mordellIntegral mockThetaFBorel u := by
  unfold mockThetaFMordell mordellIntegral mockThetaFBorel
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hsq4 : ((x : ℂ) / 2) ^ 2 = (x : ℂ) ^ 2 / 4 := by ring
  rw [← hsq4, coshSqrt_sq, coshSqrt_sq]
  have h2 : (x : ℂ) = 2 * ((x : ℂ) / 2) := by ring
  have h3 : 3 * (x : ℂ) / 2 = 3 * ((x : ℂ) / 2) := by ring
  obtain ⟨hd, ht⟩ := sinh_double_triple_identity ((x : ℂ) / 2)
  rw [h3, ht, ← h2]
  conv_lhs => rw [h2, hd]
  have hs : Complex.sinh ((x : ℂ) / 2) ≠ 0 := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sinh]
    exact Complex.ofReal_ne_zero.mpr (real_sinh_pos_of_pos (by linarith [Set.mem_Ioi.mp hx])).ne'
  field_simp [hs]

private lemma coprimeThreeSeq_strictMono : StrictMono coprimeThreeSeq := by
  intro a b hab; unfold coprimeThreeSeq; split_ifs <;> omega

private lemma coprimeThreeSeq_pos (m : ℕ) : 0 < coprimeThreeSeq m := by
  unfold coprimeThreeSeq; split_ifs <;> omega

private lemma coprimeThreeSeq_mod_three (m : ℕ) : coprimeThreeSeq m % 3 ≠ 0 := by
  unfold coprimeThreeSeq; split_ifs <;> omega

private lemma exists_coprimeThreeSeq_of_mod_three (k : ℤ) (hk : k % 3 = 1 ∨ k % 3 = 2) :
    ∃ m : ℕ, (coprimeThreeSeq m : ℤ) = |k| := by
  have hnat : k.natAbs % 3 = 1 ∨ k.natAbs % 3 = 2 := by omega
  rcases hnat with h1 | h2
  · refine ⟨2 * (k.natAbs / 3), ?_⟩
    unfold coprimeThreeSeq
    have hdiv : (2 * (k.natAbs / 3)) / 2 = k.natAbs / 3 := by omega
    have hmod : (2 * (k.natAbs / 3)) % 2 = 0 := by omega
    rw [hdiv, hmod, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    have hnat_eq : 3 * (k.natAbs / 3) + 1 = k.natAbs := by omega
    rw [hnat_eq, Int.natCast_natAbs]
  · refine ⟨2 * (k.natAbs / 3) + 1, ?_⟩
    unfold coprimeThreeSeq
    have hdiv : (2 * (k.natAbs / 3) + 1) / 2 = k.natAbs / 3 := by omega
    have hmod : (2 * (k.natAbs / 3) + 1) % 2 = 1 := by omega
    rw [hdiv, hmod, ite_eq_right_iff.mpr (fun h => by omega)]
    have hnat_eq : 3 * (k.natAbs / 3) + 2 = k.natAbs := by omega
    rw [hnat_eq, Int.natCast_natAbs]

private lemma two_coshSqrt_add_one_eq_zero_iff (z : ℂ) :
    2 * coshSqrt z + 1 = 0 ↔ ∃ m : ℕ, z = -(mockThetaFFreq m : ℂ) := by
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := exists_sq_eq z
    rw [coshSqrt_sq, Complex.cosh] at hz
    have hsum : Complex.exp w + Complex.exp (-w) = -1 := by linear_combination hz
    have hprod : Complex.exp w * Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
    have hquad : Complex.exp w ^ 2 + Complex.exp w + 1 = 0 := by
      linear_combination Complex.exp w * hsum - hprod
    let ζ : ℂ := Complex.exp (I * ((2 * Real.pi / 3 : ℝ) : ℂ))
    have hζ_sum : ζ + ζ⁻¹ = -1 := by
      dsimp only [ζ]
      rw [← Complex.exp_neg]
      have h1 : Complex.exp (I * ((2 * Real.pi / 3 : ℝ) : ℂ)) +
          Complex.exp (-(I * ((2 * Real.pi / 3 : ℝ) : ℂ))) =
          2 * Complex.cos ((2 * Real.pi / 3 : ℝ) : ℂ) := by
        rw [Complex.cos]
        have he1 : I * ((2 * Real.pi / 3 : ℝ) : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * I := by ring
        rw [he1, ← neg_mul]; ring
      rw [h1, ← Complex.ofReal_cos,
        show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
      push_cast; ring
    have hζ_prod : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ (Complex.exp_ne_zero _)
    have hfac : (Complex.exp w - ζ) * (Complex.exp w - ζ⁻¹) = 0 := by
      linear_combination hquad - Complex.exp w * hζ_sum + hζ_prod
    rcases mul_eq_zero.mp hfac with hL | hR
    · have hexp : Complex.exp w = Complex.exp (I * ((2 * Real.pi / 3 : ℝ) : ℂ)) := sub_eq_zero.mp hL
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨j, hj⟩ := hexp
      let k : ℤ := 3 * j + 1
      have hw : w = I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ) := by
        dsimp only [k]; rw [hj]; push_cast; ring
      obtain ⟨m, hm⟩ := exists_coprimeThreeSeq_of_mod_three k (Or.inl (by omega))
      refine ⟨m, ?_⟩
      rw [hw, mockThetaFFreq]
      have hsq_k : ((coprimeThreeSeq m : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by
        have h1 : (coprimeThreeSeq m : ℝ) = |(k : ℝ)| := by exact_mod_cast hm
        rw [h1, sq_abs]
      have hsq_kC : (coprimeThreeSeq m : ℂ) ^ 2 = (k : ℂ) ^ 2 := by exact_mod_cast hsq_k
      have hLHS : (I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ)) ^ 2 =
          -(2 * (Real.pi : ℂ) * (k : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast
      linear_combination -(4 * (Real.pi : ℂ) ^ 2 / 9) * hsq_kC.symm
    · have hexp : Complex.exp w = Complex.exp (-(I * ((2 * Real.pi / 3 : ℝ) : ℂ))) := by
        rw [Complex.exp_neg]; exact sub_eq_zero.mp hR
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨j, hj⟩ := hexp
      let k : ℤ := 3 * j - 1
      have hw : w = I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ) := by
        dsimp only [k]; rw [hj]; push_cast; ring
      obtain ⟨m, hm⟩ := exists_coprimeThreeSeq_of_mod_three k (Or.inr (by omega))
      refine ⟨m, ?_⟩
      rw [hw, mockThetaFFreq]
      have hsq_k : ((coprimeThreeSeq m : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by
        have h1 : (coprimeThreeSeq m : ℝ) = |(k : ℝ)| := by exact_mod_cast hm
        rw [h1, sq_abs]
      have hsq_kC : (coprimeThreeSeq m : ℂ) ^ 2 = (k : ℂ) ^ 2 := by exact_mod_cast hsq_k
      have hLHS : (I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ)) ^ 2 =
          -(2 * (Real.pi : ℂ) * (k : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast
      linear_combination -(4 * (Real.pi : ℂ) ^ 2 / 9) * hsq_kC.symm
  · rintro ⟨m, rfl⟩
    let r : ℝ := 2 * Real.pi * (coprimeThreeSeq m : ℝ) / 3
    have hsq : (I * (r : ℂ)) ^ 2 = -(mockThetaFFreq m : ℂ) := by
      rw [mockThetaFFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [← hsq, coshSqrt_sq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I,
      ← Complex.ofReal_cos]
    have hcos : Real.cos r = -(1 / 2) := by
      dsimp only [r, coprimeThreeSeq]
      split_ifs with hmod
      · rw [show 2 * Real.pi * ((3 * (m / 2) + 1 : ℕ) : ℝ) / 3 =
            (Real.pi - Real.pi / 3) + ((m / 2 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
        rw [Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub, Real.cos_pi_div_three]
      · rw [show 2 * Real.pi * ((3 * (m / 2) + 2 : ℕ) : ℝ) / 3 =
            -(Real.pi - Real.pi / 3) + ((m / 2 + 1 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
        rw [Real.cos_add_nat_mul_two_pi, Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [hcos]; push_cast; ring

private lemma deriv_two_coshSqrt_add_one_ne_zero (m : ℕ) :
    deriv (fun z => 2 * coshSqrt z + 1) (-(mockThetaFFreq m : ℂ)) ≠ 0 := by
  let z₀ : ℂ := -(mockThetaFFreq m : ℂ)
  have hd_eq : deriv (fun z => 2 * coshSqrt z + 1) z₀ = 2 * deriv coshSqrt z₀ :=
    (((coshSqrt_differentiable z₀).hasDerivAt.const_mul (2 : ℂ)).add_const (1 : ℂ)).deriv
  rw [hd_eq]
  refine mul_ne_zero (by norm_num) ?_
  let r : ℝ := 2 * Real.pi * (coprimeThreeSeq m : ℝ) / 3
  have hsq : (I * (r : ℂ)) ^ 2 = z₀ := by
    dsimp only [z₀, r]; rw [mockThetaFFreq]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hd := deriv_coshSqrt_sq (I * (r : ℂ))
  rw [hsq] at hd
  intro h0
  rw [h0, mul_zero] at hd
  have hsinh : Complex.sinh (I * (r : ℂ)) = (Real.sin r : ℂ) * I := by
    rw [show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.sinh_mul_I, Complex.ofReal_sin]
  rw [hsinh] at hd
  have hsin0 : Real.sin r = 0 := by
    have : (Real.sin r : ℂ) = 0 := (mul_eq_zero.mp hd.symm).resolve_right Complex.I_ne_zero
    exact Complex.ofReal_eq_zero.mp this
  obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hsin0
  have h3j : 3 * j = 2 * (coprimeThreeSeq m : ℤ) := by
    have : (j : ℝ) * Real.pi = 2 * Real.pi * (coprimeThreeSeq m : ℝ) / 3 := hj
    have hreal : ((3 * j : ℤ) : ℝ) = ((2 * (coprimeThreeSeq m : ℤ) : ℤ) : ℝ) := by
      push_cast; nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  have hmod := coprimeThreeSeq_mod_three m
  omega

private lemma mockThetaF_num_ne_zero (m : ℕ) :
    2 * coshSqrt (-(mockThetaFFreq m : ℂ) / 4) ≠ 0 := by
  refine mul_ne_zero (by norm_num) ?_
  let r : ℝ := Real.pi * (coprimeThreeSeq m : ℝ) / 3
  have hsq : (I * (r : ℂ)) ^ 2 = -(mockThetaFFreq m : ℂ) / 4 := by
    rw [mockThetaFFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [← hsq, coshSqrt_sq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I,
    ← Complex.ofReal_cos, ne_eq, Complex.ofReal_eq_zero]
  intro hcos0
  obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.mp hcos0
  have h2k : 2 * (coprimeThreeSeq m : ℤ) = 3 * (2 * j + 1) := by
    have hreal : ((2 * (coprimeThreeSeq m : ℤ) : ℤ) : ℝ) = ((3 * (2 * j + 1) : ℤ) : ℝ) := by
      push_cast
      have h1 : Real.pi * (coprimeThreeSeq m : ℝ) / 3 = (2 * (j : ℝ) + 1) * Real.pi / 2 := by
        dsimp only [r] at hj; exact hj
      nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  have hmod := coprimeThreeSeq_mod_three m
  omega

private lemma mockThetaF_num_analyticAt (z : ℂ) :
    AnalyticAt ℂ (fun ζ => 2 * coshSqrt (ζ / 4)) z := by
  have hcomp : AnalyticAt ℂ (fun ζ => coshSqrt (ζ / 4)) z :=
    AnalyticAt.comp (f := fun ζ : ℂ => ζ / 4) (g := coshSqrt)
      (coshSqrt_analyticAt (z / 4)) (analyticAt_id.div analyticAt_const (by norm_num))
  exact analyticAt_const.mul hcomp

/-- Concrete `HigherOrderBorelData` witness for Ramanujan's 3rd-order mock theta `f(q)`
Borel kernel `2 cosh(√z / 2) / (2 cosh(√z) + 1)` along `θ₀ = π`. -/
def mockThetaF_borelData :
    HigherOrderBorelData mockThetaFBorel Real.pi mockThetaFFreq (fun _ => 1)
      (fun m s => if s = 1 then
        (2 * coshSqrt (-(mockThetaFFreq m : ℂ) / 4)) /
          deriv (fun z => 2 * coshSqrt z + 1) (-(mockThetaFFreq m : ℂ)) else 0) where
  α₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by
    unfold mockThetaFFreq
    have := coprimeThreeSeq_pos 0
    positivity
  ω_mono := fun a b hab => by
    unfold mockThetaFFreq
    have hlt : (coprimeThreeSeq a : ℝ) < (coprimeThreeSeq b : ℝ) := by
      exact_mod_cast coprimeThreeSeq_strictMono hab
    have hlt' : 2 * Real.pi * (coprimeThreeSeq a : ℝ) / 3 <
        2 * Real.pi * (coprimeThreeSeq b : ℝ) / 3 := by
      have : Real.pi * (coprimeThreeSeq a : ℝ) < Real.pi * (coprimeThreeSeq b : ℝ) :=
        mul_lt_mul_of_pos_left hlt Real.pi_pos
      linarith
    have hpos : 0 < 2 * Real.pi * (coprimeThreeSeq a : ℝ) / 3 := by
      have := coprimeThreeSeq_pos a; positivity
    nlinarith
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by
    simpa using div_ne_zero (mockThetaF_num_ne_zero m) (deriv_two_coshSqrt_add_one_ne_zero m)
  analyticOn := by
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hz' := hz.2
    rw [exp_neg_I_pi] at hz'
    have hne : 2 * coshSqrt z + 1 ≠ 0 := by
      intro h0
      obtain ⟨m, hm⟩ := (two_coshSqrt_add_one_eq_zero_iff z).mp h0
      exact hz' ⟨m, by rw [hm]; ring⟩
    have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt ζ + 1) z :=
      (analyticAt_const.mul (coshSqrt_analyticAt z)).add analyticAt_const
    exact (mockThetaF_num_analyticAt z).div hD hne
  pole_principalPart := fun m => by
    have hpole : Complex.exp (I * (Real.pi : ℂ)) * (mockThetaFFreq m : ℂ) =
        -(mockThetaFFreq m : ℂ) := by rw [exp_I_pi]; ring
    rw [hpole]
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one]
    have hzero : 2 * coshSqrt (-(mockThetaFFreq m : ℂ)) + 1 = 0 :=
      (two_coshSqrt_add_one_eq_zero_iff _).mpr ⟨m, rfl⟩
    have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt ζ + 1) (-(mockThetaFFreq m : ℂ)) :=
      (analyticAt_const.mul (coshSqrt_analyticAt _)).add analyticAt_const
    exact simple_pole_tendsto_of_analytic (mockThetaF_num_analyticAt _) hD hzero
      (deriv_two_coshSqrt_add_one_ne_zero m)
  expType_plus := by
    refine expType_div_of_flank_bound (norm_exp_I_real _)
      (((continuous_const.mul coshSqrt_differentiable.continuous).add continuous_const).comp
        (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 2 * Real.exp 1) (B := 1)
      (by positivity) (by norm_num) (fun v hv => ?_)
    · obtain ⟨m, hm⟩ := (two_coshSqrt_add_one_eq_zero_iff _).mp h0
      have him := congrArg Complex.im hm
      have hpos : 0 < mockThetaFFreq m := by
        unfold mockThetaFFreq; have := coprimeThreeSeq_pos m; positivity
      have hv_ne : v ≠ 0 := by
        intro hv0; rw [hv0, Complex.ofReal_zero, mul_zero] at hm
        exact hpos.ne' (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hm.symm))
      have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        mul_comm I, Complex.exp_ofReal_mul_I_im, add_comm Real.pi (Real.pi / 3),
        Real.sin_add_pi, Real.sin_pi_div_three] at him
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero] at him
      have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_ray 1 (Or.inl rfl) (by linarith : 0 ≤ v)
      rw [show Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
        simpa using hw_sq.symm, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith)
        linarith
      have htri := norm_sub_le (2 * Complex.cosh w + 1) (1 : ℂ)
      rw [add_sub_cancel_right, norm_mul, Complex.norm_ofNat, norm_one] at htri
      have hs : Real.sinh 2 ≤ Real.sinh w.re := real_sinh_mono hge2
      linarith [real_sinh_two_gt_two, sinh_re_le_norm_cosh w]
    · obtain ⟨w, hw_sq, _, hw_norm⟩ := exists_sqrt_on_flank_ray 1 (Or.inl rfl) hv
      have hsq4 : (w / 2) ^ 2 =
          Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) / 4 := by
        rw [div_pow, show (2 : ℂ) ^ 2 = 4 by norm_num, hw_sq]; simp
      rw [← hsq4, coshSqrt_sq, norm_mul, Complex.norm_ofNat, Complex.cosh, norm_div,
        Complex.norm_ofNat]
      have h1 : ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ ≤
          2 * Real.exp (‖w‖ / 2) := by
        calc ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖
            ≤ ‖Complex.exp (w / 2)‖ + ‖Complex.exp (-(w / 2))‖ := norm_add_le _ _
          _ = Real.exp (w / 2).re + Real.exp (-(w / 2)).re := by rw [Complex.norm_exp, Complex.norm_exp]
          _ ≤ Real.exp ‖w / 2‖ + Real.exp ‖-(w / 2)‖ :=
              add_le_add (Real.exp_le_exp.mpr (Complex.re_le_norm _))
                (Real.exp_le_exp.mpr (Complex.re_le_norm _))
          _ = 2 * Real.exp (‖w‖ / 2) := by rw [norm_neg, norm_div, Complex.norm_ofNat]; ring
      have hsq_le : Real.sqrt v / 2 ≤ 1 + v := by
        have hsqv : (Real.sqrt v - 1) ^ 2 ≥ 0 := sq_nonneg _
        nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
      calc 2 * (‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ / 2)
          = ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ := by ring
        _ ≤ 2 * Real.exp (‖w‖ / 2) := h1
        _ = 2 * Real.exp (Real.sqrt v / 2) := by rw [hw_norm]
        _ ≤ 2 * Real.exp (1 + v) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq_le) (by norm_num)
        _ = 2 * Real.exp 1 * Real.exp (1 * v) := by rw [Real.exp_add, one_mul]; ring
  expType_minus := by
    refine expType_div_of_flank_bound (norm_exp_I_real _)
      (((continuous_const.mul coshSqrt_differentiable.continuous).add continuous_const).comp
        (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 2 * Real.exp 1) (B := 1)
      (by positivity) (by norm_num) (fun v hv => ?_)
    · obtain ⟨m, hm⟩ := (two_coshSqrt_add_one_eq_zero_iff _).mp h0
      have him := congrArg Complex.im hm
      have hpos : 0 < mockThetaFFreq m := by
        unfold mockThetaFFreq; have := coprimeThreeSeq_pos m; positivity
      have hv_ne : v ≠ 0 := by
        intro hv0; rw [hv0, Complex.ofReal_zero, mul_zero] at hm
        exact hpos.ne' (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hm.symm))
      have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        mul_comm I, Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub, Real.sin_pi_div_three] at him
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero] at him
      have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_ray (-1) (Or.inr rfl) (by linarith : 0 ≤ v)
      rw [show Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
        have : Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
        rw [← this]; exact hw_sq.symm, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith)
        linarith
      have htri := norm_sub_le (2 * Complex.cosh w + 1) (1 : ℂ)
      rw [add_sub_cancel_right, norm_mul, Complex.norm_ofNat, norm_one] at htri
      have hs : Real.sinh 2 ≤ Real.sinh w.re := real_sinh_mono hge2
      linarith [real_sinh_two_gt_two, sinh_re_le_norm_cosh w]
    · obtain ⟨w, hw_sq, _, hw_norm⟩ := exists_sqrt_on_flank_ray (-1) (Or.inr rfl) hv
      have hsq4 : (w / 2) ^ 2 =
          Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) / 4 := by
        rw [div_pow, show (2 : ℂ) ^ 2 = 4 by norm_num, hw_sq]
        have : Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
        rw [this]
      rw [← hsq4, coshSqrt_sq, norm_mul, Complex.norm_ofNat, Complex.cosh, norm_div,
        Complex.norm_ofNat]
      have h1 : ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ ≤
          2 * Real.exp (‖w‖ / 2) := by
        calc ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖
            ≤ ‖Complex.exp (w / 2)‖ + ‖Complex.exp (-(w / 2))‖ := norm_add_le _ _
          _ = Real.exp (w / 2).re + Real.exp (-(w / 2)).re := by rw [Complex.norm_exp, Complex.norm_exp]
          _ ≤ Real.exp ‖w / 2‖ + Real.exp ‖-(w / 2)‖ :=
              add_le_add (Real.exp_le_exp.mpr (Complex.re_le_norm _))
                (Real.exp_le_exp.mpr (Complex.re_le_norm _))
          _ = 2 * Real.exp (‖w‖ / 2) := by rw [norm_neg, norm_div, Complex.norm_ofNat]; ring
      have hsq_le : Real.sqrt v / 2 ≤ 1 + v := by
        have hsqv : (Real.sqrt v - 1) ^ 2 ≥ 0 := sq_nonneg _
        nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
      calc 2 * (‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ / 2)
          = ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ := by ring
        _ ≤ 2 * Real.exp (‖w‖ / 2) := h1
        _ = 2 * Real.exp (Real.sqrt v / 2) := by rw [hw_norm]
        _ ≤ 2 * Real.exp (1 + v) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq_le) (by norm_num)
        _ = 2 * Real.exp 1 * Real.exp (1 * v) := by rw [Real.exp_add, one_mul]; ring

private lemma mockThetaFBorel_real_bound (ξ : ℝ) (hξ : 0 ≤ ξ) :
    ‖mockThetaFBorel (ξ : ℂ)‖ ≤ 1 := by
  unfold mockThetaFBorel
  have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
  have hsq4 : (((Real.sqrt ξ / 2 : ℝ) : ℂ)) ^ 2 = (ξ : ℂ) / 4 := by
    rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt hξ]; push_cast; norm_num
  rw [← hsq4, ← hsq, coshSqrt_sq, coshSqrt_sq, ← Complex.ofReal_cosh, ← Complex.ofReal_cosh]
  have hnum : (2 : ℂ) * (Real.cosh (Real.sqrt ξ / 2) : ℂ) = ((2 * Real.cosh (Real.sqrt ξ / 2) : ℝ) : ℂ) := by
    push_cast; rfl
  have hden : (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) + 1 = ((2 * Real.cosh (Real.sqrt ξ) + 1 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hnum, hden, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by linarith [Real.cosh_pos (Real.sqrt ξ)])]
  rw [div_le_one (by linarith [Real.cosh_pos (Real.sqrt ξ)])]
  have hmono : Real.cosh (Real.sqrt ξ / 2) ≤ Real.cosh (Real.sqrt ξ) :=
    real_cosh_mono_nonneg (by positivity) (by linarith [Real.sqrt_nonneg ξ])
  linarith

private lemma mockThetaFBorel_cont :
    ContinuousOn (fun ξ : ℝ => mockThetaFBorel (ξ : ℂ)) (Set.Ici 0) := by
  intro ξ hξ
  have hne : 2 * coshSqrt (ξ : ℂ) + 1 ≠ 0 := by
    have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
    rw [← hsq, coshSqrt_sq, ← Complex.ofReal_cosh]
    have hcast : (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) + 1 = ((2 * Real.cosh (Real.sqrt ξ) + 1 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr (by linarith [Real.cosh_pos (Real.sqrt ξ)])
  have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt ζ + 1) (ξ : ℂ) :=
    (analyticAt_const.mul (coshSqrt_analyticAt (ξ : ℂ))).add analyticAt_const
  exact ((mockThetaF_num_analyticAt (ξ : ℂ)).div hD hne).continuousAt.comp
    Complex.continuous_ofReal.continuousAt |>.continuousWithinAt

/-- **Theorem C (Ramanujan's 3rd-Order Mock Theta `f(q)` Mordell Integral D-Transcendence over `ℂ(u)`)**:
The exact `f(q)` Mordell integral `∫_0^∞ e^{-u x^2} (x sinh(x) / sinh(3x/2)) dx` satisfies NO
nonzero rational-coefficient differential equation over `ℂ(u)`. -/
theorem mockThetaF_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val mockThetaFMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (mordellIntegral mockThetaFBorel) u)
        (evalRatU P (u : ℂ)) = 0 := by
    simpa only [show mockThetaFMordell = mordellIntegral mockThetaFBorel from
      funext mockThetaFMordell_eq] using hP
  have hana0 : AnalyticAt ℂ mockThetaFBorel 0 := by
    have h0 : 2 * coshSqrt 0 + 1 ≠ 0 := by
      have : coshSqrt ((0 : ℂ) ^ 2) = Complex.cosh 0 := coshSqrt_sq 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.cosh_zero] at this
      rw [this]; norm_num
    have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt ζ + 1) 0 :=
      (analyticAt_const.mul (coshSqrt_analyticAt 0)).add analyticAt_const
    exact (mockThetaF_num_analyticAt 0).div hD h0
  exact mordellIntegral_no_rat_ade mockThetaF_borelData hana0 mockThetaFBorel_cont
    mockThetaFBorel_real_bound P hP'

/-! ### 4. Zagier's Hurwitz Class-Number Shadow `ϑ₃(τ) - 1 = 2 ∑_{k ≥ 1} q^{k²}` -/

/-- Exact `n`-th Fourier coefficient (`q^{n+1}`) of the Jacobi theta shadow
`ϑ₃(τ) - 1 = 2 ∑_{k ≥ 1} q^{k²}` of Zagier's Hurwitz class-number generating function `H(q)`. -/
@[expose] def jacobiThetaCoeff (n : ℕ) : ℂ :=
  if IsSquare (n + 1) then 2 else 0

private lemma jacobiThetaCoeff_sq (k : ℕ) : jacobiThetaCoeff ((k + 1) ^ 2 - 1) = 2 := by
  unfold jacobiThetaCoeff
  have h1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow 2 (k + 1) (Nat.succ_pos k)
  have hadd : (k + 1) ^ 2 - 1 + 1 = (k + 1) ^ 2 := Nat.sub_add_cancel h1
  rw [hadd, ite_eq_left_iff.mpr (fun h => absurd ⟨k + 1, sq (k + 1)⟩ h)]

private lemma jacobiThetaCoeff_summable :
    Summable (fun n : ℕ => ‖jacobiThetaCoeff n‖ * Real.exp (-freq n)) := by
  refine summable_of_poly_bound (C := 2) (d := 0) fun n => ?_
  simp only [pow_zero, mul_one, jacobiThetaCoeff]
  split_ifs <;> norm_num

private lemma jacobiThetaCoeff_infinite : {n : ℕ | jacobiThetaCoeff n ≠ 0}.Infinite := by
  refine infinite_support_of_subseq (fun k => (k + 1) ^ 2 - 1) ?_ fun k => ?_
  · intro a b hab
    have h1 : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow 2 (a + 1) (Nat.succ_pos a)
    have hlt : (a + 1) ^ 2 < (b + 1) ^ 2 := Nat.pow_lt_pow_left (Nat.succ_lt_succ hab) (by norm_num)
    exact Nat.sub_lt_sub_right h1 hlt
  · rw [jacobiThetaCoeff_sq]; norm_num

/-- Concrete `HigherOrderBorelData` witness for Zagier's Hurwitz class-number shadow
`ϑ₃(τ) - 1 = 2 ∑_{k ≥ 1} q^{k²}` along `θ₀ = π`. -/
def hurwitzThetaShadow_borelData :
    HigherOrderBorelData (eichlerBorel jacobiThetaCoeff) Real.pi (poleFreq jacobiThetaCoeff)
      (fun _ => 1) (fun k s => if s = 1 then jacobiThetaCoeff (suppIdx jacobiThetaCoeff k) else 0) :=
  eichlerWeightOne_borelData jacobiThetaCoeff jacobiThetaCoeff_summable jacobiThetaCoeff_infinite

/-- **Theorem D (Zagier's Hurwitz Class-Number Shadow `ϑ₃(τ) - 1` D-Transcendence over `ℂ(u)`)**:
The split Eichler integral `eichlerIntegral jacobiThetaCoeff` of `ϑ₃(τ) - 1 = 2 ∑_{k ≥ 1} q^{k²}`
satisfies NO nonzero rational-coefficient differential equation over `ℂ(u)`. -/
theorem hurwitzThetaShadow_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral jacobiThetaCoeff) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  eichlerWeightOne_no_rat_ade jacobiThetaCoeff jacobiThetaCoeff_summable jacobiThetaCoeff_infinite P hP

/-- Formal Borel-level D-transcendence over `ℂ(u)` for Zagier's Hurwitz theta shadow. -/
theorem hurwitzThetaShadow_formal_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (eichlerBorel jacobiThetaCoeff)) P = 0) : P = 0 :=
  eichlerWeightOne_formal_no_rat_ade jacobiThetaCoeff jacobiThetaCoeff_summable
    jacobiThetaCoeff_infinite P hP

/-! ### 5. Modular D-Algebraic Controls (Modular vs. Mock Dichotomy) -/

/-- **Control 1 (Exponential / Theta-Mode D-Algebraicity)**:
`f(u) = e^{-u}` IS differentially algebraic over `ℂ` (and `ℂ(u)`), annihilated by the nonzero
order-1 autonomous differential polynomial `P = Y₁ + Y₀`. -/
theorem expNeg_is_d_algebraic :
    ∃ (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ), P ≠ 0 ∧
      ∀ u : ℝ, MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => Complex.exp (-(t : ℂ))) u) P = 0 := by
  refine ⟨1, MvPolynomial.X 1 + MvPolynomial.X 0, ?_, fun u => ?_⟩
  · intro h0
    have hc := congrArg (fun Q : MvPolynomial (Fin 2) ℂ => Q.coeff (Finsupp.single (1 : Fin 2) 1)) h0
    have hne : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1 := by
      intro h; have := congrArg (fun f => f 0) h; simp at this
    simp [MvPolynomial.coeff_X, hne] at hc
  · simp only [map_add, MvPolynomial.eval_X, Fin.val_one, Fin.val_zero,
      iteratedDeriv_zero, iteratedDeriv_one]
    have hd : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ))) (-Complex.exp (-(u : ℂ))) u := by
      have h1 : HasDerivAt (fun t : ℝ => -(t : ℂ)) (-1) u := ((hasDerivAt_id u).ofReal_comp).neg
      simpa using h1.cexp
    rw [hd.deriv]
    ring

/-- **Control 2 (Nonlinear Geometric / Modular-Kernel D-Algebraicity)**:
`f(u) = (1 - e^{-u})⁻¹` (generating function of `∑_{n ≥ 0} q^n` at `q = e^{-u}`) IS
differentially algebraic over `ℂ`, annihilated for all `u > 0` by the nonzero nonlinear order-1
autonomous differential polynomial `P = Y₁ + Y₀² - Y₀`. -/
theorem geometricKernel_is_d_algebraic :
    ∃ (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in Filter.atTop, MvPolynomial.eval
        (fun j : Fin (r + 1) =>
          iteratedDeriv j.val (fun t : ℝ => (1 - Complex.exp (-(t : ℂ)))⁻¹) u) P = 0 := by
  refine ⟨1, MvPolynomial.X 1 + MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0, ?_, ?_⟩
  · intro h0
    have hc := congrArg (fun Q : MvPolynomial (Fin 2) ℂ => Q.coeff (Finsupp.single (1 : Fin 2) 1)) h0
    have hsq : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ 2 =
        MvPolynomial.monomial (Finsupp.single (0 : Fin 2) 2) 1 := by
      rw [sq, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul, ← Finsupp.single_add]
    have hne1 : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1 := by
      intro h; have := congrArg (fun f => f 0) h; simp at this
    have hne2 : Finsupp.single (0 : Fin 2) 2 ≠ Finsupp.single (1 : Fin 2) 1 := by
      intro h; have := congrArg (fun f => f 0) h; simp at this
    rw [hsq] at hc
    simp [MvPolynomial.coeff_X, MvPolynomial.coeff_monomial, hne1, hne2] at hc
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
    simp only [map_sub, map_add, map_pow, MvPolynomial.eval_X, Fin.val_one, Fin.val_zero,
      iteratedDeriv_zero, iteratedDeriv_one]
    have hne : 1 - Complex.exp (-(u : ℂ)) ≠ 0 := by
      intro h0
      have heq : Complex.exp (-(u : ℂ)) = 1 := by linear_combination -h0
      have hnorm : ‖Complex.exp (-(u : ℂ))‖ = 1 := by rw [heq, norm_one]
      rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re] at hnorm
      have hlt : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hden : HasDerivAt (fun t : ℝ => 1 - Complex.exp (-(t : ℂ))) (Complex.exp (-(u : ℂ))) u := by
      have h1 : HasDerivAt (fun t : ℝ => -(t : ℂ)) (-1) u := ((hasDerivAt_id u).ofReal_comp).neg
      have h2 := h1.cexp.const_sub 1
      convert h2 using 1
      ring
    have hd : HasDerivAt (fun t : ℝ => (1 - Complex.exp (-(t : ℂ)))⁻¹)
        (-Complex.exp (-(u : ℂ)) / (1 - Complex.exp (-(u : ℂ))) ^ 2) u := hden.inv hne
    rw [hd.deriv]
    field_simp [hne]
    ring

end

end PakPrimes.MockThetaAndHurwitz
