module

public import PakStokes.AllD.MockModularAlgebraCore
import all PakStokes.AllD.MockModularAlgebraCore
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Wave 15 (Module 1): Rotated-Ray Analytic Continuation, Uniform Gevrey-1 Asymptotics, & Exact Hankel Keyhole Jump

Formalizes **100% unconditionally from Mathlib** (zero placeholders) the analytic
Stokes-cut engine for Paper #10 (Sections 3.2, 5.1, and 5.2):

1. **Uniform Gevrey-1 Asymptotics, Convergent Power Series Subring, & Watson Bridge:**
   Defines `sector34 u₀`, `slitDisk ρ₀`, `HasGevrey1Asymp`, algebra closure (`const`, `add`,
   `mul`, convergent power series), the convergent germ subring
   `convergentSubring : Subring (PowerSeries ℂ)`, optimal truncation `gevrey1_zero_imp_exp_decay`,
   and `watson_of_gevrey1_zero` connecting directly to `maxModulus_watson_uniqueness`.
2. **Exact Taylor Integral Remainder & Lemma 3.2(a) (`PhiReal` Holomorphy & Gevrey-1):**
   Proves the exact `(1 + w)^{-α}` integral remainder formula by induction and integration by
   parts, proves `PhiReal` and all `iteratedDeriv j (PhiReal k b)` are holomorphic on
   `Complex.slitPlane`, and proves uniform Gevrey-1 asymptotics on `sector34 u₀`.
3. **Lemma 5.1(a), (c), (d) — Rotated Rays `gammaMinus`/`gammaPlus`, Open Sectors `UPlus`/`UMinus`:**
   Proves `one_add_mul_mem_slitPlane_UPlus`, `one_add_mul_mem_slitPlane_UMinus`, the exact
   uniform bound `one_sub_txy_norm_ge_gammaMinus` / `one_sub_txy_norm_ge_gammaPlus`
   (`‖1 - t x y‖ ≥ (1 - t x)/√2 ≥ 1/(2√2)`), holomorphy of `PhiPlus`/`PhiMinus`,
   angle-invariance `ray_integral_const_on_Icc` and `ray_integral_eq_real` (giving both
   overlap agreement and moment invariance), and identical Gevrey-1 asymptotics for `Y_+`, `Y_-`.
4. **Lemma 5.1(b) — Simultaneous Lateral Annihilation (`lateral_simultaneous_annihilation`):**
   Wires `watson_of_gevrey1_zero` + Identity Theorem on connected `UPlus x₀` and `UMinus x₀`
   to prove `F₊(-x) = 0` and `F₋(-x) = 0` for all `x ∈ (0, x₀)`.
5. **Lemma 5.2 — Exact Hankel Keyhole Jump & Termwise `x`-Differentiation:**
   Proves `one_div_Gamma_ne_zero_nonBol`, `differentiable_inv_Gamma`, exact single-mode jump
   `hankel_single_mode_jump` via Euler reflection (`Complex.Gamma_mul_Gamma_one_sub`) and entire
   analytic continuation in `k ∈ ℂ`, exact series jump `hankel_series_jump`, and termwise
   `x`-differentiation matching `iteratedDeriv_mockModular_mode`. -/

@[expose] public section
namespace CubicTheta.AllD
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology Classical
noncomputable section

/-! ### 1. Sectors, Convergent Power Series, Gevrey-1 Algebra, & Watson Bridge -/

/-- The bounded closed sector `{u ∈ ℂ : 0 < ‖u‖ ≤ u₀, |arg u| ≤ 3π/4}`, characterized
algebraically as `-(√2 / 2) ‖u‖ ≤ u.re`. -/
def sector34 (u₀ : ℝ) : Set ℂ :=
  {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ≤ u₀ ∧ -(Real.sqrt 2 / 2) * ‖u‖ ≤ u.re}

/-- The open slit disk `{u ∈ ℂ : 0 < ‖u‖ < ρ₀, u ∈ Complex.slitPlane}`. -/
def slitDisk (ρ₀ : ℝ) : Set ℂ :=
  {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ < ρ₀ ∧ u ∈ Complex.slitPlane}

theorem isOpen_slitDisk (ρ₀ : ℝ) : IsOpen (slitDisk ρ₀) :=
  (isOpen_lt continuous_const continuous_norm).inter
    ((isOpen_lt continuous_norm continuous_const).inter Complex.isOpen_slitPlane)

theorem isPreconnected_slitDisk (ρ₀ : ℝ) : IsPreconnected (slitDisk ρ₀) := by
  let φ : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hφ_cont : Continuous φ :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have himg : φ '' (Set.Ioo 0 ρ₀ ×ˢ Set.Ioo (-Real.pi) Real.pi) = slitDisk ρ₀ := by
    ext u
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨⟨hr0, hr1⟩, ⟨hθ1, hθ2⟩⟩, rfl⟩
      have hnorm : ‖φ (r, θ)‖ = r := by
        dsimp [φ]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
            Complex.norm_exp_ofReal_mul_I, mul_one]
      have hslit : φ (r, θ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        by_contra hnot; push Not at hnot
        obtain ⟨hre, him⟩ := hnot
        have him' : r * Real.sin θ = 0 := by
          simpa [φ, Complex.mul_im, Complex.exp_ofReal_mul_I_im] using him
        have hsin0 : Real.sin θ = 0 := (mul_eq_zero.mp him').resolve_left hr0.ne'
        have hθ0 : θ = 0 := by
          rw [Real.sin_eq_zero_iff] at hsin0
          obtain ⟨k, hk⟩ := hsin0
          have hk0 : k = 0 := by
            by_contra hkne
            rcases lt_or_gt_of_ne hkne with hlt | hgt
            · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
              nlinarith [Real.pi_pos]
            · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hgt
              nlinarith [Real.pi_pos]
          subst hk0; simpa using hk.symm
        have hre' : r * Real.cos θ ≤ 0 := by
          simpa [φ, Complex.mul_re, Complex.exp_ofReal_mul_I_re] using hre
        rw [hθ0, Real.cos_zero, mul_one] at hre'
        linarith
      exact ⟨hnorm.symm ▸ hr0, hnorm.symm ▸ hr1, hslit⟩
    · intro ⟨h0, h1, hslit⟩
      have harg_ne : u.arg ≠ Real.pi := by
        intro hpi
        have ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hpi
        rcases Complex.mem_slitPlane_iff.mp hslit with hpos | hne
        · linarith
        · exact hne him
      refine ⟨(‖u‖, u.arg), ⟨⟨h0, h1⟩, ⟨Complex.neg_pi_lt_arg u,
        lt_of_le_of_ne (Complex.arg_le_pi u) harg_ne⟩⟩, Complex.norm_mul_exp_arg_mul_I u⟩
  rw [← himg]
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image φ hφ_cont.continuousOn

theorem sector34_subset_slitDisk {u₁ ρ₀ : ℝ} (hu₁ : u₁ < ρ₀) :
    sector34 u₁ ⊆ slitDisk ρ₀ := by
  intro u ⟨h0, h1, hre⟩
  refine ⟨h0, lt_of_le_of_lt h1 hu₁, ?_⟩
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot; push Not at hnot
  obtain ⟨hre_le, him0⟩ := hnot
  have hnorm_eq : ‖u‖ = -u.re := by
    rw [Complex.norm_def, Complex.normSq_apply, him0, mul_zero, add_zero, ← sq,
        Real.sqrt_sq_eq_abs, abs_of_nonpos hre_le]
  have hsqrt_lt : Real.sqrt 2 / 2 < 1 := by
    have : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  nlinarith

/-- Uniform Gevrey-1 asymptotic expansion of `f` on a set `S ⊆ ℂ` with formal coefficients `a`. -/
def HasGevrey1Asymp (S : Set ℂ) (f : ℂ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧
    ∀ N : ℕ, ∀ u ∈ S,
      ‖f u - ∑ n ∈ Finset.range N, a n * u ^ n‖ ≤ C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N

/-- Poincaré asymptotic expansion on the real interval `(0, u₀)`. -/
def HasRealAsymp (u₀ : ℝ) (f : ℝ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ Set.Ioo (0 : ℝ) u₀,
      ‖f x - ∑ n ∈ Finset.range N, a n * (x : ℂ) ^ n‖ ≤ C * x ^ N

theorem hasRealAsymp_of_hasGevrey1Asymp {S : Set ℂ} {u₀ : ℝ} {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hsub : ∀ x ∈ Set.Ioo (0 : ℝ) u₀, (x : ℂ) ∈ S)
    (hg : HasGevrey1Asymp S f a) :
    HasRealAsymp u₀ (fun x ↦ f (x : ℂ)) a := by
  obtain ⟨C, B, hC, hB, hbd⟩ := hg
  intro N
  refine ⟨C * B ^ N * (N.factorial : ℝ), by positivity, fun x hx ↦ ?_⟩
  have h := hbd N (x : ℂ) (hsub x hx)
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] at h

theorem hasGevrey1Asymp_mono {S T : Set ℂ} (hTS : T ⊆ S) {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasGevrey1Asymp S f a) : HasGevrey1Asymp T f a := by
  obtain ⟨C, B, hC, hB, hbd⟩ := hf
  exact ⟨C, B, hC, hB, fun N u hu ↦ hbd N u (hTS hu)⟩

theorem hasGevrey1Asymp_congr {S : Set ℂ} {f₁ f₂ : ℂ → ℂ} {a₁ a₂ : ℕ → ℂ}
    (hf : ∀ u ∈ S, f₁ u = f₂ u) (ha : ∀ n, a₁ n = a₂ n)
    (h : HasGevrey1Asymp S f₁ a₁) : HasGevrey1Asymp S f₂ a₂ := by
  obtain ⟨C, B, hC, hB, hbd⟩ := h
  refine ⟨C, B, hC, hB, fun N u hu ↦ ?_⟩
  rw [← hf u hu]
  convert hbd N u hu using 3
  apply Finset.sum_congr rfl; intro n _; rw [ha n]

theorem hasGevrey1Asymp_const (S : Set ℂ) (c : ℂ) :
    HasGevrey1Asymp S (fun _ ↦ c) (fun n ↦ if n = 0 then c else 0) := by
  refine ⟨‖c‖, 1, norm_nonneg c, zero_lt_one, fun N u _ ↦ ?_⟩
  cases N with
  | zero => simp
  | succ N =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_mul, Finset.sum_const_zero, pow_zero, mul_one,
      zero_add, sub_self, norm_zero, one_pow]
    positivity

theorem hasGevrey1Asymp_add {S : Set ℂ} {f₁ f₂ : ℂ → ℂ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : HasGevrey1Asymp S f₁ a₁) (h₂ : HasGevrey1Asymp S f₂ a₂) :
    HasGevrey1Asymp S (fun u ↦ f₁ u + f₂ u) (fun n ↦ a₁ n + a₂ n) := by
  obtain ⟨C₁, B₁, hC₁, hB₁, hbd₁⟩ := h₁
  obtain ⟨C₂, B₂, hC₂, hB₂, hbd₂⟩ := h₂
  let B := max B₁ B₂
  refine ⟨C₁ + C₂, B, add_nonneg hC₁ hC₂, lt_of_lt_of_le hB₁ (le_max_left _ _), fun N u hu ↦ ?_⟩
  have hsplit : f₁ u + f₂ u - ∑ n ∈ Finset.range N, (a₁ n + a₂ n) * u ^ n =
      (f₁ u - ∑ n ∈ Finset.range N, a₁ n * u ^ n) +
        (f₂ u - ∑ n ∈ Finset.range N, a₂ n * u ^ n) := by
    simp only [add_mul, Finset.sum_add_distrib]; ring
  rw [hsplit]
  have h1 : ‖f₁ u - ∑ n ∈ Finset.range N, a₁ n * u ^ n‖ ≤ C₁ * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N :=
    (hbd₁ N u hu).trans (by
      have hB1 : B₁ ^ N ≤ B ^ N := pow_le_pow_left₀ hB₁.le (le_max_left _ _) N
      gcongr)
  have h2 : ‖f₂ u - ∑ n ∈ Finset.range N, a₂ n * u ^ n‖ ≤ C₂ * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N :=
    (hbd₂ N u hu).trans (by
      have hB2 : B₂ ^ N ≤ B ^ N := pow_le_pow_left₀ hB₂.le (le_max_right _ _) N
      gcongr)
  calc ‖(f₁ u - ∑ n ∈ Finset.range N, a₁ n * u ^ n) +
          (f₂ u - ∑ n ∈ Finset.range N, a₂ n * u ^ n)‖
      ≤ ‖f₁ u - ∑ n ∈ Finset.range N, a₁ n * u ^ n‖ +
          ‖f₂ u - ∑ n ∈ Finset.range N, a₂ n * u ^ n‖ := norm_add_le _ _
    _ ≤ C₁ * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N +
          C₂ * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := add_le_add h1 h2
    _ = (C₁ + C₂) * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by ring

theorem hasGevrey1Asymp_const_mul {S : Set ℂ} (c : ℂ) {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasGevrey1Asymp S f a) :
    HasGevrey1Asymp S (fun u ↦ c * f u) (fun n ↦ c * a n) := by
  obtain ⟨C, B, hC, hB, hbd⟩ := hf
  refine ⟨‖c‖ * C, B, mul_nonneg (norm_nonneg c) hC, hB, fun N u hu ↦ ?_⟩
  have h : c * f u - ∑ n ∈ Finset.range N, c * a n * u ^ n =
      c * (f u - ∑ n ∈ Finset.range N, a n * u ^ n) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro n _; ring
  rw [h, norm_mul]
  calc ‖c‖ * ‖f u - ∑ n ∈ Finset.range N, a n * u ^ n‖
      ≤ ‖c‖ * (C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N) :=
        mul_le_mul_of_nonneg_left (hbd N u hu) (norm_nonneg c)
    _ = (‖c‖ * C) * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by ring

/-- Extracting the coefficient bound `‖a n‖ ≤ C * B^n * n!` when `S` accumulates at `0`. -/
theorem hasGevrey1Asymp_coeff_le {S : Set ℂ} {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ u ∈ S, 0 < ‖u‖ ∧ ‖u‖ < ε)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 < B)
    (hbd : ∀ N : ℕ, ∀ u ∈ S,
      ‖f u - ∑ n ∈ Finset.range N, a n * u ^ n‖ ≤ C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N)
    (n : ℕ) :
    ‖a n‖ ≤ C * B ^ n * (n.factorial : ℝ) := by
  by_contra hgt
  push Not at hgt
  set δ : ℝ := ‖a n‖ - C * B ^ n * (n.factorial : ℝ)
  have hδ : 0 < δ := sub_pos.mpr hgt
  set K : ℝ := C * B ^ (n + 1) * ((n + 1).factorial : ℝ) + 1
  have hK : 0 < K := by positivity
  obtain ⟨u, huS, hu0, hult⟩ := hacc (δ / K) (div_pos hδ hK)
  have hdiff : a n * u ^ n =
      (f u - ∑ k ∈ Finset.range n, a k * u ^ k) -
        (f u - ∑ k ∈ Finset.range (n + 1), a k * u ^ k) := by
    rw [Finset.sum_range_succ]; ring
  have hnorm : ‖a n‖ * ‖u‖ ^ n ≤
      C * B ^ n * (n.factorial : ℝ) * ‖u‖ ^ n +
        C * B ^ (n + 1) * ((n + 1).factorial : ℝ) * ‖u‖ ^ (n + 1) := by
    calc ‖a n‖ * ‖u‖ ^ n = ‖a n * u ^ n‖ := by rw [norm_mul, norm_pow]
      _ = ‖(f u - ∑ k ∈ Finset.range n, a k * u ^ k) -
            (f u - ∑ k ∈ Finset.range (n + 1), a k * u ^ k)‖ := by rw [hdiff]
      _ ≤ ‖f u - ∑ k ∈ Finset.range n, a k * u ^ k‖ +
            ‖f u - ∑ k ∈ Finset.range (n + 1), a k * u ^ k‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (hbd n u huS) (hbd (n + 1) u huS)
  have hun_pos : 0 < ‖u‖ ^ n := pow_pos hu0 n
  have hdiv : ‖a n‖ ≤ C * B ^ n * (n.factorial : ℝ) +
      C * B ^ (n + 1) * ((n + 1).factorial : ℝ) * ‖u‖ := by
    nlinarith [show ‖u‖ ^ (n + 1) = ‖u‖ ^ n * ‖u‖ from pow_succ ‖u‖ n]
  have hsmall : C * B ^ (n + 1) * ((n + 1).factorial : ℝ) * ‖u‖ < δ := by
    have h1 : C * B ^ (n + 1) * ((n + 1).factorial : ℝ) < K := by dsimp [K]; linarith
    have h2 : K * ‖u‖ < δ := (lt_div_iff₀' hK).mp hult
    nlinarith [norm_nonneg u]
  linarith

/-- Product closure of uniform Gevrey-1 asymptotics (Lemma 3.2(b)). -/
theorem hasGevrey1Asymp_mul {S : Set ℂ}
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ u ∈ S, 0 < ‖u‖ ∧ ‖u‖ < ε)
    {f₁ f₂ : ℂ → ℂ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : HasGevrey1Asymp S f₁ a₁) (h₂ : HasGevrey1Asymp S f₂ a₂) :
    HasGevrey1Asymp S (fun u ↦ f₁ u * f₂ u)
      (fun m ↦ ∑ p ∈ Finset.range (m + 1), a₁ p * a₂ (m - p)) := by
  obtain ⟨C₁, B₁, hC₁, hB₁, hbd₁⟩ := h₁
  obtain ⟨C₂, B₂, hC₂, hB₂, hbd₂⟩ := h₂
  let C := max C₁ C₂
  let B := max B₁ B₂
  have hC : 0 ≤ C := le_trans hC₁ (le_max_left _ _)
  have hB : 0 < B := lt_of_lt_of_le hB₁ (le_max_left _ _)
  have hbd₁' : ∀ N u, u ∈ S →
      ‖f₁ u - ∑ n ∈ Finset.range N, a₁ n * u ^ n‖ ≤ C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N :=
    fun N u hu ↦ (hbd₁ N u hu).trans (by
      have hC' : C₁ ≤ C := le_max_left _ _
      have hB' : B₁ ^ N ≤ B ^ N := pow_le_pow_left₀ hB₁.le (le_max_left _ _) N
      gcongr)
  have hbd₂' : ∀ N u, u ∈ S →
      ‖f₂ u - ∑ n ∈ Finset.range N, a₂ n * u ^ n‖ ≤ C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N :=
    fun N u hu ↦ (hbd₂ N u hu).trans (by
      have hC' : C₂ ≤ C := le_max_right _ _
      have hB' : B₂ ^ N ≤ B ^ N := pow_le_pow_left₀ hB₂.le (le_max_right _ _) N
      gcongr)
  have ha₁ : ∀ p : ℕ, ‖a₁ p‖ ≤ C * B ^ p * (p.factorial : ℝ) :=
    hasGevrey1Asymp_coeff_le hacc hC hB (fun N u hu ↦ hbd₁' N u hu)
  have hf₂_le : ∀ u ∈ S, ‖f₂ u‖ ≤ C := fun u hu ↦ by
    have h0 := hbd₂' 0 u hu
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one] at h0
    exact h0
  refine ⟨2 * C * C, 2 * B, by positivity, by positivity, fun N u hu ↦ ?_⟩
  let R₁ : ℕ → ℂ := fun k ↦ f₁ u - ∑ n ∈ Finset.range k, a₁ n * u ^ n
  let R₂ : ℕ → ℂ := fun k ↦ f₂ u - ∑ n ∈ Finset.range k, a₂ n * u ^ n
  have hident : f₁ u * f₂ u -
      ∑ m ∈ Finset.range N, (∑ p ∈ Finset.range (m + 1), a₁ p * a₂ (m - p)) * u ^ m =
      R₁ N * f₂ u + ∑ p ∈ Finset.range N, a₁ p * u ^ p * R₂ (N - p) := by
    have hsum_eq : ∑ p ∈ Finset.range N, a₁ p * u ^ p * (∑ q ∈ Finset.range (N - p), a₂ q * u ^ q) =
        ∑ m ∈ Finset.range N, (∑ p ∈ Finset.range (m + 1), a₁ p * a₂ (m - p)) * u ^ m := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij (fun x ↦ ⟨x.1 + x.2, x.1⟩) ?_ ?_ ?_ ?_
      · intro ⟨p, q⟩ h
        simp only [Finset.mem_sigma, Finset.mem_range] at h ⊢; omega
      · intro ⟨p₁, q₁⟩ _ ⟨p₂, q₂⟩ _ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        obtain ⟨hsum, hp⟩ := heq; subst hp; congr 1; omega
      · intro ⟨m, p⟩ h
        have hmp := Finset.mem_sigma.mp h
        have hm : m < N := Finset.mem_range.mp hmp.1
        have hp : p < m + 1 := Finset.mem_range.mp hmp.2
        refine ⟨⟨p, m - p⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by dsimp; omega),
          Finset.mem_range.mpr (by dsimp; omega)⟩, ?_⟩
        refine Sigma.ext (by dsimp; omega) (by simp)
      · intro ⟨p, q⟩ _
        dsimp; rw [Nat.add_sub_cancel_left, pow_add]; ring
    have hR₂ : ∑ p ∈ Finset.range N, a₁ p * u ^ p * R₂ (N - p) =
        (∑ p ∈ Finset.range N, a₁ p * u ^ p) * f₂ u -
          ∑ p ∈ Finset.range N, a₁ p * u ^ p * (∑ q ∈ Finset.range (N - p), a₂ q * u ^ q) := by
      simp only [R₂, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hR₂, hsum_eq]; dsimp [R₁]; ring
  rw [hident]
  have hterm1 : ‖R₁ N * f₂ u‖ ≤ C * C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by
    rw [norm_mul]
    calc ‖R₁ N‖ * ‖f₂ u‖
        ≤ (C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N) * C :=
          mul_le_mul (hbd₁' N u hu) (hf₂_le u hu) (norm_nonneg _) (by positivity)
      _ = C * C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by ring
  have hterm2 : ‖∑ p ∈ Finset.range N, a₁ p * u ^ p * R₂ (N - p)‖ ≤
      C * C * (2 * B) ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by
    calc ‖∑ p ∈ Finset.range N, a₁ p * u ^ p * R₂ (N - p)‖
        ≤ ∑ p ∈ Finset.range N, ‖a₁ p * u ^ p * R₂ (N - p)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.range N, C * C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by
          apply Finset.sum_le_sum
          intro p hp
          have hpN : p ≤ N := (Finset.mem_range.mp hp).le
          rw [norm_mul, norm_mul, norm_pow]
          have hfac : (p.factorial : ℝ) * ((N - p).factorial : ℝ) ≤ (N.factorial : ℝ) := by
            exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos N)
              (Nat.factorial_mul_factorial_dvd_factorial hpN)
          calc ‖a₁ p‖ * ‖u‖ ^ p * ‖R₂ (N - p)‖
              ≤ (C * B ^ p * (p.factorial : ℝ)) * ‖u‖ ^ p *
                  (C * B ^ (N - p) * ((N - p).factorial : ℝ) * ‖u‖ ^ (N - p)) := by
                gcongr
                · exact ha₁ p
                · exact hbd₂' (N - p) u hu
            _ = C * C * (B ^ p * B ^ (N - p)) * ((p.factorial : ℝ) * ((N - p).factorial : ℝ)) *
                  (‖u‖ ^ p * ‖u‖ ^ (N - p)) := by ring
            _ = C * C * B ^ N * ((p.factorial : ℝ) * ((N - p).factorial : ℝ)) * ‖u‖ ^ N := by
                rw [← pow_add, ← pow_add, Nat.add_sub_of_le hpN]
            _ ≤ C * C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by gcongr
      _ = (N : ℝ) * (C * C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ N * (C * C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N) := by
          gcongr; exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
      _ = C * C * (2 * B) ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by rw [mul_pow]; ring
  have h1_le : C * C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N ≤
      C * C * (2 * B) ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by
    have h2B : B ^ N ≤ (2 * B) ^ N := pow_le_pow_left₀ hB.le (by linarith) N
    gcongr
  calc ‖R₁ N * f₂ u + ∑ p ∈ Finset.range N, a₁ p * u ^ p * R₂ (N - p)‖
      ≤ ‖R₁ N * f₂ u‖ + ‖∑ p ∈ Finset.range N, a₁ p * u ^ p * R₂ (N - p)‖ := norm_add_le _ _
    _ ≤ C * C * (2 * B) ^ N * (N.factorial : ℝ) * ‖u‖ ^ N +
          C * C * (2 * B) ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := add_le_add (hterm1.trans h1_le) hterm2
    _ = (2 * C * C) * (2 * B) ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by ring

/-- Optimal truncation (Stirling-free via `N! ≤ N^N`): zero Gevrey-1 asymptotics implies
exponential decay `‖f u‖ ≤ (C e) exp(-1 / (e B ‖u‖))`. -/
theorem gevrey1_zero_imp_exp_decay {C B : ℝ} (hC : 0 ≤ C) (hB : 0 < B) {u : ℂ} (hu : 0 < ‖u‖)
    {v : ℂ} (hbd : ∀ N : ℕ, ‖v‖ ≤ C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N) :
    ‖v‖ ≤ (C * Real.exp 1) * Real.exp (-(1 / (Real.exp 1 * B)) / ‖u‖) := by
  let N : ℕ := Nat.floor (1 / (Real.exp 1 * B * ‖u‖))
  have hN_le : (N : ℝ) ≤ 1 / (Real.exp 1 * B * ‖u‖) := Nat.floor_le (by positivity)
  have hN_gt : 1 / (Real.exp 1 * B * ‖u‖) - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
  have hfac_le : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
    clear hN_le hN_gt
    induction N with
    | zero => simp
    | succ k ih =>
      have hk : (k : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) ^ k := by
        gcongr; exact_mod_cast Nat.le_succ k
      calc (((k + 1).factorial : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
        _ ≤ ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k := by gcongr
        _ ≤ ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k := by gcongr
        _ = ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by rw [pow_succ']
  have hprod_le : B * ‖u‖ * (N : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have h1 := mul_le_mul_of_nonneg_left hN_le (show 0 ≤ B * ‖u‖ by positivity)
    have heq : B * ‖u‖ * (1 / (Real.exp 1 * B * ‖u‖)) = (Real.exp 1)⁻¹ := by
      field_simp [hB.ne', hu.ne', (Real.exp_pos 1).ne']
    linarith
  have hpow_le : B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N ≤ Real.exp (-(N : ℝ)) := by
    calc B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N
        ≤ B ^ N * (N : ℝ) ^ N * ‖u‖ ^ N := by gcongr
      _ = (B * ‖u‖ * (N : ℝ)) ^ N := by rw [mul_pow, mul_pow]; ring
      _ ≤ (Real.exp (-1)) ^ N := by
          exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg hB.le hu.le) (Nat.cast_nonneg N)) hprod_le N
      _ = Real.exp (-(N : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hexp_le : Real.exp (-(N : ℝ)) ≤ Real.exp 1 * Real.exp (-(1 / (Real.exp 1 * B)) / ‖u‖) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hdiv : 1 / (Real.exp 1 * B * ‖u‖) = (1 / (Real.exp 1 * B)) / ‖u‖ := by
      field_simp [hB.ne', hu.ne', (Real.exp_pos 1).ne']
    rw [neg_div]
    linarith
  calc ‖v‖ ≤ C * B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := hbd N
    _ = C * (B ^ N * (N.factorial : ℝ) * ‖u‖ ^ N) := by ring
    _ ≤ C * Real.exp (-(N : ℝ)) := mul_le_mul_of_nonneg_left hpow_le hC
    _ ≤ C * (Real.exp 1 * Real.exp (-(1 / (Real.exp 1 * B)) / ‖u‖)) :=
        mul_le_mul_of_nonneg_left hexp_le hC
    _ = (C * Real.exp 1) * Real.exp (-(1 / (Real.exp 1 * B)) / ‖u‖) := by ring

/-- **Watson Uniqueness from Uniform Gevrey-1 Zero Expansion**:
Connects directly to `maxModulus_watson_uniqueness` from `MockModularAlgebraCore.lean`! -/
theorem watson_of_gevrey1_zero {u₁ ρ₀ : ℝ} (hu₁ : 0 < u₁) (hρ₀ : u₁ < ρ₀)
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (slitDisk ρ₀))
    (hF_gev : HasGevrey1Asymp (sector34 u₁) F (fun _ ↦ 0)) :
    ∀ u ∈ slitDisk ρ₀, F u = 0 := by
  obtain ⟨C, B, hC, hB, hbd⟩ := hF_gev
  let R₀ : ℝ := 1 / u₁
  have hR₀ : 0 < R₀ := one_div_pos.mpr hu₁
  let g : ℂ → ℂ := fun z ↦ F z⁻¹
  have hinv_mem : ∀ z ∈ watsonClosedSector R₀, z⁻¹ ∈ sector34 u₁ := by
    intro z hz
    change R₀ ≤ ‖z‖ ∧ -(1 / 2 : ℝ) * ‖z‖ ≤ z.re at hz
    obtain ⟨hnorm, hre⟩ := hz
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le hR₀ hnorm
    have hinv_norm : ‖z⁻¹‖ = ‖z‖⁻¹ := norm_inv z
    refine ⟨by rw [hinv_norm]; exact inv_pos.mpr hz_pos, ?_, ?_⟩
    · rw [hinv_norm]
      have := inv_anti₀ hR₀ hnorm
      simpa [R₀] using this
    · rw [Complex.inv_re, Complex.normSq_eq_norm_sq, hinv_norm]
      have h12 : (1 / 2 : ℝ) ≤ Real.sqrt 2 / 2 := by
        have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        linarith
      have h2 : -(Real.sqrt 2 / 2) * ‖z‖ ≤ z.re := by nlinarith
      rw [le_div_iff₀ (sq_pos_of_pos hz_pos)]
      have heq : -(Real.sqrt 2 / 2) * ‖z‖⁻¹ * ‖z‖ ^ 2 = -(Real.sqrt 2 / 2) * ‖z‖ := by
        field_simp [hz_pos.ne']
      linarith
  have hg_diff : DifferentiableOn ℂ g (watsonOpenSector R₀) := by
    intro z hz
    change R₀ < ‖z‖ ∧ -(1 / 2 : ℝ) * ‖z‖ < z.re at hz
    have hz_cl : z ∈ watsonClosedSector R₀ := ⟨hz.1.le, hz.2.le⟩
    have hz_ne : z ≠ 0 := norm_pos_iff.mp (lt_trans hR₀ hz.1)
    have hF_at : DifferentiableAt ℂ F z⁻¹ :=
      (hF_diff z⁻¹ (sector34_subset_slitDisk hρ₀ (hinv_mem z hz_cl))).differentiableAt
        ((isOpen_slitDisk ρ₀).mem_nhds (sector34_subset_slitDisk hρ₀ (hinv_mem z hz_cl)))
    exact (hF_at.comp z (differentiableAt_inv hz_ne)).differentiableWithinAt
  have hg_cont : ContinuousOn g (watsonClosedSector R₀) := by
    intro z hz
    have hz' : R₀ ≤ ‖z‖ ∧ -(1 / 2 : ℝ) * ‖z‖ ≤ z.re := hz
    have hz_ne : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR₀ hz'.1)
    have hF_at : ContinuousAt F z⁻¹ :=
      ((hF_diff z⁻¹ (sector34_subset_slitDisk hρ₀ (hinv_mem z hz))).differentiableAt
        ((isOpen_slitDisk ρ₀).mem_nhds (sector34_subset_slitDisk hρ₀ (hinv_mem z hz)))).continuousAt
    exact (hF_at.comp (continuousAt_inv₀ hz_ne)).continuousWithinAt
  have hg_decay : ∀ z ∈ watsonClosedSector R₀,
      ‖g z‖ ≤ (C * Real.exp 1) * Real.exp (-(1 / (Real.exp 1 * B)) * ‖z‖) := by
    intro z hz
    have hmem := hinv_mem z hz
    have hbd_z : ∀ N : ℕ, ‖g z‖ ≤ C * B ^ N * (N.factorial : ℝ) * ‖z⁻¹‖ ^ N := fun N ↦ by
      have h := hbd N z⁻¹ hmem
      simpa [g] using h
    have hdec := gevrey1_zero_imp_exp_decay hC hB hmem.1 hbd_z
    rwa [norm_inv, div_inv_eq_mul] at hdec
  have hwat := (maxModulus_watson_uniqueness hR₀ (by positivity) (by positivity)
    hg_diff hg_cont hg_decay).1
  have hreal0 : ∀ x : ℝ, 0 < x → x < u₁ → F (x : ℂ) = 0 := by
    intro x hx0 hxu
    have hinv_gt : R₀ < x⁻¹ := by
      dsimp [R₀]; rw [one_div]; exact inv_strictAnti₀ hx0 hxu
    have h0 := hwat x⁻¹ hinv_gt
    simpa [g, Complex.ofReal_inv, inv_inv] using h0
  have hAnal : AnalyticOnNhd ℂ F (slitDisk ρ₀) := hF_diff.analyticOnNhd (isOpen_slitDisk ρ₀)
  let u_pt : ℂ := ((u₁ / 2 : ℝ) : ℂ)
  have hu_mem : u_pt ∈ slitDisk ρ₀ := by
    refine ⟨?_, ?_, Complex.mem_slitPlane_iff.mpr (Or.inl (by dsimp [u_pt]; simp; linarith))⟩
    · dsimp [u_pt]; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    · dsimp [u_pt]; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hfreq : ∃ᶠ u in 𝓝[≠] u_pt, F u = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hVopen, huV, hVsub⟩ := hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hVopen u_pt huV
    let δ : ℝ := min (ε / 2) (u₁ / 4)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    let x' : ℝ := u₁ / 2 + δ
    have hx'ne : (x' : ℂ) ≠ u_pt := by
      intro h0
      have := Complex.ofReal_injective h0
      dsimp [x'] at this; linarith
    have hx'ball : (x' : ℂ) ∈ Metric.ball u_pt ε := by
      rw [Metric.mem_ball, Complex.dist_eq, show (x' : ℂ) - u_pt = (δ : ℂ) by
        dsimp [x', u_pt]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact ⟨(x' : ℂ), hVsub ⟨hball hx'ball, hx'ne⟩,
      hreal0 x' (by dsimp [x']; linarith)
        (by dsimp [x']; have := min_le_right (ε / 2) (u₁ / 4); linarith)⟩
  exact hAnal.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_slitDisk ρ₀) hu_mem hfreq

/-! ### 1B. Convergent Power Series Subring `ℂ{x}` Inside `PowerSeries ℂ` -/

/-- A formal power series `p ∈ ℂ[[x]]` converges on `Metric.ball 0 ρ` with Cauchy bound `M`. -/
def IsConvergentOn (ρ M : ℝ) (p : PowerSeries ℂ) : Prop :=
  0 < ρ ∧ 0 ≤ M ∧ ∀ n : ℕ, ‖p.coeff n‖ * ρ ^ n ≤ M

/-- Evaluation of a power series at `z ∈ ℂ` via `tsum`. -/
def psEval (p : PowerSeries ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, p.coeff n * z ^ n

/-- The subring `ℂ{x} ⊂ ℂ[[x]]` of formal power series with positive radius of convergence. -/
def convergentSubring : Subring (PowerSeries ℂ) where
  carrier := {p : PowerSeries ℂ | ∃ ρ M : ℝ, IsConvergentOn ρ M p}
  zero_mem' := ⟨1, 0, zero_lt_one, le_rfl, fun n ↦ by simp⟩
  one_mem' := ⟨1, 1, zero_lt_one, zero_le_one, fun n ↦ by
    cases n <;> simp⟩
  neg_mem' := by
    rintro p ⟨ρ, M, hρ, hM, hbd⟩
    exact ⟨ρ, M, hρ, hM, fun n ↦ by simpa using hbd n⟩
  add_mem' := by
    rintro p q ⟨ρ₁, M₁, hρ₁, hM₁, hbd₁⟩ ⟨ρ₂, M₂, hρ₂, hM₂, hbd₂⟩
    let ρ := min ρ₁ ρ₂
    refine ⟨ρ, M₁ + M₂, lt_min hρ₁ hρ₂, add_nonneg hM₁ hM₂, fun n ↦ ?_⟩
    have h1 : ‖p.coeff n‖ * ρ ^ n ≤ M₁ :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (lt_min hρ₁ hρ₂).le (min_le_left _ _) n)
        (norm_nonneg _)).trans (hbd₁ n)
    have h2 : ‖q.coeff n‖ * ρ ^ n ≤ M₂ :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (lt_min hρ₁ hρ₂).le (min_le_right _ _) n)
        (norm_nonneg _)).trans (hbd₂ n)
    rw [map_add]
    calc ‖p.coeff n + q.coeff n‖ * ρ ^ n
        ≤ (‖p.coeff n‖ + ‖q.coeff n‖) * ρ ^ n :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ = ‖p.coeff n‖ * ρ ^ n + ‖q.coeff n‖ * ρ ^ n := add_mul _ _ _
      _ ≤ M₁ + M₂ := add_le_add h1 h2
  mul_mem' := by
    rintro p q ⟨ρ₁, M₁, hρ₁, hM₁, hbd₁⟩ ⟨ρ₂, M₂, hρ₂, hM₂, hbd₂⟩
    let ρ₀ := min ρ₁ ρ₂
    have hρ₀ : 0 < ρ₀ := lt_min hρ₁ hρ₂
    refine ⟨ρ₀ / 2, 2 * M₁ * M₂, by positivity, by positivity, fun n ↦ ?_⟩
    rw [PowerSeries.coeff_mul]
    have hsum : ‖∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2‖ * (ρ₀ / 2) ^ n ≤
        (n + 1 : ℝ) * (1 / 2 : ℝ) ^ n * (M₁ * M₂) := by
      have h1 : ‖∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2‖ ≤
          ∑ x ∈ Finset.antidiagonal n, ‖p.coeff x.1‖ * ‖q.coeff x.2‖ := by
        simpa only [norm_mul] using norm_sum_le (Finset.antidiagonal n) (fun x ↦ p.coeff x.1 * q.coeff x.2)
      have h2 : (∑ x ∈ Finset.antidiagonal n, ‖p.coeff x.1‖ * ‖q.coeff x.2‖) * (ρ₀ / 2) ^ n ≤
          ∑ _x ∈ Finset.antidiagonal n, (1 / 2 : ℝ) ^ n * (M₁ * M₂) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro ⟨i, j⟩ hij
        have hij_eq : i + j = n := Finset.mem_antidiagonal.mp hij
        have hp : ‖p.coeff i‖ * ρ₀ ^ i ≤ M₁ :=
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ₀.le (min_le_left _ _) i)
            (norm_nonneg _)).trans (hbd₁ i)
        have hq : ‖q.coeff j‖ * ρ₀ ^ j ≤ M₂ :=
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ₀.le (min_le_right _ _) j)
            (norm_nonneg _)).trans (hbd₂ j)
        calc ‖p.coeff i‖ * ‖q.coeff j‖ * (ρ₀ / 2) ^ n
            = (1 / 2 : ℝ) ^ n * ((‖p.coeff i‖ * ρ₀ ^ i) * (‖q.coeff j‖ * ρ₀ ^ j)) := by
              rw [show ρ₀ / 2 = ρ₀ * (1 / 2) by ring, mul_pow, ← hij_eq, pow_add]; ring
          _ ≤ (1 / 2 : ℝ) ^ n * (M₁ * M₂) := by
              gcongr
      calc ‖∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2‖ * (ρ₀ / 2) ^ n
          ≤ (∑ x ∈ Finset.antidiagonal n, ‖p.coeff x.1‖ * ‖q.coeff x.2‖) * (ρ₀ / 2) ^ n :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ ∑ _x ∈ Finset.antidiagonal n, (1 / 2 : ℝ) ^ n * (M₁ * M₂) := h2
        _ = (n + 1 : ℝ) * (1 / 2 : ℝ) ^ n * (M₁ * M₂) := by
            rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
            ring
    have hn_le : (n + 1 : ℝ) * (1 / 2 : ℝ) ^ n ≤ 2 := by
      have hpow : (n + 1 : ℕ) ≤ 2 * 2 ^ n := by
        clear hsum
        induction n with
        | zero => omega
        | succ k ih =>
          have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          calc k + 1 + 1 ≤ 2 * 2 ^ k + 1 := Nat.add_le_add_right ih 1
            _ ≤ 2 * 2 ^ k + 2 * 2 ^ k := Nat.add_le_add_left (by omega) _
            _ = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      have hpowR : (n + 1 : ℝ) ≤ 2 * (2 : ℝ) ^ n := by exact_mod_cast hpow
      rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    calc ‖∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2‖ * (ρ₀ / 2) ^ n
        ≤ (n + 1 : ℝ) * (1 / 2 : ℝ) ^ n * (M₁ * M₂) := hsum
      _ ≤ 2 * (M₁ * M₂) := mul_le_mul_of_nonneg_right hn_le (mul_nonneg hM₁ hM₂)
      _ = 2 * M₁ * M₂ := by ring

theorem isConvergentOn_summable {ρ M : ℝ} {p : PowerSeries ℂ}
    (hp : IsConvergentOn ρ M p) {z : ℂ} (hz : ‖z‖ < ρ) :
    Summable (fun n : ℕ ↦ p.coeff n * z ^ n) := by
  obtain ⟨hρ, hM, hbd⟩ := hp
  have hr : ‖z‖ / ρ < 1 := (div_lt_one hρ).mpr hz
  have hgeom : Summable (fun n : ℕ ↦ M * (‖z‖ / ρ) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left M
  refine Summable.of_norm_bounded hgeom fun n ↦ ?_
  rw [norm_mul, norm_pow]
  have h1 := hbd n
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hρ n)]
  calc ‖p.coeff n‖ * ‖z‖ ^ n * ρ ^ n = (‖p.coeff n‖ * ρ ^ n) * ‖z‖ ^ n := by ring
    _ ≤ M * ‖z‖ ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg z) n)

theorem psEval_differentiableOn {ρ M : ℝ} {p : PowerSeries ℂ}
    (hp : IsConvergentOn ρ M p) :
    DifferentiableOn ℂ (psEval p) (Metric.ball 0 ρ) := by
  obtain ⟨hρ, hM, hbd⟩ := hp
  intro z₀ hz₀
  have hz₀_lt : ‖z₀‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hz₀
  let r : ℝ := (‖z₀‖ + ρ) / 2
  have hz₀r : ‖z₀‖ < r := by dsimp [r]; linarith
  have hrρ : r < ρ := by dsimp [r]; linarith
  have hr_pos : 0 < r := lt_of_le_of_lt (norm_nonneg z₀) hz₀r
  let u : ℕ → ℝ := fun n ↦ M * (n : ℝ) * (r / ρ) ^ n / r
  have hu_sum : Summable u := by
    let q : ℝ := r / ρ
    have hq0 : 0 < q := div_pos hr_pos hρ
    have hq1 : q < 1 := (div_lt_one hρ).mpr hrρ
    have h1 : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
      have hgeom : Summable (fun n : ℕ ↦ ((1 + q) / 2) ^ n) :=
        summable_geometric_of_lt_one (by positivity) (by linarith)
      have hrat : q / ((1 + q) / 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      have htend : Tendsto (fun n : ℕ ↦ (n : ℝ) * (q / ((1 + q) / 2)) ^ n) atTop (𝓝 0) :=
        tendsto_self_mul_const_pow_of_lt_one (by positivity) hrat
      obtain ⟨N, hN⟩ := (htend.eventually (eventually_le_nhds zero_lt_one)).exists_forall_of_atTop
      refine (summable_nat_add_iff N).mp ?_
      refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
        ((summable_nat_add_iff N).mpr hgeom)
      have hk := hN (k + N) (Nat.le_add_left N k)
      have hpos : 0 < ((1 + q) / 2) ^ (k + N) := by positivity
      calc ((k + N : ℕ) : ℝ) * q ^ (k + N)
          = ((k + N : ℕ) : ℝ) * (q / ((1 + q) / 2)) ^ (k + N) * ((1 + q) / 2) ^ (k + N) := by
            rw [mul_assoc, ← mul_pow, div_mul_cancel₀ q (by positivity)]
        _ ≤ 1 * ((1 + q) / 2) ^ (k + N) := mul_le_mul_of_nonneg_right hk hpos.le
        _ = ((1 + q) / 2) ^ (k + N) := one_mul _
    have h2 := (h1.mul_left M).div_const r
    simpa [u, q, mul_assoc] using h2
  have hhd := hasDerivAt_tsum_of_isPreconnected
    (g := fun n z ↦ p.coeff n * z ^ n)
    (g' := fun n z ↦ p.coeff n * ((n : ℂ) * z ^ (n - 1)))
    (t := Metric.ball 0 r) (y₀ := 0) (y := z₀)
    hu_sum Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    (fun n z _ ↦ (hasDerivAt_pow n z).const_mul (p.coeff n))
    (fun n z hz ↦ by
      have hz_lt : ‖z‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hz
      cases n with
      | zero => simp [u]
      | succ n =>
        rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, Nat.add_sub_cancel]
        have h1 : ‖p.coeff (n + 1)‖ * ‖z‖ ^ n ≤ M * r ^ n / ρ ^ (n + 1) := by
          have hbd1 := hbd (n + 1)
          rw [le_div_iff₀ (pow_pos hρ (n + 1))]
          calc ‖p.coeff (n + 1)‖ * ‖z‖ ^ n * ρ ^ (n + 1)
              = (‖p.coeff (n + 1)‖ * ρ ^ (n + 1)) * ‖z‖ ^ n := by ring
            _ ≤ M * r ^ n := mul_le_mul hbd1 (pow_le_pow_left₀ (norm_nonneg z) hz_lt.le n)
                (by positivity) hM
        dsimp [u]
        have h2 : M * ((n + 1 : ℕ) : ℝ) * (r / ρ) ^ (n + 1) / r =
            ((n + 1 : ℕ) : ℝ) * (M * r ^ n / ρ ^ (n + 1)) := by
          rw [div_pow, pow_succ]
          field_simp [hr_pos.ne', hρ.ne']
        rw [h2]
        calc ‖p.coeff (n + 1)‖ * (((n + 1 : ℕ) : ℝ) * ‖z‖ ^ n)
            = ((n + 1 : ℕ) : ℝ) * (‖p.coeff (n + 1)‖ * ‖z‖ ^ n) := by ring
          _ ≤ ((n + 1 : ℕ) : ℝ) * (M * r ^ n / ρ ^ (n + 1)) := by gcongr)
    (by simpa [Metric.mem_ball] using hr_pos)
    (isConvergentOn_summable ⟨hρ, hM, hbd⟩ (by simpa using hρ))
    (by simpa [Metric.mem_ball, dist_zero_right] using hz₀r)
  exact hhd.differentiableAt.differentiableWithinAt

theorem hasGevrey1Asymp_psEval {ρ M : ℝ} {p : PowerSeries ℂ}
    (hp : IsConvergentOn ρ M p) :
    HasGevrey1Asymp {z : ℂ | ‖z‖ ≤ ρ / 2} (psEval p) (fun n ↦ p.coeff n) := by
  obtain ⟨hρ, hM, hbd⟩ := hp
  refine ⟨2 * M, 1 / ρ, by positivity, by positivity, fun N z hz ↦ ?_⟩
  have hz_le : ‖z‖ ≤ ρ / 2 := hz
  have hz_lt : ‖z‖ < ρ := lt_of_le_of_lt hz_le (by linarith)
  have hsum := isConvergentOn_summable ⟨hρ, hM, hbd⟩ hz_lt
  have htail : psEval p z - ∑ n ∈ Finset.range N, p.coeff n * z ^ n =
      ∑' k : ℕ, p.coeff (k + N) * z ^ (k + N) := by
    unfold psEval
    rw [← hsum.sum_add_tsum_nat_add N]
    ring
  rw [htail]
  have hnorm_sum : Summable (fun k : ℕ ↦ M * (‖z‖ / ρ) ^ (k + N)) := by
    have hq : ‖z‖ / ρ < 1 := (div_lt_one hρ).mpr hz_lt
    have := (summable_geometric_of_lt_one (by positivity) hq).mul_left (M * (‖z‖ / ρ) ^ N)
    refine this.congr fun k ↦ ?_
    rw [pow_add]; ring
  have hle_term : ∀ k : ℕ, ‖p.coeff (k + N) * z ^ (k + N)‖ ≤ M * (‖z‖ / ρ) ^ (k + N) := fun k ↦ by
    rw [norm_mul, norm_pow, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hρ _)]
    calc ‖p.coeff (k + N)‖ * ‖z‖ ^ (k + N) * ρ ^ (k + N)
        = (‖p.coeff (k + N)‖ * ρ ^ (k + N)) * ‖z‖ ^ (k + N) := by ring
      _ ≤ M * ‖z‖ ^ (k + N) := mul_le_mul_of_nonneg_right (hbd _) (by positivity)
  have htsum_le : ‖∑' k : ℕ, p.coeff (k + N) * z ^ (k + N)‖ ≤ ∑' k : ℕ, M * (‖z‖ / ρ) ^ (k + N) :=
    (norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr hsum).norm).trans
      (Summable.tsum_le_tsum hle_term ((summable_nat_add_iff N).mpr hsum).norm hnorm_sum)
  have hgeom_val : ∑' k : ℕ, M * (‖z‖ / ρ) ^ (k + N) =
      M * (‖z‖ / ρ) ^ N * (1 - ‖z‖ / ρ)⁻¹ := by
    have h1 : (fun k : ℕ ↦ M * (‖z‖ / ρ) ^ (k + N)) =
        fun k : ℕ ↦ (M * (‖z‖ / ρ) ^ N) * (‖z‖ / ρ) ^ k := by
      ext k; rw [pow_add]; ring
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) ((div_lt_one hρ).mpr hz_lt)]
  have hinv_le : (1 - ‖z‖ / ρ)⁻¹ ≤ 2 := by
    have hq_le : ‖z‖ / ρ ≤ 1 / 2 := (div_le_iff₀ hρ).mpr (by linarith)
    have hden : (1 / 2 : ℝ) ≤ 1 - ‖z‖ / ρ := by linarith
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num at this; exact this
  have hfac_ge : (1 : ℝ) ≤ (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  calc ‖∑' k : ℕ, p.coeff (k + N) * z ^ (k + N)‖
      ≤ M * (‖z‖ / ρ) ^ N * (1 - ‖z‖ / ρ)⁻¹ := by rw [← hgeom_val]; exact htsum_le
    _ ≤ M * (‖z‖ / ρ) ^ N * 2 := by gcongr
    _ = 2 * M * (1 / ρ) ^ N * 1 * ‖z‖ ^ N := by rw [div_pow, one_div, inv_pow]; ring
    _ ≤ 2 * M * (1 / ρ) ^ N * (N.factorial : ℝ) * ‖z‖ ^ N := by gcongr

/-! ### 2. Exact Taylor Integral Remainder & Lemma 3.2(a) (`PhiReal`) -/

/-- Generalized binomial coefficient `α (α - 1) ⋯ (α - n + 1) / n!`. -/
def genBinom (α : ℂ) (n : ℕ) : ℂ :=
  (∏ j ∈ Finset.range n, (α - (j : ℂ))) / (n.factorial : ℂ)

/-- Rising factorial `(k)_j = k (k + 1) ⋯ (k + j - 1)`. -/
def risingFac (k : ℂ) (j : ℕ) : ℂ :=
  ∏ m ∈ Finset.range j, (k + (m : ℂ))

@[simp] theorem genBinom_zero (α : ℂ) : genBinom α 0 = 1 := by simp [genBinom]

theorem genBinom_succ (α : ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * genBinom α (n + 1) = (α - (n : ℂ)) * genBinom α n := by
  unfold genBinom
  rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
  have h1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [h1, h2]

@[simp] theorem risingFac_zero (k : ℂ) : risingFac k 0 = 1 := by simp [risingFac]

theorem risingFac_succ (k : ℂ) (j : ℕ) :
    risingFac k (j + 1) = risingFac k j * (k + (j : ℂ)) := by
  simp [risingFac, Finset.prod_range_succ]

private lemma continuousAt_cpow_const_slit {z c : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContinuousAt (fun w : ℂ ↦ w ^ c) z :=
  ((hasDerivAt_id z).cpow_const (c := c) hz).continuousAt

private lemma continuousAt_cpow_const_comp {α : Type*} [TopologicalSpace α] {f : α → ℂ} {x : α} {c : ℂ}
    (hf : ContinuousAt f x) (hsl : f x ∈ Complex.slitPlane) :
    ContinuousAt (fun t ↦ (f t) ^ c) x :=
  (continuousAt_cpow_const_slit (c := c) hsl).comp hf

private lemma differentiableOn_iteratedDeriv_open {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv hU

private lemma hasDerivAt_conj_comp {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' (starRingEnd ℂ z)) :
    HasDerivAt (fun w : ℂ ↦ starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') z := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hd0 := hasDerivAt_iff_tendsto_slope_zero.mp hf
  have hmap : Tendsto (starRingEnd ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by
        have hc : Tendsto (starRingEnd ℂ) (𝓝 (0 : ℂ)) (𝓝 ((starRingEnd ℂ) 0)) :=
          (Complex.continuous_conj.continuousAt (x := (0 : ℂ))).tendsto
        rw [map_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht ↦ by simpa using ht)
  exact (Complex.continuous_conj.continuousAt.tendsto.comp (hd0.comp hmap)).congr fun t ↦ by
    dsimp only [Function.comp_apply]
    simp only [smul_eq_mul, map_mul, map_inv₀, map_sub, map_add, Complex.conj_conj]

private lemma hasDerivAt_comp_real {F : ℂ → ℂ} {g : ℝ → ℂ} {f' g' : ℂ} {t : ℝ}
    (hF : HasDerivAt F f' (g t)) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s : ℝ ↦ F (g s)) (f' * g') t := by
  have h1 : HasDerivAt (F ∘ g) (g' • f') t := hF.scomp t hg
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using h1

/-- Exact Taylor integral remainder for `(1 + w)^{-α}` whenever `1 + t w ∈ slitPlane` on `[0, 1]`. -/
theorem cpow_taylor_integral_remainder (α w : ℂ) :
    ∀ N : ℕ, 1 ≤ N →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 1 + (t : ℂ) * w ∈ Complex.slitPlane) →
      (1 + w) ^ (-α) =
        ∑ n ∈ Finset.range N, genBinom (-α) n * w ^ n +
          (N : ℂ) * genBinom (-α) N * w ^ N *
            ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 + (t : ℂ) * w) ^ (-α - (N : ℂ)) := by
  intro N hN hslit
  induction N with
  | zero => omega
  | succ N ih =>
    cases N with
    | zero =>
      have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ ↦ (1 + (s : ℂ) * w) ^ (-α))
            ((-α) * w * (1 + (t : ℂ) * w) ^ (-α - 1)) t := by
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        have hC : HasDerivAt (fun z : ℂ ↦ (1 + z * w) ^ (-α))
            ((-α) * (1 + (t : ℂ) * w) ^ (-α - 1) * (1 * w)) (t : ℂ) :=
          (((hasDerivAt_id (t : ℂ)).mul_const w).const_add (1 : ℂ)).cpow_const (c := -α) (hslit t ht)
        convert hC.comp_ofReal using 1; ring
      have hcont : ContinuousOn (fun s : ℝ ↦ (-α) * w * (1 + (s : ℂ) * w) ^ (-α - 1))
          (Set.uIcc 0 1) := by
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        have hlin : ContinuousAt (fun s : ℝ ↦ 1 + (s : ℂ) * w) t :=
          continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
        have hpow : ContinuousAt (fun s : ℝ ↦ (1 + (s : ℂ) * w) ^ (-α - 1)) t :=
          continuousAt_cpow_const_comp hlin (hslit t ht)
        exact (continuousAt_const.mul hpow).continuousWithinAt
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
      simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero,
        Complex.one_cpow] at hftc
      have hgb : genBinom (-α) 1 = -α := by simp [genBinom]
      have hsum1 : ∑ n ∈ Finset.range 1, genBinom (-α) n * w ^ n = 1 := by simp
      rw [show (0 : ℕ) + 1 = 1 from rfl, hsum1, hgb, Nat.cast_one, one_mul, pow_one, Nat.sub_self]
      simp only [pow_zero, one_mul]
      rw [← intervalIntegral.integral_const_mul]
      linear_combination -hftc
    | succ m =>
      have hprev := ih (Nat.succ_pos m)
      set k : ℕ := m + 1
      have hk_pos : 0 < k := Nat.succ_pos m
      have hk_ne : (k : ℂ) ≠ 0 := by exact_mod_cast hk_pos.ne'
      let u : ℝ → ℂ := fun t ↦ (1 + (t : ℂ) * w) ^ (-α - (k : ℂ))
      let u' : ℝ → ℂ := fun t ↦ (-α - (k : ℂ)) * w * (1 + (t : ℂ) * w) ^ (-α - ((k + 1 : ℕ) : ℂ))
      let v : ℝ → ℂ := fun t ↦ -(((1 - t : ℝ) : ℂ) ^ k) / (k : ℂ)
      let v' : ℝ → ℂ := fun t ↦ ((1 - t : ℝ) : ℂ) ^ (k - 1)
      have hu : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u (u' t) t := by
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        have hC : HasDerivAt (fun z : ℂ ↦ (1 + z * w) ^ (-α - (k : ℂ)))
            ((-α - (k : ℂ)) * (1 + (t : ℂ) * w) ^ (-α - (k : ℂ) - 1) * (1 * w)) (t : ℂ) :=
          (((hasDerivAt_id (t : ℂ)).mul_const w).const_add (1 : ℂ)).cpow_const
            (c := -α - (k : ℂ)) (hslit t ht)
        convert hC.comp_ofReal using 1
        dsimp [u']; push_cast; ring_nf
      have hv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt v (v' t) t := by
        intro t _
        have h1 : HasDerivAt (fun s : ℝ ↦ ((1 - s : ℝ) : ℂ)) (-1 : ℂ) t := by
          have hC : HasDerivAt (fun z : ℂ ↦ (1 : ℂ) - z) (-1 : ℂ) (t : ℂ) := by
            simpa using (hasDerivAt_id (t : ℂ)).const_sub (1 : ℂ)
          simpa [Complex.ofReal_sub] using hC.comp_ofReal
        have h2 := (h1.pow k).neg.div_const (k : ℂ)
        convert h2 using 1
        dsimp [v']; field_simp [hk_ne]
      have hu'_int : IntervalIntegrable u' volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        have hlin : ContinuousAt (fun s : ℝ ↦ 1 + (s : ℂ) * w) t :=
          continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
        exact (continuousAt_const.mul
          (continuousAt_cpow_const_comp hlin (hslit t ht))).continuousWithinAt
      have hv'_int : IntervalIntegrable v' volume 0 1 :=
        ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow (k - 1)).intervalIntegrable 0 1
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'_int hv'_int
      have hcomm : ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (k - 1) * (1 + (t : ℂ) * w) ^ (-α - (k : ℂ)) =
          ∫ t in (0 : ℝ)..1, u t * v' t := by
        apply intervalIntegral.integral_congr; intro t _; dsimp [u, v']; ring
      have huv1 : u 1 * v 1 = 0 := by
        dsimp [v]; simp [hk_pos.ne']
      have huv0 : u 0 * v 0 = -(1 / (k : ℂ)) := by
        dsimp [u, v]; simp [Complex.one_cpow]; ring
      have hrhs : ∫ t in (0 : ℝ)..1, u' t * v t =
          -((-α - (k : ℂ)) * w / (k : ℂ)) *
            ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ k * (1 + (t : ℂ) * w) ^ (-α - ((k + 1 : ℕ) : ℂ)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr; intro t _
        dsimp [u', v]; ring
      have hgb := genBinom_succ (-α) k
      have hstep : (k : ℂ) * genBinom (-α) k * w ^ k *
          (0 - -(1 / (k : ℂ)) -
            -((-α - (k : ℂ)) * w / (k : ℂ)) *
              ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ k *
                (1 + (t : ℂ) * w) ^ (-α - ((k + 1 : ℕ) : ℂ))) =
          genBinom (-α) k * w ^ k +
            ((k + 1 : ℕ) : ℂ) * genBinom (-α) (k + 1) * w ^ (k + 1) *
              ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ k *
                (1 + (t : ℂ) * w) ^ (-α - ((k + 1 : ℕ) : ℂ)) := by
        have h1 : (k : ℂ) * genBinom (-α) k * w ^ k * (1 / (k : ℂ)) = genBinom (-α) k * w ^ k := by
          field_simp [hk_ne]
        have h2 : (k : ℂ) * genBinom (-α) k * w ^ k * ((-α - (k : ℂ)) * w / (k : ℂ)) =
            ((k + 1 : ℕ) : ℂ) * genBinom (-α) (k + 1) * w ^ (k + 1) := by
          calc (k : ℂ) * genBinom (-α) k * w ^ k * ((-α - (k : ℂ)) * w / (k : ℂ))
              = ((-α - (k : ℂ)) * genBinom (-α) k) * (w ^ k * w) := by field_simp [hk_ne]
            _ = (((k + 1 : ℕ) : ℂ) * genBinom (-α) (k + 1)) * w ^ (k + 1) := by
                rw [← hgb, ← pow_succ]
            _ = ((k + 1 : ℕ) : ℂ) * genBinom (-α) (k + 1) * w ^ (k + 1) := by ring
        linear_combination h1 +
          (∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ k * (1 + (t : ℂ) * w) ^ (-α - ((k + 1 : ℕ) : ℂ))) * h2
      calc (1 + w) ^ (-α)
          = ∑ n ∈ Finset.range k, genBinom (-α) n * w ^ n +
              (k : ℂ) * genBinom (-α) k * w ^ k *
                ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (k - 1) * (1 + (t : ℂ) * w) ^ (-α - (k : ℂ)) := hprev
        _ = ∑ n ∈ Finset.range k, genBinom (-α) n * w ^ n +
              (genBinom (-α) k * w ^ k +
                ((k + 1 : ℕ) : ℂ) * genBinom (-α) (k + 1) * w ^ (k + 1) *
                  ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ k *
                    (1 + (t : ℂ) * w) ^ (-α - ((k + 1 : ℕ) : ℂ))) := by
            rw [hcomm, hibp, huv1, huv0, hrhs, hstep]
        _ = ∑ n ∈ Finset.range (k + 1), genBinom (-α) n * w ^ n +
              ((k + 1 : ℕ) : ℂ) * genBinom (-α) (k + 1) * w ^ (k + 1) *
                ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ ((k + 1) - 1) *
                  (1 + (t : ℂ) * w) ^ (-α - ((k + 1 : ℕ) : ℂ)) := by
            simp only [Nat.add_sub_cancel, Finset.sum_range_succ]; ring

/-- Uniform bound on `sector34 u₀`: `1 + t u y ∈ slitPlane` and `‖1 + t u y‖ ≥ 1 / √2`. -/
theorem sector34_one_add_norm_ge {u₀ : ℝ} {u : ℂ} (hu : u ∈ sector34 u₀)
    {t y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) :
    1 + (t : ℂ) * u * (y : ℂ) ∈ Complex.slitPlane ∧
      1 / Real.sqrt 2 ≤ ‖1 + (t : ℂ) * u * (y : ℂ)‖ := by
  have hnorm_sq : (1 / Real.sqrt 2) ^ 2 ≤ ‖1 + (t : ℂ) * u * (y : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (1 + (t : ℂ) * u * (y : ℂ)).re = 1 + t * y * u.re := by simp; ring
    have him : (1 + (t : ℂ) * u * (y : ℂ)).im = t * y * u.im := by simp; ring
    rw [hre, him]
    have hsq : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    set s : ℝ := t * y * ‖u‖
    have hre_ge : -(Real.sqrt 2 / 2) * s ≤ t * y * u.re := by
      have := mul_le_mul_of_nonneg_left hu.2.2 (mul_nonneg ht hy)
      dsimp [s]; linarith
    have hexpand : (1 + t * y * u.re) * (1 + t * y * u.re) + (t * y * u.im) * (t * y * u.im) =
        1 + 2 * (t * y * u.re) + s ^ 2 := by
      dsimp [s]; linear_combination (t * y) ^ 2 * hsq
    rw [hexpand, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hsq2 : (s - Real.sqrt 2 / 2) ^ 2 = s ^ 2 - Real.sqrt 2 * s + 1 / 2 := by
      have : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      linarith [show (s - Real.sqrt 2 / 2) ^ 2 = s ^ 2 - Real.sqrt 2 * s + (Real.sqrt 2 / 2) ^ 2 by ring]
    nlinarith [sq_nonneg (s - Real.sqrt 2 / 2)]
  have hnorm_ge : 1 / Real.sqrt 2 ≤ ‖1 + (t : ℂ) * u * (y : ℂ)‖ := by
    nlinarith [norm_nonneg (1 + (t : ℂ) * u * (y : ℂ)),
      show (0 : ℝ) ≤ 1 / Real.sqrt 2 by positivity]
  refine ⟨?_, hnorm_ge⟩
  rw [Complex.mem_slitPlane_iff]
  by_cases him0 : u.im = 0
  · left
    have hre_pos : 0 < u.re := by
      by_contra hle; push Not at hle
      have hnorm_eq : ‖u‖ = -u.re := by
        rw [Complex.norm_def, Complex.normSq_apply, him0, mul_zero, add_zero, ← sq,
            Real.sqrt_sq_eq_abs, abs_of_nonpos hle]
      have hsqrt_lt : Real.sqrt 2 / 2 < 1 := by
        have : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        linarith
      nlinarith [hu.1, hu.2.2]
    have hre : (1 + (t : ℂ) * u * (y : ℂ)).re = 1 + t * y * u.re := by simp; ring
    rw [hre]; nlinarith [mul_nonneg ht hy]
  · by_cases hty : t * y = 0
    · left
      have : (t : ℂ) * u * (y : ℂ) = 0 := by
        have htyC : (t : ℂ) * (y : ℂ) = 0 := by exact_mod_cast hty
        calc (t : ℂ) * u * (y : ℂ) = u * ((t : ℂ) * (y : ℂ)) := by ring
          _ = 0 := by rw [htyC, mul_zero]
      rw [this, add_zero]; simp
    · right
      have him : (1 + (t : ℂ) * u * (y : ℂ)).im = t * y * u.im := by simp; ring
      rw [him]; exact mul_ne_zero hty him0

/-- Universal norm bound on principal-branch complex powers:
`‖z ^ w‖ ≤ ‖z‖ ^ w.re * exp (|w.im| * π)` for `z ≠ 0`. -/
theorem norm_cpow_le_rpow_mul_exp {z w : ℂ} (hz : z ≠ 0) :
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (|w.im| * Real.pi) := by
  rw [Complex.norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  have harg : |z.arg| ≤ Real.pi := abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  calc -(z.arg * w.im) ≤ |-(z.arg * w.im)| := le_abs_self _
    _ = |z.arg| * |w.im| := by rw [abs_neg, abs_mul]
    _ ≤ Real.pi * |w.im| := mul_le_mul_of_nonneg_right harg (abs_nonneg _)
    _ = |w.im| * Real.pi := mul_comm _ _

/-- Elementary moment integral identity: `∫_{y > 0} y^m exp(-c y) dy = m! / c^{m+1}` for `c > 0`. -/
theorem integral_pow_mul_exp_Ioi_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ ↦ y ^ m * Real.exp (-c * y)) (Set.Ioi 0) ∧
      ∫ y in Set.Ioi (0 : ℝ), y ^ m * Real.exp (-c * y) = (m.factorial : ℝ) / c ^ (m + 1) := by
  have hint_gamma : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * t ^ ((m + 1 : ℝ) - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hval_gamma : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ ((m + 1 : ℝ) - 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_eq_integral (by positivity), Real.Gamma_nat_eq_factorial]
  have hpow_eq : ∀ t : ℝ, 0 < t → Real.exp (-t) * t ^ ((m + 1 : ℝ) - 1) = t ^ m * Real.exp (-t) := by
    intro t ht
    rw [show ((m + 1 : ℝ) - 1) = (m : ℝ) by ring, Real.rpow_natCast, mul_comm]
  have hint0 : IntegrableOn (fun t : ℝ ↦ t ^ m * Real.exp (-t)) (Set.Ioi 0) :=
    hint_gamma.congr_fun (fun t ht ↦ hpow_eq t ht) measurableSet_Ioi
  have hval0 : ∫ t in Set.Ioi (0 : ℝ), t ^ m * Real.exp (-t) = (m.factorial : ℝ) := by
    rw [← hval_gamma]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ (hpow_eq t ht).symm)
  have hcomp_val := MeasureTheory.integral_comp_mul_left_Ioi
    (fun t : ℝ ↦ t ^ m * Real.exp (-t)) (0 : ℝ) hc
  simp only [mul_zero, smul_eq_mul] at hcomp_val
  have hscale_eq : (fun y : ℝ ↦ (c * y) ^ m * Real.exp (-(c * y))) =
      fun y : ℝ ↦ c ^ m * (y ^ m * Real.exp (-c * y)) := by
    ext y; rw [mul_pow, neg_mul]; ring
  have hint_c : IntegrableOn (fun y : ℝ ↦ y ^ m * Real.exp (-c * y)) (Set.Ioi 0) := by
    have hcomp_int : IntegrableOn (fun y : ℝ ↦ (c * y) ^ m * Real.exp (-(c * y))) (Set.Ioi 0) :=
      (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
        (fun t : ℝ ↦ t ^ m * Real.exp (-t)) (0 : ℝ) hc).mpr (by simpa using hint0)
    rw [hscale_eq] at hcomp_int
    have hmul : IntegrableOn (fun y : ℝ ↦ (c ^ m)⁻¹ * (c ^ m * (y ^ m * Real.exp (-c * y)))) (Set.Ioi 0) :=
      hcomp_int.const_mul (c ^ m)⁻¹
    exact hmul.congr_fun (fun y _ ↦ by field_simp [(pow_pos hc m).ne']) measurableSet_Ioi
  refine ⟨hint_c, ?_⟩
  rw [hscale_eq, integral_const_mul, hval0] at hcomp_val
  have hcm : c ^ m ≠ 0 := (pow_pos hc m).ne'
  have hc_ne : c ≠ 0 := hc.ne'
  rw [pow_succ']
  field_simp [hcm, hc_ne] at hcomp_val ⊢
  linarith

private lemma integrableOn_one_add_pow_mul_exp {c : ℝ} (hc : 0 < c) (d : ℕ) :
    IntegrableOn (fun r : ℝ ↦ (1 + r) ^ d * Real.exp (-c * r)) (Set.Ioi 0) := by
  have hbin : (fun r : ℝ ↦ ∑ m ∈ Finset.range (d + 1),
      (Nat.choose d m : ℝ) * (r ^ m * Real.exp (-c * r))) =
      fun r : ℝ ↦ (1 + r) ^ d * Real.exp (-c * r) := by
    ext r; rw [add_comm 1 r, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _; simp; ring
  rw [← hbin]
  exact integrable_finsetSum _ fun m _ ↦ (integral_pow_mul_exp_Ioi_le m hc).1.const_mul _

/-- Real-axis Eichler tail integral `Φ_{[1,∞)}(u) = ∫_1^∞ b(y) (1 + u y)^{-k} dy`. -/
def PhiReal (k : ℂ) (b : ℂ → ℂ) (u : ℂ) : ℂ :=
  ∫ y in Set.Ioi (1 : ℝ), b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-k)

/-- Formal Taylor coefficients of `Φ_{[1,∞)}^{(j)}(u)`. -/
def phiFormalCoeff (k : ℂ) (b : ℂ → ℂ) (j n : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * risingFac k j * genBinom (-(k + (j : ℂ))) n *
    ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ (n + j) * b (y : ℂ)

/-- Exponential decay hypothesis on `b` along `Re z ≥ 1`. -/
structure ExpDecayKernel (b : ℂ → ℂ) (C_b c_b : ℝ) : Prop where
  C_nonneg : 0 ≤ C_b
  c_pos : 0 < c_b
  holo : DifferentiableOn ℂ b {z : ℂ | (1 / 2 : ℝ) < z.re}
  bound : ∀ z : ℂ, 1 ≤ z.re → ‖b z‖ ≤ C_b * Real.exp (-c_b * z.re)
  deriv_bound : ∀ z : ℂ, 1 ≤ z.re → ‖deriv b z‖ ≤ C_b * Real.exp (-c_b * z.re)

/-- For `u ∈ Complex.slitPlane` and `y > 0`, `1 + u * y ∈ Complex.slitPlane`. -/
theorem one_add_mul_ofReal_mem_slitPlane {u : ℂ} (hu : u ∈ Complex.slitPlane)
    {y : ℝ} (hy : 0 < y) : 1 + u * (y : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hu ⊢
  rcases hu with hre | him
  · left; simp; nlinarith
  · right; simp [mul_ne_zero him hy.ne']

/-- Uniform positive lower bound on `‖1 + u * y‖` on a small closed ball inside `Complex.slitPlane`. -/
private lemma slitPlane_ball_lower_bound {u₀ : ℂ} (hu₀ : u₀ ∈ Complex.slitPlane) :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ Metric.closedBall u₀ δ ⊆ Complex.slitPlane ∧
      ∀ u ∈ Metric.closedBall u₀ δ, ∀ y : ℝ, 0 ≤ y → η ≤ ‖1 + u * (y : ℂ)‖ := by
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.isOpen_iff.mp Complex.isOpen_slitPlane u₀ hu₀
  let δ : ℝ := min (δ₀ / 2) (‖u₀‖ / 2)
  have hu₀_ne : u₀ ≠ 0 := Complex.slitPlane_ne_zero hu₀
  have hδ : 0 < δ := lt_min (by linarith) (div_pos (norm_pos_iff.mpr hu₀_ne) zero_lt_two)
  have hcl_sub : Metric.closedBall u₀ δ ⊆ Complex.slitPlane := by
    intro u hu
    apply hball₀
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hu) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hnorm_low : ∀ u ∈ Metric.closedBall u₀ δ, ‖u₀‖ / 2 ≤ ‖u‖ := fun u hu ↦ by
    have hd : ‖u - u₀‖ ≤ ‖u₀‖ / 2 := by
      rw [← Complex.dist_eq]
      exact (Metric.mem_closedBall.mp hu).trans (min_le_right _ _)
    have htri : ‖u₀‖ - ‖u‖ ≤ ‖u - u₀‖ := by
      have := norm_sub_norm_le u₀ u; rw [norm_sub_rev] at this; exact this
    linarith
  let R : ℝ := 4 / ‖u₀‖
  have hR_pos : 0 < R := div_pos (by norm_num) (norm_pos_iff.mpr hu₀_ne)
  let K : Set (ℂ × ℝ) := Metric.closedBall u₀ δ ×ˢ Set.Icc 0 R
  have hK_comp : IsCompact K := (isCompact_closedBall u₀ δ).prod isCompact_Icc
  have hK_ne : K.Nonempty := ⟨(u₀, 0), Metric.mem_closedBall_self hδ.le, left_mem_Icc.mpr hR_pos.le⟩
  let g : ℂ × ℝ → ℝ := fun p ↦ ‖1 + p.1 * (p.2 : ℂ)‖
  have hg_cont : Continuous g :=
    (continuous_const.add (continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd))).norm
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hK_comp.exists_isMinOn hK_ne hg_cont.continuousOn
  have hg_pos : 0 < g p₀ := by
    dsimp [g]
    rw [norm_pos_iff]
    by_cases hp2 : p₀.2 = 0
    · simp [hp2]
    · have hp2_pos : 0 < p₀.2 := lt_of_le_of_ne hp₀K.2.1 (Ne.symm hp2)
      exact Complex.slitPlane_ne_zero (one_add_mul_ofReal_mem_slitPlane (hcl_sub hp₀K.1) hp2_pos)
  refine ⟨δ, min 1 (g p₀), hδ, lt_min zero_lt_one hg_pos, hcl_sub, fun u hu y hy ↦ ?_⟩
  by_cases hyR : y ≤ R
  · have hmin : g p₀ ≤ g (u, y) := hp₀min ⟨hu, hy, hyR⟩
    exact (min_le_right 1 (g p₀)).trans hmin
  · push Not at hyR
    have hbig : 2 ≤ ‖u * (y : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
      have h1 := hnorm_low u hu
      have h2 : (‖u₀‖ / 2) * R = 2 := by
        dsimp [R]; field_simp [(norm_pos_iff.mpr hu₀_ne).ne']; norm_num
      have h3 : (‖u₀‖ / 2) * R ≤ ‖u‖ * y :=
        mul_le_mul h1 hyR.le hR_pos.le (norm_nonneg u)
      linarith
    have htri : ‖u * (y : ℂ)‖ - 1 ≤ ‖1 + u * (y : ℂ)‖ := by
      have := norm_sub_norm_le (u * (y : ℂ)) (-1 : ℂ)
      simpa [sub_neg_eq_add, add_comm] using this
    exact (min_le_left 1 (g p₀)).trans (by linarith)

/-- `PhiReal` and all its `j`-th derivatives are holomorphic on `Complex.slitPlane`, with the
exact integral formula `(-1)^j (k)_j ∫_1^∞ y^j b(y) (1 + u y)^{-(k+j)} dy`. -/
theorem PhiReal_iteratedDeriv {b : ℂ → ℂ} {C_b c_b : ℝ} (hb : ExpDecayKernel b C_b c_b)
    (k : ℂ) (j : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv j (PhiReal k b)) Complex.slitPlane ∧
      ∀ u ∈ Complex.slitPlane,
        iteratedDeriv j (PhiReal k b) u =
          (-1 : ℂ) ^ j * risingFac k j *
            ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ j * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-(k + (j : ℂ))) := by
  have hCb : 0 ≤ C_b := hb.C_nonneg
  have hdiff_step : ∀ (α : ℂ) (m : ℕ) (u₀ : ℂ), u₀ ∈ Complex.slitPlane →
      HasDerivAt
        (fun u : ℂ ↦ ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ m * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-α))
        ((-α) * ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ (m + 1) * b (y : ℂ) * (1 + u₀ * (y : ℂ)) ^ (-(α + 1))) u₀ := by
    intro α m u₀ hu₀
    obtain ⟨δ, η, hδ, hη, hcl_sub, hlow⟩ := slitPlane_ball_lower_bound hu₀
    let s : Set ℂ := Metric.ball u₀ δ
    have hs_nhds : s ∈ 𝓝 u₀ := Metric.ball_mem_nhds u₀ hδ
    have hs_sub : s ⊆ Metric.closedBall u₀ δ := Metric.ball_subset_closedBall
    let M_u : ℝ := ‖u₀‖ + δ
    have hpow_bd : ∀ (β : ℂ), ∃ K_β : ℝ, ∃ d_β : ℕ, 0 ≤ K_β ∧
        ∀ u ∈ s, ∀ y : ℝ, 1 ≤ y → ‖(1 + u * (y : ℂ)) ^ (-β)‖ ≤ K_β * y ^ d_β := by
      intro β
      let d : ℕ := Nat.ceil (max (-β.re) 0)
      have hd_ge : -β.re ≤ (d : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
      have hC_const : ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ s, ∀ y : ℝ, 1 ≤ y →
          ‖1 + u * (y : ℂ)‖ ^ (-β.re) ≤ K * y ^ d := by
        by_cases hneg : -β.re ≤ 0
        · refine ⟨η ^ (-β.re), Real.rpow_nonneg hη.le _, fun u hu y hy ↦ ?_⟩
          have h1 : ‖1 + u * (y : ℂ)‖ ^ (-β.re) ≤ η ^ (-β.re) :=
            Real.rpow_le_rpow_of_nonpos hη (hlow u (hs_sub hu) y (by linarith)) hneg
          have h2 : (1 : ℝ) ≤ y ^ d := one_le_pow₀ hy
          nlinarith [Real.rpow_nonneg hη.le (-β.re)]
        · push Not at hneg
          refine ⟨(1 + M_u) ^ (-β.re), by positivity, fun u hu y hy ↦ ?_⟩
          have hu_le : ‖u‖ ≤ M_u := by
            have hd' : ‖u - u₀‖ < δ := by rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hu
            have htri := norm_sub_norm_le u u₀
            dsimp [M_u]; linarith
          have hup : ‖1 + u * (y : ℂ)‖ ≤ (1 + M_u) * y := by
            calc ‖1 + u * (y : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖u * (y : ℂ)‖ := norm_add_le _ _
              _ = 1 + ‖u‖ * y := by
                  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
              _ ≤ 1 * y + M_u * y := by nlinarith
              _ = (1 + M_u) * y := by ring
          calc ‖1 + u * (y : ℂ)‖ ^ (-β.re)
              ≤ ((1 + M_u) * y) ^ (-β.re) :=
                Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
            _ = (1 + M_u) ^ (-β.re) * y ^ (-β.re) :=
                Real.mul_rpow (by positivity) (by linarith)
            _ ≤ (1 + M_u) ^ (-β.re) * y ^ (d : ℝ) := by
                have hy_rpow : y ^ (-β.re) ≤ y ^ (d : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hy hd_ge
                exact mul_le_mul_of_nonneg_left hy_rpow (by positivity)
            _ = (1 + M_u) ^ (-β.re) * y ^ d := by rw [Real.rpow_natCast]
      obtain ⟨K, hK, hKbd⟩ := hC_const
      refine ⟨K * Real.exp (|(-β).im| * Real.pi), d, by positivity, fun u hu y hy ↦ ?_⟩
      have hne : 1 + u * (y : ℂ) ≠ 0 :=
        Complex.slitPlane_ne_zero (one_add_mul_ofReal_mem_slitPlane (hcl_sub (hs_sub hu)) (by linarith))
      calc ‖(1 + u * (y : ℂ)) ^ (-β)‖
          ≤ ‖1 + u * (y : ℂ)‖ ^ (-β).re * Real.exp (|(-β).im| * Real.pi) :=
            norm_cpow_le_rpow_mul_exp hne
        _ ≤ (K * y ^ d) * Real.exp (|(-β).im| * Real.pi) := by
            rw [Complex.neg_re]; exact mul_le_mul_of_nonneg_right (hKbd u hu y hy) (Real.exp_pos _).le
        _ = K * Real.exp (|(-β).im| * Real.pi) * y ^ d := by ring
    obtain ⟨K₀, d₀, hK₀, hbd₀⟩ := hpow_bd α
    obtain ⟨K₁, d₁, hK₁, hbd₁⟩ := hpow_bd (α + 1)
    let F : ℂ → ℝ → ℂ := fun u y ↦ (y : ℂ) ^ m * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-α)
    let F' : ℂ → ℝ → ℂ := fun u y ↦ (-α) * ((y : ℂ) ^ (m + 1) * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-(α + 1)))
    have hcont_b : ContinuousOn (fun y : ℝ ↦ b (y : ℂ)) (Set.Ioi 1) := by
      intro y hy
      have hy_re : (1 / 2 : ℝ) < ((y : ℂ)).re := by
        simp; linarith [Set.mem_Ioi.mp hy]
      have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact (((hb.holo (y : ℂ) hy_re).differentiableAt (hopen.mem_nhds hy_re)).continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have hmeas_F : ∀ u ∈ s, AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi 1)) := by
      intro u hu
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      have hpow_c : ContinuousOn (fun y : ℝ ↦ (1 + u * (y : ℂ)) ^ (-α)) (Set.Ioi 1) := by
        intro y hy
        have hsl : 1 + u * (y : ℂ) ∈ Complex.slitPlane :=
          one_add_mul_ofReal_mem_slitPlane (hcl_sub (hs_sub hu)) (by linarith [Set.mem_Ioi.mp hy])
        exact (continuousAt_cpow_const_comp
          (continuousAt_const.add (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)) hsl).continuousWithinAt
      exact (((Complex.continuous_ofReal.pow m).continuousOn).mul hcont_b).mul hpow_c
    have hmeas_F' : AEStronglyMeasurable (F' u₀) (volume.restrict (Set.Ioi 1)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      have hpow_c : ContinuousOn (fun y : ℝ ↦ (1 + u₀ * (y : ℂ)) ^ (-(α + 1))) (Set.Ioi 1) := by
        intro y hy
        have hsl : 1 + u₀ * (y : ℂ) ∈ Complex.slitPlane :=
          one_add_mul_ofReal_mem_slitPlane hu₀ (by linarith [Set.mem_Ioi.mp hy])
        exact (continuousAt_cpow_const_comp
          (continuousAt_const.add (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)) hsl).continuousWithinAt
      exact continuousOn_const.mul ((((Complex.continuous_ofReal.pow (m + 1)).continuousOn).mul hcont_b).mul hpow_c)
    have hF_int : Integrable (F u₀) (volume.restrict (Set.Ioi 1)) := by
      have hdom : IntegrableOn (fun y : ℝ ↦ (C_b * K₀) * (y ^ (m + d₀) * Real.exp (-c_b * y))) (Set.Ioi 1) :=
        ((integral_pow_mul_exp_Ioi_le (m + d₀) hb.c_pos).1.mono_set
          (Set.Ioi_subset_Ioi zero_le_one)).const_mul (C_b * K₀)
      refine hdom.mono' (hmeas_F u₀ (Metric.mem_ball_self hδ)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy1 : (1 : ℝ) ≤ y := (Set.mem_Ioi.mp hy).le
      dsimp [F]
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have hb_y : ‖b (y : ℂ)‖ ≤ C_b * Real.exp (-c_b * y) := by simpa using hb.bound (y : ℂ) (by simpa using hy1)
      have hp_y := hbd₀ u₀ (Metric.mem_ball_self hδ) y hy1
      calc y ^ m * ‖b (y : ℂ)‖ * ‖(1 + u₀ * (y : ℂ)) ^ (-α)‖
          ≤ y ^ m * (C_b * Real.exp (-c_b * y)) * (K₀ * y ^ d₀) := by
            have h1 : y ^ m * ‖b (y : ℂ)‖ ≤ y ^ m * (C_b * Real.exp (-c_b * y)) :=
              mul_le_mul_of_nonneg_left hb_y (by positivity)
            exact mul_le_mul h1 hp_y (norm_nonneg _) (by positivity)
        _ = C_b * K₀ * (y ^ (m + d₀) * Real.exp (-c_b * y)) := by rw [pow_add]; ring
    let bound : ℝ → ℝ := fun y ↦ (‖α‖ * C_b * K₁) * (y ^ (m + 1 + d₁) * Real.exp (-c_b * y))
    have hbound_int : Integrable bound (volume.restrict (Set.Ioi 1)) :=
      ((integral_pow_mul_exp_Ioi_le (m + 1 + d₁) hb.c_pos).1.mono_set
        (Set.Ioi_subset_Ioi zero_le_one)).const_mul (‖α‖ * C_b * K₁)
    have hbound_ae : ∀ᵐ y ∂volume.restrict (Set.Ioi 1), ∀ u ∈ s, ‖F' u y‖ ≤ bound y := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy u hu
      have hy1 : (1 : ℝ) ≤ y := (Set.mem_Ioi.mp hy).le
      dsimp [F', bound]
      rw [norm_mul, norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      have hb_y : ‖b (y : ℂ)‖ ≤ C_b * Real.exp (-c_b * y) := by simpa using hb.bound (y : ℂ) (by simpa using hy1)
      have hp_y := hbd₁ u hu y hy1
      calc ‖α‖ * (y ^ (m + 1) * ‖b (y : ℂ)‖ * ‖(1 + u * (y : ℂ)) ^ (-(α + 1))‖)
          ≤ ‖α‖ * (y ^ (m + 1) * (C_b * Real.exp (-c_b * y)) * (K₁ * y ^ d₁)) := by
            have h1 : y ^ (m + 1) * ‖b (y : ℂ)‖ ≤ y ^ (m + 1) * (C_b * Real.exp (-c_b * y)) :=
              mul_le_mul_of_nonneg_left hb_y (by positivity)
            exact mul_le_mul_of_nonneg_left (mul_le_mul h1 hp_y (norm_nonneg _) (by positivity)) (norm_nonneg _)
        _ = ‖α‖ * C_b * K₁ * (y ^ (m + 1 + d₁) * Real.exp (-c_b * y)) := by rw [pow_add]; ring
    have hderiv_ae : ∀ᵐ y ∂volume.restrict (Set.Ioi 1), ∀ u ∈ s, HasDerivAt (fun w ↦ F w y) (F' u y) u := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy u hu
      have hy_pos : 0 < y := lt_trans zero_lt_one (Set.mem_Ioi.mp hy)
      have hsl : 1 + u * (y : ℂ) ∈ Complex.slitPlane :=
        one_add_mul_ofReal_mem_slitPlane (hcl_sub (hs_sub hu)) hy_pos
      have hlin : HasDerivAt (fun w : ℂ ↦ 1 + w * (y : ℂ)) (y : ℂ) u := by
        simpa using ((hasDerivAt_id u).mul_const (y : ℂ)).const_add (1 : ℂ)
      have hpow := (hlin.cpow_const (c := -α) hsl).const_mul ((y : ℂ) ^ m * b (y : ℂ))
      convert hpow using 1
      dsimp [F']; rw [pow_succ]; ring_nf
    have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds
      (Filter.eventually_of_mem hs_nhds hmeas_F) hF_int hmeas_F' hbound_ae hbound_int hderiv_ae).2
    convert hres using 1
    rw [← integral_const_mul]
  induction j with
  | zero =>
    refine ⟨fun u hu ↦ (hdiff_step k 0 u hu).differentiableAt.differentiableWithinAt.congr
        (fun w _ ↦ by simp [PhiReal]) (by simp [PhiReal]), fun u _ ↦ by simp [PhiReal]⟩
  | succ j ih =>
    obtain ⟨_, hform⟩ := ih
    have heq_step : ∀ u ∈ Complex.slitPlane,
        iteratedDeriv (j + 1) (PhiReal k b) u =
          (-1 : ℂ) ^ (j + 1) * risingFac k (j + 1) *
            ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ (j + 1) * b (y : ℂ) *
              (1 + u * (y : ℂ)) ^ (-(k + ((j + 1 : ℕ) : ℂ))) := by
      intro u hu
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (PhiReal k b) =ᶠ[𝓝 u]
          fun w ↦ (-1 : ℂ) ^ j * risingFac k j *
            ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ j * b (y : ℂ) * (1 + w * (y : ℂ)) ^ (-(k + (j : ℂ))) := by
        filter_upwards [Complex.isOpen_slitPlane.mem_nhds hu] with w hw
        exact hform w hw
      rw [hev.deriv_eq]
      have hd := (hdiff_step (k + (j : ℂ)) j u hu).const_mul ((-1 : ℂ) ^ j * risingFac k j)
      rw [hd.deriv, risingFac_succ, pow_succ]
      have hexp : -(k + (j : ℂ) + 1) = -(k + ((j + 1 : ℕ) : ℂ)) := by push_cast; ring
      rw [hexp]; ring
    refine ⟨fun u hu ↦ ?_, heq_step⟩
    have hd := (hdiff_step (k + ((j + 1 : ℕ) : ℂ)) (j + 1) u hu).const_mul
      ((-1 : ℂ) ^ (j + 1) * risingFac k (j + 1))
    exact hd.differentiableAt.differentiableWithinAt.congr
      (fun w hw ↦ heq_step w hw) (heq_step u hu)

/-- Elementary binomial coefficient bound: `‖N * genBinom α N‖ ≤ (2 + ‖α‖) ^ N`. -/
theorem norm_mul_genBinom_le (α : ℂ) (N : ℕ) :
    ‖(N : ℂ) * genBinom α N‖ ≤ (2 + ‖α‖) ^ N := by
  cases N with
  | zero => simp
  | succ m =>
    unfold genBinom
    have hprod2 : ‖∏ j ∈ Finset.range (m + 1), (α - (j : ℂ))‖ ≤
        (2 + ‖α‖) ^ (m + 1) * (m.factorial : ℝ) := by
      rw [norm_prod, Finset.prod_range_succ']
      simp only [Nat.cast_zero, sub_zero]
      have htail : ∏ j ∈ Finset.range m, ‖α - ((j + 1 : ℕ) : ℂ)‖ ≤
          (2 + ‖α‖) ^ m * (m.factorial : ℝ) := by
        induction m with
        | zero => simp
        | succ k ih =>
          rw [Finset.prod_range_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul]
          have hstep : ‖α - ((k + 1 : ℕ) : ℂ)‖ ≤ (2 + ‖α‖) * ((k + 1 : ℕ) : ℝ) := by
            calc ‖α - ((k + 1 : ℕ) : ℂ)‖ ≤ ‖α‖ + ‖((k + 1 : ℕ) : ℂ)‖ := norm_sub_le _ _
              _ = ‖α‖ + ((k + 1 : ℕ) : ℝ) := by rw [Complex.norm_natCast]
              _ ≤ (2 + ‖α‖) * ((k + 1 : ℕ) : ℝ) := by
                  push_cast; nlinarith [norm_nonneg α, Nat.cast_nonneg (α := ℝ) k]
          calc (∏ j ∈ Finset.range k, ‖α - ((j + 1 : ℕ) : ℂ)‖) * ‖α - ((k + 1 : ℕ) : ℂ)‖
              ≤ ((2 + ‖α‖) ^ k * (k.factorial : ℝ)) * ((2 + ‖α‖) * ((k + 1 : ℕ) : ℝ)) :=
                mul_le_mul ih hstep (norm_nonneg _) (by positivity)
            _ = (2 + ‖α‖) ^ k * (2 + ‖α‖) * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) := by ring
      calc (∏ j ∈ Finset.range m, ‖α - ((j + 1 : ℕ) : ℂ)‖) * ‖α‖
          ≤ ((2 + ‖α‖) ^ m * (m.factorial : ℝ)) * (2 + ‖α‖) :=
            mul_le_mul htail (by linarith) (norm_nonneg α) (by positivity)
        _ = (2 + ‖α‖) ^ (m + 1) * (m.factorial : ℝ) := by rw [pow_succ]; ring
    rw [norm_mul, Complex.norm_natCast, norm_div, Complex.norm_natCast,
        Nat.factorial_succ, Nat.cast_mul]
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hmf_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    rw [mul_div_assoc', div_le_iff₀ (mul_pos hm1_pos hmf_pos)]
    calc ((m + 1 : ℕ) : ℝ) * ‖∏ j ∈ Finset.range (m + 1), (α - (j : ℂ))‖
        ≤ ((m + 1 : ℕ) : ℝ) * ((2 + ‖α‖) ^ (m + 1) * (m.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod2 hm1_pos.le
      _ = (2 + ‖α‖) ^ (m + 1) * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)) := by ring

/-- **Lemma 3.2(a)**: `iteratedDeriv j (PhiReal k b)` has uniform Gevrey-1 asymptotics on
`sector34 u₀` with formal coefficients `phiFormalCoeff k b j`. -/
theorem PhiReal_iteratedDeriv_hasGevrey1Asymp {b : ℂ → ℂ} {C_b c_b : ℝ}
    (hb : ExpDecayKernel b C_b c_b) (k : ℂ) (j : ℕ) {u₀ : ℝ} (_hu₀ : 0 < u₀) :
    HasGevrey1Asymp (sector34 u₀) (iteratedDeriv j (PhiReal k b)) (phiFormalCoeff k b j) := by
  have hCb : 0 ≤ C_b := hb.C_nonneg
  set α : ℂ := k + (j : ℂ)
  set N₀ : ℕ := max 1 (Nat.ceil (-α.re))
  have hN₀_pos : 1 ≤ N₀ := le_max_left _ _
  have hN₀_ge : -α.re ≤ (N₀ : ℝ) :=
    (Nat.le_ceil (-α.re)).trans (Nat.cast_le.mpr (le_max_right 1 _))
  let pref : ℂ := (-1 : ℂ) ^ j * risingFac k j
  have hcont_b : ContinuousOn (fun y : ℝ ↦ b (y : ℂ)) (Set.Ioi 1) := by
    intro y hy
    have hy_re : (1 / 2 : ℝ) < ((y : ℂ)).re := by simp; linarith [Set.mem_Ioi.mp hy]
    have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
    exact (((hb.holo (y : ℂ) hy_re).differentiableAt (hopen.mem_nhds hy_re)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hint_mom : ∀ m : ℕ, IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ m * b (y : ℂ)) (Set.Ioi 1) := fun m ↦ by
    have hdom : IntegrableOn (fun y : ℝ ↦ C_b * (y ^ m * Real.exp (-c_b * y))) (Set.Ioi 1) :=
      ((integral_pow_mul_exp_Ioi_le m hb.c_pos).1.mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul C_b
    refine hdom.mono' (((Complex.continuous_ofReal.pow m).continuousOn.mul hcont_b).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy1 : (1 : ℝ) ≤ y := (Set.mem_Ioi.mp hy).le
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hby : ‖b (y : ℂ)‖ ≤ C_b * Real.exp (-c_b * y) := by simpa using hb.bound (y : ℂ) (by simpa using hy1)
    calc y ^ m * ‖b (y : ℂ)‖ ≤ y ^ m * (C_b * Real.exp (-c_b * y)) := by gcongr
      _ = C_b * (y ^ m * Real.exp (-c_b * y)) := by ring
  have hcb_pos : 0 < c_b := hb.c_pos
  have hsq2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr zero_lt_two
  let B₁ : ℝ := (2 + ‖-α‖) * Real.sqrt 2 * (2 / c_b)
  have hB₁_pos : 0 < B₁ := by positivity
  let C₁ : ℝ := ‖pref‖ * C_b * (Real.sqrt 2) ^ (α.re) * Real.exp (|α.im| * Real.pi) *
      (2 ^ j * (j.factorial : ℝ) / c_b ^ (j + 1))
  have hC₁_nn : 0 ≤ C₁ := by positivity
  have hbig : ∀ N : ℕ, N₀ ≤ N → ∀ u ∈ sector34 u₀,
      ‖iteratedDeriv j (PhiReal k b) u - ∑ n ∈ Finset.range N, phiFormalCoeff k b j n * u ^ n‖ ≤
        C₁ * B₁ ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by
    intro N hN u hu
    have hu_slit : u ∈ Complex.slitPlane := (sector34_subset_slitDisk (lt_add_one u₀) hu).2.2
    rw [(PhiReal_iteratedDeriv hb k j).2 u hu_slit]
    have hN1 : 1 ≤ N := le_trans hN₀_pos hN
    let rem : ℝ → ℂ := fun y ↦
      (N : ℂ) * genBinom (-α) N * (u * (y : ℂ)) ^ N *
        ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))
    have hrem_pt : ∀ y ∈ Set.Ioi (1 : ℝ),
        (y : ℂ) ^ j * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-α) -
          ∑ n ∈ Finset.range N, genBinom (-α) n * u ^ n * ((y : ℂ) ^ (n + j) * b (y : ℂ)) =
        (y : ℂ) ^ j * b (y : ℂ) * rem y := by
      intro y hy
      have hy_pos : 0 < y := lt_trans zero_lt_one (Set.mem_Ioi.mp hy)
      have hty := cpow_taylor_integral_remainder α (u * (y : ℂ)) N hN1 (fun t ht ↦ by
        have := (sector34_one_add_norm_ge hu ht.1 hy_pos.le).1
        rwa [mul_assoc] at this)
      have hsum_eq : (y : ℂ) ^ j * b (y : ℂ) *
          (∑ n ∈ Finset.range N, genBinom (-α) n * (u * (y : ℂ)) ^ n) =
          ∑ n ∈ Finset.range N, genBinom (-α) n * u ^ n * ((y : ℂ) ^ (n + j) * b (y : ℂ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [mul_pow, pow_add]; ring
      rw [hty, mul_add, hsum_eq, add_sub_cancel_left]
    have hrem_bd : ∀ y ∈ Set.Ioi (1 : ℝ),
        ‖(y : ℂ) ^ j * b (y : ℂ) * rem y‖ ≤
          (C_b * (2 + ‖-α‖) ^ N * (Real.sqrt 2) ^ (α.re + (N : ℝ)) *
            Real.exp (|α.im| * Real.pi) * ‖u‖ ^ N) * (y ^ (N + j) * Real.exp (-c_b * y)) := by
      intro y hy
      have hy1 : (1 : ℝ) ≤ y := (Set.mem_Ioi.mp hy).le
      have hint_t : ‖∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) *
          (1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))‖ ≤
          (Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi) := by
        have hbd_t : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
            ‖((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))‖ ≤
              (Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi) := by
          intro t ht
          rw [Set.uIoc_of_le zero_le_one] at ht
          have ⟨hsl, hng⟩ := sector34_one_add_norm_ge (y := y) hu ht.1.le (by linarith)
          rw [mul_assoc] at hsl hng
          have h1t : ‖((1 - t : ℝ) : ℂ) ^ (N - 1)‖ ≤ 1 := by
            rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
            exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
          have hcpow : ‖(1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))‖ ≤
              (Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi) := by
            have hne := Complex.slitPlane_ne_zero hsl
            have h1 := norm_cpow_le_rpow_mul_exp (z := 1 + (t : ℂ) * (u * (y : ℂ))) (w := -α - (N : ℂ)) hne
            have hre_eq : (-α - (N : ℂ)).re = -(α.re + (N : ℝ)) := by simp; ring
            have him_eq : |(-α - (N : ℂ)).im| = |α.im| := by simp
            rw [hre_eq, him_eq] at h1
            have hexp_nonpos : -(α.re + (N : ℝ)) ≤ 0 := by
              have hN_cast : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
              linarith
            have hrpow_le : ‖1 + (t : ℂ) * (u * (y : ℂ))‖ ^ (-(α.re + (N : ℝ))) ≤
                (1 / Real.sqrt 2) ^ (-(α.re + (N : ℝ))) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hng hexp_nonpos
            have hinv_eq : (1 / Real.sqrt 2) ^ (-(α.re + (N : ℝ))) = (Real.sqrt 2) ^ (α.re + (N : ℝ)) := by
              rw [one_div, Real.inv_rpow (Real.sqrt_nonneg 2), Real.rpow_neg (Real.sqrt_nonneg 2), inv_inv]
            rw [hinv_eq] at hrpow_le
            exact h1.trans (mul_le_mul_of_nonneg_right hrpow_le (Real.exp_pos _).le)
          rw [norm_mul]
          calc ‖((1 - t : ℝ) : ℂ) ^ (N - 1)‖ * ‖(1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))‖
              ≤ 1 * ((Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi)) :=
                mul_le_mul h1t hcpow (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
        have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd_t
        simpa using h
      have hgb := norm_mul_genBinom_le (-α) N
      have hby : ‖b (y : ℂ)‖ ≤ C_b * Real.exp (-c_b * y) := by simpa using hb.bound (y : ℂ) (by simpa using hy1)
      have hnorm_eq : ‖(y : ℂ) ^ j * b (y : ℂ) * rem y‖ =
          y ^ j * ‖b (y : ℂ)‖ * (‖(N : ℂ) * genBinom (-α) N‖ * (‖u‖ ^ N * y ^ N) *
            ‖∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) *
              (1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))‖) := by
        dsimp [rem]
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ y by linarith)]
        ring
      rw [hnorm_eq]
      have h1 : y ^ j * ‖b (y : ℂ)‖ ≤ y ^ j * (C_b * Real.exp (-c_b * y)) :=
        mul_le_mul_of_nonneg_left hby (by positivity)
      have h2 : ‖(N : ℂ) * genBinom (-α) N‖ * (‖u‖ ^ N * y ^ N) *
            ‖∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) *
              (1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))‖ ≤
          (2 + ‖-α‖) ^ N * (‖u‖ ^ N * y ^ N) *
            ((Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hgb (by positivity)) hint_t (norm_nonneg _) (by positivity)
      calc y ^ j * ‖b (y : ℂ)‖ *
            (‖(N : ℂ) * genBinom (-α) N‖ * (‖u‖ ^ N * y ^ N) *
              ‖∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) *
                (1 + (t : ℂ) * (u * (y : ℂ))) ^ (-α - (N : ℂ))‖)
          ≤ (y ^ j * (C_b * Real.exp (-c_b * y))) *
              ((2 + ‖-α‖) ^ N * (‖u‖ ^ N * y ^ N) *
                ((Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi))) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (C_b * (2 + ‖-α‖) ^ N * (Real.sqrt 2) ^ (α.re + (N : ℝ)) *
              Real.exp (|α.im| * Real.pi) * ‖u‖ ^ N) * (y ^ (N + j) * Real.exp (-c_b * y)) := by
            rw [pow_add]; ring
    have hint_lhs : IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ j * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-α))
        (Set.Ioi 1) := by
      have hdom2 : IntegrableOn (fun y : ℝ ↦
          (C_b * (1 + ‖u‖) ^ (max (-α.re) 0) * (Real.sqrt 2) ^ (max α.re 0) *
            Real.exp (|α.im| * Real.pi)) *
            (y ^ (j + Nat.ceil (max (-α.re) 0)) * Real.exp (-c_b * y))) (Set.Ioi 1) :=
        ((integral_pow_mul_exp_Ioi_le _ hb.c_pos).1.mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul _
      have hmeas : AEStronglyMeasurable
          (fun y : ℝ ↦ (y : ℂ) ^ j * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-α))
          (volume.restrict (Set.Ioi 1)) := by
        apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
        have hpow_c : ContinuousOn (fun y : ℝ ↦ (1 + u * (y : ℂ)) ^ (-α)) (Set.Ioi 1) := by
          intro y hy
          have hsl := one_add_mul_ofReal_mem_slitPlane hu_slit (lt_trans zero_lt_one (Set.mem_Ioi.mp hy))
          exact (continuousAt_cpow_const_comp
            (continuousAt_const.add (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)) hsl).continuousWithinAt
        exact (((Complex.continuous_ofReal.pow j).continuousOn).mul hcont_b).mul hpow_c
      refine hdom2.mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy1 : (1 : ℝ) ≤ y := (Set.mem_Ioi.mp hy).le
      have ⟨hsl, hng⟩ := sector34_one_add_norm_ge (y := y) hu zero_le_one (by linarith)
      simp only [Complex.ofReal_one, one_mul] at hsl hng
      have hcp := norm_cpow_le_rpow_mul_exp (z := 1 + u * (y : ℂ)) (w := -α) (Complex.slitPlane_ne_zero hsl)
      rw [Complex.neg_re, Complex.neg_im, abs_neg] at hcp
      have hrpow_le : ‖1 + u * (y : ℂ)‖ ^ (-α.re) ≤
          (1 + ‖u‖) ^ (max (-α.re) 0) * (Real.sqrt 2) ^ (max α.re 0) * y ^ Nat.ceil (max (-α.re) 0) := by
        by_cases hneg : -α.re ≤ 0
        · have hmax1 : max (-α.re) 0 = 0 := max_eq_right hneg
          have hmax2 : max α.re 0 = α.re := max_eq_left (by linarith)
          rw [hmax1, hmax2, Real.rpow_zero, one_mul, Nat.ceil_zero, pow_zero, mul_one]
          have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hng hneg
          rwa [one_div, Real.inv_rpow (Real.sqrt_nonneg 2), Real.rpow_neg (Real.sqrt_nonneg 2), inv_inv] at h1
        · push Not at hneg
          have hmax1 : max (-α.re) 0 = -α.re := max_eq_left hneg.le
          have hmax2 : max α.re 0 = 0 := max_eq_right (by linarith)
          rw [hmax1, hmax2, Real.rpow_zero, mul_one]
          have hup : ‖1 + u * (y : ℂ)‖ ≤ (1 + ‖u‖) * y := by
            calc ‖1 + u * (y : ℂ)‖ ≤ 1 + ‖u‖ * y := by
                  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ y by linarith)] using
                    norm_add_le (1 : ℂ) (u * (y : ℂ))
              _ ≤ 1 * y + ‖u‖ * y := by nlinarith
              _ = (1 + ‖u‖) * y := by ring
          calc ‖1 + u * (y : ℂ)‖ ^ (-α.re)
              ≤ ((1 + ‖u‖) * y) ^ (-α.re) := Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
            _ = (1 + ‖u‖) ^ (-α.re) * y ^ (-α.re) := Real.mul_rpow (by positivity) (by linarith)
            _ ≤ (1 + ‖u‖) ^ (-α.re) * y ^ (Nat.ceil (-α.re) : ℝ) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 (Nat.le_ceil _)) (by positivity)
            _ = (1 + ‖u‖) ^ (-α.re) * y ^ Nat.ceil (-α.re) := by rw [Real.rpow_natCast]
      have hby : ‖b (y : ℂ)‖ ≤ C_b * Real.exp (-c_b * y) := by simpa using hb.bound (y : ℂ) (by simpa using hy1)
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have h1 : y ^ j * ‖b (y : ℂ)‖ ≤ y ^ j * (C_b * Real.exp (-c_b * y)) :=
        mul_le_mul_of_nonneg_left hby (by positivity)
      calc y ^ j * ‖b (y : ℂ)‖ * ‖(1 + u * (y : ℂ)) ^ (-α)‖
          ≤ (y ^ j * (C_b * Real.exp (-c_b * y))) *
              (((1 + ‖u‖) ^ max (-α.re) 0 * Real.sqrt 2 ^ max α.re 0 *
                y ^ Nat.ceil (max (-α.re) 0)) * Real.exp (|α.im| * Real.pi)) :=
            mul_le_mul h1 (hcp.trans (mul_le_mul_of_nonneg_right hrpow_le (Real.exp_pos _).le))
              (norm_nonneg _) (by positivity)
        _ = C_b * (1 + ‖u‖) ^ max (-α.re) 0 * Real.sqrt 2 ^ max α.re 0 *
              Real.exp (|α.im| * Real.pi) * (y ^ (j + Nat.ceil (max (-α.re) 0)) * Real.exp (-c_b * y)) := by
            rw [pow_add]; ring
    have hdiff_int : (pref * ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ j * b (y : ℂ) * (1 + u * (y : ℂ)) ^ (-α)) -
        ∑ n ∈ Finset.range N, phiFormalCoeff k b j n * u ^ n =
        pref * ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ j * b (y : ℂ) * rem y := by
      have hsum_int : ∑ n ∈ Finset.range N, phiFormalCoeff k b j n * u ^ n =
          pref * ∫ y in Set.Ioi (1 : ℝ),
            ∑ n ∈ Finset.range N, genBinom (-α) n * u ^ n * ((y : ℂ) ^ (n + j) * b (y : ℂ)) := by
        rw [integral_finsetSum _ (fun n _ ↦ (hint_mom (n + j)).const_mul _), Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [integral_const_mul]; dsimp [phiFormalCoeff, pref, α]; ring
      rw [hsum_int, ← mul_sub, ← integral_sub hint_lhs
        (integrable_finsetSum _ (fun n _ ↦ (hint_mom (n + j)).const_mul _))]
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioi hrem_pt
    have hα_eq : -(k + (j : ℂ)) = -α := rfl
    rw [show (-1 : ℂ) ^ j * risingFac k j = pref from rfl, hα_eq, hdiff_int, norm_mul]
    have hmom_bound' : ∫ y in Set.Ioi (1 : ℝ), y ^ (N + j) * Real.exp (-c_b * y) ≤
        ((N + j).factorial : ℝ) / c_b ^ (N + j + 1) := by
      have ⟨hint0, hval0⟩ := integral_pow_mul_exp_Ioi_le (N + j) hb.c_pos
      rw [← hval0]
      refine setIntegral_mono_set hint0 ?_ (Eventually.of_forall (Set.Ioi_subset_Ioi zero_le_one))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (pow_nonneg (Set.mem_Ioi.mp hy).le _) (Real.exp_pos _).le
    have hnorm_rem_int : ‖∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ j * b (y : ℂ) * rem y‖ ≤
        (C_b * (2 + ‖-α‖) ^ N * (Real.sqrt 2) ^ (α.re + (N : ℝ)) *
          Real.exp (|α.im| * Real.pi) * ‖u‖ ^ N) * (((N + j).factorial : ℝ) / c_b ^ (N + j + 1)) := by
      have hdom_int : IntegrableOn (fun y : ℝ ↦
          (C_b * (2 + ‖-α‖) ^ N * (Real.sqrt 2) ^ (α.re + (N : ℝ)) *
            Real.exp (|α.im| * Real.pi) * ‖u‖ ^ N) * (y ^ (N + j) * Real.exp (-c_b * y))) (Set.Ioi 1) :=
        ((integral_pow_mul_exp_Ioi_le (N + j) hb.c_pos).1.mono_set
          (Set.Ioi_subset_Ioi zero_le_one)).const_mul _
      have h1 := (norm_integral_le_integral_norm _).trans
        (setIntegral_mono_on (hint_lhs.sub (integrable_finsetSum _ (fun n _ ↦ (hint_mom (n + j)).const_mul _)) |>.congr_fun
            hrem_pt measurableSet_Ioi).norm hdom_int measurableSet_Ioi hrem_bd)
      rw [integral_const_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hmom_bound' (by positivity))
    have hfac_split : ((N + j).factorial : ℝ) ≤ (2 : ℝ) ^ (N + j) * (N.factorial : ℝ) * (j.factorial : ℝ) := by
      have hch : Nat.choose (N + j) N ≤ 2 ^ (N + j) := by
        have := Nat.sum_range_choose (N + j)
        have hmem : N ∈ Finset.range (N + j + 1) := Finset.mem_range.mpr (by omega)
        calc Nat.choose (N + j) N
            ≤ ∑ i ∈ Finset.range (N + j + 1), Nat.choose (N + j) i :=
              Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hmem
          _ = 2 ^ (N + j) := this
      have hmul := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right N j)
      rw [Nat.add_sub_cancel_left] at hmul
      have hnat : (N + j).factorial ≤ 2 ^ (N + j) * N.factorial * j.factorial := by
        calc (N + j).factorial = Nat.choose (N + j) N * N.factorial * j.factorial := hmul.symm
          _ ≤ 2 ^ (N + j) * N.factorial * j.factorial := by gcongr
      exact_mod_cast hnat
    have hsqrt_add : (Real.sqrt 2) ^ (α.re + (N : ℝ)) = (Real.sqrt 2) ^ α.re * (Real.sqrt 2) ^ N := by
      rw [Real.rpow_add (Real.sqrt_pos.mpr zero_lt_two), Real.rpow_natCast]
    calc ‖pref‖ * ‖∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ j * b (y : ℂ) * rem y‖
        ≤ ‖pref‖ * ((C_b * (2 + ‖-α‖) ^ N * (Real.sqrt 2) ^ (α.re + (N : ℝ)) *
            Real.exp (|α.im| * Real.pi) * ‖u‖ ^ N) * (((N + j).factorial : ℝ) / c_b ^ (N + j + 1))) :=
          mul_le_mul_of_nonneg_left hnorm_rem_int (norm_nonneg _)
      _ ≤ ‖pref‖ * ((C_b * (2 + ‖-α‖) ^ N * (Real.sqrt 2) ^ (α.re + (N : ℝ)) *
            Real.exp (|α.im| * Real.pi) * ‖u‖ ^ N) *
              (((2 : ℝ) ^ (N + j) * (N.factorial : ℝ) * (j.factorial : ℝ)) / c_b ^ (N + j + 1))) := by
          gcongr
      _ = C₁ * B₁ ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by
          dsimp [C₁, B₁]
          rw [hsqrt_add, mul_pow, mul_pow, div_pow, pow_add,
              show N + j + 1 = N + (j + 1) by omega, pow_add]
          field_simp [hb.c_pos.ne']
  let tailConst : ℕ → ℝ := fun N ↦
    C₁ * B₁ ^ N₀ * (N₀.factorial : ℝ) * u₀ ^ (N₀ - N) +
      ∑ n ∈ Finset.Ico N N₀, ‖phiFormalCoeff k b j n‖ * u₀ ^ (n - N)
  let C_fin : ℝ := max C₁ ((Finset.range N₀).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun N ↦ tailConst N / (B₁ ^ N * (N.factorial : ℝ))))
  refine ⟨C_fin, B₁, le_trans hC₁_nn (le_max_left _ _), hB₁_pos, fun N u hu ↦ ?_⟩
  by_cases hN : N₀ ≤ N
  · exact (hbig N hN u hu).trans (by
      have hC_le : C₁ ≤ C_fin := le_max_left _ _
      gcongr)
  · push Not at hN
    have hsplit : iteratedDeriv j (PhiReal k b) u - ∑ n ∈ Finset.range N, phiFormalCoeff k b j n * u ^ n =
        (iteratedDeriv j (PhiReal k b) u - ∑ n ∈ Finset.range N₀, phiFormalCoeff k b j n * u ^ n) +
          ∑ n ∈ Finset.Ico N N₀, phiFormalCoeff k b j n * u ^ n := by
      have := Finset.sum_range_add_sum_Ico (fun n ↦ phiFormalCoeff k b j n * u ^ n) hN.le
      linear_combination -this
    rw [hsplit]
    have hbd_N0 := hbig N₀ le_rfl u hu
    have h1 : ‖iteratedDeriv j (PhiReal k b) u - ∑ n ∈ Finset.range N₀, phiFormalCoeff k b j n * u ^ n‖ ≤
        C₁ * B₁ ^ N₀ * (N₀.factorial : ℝ) * u₀ ^ (N₀ - N) * ‖u‖ ^ N := by
      calc _ ≤ C₁ * B₁ ^ N₀ * (N₀.factorial : ℝ) * ‖u‖ ^ N₀ := hbd_N0
        _ = C₁ * B₁ ^ N₀ * (N₀.factorial : ℝ) * (‖u‖ ^ (N₀ - N) * ‖u‖ ^ N) := by
            rw [← pow_add, Nat.sub_add_cancel hN.le]
        _ ≤ C₁ * B₁ ^ N₀ * (N₀.factorial : ℝ) * (u₀ ^ (N₀ - N) * ‖u‖ ^ N) := by
            have hu_pow : ‖u‖ ^ (N₀ - N) ≤ u₀ ^ (N₀ - N) := pow_le_pow_left₀ (norm_nonneg u) hu.2.1 _
            gcongr
        _ = _ := by ring
    have h2 : ‖∑ n ∈ Finset.Ico N N₀, phiFormalCoeff k b j n * u ^ n‖ ≤
        (∑ n ∈ Finset.Ico N N₀, ‖phiFormalCoeff k b j n‖ * u₀ ^ (n - N)) * ‖u‖ ^ N := by
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
      have hNn : N ≤ n := (Finset.mem_Ico.mp hn).1
      rw [norm_mul, norm_pow]
      have hu_pow : ‖u‖ ^ (n - N) ≤ u₀ ^ (n - N) := pow_le_pow_left₀ (norm_nonneg u) hu.2.1 _
      calc ‖phiFormalCoeff k b j n‖ * ‖u‖ ^ n
          = ‖phiFormalCoeff k b j n‖ * (‖u‖ ^ (n - N) * ‖u‖ ^ N) := by
            rw [← pow_add, Nat.sub_add_cancel hNn]
        _ ≤ ‖phiFormalCoeff k b j n‖ * (u₀ ^ (n - N) * ‖u‖ ^ N) := by gcongr
        _ = ‖phiFormalCoeff k b j n‖ * u₀ ^ (n - N) * ‖u‖ ^ N := by ring
    have hC_ge : tailConst N / (B₁ ^ N * (N.factorial : ℝ)) ≤ C_fin :=
      (Finset.le_sup' (f := fun N ↦ tailConst N / (B₁ ^ N * (N.factorial : ℝ)))
        (Finset.mem_range.mpr hN)).trans (le_max_right _ _)
    have hden_pos : 0 < B₁ ^ N * (N.factorial : ℝ) :=
      mul_pos (pow_pos hB₁_pos N) (by exact_mod_cast Nat.factorial_pos N)
    have htail_le : tailConst N ≤ C_fin * B₁ ^ N * (N.factorial : ℝ) := by
      have := (div_le_iff₀ hden_pos).mp hC_ge; linarith
    calc ‖(iteratedDeriv j (PhiReal k b) u - ∑ n ∈ Finset.range N₀, phiFormalCoeff k b j n * u ^ n) +
            ∑ n ∈ Finset.Ico N N₀, phiFormalCoeff k b j n * u ^ n‖
        ≤ ‖iteratedDeriv j (PhiReal k b) u - ∑ n ∈ Finset.range N₀, phiFormalCoeff k b j n * u ^ n‖ +
            ‖∑ n ∈ Finset.Ico N N₀, phiFormalCoeff k b j n * u ^ n‖ := norm_add_le _ _
      _ ≤ tailConst N * ‖u‖ ^ N := by dsimp [tailConst]; linarith
      _ ≤ (C_fin * B₁ ^ N * (N.factorial : ℝ)) * ‖u‖ ^ N :=
          mul_le_mul_of_nonneg_right htail_le (pow_nonneg (norm_nonneg u) N)
      _ = C_fin * B₁ ^ N * (N.factorial : ℝ) * ‖u‖ ^ N := by ring

/-! ### 3. Lemma 5.1(a), (c), (d): Rotated Rays `gammaMinus`/`gammaPlus` & Open Sectors `UPlus`/`UMinus` -/

/-- Lower-half-plane rotated ray `γ₋(r) = 1 + r e^{-i π / 4}` (`r ≥ 0`). -/
def gammaMinus (r : ℝ) : ℂ :=
  1 + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)

/-- Upper-half-plane rotated ray `γ₊(r) = 1 + r e^{+i π / 4}` (`r ≥ 0`). -/
def gammaPlus (r : ℝ) : ℂ :=
  1 + (r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)

/-- Upper analytic-continuation sector `U₊(x₀) = {0 < ‖u‖ < x₀, -π/8 < arg u < 9π/8}`,
characterized algebraically as `-sin(π/8) ‖u‖ < u.im`. -/
def UPlus (x₀ : ℝ) : Set ℂ :=
  {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ < x₀ ∧ -Real.sin (Real.pi / 8) * ‖u‖ < u.im}

/-- Lower analytic-continuation sector `U₋(x₀) = {0 < ‖u‖ < x₀, -9π/8 < arg u < π/8}`,
characterized algebraically as `u.im < sin(π/8) ‖u‖`. -/
def UMinus (x₀ : ℝ) : Set ℂ :=
  {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ < x₀ ∧ u.im < Real.sin (Real.pi / 8) * ‖u‖}

theorem exp_neg_I_pi_div_four_re :
    (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)).re = 1 / Real.sqrt 2 := by
  have heq : -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq, Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp [(Real.sqrt_pos.mpr zero_lt_two).ne']; linarith

theorem exp_neg_I_pi_div_four_im :
    (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)).im = -(1 / Real.sqrt 2) := by
  have heq : -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq, Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.sin_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp [(Real.sqrt_pos.mpr zero_lt_two).ne']; linarith

theorem exp_I_pi_div_four_re :
    (Complex.exp (Complex.I * (Real.pi : ℂ) / 4)).re = 1 / Real.sqrt 2 := by
  have heq : Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp [(Real.sqrt_pos.mpr zero_lt_two).ne']; linarith

theorem exp_I_pi_div_four_im :
    (Complex.exp (Complex.I * (Real.pi : ℂ) / 4)).im = 1 / Real.sqrt 2 := by
  have heq : Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp [(Real.sqrt_pos.mpr zero_lt_two).ne']; linarith

theorem gammaMinus_re (r : ℝ) : (gammaMinus r).re = 1 + r / Real.sqrt 2 := by
  simp only [gammaMinus, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, exp_neg_I_pi_div_four_re]
  ring

theorem gammaMinus_im (r : ℝ) : (gammaMinus r).im = -(r / Real.sqrt 2) := by
  simp only [gammaMinus, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_add, exp_neg_I_pi_div_four_im]
  ring

theorem gammaPlus_re (r : ℝ) : (gammaPlus r).re = 1 + r / Real.sqrt 2 := by
  simp only [gammaPlus, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, exp_I_pi_div_four_re]
  ring

theorem gammaPlus_im (r : ℝ) : (gammaPlus r).im = r / Real.sqrt 2 := by
  simp only [gammaPlus, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_add, exp_I_pi_div_four_im]
  ring

theorem star_gammaMinus (r : ℝ) : starRingEnd ℂ (gammaMinus r) = gammaPlus r := by
  apply Complex.ext
  · simp [gammaMinus_re, gammaPlus_re]
  · simp [gammaMinus_im, gammaPlus_im]

theorem star_gammaPlus (r : ℝ) : starRingEnd ℂ (gammaPlus r) = gammaMinus r := by
  rw [← star_gammaMinus, RingHomCompTriple.comp_apply]
  simp

theorem isOpen_UPlus (x₀ : ℝ) : IsOpen (UPlus x₀) :=
  (isOpen_lt continuous_const continuous_norm).inter
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt (continuous_const.mul continuous_norm) Complex.continuous_im))

theorem isOpen_UMinus (x₀ : ℝ) : IsOpen (UMinus x₀) :=
  (isOpen_lt continuous_const continuous_norm).inter
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt Complex.continuous_im (continuous_const.mul continuous_norm)))

theorem mem_UMinus_iff_star {x₀ : ℝ} {u : ℂ} :
    u ∈ UMinus x₀ ↔ starRingEnd ℂ u ∈ UPlus x₀ := by
  simp only [UMinus, UPlus, Set.mem_ofPred_eq, RCLike.norm_conj, Complex.conj_im]
  constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩)

theorem ofReal_mem_UPlus {x₀ x : ℝ} (hx0 : 0 < x) (hx1 : x < x₀) : (x : ℂ) ∈ UPlus x₀ := by
  have hsin : 0 < Real.sin (Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx0
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Complex.ofReal_im]; nlinarith

theorem neg_ofReal_mem_UPlus {x₀ x : ℝ} (hx0 : 0 < x) (hx1 : x < x₀) : (-(x : ℂ)) ∈ UPlus x₀ := by
  have hsin : 0 < Real.sin (Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx0
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Complex.neg_im,
      Complex.ofReal_im, neg_zero]; nlinarith

theorem ofReal_mem_UMinus {x₀ x : ℝ} (hx0 : 0 < x) (hx1 : x < x₀) : (x : ℂ) ∈ UMinus x₀ := by
  rw [mem_UMinus_iff_star]; simpa using ofReal_mem_UPlus hx0 hx1

theorem neg_ofReal_mem_UMinus {x₀ x : ℝ} (hx0 : 0 < x) (hx1 : x < x₀) : (-(x : ℂ)) ∈ UMinus x₀ := by
  rw [mem_UMinus_iff_star]; simpa using neg_ofReal_mem_UPlus hx0 hx1

/-- Exact polar characterization of `UPlus x₀` matching `main.tex:817`:
`UPlus x₀ = {ρ e^{iθ} : 0 < ρ < x₀, -π/8 < θ < 9π/8}`. -/
theorem UPlus_eq_polar_image (x₀ : ℝ) :
    (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
      (Set.Ioo 0 x₀ ×ˢ Set.Ioo (-(Real.pi / 8)) (9 * Real.pi / 8)) = UPlus x₀ := by
  ext u
  constructor
  · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ0, hρ1⟩, ⟨hθ1, hθ2⟩⟩, rfl⟩
    have hnorm : ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0,
          Complex.norm_exp_ofReal_mul_I, mul_one]
    have him : ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = ρ * Real.sin θ := by
      simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]
    refine ⟨hnorm.symm ▸ hρ0, hnorm.symm ▸ hρ1, ?_⟩
    rw [hnorm, him]
    have hsin_gt : -Real.sin (Real.pi / 8) < Real.sin θ := by
      rw [← Real.sin_neg]
      by_cases hle : θ ≤ Real.pi / 2
      · exact Real.strictMonoOn_sin
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          ⟨by linarith [Real.pi_pos], hle⟩ hθ1
      · push Not at hle
        rw [← Real.sin_pi_sub θ]
        exact Real.strictMonoOn_sin
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith)
    nlinarith
  · intro ⟨h0, h1, him⟩
    have hu0 : u ≠ 0 := norm_pos_iff.mp h0
    have hsin_gt : -Real.sin (Real.pi / 8) < Real.sin u.arg := by
      rw [Complex.sin_arg, lt_div_iff₀ h0]; linarith
    by_cases harg : -(Real.pi / 8) < u.arg
    · refine ⟨(‖u‖, u.arg), ⟨⟨h0, h1⟩, ⟨harg, lt_of_le_of_lt (Complex.arg_le_pi u)
        (by linarith [Real.pi_pos])⟩⟩, Complex.norm_mul_exp_arg_mul_I u⟩
    · push Not at harg
      have harg_lt : u.arg < -(7 * Real.pi / 8) := by
        by_contra hge; push Not at hge
        have hsin_le : Real.sin u.arg ≤ -Real.sin (Real.pi / 8) := by
          rw [← Real.sin_neg]
          by_cases hmid : -(Real.pi / 2) ≤ u.arg
          · exact Real.strictMonoOn_sin.monotoneOn
              ⟨hmid, by linarith [Real.pi_pos]⟩
              ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ harg
          · push Not at hmid
            rw [show Real.sin u.arg = Real.sin (-Real.pi - u.arg) by
              rw [show -Real.pi - u.arg = -(u.arg + Real.pi) by ring, Real.sin_neg, Real.sin_add_pi, neg_neg]]
            exact Real.strictMonoOn_sin.monotoneOn
              ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
              ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith)
        linarith
      refine ⟨(‖u‖, u.arg + 2 * Real.pi), ⟨⟨h0, h1⟩, ⟨by linarith [Complex.neg_pi_lt_arg u, Real.pi_pos],
        by linarith⟩⟩, ?_⟩
      have hexp : Complex.exp (((u.arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((u.arg : ℂ) * Complex.I) := by
        push_cast
        rw [add_mul, Complex.exp_add]
        have h2pi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 2 * Real.pi * Complex.I := rfl
        rw [Complex.exp_two_pi_mul_I, mul_one]
      dsimp only
      rw [hexp]
      exact Complex.norm_mul_exp_arg_mul_I u

theorem isPreconnected_UPlus (x₀ : ℝ) : IsPreconnected (UPlus x₀) := by
  rw [← UPlus_eq_polar_image x₀]
  have hcont : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ hcont.continuousOn

theorem isPreconnected_UMinus (x₀ : ℝ) : IsPreconnected (UMinus x₀) := by
  have himg : (starRingEnd ℂ) '' UPlus x₀ = UMinus x₀ := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_UMinus_iff_star]; simpa using hw
    · intro hu
      exact ⟨starRingEnd ℂ u, mem_UMinus_iff_star.mp hu, by simp⟩
  rw [← himg]
  exact (isPreconnected_UPlus x₀).image _ Complex.continuous_conj.continuousOn

/-- **Lemma 5.1(a) Slit-Plane Guarantee on `U₊ × γ₋`**:
For every `0 < x₀ ≤ 1/4`, every `u ∈ UPlus x₀`, and every `r ≥ 0`,
`1 + u * gammaMinus r ∈ Complex.slitPlane` (verifying all 4 cases from `main.tex:849–854`!). -/
theorem one_add_mul_mem_slitPlane_UPlus {x₀ : ℝ} (hx₀ : x₀ ≤ 1 / 4)
    {u : ℂ} (hu : u ∈ UPlus x₀) {r : ℝ} (hr : 0 ≤ r) :
    1 + u * gammaMinus r ∈ Complex.slitPlane := by
  rw [← UPlus_eq_polar_image x₀] at hu
  obtain ⟨⟨ρ, θ⟩, ⟨⟨hρ0, hρ1⟩, ⟨hθ1, hθ2⟩⟩, rfl⟩ := hu
  rw [Complex.mem_slitPlane_iff]
  have hprod : (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * gammaMinus r =
      (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) +
        ((ρ * r : ℝ) : ℂ) * Complex.exp (((θ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    unfold gammaMinus
    have hexp : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) =
        Complex.exp (((θ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) *
          (1 + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
        = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) +
            (ρ : ℂ) * (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) *
              Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)) := by ring
      _ = _ := by rw [hexp]; push_cast; ring
  have hre : (1 + (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * gammaMinus r).re =
      1 + ρ * Real.cos θ + ρ * r * Real.cos (θ - Real.pi / 4) := by
    rw [hprod, Complex.add_re, Complex.one_re, Complex.add_re, Complex.mul_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re]
    ring
  have him : (1 + (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * gammaMinus r).im =
      ρ * Real.sin θ + ρ * r * Real.sin (θ - Real.pi / 4) := by
    rw [hprod, Complex.add_im, Complex.one_im, Complex.add_im, Complex.mul_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im]
    ring
  have hρ_lt : ρ < 1 / 4 := lt_of_lt_of_le hρ1 hx₀
  by_cases hr1 : r ≤ 1
  · left
    have hcos1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    have hcos2 : -1 ≤ Real.cos (θ - Real.pi / 4) := Real.neg_one_le_cos _
    have h1 : -ρ ≤ ρ * Real.cos θ := by nlinarith
    have h2 : -(ρ * r) ≤ ρ * r * Real.cos (θ - Real.pi / 4) := by nlinarith [mul_nonneg hρ0.le hr]
    rw [hre]; nlinarith
  · push Not at hr1
    by_cases hθ_le1 : θ ≤ Real.pi / 4
    · left
      have hc1 : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have hc2 : 0 < Real.cos (θ - Real.pi / 4) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have h1 : 0 < ρ * Real.cos θ := mul_pos hρ0 hc1
      have h2 : 0 < ρ * r * Real.cos (θ - Real.pi / 4) := mul_pos (mul_pos hρ0 (by linarith)) hc2
      rw [hre]; linarith
    · push Not at hθ_le1
      by_cases hθ_le2 : θ ≤ Real.pi
      · right
        have hs1 : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) hθ_le2
        have hs2 : 0 < Real.sin (θ - Real.pi / 4) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        have h1 : 0 ≤ ρ * Real.sin θ := mul_nonneg hρ0.le hs1
        have h2 : 0 < ρ * r * Real.sin (θ - Real.pi / 4) := mul_pos (mul_pos hρ0 (by linarith)) hs2
        rw [him]; exact ne_of_gt (by linarith)
      · push Not at hθ_le2
        right
        set δ : ℝ := θ - Real.pi
        have hδ0 : 0 < δ := by dsimp [δ]; linarith
        have hδ1 : δ < Real.pi / 8 := by dsimp [δ]; linarith
        have hs1 : Real.sin θ = -Real.sin δ := by
          rw [show θ = δ + Real.pi by dsimp [δ]; ring, Real.sin_add_pi]
        have hs2 : Real.sin (θ - Real.pi / 4) = Real.cos (Real.pi / 4 + δ) := by
          rw [show θ - Real.pi / 4 = (Real.pi / 4 + δ) + Real.pi / 2 by dsimp [δ]; ring,
              Real.sin_add_pi_div_two]
        have hcos_gt : Real.sin (Real.pi / 8) < Real.cos (Real.pi / 4 + δ) := by
          rw [show Real.sin (Real.pi / 8) = Real.cos (3 * Real.pi / 8) by
            rw [← Real.sin_pi_div_two_sub]; congr 1; ring]
          exact Real.strictAntiOn_cos
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith)
        have hsin_lt : Real.sin δ < Real.sin (Real.pi / 8) :=
          Real.strictMonoOn_sin
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hδ1
        have hsin_pos : 0 < Real.sin (Real.pi / 8) :=
          Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
        have hcomb : 0 < -Real.sin δ + r * Real.cos (Real.pi / 4 + δ) := by
          have hr_gt : Real.sin (Real.pi / 8) < r * Real.cos (Real.pi / 4 + δ) := by nlinarith
          linarith
        rw [him, hs1, hs2]
        have hfac : ρ * -Real.sin δ + ρ * r * Real.cos (Real.pi / 4 + δ) =
            ρ * (-Real.sin δ + r * Real.cos (Real.pi / 4 + δ)) := by ring
        rw [hfac]; exact ne_of_gt (mul_pos hρ0 hcomb)

/-- **Lemma 5.1(a) Slit-Plane Guarantee on `U₋ × γ₊`** (by complex conjugation). -/
theorem one_add_mul_mem_slitPlane_UMinus {x₀ : ℝ} (hx₀ : x₀ ≤ 1 / 4)
    {u : ℂ} (hu : u ∈ UMinus x₀) {r : ℝ} (hr : 0 ≤ r) :
    1 + u * gammaPlus r ∈ Complex.slitPlane := by
  have hconj := one_add_mul_mem_slitPlane_UPlus hx₀ (mem_UMinus_iff_star.mp hu) hr
  have heq : starRingEnd ℂ (1 + u * gammaPlus r) = 1 + starRingEnd ℂ u * gammaMinus r := by
    rw [map_add, map_one, map_mul, star_gammaPlus]
  rw [← heq] at hconj
  rw [Complex.mem_slitPlane_iff] at hconj ⊢
  rcases hconj with h | h
  · left; simpa using h
  · right; intro h0; apply h; rw [Complex.conj_im, h0, neg_zero]

/-- **Lemma 5.1(c) Exact Uniform Lower Bound on `γ₋`**:
For all `t ∈ [0, 1]`, `x ∈ [0, 1/2]`, and `r ≥ 0`:
`‖1 - t x γ₋(r)‖ ≥ (1 - t x) / √2 ≥ 1 / (2 √2)` and `1 - t x γ₋(r) ∈ Complex.slitPlane`. -/
theorem one_sub_txy_norm_ge_gammaMinus {t x r : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (_hr : 0 ≤ r) :
    1 / (2 * Real.sqrt 2) ≤ (1 - t * x) / Real.sqrt 2 ∧
      (1 - t * x) / Real.sqrt 2 ≤ ‖1 - (t : ℂ) * (x : ℂ) * gammaMinus r‖ ∧
      1 - (t : ℂ) * (x : ℂ) * gammaMinus r ∈ Complex.slitPlane := by
  set A : ℝ := 1 - t * x
  set s : ℝ := t * x * r / Real.sqrt 2
  have hA_ge : 1 / 2 ≤ A := by dsimp [A]; nlinarith
  have hA_pos : 0 < A := by linarith
  have hre : (1 - (t : ℂ) * (x : ℂ) * gammaMinus r).re = A - s := by
    have hmul : (t : ℂ) * (x : ℂ) * gammaMinus r = ((t * x : ℝ) : ℂ) * gammaMinus r := by push_cast; rfl
    rw [hmul, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, gammaMinus_re]
    dsimp [A, s]; ring
  have him : (1 - (t : ℂ) * (x : ℂ) * gammaMinus r).im = s := by
    have hmul : (t : ℂ) * (x : ℂ) * gammaMinus r = ((t * x : ℝ) : ℂ) * gammaMinus r := by push_cast; rfl
    rw [hmul, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, gammaMinus_im]
    dsimp [s]; ring
  have hsq : (A / Real.sqrt 2) ^ 2 ≤ ‖1 - (t : ℂ) * (x : ℂ) * gammaMinus r‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him, div_pow, Real.sq_sqrt (by norm_num)]
    have hident : (A - s) * (A - s) + s * s = 2 * (s - A / 2) ^ 2 + A ^ 2 / 2 := by ring
    rw [hident]; linarith [sq_nonneg (s - A / 2)]
  have hnorm_ge : A / Real.sqrt 2 ≤ ‖1 - (t : ℂ) * (x : ℂ) * gammaMinus r‖ := by
    nlinarith [norm_nonneg (1 - (t : ℂ) * (x : ℂ) * gammaMinus r),
      show 0 ≤ A / Real.sqrt 2 by positivity]
  have hfirst : 1 / (2 * Real.sqrt 2) ≤ A / Real.sqrt 2 := by
    rw [show 1 / (2 * Real.sqrt 2) = (1 / 2) / Real.sqrt 2 by ring]
    exact div_le_div_of_nonneg_right hA_ge (Real.sqrt_nonneg 2)
  refine ⟨hfirst, hnorm_ge, ?_⟩
  rw [Complex.mem_slitPlane_iff]
  by_cases hs : s = 0
  · left; rw [hre, hs, sub_zero]; exact hA_pos
  · right; rw [him]; exact hs

/-- **Lemma 5.1(c) Exact Uniform Lower Bound on `γ₊`** (by complex conjugation). -/
theorem one_sub_txy_norm_ge_gammaPlus {t x r : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hr : 0 ≤ r) :
    1 / (2 * Real.sqrt 2) ≤ (1 - t * x) / Real.sqrt 2 ∧
      (1 - t * x) / Real.sqrt 2 ≤ ‖1 - (t : ℂ) * (x : ℂ) * gammaPlus r‖ ∧
      1 - (t : ℂ) * (x : ℂ) * gammaPlus r ∈ Complex.slitPlane := by
  have h := one_sub_txy_norm_ge_gammaMinus ht0 ht1 hx0 hx1 hr
  have heq : starRingEnd ℂ (1 - (t : ℂ) * (x : ℂ) * gammaMinus r) =
      1 - (t : ℂ) * (x : ℂ) * gammaPlus r := by
    rw [map_sub, map_one, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, star_gammaMinus]
  refine ⟨h.1, ?_, ?_⟩
  · rw [← heq, RCLike.norm_conj]; exact h.2.1
  · rw [← heq, Complex.mem_slitPlane_iff]
    simpa [Complex.mem_slitPlane_iff] using h.2.2

/-- **Universal Ray-Rotation Invariance Lemma**:
If `F` is holomorphic on an open set `Ω` containing the sector `{1 + r e^{iθ} : r ≥ 0, θ ∈ (a₀, b₀)}`
with `a₀ < a ≤ b < b₀` and `‖F‖ + ‖deriv F‖` decays like `C (1 + r)^M exp(-c r)` (`c > 0`),
then `e^{iθ} ∫_0^∞ F(1 + r e^{iθ}) dr` is **independent of `θ ∈ [a, b]`**! -/
theorem ray_integral_const_on_Icc {F : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hF_holo : DifferentiableOn ℂ F Ω) {a₀ a b b₀ : ℝ}
    (ha₀ : a₀ < a) (hab : a ≤ b) (hb₀ : b < b₀)
    (hsub : ∀ θ ∈ Set.Ioo a₀ b₀, ∀ r : ℝ, 0 ≤ r →
      1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Ω)
    {C c : ℝ} {M : ℕ} (_hC : 0 ≤ C) (hc : 0 < c)
    (hbdF : ∀ θ ∈ Set.Ioo a₀ b₀, ∀ r : ℝ, 0 ≤ r →
      ‖F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ C * (1 + r) ^ M * Real.exp (-c * r))
    (hbdF' : ∀ θ ∈ Set.Ioo a₀ b₀, ∀ r : ℝ, 0 ≤ r →
      ‖deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ C * (1 + r) ^ M * Real.exp (-c * r)) :
    Complex.exp ((a : ℂ) * Complex.I) *
        ∫ r in Set.Ioi (0 : ℝ), F (1 + (r : ℂ) * Complex.exp ((a : ℂ) * Complex.I)) =
      Complex.exp ((b : ℂ) * Complex.I) *
        ∫ r in Set.Ioi (0 : ℝ), F (1 + (r : ℂ) * Complex.exp ((b : ℂ) * Complex.I)) := by
  let I : ℝ → ℂ := fun θ ↦
    ∫ r in Set.Ioi (0 : ℝ), Complex.exp ((θ : ℂ) * Complex.I) * F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  have hdom_int : ∀ d : ℕ, IntegrableOn (fun r : ℝ ↦ (1 + r) ^ d * Real.exp (-c * r)) (Set.Ioi 0) := fun d ↦ by
    have hbin : ∀ r : ℝ, (1 + r) ^ d * Real.exp (-c * r) =
        ∑ k ∈ Finset.range (d + 1), (Nat.choose d k : ℝ) * (r ^ k * Real.exp (-c * r)) := by
      intro r
      rw [add_comm, add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _; simp; ring
    have hint_sum : IntegrableOn
        (fun r : ℝ ↦ ∑ k ∈ Finset.range (d + 1), (Nat.choose d k : ℝ) * (r ^ k * Real.exp (-c * r))) (Set.Ioi 0) :=
      integrable_finsetSum _ fun k _ ↦ (integral_pow_mul_exp_Ioi_le k hc).1.const_mul _
    exact hint_sum.congr_fun (fun r _ ↦ (hbin r).symm) measurableSet_Ioi
  have hderiv_zero : ∀ θ ∈ Set.Ioo a₀ b₀, HasDerivAt I 0 θ := by
    intro θ₀ hθ₀
    let G : ℝ → ℝ → ℂ := fun θ r ↦
      Complex.exp ((θ : ℂ) * Complex.I) * F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    let G' : ℝ → ℝ → ℂ := fun θ r ↦
      Complex.I * (Complex.exp ((θ : ℂ) * Complex.I) * F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) +
        (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) *
          deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
    have hcont_F : ∀ θ ∈ Set.Ioo a₀ b₀,
        ContinuousOn (fun r : ℝ ↦ F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (Set.Ici 0) := by
      intro θ hθ r hr
      have hm := hsub θ hθ r hr
      have harg_c : ContinuousAt (fun t : ℝ ↦ 1 + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) r :=
        continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
      exact (ContinuousAt.comp (f := fun t : ℝ ↦ 1 + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        ((hF_holo _ hm).differentiableAt (hΩ.mem_nhds hm)).continuousAt harg_c).continuousWithinAt
    have hcont_F' : ∀ θ ∈ Set.Ioo a₀ b₀,
        ContinuousOn (fun r : ℝ ↦ deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (Set.Ici 0) := by
      intro θ hθ r hr
      have hm := hsub θ hθ r hr
      have hdiff' : DifferentiableOn ℂ (deriv F) Ω := hF_holo.deriv hΩ
      have harg_c : ContinuousAt (fun t : ℝ ↦ 1 + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) r :=
        continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
      exact (ContinuousAt.comp (f := fun t : ℝ ↦ 1 + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        ((hdiff' _ hm).differentiableAt (hΩ.mem_nhds hm)).continuousAt harg_c).continuousWithinAt
    have hmeas_G : ∀ θ ∈ Set.Ioo a₀ b₀, AEStronglyMeasurable (G θ) (volume.restrict (Set.Ioi 0)) := by
      intro θ hθ
      exact (continuousOn_const.mul ((hcont_F θ hθ).mono Set.Ioi_subset_Ici_self)).aestronglyMeasurable
        measurableSet_Ioi
    have hmeas_G' : AEStronglyMeasurable (G' θ₀) (volume.restrict (Set.Ioi 0)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      exact continuousOn_const.mul
        ((continuousOn_const.mul ((hcont_F θ₀ hθ₀).mono Set.Ioi_subset_Ici_self)).add
          (((Complex.continuous_ofReal.continuousOn.mul continuousOn_const).mul continuousOn_const).mul
            ((hcont_F' θ₀ hθ₀).mono Set.Ioi_subset_Ici_self)))
    have hG_int : Integrable (G θ₀) (volume.restrict (Set.Ioi 0)) := by
      refine ((hdom_int M).const_mul C).mono' (hmeas_G θ₀ hθ₀) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      dsimp [G]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      simpa [mul_assoc] using hbdF θ₀ hθ₀ r (Set.mem_Ioi.mp hr).le
    let bound : ℝ → ℝ := fun r ↦ C * ((1 + r) ^ (M + 1) * Real.exp (-c * r))
    have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) := (hdom_int (M + 1)).const_mul C
    have hbound_ae : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), ∀ θ ∈ Set.Ioo a₀ b₀, ‖G' θ r‖ ≤ bound r := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr θ hθ
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      dsimp [G', bound]
      rw [norm_mul, Complex.norm_I, one_mul]
      have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I) * F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
          C * (1 + r) ^ M * Real.exp (-c * r) := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact hbdF θ hθ r hr0
      have h2 : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) *
            deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
          r * (C * (1 + r) ^ M * Real.exp (-c * r)) := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
            Complex.norm_exp_ofReal_mul_I, mul_one, mul_one]
        exact mul_le_mul_of_nonneg_left (hbdF' θ hθ r hr0) hr0
      calc ‖Complex.exp ((θ : ℂ) * Complex.I) * F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) +
              (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) *
                deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
          ≤ _ := norm_add_le _ _
        _ ≤ C * (1 + r) ^ M * Real.exp (-c * r) + r * (C * (1 + r) ^ M * Real.exp (-c * r)) :=
            add_le_add h1 h2
        _ = C * ((1 + r) ^ (M + 1) * Real.exp (-c * r)) := by rw [pow_succ]; ring
    have hderiv_ae : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), ∀ θ ∈ Set.Ioo a₀ b₀,
        HasDerivAt (fun φ ↦ G φ r) (G' θ r) θ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr θ hθ
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      have hexp : HasDerivAt (fun φ : ℝ ↦ Complex.exp ((φ : ℂ) * Complex.I))
          (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := by
        have hC : HasDerivAt (fun z : ℂ ↦ Complex.exp (z * Complex.I))
            (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I)) (θ : ℂ) :=
          ((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp
        simpa using hC.comp_ofReal
      have harg : HasDerivAt (fun φ : ℝ ↦ 1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
          ((r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ :=
        (hexp.const_mul (r : ℂ)).const_add (1 : ℂ)
      have hF_at : HasDerivAt F (deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :=
        ((hF_holo _ (hsub θ hθ r hr0)).differentiableAt (hΩ.mem_nhds (hsub θ hθ r hr0))).hasDerivAt
      have hcomp : HasDerivAt (fun φ : ℝ ↦ F (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)))
          (deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            ((r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))) θ :=
        hasDerivAt_comp_real hF_at harg
      convert hexp.mul hcomp using 1
      dsimp [G']; ring
    have hhd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (isOpen_Ioo.mem_nhds hθ₀)
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hθ₀) hmeas_G) hG_int hmeas_G'
      hbound_ae hbound_int hderiv_ae)
    -- Now evaluate `∫ r in Ioi 0, G' θ₀ r = 0` by FTC on `Ioi 0`!
    let P : ℝ → ℂ := fun r ↦
      Complex.I * ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I) *
        F (1 + (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
    have hP_deriv : ∀ r ∈ Set.Ici (0 : ℝ), HasDerivAt P (G' θ₀ r) r := by
      intro r hr
      have hlin : HasDerivAt (fun t : ℝ ↦ 1 + (t : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I))
          (Complex.exp ((θ₀ : ℂ) * Complex.I)) r := by
        have hC : HasDerivAt (fun z : ℂ ↦ 1 + z * Complex.exp ((θ₀ : ℂ) * Complex.I))
            (1 * Complex.exp ((θ₀ : ℂ) * Complex.I)) (r : ℂ) :=
          ((hasDerivAt_id (r : ℂ)).mul_const _).const_add 1
        simpa using hC.comp_ofReal
      have hF_at : HasDerivAt F (deriv F (1 + (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)))
          (1 + (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) :=
        ((hF_holo _ (hsub θ₀ hθ₀ r hr)).differentiableAt (hΩ.mem_nhds (hsub θ₀ hθ₀ r hr))).hasDerivAt
      have hFC : HasDerivAt (fun z : ℂ ↦ F (1 + z * Complex.exp ((θ₀ : ℂ) * Complex.I)))
          (deriv F (1 + (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) * Complex.exp ((θ₀ : ℂ) * Complex.I)) (r : ℂ) :=
        hF_at.comp (r : ℂ) (by simpa using ((hasDerivAt_id (r : ℂ)).mul_const _).const_add 1)
      have hF_r := hFC.comp_ofReal
      have hpre : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I))
          (Complex.exp ((θ₀ : ℂ) * Complex.I)) r := by
        have hC : HasDerivAt (fun z : ℂ ↦ z * Complex.exp ((θ₀ : ℂ) * Complex.I))
            (1 * Complex.exp ((θ₀ : ℂ) * Complex.I)) (r : ℂ) := (hasDerivAt_id (r : ℂ)).mul_const _
        simpa using hC.comp_ofReal
      have htot := (hpre.mul hF_r).const_mul Complex.I
      convert htot using 1
      dsimp [G']; ring
    have hP_tendsto : Tendsto P atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hdom_lim : Tendsto (fun r : ℝ ↦ C * ((1 + r) ^ (M + 1) * Real.exp (-c * r))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun r : ℝ ↦ (1 + r) ^ (M + 1) * Real.exp (-c * r)) atTop (𝓝 0) := by
          have hpow := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (M + 1)
          have hcomp := hpow.comp (tendsto_atTop_add_const_left atTop c
            (tendsto_id.const_mul_atTop hc))
          have h2 : (fun r : ℝ ↦ (1 + r) ^ (M + 1) * Real.exp (-c * r)) =
              fun r : ℝ ↦ (Real.exp c / c ^ (M + 1)) * ((c + c * r) ^ (M + 1) * Real.exp (-(c + c * r))) := by
            ext r
            have hc_ne : c ≠ 0 := hc.ne'
            have hexp : Real.exp (-(c + c * r)) = Real.exp (-c) * Real.exp (-c * r) := by
              rw [show -(c + c * r) = -c + -c * r by ring, Real.exp_add]
            rw [hexp, show c + c * r = c * (1 + r) by ring, mul_pow, Real.exp_neg]
            field_simp [hc_ne, (Real.exp_pos c).ne']
          rw [h2]
          simpa using hcomp.const_mul (Real.exp c / c ^ (M + 1))
        simpa using h1.const_mul C
      refine squeeze_zero_norm' ?_ hdom_lim
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      dsimp [P]
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_exp_ofReal_mul_I, mul_one]
      calc r * ‖F (1 + (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I))‖
          ≤ (1 + r) * (C * (1 + r) ^ M * Real.exp (-c * r)) :=
            mul_le_mul (by linarith) (hbdF θ₀ hθ₀ r hr) (norm_nonneg _) (by linarith)
        _ = C * ((1 + r) ^ (M + 1) * Real.exp (-c * r)) := by rw [pow_succ']; ring
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hP_deriv hhd.1 hP_tendsto
    have hP0 : P 0 = 0 := by simp [P]
    rw [hP0, sub_zero] at hftc
    rw [hftc] at hhd
    exact hhd.2
  have hftc0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := I) (f' := fun _ ↦ (0 : ℂ))
    (fun θ hθ ↦ by
      rw [Set.uIcc_of_le hab] at hθ
      exact hderiv_zero θ ⟨lt_of_lt_of_le ha₀ hθ.1, lt_of_le_of_lt hθ.2 hb₀⟩)
    intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at hftc0
  have hconst : I a = I b := (sub_eq_zero.mp hftc0.symm).symm
  simpa [I, integral_const_mul] using hconst

/-- Shift identity for Lebesgue integrals on `(0, ∞)`: `∫ r in Ioi 0, f (1 + r) = ∫ y in Ioi 1, f y`. -/
theorem integral_Ioi_zero_one_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ r in Set.Ioi (0 : ℝ), f (1 + r) = ∫ y in Set.Ioi (1 : ℝ), f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have heq : (fun r : ℝ ↦ (Set.Ioi (0 : ℝ)).indicator (fun t ↦ f (1 + t)) r) =
      fun r : ℝ ↦ (Set.Ioi (1 : ℝ)).indicator f (1 + r) := by
    ext r
    by_cases hr : 0 < r
    · have h1 : 1 < 1 + r := by linarith
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hr), Set.indicator_of_mem (Set.mem_Ioi.mpr h1)]
    · have h1 : ¬ (1 < 1 + r) := by linarith
      rw [Set.indicator_of_notMem (show r ∉ Set.Ioi (0 : ℝ) from hr),
          Set.indicator_of_notMem (show 1 + r ∉ Set.Ioi (1 : ℝ) from h1)]
  rw [heq]
  exact MeasureTheory.integral_add_left_eq_self (fun y : ℝ ↦ (Set.Ioi (1 : ℝ)).indicator f y) 1

/-- Special case of `ray_integral_const_on_Icc`: for any holomorphic `F` on `{1/2 < Re z}` with
exponential decay `C (1 + r)^M exp(-c Re z)` on `Re z ≥ 1`, rotating `[1, ∞)` to `γ₋` or `γ₊`
leaves the integral unchanged! -/
theorem ray_integral_eq_real {F : ℂ → ℂ}
    (hF_holo : DifferentiableOn ℂ F {z : ℂ | (1 / 2 : ℝ) < z.re})
    {C c : ℝ} {M : ℕ} (hC : 0 ≤ C) (hc : 0 < c)
    (hbdF : ∀ z : ℂ, 1 ≤ z.re → ‖F z‖ ≤ C * (1 + ‖z‖) ^ M * Real.exp (-c * z.re))
    (hbdF' : ∀ z : ℂ, 1 ≤ z.re → ‖deriv F z‖ ≤ C * (1 + ‖z‖) ^ M * Real.exp (-c * z.re)) :
    (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) * ∫ r in Set.Ioi (0 : ℝ), F (gammaMinus r) =
      ∫ y in Set.Ioi (1 : ℝ), F (y : ℂ)) ∧
    (Complex.exp (Complex.I * (Real.pi : ℂ) / 4) * ∫ r in Set.Ioi (0 : ℝ), F (gammaPlus r) =
      ∫ y in Set.Ioi (1 : ℝ), F (y : ℂ)) := by
  have hre_ge : ∀ θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3), ∀ r : ℝ, 0 ≤ r →
      1 + r / 2 ≤ (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re := by
    intro θ hθ r hr
    have hcos : 1 / 2 ≤ Real.cos θ := by
      rw [← Real.cos_abs, ← Real.cos_pi_div_three]
      exact Real.strictAntiOn_cos.antitoneOn
        ⟨abs_nonneg _, (abs_lt.mpr hθ).le.trans (by linarith [Real.pi_pos])⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩ (abs_lt.mpr hθ).le
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
    nlinarith
  have hnorm_le : ∀ θ : ℝ, ∀ r : ℝ, 0 ≤ r →
      1 + ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ 2 * (1 + r) := by
    intro θ r hr
    have h1 : ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ 1 + r := by
      calc ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖
          ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := norm_add_le _ _
        _ = 1 + r := by
            rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                Complex.norm_exp_ofReal_mul_I, mul_one]
    linarith
  have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsub : ∀ θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3), ∀ r : ℝ, 0 ≤ r →
      1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ {z : ℂ | (1 / 2 : ℝ) < z.re} :=
    fun θ hθ r hr ↦ by have := hre_ge θ hθ r hr; change (1 / 2 : ℝ) < _; linarith
  have hbd1 : ∀ θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3), ∀ r : ℝ, 0 ≤ r →
      ‖F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
        (C * 2 ^ M) * (1 + r) ^ M * Real.exp (-(c / 2) * r) := fun θ hθ r hr ↦ by
    have hre := hre_ge θ hθ r hr
    have h1 := hbdF _ (by linarith)
    have h2 : (1 + ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖) ^ M ≤ 2 ^ M * (1 + r) ^ M := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (hnorm_le θ r hr) M
    have h3 : Real.exp (-c * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re) ≤
        Real.exp (-(c / 2) * r) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc ‖F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
        ≤ C * (1 + ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖) ^ M *
            Real.exp (-c * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re) := h1
      _ ≤ C * (2 ^ M * (1 + r) ^ M) * Real.exp (-(c / 2) * r) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (Real.exp_pos _).le (by positivity)
      _ = (C * 2 ^ M) * (1 + r) ^ M * Real.exp (-(c / 2) * r) := by ring
  have hbd2 : ∀ θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3), ∀ r : ℝ, 0 ≤ r →
      ‖deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
        (C * 2 ^ M) * (1 + r) ^ M * Real.exp (-(c / 2) * r) := fun θ hθ r hr ↦ by
    have hre := hre_ge θ hθ r hr
    have h1 := hbdF' _ (by linarith)
    have h2 : (1 + ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖) ^ M ≤ 2 ^ M * (1 + r) ^ M := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (hnorm_le θ r hr) M
    have h3 : Real.exp (-c * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re) ≤
        Real.exp (-(c / 2) * r) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc ‖deriv F (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
        ≤ C * (1 + ‖1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖) ^ M *
            Real.exp (-c * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re) := h1
      _ ≤ C * (2 ^ M * (1 + r) ^ M) * Real.exp (-(c / 2) * r) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (Real.exp_pos _).le (by positivity)
      _ = (C * 2 ^ M) * (1 + r) ^ M * Real.exp (-(c / 2) * r) := by ring
  have hzero_eq : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) *
      ∫ r in Set.Ioi (0 : ℝ), F (1 + (r : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) =
      ∫ y in Set.Ioi (1 : ℝ), F (y : ℂ) := by
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one]
    simpa [Complex.ofReal_add] using integral_Ioi_zero_one_add (fun y : ℝ ↦ F (y : ℂ))
  constructor
  · have h := ray_integral_const_on_Icc hopen hF_holo
      (a₀ := -(Real.pi / 3)) (a := -(Real.pi / 4)) (b := 0) (b₀ := Real.pi / 3)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      hsub (by positivity) (by positivity) hbd1 hbd2
    rw [hzero_eq] at h
    have hexp : (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) = -Complex.I * (Real.pi : ℂ) / 4 := by
      push_cast; ring
    simpa only [hexp, gammaMinus] using h
  · have h := ray_integral_const_on_Icc hopen hF_holo
      (a₀ := -(Real.pi / 3)) (a := 0) (b := Real.pi / 4) (b₀ := Real.pi / 3)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      hsub (by positivity) (by positivity) hbd1 hbd2
    rw [hzero_eq] at h
    have hexp : (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) = Complex.I * (Real.pi : ℂ) / 4 := by
      push_cast; ring
    simpa only [hexp, gammaPlus] using h.symm

/-- Lateral rotated-ray integral `Φ₊(u) = ∫_{γ₋} b(y) (1 + u y)^{-k} dy` (`u ∈ U₊`). -/
def PhiPlus (k : ℂ) (b : ℂ → ℂ) (u : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
    ∫ r in Set.Ioi (0 : ℝ), b (gammaMinus r) * (1 + u * gammaMinus r) ^ (-k)

/-- Lateral rotated-ray integral `Φ₋(u) = ∫_{γ₊} b(y) (1 + u y)^{-k} dy` (`u ∈ U₋`). -/
def PhiMinus (k : ℂ) (b : ℂ → ℂ) (u : ℂ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) / 4) *
    ∫ r in Set.Ioi (0 : ℝ), b (gammaPlus r) * (1 + u * gammaPlus r) ^ (-k)

/-- Uniform positive lower bound on `‖1 + u * gammaMinus r‖` on a small closed ball in `UPlus x₀`. -/
private lemma UPlus_ball_lower_bound {x₀ : ℝ} (hx₀ : x₀ ≤ 1 / 4)
    {u₀ : ℂ} (hu₀ : u₀ ∈ UPlus x₀) :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ Metric.closedBall u₀ δ ⊆ UPlus x₀ ∧
      ∀ u ∈ Metric.closedBall u₀ δ, ∀ r : ℝ, 0 ≤ r → η ≤ ‖1 + u * gammaMinus r‖ := by
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.isOpen_iff.mp (isOpen_UPlus x₀) u₀ hu₀
  let δ : ℝ := min (δ₀ / 2) (‖u₀‖ / 2)
  have hu₀_pos : 0 < ‖u₀‖ := hu₀.1
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hcl_sub : Metric.closedBall u₀ δ ⊆ UPlus x₀ := fun u hu ↦
    hball₀ (lt_of_le_of_lt (Metric.mem_closedBall.mp hu) (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
  have hnorm_low : ∀ u ∈ Metric.closedBall u₀ δ, ‖u₀‖ / 2 ≤ ‖u‖ := fun u hu ↦ by
    have hd : ‖u - u₀‖ ≤ ‖u₀‖ / 2 := by
      rw [← Complex.dist_eq]; exact (Metric.mem_closedBall.mp hu).trans (min_le_right _ _)
    have htri := norm_sub_norm_le u₀ u; rw [norm_sub_rev] at htri; linarith
  let R : ℝ := 4 * Real.sqrt 2 / ‖u₀‖
  have hR_pos : 0 < R := by positivity
  let K : Set (ℂ × ℝ) := Metric.closedBall u₀ δ ×ˢ Set.Icc 0 R
  have hK_comp : IsCompact K := (isCompact_closedBall u₀ δ).prod isCompact_Icc
  have hK_ne : K.Nonempty := ⟨(u₀, 0), Metric.mem_closedBall_self hδ.le, left_mem_Icc.mpr hR_pos.le⟩
  let g : ℂ × ℝ → ℝ := fun p ↦ ‖1 + p.1 * gammaMinus p.2‖
  have hg_cont : Continuous g :=
    (continuous_const.add (continuous_fst.mul
      (continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))).norm
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hK_comp.exists_isMinOn hK_ne hg_cont.continuousOn
  have hg_pos : 0 < g p₀ :=
    norm_pos_iff.mpr (Complex.slitPlane_ne_zero
      (one_add_mul_mem_slitPlane_UPlus hx₀ (hcl_sub hp₀K.1) hp₀K.2.1))
  refine ⟨δ, min 1 (g p₀), hδ, lt_min zero_lt_one hg_pos, hcl_sub, fun u hu r hr ↦ ?_⟩
  by_cases hrR : r ≤ R
  · have hmin : g p₀ ≤ g (u, r) := hp₀min ⟨hu, hr, hrR⟩
    exact (min_le_right 1 (g p₀)).trans hmin
  · push Not at hrR
    have hgm_ge : r / Real.sqrt 2 ≤ ‖gammaMinus r‖ := by
      have hre : 1 + r / Real.sqrt 2 = (gammaMinus r).re := (gammaMinus_re r).symm
      have h1 : (gammaMinus r).re ≤ ‖gammaMinus r‖ := Complex.re_le_norm _
      linarith
    have hbig : 2 ≤ ‖u * gammaMinus r‖ := by
      rw [norm_mul]
      have h1 := hnorm_low u hu
      have h2 : (‖u₀‖ / 2) * (R / Real.sqrt 2) = 2 := by
        dsimp [R]; field_simp [hu₀_pos.ne', (Real.sqrt_pos.mpr zero_lt_two).ne']; norm_num
      have h3 : (‖u₀‖ / 2) * (R / Real.sqrt 2) ≤ ‖u‖ * ‖gammaMinus r‖ :=
        mul_le_mul h1 ((div_le_div_of_nonneg_right hrR.le (Real.sqrt_nonneg 2)).trans hgm_ge)
          (by positivity) (norm_nonneg u)
      linarith
    have htri : ‖u * gammaMinus r‖ - 1 ≤ ‖1 + u * gammaMinus r‖ := by
      have := norm_sub_norm_le (u * gammaMinus r) (-1 : ℂ)
      simpa [sub_neg_eq_add, add_comm] using this
    exact (min_le_left 1 (g p₀)).trans (by linarith)

/-- Holomorphy and exact `j`-th derivative formula for `PhiPlus` on `UPlus x₀` (`x₀ ≤ 1/4`). -/
theorem PhiPlus_iteratedDeriv {b : ℂ → ℂ} {C_b c_b : ℝ} (hb : ExpDecayKernel b C_b c_b)
    {x₀ : ℝ} (hx₀ : x₀ ≤ 1 / 4) (k : ℂ) (j : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv j (PhiPlus k b)) (UPlus x₀) ∧
      ∀ u ∈ UPlus x₀,
        iteratedDeriv j (PhiPlus k b) u =
          (-1 : ℂ) ^ j * risingFac k j * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
            ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ j * b (gammaMinus r) *
              (1 + u * gammaMinus r) ^ (-(k + (j : ℂ))) := by
  have hCb : 0 ≤ C_b := hb.C_nonneg
  have hc' : 0 < c_b / Real.sqrt 2 := div_pos hb.c_pos (Real.sqrt_pos.mpr zero_lt_two)
  have hdom_int : ∀ d : ℕ, IntegrableOn (fun r : ℝ ↦ (1 + r) ^ d * Real.exp (-(c_b / Real.sqrt 2) * r)) (Set.Ioi 0) :=
    integrableOn_one_add_pow_mul_exp hc'
  have hgm_norm : ∀ r : ℝ, 0 ≤ r → ‖gammaMinus r‖ ≤ 1 + r := fun r hr ↦ by
    dsimp [gammaMinus]
    calc ‖1 + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖
        ≤ 1 + ‖(r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖ := by
          simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
      _ = 1 + r := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
              show -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I, mul_one]
  have hdiff_step : ∀ (α : ℂ) (m : ℕ) (u₀ : ℂ), u₀ ∈ UPlus x₀ →
      HasDerivAt
        (fun u : ℂ ↦ ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ m * b (gammaMinus r) * (1 + u * gammaMinus r) ^ (-α))
        ((-α) * ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ (m + 1) * b (gammaMinus r) * (1 + u₀ * gammaMinus r) ^ (-(α + 1))) u₀ := by
    intro α m u₀ hu₀
    obtain ⟨δ, η, hδ, hη, hcl_sub, hlow⟩ := UPlus_ball_lower_bound hx₀ hu₀
    let s : Set ℂ := Metric.ball u₀ δ
    have hs_nhds : s ∈ 𝓝 u₀ := Metric.ball_mem_nhds u₀ hδ
    have hs_sub : s ⊆ Metric.closedBall u₀ δ := Metric.ball_subset_closedBall
    let M_u : ℝ := ‖u₀‖ + δ
    have hpow_bd : ∀ (β : ℂ), ∃ K_β : ℝ, ∃ d_β : ℕ, 0 ≤ K_β ∧
        ∀ u ∈ s, ∀ r : ℝ, 0 ≤ r → ‖(1 + u * gammaMinus r) ^ (-β)‖ ≤ K_β * (1 + r) ^ d_β := by
      intro β
      let d : ℕ := Nat.ceil (max (-β.re) 0)
      have hd_ge : -β.re ≤ (d : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
      have hC_const : ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ s, ∀ r : ℝ, 0 ≤ r →
          ‖1 + u * gammaMinus r‖ ^ (-β.re) ≤ K * (1 + r) ^ d := by
        by_cases hneg : -β.re ≤ 0
        · refine ⟨η ^ (-β.re), Real.rpow_nonneg hη.le _, fun u hu r hr ↦ ?_⟩
          have h1 := Real.rpow_le_rpow_of_nonpos hη (hlow u (hs_sub hu) r hr) hneg
          have h2 : (1 : ℝ) ≤ (1 + r) ^ d := one_le_pow₀ (by linarith)
          nlinarith [Real.rpow_nonneg hη.le (-β.re)]
        · push Not at hneg
          refine ⟨(1 + M_u) ^ (-β.re), by positivity, fun u hu r hr ↦ ?_⟩
          have hu_le : ‖u‖ ≤ M_u := by
            have hd' : ‖u - u₀‖ < δ := by rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hu
            have := norm_sub_norm_le u u₀; dsimp [M_u]; linarith
          have hup : ‖1 + u * gammaMinus r‖ ≤ (1 + M_u) * (1 + r) := by
            calc ‖1 + u * gammaMinus r‖ ≤ 1 + ‖u‖ * ‖gammaMinus r‖ := by
                  simpa [norm_mul] using norm_add_le (1 : ℂ) (u * gammaMinus r)
              _ ≤ 1 * (1 + r) + M_u * (1 + r) := by
                  have := hgm_norm r hr; nlinarith [norm_nonneg u, norm_nonneg (gammaMinus r)]
              _ = (1 + M_u) * (1 + r) := by ring
          calc ‖1 + u * gammaMinus r‖ ^ (-β.re)
              ≤ ((1 + M_u) * (1 + r)) ^ (-β.re) := Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
            _ = (1 + M_u) ^ (-β.re) * (1 + r) ^ (-β.re) := Real.mul_rpow (by positivity) (by linarith)
            _ ≤ (1 + M_u) ^ (-β.re) * (1 + r) ^ (d : ℝ) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hd_ge) (by positivity)
            _ = (1 + M_u) ^ (-β.re) * (1 + r) ^ d := by rw [Real.rpow_natCast]
      obtain ⟨K, hK, hKbd⟩ := hC_const
      refine ⟨K * Real.exp (|(-β).im| * Real.pi), d, by positivity, fun u hu r hr ↦ ?_⟩
      have hne := Complex.slitPlane_ne_zero (one_add_mul_mem_slitPlane_UPlus hx₀ (hcl_sub (hs_sub hu)) hr)
      calc ‖(1 + u * gammaMinus r) ^ (-β)‖
          ≤ ‖1 + u * gammaMinus r‖ ^ (-β).re * Real.exp (|(-β).im| * Real.pi) := norm_cpow_le_rpow_mul_exp hne
        _ ≤ (K * (1 + r) ^ d) * Real.exp (|(-β).im| * Real.pi) := by
            rw [Complex.neg_re]; exact mul_le_mul_of_nonneg_right (hKbd u hu r hr) (Real.exp_pos _).le
        _ = K * Real.exp (|(-β).im| * Real.pi) * (1 + r) ^ d := by ring
    obtain ⟨K₀, d₀, hK₀, hbd₀⟩ := hpow_bd α
    obtain ⟨K₁, d₁, hK₁, hbd₁⟩ := hpow_bd (α + 1)
    let F : ℂ → ℝ → ℂ := fun u r ↦ (gammaMinus r) ^ m * b (gammaMinus r) * (1 + u * gammaMinus r) ^ (-α)
    let F' : ℂ → ℝ → ℂ := fun u r ↦ (-α) * ((gammaMinus r) ^ (m + 1) * b (gammaMinus r) * (1 + u * gammaMinus r) ^ (-(α + 1)))
    have hgm_cont : Continuous gammaMinus :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcont_b : ContinuousOn (fun r : ℝ ↦ b (gammaMinus r)) (Set.Ioi 0) := by
      intro r hr
      have hre : (1 / 2 : ℝ) < (gammaMinus r).re := by
        rw [gammaMinus_re]; have h1 : 0 < r := hr; linarith [div_pos h1 (Real.sqrt_pos.mpr zero_lt_two)]
      have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact (((hb.holo _ hre).differentiableAt (hopen.mem_nhds hre)).continuousAt.comp
        hgm_cont.continuousAt).continuousWithinAt
    have hmeas_F : ∀ u ∈ s, AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi 0)) := by
      intro u hu
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      have hpow_c : ContinuousOn (fun r : ℝ ↦ (1 + u * gammaMinus r) ^ (-α)) (Set.Ioi 0) := fun r hr ↦ by
        have hsl := one_add_mul_mem_slitPlane_UPlus hx₀ (hcl_sub (hs_sub hu)) (Set.mem_Ioi.mp hr).le
        exact (continuousAt_cpow_const_comp
          (continuousAt_const.add (continuousAt_const.mul hgm_cont.continuousAt)) hsl).continuousWithinAt
      exact (((hgm_cont.pow m).continuousOn).mul hcont_b).mul hpow_c
    have hmeas_F' : AEStronglyMeasurable (F' u₀) (volume.restrict (Set.Ioi 0)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      have hpow_c : ContinuousOn (fun r : ℝ ↦ (1 + u₀ * gammaMinus r) ^ (-(α + 1))) (Set.Ioi 0) := fun r hr ↦ by
        have hsl := one_add_mul_mem_slitPlane_UPlus hx₀ hu₀ (Set.mem_Ioi.mp hr).le
        exact (continuousAt_cpow_const_comp
          (continuousAt_const.add (continuousAt_const.mul hgm_cont.continuousAt)) hsl).continuousWithinAt
      exact continuousOn_const.mul ((((hgm_cont.pow (m + 1)).continuousOn).mul hcont_b).mul hpow_c)
    have hF_int : Integrable (F u₀) (volume.restrict (Set.Ioi 0)) := by
      refine ((hdom_int (m + d₀)).const_mul (C_b * K₀)).mono' (hmeas_F u₀ (Metric.mem_ball_self hδ)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      dsimp [F]; rw [norm_mul, norm_mul, norm_pow]
      have hre : 1 ≤ (gammaMinus r).re := by rw [gammaMinus_re]; linarith [div_nonneg hr0 (Real.sqrt_nonneg 2)]
      have hb_r : ‖b (gammaMinus r)‖ ≤ C_b * Real.exp (-(c_b / Real.sqrt 2) * r) := by
        have h1 := hb.bound (gammaMinus r) hre
        rw [gammaMinus_re] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have : -c_b * (1 + r / Real.sqrt 2) = -c_b + -(c_b / Real.sqrt 2) * r := by ring
          linarith [hb.c_pos])) hCb)
      have hgm_p : ‖gammaMinus r‖ ^ m ≤ (1 + r) ^ m := pow_le_pow_left₀ (norm_nonneg _) (hgm_norm r hr0) m
      have hp_r := hbd₀ u₀ (Metric.mem_ball_self hδ) r hr0
      calc ‖gammaMinus r‖ ^ m * ‖b (gammaMinus r)‖ * ‖(1 + u₀ * gammaMinus r) ^ (-α)‖
          ≤ ((1 + r) ^ m * (C_b * Real.exp (-(c_b / Real.sqrt 2) * r))) * (K₀ * (1 + r) ^ d₀) :=
            mul_le_mul (mul_le_mul hgm_p hb_r (norm_nonneg _) (by positivity)) hp_r (norm_nonneg _) (by positivity)
        _ = C_b * K₀ * ((1 + r) ^ (m + d₀) * Real.exp (-(c_b / Real.sqrt 2) * r)) := by rw [pow_add]; ring
    let bound : ℝ → ℝ := fun r ↦ (‖α‖ * C_b * K₁) * ((1 + r) ^ (m + 1 + d₁) * Real.exp (-(c_b / Real.sqrt 2) * r))
    have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) := (hdom_int (m + 1 + d₁)).const_mul _
    have hbound_ae : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), ∀ u ∈ s, ‖F' u r‖ ≤ bound r := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr u hu
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      dsimp [F', bound]; rw [norm_mul, norm_neg, norm_mul, norm_mul, norm_pow]
      have hre : 1 ≤ (gammaMinus r).re := by rw [gammaMinus_re]; linarith [div_nonneg hr0 (Real.sqrt_nonneg 2)]
      have hb_r : ‖b (gammaMinus r)‖ ≤ C_b * Real.exp (-(c_b / Real.sqrt 2) * r) := by
        have h1 := hb.bound (gammaMinus r) hre
        rw [gammaMinus_re] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have : -c_b * (1 + r / Real.sqrt 2) = -c_b + -(c_b / Real.sqrt 2) * r := by ring
          linarith [hb.c_pos])) hCb)
      have hgm_p : ‖gammaMinus r‖ ^ (m + 1) ≤ (1 + r) ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg _) (hgm_norm r hr0) _
      have hp_r := hbd₁ u hu r hr0
      calc ‖α‖ * (‖gammaMinus r‖ ^ (m + 1) * ‖b (gammaMinus r)‖ * ‖(1 + u * gammaMinus r) ^ (-(α + 1))‖)
          ≤ ‖α‖ * (((1 + r) ^ (m + 1) * (C_b * Real.exp (-(c_b / Real.sqrt 2) * r))) * (K₁ * (1 + r) ^ d₁)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul hgm_p hb_r (norm_nonneg _) (by positivity)) hp_r (norm_nonneg _) (by positivity))
              (norm_nonneg _)
        _ = ‖α‖ * C_b * K₁ * ((1 + r) ^ (m + 1 + d₁) * Real.exp (-(c_b / Real.sqrt 2) * r)) := by
            rw [pow_add]; ring
    have hderiv_ae : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), ∀ u ∈ s, HasDerivAt (fun w ↦ F w r) (F' u r) u := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr u hu
      have hsl := one_add_mul_mem_slitPlane_UPlus hx₀ (hcl_sub (hs_sub hu)) (Set.mem_Ioi.mp hr).le
      have hlin : HasDerivAt (fun w : ℂ ↦ 1 + w * gammaMinus r) (gammaMinus r) u := by
        simpa using ((hasDerivAt_id u).mul_const (gammaMinus r)).const_add (1 : ℂ)
      have hpow := (hlin.cpow_const (c := -α) hsl).const_mul ((gammaMinus r) ^ m * b (gammaMinus r))
      convert hpow using 1; dsimp [F']; rw [pow_succ]; ring_nf
    have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds
      (Filter.eventually_of_mem hs_nhds hmeas_F) hF_int hmeas_F' hbound_ae hbound_int hderiv_ae).2
    convert hres using 1; rw [← integral_const_mul]
  induction j with
  | zero =>
    refine ⟨fun u hu ↦ ((hdiff_step k 0 u hu).const_mul
        (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))).differentiableAt.differentiableWithinAt.congr
        (fun w _ ↦ by simp [PhiPlus]) (by simp [PhiPlus]), fun u _ ↦ by simp [PhiPlus]⟩
  | succ j ih =>
    obtain ⟨_, hform⟩ := ih
    have heq_step : ∀ u ∈ UPlus x₀,
        iteratedDeriv (j + 1) (PhiPlus k b) u =
          (-1 : ℂ) ^ (j + 1) * risingFac k (j + 1) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
            ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ (j + 1) * b (gammaMinus r) *
              (1 + u * gammaMinus r) ^ (-(k + ((j + 1 : ℕ) : ℂ))) := by
      intro u hu
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (PhiPlus k b) =ᶠ[𝓝 u]
          fun w ↦ (-1 : ℂ) ^ j * risingFac k j * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
            ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ j * b (gammaMinus r) *
              (1 + w * gammaMinus r) ^ (-(k + (j : ℂ))) := by
        filter_upwards [(isOpen_UPlus x₀).mem_nhds hu] with w hw; exact hform w hw
      rw [hev.deriv_eq]
      have hd := (hdiff_step (k + (j : ℂ)) j u hu).const_mul
        ((-1 : ℂ) ^ j * risingFac k j * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
      rw [hd.deriv, risingFac_succ, pow_succ]
      have hexp : -(k + (j : ℂ) + 1) = -(k + ((j + 1 : ℕ) : ℂ)) := by push_cast; ring
      rw [hexp]; ring
    refine ⟨fun u hu ↦ ?_, heq_step⟩
    have hd := (hdiff_step (k + ((j + 1 : ℕ) : ℂ)) (j + 1) u hu).const_mul
      ((-1 : ℂ) ^ (j + 1) * risingFac k (j + 1) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
    exact hd.differentiableAt.differentiableWithinAt.congr (fun w hw ↦ heq_step w hw) (heq_step u hu)

/-- Holomorphy and exact `j`-th derivative formula for `PhiMinus` on `UMinus x₀` (`x₀ ≤ 1/4`),
obtained cleanly from `PhiPlus_iteratedDeriv` via complex conjugation! -/
theorem PhiMinus_iteratedDeriv {b : ℂ → ℂ} {C_b c_b : ℝ} (hb : ExpDecayKernel b C_b c_b)
    {x₀ : ℝ} (hx₀ : x₀ ≤ 1 / 4) (k : ℂ) (j : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv j (PhiMinus k b)) (UMinus x₀) ∧
      ∀ u ∈ UMinus x₀,
        iteratedDeriv j (PhiMinus k b) u =
          (-1 : ℂ) ^ j * risingFac k j * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) *
            ∫ r in Set.Ioi (0 : ℝ), (gammaPlus r) ^ j * b (gammaPlus r) *
              (1 + u * gammaPlus r) ^ (-(k + (j : ℂ))) := by
  -- Define conjugate kernel `bConj z := star (b (star z))`, which also satisfies `ExpDecayKernel`!
  let bConj : ℂ → ℂ := fun z ↦ starRingEnd ℂ (b (starRingEnd ℂ z))
  have hbConj : ExpDecayKernel bConj C_b c_b := by
    have hholo : DifferentiableOn ℂ bConj {z : ℂ | (1 / 2 : ℝ) < z.re} := by
      intro z hz
      have hsz : (1 / 2 : ℝ) < (starRingEnd ℂ z).re := by simpa using hz
      have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const Complex.continuous_re
      have hd := ((hb.holo _ hsz).differentiableAt (hopen.mem_nhds hsz)).hasDerivAt
      exact (hasDerivAt_conj_comp hd).differentiableAt.differentiableWithinAt
    refine ⟨hb.C_nonneg, hb.c_pos, hholo, ?_, ?_⟩
    · intro z hz
      dsimp [bConj]; rw [RCLike.norm_conj]
      simpa using hb.bound (starRingEnd ℂ z) (by simpa using hz)
    · intro z hz
      have hsz : (1 / 2 : ℝ) < (starRingEnd ℂ z).re := by simp; linarith
      have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const Complex.continuous_re
      have hd := ((hb.holo _ hsz).differentiableAt (hopen.mem_nhds hsz)).hasDerivAt
      rw [(hasDerivAt_conj_comp hd).deriv, RCLike.norm_conj]
      simpa using hb.deriv_bound (starRingEnd ℂ z) (by simpa using hz)
  have hexp_conj : starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)) =
      Complex.exp (Complex.I * (Real.pi : ℂ) / 4) := by
    rw [← Complex.exp_conj]; congr 1
    simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring
  have hphi_conj : ∀ u ∈ UMinus x₀,
      PhiMinus k b u = starRingEnd ℂ (PhiPlus (starRingEnd ℂ k) bConj (starRingEnd ℂ u)) := by
    intro u hu
    unfold PhiMinus PhiPlus
    rw [map_mul, hexp_conj, ← integral_conj]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hsl : 1 + u * gammaPlus r ∈ Complex.slitPlane :=
      one_add_mul_mem_slitPlane_UMinus hx₀ hu (Set.mem_Ioi.mp hr).le
    have harg_ne : (1 + u * gammaPlus r).arg ≠ Real.pi := by
      intro hpi; have ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hpi
      rcases Complex.mem_slitPlane_iff.mp hsl with h | h
      · linarith
      · exact h him
    dsimp [bConj]
    have hcp := Complex.cpow_conj (1 + u * gammaPlus r) (-(starRingEnd ℂ k)) harg_ne
    simp only [map_add, map_one, map_mul, map_neg, Complex.conj_conj, star_gammaPlus] at hcp
    rw [map_mul, Complex.conj_conj, star_gammaMinus, ← hcp]
  have hiter_conj : ∀ (f : ℂ → ℂ) (m : ℕ), DifferentiableOn ℂ f (UPlus x₀) →
      ∀ u ∈ UMinus x₀,
        iteratedDeriv m (fun w ↦ starRingEnd ℂ (f (starRingEnd ℂ w))) u =
          starRingEnd ℂ (iteratedDeriv m f (starRingEnd ℂ u)) := by
    intro f m hf_diff
    induction m with
    | zero => intro u _; simp
    | succ m ih =>
      intro u hu
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hev : iteratedDeriv m (fun w ↦ starRingEnd ℂ (f (starRingEnd ℂ w))) =ᶠ[𝓝 u]
          fun w ↦ starRingEnd ℂ (iteratedDeriv m f (starRingEnd ℂ w)) := by
        filter_upwards [(isOpen_UMinus x₀).mem_nhds hu] with w hw; exact ih w hw
      rw [hev.deriv_eq]
      have hdiff_m := differentiableOn_iteratedDeriv_open (isOpen_UPlus x₀) hf_diff m
      have hsu : starRingEnd ℂ u ∈ UPlus x₀ := mem_UMinus_iff_star.mp hu
      have hd := ((hdiff_m _ hsu).differentiableAt ((isOpen_UPlus x₀).mem_nhds hsu)).hasDerivAt
      exact (hasDerivAt_conj_comp hd).deriv
  have hP := PhiPlus_iteratedDeriv hbConj hx₀ (starRingEnd ℂ k) j
  have hP0' : DifferentiableOn ℂ (PhiPlus (starRingEnd ℂ k) bConj) (UPlus x₀) := by
    simpa [iteratedDeriv_zero] using (PhiPlus_iteratedDeriv hbConj hx₀ (starRingEnd ℂ k) 0).1
  have hiter_eq : ∀ u ∈ UMinus x₀,
      iteratedDeriv j (PhiMinus k b) u =
        starRingEnd ℂ (iteratedDeriv j (PhiPlus (starRingEnd ℂ k) bConj) (starRingEnd ℂ u)) := by
    intro u hu
    have hev : PhiMinus k b =ᶠ[𝓝 u]
        fun w ↦ starRingEnd ℂ (PhiPlus (starRingEnd ℂ k) bConj (starRingEnd ℂ w)) := by
      filter_upwards [(isOpen_UMinus x₀).mem_nhds hu] with w hw; exact hphi_conj w hw
    rw [hev.iteratedDeriv_eq j]
    exact hiter_conj _ j hP0' u hu
  have hform_minus : ∀ u ∈ UMinus x₀,
      iteratedDeriv j (PhiMinus k b) u =
        (-1 : ℂ) ^ j * risingFac k j * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) *
          ∫ r in Set.Ioi (0 : ℝ), (gammaPlus r) ^ j * b (gammaPlus r) *
            (1 + u * gammaPlus r) ^ (-(k + (j : ℂ))) := by
    intro u hu
    rw [hiter_eq u hu, hP.2 (starRingEnd ℂ u) (mem_UMinus_iff_star.mp hu)]
    have hrf : starRingEnd ℂ (risingFac (starRingEnd ℂ k) j) = risingFac k j := by
      unfold risingFac; rw [map_prod]; apply Finset.prod_congr rfl; intro m _; simp
    rw [map_mul, map_mul, map_mul, map_pow, map_neg, map_one, hrf, hexp_conj, ← integral_conj]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hsl : 1 + u * gammaPlus r ∈ Complex.slitPlane :=
      one_add_mul_mem_slitPlane_UMinus hx₀ hu (Set.mem_Ioi.mp hr).le
    have harg_ne : (1 + u * gammaPlus r).arg ≠ Real.pi := by
      intro hpi; have ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hpi
      rcases Complex.mem_slitPlane_iff.mp hsl with h | h
      · linarith
      · exact h him
    dsimp [bConj]
    have hcp := Complex.cpow_conj (1 + u * gammaPlus r) (-(starRingEnd ℂ k + (j : ℂ))) harg_ne
    simp only [map_add, map_one, map_mul, map_neg, map_natCast, Complex.conj_conj, star_gammaPlus] at hcp
    rw [map_mul, map_mul, map_pow, star_gammaMinus, Complex.conj_conj, ← hcp]
  refine ⟨fun u hu ↦ ?_, hform_minus⟩
  have hsu : starRingEnd ℂ u ∈ UPlus x₀ := mem_UMinus_iff_star.mp hu
  have hd := ((hP.1 _ hsu).differentiableAt ((isOpen_UPlus x₀).mem_nhds hsu)).hasDerivAt
  exact (hasDerivAt_conj_comp hd).differentiableAt.differentiableWithinAt.congr
    (fun w hw ↦ hiter_eq w hw) (hiter_eq u hu)

/-- **Overlap Agreement (`Lemma 5.1(a)`)**: For every positive real `x > 0`,
`PhiPlus k b x = PhiReal k b x` and `PhiMinus k b x = PhiReal k b x`! -/
theorem PhiPlus_PhiMinus_eq_PhiReal_of_pos {b : ℂ → ℂ} {C_b c_b : ℝ}
    (hb : ExpDecayKernel b C_b c_b) (k : ℂ) {x : ℝ} (hx : 0 < x) :
    PhiPlus k b (x : ℂ) = PhiReal k b (x : ℂ) ∧ PhiMinus k b (x : ℂ) = PhiReal k b (x : ℂ) := by
  let F : ℂ → ℂ := fun z ↦ b z * (1 + (x : ℂ) * z) ^ (-k)
  have hre_slit : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → 1 + (x : ℂ) * z ∈ Complex.slitPlane := fun z hz ↦ by
    rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hF_holo : DifferentiableOn ℂ F {z : ℂ | (1 / 2 : ℝ) < z.re} := by
    intro z hz
    have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hb_at := (hb.holo z hz).differentiableAt (hopen.mem_nhds hz)
    have hlin : HasDerivAt (fun w : ℂ ↦ 1 + (x : ℂ) * w) (x : ℂ) z := by
      simpa using ((hasDerivAt_id z).const_mul (x : ℂ)).const_add (1 : ℂ)
    exact (hb_at.mul (hlin.cpow_const (c := -k) (hre_slit z hz)).differentiableAt).differentiableWithinAt
  have hpow_bd : ∀ β : ℂ, ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧
      ∀ z : ℂ, 1 ≤ z.re → ‖(1 + (x : ℂ) * z) ^ (-β)‖ ≤ K * (1 + ‖z‖) ^ d := by
    intro β
    let d : ℕ := Nat.ceil (max (-β.re) 0)
    have hd_ge : -β.re ≤ (d : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
    have hC_const : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 1 ≤ z.re → ‖1 + (x : ℂ) * z‖ ^ (-β.re) ≤ K * (1 + ‖z‖) ^ d := by
      by_cases hneg : -β.re ≤ 0
      · refine ⟨1, zero_le_one, fun z hz ↦ ?_⟩
        have hge1 : 1 ≤ ‖1 + (x : ℂ) * z‖ := by
          have hre : 1 ≤ (1 + (x : ℂ) * z).re := by simp; nlinarith
          exact hre.trans (Complex.re_le_norm _)
        have h1 : ‖1 + (x : ℂ) * z‖ ^ (-β.re) ≤ (1 : ℝ) ^ (-β.re) :=
          Real.rpow_le_rpow_of_nonpos zero_lt_one hge1 hneg
        rw [Real.one_rpow] at h1
        have h2 : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
        linarith
      · push Not at hneg
        refine ⟨(1 + x) ^ (-β.re), by positivity, fun z hz ↦ ?_⟩
        have hup : ‖1 + (x : ℂ) * z‖ ≤ (1 + x) * (1 + ‖z‖) := by
          calc ‖1 + (x : ℂ) * z‖ ≤ 1 + x * ‖z‖ := by
                simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using
                  norm_add_le (1 : ℂ) ((x : ℂ) * z)
            _ ≤ (1 + x) * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
        calc ‖1 + (x : ℂ) * z‖ ^ (-β.re)
            ≤ ((1 + x) * (1 + ‖z‖)) ^ (-β.re) := Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
          _ = (1 + x) ^ (-β.re) * (1 + ‖z‖) ^ (-β.re) := Real.mul_rpow (by positivity) (by positivity)
          _ ≤ (1 + x) ^ (-β.re) * (1 + ‖z‖) ^ (d : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) hd_ge) (by positivity)
          _ = (1 + x) ^ (-β.re) * (1 + ‖z‖) ^ d := by rw [Real.rpow_natCast]
    obtain ⟨K, hK, hKbd⟩ := hC_const
    refine ⟨K * Real.exp (|(-β).im| * Real.pi), d, by positivity, fun z hz ↦ ?_⟩
    have hne := Complex.slitPlane_ne_zero (hre_slit z (by linarith))
    calc ‖(1 + (x : ℂ) * z) ^ (-β)‖
        ≤ ‖1 + (x : ℂ) * z‖ ^ (-β).re * Real.exp (|(-β).im| * Real.pi) := norm_cpow_le_rpow_mul_exp hne
      _ ≤ (K * (1 + ‖z‖) ^ d) * Real.exp (|(-β).im| * Real.pi) := by
          rw [Complex.neg_re]; exact mul_le_mul_of_nonneg_right (hKbd z hz) (Real.exp_pos _).le
      _ = K * Real.exp (|(-β).im| * Real.pi) * (1 + ‖z‖) ^ d := by ring
  obtain ⟨K₀, d₀, hK₀, hbd₀⟩ := hpow_bd k
  obtain ⟨K₁, d₁, hK₁, hbd₁⟩ := hpow_bd (k + 1)
  let M := max d₀ d₁
  let C_tot : ℝ := C_b * (K₀ + ‖k‖ * x * K₁)
  have hCb := hb.C_nonneg
  have hbdF : ∀ z : ℂ, 1 ≤ z.re → ‖F z‖ ≤ C_tot * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := fun z hz ↦ by
    dsimp [F]; rw [norm_mul]
    have hd0 : (1 + ‖z‖) ^ d₀ ≤ (1 + ‖z‖) ^ M := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (le_max_left _ _)
    have hK_le : K₀ ≤ K₀ + ‖k‖ * x * K₁ := by linarith [mul_nonneg (mul_nonneg (norm_nonneg k) hx.le) hK₁]
    calc ‖b z‖ * ‖(1 + (x : ℂ) * z) ^ (-k)‖
        ≤ (C_b * Real.exp (-c_b * z.re)) * (K₀ * (1 + ‖z‖) ^ d₀) :=
          mul_le_mul (hb.bound z hz) (hbd₀ z hz) (norm_nonneg _) (by positivity)
      _ ≤ (C_b * Real.exp (-c_b * z.re)) * ((K₀ + ‖k‖ * x * K₁) * (1 + ‖z‖) ^ M) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul hK_le hd0 (by positivity) (by positivity)) (by positivity)
      _ = C_tot * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := by dsimp [C_tot]; ring
  have hbdF' : ∀ z : ℂ, 1 ≤ z.re → ‖deriv F z‖ ≤ C_tot * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := fun z hz ↦ by
    have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz' : (1 / 2 : ℝ) < z.re := by linarith
    have hb_at := ((hb.holo z hz').differentiableAt (hopen.mem_nhds hz')).hasDerivAt
    have hlin : HasDerivAt (fun w : ℂ ↦ 1 + (x : ℂ) * w) (x : ℂ) z := by
      simpa using ((hasDerivAt_id z).const_mul (x : ℂ)).const_add (1 : ℂ)
    have hpow_hd := hlin.cpow_const (c := -k) (hre_slit z (by linarith))
    have hF_hd := hb_at.mul hpow_hd
    rw [show deriv F z = _ from hF_hd.deriv]
    have hd0 : (1 + ‖z‖) ^ d₀ ≤ (1 + ‖z‖) ^ M := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (le_max_left _ _)
    have hd1 : (1 + ‖z‖) ^ d₁ ≤ (1 + ‖z‖) ^ M := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (le_max_right _ _)
    have h1 : ‖deriv b z * (1 + (x : ℂ) * z) ^ (-k)‖ ≤ C_b * K₀ * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := by
      rw [norm_mul]
      calc ‖deriv b z‖ * ‖(1 + (x : ℂ) * z) ^ (-k)‖
          ≤ (C_b * Real.exp (-c_b * z.re)) * (K₀ * (1 + ‖z‖) ^ d₀) :=
            mul_le_mul (hb.deriv_bound z hz) (hbd₀ z hz) (norm_nonneg _) (by positivity)
        _ ≤ (C_b * Real.exp (-c_b * z.re)) * (K₀ * (1 + ‖z‖) ^ M) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd0 hK₀) (by positivity)
        _ = C_b * K₀ * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := by ring
    have h2 : ‖b z * (-k * (1 + (x : ℂ) * z) ^ (-k - 1) * (x : ℂ))‖ ≤
        C_b * (‖k‖ * x * K₁) * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := by
      rw [show -k - 1 = -(k + 1) by ring, norm_mul, norm_mul, norm_mul, norm_neg,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      calc ‖b z‖ * (‖k‖ * ‖(1 + (x : ℂ) * z) ^ (-(k + 1))‖ * x)
          ≤ (C_b * Real.exp (-c_b * z.re)) * (‖k‖ * (K₁ * (1 + ‖z‖) ^ d₁) * x) := by
            have hinner : ‖k‖ * ‖(1 + (x : ℂ) * z) ^ (-(k + 1))‖ * x ≤ ‖k‖ * (K₁ * (1 + ‖z‖) ^ d₁) * x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbd₁ z hz) (norm_nonneg k)) hx.le
            exact mul_le_mul (hb.bound z hz) hinner (by positivity) (by positivity)
        _ ≤ (C_b * Real.exp (-c_b * z.re)) * (‖k‖ * (K₁ * (1 + ‖z‖) ^ M) * x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd1 hK₁) (norm_nonneg k)) hx.le) (by positivity)
        _ = C_b * (‖k‖ * x * K₁) * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := by ring
    calc ‖deriv b z * (1 + (x : ℂ) * z) ^ (-k) + b z * (-k * (1 + (x : ℂ) * z) ^ (-k - 1) * (x : ℂ))‖
        ≤ _ := norm_add_le _ _
      _ ≤ C_b * K₀ * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) +
            C_b * (‖k‖ * x * K₁) * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := add_le_add h1 h2
      _ = C_tot * (1 + ‖z‖) ^ M * Real.exp (-c_b * z.re) := by dsimp [C_tot]; ring
  have hrot := ray_integral_eq_real hF_holo (by positivity) hb.c_pos hbdF hbdF'
  have heq_m : ∀ y : ℂ, F y = b y * (1 + (x : ℂ) * y) ^ (-k) := fun _ ↦ rfl
  simpa only [PhiPlus, PhiMinus, PhiReal, F, mul_comm (x : ℂ)] using hrot

/-- **Moment Invariance (`Lemma 5.1(d)`)**: For every `m : ℕ`,
`∫_{γ₋} y^m b(y) dy = ∫_1^∞ y^m b(y) dy = ∫_{γ₊} y^m b(y) dy`! -/
theorem moment_ray_eq_real {b : ℂ → ℂ} {C_b c_b : ℝ} (hb : ExpDecayKernel b C_b c_b) (m : ℕ) :
    (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
        ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ m * b (gammaMinus r) =
      ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ m * b (y : ℂ)) ∧
    (Complex.exp (Complex.I * (Real.pi : ℂ) / 4) *
        ∫ r in Set.Ioi (0 : ℝ), (gammaPlus r) ^ m * b (gammaPlus r) =
      ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ m * b (y : ℂ)) := by
  let F : ℂ → ℂ := fun z ↦ z ^ m * b z
  have hF_holo : DifferentiableOn ℂ F {z : ℂ | (1 / 2 : ℝ) < z.re} :=
    (differentiable_id.pow m).differentiableOn.mul hb.holo
  have hCb := hb.C_nonneg
  let C_tot : ℝ := C_b * ((m : ℝ) + 1)
  have hbdF : ∀ z : ℂ, 1 ≤ z.re → ‖F z‖ ≤ C_tot * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := fun z hz ↦ by
    dsimp [F]; rw [norm_mul, norm_pow]
    have hzm : ‖z‖ ^ m ≤ (1 + ‖z‖) ^ m := pow_le_pow_left₀ (norm_nonneg z) (by linarith) m
    have h1 : 1 ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    calc ‖z‖ ^ m * ‖b z‖ ≤ (1 + ‖z‖) ^ m * (C_b * Real.exp (-c_b * z.re)) :=
          mul_le_mul hzm (hb.bound z hz) (norm_nonneg _) (by positivity)
      _ ≤ (1 + ‖z‖) ^ m * (C_tot * Real.exp (-c_b * z.re)) := by
          gcongr; dsimp [C_tot]; nlinarith
      _ = C_tot * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := by ring
  have hbdF' : ∀ z : ℂ, 1 ≤ z.re → ‖deriv F z‖ ≤ C_tot * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := fun z hz ↦ by
    have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz' : (1 / 2 : ℝ) < z.re := by linarith
    have hb_at := ((hb.holo z hz').differentiableAt (hopen.mem_nhds hz')).hasDerivAt
    have hd := (hasDerivAt_pow m z).mul hb_at
    rw [show deriv F z = _ from hd.deriv]
    have hzm : ‖z‖ ^ m ≤ (1 + ‖z‖) ^ m := pow_le_pow_left₀ (norm_nonneg z) (by linarith) m
    have hzm1 : ‖z‖ ^ (m - 1) ≤ (1 + ‖z‖) ^ m := by
      calc ‖z‖ ^ (m - 1) ≤ (1 + ‖z‖) ^ (m - 1) := pow_le_pow_left₀ (norm_nonneg z) (by linarith) _
        _ ≤ (1 + ‖z‖) ^ m := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.sub_le m 1)
    have h1 : ‖(m : ℂ) * z ^ (m - 1) * b z‖ ≤ (C_b * (m : ℝ)) * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := by
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
      calc (m : ℝ) * ‖z‖ ^ (m - 1) * ‖b z‖
          ≤ (m : ℝ) * (1 + ‖z‖) ^ m * (C_b * Real.exp (-c_b * z.re)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hzm1 (Nat.cast_nonneg m)) (hb.bound z hz) (norm_nonneg _) (by positivity)
        _ = (C_b * (m : ℝ)) * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := by ring
    have h2 : ‖z ^ m * deriv b z‖ ≤ C_b * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := by
      rw [norm_mul, norm_pow]
      calc ‖z‖ ^ m * ‖deriv b z‖
          ≤ (1 + ‖z‖) ^ m * (C_b * Real.exp (-c_b * z.re)) :=
            mul_le_mul hzm (hb.deriv_bound z hz) (norm_nonneg _) (by positivity)
        _ = C_b * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := by ring
    calc ‖(m : ℂ) * z ^ (m - 1) * b z + z ^ m * deriv b z‖
        ≤ _ := norm_add_le _ _
      _ ≤ (C_b * (m : ℝ)) * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) +
            C_b * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := add_le_add h1 h2
      _ = C_tot * (1 + ‖z‖) ^ m * Real.exp (-c_b * z.re) := by dsimp [C_tot]; ring
  exact ray_integral_eq_real hF_holo (by positivity) hb.c_pos hbdF hbdF'

/-- Chain rule for real `j`-th derivative along `t ↦ f (-t)`:
`iteratedDeriv j (fun t : ℝ ↦ f (-(t : ℂ))) x = (-1)^j * iteratedDeriv j f (-(x : ℂ))`. -/
theorem iteratedDeriv_comp_neg_ofReal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (j : ℕ) :
    ∀ x : ℝ, (-(x : ℂ)) ∈ U →
      iteratedDeriv j (fun t : ℝ ↦ f (-(t : ℂ))) x = (-1 : ℂ) ^ j * iteratedDeriv j f (-(x : ℂ)) := by
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hopen_R : IsOpen {t : ℝ | (-(t : ℂ)) ∈ U} :=
      hU.preimage Complex.continuous_ofReal.neg
    have hev : iteratedDeriv j (fun t : ℝ ↦ f (-(t : ℂ))) =ᶠ[𝓝 x]
        fun t : ℝ ↦ (-1 : ℂ) ^ j * iteratedDeriv j f (-(t : ℂ)) := by
      filter_upwards [hopen_R.mem_nhds hx] with t ht; exact ih t ht
    rw [hev.deriv_eq]
    have hdiff_j : DifferentiableOn ℂ (iteratedDeriv j f) U :=
      differentiableOn_iteratedDeriv_open hU hf j
    have hd_C : HasDerivAt (iteratedDeriv j f) (deriv (iteratedDeriv j f) (-(x : ℂ))) (-(x : ℂ)) :=
      ((hdiff_j _ hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
    have hneg_C : HasDerivAt (fun z : ℂ ↦ iteratedDeriv j f (-z))
        (deriv (iteratedDeriv j f) (-(x : ℂ)) * (-1 : ℂ)) (x : ℂ) :=
      hd_C.comp (x : ℂ) (hasDerivAt_neg (x : ℂ))
    have hneg_R : HasDerivAt (fun t : ℝ ↦ (-1 : ℂ) ^ j * iteratedDeriv j f (-(t : ℂ)))
        ((-1 : ℂ) ^ j * (deriv (iteratedDeriv j f) (-(x : ℂ)) * (-1 : ℂ))) x :=
      (hneg_C.comp_ofReal).const_mul ((-1 : ℂ) ^ j)
    rw [hneg_R.deriv, iteratedDeriv_succ, pow_succ]; ring

/-- **Lemma 5.1(d) — Identical Asymptotics for `Y_+` and `Y_-` as `x → 0⁺`**:
Both `x ↦ iteratedDeriv j (fun t : ℝ ↦ PhiPlus k b (-t)) x` and
`x ↦ iteratedDeriv j (fun t : ℝ ↦ PhiMinus k b (-t)) x` admit Poincaré (in fact Gevrey-1)
asymptotic expansions on `(0, x₀)` with the **exact same** formal coefficients
`fun n ↦ (-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n`! -/
theorem PhiPlus_PhiMinus_neg_iteratedDeriv_hasRealAsymp
    {b : ℂ → ℂ} {C_b c_b : ℝ} (hb : ExpDecayKernel b C_b c_b)
    {x₀ : ℝ} (hx₀_pos : 0 < x₀) (hx₀ : x₀ ≤ 1 / 4) (k : ℂ) (j : ℕ) :
    HasRealAsymp x₀ (iteratedDeriv j (fun t : ℝ ↦ PhiPlus k b (-(t : ℂ))))
      (fun n ↦ (-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) ∧
    HasRealAsymp x₀ (iteratedDeriv j (fun t : ℝ ↦ PhiMinus k b (-(t : ℂ))))
      (fun n ↦ (-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) := by
  have hCb := hb.C_nonneg
  have hc' : 0 < c_b / Real.sqrt 2 := div_pos hb.c_pos (Real.sqrt_pos.mpr zero_lt_two)
  set α : ℂ := k + (j : ℂ)
  set N₀ : ℕ := max 1 (Nat.ceil (-α.re))
  have hN₀_pos : 1 ≤ N₀ := le_max_left _ _
  have hN₀_ge : -α.re ≤ (N₀ : ℝ) := (Nat.le_ceil (-α.re)).trans (Nat.cast_le.mpr (le_max_right 1 _))
  have hdom_int : ∀ d : ℕ, IntegrableOn (fun r : ℝ ↦ (1 + r) ^ d * Real.exp (-(c_b / Real.sqrt 2) * r)) (Set.Ioi 0) :=
    integrableOn_one_add_pow_mul_exp hc'
  -- Helper proving the asymptotics for either ray `γ = gammaMinus` or `γ = gammaPlus`!
  have hray_asymp : ∀ (γ : ℝ → ℂ) (ω_ang : ℂ) (f : ℝ → ℂ),
      ‖ω_ang‖ = 1 →
      (∀ r : ℝ, 0 ≤ r → 1 ≤ (γ r).re ∧ (γ r).re = 1 + r / Real.sqrt 2 ∧ ‖γ r‖ ≤ 1 + r) →
      Continuous γ →
      (∀ x ∈ Set.Ioo (0 : ℝ) x₀, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r : ℝ, 0 ≤ r →
        1 / (2 * Real.sqrt 2) ≤ ‖1 - (t : ℂ) * (x : ℂ) * γ r‖ ∧
        1 - (t : ℂ) * (x : ℂ) * γ r ∈ Complex.slitPlane) →
      (∀ m : ℕ, ω_ang * ∫ r in Set.Ioi (0 : ℝ), (γ r) ^ m * b (γ r) =
        ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ m * b (y : ℂ)) →
      (∀ x ∈ Set.Ioo (0 : ℝ) x₀,
        f x = risingFac k j * ω_ang *
          ∫ r in Set.Ioi (0 : ℝ), (γ r) ^ j * b (γ r) * (1 - (x : ℂ) * γ r) ^ (-α)) →
      HasRealAsymp x₀ f (fun n ↦ (-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) := by
    intro γ ω_ang f hω_norm hγ_prop hγ_cont hγ_lb hmom hf_eq
    have hcont_b : ContinuousOn (fun r : ℝ ↦ b (γ r)) (Set.Ioi 0) := fun r hr ↦ by
      have hre : (1 / 2 : ℝ) < (γ r).re := by linarith [(hγ_prop r (Set.mem_Ioi.mp hr).le).1]
      have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact (((hb.holo _ hre).differentiableAt (hopen.mem_nhds hre)).continuousAt.comp
        hγ_cont.continuousAt).continuousWithinAt
    have hint_m : ∀ m : ℕ, IntegrableOn (fun r : ℝ ↦ (γ r) ^ m * b (γ r)) (Set.Ioi 0) := fun m ↦ by
      refine ((hdom_int m).const_mul C_b).mono'
        (((hγ_cont.pow m).continuousOn.mul hcont_b).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have ⟨hre1, hre_eq, hgn⟩ := hγ_prop r (Set.mem_Ioi.mp hr).le
      rw [norm_mul, norm_pow]
      have hbr : ‖b (γ r)‖ ≤ C_b * Real.exp (-(c_b / Real.sqrt 2) * r) := by
        have h1 := hb.bound (γ r) hre1; rw [hre_eq] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have : -c_b * (1 + r / Real.sqrt 2) = -c_b + -(c_b / Real.sqrt 2) * r := by ring
          linarith [hb.c_pos])) hCb)
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      calc ‖γ r‖ ^ m * ‖b (γ r)‖
          ≤ (1 + r) ^ m * (C_b * Real.exp (-(c_b / Real.sqrt 2) * r)) :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hgn m) hbr (norm_nonneg _) (by positivity)
        _ = C_b * ((1 + r) ^ m * Real.exp (-(c_b / Real.sqrt 2) * r)) := by ring
    have hbig : ∀ N : ℕ, N₀ ≤ N → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Set.Ioo (0 : ℝ) x₀,
          ‖f x - ∑ n ∈ Finset.range N, ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n‖ ≤ C * x ^ N := by
      intro N hN
      have hN1 : 1 ≤ N := le_trans hN₀_pos hN
      let M_int : ℝ := ∫ r in Set.Ioi (0 : ℝ), (1 + r) ^ (N + j) * Real.exp (-(c_b / Real.sqrt 2) * r)
      have hMint_nn : 0 ≤ M_int := setIntegral_nonneg measurableSet_Ioi fun r hr ↦ by
        have hr0 : 0 ≤ r := hr.le; positivity
      let C_N : ℝ := ‖risingFac k j‖ * C_b * (2 + ‖-α‖) ^ N *
        (2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi) * M_int
      refine ⟨C_N, by positivity, fun x hx ↦ ?_⟩
      rw [hf_eq x hx]
      let rem : ℝ → ℂ := fun r ↦
        (N : ℂ) * genBinom (-α) N * (-(x : ℂ) * γ r) ^ N *
          ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 - (t : ℂ) * (x : ℂ) * γ r) ^ (-α - (N : ℂ))
      have hrem_pt : ∀ r ∈ Set.Ioi (0 : ℝ),
          (γ r) ^ j * b (γ r) * (1 - (x : ℂ) * γ r) ^ (-α) -
            ∑ n ∈ Finset.range N, genBinom (-α) n * (-(x : ℂ)) ^ n * ((γ r) ^ (n + j) * b (γ r)) =
          (γ r) ^ j * b (γ r) * rem r := by
        intro r hr
        have hty := cpow_taylor_integral_remainder α (-(x : ℂ) * γ r) N hN1 (fun t ht ↦ by
          have := (hγ_lb x hx t ht r (Set.mem_Ioi.mp hr).le).2
          convert this using 1; ring)
        have h1eq : 1 + (-(x : ℂ) * γ r) = 1 - (x : ℂ) * γ r := by ring
        rw [h1eq] at hty
        have ht_congr : ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 + (t : ℂ) * (-(x : ℂ) * γ r)) ^ (-α - (N : ℂ)) =
            ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 - (t : ℂ) * (x : ℂ) * γ r) ^ (-α - (N : ℂ)) := by
          apply intervalIntegral.integral_congr; intro t _
          dsimp only
          have : 1 + (t : ℂ) * (-(x : ℂ) * γ r) = 1 - (t : ℂ) * (x : ℂ) * γ r := by ring
          rw [this]
        rw [ht_congr] at hty
        have hsum_eq : (γ r) ^ j * b (γ r) *
            (∑ n ∈ Finset.range N, genBinom (-α) n * (-(x : ℂ) * γ r) ^ n) =
            ∑ n ∈ Finset.range N, genBinom (-α) n * (-(x : ℂ)) ^ n * ((γ r) ^ (n + j) * b (γ r)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; rw [mul_pow, pow_add]; ring
        rw [hty, mul_add, hsum_eq, add_sub_cancel_left]
      have hsum_id : ∑ n ∈ Finset.range N, ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n =
          risingFac k j * ω_ang * ∫ r in Set.Ioi (0 : ℝ),
            ∑ n ∈ Finset.range N, genBinom (-α) n * (-(x : ℂ)) ^ n * ((γ r) ^ (n + j) * b (γ r)) := by
        rw [integral_finsetSum _ (fun n _ ↦ (hint_m (n + j)).const_mul _), Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [integral_const_mul]
        have hstep : risingFac k j * ω_ang * (genBinom (-α) n * (-(x : ℂ)) ^ n *
            ∫ r in Set.Ioi (0 : ℝ), (γ r) ^ (n + j) * b (γ r)) =
            risingFac k j * genBinom (-α) n * (-(x : ℂ)) ^ n *
              (ω_ang * ∫ r in Set.Ioi (0 : ℝ), (γ r) ^ (n + j) * b (γ r)) := by ring
        rw [hstep, hmom (n + j)]
        dsimp [phiFormalCoeff, α]
        have hsign : (-1 : ℂ) ^ (n + j) * (-1 : ℂ) ^ j = (-1 : ℂ) ^ n := by
          rw [← pow_add, show n + j + j = n + 2 * j by omega, pow_add, pow_mul]; simp
        have hnegx : (-(x : ℂ)) ^ n = (-1 : ℂ) ^ n * (x : ℂ) ^ n := by rw [← mul_pow]; simp
        rw [hnegx]
        calc (-1 : ℂ) ^ (n + j) * ((-1 : ℂ) ^ j * risingFac k j * genBinom (-(k + (j : ℂ))) n *
                ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ (n + j) * b (y : ℂ)) * (x : ℂ) ^ n
            = ((-1 : ℂ) ^ (n + j) * (-1 : ℂ) ^ j) * risingFac k j * genBinom (-(k + (j : ℂ))) n *
                (x : ℂ) ^ n * ∫ y in Set.Ioi (1 : ℝ), (y : ℂ) ^ (n + j) * b (y : ℂ) := by ring
          _ = _ := by rw [hsign]; ring
      have hint_lhs : IntegrableOn (fun r : ℝ ↦ (γ r) ^ j * b (γ r) * (1 - (x : ℂ) * γ r) ^ (-α)) (Set.Ioi 0) := by
        let d_a := Nat.ceil (max (-α.re) 0)
        refine ((hdom_int (j + d_a)).const_mul
          (C_b * (1 + x) ^ max (-α.re) 0 * (2 * Real.sqrt 2) ^ max α.re 0 * Real.exp (|α.im| * Real.pi))).mono' ?_ ?_
        · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
          have hpow_c : ContinuousOn (fun r : ℝ ↦ (1 - (x : ℂ) * γ r) ^ (-α)) (Set.Ioi 0) := fun r hr ↦ by
            have hsl := (hγ_lb x hx 1 (right_mem_Icc.mpr zero_le_one) r (Set.mem_Ioi.mp hr).le).2
            simp only [Complex.ofReal_one, one_mul] at hsl
            exact (continuousAt_cpow_const_comp
              (continuousAt_const.sub (continuousAt_const.mul hγ_cont.continuousAt)) hsl).continuousWithinAt
          exact (((hγ_cont.pow j).continuousOn).mul hcont_b).mul hpow_c
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
          have ⟨hre1, hre_eq, hgn⟩ := hγ_prop r hr0
          have ⟨hng, hsl⟩ := hγ_lb x hx 1 (right_mem_Icc.mpr zero_le_one) r hr0
          simp only [Complex.ofReal_one, one_mul] at hng hsl
          have hcp := norm_cpow_le_rpow_mul_exp (z := 1 - (x : ℂ) * γ r) (w := -α) (Complex.slitPlane_ne_zero hsl)
          rw [Complex.neg_re, Complex.neg_im, abs_neg] at hcp
          have hrpow : ‖1 - (x : ℂ) * γ r‖ ^ (-α.re) ≤
              (1 + x) ^ max (-α.re) 0 * (2 * Real.sqrt 2) ^ max α.re 0 * (1 + r) ^ d_a := by
            by_cases hneg : -α.re ≤ 0
            · rw [max_eq_right hneg, max_eq_left (by linarith : 0 ≤ α.re), Real.rpow_zero, one_mul]
              have hda : d_a = 0 := by dsimp [d_a]; rw [max_eq_right hneg, Nat.ceil_zero]
              rw [hda, pow_zero, mul_one]
              have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hng hneg
              have hinv : (1 / (2 * Real.sqrt 2)) ^ (-α.re) = (2 * Real.sqrt 2) ^ α.re := by
                rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
              exact h1.trans_eq hinv
            · push Not at hneg
              rw [max_eq_left hneg.le, max_eq_right (by linarith : α.re ≤ 0), Real.rpow_zero, mul_one]
              have hup : ‖1 - (x : ℂ) * γ r‖ ≤ (1 + x) * (1 + r) := by
                calc ‖1 - (x : ℂ) * γ r‖ ≤ 1 + x * ‖γ r‖ := by
                      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] using
                        norm_sub_le (1 : ℂ) ((x : ℂ) * γ r)
                  _ ≤ (1 + x) * (1 + r) := by nlinarith [hx.1, hgn]
              have hx1_nn : 0 ≤ 1 + x := by linarith [hx.1]
              calc ‖1 - (x : ℂ) * γ r‖ ^ (-α.re)
                  ≤ ((1 + x) * (1 + r)) ^ (-α.re) := Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
                _ = (1 + x) ^ (-α.re) * (1 + r) ^ (-α.re) := Real.mul_rpow hx1_nn (by linarith)
                _ ≤ (1 + x) ^ (-α.re) * (1 + r) ^ (d_a : ℝ) :=
                    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith)
                      ((le_max_left (-α.re) 0).trans (Nat.le_ceil _))) (Real.rpow_nonneg hx1_nn _)
                _ = (1 + x) ^ (-α.re) * (1 + r) ^ d_a := by rw [Real.rpow_natCast]
          have hbr : ‖b (γ r)‖ ≤ C_b * Real.exp (-(c_b / Real.sqrt 2) * r) := by
            have h1 := hb.bound (γ r) hre1; rw [hre_eq] at h1
            exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
              have : -c_b * (1 + r / Real.sqrt 2) = -c_b + -(c_b / Real.sqrt 2) * r := by ring
              linarith [hb.c_pos])) hCb)
          rw [norm_mul, norm_mul, norm_pow]
          calc ‖γ r‖ ^ j * ‖b (γ r)‖ * ‖(1 - (x : ℂ) * γ r) ^ (-α)‖
              ≤ ((1 + r) ^ j * (C_b * Real.exp (-(c_b / Real.sqrt 2) * r))) *
                  (((1 + x) ^ max (-α.re) 0 * (2 * Real.sqrt 2) ^ max α.re 0 * (1 + r) ^ d_a) *
                    Real.exp (|α.im| * Real.pi)) :=
                mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hgn j) hbr (norm_nonneg _) (by positivity))
                  (hcp.trans (mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le)) (norm_nonneg _) (by positivity)
            _ = C_b * (1 + x) ^ max (-α.re) 0 * (2 * Real.sqrt 2) ^ max α.re 0 *
                  Real.exp (|α.im| * Real.pi) * ((1 + r) ^ (j + d_a) * Real.exp (-(c_b / Real.sqrt 2) * r)) := by
                rw [pow_add]; ring
      rw [hsum_id, ← mul_sub, ← integral_sub hint_lhs
          (integrable_finsetSum _ (fun n _ ↦ (hint_m (n + j)).const_mul _))]
      rw [setIntegral_congr_fun measurableSet_Ioi hrem_pt, norm_mul, norm_mul, hω_norm, mul_one]
      have hrem_bd : ∀ r ∈ Set.Ioi (0 : ℝ),
          ‖(γ r) ^ j * b (γ r) * rem r‖ ≤
            (C_b * (2 + ‖-α‖) ^ N * (2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) *
              Real.exp (|α.im| * Real.pi) * x ^ N) * ((1 + r) ^ (N + j) * Real.exp (-(c_b / Real.sqrt 2) * r)) := by
        intro r hr
        have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
        have ⟨hre1, hre_eq, hgn⟩ := hγ_prop r hr0
        have hint_t : ‖∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) *
            (1 - (t : ℂ) * (x : ℂ) * γ r) ^ (-α - (N : ℂ))‖ ≤
            (2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi) := by
          have hbd_t : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
              ‖((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 - (t : ℂ) * (x : ℂ) * γ r) ^ (-α - (N : ℂ))‖ ≤
                (2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi) := by
            intro t ht
            rw [Set.uIoc_of_le zero_le_one] at ht
            have ⟨hng, hsl⟩ := hγ_lb x hx t ⟨ht.1.le, ht.2⟩ r hr0
            have h1t : ‖((1 - t : ℝ) : ℂ) ^ (N - 1)‖ ≤ 1 := by
              rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
              exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
            have hcp := norm_cpow_le_rpow_mul_exp (z := 1 - (t : ℂ) * (x : ℂ) * γ r) (w := -α - (N : ℂ))
              (Complex.slitPlane_ne_zero hsl)
            have hre_w : (-α - (N : ℂ)).re = -(α.re + (N : ℝ)) := by simp; ring
            have him_w : |(-α - (N : ℂ)).im| = |α.im| := by simp
            rw [hre_w, him_w] at hcp
            have hexp_nonpos : -(α.re + (N : ℝ)) ≤ 0 := by
              have : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
              linarith
            have hrpow := (Real.rpow_le_rpow_of_nonpos (by positivity) hng hexp_nonpos).trans_eq (by
              rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv])
            rw [norm_mul]
            exact (mul_le_mul h1t (hcp.trans (mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le))
              (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
          simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd_t
        have hbr : ‖b (γ r)‖ ≤ C_b * Real.exp (-(c_b / Real.sqrt 2) * r) := by
          have h1 := hb.bound (γ r) hre1; rw [hre_eq] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            have : -c_b * (1 + r / Real.sqrt 2) = -c_b + -(c_b / Real.sqrt 2) * r := by ring
            linarith [hb.c_pos])) hCb)
        have hnorm_eq : ‖(γ r) ^ j * b (γ r) * rem r‖ =
            ‖γ r‖ ^ j * ‖b (γ r)‖ * (‖(N : ℂ) * genBinom (-α) N‖ * (x ^ N * ‖γ r‖ ^ N) *
              ‖∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 - (t : ℂ) * (x : ℂ) * γ r) ^ (-α - (N : ℂ))‖) := by
          dsimp [rem]
          simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
          ring
        have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
        have hx_pos : 0 < x := hx.1
        rw [hnorm_eq]
        have h1 : ‖γ r‖ ^ j * ‖b (γ r)‖ ≤ (1 + r) ^ j * (C_b * Real.exp (-(c_b / Real.sqrt 2) * r)) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hgn j) hbr (norm_nonneg _) (by positivity)
        have h2 : ‖(N : ℂ) * genBinom (-α) N‖ * (x ^ N * ‖γ r‖ ^ N) *
              ‖∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) ^ (N - 1) * (1 - (t : ℂ) * (x : ℂ) * γ r) ^ (-α - (N : ℂ))‖ ≤
            (2 + ‖-α‖) ^ N * (x ^ N * (1 + r) ^ N) * ((2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi)) :=
          mul_le_mul
            (mul_le_mul (norm_mul_genBinom_le (-α) N)
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hgn N) (pow_nonneg hx.1.le N))
              (by positivity) (by positivity))
            hint_t (norm_nonneg _) (by positivity)
        calc ‖γ r‖ ^ j * ‖b (γ r)‖ * _
            ≤ ((1 + r) ^ j * (C_b * Real.exp (-(c_b / Real.sqrt 2) * r))) *
                ((2 + ‖-α‖) ^ N * (x ^ N * (1 + r) ^ N) *
                  ((2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) * Real.exp (|α.im| * Real.pi))) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (C_b * (2 + ‖-α‖) ^ N * (2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) *
                Real.exp (|α.im| * Real.pi) * x ^ N) * ((1 + r) ^ (N + j) * Real.exp (-(c_b / Real.sqrt 2) * r)) := by
              rw [pow_add]; ring
      have hdom_r : IntegrableOn (fun r : ℝ ↦
          (C_b * (2 + ‖-α‖) ^ N * (2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) *
            Real.exp (|α.im| * Real.pi) * x ^ N) * ((1 + r) ^ (N + j) * Real.exp (-(c_b / Real.sqrt 2) * r))) (Set.Ioi 0) :=
        (hdom_int (N + j)).const_mul _
      have hint_rem : IntegrableOn (fun r : ℝ ↦ (γ r) ^ j * b (γ r) * rem r) (Set.Ioi 0) :=
        (hint_lhs.sub (integrable_finsetSum _ (fun n _ ↦ (hint_m (n + j)).const_mul _))).congr_fun
          hrem_pt measurableSet_Ioi
      have hbd_int := (norm_integral_le_integral_norm _).trans
        (setIntegral_mono_on hint_rem.norm hdom_r measurableSet_Ioi hrem_bd)
      rw [integral_const_mul] at hbd_int
      calc ‖risingFac k j‖ * ‖∫ r in Set.Ioi (0 : ℝ), (γ r) ^ j * b (γ r) * rem r‖
          ≤ ‖risingFac k j‖ * ((C_b * (2 + ‖-α‖) ^ N * (2 * Real.sqrt 2) ^ (α.re + (N : ℝ)) *
              Real.exp (|α.im| * Real.pi) * x ^ N) * M_int) :=
            mul_le_mul_of_nonneg_left hbd_int (norm_nonneg _)
        _ = C_N * x ^ N := by dsimp [C_N, M_int]; ring
    -- Extend from `N ≥ N₀` to all `N : ℕ`!
    intro N
    by_cases hN : N₀ ≤ N
    · exact hbig N hN
    · push Not at hN
      obtain ⟨C₀, hC₀, hbd₀⟩ := hbig N₀ le_rfl
      let C' : ℝ := C₀ * x₀ ^ (N₀ - N) +
        ∑ n ∈ Finset.Ico N N₀, ‖(-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n‖ * x₀ ^ (n - N)
      refine ⟨C', by positivity, fun x hx ↦ ?_⟩
      have hsplit : f x - ∑ n ∈ Finset.range N, ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n =
          (f x - ∑ n ∈ Finset.range N₀, ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n) +
            ∑ n ∈ Finset.Ico N N₀, ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n := by
        have := Finset.sum_range_add_sum_Ico
          (fun n ↦ ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n) hN.le
        linear_combination -this
      rw [hsplit]
      have h1 : ‖f x - ∑ n ∈ Finset.range N₀, ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n‖ ≤
          C₀ * x₀ ^ (N₀ - N) * x ^ N := by
        calc _ ≤ C₀ * x ^ N₀ := hbd₀ x hx
          _ = C₀ * (x ^ (N₀ - N) * x ^ N) := by rw [← pow_add, Nat.sub_add_cancel hN.le]
          _ ≤ C₀ * (x₀ ^ (N₀ - N) * x ^ N) := by
              have hx_nn : 0 ≤ x := hx.1.le
              have hp : x ^ (N₀ - N) ≤ x₀ ^ (N₀ - N) := pow_le_pow_left₀ hx_nn hx.2.le _
              gcongr
          _ = C₀ * x₀ ^ (N₀ - N) * x ^ N := by ring
      have h2 : ‖∑ n ∈ Finset.Ico N N₀, ((-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n) * (x : ℂ) ^ n‖ ≤
          (∑ n ∈ Finset.Ico N N₀, ‖(-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n‖ * x₀ ^ (n - N)) * x ^ N := by
        rw [Finset.sum_mul]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
        have hNn : N ≤ n := (Finset.mem_Ico.mp hn).1
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
        have hp : x ^ (n - N) ≤ x₀ ^ (n - N) := pow_le_pow_left₀ hx.1.le hx.2.le _
        calc ‖(-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n‖ * x ^ n
            = ‖(-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n‖ * (x ^ (n - N) * x ^ N) := by
              rw [← pow_add, Nat.sub_add_cancel hNn]
          _ ≤ ‖(-1 : ℂ) ^ (n + j) * phiFormalCoeff k b j n‖ * (x₀ ^ (n - N) * x ^ N) := by
              have hx_nn : 0 ≤ x := hx.1.le; gcongr
          _ = _ := by ring
      calc ‖(f x - ∑ n ∈ Finset.range N₀, _) + ∑ n ∈ Finset.Ico N N₀, _‖
          ≤ _ := norm_add_le _ _
        _ ≤ C' * x ^ N := by dsimp [C']; linarith
  -- Apply `hray_asymp` to `PhiPlus` and `PhiMinus`!
  have hP0 := (PhiPlus_iteratedDeriv hb hx₀ k 0).1
  have hM0 := (PhiMinus_iteratedDeriv hb hx₀ k 0).1
  have hP0' : DifferentiableOn ℂ (PhiPlus k b) (UPlus x₀) := by simpa [iteratedDeriv_zero] using hP0
  have hM0' : DifferentiableOn ℂ (PhiMinus k b) (UMinus x₀) := by simpa [iteratedDeriv_zero] using hM0
  constructor
  · apply hray_asymp gammaMinus (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
    · rw [show -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    · intro r hr
      refine ⟨by rw [gammaMinus_re]; linarith [div_nonneg hr (Real.sqrt_nonneg 2)], gammaMinus_re r, ?_⟩
      dsimp [gammaMinus]
      calc ‖1 + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]
    · exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    · intro x hx t ht r hr
      have h := one_sub_txy_norm_ge_gammaMinus ht.1 ht.2 hx.1.le (hx.2.le.trans (by linarith)) hr
      exact ⟨h.1.trans h.2.1, h.2.2⟩
    · exact fun m ↦ (moment_ray_eq_real hb m).1
    · intro x hx
      rw [iteratedDeriv_comp_neg_ofReal (isOpen_UPlus x₀) hP0' j x (neg_ofReal_mem_UPlus hx.1 hx.2),
          (PhiPlus_iteratedDeriv hb hx₀ k j).2 (-(x : ℂ)) (neg_ofReal_mem_UPlus hx.1 hx.2)]
      have hneg1 : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by rw [← mul_pow]; simp
      have harg : ∀ r, 1 + -(x : ℂ) * gammaMinus r = 1 - (x : ℂ) * gammaMinus r := fun r ↦ by ring
      simp_rw [harg]
      calc (-1 : ℂ) ^ j * ((-1 : ℂ) ^ j * risingFac k j * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
              ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ j * b (gammaMinus r) * (1 - (x : ℂ) * gammaMinus r) ^ (-α))
          = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * (risingFac k j * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
              ∫ r in Set.Ioi (0 : ℝ), (gammaMinus r) ^ j * b (gammaMinus r) * (1 - (x : ℂ) * gammaMinus r) ^ (-α)) := by ring
        _ = _ := by rw [hneg1, one_mul]
  · apply hray_asymp gammaPlus (Complex.exp (Complex.I * (Real.pi : ℂ) / 4))
    · rw [show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    · intro r hr
      refine ⟨by rw [gammaPlus_re]; linarith [div_nonneg hr (Real.sqrt_nonneg 2)], gammaPlus_re r, ?_⟩
      dsimp [gammaPlus]
      calc ‖1 + (r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]
    · exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    · intro x hx t ht r hr
      have h := one_sub_txy_norm_ge_gammaPlus ht.1 ht.2 hx.1.le (hx.2.le.trans (by linarith)) hr
      exact ⟨h.1.trans h.2.1, h.2.2⟩
    · exact fun m ↦ (moment_ray_eq_real hb m).2
    · intro x hx
      rw [iteratedDeriv_comp_neg_ofReal (isOpen_UMinus x₀) hM0' j x (neg_ofReal_mem_UMinus hx.1 hx.2),
          (PhiMinus_iteratedDeriv hb hx₀ k j).2 (-(x : ℂ)) (neg_ofReal_mem_UMinus hx.1 hx.2)]
      have hneg1 : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by rw [← mul_pow]; simp
      have harg : ∀ r, 1 + -(x : ℂ) * gammaPlus r = 1 - (x : ℂ) * gammaPlus r := fun r ↦ by ring
      simp_rw [harg]
      calc (-1 : ℂ) ^ j * ((-1 : ℂ) ^ j * risingFac k j * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) *
              ∫ r in Set.Ioi (0 : ℝ), (gammaPlus r) ^ j * b (gammaPlus r) * (1 - (x : ℂ) * gammaPlus r) ^ (-α))
          = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * (risingFac k j * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) *
              ∫ r in Set.Ioi (0 : ℝ), (gammaPlus r) ^ j * b (gammaPlus r) * (1 - (x : ℂ) * gammaPlus r) ^ (-α)) := by ring
        _ = _ := by rw [hneg1, one_mul]

/-! ### 4. Lemma 5.1(b): Simultaneous Lateral Annihilation on Both Sides of the Cut -/

/-- **Lemma 5.1(b) — Simultaneous Lateral Annihilation**:
If `F` is holomorphic on `slitDisk ρ₀` with zero uniform Gevrey-1 expansion on `sector34 x₀`
(`0 < x₀ < ρ₀`), and `F₊` (holomorphic on `UPlus x₀`) and `F₋` (holomorphic on `UMinus x₀`)
both agree with `F` on `(0, x₀)`, then `F₊ ≡ 0` on `UPlus x₀` AND `F₋ ≡ 0` on `UMinus x₀` —
in particular **`F₊(-x) = 0` AND `F₋(-x) = 0` for EVERY `x ∈ (0, x₀)`**! -/
theorem lateral_simultaneous_annihilation {x₀ ρ₀ : ℝ} (hx₀ : 0 < x₀) (hxρ : x₀ < ρ₀)
    {F Fp Fm : ℂ → ℂ}
    (hF_diff : DifferentiableOn ℂ F (slitDisk ρ₀))
    (hF_gev : HasGevrey1Asymp (sector34 x₀) F (fun _ ↦ 0))
    (hFp_diff : DifferentiableOn ℂ Fp (UPlus x₀))
    (hFm_diff : DifferentiableOn ℂ Fm (UMinus x₀))
    (hFp_eq : ∀ x ∈ Set.Ioo (0 : ℝ) x₀, Fp (x : ℂ) = F (x : ℂ))
    (hFm_eq : ∀ x ∈ Set.Ioo (0 : ℝ) x₀, Fm (x : ℂ) = F (x : ℂ)) :
    (∀ u ∈ UPlus x₀, Fp u = 0) ∧
    (∀ u ∈ UMinus x₀, Fm u = 0) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) x₀, Fp (-(x : ℂ)) = 0 ∧ Fm (-(x : ℂ)) = 0) := by
  have hF0 : ∀ u ∈ slitDisk ρ₀, F u = 0 :=
    watson_of_gevrey1_zero hx₀ hxρ hF_diff hF_gev
  have hreal0 : ∀ x ∈ Set.Ioo (0 : ℝ) x₀, F (x : ℂ) = 0 := fun x hx ↦ by
    apply hF0 (x : ℂ)
    refine ⟨?_, ?_, Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hx.1))⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]; exact hx.1
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]; exact lt_trans hx.2 hxρ
  let u_pt : ℂ := ((x₀ / 2 : ℝ) : ℂ)
  have hfreq_of : ∀ (G : ℂ → ℂ), (∀ x ∈ Set.Ioo (0 : ℝ) x₀, G (x : ℂ) = 0) →
      ∃ᶠ u in 𝓝[≠] u_pt, G u = 0 := by
    intro G hG
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hVopen, huV, hVsub⟩ := hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hVopen u_pt huV
    let δ : ℝ := min (ε / 2) (x₀ / 4)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    let x' : ℝ := x₀ / 2 + δ
    have hx'ne : (x' : ℂ) ≠ u_pt := fun h0 ↦ by
      have := Complex.ofReal_injective h0; dsimp [x'] at this; linarith
    have hx'ball : (x' : ℂ) ∈ Metric.ball u_pt ε := by
      rw [Metric.mem_ball, Complex.dist_eq, show (x' : ℂ) - u_pt = (δ : ℂ) by
        dsimp [x', u_pt]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact ⟨(x' : ℂ), hVsub ⟨hball hx'ball, hx'ne⟩,
      hG x' ⟨by dsimp [x']; linarith, by dsimp [x']; have := min_le_right (ε / 2) (x₀ / 4); linarith⟩⟩
  have hFp0 : ∀ u ∈ UPlus x₀, Fp u = 0 :=
    (hFp_diff.analyticOnNhd (isOpen_UPlus x₀)).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_UPlus x₀) (ofReal_mem_UPlus (by linarith) (by linarith))
      (hfreq_of Fp fun x hx ↦ (hFp_eq x hx).trans (hreal0 x hx))
  have hFm0 : ∀ u ∈ UMinus x₀, Fm u = 0 :=
    (hFm_diff.analyticOnNhd (isOpen_UMinus x₀)).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_UMinus x₀) (ofReal_mem_UMinus (by linarith) (by linarith))
      (hfreq_of Fm fun x hx ↦ (hFm_eq x hx).trans (hreal0 x hx))
  exact ⟨hFp0, hFm0, fun x hx ↦
    ⟨hFp0 (-(x : ℂ)) (neg_ofReal_mem_UPlus hx.1 hx.2),
     hFm0 (-(x : ℂ)) (neg_ofReal_mem_UMinus hx.1 hx.2)⟩⟩

/-! ### 5. Lemma 5.2: Exact Hankel Keyhole Jump & Termwise `x`-Differentiation -/

/-- For every non-Bol weight `k ∈ {1} ∪ (1/2 + ℤ)`, `1 / Γ(k) ≠ 0`! -/
theorem one_div_Gamma_ne_zero_nonBol {k : ℂ}
    (hk : k = 1 ∨ ∃ n : ℤ, k = (n : ℂ) + 1 / 2) :
    (Complex.Gamma k)⁻¹ ≠ 0 := by
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero
  intro m hkm
  rcases hk with rfl | ⟨n, rfl⟩
  · have hre := congrArg Complex.re hkm
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  · have hre := congrArg Complex.re hkm
    simp only [Complex.add_re, Complex.intCast_re, Complex.one_re, Complex.div_ofNat_re,
      Complex.neg_re, Complex.natCast_re] at hre
    have h2 : (2 : ℝ) * (n : ℝ) + 1 = -(2 : ℝ) * (m : ℝ) := by linarith
    have h2Z : 2 * n + 1 = -(2 * (m : ℤ)) := by exact_mod_cast h2
    omega

/-- `k ↦ (Complex.Gamma k)⁻¹` is an **entire** function on `ℂ`! -/
theorem differentiable_inv_Gamma : Differentiable ℂ (fun k : ℂ ↦ (Complex.Gamma k)⁻¹) := by
  intro k
  by_cases hpole : ∃ m : ℕ, k = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hpole
    let g : ℂ → ℂ := fun z ↦ Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)
    have h1sub_ne : ∀ n : ℕ, (1 : ℂ) - (-(m : ℂ)) ≠ -(n : ℂ) := fun n h ↦ by
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
    have hg_diff : DifferentiableAt ℂ g (-(m : ℂ)) := by
      have hG := (Complex.differentiableAt_Gamma _ h1sub_ne).comp (-(m : ℂ))
        ((differentiableAt_id (x := -(m : ℂ))).const_sub (1 : ℂ))
      have hsin := ((differentiableAt_id (x := -(m : ℂ))).const_mul (Real.pi : ℂ)).csin
      exact (hG.mul hsin).div_const (Real.pi : ℂ)
    have hev : (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) =ᶠ[𝓝 (-(m : ℂ))] g := by
      filter_upwards [Metric.ball_mem_nhds (-(m : ℂ)) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
      have hdist : ‖z - (-(m : ℂ))‖ < 1 / 2 := by simpa [Metric.mem_ball, Complex.dist_eq] using hz
      by_cases hzm : z = -(m : ℂ)
      · subst hzm
        dsimp [g]
        rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
        have hsin0 : Complex.sin ((Real.pi : ℂ) * -(m : ℂ)) = 0 := by
          rw [mul_neg, Complex.sin_neg, mul_comm, Complex.sin_nat_mul_pi, neg_zero]
        rw [hsin0, mul_zero, zero_div]
      · have hnot_int : ∀ n : ℤ, z ≠ (n : ℂ) := by
          intro n hzn
          subst hzn
          have hneZ : n ≠ -(m : ℤ) := fun h ↦ hzm (by exact_mod_cast h)
          have habs : (1 : ℝ) ≤ |(n : ℝ) + (m : ℝ)| := by
            have h1 : (1 : ℤ) ≤ |n + (m : ℤ)| := Int.one_le_abs (by omega)
            exact_mod_cast h1
          have hnorm : ‖(n : ℂ) - (-(m : ℂ))‖ = |(n : ℝ) + (m : ℝ)| := by
            rw [sub_neg_eq_add, show (n : ℂ) + (m : ℂ) = (((n : ℝ) + (m : ℝ) : ℝ) : ℂ) by push_cast; rfl,
                Complex.norm_real, Real.norm_eq_abs]
          linarith
        have hG_ne : Complex.Gamma z ≠ 0 :=
          Complex.Gamma_ne_zero fun n h ↦ hnot_int (-(n : ℤ)) (by simpa using h)
        have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
          intro h0
          rw [Complex.sin_eq_zero_iff] at h0
          obtain ⟨n, hn⟩ := h0
          have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
          exact hnot_int n (mul_left_cancel₀ hpi_ne (by linear_combination hn))
        have href := Complex.Gamma_mul_Gamma_one_sub z
        have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        dsimp [g]
        have hmul : Complex.Gamma z * (Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) = 1 := by
          calc Complex.Gamma z * (Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ))
              = (Complex.Gamma z * Complex.Gamma (1 - z)) * (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) := by ring
            _ = ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z)) * (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) := by
                rw [href]
            _ = 1 := by field_simp [hpi_ne, hsin_ne]
        exact eq_inv_of_mul_eq_one_right hmul |>.symm
    exact hg_diff.congr_of_eventuallyEq hev
  · push Not at hpole
    exact (Complex.differentiableAt_Gamma k hpole).inv (Complex.Gamma_ne_zero hpole)

/-- Helper: for `0 < z.im`, `Complex.log z = Complex.log (-I * z) + (π / 2) * I`! -/
private lemma log_eq_log_neg_I_mul_add {z : ℂ} (hz : 0 < z.im) :
    Complex.log z = Complex.log (-Complex.I * z) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have hre : 0 < (-Complex.I * z).re := by simp [hz]
  have hne : -Complex.I * z ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h; simp at this; linarith
  have harg_lt : |(-Complex.I * z).arg| < Real.pi / 2 := by
    have hcos : 0 < Real.cos (-Complex.I * z).arg := by
      rw [Complex.cos_arg hne]; exact div_pos hre (norm_pos_iff.mpr hne)
    rw [← Real.cos_abs] at hcos
    by_contra hge; push Not at hge
    have hle := Real.cos_nonpos_of_pi_div_two_le_of_le hge
      ((abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩).trans (by linarith [Real.pi_pos]))
    linarith
  have habs := abs_lt.mp harg_lt
  have hexp : Complex.exp (Complex.log (-Complex.I * z) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = z := by
    rw [Complex.exp_add, Complex.exp_log hne]
    push_cast
    rw [Complex.exp_pi_div_two_mul_I]
    ring_nf; simp
  have him : (Complex.log (-Complex.I * z) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im =
      (-Complex.I * z).arg + Real.pi / 2 := by
    simp [Complex.log_im]
  conv_lhs => rw [← hexp]
  rw [Complex.log_exp]
  · rw [him]; linarith
  · rw [him]; linarith

private lemma hankel_single_mode_entire {ω x : ℝ} (hω : 0 < ω) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    Differentiable ℂ (fun s : ℂ ↦
      PhiPlus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) -
        PhiMinus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ))) := by
  let J : ℂ → ℂ := fun s ↦
    PhiPlus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) -
      PhiMinus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ))
  change Differentiable ℂ J
  have hray_entire : ∀ (γ : ℝ → ℂ),
      Continuous γ →
      (∀ r : ℝ, 0 ≤ r → (γ r).re = 1 + r / Real.sqrt 2 ∧ ‖γ r‖ ≤ 1 + r) →
      (∀ r : ℝ, 0 ≤ r → 1 / (2 * Real.sqrt 2) ≤ ‖1 - (x : ℂ) * γ r‖ ∧
        1 - (x : ℂ) * γ r ∈ Complex.slitPlane) →
      Differentiable ℂ (fun s : ℂ ↦ ∫ r in Set.Ioi (0 : ℝ),
        Complex.exp (-(ω : ℂ) * γ r) * (1 - (x : ℂ) * γ r) ^ (-s)) := by
    intro γ hγ_cont hγ_prop hγ_lb s₀
    let F : ℂ → ℝ → ℂ := fun s r ↦ Complex.exp (-(ω : ℂ) * γ r) * (1 - (x : ℂ) * γ r) ^ (-s)
    let F' : ℂ → ℝ → ℂ := fun s r ↦
      Complex.exp (-(ω : ℂ) * γ r) * ((1 - (x : ℂ) * γ r) ^ (-s) * (-Complex.log (1 - (x : ℂ) * γ r)))
    have hω' : 0 < ω / Real.sqrt 2 := div_pos hω (Real.sqrt_pos.mpr zero_lt_two)
    have hdom_int : ∀ d : ℕ, IntegrableOn (fun r : ℝ ↦ (1 + r) ^ d * Real.exp (-(ω / Real.sqrt 2) * r)) (Set.Ioi 0) :=
      integrableOn_one_add_pow_mul_exp hω'
    have hmeas_F : ∀ s : ℂ, AEStronglyMeasurable (F s) (volume.restrict (Set.Ioi 0)) := fun s ↦ by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro r hr
      have hsl := (hγ_lb r (Set.mem_Ioi.mp hr).le).2
      have h1 : ContinuousAt (fun t : ℝ ↦ Complex.exp (-(ω : ℂ) * γ t)) r :=
        Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hγ_cont.continuousAt)
      have h2 : ContinuousAt (fun t : ℝ ↦ (1 - (x : ℂ) * γ t) ^ (-s)) r :=
        continuousAt_cpow_const_comp (continuousAt_const.sub (continuousAt_const.mul hγ_cont.continuousAt)) hsl
      exact (h1.mul h2).continuousWithinAt
    have hmeas_F' : AEStronglyMeasurable (F' s₀) (volume.restrict (Set.Ioi 0)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro r hr
      have hsl := (hγ_lb r (Set.mem_Ioi.mp hr).le).2
      have h1 : ContinuousAt (fun t : ℝ ↦ Complex.exp (-(ω : ℂ) * γ t)) r :=
        Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hγ_cont.continuousAt)
      have h2 : ContinuousAt (fun t : ℝ ↦ (1 - (x : ℂ) * γ t) ^ (-s₀)) r :=
        continuousAt_cpow_const_comp (continuousAt_const.sub (continuousAt_const.mul hγ_cont.continuousAt)) hsl
      have h3 : ContinuousAt (fun t : ℝ ↦ -Complex.log (1 - (x : ℂ) * γ t)) r :=
        (ContinuousAt.comp (f := fun t : ℝ ↦ 1 - (x : ℂ) * γ t)
          (Complex.hasDerivAt_log hsl).continuousAt
          (continuousAt_const.sub (continuousAt_const.mul hγ_cont.continuousAt))).neg
      exact (h1.mul (h2.mul h3)).continuousWithinAt
    let K_re : ℕ := Nat.ceil (‖s₀‖ + 1)
    have hK_re : ∀ s ∈ Metric.ball s₀ 1, |s.re| ≤ (K_re : ℝ) ∧ |s.im| ≤ ‖s₀‖ + 1 := fun s hs ↦ by
      have hsn : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have hd : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, Complex.dist_eq] using hs
        have := norm_sub_norm_le s s₀; linarith
      exact ⟨(Complex.abs_re_le_norm s).trans (hsn.trans (Nat.le_ceil _)),
             (Complex.abs_im_le_norm s).trans hsn⟩
    have hpow_unif : ∀ s ∈ Metric.ball s₀ 1, ∀ r : ℝ, 0 ≤ r →
        ‖(1 - (x : ℂ) * γ r) ^ (-s)‖ ≤
          ((2 * Real.sqrt 2) ^ K_re * 2 ^ K_re * Real.exp ((‖s₀‖ + 1) * Real.pi)) * (1 + r) ^ K_re := by
      intro s hs r hr
      have ⟨hng, hsl⟩ := hγ_lb r hr
      have ⟨_, hgn⟩ := hγ_prop r hr
      have ⟨hre_le, him_le⟩ := hK_re s hs
      have hcp := norm_cpow_le_rpow_mul_exp (z := 1 - (x : ℂ) * γ r) (w := -s) (Complex.slitPlane_ne_zero hsl)
      rw [Complex.neg_re, Complex.neg_im, abs_neg] at hcp
      have hup : ‖1 - (x : ℂ) * γ r‖ ≤ 2 * (1 + r) := by
        calc ‖1 - (x : ℂ) * γ r‖ ≤ 1 + x * ‖γ r‖ := by
              simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] using
                norm_sub_le (1 : ℂ) ((x : ℂ) * γ r)
          _ ≤ 1 + (1 / 2) * (1 + r) := by nlinarith [hx0, hx1, hgn]
          _ ≤ 2 * (1 + r) := by linarith
      have hrpow : ‖1 - (x : ℂ) * γ r‖ ^ (-s.re) ≤ (2 * Real.sqrt 2) ^ K_re * (2 * (1 + r)) ^ K_re := by
        by_cases hneg : -s.re ≤ 0
        · have h1 : ‖1 - (x : ℂ) * γ r‖ ^ (-s.re) ≤ (2 * Real.sqrt 2) ^ s.re :=
            (Real.rpow_le_rpow_of_nonpos (by positivity) hng hneg).trans_eq (by
              rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv])
          have h2 : (2 * Real.sqrt 2) ^ s.re ≤ (2 * Real.sqrt 2) ^ (K_re : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by
              have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
              linarith) ((le_abs_self s.re).trans hre_le)
          rw [Real.rpow_natCast] at h2
          have h3 : (1 : ℝ) ≤ (2 * (1 + r)) ^ K_re := one_le_pow₀ (by linarith)
          nlinarith [h1, h2, show (0 : ℝ) ≤ (2 * Real.sqrt 2) ^ K_re by positivity]
        · push Not at hneg
          have h1 := Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
          have h2 : (2 * (1 + r)) ^ (-s.re) ≤ (2 * (1 + r)) ^ (K_re : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) ((neg_le_abs s.re).trans hre_le)
          rw [Real.rpow_natCast] at h2
          have h3 : (1 : ℝ) ≤ (2 * Real.sqrt 2) ^ K_re := one_le_pow₀ (by
            have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
            linarith)
          nlinarith [h1, h2, show (0 : ℝ) ≤ (2 * (1 + r)) ^ K_re by positivity]
      calc ‖(1 - (x : ℂ) * γ r) ^ (-s)‖
          ≤ ((2 * Real.sqrt 2) ^ K_re * (2 * (1 + r)) ^ K_re) * Real.exp ((‖s₀‖ + 1) * Real.pi) :=
            hcp.trans (mul_le_mul hrpow (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right him_le Real.pi_pos.le))
              (Real.exp_pos _).le (by positivity))
        _ = ((2 * Real.sqrt 2) ^ K_re * 2 ^ K_re * Real.exp ((‖s₀‖ + 1) * Real.pi)) * (1 + r) ^ K_re := by
            rw [mul_pow 2 (1 + r) K_re]; ring
    have hlog_bd : ∀ r : ℝ, 0 ≤ r →
        ‖Complex.log (1 - (x : ℂ) * γ r)‖ ≤ (Real.log (2 * Real.sqrt 2) + 2 + Real.pi) * (1 + r) := by
      intro r hr
      have ⟨hng, hsl⟩ := hγ_lb r hr
      have ⟨_, hgn⟩ := hγ_prop r hr
      have hup : ‖1 - (x : ℂ) * γ r‖ ≤ 2 * (1 + r) := by
        calc ‖1 - (x : ℂ) * γ r‖ ≤ 1 + x * ‖γ r‖ := by
              simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] using
                norm_sub_le (1 : ℂ) ((x : ℂ) * γ r)
          _ ≤ 2 * (1 + r) := by nlinarith [hx0, hx1, hgn]
      have hre_abs : |Real.log ‖1 - (x : ℂ) * γ r‖| ≤ Real.log (2 * Real.sqrt 2) + 2 * (1 + r) := by
        rw [abs_le]; constructor
        · have h1 := Real.log_le_log (by positivity) hng
          rw [one_div, Real.log_inv] at h1
          linarith
        · have h1 := Real.log_le_log (lt_of_lt_of_le (by positivity) hng) hup
          have h2 := Real.log_le_self (show (0 : ℝ) ≤ 2 * (1 + r) by positivity)
          have h3 : 0 ≤ Real.log (2 * Real.sqrt 2) := Real.log_nonneg (by
            have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
            linarith)
          linarith
      have hnorm_log : ‖Complex.log (1 - (x : ℂ) * γ r)‖ ≤
          |Real.log ‖1 - (x : ℂ) * γ r‖| + Real.pi := by
        have h1 : ‖Complex.log (1 - (x : ℂ) * γ r)‖ ≤
            |(Complex.log (1 - (x : ℂ) * γ r)).re| + |(Complex.log (1 - (x : ℂ) * γ r)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h1
        have harg : |(1 - (x : ℂ) * γ r).arg| ≤ Real.pi :=
          abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
        linarith
      have hlog_nn : 0 ≤ Real.log (2 * Real.sqrt 2) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        linarith)
      nlinarith [Real.pi_pos]
    let A_c : ℝ := (2 * Real.sqrt 2) ^ K_re * 2 ^ K_re * Real.exp ((‖s₀‖ + 1) * Real.pi)
    let B_c : ℝ := Real.log (2 * Real.sqrt 2) + 2 + Real.pi
    have hF_int : Integrable (F s₀) (volume.restrict (Set.Ioi 0)) := by
      refine ((hdom_int K_re).const_mul A_c).mono' (hmeas_F s₀) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      have hre := (hγ_prop r hr0).1
      dsimp [F]; rw [norm_mul, Complex.norm_exp]
      have hexp_le : Real.exp (-(ω : ℂ) * γ r).re ≤ Real.exp (-(ω / Real.sqrt 2) * r) := by
        apply Real.exp_le_exp.mpr
        have : (-(ω : ℂ) * γ r).re = -ω * (1 + r / Real.sqrt 2) := by
          simp [Complex.mul_re, hre]
        rw [this]; linarith [show -ω * (1 + r / Real.sqrt 2) = -ω + -(ω / Real.sqrt 2) * r by ring]
      calc Real.exp (-(ω : ℂ) * γ r).re * ‖(1 - (x : ℂ) * γ r) ^ (-s₀)‖
          ≤ Real.exp (-(ω / Real.sqrt 2) * r) * (A_c * (1 + r) ^ K_re) :=
            mul_le_mul hexp_le (hpow_unif s₀ (Metric.mem_ball_self zero_lt_one) r hr0) (norm_nonneg _) (Real.exp_pos _).le
        _ = A_c * ((1 + r) ^ K_re * Real.exp (-(ω / Real.sqrt 2) * r)) := by ring
    let bound : ℝ → ℝ := fun r ↦ (A_c * B_c) * ((1 + r) ^ (K_re + 1) * Real.exp (-(ω / Real.sqrt 2) * r))
    have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) := (hdom_int (K_re + 1)).const_mul _
    have hbound_ae : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), ∀ s ∈ Metric.ball s₀ 1, ‖F' s r‖ ≤ bound r := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr s hs
      have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
      have hre := (hγ_prop r hr0).1
      dsimp [F', bound]; rw [norm_mul, Complex.norm_exp, norm_mul, norm_neg]
      have hexp_le : Real.exp (-(ω : ℂ) * γ r).re ≤ Real.exp (-(ω / Real.sqrt 2) * r) := by
        apply Real.exp_le_exp.mpr
        have : (-(ω : ℂ) * γ r).re = -ω * (1 + r / Real.sqrt 2) := by simp [Complex.mul_re, hre]
        rw [this]; linarith [show -ω * (1 + r / Real.sqrt 2) = -ω + -(ω / Real.sqrt 2) * r by ring]
      have hmul_bd : ‖(1 - (x : ℂ) * γ r) ^ (-s)‖ * ‖Complex.log (1 - (x : ℂ) * γ r)‖ ≤
          (A_c * (1 + r) ^ K_re) * (B_c * (1 + r)) :=
        mul_le_mul (hpow_unif s hs r hr0) (hlog_bd r hr0) (norm_nonneg _) (by positivity)
      calc Real.exp (-(ω : ℂ) * γ r).re * (‖(1 - (x : ℂ) * γ r) ^ (-s)‖ * ‖Complex.log (1 - (x : ℂ) * γ r)‖)
          ≤ Real.exp (-(ω / Real.sqrt 2) * r) * ((A_c * (1 + r) ^ K_re) * (B_c * (1 + r))) :=
            mul_le_mul hexp_le hmul_bd (by positivity) (Real.exp_pos _).le
        _ = (A_c * B_c) * ((1 + r) ^ (K_re + 1) * Real.exp (-(ω / Real.sqrt 2) * r)) := by
            rw [pow_succ]; ring
    have hderiv_ae : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), ∀ s ∈ Metric.ball s₀ 1,
        HasDerivAt (fun w ↦ F w r) (F' s r) s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr s _
      have hsl := (hγ_lb r (Set.mem_Ioi.mp hr).le).2
      have h1 : HasDerivAt (fun w : ℂ ↦ (1 - (x : ℂ) * γ r) ^ (-w))
          ((1 - (x : ℂ) * γ r) ^ (-s) * Complex.log (1 - (x : ℂ) * γ r) * (-1 : ℂ)) s := by
        have hcp := (hasDerivAt_const s (1 - (x : ℂ) * γ r)).cpow (hasDerivAt_neg s)
          (Complex.mem_slitPlane_iff.mp hsl)
        simpa using hcp
      have h2 := h1.const_mul (Complex.exp (-(ω : ℂ) * γ r))
      convert h2 using 1; dsimp [F']; ring
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ zero_lt_one)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds s₀ zero_lt_one) fun s _ ↦ hmeas_F s)
      hF_int hmeas_F' hbound_ae hbound_int hderiv_ae).2.differentiableAt
  have h1 := hray_entire gammaMinus
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun r hr ↦ ⟨gammaMinus_re r, by
      dsimp [gammaMinus]
      calc ‖1 + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]⟩)
    (fun r hr ↦ by
      have h := one_sub_txy_norm_ge_gammaMinus zero_le_one le_rfl hx0.le hx1 hr
      simp only [Complex.ofReal_one, one_mul] at h
      exact ⟨h.1.trans h.2.1, h.2.2⟩)
  have h2 := hray_entire gammaPlus
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun r hr ↦ ⟨gammaPlus_re r, by
      dsimp [gammaPlus]
      calc ‖1 + (r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]⟩)
    (fun r hr ↦ by
      have h := one_sub_txy_norm_ge_gammaPlus zero_le_one le_rfl hx0.le hx1 hr
      simp only [Complex.ofReal_one, one_mul] at h
      exact ⟨h.1.trans h.2.1, h.2.2⟩)
  have hJeq : J = fun s ↦
      Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) *
        (∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(ω : ℂ) * gammaMinus r) * (1 - (x : ℂ) * gammaMinus r) ^ (-s)) -
      Complex.exp (Complex.I * (Real.pi : ℂ) / 4) *
        (∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(ω : ℂ) * gammaPlus r) * (1 - (x : ℂ) * gammaPlus r) ^ (-s)) := by
    ext s; dsimp [J, PhiPlus, PhiMinus]
    congr 1 <;> (congr 1; apply setIntegral_congr_fun measurableSet_Ioi; intro r _; simp [sub_eq_add_neg])
  rw [hJeq]
  exact (h1.const_mul _).sub (h2.const_mul _)

private lemma hankel_single_mode_jump_real {ω x κ : ℝ} (hω : 0 < ω) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    PhiPlus (κ : ℂ) (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) -
      PhiMinus (κ : ℂ) (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) =
    -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (κ : ℂ)) *
      (x : ℂ) ^ (-(κ : ℂ)) * (ω : ℂ) ^ ((κ : ℂ) - 1) * Complex.exp (-(ω : ℂ) / (x : ℂ)) := by
  let J : ℂ → ℂ := fun s ↦
    PhiPlus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) -
      PhiMinus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ))
  let R : ℂ → ℂ := fun s ↦
    -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma s) *
      (x : ℂ) ^ (-s) * (ω : ℂ) ^ (s - 1) * Complex.exp (-(ω : ℂ) / (x : ℂ))
  change J (κ : ℂ) = R (κ : ℂ)
  set r₀ : ℝ := 1 / x - 1
  have hr₀_ge : 1 ≤ r₀ := by
    dsimp [r₀]; rw [le_sub_iff_add_le, one_add_one_eq_two, le_div_iff₀ hx0]; linarith
  have hr₀_pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀_ge
  let I_ray : ℝ → ℂ := fun θ ↦
    Complex.exp ((θ : ℂ) * Complex.I) *
      ∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
        (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) ^ (-(κ : ℂ))
  -- 2a. Angle invariance: `I_ray θ = I_ray (-π/4)` for EVERY `θ ∈ [-π/4, 0)`!
  have hconst_ray : ∀ θ ∈ Set.Ico (-(Real.pi / 4)) 0, I_ray θ = I_ray (-(Real.pi / 4)) := by
    intro θ hθ
    let Ω : Set ℂ := {z : ℂ | 1 - (x : ℂ) * z ∈ Complex.slitPlane}
    have hΩ : IsOpen Ω := Complex.isOpen_slitPlane.preimage (continuous_const.sub (continuous_const.mul continuous_id))
    let F : ℂ → ℂ := fun z ↦ Complex.exp (-(ω : ℂ) * z) * (1 - (x : ℂ) * z) ^ (-(κ : ℂ))
    have hF_holo : DifferentiableOn ℂ F Ω := by
      intro z hz
      have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.exp (-(ω : ℂ) * w)) z :=
        (differentiableAt_id.const_mul _).cexp
      have hlin : HasDerivAt (fun w : ℂ ↦ 1 - (x : ℂ) * w) (-(x : ℂ)) z := by
        simpa using ((hasDerivAt_id z).const_mul (x : ℂ)).const_sub (1 : ℂ)
      exact (h1.mul (hlin.cpow_const (c := -(κ : ℂ)) hz).differentiableAt).differentiableWithinAt
    let b₀ : ℝ := θ / 2
    have hb₀_neg : b₀ < 0 := by dsimp [b₀]; linarith [hθ.2]
    have hθ_lt_b₀ : θ < b₀ := by dsimp [b₀]; linarith [hθ.2]
    have hsin_b₀ : 0 < -Real.sin b₀ := by
      have hpos := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < -b₀) (by linarith [hθ.1, Real.pi_pos])
      rw [Real.sin_neg] at hpos; linarith
    -- Uniform positive lower bound `η` on `‖1 - x (1 + r e^{iφ})‖` for `φ ∈ (-π/3, b₀)`!
    let η : ℝ := min (x * r₀ / 2) (x * (r₀ / 2) * (-Real.sin b₀))
    have hη_pos : 0 < η := lt_min (by positivity) (by positivity)
    have hray_lb : ∀ φ ∈ Set.Ioo (-(Real.pi / 3)) b₀, ∀ r : ℝ, 0 ≤ r →
        1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∈ Ω ∧
        η ≤ ‖1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))‖ := by
      intro φ hφ r hr
      have hφ_neg : φ < 0 := lt_trans hφ.2 hb₀_neg
      have hsin_le : Real.sin φ ≤ Real.sin b₀ :=
        Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [hφ.1, Real.pi_pos], by linarith [Real.pi_pos]⟩
          ⟨by linarith [hθ.1, Real.pi_pos], by linarith [Real.pi_pos]⟩ hφ.2.le
      have hmem : 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        by_cases hr0 : r = 0
        · left; simp [hr0]; linarith
        · right
          have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
          have him : (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im =
              -x * r * Real.sin φ := by
            simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]; ring
          have hsin_neg : Real.sin φ < 0 := by linarith
          rw [him]; exact ne_of_gt (by nlinarith [mul_pos hx0 hr_pos])
      refine ⟨hmem, ?_⟩
      by_cases hr_small : r ≤ r₀ / 2
      · have h1 : 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) =
            (x : ℂ) * ((r₀ : ℂ) - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) := by
          dsimp [r₀]; push_cast; field_simp [hx0.ne']; ring
        rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        have htri : r₀ - r ≤ ‖(r₀ : ℂ) - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ := by
          have := norm_sub_norm_le (r₀ : ℂ) ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀_pos, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
              Complex.norm_exp_ofReal_mul_I, mul_one] at this
          exact this
        exact (min_le_left _ _).trans (by nlinarith)
      · push Not at hr_small
        have him : (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im =
            -x * r * Real.sin φ := by
          simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]; ring
        have him_le : (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im ≤
            ‖1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))‖ := Complex.im_le_norm _
        rw [him] at him_le
        have hxr : x * (r₀ / 2) ≤ x * r := by nlinarith
        have hneg_sin : -Real.sin b₀ ≤ -Real.sin φ := by linarith
        have hprod : x * (r₀ / 2) * (-Real.sin b₀) ≤ -x * r * Real.sin φ := by
          have := mul_le_mul hxr hneg_sin hsin_b₀.le (by positivity)
          linarith
        exact (min_le_right _ _).trans (hprod.trans him_le)
    let C_ray : ℝ := (1 + ω) * η ^ (-κ) + κ * x * η ^ (-(κ + 1))
    have hre_ge : ∀ φ ∈ Set.Ioo (-(Real.pi / 3)) b₀, ∀ r : ℝ, 0 ≤ r →
        1 + r / 2 ≤ (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)).re := by
      intro φ hφ r hr
      have hcos : 1 / 2 ≤ Real.cos φ := by
        rw [← Real.cos_abs, ← Real.cos_pi_div_three]
        exact Real.strictAntiOn_cos.antitoneOn
          ⟨abs_nonneg _, (abs_le.mpr ⟨hφ.1.le, (lt_trans hφ.2 hb₀_neg).le.trans (by positivity)⟩).trans
            (by linarith [Real.pi_pos])⟩
          ⟨by positivity, by linarith [Real.pi_pos]⟩
          (abs_le.mpr ⟨hφ.1.le, (lt_trans hφ.2 hb₀_neg).le.trans (by positivity)⟩)
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
      nlinarith
    have hbd_F : ∀ φ ∈ Set.Ioo (-(Real.pi / 3)) b₀, ∀ r : ℝ, 0 ≤ r →
        ‖F (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))‖ ≤ C_ray * (1 + r) ^ 0 * Real.exp (-(ω / 2) * r) := by
      intro φ hφ r hr
      have ⟨hsl, hng⟩ := hray_lb φ hφ r hr
      have hre := hre_ge φ hφ r hr
      dsimp [F]; rw [norm_mul, Complex.norm_exp, pow_zero, mul_one]
      have hexp : Real.exp (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).re ≤
          Real.exp (-(ω / 2) * r) := by
        apply Real.exp_le_exp.mpr
        have : (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).re =
            -ω * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)).re := by simp [Complex.mul_re]
        rw [this]; nlinarith
      have hcp : ‖(1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) ^ (-(κ : ℂ))‖ ≤ η ^ (-κ) := by
        have h1 := norm_cpow_le_rpow_mul_exp (w := -(κ : ℂ)) (Complex.slitPlane_ne_zero hsl)
        simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
          abs_zero, zero_mul, Real.exp_zero, mul_one] at h1
        exact h1.trans (Real.rpow_le_rpow_of_nonpos hη_pos hng (by linarith))
      have hC_ge : η ^ (-κ) ≤ C_ray := by
        dsimp [C_ray]
        have h1 : 0 ≤ ω * η ^ (-κ) := by positivity
        have h2 : 0 ≤ κ * x * η ^ (-(κ + 1)) := by positivity
        linarith
      calc Real.exp _ * ‖_‖ ≤ Real.exp (-(ω / 2) * r) * η ^ (-κ) :=
            mul_le_mul hexp hcp (norm_nonneg _) (Real.exp_pos _).le
        _ ≤ Real.exp (-(ω / 2) * r) * C_ray := mul_le_mul_of_nonneg_left hC_ge (Real.exp_pos _).le
        _ = C_ray * Real.exp (-(ω / 2) * r) := mul_comm _ _
    have hbd_F' : ∀ φ ∈ Set.Ioo (-(Real.pi / 3)) b₀, ∀ r : ℝ, 0 ≤ r →
        ‖deriv F (1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))‖ ≤ C_ray * (1 + r) ^ 0 * Real.exp (-(ω / 2) * r) := by
      intro φ hφ r hr
      set z := 1 + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
      have ⟨hsl, hng⟩ := hray_lb φ hφ r hr
      have hre := hre_ge φ hφ r hr
      have h1 : HasDerivAt (fun w : ℂ ↦ Complex.exp (-(ω : ℂ) * w)) (Complex.exp (-(ω : ℂ) * z) * (-(ω : ℂ))) z := by
        simpa using ((hasDerivAt_id z).const_mul (-(ω : ℂ))).cexp
      have hlin : HasDerivAt (fun w : ℂ ↦ 1 - (x : ℂ) * w) (-(x : ℂ)) z := by
        simpa using ((hasDerivAt_id z).const_mul (x : ℂ)).const_sub (1 : ℂ)
      have h2 := hlin.cpow_const (c := -(κ : ℂ)) hsl
      have hFd : deriv F z =
          Complex.exp (-(ω : ℂ) * z) * -(ω : ℂ) * (1 - (x : ℂ) * z) ^ (-(κ : ℂ)) +
          Complex.exp (-(ω : ℂ) * z) * (-(κ : ℂ) * (1 - (x : ℂ) * z) ^ (-(κ : ℂ) - 1) * -(x : ℂ)) :=
        (h1.mul h2).deriv
      rw [hFd, pow_zero, mul_one]
      have hexp : Real.exp (-(ω : ℂ) * z).re ≤ Real.exp (-(ω / 2) * r) := by
        apply Real.exp_le_exp.mpr
        have : (-(ω : ℂ) * z).re = -ω * z.re := by simp [Complex.mul_re]
        rw [this]; nlinarith
      have hcp0 : ‖(1 - (x : ℂ) * z) ^ (-(κ : ℂ))‖ ≤ η ^ (-κ) := by
        have h := norm_cpow_le_rpow_mul_exp (w := -(κ : ℂ)) (Complex.slitPlane_ne_zero hsl)
        simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
          abs_zero, zero_mul, Real.exp_zero, mul_one] at h
        exact h.trans (Real.rpow_le_rpow_of_nonpos hη_pos hng (by linarith))
      have hcp1 : ‖(1 - (x : ℂ) * z) ^ (-(κ : ℂ) - 1)‖ ≤ η ^ (-(κ + 1)) := by
        have h := norm_cpow_le_rpow_mul_exp (w := -(κ : ℂ) - 1) (Complex.slitPlane_ne_zero hsl)
        have hre_w : (-(κ : ℂ) - 1).re = -(κ + 1) := by simp; ring
        have him_w : |(-(κ : ℂ) - 1).im| = 0 := by simp
        rw [hre_w, him_w, zero_mul, Real.exp_zero, mul_one] at h
        exact h.trans (Real.rpow_le_rpow_of_nonpos hη_pos hng (by linarith))
      have ht1 : ‖Complex.exp (-(ω : ℂ) * z) * -(ω : ℂ) * (1 - (x : ℂ) * z) ^ (-(κ : ℂ))‖ ≤
          ω * η ^ (-κ) * Real.exp (-(ω / 2) * r) := by
        rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
        calc Real.exp (-(ω : ℂ) * z).re * ω * ‖(1 - (x : ℂ) * z) ^ (-(κ : ℂ))‖
            ≤ Real.exp (-(ω / 2) * r) * ω * η ^ (-κ) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hexp hω.le) hcp0 (norm_nonneg _) (by positivity)
          _ = ω * η ^ (-κ) * Real.exp (-(ω / 2) * r) := by ring
      have ht2 : ‖Complex.exp (-(ω : ℂ) * z) * (-(κ : ℂ) * (1 - (x : ℂ) * z) ^ (-(κ : ℂ) - 1) * -(x : ℂ))‖ ≤
          κ * x * η ^ (-(κ + 1)) * Real.exp (-(ω / 2) * r) := by
        rw [norm_mul, Complex.norm_exp, norm_mul, norm_mul, norm_neg, norm_neg,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hκ0, abs_of_pos hx0]
        calc Real.exp (-(ω : ℂ) * z).re * (κ * ‖(1 - (x : ℂ) * z) ^ (-(κ : ℂ) - 1)‖ * x)
            ≤ Real.exp (-(ω / 2) * r) * (κ * η ^ (-(κ + 1)) * x) :=
              mul_le_mul hexp (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcp1 hκ0.le) hx0.le)
                (by positivity) (Real.exp_pos _).le
          _ = κ * x * η ^ (-(κ + 1)) * Real.exp (-(ω / 2) * r) := by ring
      calc ‖Complex.exp (-(ω : ℂ) * z) * -(ω : ℂ) * (1 - (x : ℂ) * z) ^ (-(κ : ℂ)) +
            Complex.exp (-(ω : ℂ) * z) * (-(κ : ℂ) * (1 - (x : ℂ) * z) ^ (-(κ : ℂ) - 1) * -(x : ℂ))‖
          ≤ _ := norm_add_le _ _
        _ ≤ (ω * η ^ (-κ) + κ * x * η ^ (-(κ + 1))) * Real.exp (-(ω / 2) * r) := by linarith
        _ ≤ C_ray * Real.exp (-(ω / 2) * r) :=
            mul_le_mul_of_nonneg_right (by dsimp [C_ray]; linarith [Real.rpow_nonneg hη_pos.le (-κ)]) (Real.exp_pos _).le
    exact (ray_integral_const_on_Icc hΩ hF_holo (a₀ := -(Real.pi / 3)) (a := -(Real.pi / 4))
      (b := θ) (b₀ := b₀) (by linarith [Real.pi_pos]) hθ.1 hθ_lt_b₀
      (fun φ hφ r hr ↦ (hray_lb φ hφ r hr).1) (by positivity) (by positivity) hbd_F hbd_F').symm
  -- 2b. Dominated convergence as `θ → 0⁻`!
  let limFun : ℝ → ℂ := fun r ↦
    if r < r₀ then
      Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((1 - x * (1 + r) : ℝ) : ℂ) ^ (-(κ : ℂ))
    else
      Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ)) *
        Complex.exp (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I)
  let bound : ℝ → ℝ := fun r ↦ Real.exp (-ω * (1 + r / Real.sqrt 2)) * (x * |r - r₀|) ^ (-κ)
  have hbound_int : IntegrableOn bound (Set.Ioi 0) := by
    -- Split `Ioi 0 = Ioc 0 r₀ ∪ Ioi r₀`!
    have hunion : Set.Ioi (0 : ℝ) = Set.Ioc 0 r₀ ∪ Set.Ioi r₀ := (Set.Ioc_union_Ioi_eq_Ioi hr₀_pos.le).symm
    rw [hunion]
    refine IntegrableOn.union ?_ ?_
    · -- On `Ioc 0 r₀`: bounded by `x^{-κ} * (r₀ - r)^{-κ}`!
      have hint1 : IntegrableOn (fun r : ℝ ↦ (r₀ - r) ^ (-κ)) (Set.Ioc 0 r₀) := by
        have h1 : IntervalIntegrable (fun t : ℝ ↦ t ^ (-κ)) volume 0 r₀ :=
          intervalIntegral.intervalIntegrable_rpow' (by linarith)
        have h2 : IntervalIntegrable (fun r : ℝ ↦ (r₀ - r) ^ (-κ)) volume 0 r₀ := by
          have h := (h1.comp_sub_left r₀).symm
          simpa [sub_zero, sub_self] using h
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr₀_pos.le).mp h2
      refine (hint1.const_mul (x ^ (-κ))).mono' ?_ ?_
      · have hcont : ContinuousOn bound (Set.Ioo 0 r₀) := fun r hr ↦ by
          have hne : x * |r - r₀| ≠ 0 := mul_ne_zero hx0.ne' (abs_ne_zero.mpr (sub_ne_zero.mpr hr.2.ne))
          exact ((continuous_const.mul (continuous_const.add (continuous_id.div_const _))).rexp.continuousAt.mul
            ((continuousAt_const.mul (continuous_id.sub continuous_const).abs.continuousAt).rpow_const
              (Or.inl hne))).continuousWithinAt
        have hmeas : AEStronglyMeasurable bound (volume.restrict (Set.Ioo 0 r₀)) :=
          hcont.aestronglyMeasurable measurableSet_Ioo
        rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hmeas
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hr0_sub : 0 ≤ r₀ - r := sub_nonneg.mpr hr.2
        dsimp [bound]
        rw [abs_of_nonneg (by positivity), abs_of_nonpos (sub_nonpos.mpr hr.2), neg_sub,
            Real.mul_rpow hx0.le hr0_sub]
        have hexp1 : Real.exp (-ω * (1 + r / Real.sqrt 2)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [div_nonneg hr.1.le (Real.sqrt_nonneg 2)])
        calc Real.exp (-ω * (1 + r / Real.sqrt 2)) * (x ^ (-κ) * (r₀ - r) ^ (-κ))
            ≤ 1 * (x ^ (-κ) * (r₀ - r) ^ (-κ)) := mul_le_mul_of_nonneg_right hexp1 (by positivity)
          _ = x ^ (-κ) * (r₀ - r) ^ (-κ) := one_mul _
    · -- On `Ioi r₀`: bounded by `x^{-κ} * exp(-(ω/√2) (r - r₀)) * (r - r₀)^{-κ}`!
      have hω' : 0 < ω / Real.sqrt 2 := div_pos hω (Real.sqrt_pos.mpr zero_lt_two)
      have hgam : IntegrableOn (fun s : ℝ ↦ Real.exp (-s) * s ^ ((1 - κ) - 1)) (Set.Ioi 0) :=
        Real.GammaIntegral_convergent (by linarith)
      have hscale : IntegrableOn (fun t : ℝ ↦ Real.exp (-(ω / Real.sqrt 2) * t) * t ^ (-κ)) (Set.Ioi 0) := by
        have h1 := (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
          (fun s : ℝ ↦ Real.exp (-s) * s ^ ((1 - κ) - 1)) (0 : ℝ) hω').mpr (by simpa using hgam)
        refine (h1.const_mul ((ω / Real.sqrt 2) ^ κ)).congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        rw [show (1 - κ) - 1 = -κ by ring, Real.mul_rpow hω'.le ht0.le,
            Real.rpow_neg hω'.le, neg_mul]
        have hne : (ω / Real.sqrt 2) ^ κ ≠ 0 := (Real.rpow_pos_of_pos hω' κ).ne'
        field_simp [hne]
      have hshift : IntegrableOn (fun r : ℝ ↦ Real.exp (-(ω / Real.sqrt 2) * (r - r₀)) * (r - r₀) ^ (-κ)) (Set.Ioi r₀) := by
        rw [← integrable_indicator_iff measurableSet_Ioi] at hscale ⊢
        have h1 := hscale.comp_sub_right r₀
        refine h1.congr (Eventually.of_forall fun r ↦ ?_)
        by_cases hr : r₀ < r
        · have hr' : 0 < r - r₀ := sub_pos.mpr hr
          simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hr), Set.indicator_of_mem (Set.mem_Ioi.mpr hr')]
        · have hr' : ¬ (0 < r - r₀) := by linarith
          simp only [Set.indicator_of_notMem (show r ∉ Set.Ioi r₀ from hr),
            Set.indicator_of_notMem (show r - r₀ ∉ Set.Ioi 0 from hr')]
      refine (hshift.const_mul (x ^ (-κ))).mono' ?_ ?_
      · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
        intro r hr
        have hne : x * |r - r₀| ≠ 0 := mul_ne_zero hx0.ne' (abs_ne_zero.mpr (sub_ne_zero.mpr (Set.mem_Ioi.mp hr).ne'))
        exact ((continuous_const.mul (continuous_const.add (continuous_id.div_const _))).rexp.continuousAt.mul
          ((continuousAt_const.mul (continuous_id.sub continuous_const).abs.continuousAt).rpow_const
            (Or.inl hne))).continuousWithinAt
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr_gt : r₀ < r := hr
        dsimp [bound]
        rw [abs_of_nonneg (by positivity), abs_of_pos (sub_pos.mpr hr_gt),
            Real.mul_rpow hx0.le (sub_pos.mpr hr_gt).le]
        have hexp_le : Real.exp (-ω * (1 + r / Real.sqrt 2)) ≤ Real.exp (-(ω / Real.sqrt 2) * (r - r₀)) :=
          Real.exp_le_exp.mpr (by
            have h1 : -ω * (1 + r / Real.sqrt 2) = -ω - (ω / Real.sqrt 2) * r := by ring
            have h2 : -(ω / Real.sqrt 2) * (r - r₀) = (ω / Real.sqrt 2) * r₀ - (ω / Real.sqrt 2) * r := by ring
            nlinarith [div_pos hω (Real.sqrt_pos.mpr zero_lt_two)])
        calc Real.exp (-ω * (1 + r / Real.sqrt 2)) * (x ^ (-κ) * (r - r₀) ^ (-κ))
            ≤ Real.exp (-(ω / Real.sqrt 2) * (r - r₀)) * (x ^ (-κ) * (r - r₀) ^ (-κ)) :=
              mul_le_mul_of_nonneg_right hexp_le (by positivity)
          _ = x ^ (-κ) * (Real.exp (-(ω / Real.sqrt 2) * (r - r₀)) * (r - r₀) ^ (-κ)) := by ring
  -- Apply DCT to `I_ray θ` as `θ → 0⁻`!
  have hlim : Tendsto I_ray (𝓝[<] (0 : ℝ)) (𝓝 (∫ r in Set.Ioi (0 : ℝ), limFun r)) := by
    let H : ℝ → ℝ → ℂ := fun θ r ↦
      Complex.exp (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
        (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) ^ (-(κ : ℂ))
    have hmeas_H : ∀ᶠ θ in 𝓝[<] (0 : ℝ), AEStronglyMeasurable (H θ) (volume.restrict (Set.Ioi 0)) := by
      filter_upwards [Ico_mem_nhdsLT (show -(Real.pi / 4) < 0 by linarith [Real.pi_pos])] with θ hθ
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro r hr
      have hsin_neg : Real.sin θ < 0 := by
        rw [← neg_pos, ← Real.sin_neg]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.2]) (by linarith [hθ.1, Real.pi_pos])
      have hsl : 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; right
        have him : (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).im = -x * r * Real.sin θ := by
          simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]; ring
        rw [him]; exact ne_of_gt (by nlinarith [mul_pos hx0 (Set.mem_Ioi.mp hr), hsin_neg])
      have h1 : ContinuousAt (fun t : ℝ ↦ Complex.exp (-(ω : ℂ) * (1 + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) r :=
        Complex.continuous_exp.continuousAt.comp
          (continuousAt_const.mul (continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)))
      have h2 : ContinuousAt (fun t : ℝ ↦ (1 - (x : ℂ) * (1 + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) ^ (-(κ : ℂ))) r :=
        continuousAt_cpow_const_comp
          (continuousAt_const.sub (continuousAt_const.mul
            (continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)))) hsl
      exact (h1.mul h2).continuousWithinAt
    have hdom_H : ∀ᶠ θ in 𝓝[<] (0 : ℝ), ∀ᵐ r ∂volume.restrict (Set.Ioi 0), ‖H θ r‖ ≤ bound r := by
      filter_upwards [Ico_mem_nhdsLT (show -(Real.pi / 4) < 0 by linarith [Real.pi_pos])] with θ hθ
      have hae_ne : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), r ≠ r₀ :=
        ae_restrict_of_ae (compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton r₀))
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hae_ne] with r hr hrr₀
      have hr_pos : 0 < r := hr
      have hsin_neg : Real.sin θ < 0 := by
        rw [← neg_pos, ← Real.sin_neg]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.2]) (by linarith [hθ.1, Real.pi_pos])
      have hcos_ge : 1 / Real.sqrt 2 ≤ Real.cos θ := by
        have h1 : Real.cos (Real.pi / 4) ≤ Real.cos θ := by
          rw [← Real.cos_abs θ]
          exact Real.strictAntiOn_cos.antitoneOn
            ⟨abs_nonneg _, (abs_le.mpr ⟨hθ.1, hθ.2.le.trans (by positivity)⟩).trans (by linarith [Real.pi_pos])⟩
            ⟨by positivity, by linarith [Real.pi_pos]⟩
            (abs_le.mpr ⟨hθ.1, hθ.2.le.trans (by positivity)⟩)
        rw [Real.cos_pi_div_four] at h1
        have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        have h2 : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
          field_simp [(Real.sqrt_pos.mpr zero_lt_two).ne']; linarith
        linarith
      have hnorm_ge : x * |r - r₀| ≤ ‖1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ := by
        have hfac : 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
            (x : ℂ) * ((r₀ : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
          dsimp [r₀]; push_cast; field_simp [hx0.ne']; ring
        rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        apply mul_le_mul_of_nonneg_left _ hx0.le
        have hsq : |r - r₀| ^ 2 ≤ ‖(r₀ : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 := by
          rw [sq_abs, Complex.sq_norm, Complex.normSq_apply]
          have hre : ((r₀ : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = r₀ - r * Real.cos θ := by
            simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
          have him : ((r₀ : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = -(r * Real.sin θ) := by
            simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]
          rw [hre, him]
          have hsc := Real.sin_sq_add_cos_sq θ
          have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
          nlinarith [mul_nonneg hr₀_pos.le hr_pos.le,
            show (r₀ - r * Real.cos θ) * (r₀ - r * Real.cos θ) + -(r * Real.sin θ) * -(r * Real.sin θ) =
              r₀ ^ 2 - 2 * r₀ * r * Real.cos θ + r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) by ring]
        nlinarith [abs_nonneg (r - r₀), norm_nonneg ((r₀ : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))]
      have hne : 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
        intro h0
        have him := congrArg Complex.im h0
        have him' : (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).im = -x * r * Real.sin θ := by
          simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]; ring
        rw [him', Complex.zero_im] at him; nlinarith [mul_pos hx0 hr_pos, hsin_neg]
      dsimp [H, bound]
      rw [norm_mul, Complex.norm_exp]
      have hexp_le : Real.exp (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re ≤
          Real.exp (-ω * (1 + r / Real.sqrt 2)) := by
        apply Real.exp_le_exp.mpr
        have : (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re =
            -ω * (1 + r * Real.cos θ) := by
          simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
        rw [this]; nlinarith [mul_pos hω hr_pos, hcos_ge, show r / Real.sqrt 2 = r * (1 / Real.sqrt 2) by ring]
      have hcp : ‖(1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) ^ (-(κ : ℂ))‖ ≤
          (x * |r - r₀|) ^ (-κ) := by
        have h1 := norm_cpow_le_rpow_mul_exp (w := -(κ : ℂ)) hne
        simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
          abs_zero, zero_mul, Real.exp_zero, mul_one] at h1
        exact h1.trans (Real.rpow_le_rpow_of_nonpos (mul_pos hx0 (abs_pos.mpr (sub_ne_zero.mpr hrr₀)))
          hnorm_ge (by linarith))
      exact mul_le_mul hexp_le hcp (norm_nonneg _) (Real.exp_pos _).le
    have hpt_H : ∀ᵐ r ∂volume.restrict (Set.Ioi 0), Tendsto (fun θ ↦ H θ r) (𝓝[<] (0 : ℝ)) (𝓝 (limFun r)) := by
      have hae_ne : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), r ≠ r₀ :=
        ae_restrict_of_ae (compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton r₀))
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hae_ne] with r hr hrr₀
      have hr_pos : 0 < r := hr
      have hexp_lim : Tendsto (fun θ : ℝ ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
          (𝓝[<] (0 : ℝ)) (𝓝 (Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))))) := by
        have hc : Continuous (fun θ : ℝ ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) :=
          Complex.continuous_exp.comp (continuous_const.mul (continuous_const.add
            (continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))))
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0))
      have harg_lim : Tendsto (fun θ : ℝ ↦ 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          (𝓝[<] (0 : ℝ)) (𝓝 (1 - (x : ℂ) * (1 + (r : ℂ)))) := by
        have hc : Continuous (fun θ : ℝ ↦ 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
          continuous_const.sub (continuous_const.mul (continuous_const.add
            (continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))))
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0))
      rcases lt_or_gt_of_ne hrr₀ with hlt | hgt
      · dsimp [H, limFun]
        simp only [hlt, ↓reduceIte]
        have hpos : 0 < 1 - x * (1 + r) := by
          have h1 : x * (1 + r₀) = 1 := by dsimp [r₀]; field_simp [hx0.ne']; ring
          nlinarith
        have hsl : 1 - (x : ℂ) * (1 + (r : ℂ)) ∈ Complex.slitPlane := by
          rw [Complex.mem_slitPlane_iff]; left
          have : (1 - (x : ℂ) * (1 + (r : ℂ))).re = 1 - x * (1 + r) := by simp
          rw [this]; exact hpos
        have hpow_lim := ((continuousAt_cpow_const_slit (c := -(κ : ℂ)) hsl).tendsto).comp harg_lim
        have heqC : 1 - (x : ℂ) * (1 + (r : ℂ)) = ((1 - x * (1 + r) : ℝ) : ℂ) := by push_cast; ring
        rw [heqC] at hpow_lim
        exact hexp_lim.mul hpow_lim
      · dsimp [H, limFun]
        simp only [not_lt.mpr hgt.le, ↓reduceIte]
        have hpos : 0 < x * (1 + r) - 1 := by
          have h1 : x * (1 + r₀) = 1 := by dsimp [r₀]; field_simp [hx0.ne']; ring
          nlinarith
        -- Rotate by `-I` to lift `log` into the interior of `slitPlane`!
        have hev_eq : (fun θ : ℝ ↦ (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) ^ (-(κ : ℂ))) =ᶠ[𝓝[<] (0 : ℝ)]
            fun θ : ℝ ↦ Complex.exp (-(κ : ℂ) * (Complex.log (-Complex.I * (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) +
              ((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) := by
          filter_upwards [Ico_mem_nhdsLT (show -(Real.pi / 4) < 0 by linarith [Real.pi_pos])] with θ hθ
          have hsin_neg : Real.sin θ < 0 := by
            rw [← neg_pos, ← Real.sin_neg]
            exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.2]) (by linarith [hθ.1, Real.pi_pos])
          have him_pos : 0 < (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).im := by
            have him : (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).im = -x * r * Real.sin θ := by
              simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]; ring
            rw [him]; nlinarith
          have hne : 1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := fun h0 ↦ by
            have := congrArg Complex.im h0; rw [Complex.zero_im] at this; linarith
          rw [Complex.cpow_def_of_ne_zero hne, log_eq_log_neg_I_mul_add him_pos, mul_comm]
        have hlim_rot : Tendsto (fun θ : ℝ ↦ -Complex.I * (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
            (𝓝[<] (0 : ℝ)) (𝓝 (((x * (1 + r) - 1 : ℝ) : ℂ) * Complex.I)) := by
          have h1 := harg_lim.const_mul (-Complex.I)
          have heq : -Complex.I * (1 - (x : ℂ) * (1 + (r : ℂ))) = ((x * (1 + r) - 1 : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rwa [heq] at h1
        have hsl_rot : ((x * (1 + r) - 1 : ℝ) : ℂ) * Complex.I ∈ Complex.slitPlane := by
          rw [Complex.mem_slitPlane_iff]; right; simp [hpos.ne']
        have hlog_rot : Complex.log (((x * (1 + r) - 1 : ℝ) : ℂ) * Complex.I) =
            ((Real.log (x * (1 + r) - 1) : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
          have hexp : Complex.exp (((Real.log (x * (1 + r) - 1) : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
              ((x * (1 + r) - 1 : ℝ) : ℂ) * Complex.I := by
            rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
            push_cast
            rw [Complex.exp_pi_div_two_mul_I]
          rw [← hexp, Complex.log_exp]
          · simp; linarith [Real.pi_pos]
          · simp; linarith [Real.pi_pos]
        have hpow_lim : Tendsto (fun θ : ℝ ↦ (1 - (x : ℂ) * (1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) ^ (-(κ : ℂ)))
            (𝓝[<] (0 : ℝ))
            (𝓝 (((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ)) * Complex.exp (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I))) := by
          refine Tendsto.congr' hev_eq.symm ?_
          have hlog_lim := ((Complex.hasDerivAt_log hsl_rot).continuousAt.tendsto).comp hlim_rot
          have hadd_lim := hlog_lim.add_const (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)
          have hmul_lim := hadd_lim.const_mul (-(κ : ℂ))
          have hexp_lim2 := Complex.continuous_exp.continuousAt.tendsto.comp hmul_lim
          rw [hlog_rot] at hexp_lim2
          have heq_val : Complex.exp (-(κ : ℂ) * ((((Real.log (x * (1 + r) - 1) : ℝ) : ℂ) +
                ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) =
              ((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ)) * Complex.exp (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I) := by
            rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
                ← Complex.ofReal_log hpos.le, ← Complex.exp_add]
            congr 1; push_cast; ring
          rwa [heq_val] at hexp_lim2
        simpa [mul_assoc] using hexp_lim.mul hpow_lim
    have hdct := tendsto_integral_filter_of_dominated_convergence bound hmeas_H hdom_H hbound_int hpt_H
    have hexp0 : Tendsto (fun θ : ℝ ↦ Complex.exp ((θ : ℂ) * Complex.I)) (𝓝[<] (0 : ℝ)) (𝓝 1) := by
      have hc : Continuous (fun θ : ℝ ↦ Complex.exp ((θ : ℂ) * Complex.I)) :=
        Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0))
    simpa [I_ray, H, one_mul] using hexp0.mul hdct
  -- Since `I_ray θ = I_ray (-π/4)` on `[-π/4, 0)`, uniqueness of limits gives `I_ray (-π/4) = ∫ limFun`!
  have hI_val : I_ray (-(Real.pi / 4)) = ∫ r in Set.Ioi (0 : ℝ), limFun r := by
    have hconst_lim : Tendsto I_ray (𝓝[<] (0 : ℝ)) (𝓝 (I_ray (-(Real.pi / 4)))) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [Ico_mem_nhdsLT (show -(Real.pi / 4) < 0 by linarith [Real.pi_pos])] with θ hθ
        exact (hconst_ray θ hθ).symm)
    exact tendsto_nhds_unique hconst_lim hlim
  -- 2c. For real `κ, ω, x`, `PhiMinus = star (PhiPlus)` → `J κ = ∫ (limFun - star limFun)`!
  have hPhiPlus_eq : PhiPlus (κ : ℂ) (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) = I_ray (-(Real.pi / 4)) := by
    dsimp [PhiPlus, I_ray, gammaMinus]
    have hexp : (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) = -Complex.I * (Real.pi : ℂ) / 4 := by push_cast; ring
    rw [hexp]
    congr 1; apply setIntegral_congr_fun measurableSet_Ioi; intro r _; simp [sub_eq_add_neg]
  have hPhiMinus_conj : PhiMinus (κ : ℂ) (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) =
      starRingEnd ℂ (PhiPlus (κ : ℂ) (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ))) := by
    dsimp [PhiMinus, PhiPlus]
    have hexp_c : starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)) =
        Complex.exp (Complex.I * (Real.pi : ℂ) / 4) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring
    rw [map_mul, hexp_c, ← integral_conj]
    congr 1; apply setIntegral_congr_fun measurableSet_Ioi; intro r hr
    have hsl := (one_sub_txy_norm_ge_gammaPlus zero_le_one le_rfl hx0.le hx1 (Set.mem_Ioi.mp hr).le).2.2
    simp only [Complex.ofReal_one, one_mul] at hsl
    have harg_ne : (1 + -(x : ℂ) * gammaPlus r).arg ≠ Real.pi := by
      have heq : 1 + -(x : ℂ) * gammaPlus r = 1 - (x : ℂ) * gammaPlus r := by ring
      rw [heq]; intro hpi; have ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hpi
      rcases Complex.mem_slitPlane_iff.mp hsl with h | h
      · linarith
      · exact h him
    have hcp := Complex.cpow_conj (1 + -(x : ℂ) * gammaPlus r) (-(κ : ℂ)) harg_ne
    simp only [map_add, map_one, map_mul, map_neg, Complex.conj_ofReal, star_gammaPlus] at hcp
    dsimp only
    rw [map_mul, ← Complex.exp_conj, ← hcp]
    simp [star_gammaMinus]
  have hlim_int : IntegrableOn limFun (Set.Ioi 0) := by
    refine hbound_int.mono' ?_ ?_
    · have heq_m : limFun =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          fun r ↦ (Set.Iio r₀).indicator (fun r ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((1 - x * (1 + r) : ℝ) : ℂ) ^ (-(κ : ℂ))) r +
          (Set.Ioi r₀).indicator (fun r ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ)) *
            Complex.exp (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I)) r := by
        have hae_ne : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), r ≠ r₀ :=
          ae_restrict_of_ae (compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton r₀))
        filter_upwards [hae_ne] with r hrr₀
        dsimp [limFun]
        rcases lt_or_gt_of_ne hrr₀ with hlt | hgt
        · simp [hlt, not_lt.mpr hlt.le, Set.indicator_of_mem, Set.indicator_of_notMem]
        · simp [hgt, not_lt.mpr hgt.le, Set.indicator_of_mem, Set.indicator_of_notMem]
      refine AEStronglyMeasurable.congr ?_ heq_m.symm
      have hm1 : AEStronglyMeasurable
          ((Set.Iio r₀).indicator (fun r : ℝ ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((1 - x * (1 + r) : ℝ) : ℂ) ^ (-(κ : ℂ))))
          (volume.restrict (Set.Ioi 0)) := by
        refine AEStronglyMeasurable.indicator ?_ measurableSet_Iio
        have h1 : Measurable (fun r : ℝ ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ)))) :=
          (Complex.continuous_exp.comp (continuous_const.mul (continuous_const.add Complex.continuous_ofReal))).measurable
        have h2 : Measurable (fun r : ℝ ↦ ((1 - x * (1 + r) : ℝ) : ℂ) ^ (-(κ : ℂ))) :=
          (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_const.mul
            (continuous_const.add continuous_id)))).measurable.pow_const _
        exact (h1.mul h2).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable
          ((Set.Ioi r₀).indicator (fun r : ℝ ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ)) *
            Complex.exp (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I)))
          (volume.restrict (Set.Ioi 0)) := by
        refine AEStronglyMeasurable.indicator ?_ measurableSet_Ioi
        have h1 : Measurable (fun r : ℝ ↦ Complex.exp (-(ω : ℂ) * (1 + (r : ℂ)))) :=
          (Complex.continuous_exp.comp (continuous_const.mul (continuous_const.add Complex.continuous_ofReal))).measurable
        have h2 : Measurable (fun r : ℝ ↦ ((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ))) :=
          (Complex.continuous_ofReal.comp ((continuous_const.mul
            (continuous_const.add continuous_id)).sub continuous_const)).measurable.pow_const _
        exact ((h1.mul h2).mul measurable_const).aestronglyMeasurable
      exact hm1.add hm2
    · have hae_ne : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), r ≠ r₀ :=
        ae_restrict_of_ae (compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton r₀))
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hae_ne] with r hr hrr₀
      dsimp [limFun, bound]
      have hexp_le : Real.exp (-ω * (1 + r)) ≤ Real.exp (-ω * (1 + r / Real.sqrt 2)) := by
        apply Real.exp_le_exp.mpr
        have h1 : r / Real.sqrt 2 ≤ r := div_le_self (Set.mem_Ioi.mp hr).le (by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)
        nlinarith
      rcases lt_or_gt_of_ne hrr₀ with hlt | hgt
      · simp only [hlt, ↓reduceIte, norm_mul, Complex.norm_exp]
        have hpos : 0 < 1 - x * (1 + r) := by
          have h1 : x * (1 + r₀) = 1 := by dsimp [r₀]; field_simp [hx0.ne']; ring
          nlinarith
        have hre_e : (-(ω : ℂ) * (1 + (r : ℂ))).re = -ω * (1 + r) := by simp
        have hcp : ‖((1 - x * (1 + r) : ℝ) : ℂ) ^ (-(κ : ℂ))‖ = (x * |r - r₀|) ^ (-κ) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
          have : 1 - x * (1 + r) = x * |r - r₀| := by
            rw [abs_of_neg (sub_neg.mpr hlt)]; dsimp [r₀]; field_simp [hx0.ne']; ring
          simp [this]
        rw [hre_e, hcp]
        exact mul_le_mul_of_nonneg_right hexp_le (by positivity)
      · simp only [not_lt.mpr hgt.le, ↓reduceIte, norm_mul, Complex.norm_exp]
        have hpos : 0 < x * (1 + r) - 1 := by
          have h1 : x * (1 + r₀) = 1 := by dsimp [r₀]; field_simp [hx0.ne']; ring
          nlinarith
        have hre_e : (-(ω : ℂ) * (1 + (r : ℂ))).re = -ω * (1 + r) := by simp
        have hcp : ‖((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ))‖ = (x * |r - r₀|) ^ (-κ) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
          have : x * (1 + r) - 1 = x * |r - r₀| := by
            rw [abs_of_pos (sub_pos.mpr hgt)]; dsimp [r₀]; field_simp [hx0.ne']; ring
          simp [this]
        have hre_pi : (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
        rw [hre_e, hcp, hre_pi, Real.exp_zero, mul_one]
        exact mul_le_mul_of_nonneg_right hexp_le (by positivity)
  have hlim_conj_int : IntegrableOn (fun r ↦ starRingEnd ℂ (limFun r)) (Set.Ioi 0) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hlim_int
  have hJ_eq_int : J (κ : ℂ) = ∫ r in Set.Ioi (0 : ℝ), (limFun r - starRingEnd ℂ (limFun r)) := by
    dsimp [J]
    rw [hPhiMinus_conj, hPhiPlus_eq, hI_val, ← integral_conj, ← integral_sub hlim_int hlim_conj_int]
  -- Split at `r₀`: `Ioc 0 r₀` gives `0` and `Ioi r₀` gives `-2 i sin(π κ) * real_int`!
  have hdiff_eq : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      limFun r - starRingEnd ℂ (limFun r) =
        (Set.Ioi r₀).indicator (fun r : ℝ ↦
          (-2 * Complex.I * Complex.sin ((Real.pi : ℂ) * (κ : ℂ))) *
            (((Real.exp (-ω * (1 + r)) * (x * (1 + r) - 1) ^ (-κ)) : ℝ) : ℂ)) r := by
    have hae_ne : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), r ≠ r₀ :=
      ae_restrict_of_ae (compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton r₀))
    filter_upwards [hae_ne] with r hrr₀
    dsimp [limFun]
    rcases lt_or_gt_of_ne hrr₀ with hlt | hgt
    · simp only [hlt, ↓reduceIte, Set.indicator_of_notMem (show r ∉ Set.Ioi r₀ from not_lt.mpr hlt.le)]
      have hpos : 0 < 1 - x * (1 + r) := by
        have h1 : x * (1 + r₀) = 1 := by dsimp [r₀]; field_simp [hx0.ne']; ring
        nlinarith
      have hreal_val : Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((1 - x * (1 + r) : ℝ) : ℂ) ^ (-(κ : ℂ)) =
          ((Real.exp (-ω * (1 + r)) * (1 - x * (1 + r)) ^ (-κ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_cpow hpos.le]
        push_cast; ring_nf
      rw [hreal_val, Complex.conj_ofReal, sub_self]
    · simp only [not_lt.mpr hgt.le, ↓reduceIte, Set.indicator_of_mem (Set.mem_Ioi.mpr hgt)]
      have hpos : 0 < x * (1 + r) - 1 := by
        have h1 : x * (1 + r₀) = 1 := by dsimp [r₀]; field_simp [hx0.ne']; ring
        nlinarith
      have hreal_val : Complex.exp (-(ω : ℂ) * (1 + (r : ℂ))) * ((x * (1 + r) - 1 : ℝ) : ℂ) ^ (-(κ : ℂ)) =
          ((Real.exp (-ω * (1 + r)) * (x * (1 + r) - 1) ^ (-κ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_cpow hpos.le]
        push_cast; ring_nf
      rw [hreal_val, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      have hsin : Complex.exp (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I) -
          Complex.exp ((starRingEnd ℂ) (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I)) =
          -2 * Complex.I * Complex.sin ((Real.pi : ℂ) * (κ : ℂ)) := by
        have hst : (starRingEnd ℂ) (-(κ : ℂ) * (Real.pi : ℂ) * Complex.I) =
            ((Real.pi : ℂ) * (κ : ℂ)) * Complex.I := by simp; ring
        rw [hst, Complex.sin,
            show -(κ : ℂ) * (Real.pi : ℂ) * Complex.I = -((Real.pi : ℂ) * (κ : ℂ) * Complex.I) by ring]
        have hI2 : (-2 * Complex.I) * (Complex.I / 2) = 1 := by
          calc (-2 * Complex.I) * (Complex.I / 2) = -(Complex.I ^ 2) := by ring
            _ = 1 := by rw [Complex.I_sq]; norm_num
        have hneg_arg : -((Real.pi : ℂ) * (κ : ℂ)) * Complex.I = -((Real.pi : ℂ) * (κ : ℂ) * Complex.I) := by ring
        rw [hneg_arg]
        calc Complex.exp (-((Real.pi : ℂ) * (κ : ℂ) * Complex.I)) -
                Complex.exp ((Real.pi : ℂ) * (κ : ℂ) * Complex.I)
            = ((-2 * Complex.I) * (Complex.I / 2)) *
                (Complex.exp (-((Real.pi : ℂ) * (κ : ℂ) * Complex.I)) -
                  Complex.exp ((Real.pi : ℂ) * (κ : ℂ) * Complex.I)) := by rw [hI2, one_mul]
          _ = -2 * Complex.I *
                ((Complex.exp (-((Real.pi : ℂ) * (κ : ℂ) * Complex.I)) -
                  Complex.exp ((Real.pi : ℂ) * (κ : ℂ) * Complex.I)) * Complex.I / 2) := by ring
      linear_combination (((Real.exp (-ω * (1 + r)) * (x * (1 + r) - 1) ^ (-κ)) : ℝ) : ℂ) * hsin
  have hof : ∫ a in Set.Ioi r₀, ((Real.exp (-ω * (1 + a)) * (x * (1 + a) - 1) ^ (-κ) : ℝ) : ℂ) =
      ((∫ a in Set.Ioi r₀, Real.exp (-ω * (1 + a)) * (x * (1 + a) - 1) ^ (-κ) : ℝ) : ℂ) :=
    integral_ofReal
  rw [hJ_eq_int, integral_congr_ae hdiff_eq, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hr₀_pos.le), integral_const_mul, hof]
  -- 2d. Evaluate the real Gamma integral `∫ r in Ioi r₀, exp(-ω(1+r)) (x(1+r) - 1)^{-κ}`!
  have hreal_int : ∫ r in Set.Ioi r₀, Real.exp (-ω * (1 + r)) * (x * (1 + r) - 1) ^ (-κ) =
      Real.exp (-ω / x) * x ^ (-κ) * ω ^ (κ - 1) * Real.Gamma (1 - κ) := by
    -- Shift `r = r₀ + t` (`t ∈ Ioi 0`)!
    have hshift : ∫ r in Set.Ioi r₀, Real.exp (-ω * (1 + r)) * (x * (1 + r) - 1) ^ (-κ) =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ω / x) * x ^ (-κ) * (Real.exp (-ω * t) * t ^ (-κ)) := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
          ← MeasureTheory.integral_add_left_eq_self _ r₀]
      congr 1; ext t
      by_cases ht : 0 < t
      · have ht' : r₀ < r₀ + t := by linarith
        simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Set.indicator_of_mem (Set.mem_Ioi.mpr ht')]
        have h1 : 1 + (r₀ + t) = 1 / x + t := by dsimp [r₀]; ring
        have h2 : x * (1 + (r₀ + t)) - 1 = x * t := by
          rw [h1]; field_simp [hx0.ne']; ring
        rw [h2, h1, show -ω * (1 / x + t) = -ω / x + -ω * t by ring, Real.exp_add,
            Real.mul_rpow hx0.le ht.le]
        ring
      · have ht' : ¬ (r₀ < r₀ + t) := by linarith
        simp only [Set.indicator_of_notMem (show t ∉ Set.Ioi 0 from ht),
          Set.indicator_of_notMem (show r₀ + t ∉ Set.Ioi r₀ from ht')]
    rw [hshift, integral_const_mul]
    -- Scale `s = ω * t`!
    have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
      (fun s : ℝ ↦ Real.exp (-s) * s ^ ((1 - κ) - 1)) (0 : ℝ) hω
    simp only [mul_zero, smul_eq_mul, ← Real.Gamma_eq_integral (show 0 < 1 - κ by linarith)] at hcomp
    have hscale : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(ω * t)) * (ω * t) ^ ((1 - κ) - 1) =
        ω ^ (-κ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ω * t) * t ^ (-κ) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi; intro t ht
      dsimp only
      rw [show (1 - κ) - 1 = -κ by ring, Real.mul_rpow hω.le (Set.mem_Ioi.mp ht).le, neg_mul]
      ring
    rw [hscale] at hcomp
    have hω_ne : ω ^ (-κ) ≠ 0 := (Real.rpow_pos_of_pos hω (-κ)).ne'
    have hval : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ω * t) * t ^ (-κ) = ω ^ (κ - 1) * Real.Gamma (1 - κ) := by
      have h1 : ω ^ (κ - 1) = ω⁻¹ * (ω ^ (-κ))⁻¹ := by
        rw [Real.rpow_sub hω, Real.rpow_one, Real.rpow_neg hω.le, inv_inv, div_eq_mul_inv]; ring
      rw [h1]
      have h2 := congrArg (fun z : ℝ ↦ (ω ^ (-κ))⁻¹ * z) hcomp
      rw [← mul_assoc, inv_mul_cancel₀ hω_ne, one_mul] at h2
      rw [h2]; ring
    rw [hval]; ring
  rw [hreal_int]
  -- Apply Euler's reflection formula `Real.Gamma κ * Real.Gamma (1 - κ) = π / sin(π κ)`!
  have href := Real.Gamma_mul_Gamma_one_sub κ
  have hsin_ne : Real.sin (Real.pi * κ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hκ0) (by nlinarith [Real.pi_pos])).ne'
  have hG_ne : Real.Gamma κ ≠ 0 := (Real.Gamma_pos_of_pos hκ0).ne'
  have href' : Real.sin (Real.pi * κ) * Real.Gamma (1 - κ) = Real.pi / Real.Gamma κ := by
    rw [eq_div_iff hG_ne]
    have h1 := (eq_div_iff hsin_ne).mp href
    linarith
  dsimp [R]
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_mul Real.pi κ, ← Complex.ofReal_sin]
  have hpow_x : (x : ℂ) ^ (-(κ : ℂ)) = ((x ^ (-κ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, Complex.ofReal_cpow hx0.le]
  have hpow_ω : (ω : ℂ) ^ ((κ : ℂ) - 1) = ((ω ^ (κ - 1) : ℝ) : ℂ) := by
    rw [show (κ : ℂ) - 1 = ((κ - 1 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_cpow hω.le]
  have hexp_ωx : Complex.exp (-(ω : ℂ) / (x : ℂ)) = ((Real.exp (-ω / x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_exp]
  rw [hpow_x, hpow_ω, hexp_ωx, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  have hrefC : ((Real.sin (Real.pi * κ) : ℝ) : ℂ) * ((Real.Gamma (1 - κ) : ℝ) : ℂ) =
      (Real.pi : ℂ) / ((Real.Gamma κ : ℝ) : ℂ) := by
    exact_mod_cast href'
  linear_combination -2 * Complex.I * ((Real.exp (-ω / x) : ℝ) : ℂ) *
    ((x ^ (-κ) : ℝ) : ℂ) * ((ω ^ (κ - 1) : ℝ) : ℂ) * hrefC

/-- **Lemma 5.2 (Single-Mode Exact Hankel Keyhole Jump)**:
For EVERY `k ∈ ℂ`, EVERY `ω > 0`, and EVERY real `x ∈ (0, 1/2]`:
`Φ₊(e^{-ω y}; -x) - Φ₋(e^{-ω y}; -x) = -(2 π i / Γ(k)) x^{-k} ω^{k - 1} e^{-ω / x}`! -/
theorem hankel_single_mode_jump (k : ℂ) {ω x : ℝ} (hω : 0 < ω) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    PhiPlus k (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) -
      PhiMinus k (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) =
    -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma k) *
      (x : ℂ) ^ (-k) * (ω : ℂ) ^ (k - 1) * Complex.exp (-(ω : ℂ) / (x : ℂ)) := by
  let J : ℂ → ℂ := fun s ↦
    PhiPlus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ)) -
      PhiMinus s (fun y ↦ Complex.exp (-(ω : ℂ) * y)) (-(x : ℂ))
  let R : ℂ → ℂ := fun s ↦
    -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma s) *
      (x : ℂ) ^ (-s) * (ω : ℂ) ^ (s - 1) * Complex.exp (-(ω : ℂ) / (x : ℂ))
  have hR_entire : Differentiable ℂ R := by
    intro s
    have hinvG : DifferentiableAt ℂ (fun w : ℂ ↦ -(2 * (Real.pi : ℂ) * Complex.I) * (Complex.Gamma w)⁻¹) s :=
      (differentiable_inv_Gamma s).const_mul _
    have hxpow : DifferentiableAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) s :=
      (differentiableAt_const (x : ℂ)).cpow differentiableAt_id.neg (Or.inl (by simpa using hx0))
    have hωpow : DifferentiableAt ℂ (fun w : ℂ ↦ (ω : ℂ) ^ (w - 1)) s :=
      (differentiableAt_const (ω : ℂ)).cpow (differentiableAt_id.sub_const 1) (Or.inl (by simpa using hω))
    have heq : R = fun w ↦ (-(2 * (Real.pi : ℂ) * Complex.I) * (Complex.Gamma w)⁻¹) *
        (x : ℂ) ^ (-w) * (ω : ℂ) ^ (w - 1) * Complex.exp (-(ω : ℂ) / (x : ℂ)) := by
      ext w; dsimp [R]; ring
    rw [heq]
    exact ((hinvG.mul hxpow).mul hωpow).mul_const _
  have hJ_entire : Differentiable ℂ J := hankel_single_mode_entire hω hx0 hx1
  have hreal : ∀ κ : ℝ, 0 < κ → κ < 1 → J (κ : ℂ) = R (κ : ℂ) :=
    fun κ hκ0 hκ1 ↦ hankel_single_mode_jump_real hω hx0 hx1 hκ0 hκ1
  -- Step 3: Identity Theorem for entire functions `J` and `R`!
  have hAnJ : AnalyticOnNhd ℂ J Set.univ := hJ_entire.differentiableOn.analyticOnNhd isOpen_univ
  have hAnR : AnalyticOnNhd ℂ R Set.univ := hR_entire.differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ s in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), J s = R s := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hVopen, hmemV, hVsub⟩ := hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hVopen ((1 / 2 : ℝ) : ℂ) hmemV
    let δ : ℝ := min (ε / 2) (1 / 4)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
    let κ : ℝ := 1 / 2 + δ
    have hκ_ne : (κ : ℂ) ≠ ((1 / 2 : ℝ) : ℂ) := fun h ↦ by
      have := Complex.ofReal_injective h; dsimp [κ] at this; linarith
    have hκ_ball : (κ : ℂ) ∈ Metric.ball ((1 / 2 : ℝ) : ℂ) ε := by
      rw [Metric.mem_ball, Complex.dist_eq, show (κ : ℂ) - ((1 / 2 : ℝ) : ℂ) = (δ : ℂ) by
        dsimp [κ]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact ⟨(κ : ℂ), hVsub ⟨hball hκ_ball, hκ_ne⟩,
      hreal κ (by dsimp [κ]; linarith) (by dsimp [κ]; have := min_le_right (ε / 2) (1 / 4); linarith)⟩
  exact hAnJ.eqOn_of_preconnected_of_frequently_eq hAnR isPreconnected_univ (Set.mem_univ _) hfreq (Set.mem_univ k)

/-- Polynomial bound on `‖(mockJetQAt k j ω).eval x‖` for `ω ≥ 0` and `x ∈ [0, 1]`. -/
theorem norm_eval_mockJetQAt_le (k : ℂ) (j : ℕ) :
    ∃ M_j : ℝ, 0 ≤ M_j ∧
      ∀ ω x : ℝ, 0 ≤ ω → 0 ≤ x → x ≤ 1 →
        ‖(mockJetQAt k j (ω : ℂ)).eval (x : ℂ)‖ ≤ M_j * (1 + ω) ^ j := by
  let coeffBd : ℕ → ℝ := fun m ↦
    ∑ d ∈ ((mockJetQ k j).coeff m).support, ‖((mockJetQ k j).coeff m).coeff d‖
  refine ⟨∑ m ∈ Finset.range (j + 1), coeffBd m, Finset.sum_nonneg fun m _ ↦
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, fun ω x hω hx0 hx1 ↦ ?_⟩
  have heval_eq : (mockJetQAt k j (ω : ℂ)).eval (x : ℂ) =
      ∑ m ∈ Finset.range (j + 1), (((mockJetQ k j).coeff m).eval (x : ℂ)) * (ω : ℂ) ^ m := by
    unfold mockJetQAt
    rw [Polynomial.eval_eq_sum_range' (lt_of_eq_of_lt (mockJetQ_natDegree k j) (Nat.lt_succ_self j))]
    change (Polynomial.evalRingHom (x : ℂ)) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl; intro m _
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
  rw [heval_eq, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω]
  have hpx : ‖((mockJetQ k j).coeff m).eval (x : ℂ)‖ ≤ coeffBd m := by
    rw [Polynomial.eval_eq_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ ↦ ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hx0 hx1)
  have hωm : ω ^ m ≤ (1 + ω) ^ j :=
    (pow_le_pow_left₀ hω (by linarith) m).trans (pow_le_pow_right₀ (by linarith) hmj)
  exact mul_le_mul hpx hωm (pow_nonneg hω m) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- **Lemma 5.2 (Full Series Hankel Keyhole Jump)**:
For any exponentially decaying Fourier series `b(y) = ∑' n, c n * exp(-ω n * y)` with
`δ * (n + 1) ≤ ω n` (`0 < δ`) and `‖c n‖ ≤ C₀ * exp(a * ω n)` (`a < 1`), for EVERY `k ∈ ℂ`
and EVERY `x ∈ (0, 1/2]`:
`Φ₊(b; -x) - Φ₋(b; -x) = -(2 π i / Γ(k)) * ∑' n, c n * x^{-k} * ω_n^{k-1} * e^{-ω_n / x}`! -/
theorem hankel_series_jump (k : ℂ) (c : ℕ → ℂ) (ω : ℕ → ℝ) {δ C₀ a : ℝ}
    (hδ : 0 < δ) (hC₀ : 0 ≤ C₀) (ha : a < 1)
    (hω : ∀ n : ℕ, δ * ((n + 1 : ℕ) : ℝ) ≤ ω n)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ C₀ * Real.exp (a * ω n))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    PhiPlus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(x : ℂ)) -
      PhiMinus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(x : ℂ)) =
    -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma k) *
      ∑' n : ℕ, c n * (x : ℂ) ^ (-k) * (ω n : ℂ) ^ (k - 1) * Complex.exp (-(ω n : ℂ) / (x : ℂ)) := by
  have hω_pos : ∀ n : ℕ, 0 < ω n := fun n ↦ lt_of_lt_of_le (by positivity) (hω n)
  have h1a : 0 < 1 - a := sub_pos.mpr ha
  -- Helper: Fubini swap on either rotated ray `γ = gammaMinus` or `γ = gammaPlus`!
  have hfubini : ∀ (γ : ℝ → ℂ),
      Continuous γ →
      (∀ r : ℝ, 0 ≤ r → (γ r).re = 1 + r / Real.sqrt 2 ∧ ‖γ r‖ ≤ 1 + r) →
      (∀ r : ℝ, 0 ≤ r → 1 / (2 * Real.sqrt 2) ≤ ‖1 - (x : ℂ) * γ r‖ ∧
        1 - (x : ℂ) * γ r ∈ Complex.slitPlane) →
      (∫ r in Set.Ioi (0 : ℝ), (∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * γ r)) * (1 + -(x : ℂ) * γ r) ^ (-k)) =
        ∑' n : ℕ, c n * ∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k) := by
    intro γ hγ_cont hγ_prop hγ_lb
    have heq_f : ∀ r ∈ Set.Ioi (0 : ℝ),
        (∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * γ r)) * (1 + -(x : ℂ) * γ r) ^ (-k) =
          ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k) := fun r _ ↦ by
      rw [← tsum_mul_right]
    rw [setIntegral_congr_fun measurableSet_Ioi heq_f]
    -- Uniform polynomial bound on `‖(1 - x γ r)^{-k}‖ ≤ K_k * (1 + r)^d_k`!
    let d_k : ℕ := Nat.ceil (max (-k.re) 0)
    let K_k : ℝ := (2 * Real.sqrt 2) ^ max k.re 0 * 2 ^ max (-k.re) 0 * Real.exp (|k.im| * Real.pi)
    have hKk_nn : 0 ≤ K_k := by positivity
    have hpow_le : ∀ r : ℝ, 0 ≤ r → ‖(1 + -(x : ℂ) * γ r) ^ (-k)‖ ≤ K_k * (1 + r) ^ d_k := by
      intro r hr
      have ⟨hng, hsl⟩ := hγ_lb r hr
      have ⟨_, hgn⟩ := hγ_prop r hr
      have harg : 1 + -(x : ℂ) * γ r = 1 - (x : ℂ) * γ r := by ring
      rw [harg]
      have hcp := norm_cpow_le_rpow_mul_exp (z := 1 - (x : ℂ) * γ r) (w := -k) (Complex.slitPlane_ne_zero hsl)
      rw [Complex.neg_re, Complex.neg_im, abs_neg] at hcp
      have hrpow : ‖1 - (x : ℂ) * γ r‖ ^ (-k.re) ≤
          (2 * Real.sqrt 2) ^ max k.re 0 * 2 ^ max (-k.re) 0 * (1 + r) ^ d_k := by
        by_cases hneg : -k.re ≤ 0
        · rw [max_eq_left (by linarith : 0 ≤ k.re), max_eq_right hneg, Real.rpow_zero, mul_one]
          have h1 : ‖1 - (x : ℂ) * γ r‖ ^ (-k.re) ≤ (2 * Real.sqrt 2) ^ k.re :=
            (Real.rpow_le_rpow_of_nonpos (by positivity) hng hneg).trans_eq (by
              rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv])
          have h2 : (1 : ℝ) ≤ (1 + r) ^ d_k := one_le_pow₀ (by linarith)
          nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * Real.sqrt 2 by positivity) k.re]
        · push Not at hneg
          rw [max_eq_right (by linarith : k.re ≤ 0), max_eq_left hneg.le, Real.rpow_zero, one_mul]
          have hup : ‖1 - (x : ℂ) * γ r‖ ≤ 2 * (1 + r) := by
            calc ‖1 - (x : ℂ) * γ r‖ ≤ 1 + x * ‖γ r‖ := by
                  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] using
                    norm_sub_le (1 : ℂ) ((x : ℂ) * γ r)
              _ ≤ 1 + (1 / 2) * (1 + r) := by nlinarith [hx0, hx1, hgn]
              _ ≤ 2 * (1 + r) := by linarith
          calc ‖1 - (x : ℂ) * γ r‖ ^ (-k.re)
              ≤ (2 * (1 + r)) ^ (-k.re) := Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
            _ = 2 ^ (-k.re) * (1 + r) ^ (-k.re) := Real.mul_rpow (by norm_num) (by linarith)
            _ ≤ 2 ^ (-k.re) * (1 + r) ^ (d_k : ℝ) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith)
                  ((le_max_left (-k.re) 0).trans (Nat.le_ceil _))) (by positivity)
            _ = 2 ^ (-k.re) * (1 + r) ^ d_k := by rw [Real.rpow_natCast]
      exact hcp.trans ((mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le).trans_eq (by dsimp [K_k]; ring))
    have hδ' : 0 < δ / Real.sqrt 2 := div_pos hδ (Real.sqrt_pos.mpr zero_lt_two)
    have hdom_r : IntegrableOn (fun r : ℝ ↦ (1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r)) (Set.Ioi 0) :=
      integrableOn_one_add_pow_mul_exp hδ' d_k
    let M_r : ℝ := ∫ r in Set.Ioi (0 : ℝ), (1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r)
    have hMr_nn : 0 ≤ M_r := setIntegral_nonneg measurableSet_Ioi fun r hr ↦ by
      have : 0 ≤ r := (Set.mem_Ioi.mp hr).le; positivity
    have hmeas_n : ∀ n : ℕ, AEStronglyMeasurable
        (fun r : ℝ ↦ c n * Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k))
        (volume.restrict (Set.Ioi 0)) := fun n ↦ by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro r hr
      have hsl := (hγ_lb r (Set.mem_Ioi.mp hr).le).2
      have harg : 1 + -(x : ℂ) * γ r = 1 - (x : ℂ) * γ r := by ring
      have h1 : ContinuousAt (fun t : ℝ ↦ c n * Complex.exp (-(ω n : ℂ) * γ t)) r :=
        continuousAt_const.mul (Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hγ_cont.continuousAt))
      have h2 : ContinuousAt (fun t : ℝ ↦ (1 + -(x : ℂ) * γ t) ^ (-k)) r :=
        continuousAt_cpow_const_comp
          (continuousAt_const.add (continuousAt_const.mul hγ_cont.continuousAt)) (harg.symm ▸ hsl)
      exact (h1.mul h2).continuousWithinAt
    have hlintegral_ne_top :
        (∑' n : ℕ, ∫⁻ r in Set.Ioi (0 : ℝ),
          ‖c n * Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)‖ₑ) ≠ ⊤ := by
      have hgeom_sum : Summable (fun n : ℕ ↦ (C₀ * K_k * M_r) * (Real.exp (-(1 - a) * δ)) ^ n) :=
        (summable_geometric_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (by nlinarith))).mul_left _
      have hterm_le : ∀ n : ℕ,
          (∫⁻ r in Set.Ioi (0 : ℝ),
            ‖c n * Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)‖ₑ) ≤
          ENNReal.ofReal ((C₀ * K_k * M_r) * (Real.exp (-(1 - a) * δ)) ^ n) := by
        intro n
        have hint_n : IntegrableOn
            (fun r : ℝ ↦ (C₀ * K_k * Real.exp (-(1 - a) * δ * (n : ℝ))) *
              ((1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r))) (Set.Ioi 0) :=
          hdom_r.const_mul _
        have hpt_le : ∀ᵐ r ∂volume.restrict (Set.Ioi 0),
            ‖c n * Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)‖ₑ ≤
            ENNReal.ofReal ((C₀ * K_k * Real.exp (-(1 - a) * δ * (n : ℝ))) *
              ((1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r))) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
          rw [← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          rw [norm_mul, norm_mul, Complex.norm_exp]
          have hre := (hγ_prop r hr0).1
          have hre_e : (-(ω n : ℂ) * γ r).re = -ω n * (1 + r / Real.sqrt 2) := by simp [Complex.mul_re, hre]
          rw [hre_e]
          have hω_ge1 : δ ≤ ω n := (le_mul_of_one_le_right hδ.le (by exact_mod_cast Nat.succ_pos n)).trans (hω n)
          have hω_gen : δ * (n : ℝ) ≤ ω n :=
            (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hδ.le).trans (hω n)
          have hexp_comb : Real.exp (a * ω n) * Real.exp (-ω n * (1 + r / Real.sqrt 2)) ≤
              Real.exp (-(1 - a) * δ * (n : ℝ)) * Real.exp (-(δ / Real.sqrt 2) * r) := by
            rw [← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hr_div : 0 ≤ r / Real.sqrt 2 := div_nonneg hr0 (Real.sqrt_nonneg 2)
            nlinarith [show a * ω n + -ω n * (1 + r / Real.sqrt 2) = -(1 - a) * ω n - ω n * (r / Real.sqrt 2) by ring,
                       show -(δ / Real.sqrt 2) * r = -(δ * (r / Real.sqrt 2)) by ring]
          calc ‖c n‖ * Real.exp (-ω n * (1 + r / Real.sqrt 2)) * ‖(1 + -(x : ℂ) * γ r) ^ (-k)‖
              ≤ (C₀ * Real.exp (a * ω n)) * Real.exp (-ω n * (1 + r / Real.sqrt 2)) * (K_k * (1 + r) ^ d_k) :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hc n) (Real.exp_pos _).le)
                  (hpow_le r hr0) (norm_nonneg _) (by positivity)
            _ = C₀ * K_k * (Real.exp (a * ω n) * Real.exp (-ω n * (1 + r / Real.sqrt 2))) * (1 + r) ^ d_k := by ring
            _ ≤ C₀ * K_k * (Real.exp (-(1 - a) * δ * (n : ℝ)) * Real.exp (-(δ / Real.sqrt 2) * r)) * (1 + r) ^ d_k := by
                have := mul_le_mul_of_nonneg_left hexp_comb (mul_nonneg hC₀ hKk_nn)
                exact mul_le_mul_of_nonneg_right this (by positivity)
            _ = (C₀ * K_k * Real.exp (-(1 - a) * δ * (n : ℝ))) * ((1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r)) := by ring
        calc (∫⁻ r in Set.Ioi (0 : ℝ),
              ‖c n * Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)‖ₑ)
            ≤ ∫⁻ r in Set.Ioi (0 : ℝ),
                ENNReal.ofReal ((C₀ * K_k * Real.exp (-(1 - a) * δ * (n : ℝ))) *
                  ((1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r))) := lintegral_mono_ae hpt_le
          _ = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ),
                (C₀ * K_k * Real.exp (-(1 - a) * δ * (n : ℝ))) *
                  ((1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r))) :=
              (ofReal_integral_eq_lintegral_ofReal hint_n
                (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ by
                  have : 0 ≤ r := (Set.mem_Ioi.mp hr).le; positivity)).symm
          _ = ENNReal.ofReal ((C₀ * K_k * M_r) * (Real.exp (-(1 - a) * δ)) ^ n) := by
              rw [integral_const_mul]
              change ENNReal.ofReal ((C₀ * K_k * Real.exp (-(1 - a) * δ * (n : ℝ))) * M_r) = _
              rw [← Real.exp_nat_mul, show -(1 - a) * δ * (n : ℝ) = (n : ℝ) * (-(1 - a) * δ) by ring]
              congr 1; ring
      exact ne_top_of_le_ne_top (by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hgeom_sum]
        exact ENNReal.ofReal_ne_top) (tsum_le_tsum hterm_le)
    rw [MeasureTheory.integral_tsum hmeas_n hlintegral_ne_top]
    apply tsum_congr; intro n
    have : (fun r : ℝ ↦ c n * Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)) =
        fun r : ℝ ↦ c n * (Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)) := by
      ext r; ring
    rw [this, integral_const_mul]
  have hfub_m := hfubini gammaMinus
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun r hr ↦ ⟨gammaMinus_re r, by
      dsimp [gammaMinus]
      calc ‖1 + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]⟩)
    (fun r hr ↦ by
      have h := one_sub_txy_norm_ge_gammaMinus zero_le_one le_rfl hx0.le hx1 hr
      simp only [Complex.ofReal_one, one_mul] at h; exact ⟨h.1.trans h.2.1, h.2.2⟩)
  have hfub_p := hfubini gammaPlus
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun r hr ↦ ⟨gammaPlus_re r, by
      dsimp [gammaPlus]
      calc ‖1 + (r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]⟩)
    (fun r hr ↦ by
      have h := one_sub_txy_norm_ge_gammaPlus zero_le_one le_rfl hx0.le hx1 hr
      simp only [Complex.ofReal_one, one_mul] at h; exact ⟨h.1.trans h.2.1, h.2.2⟩)
  -- Summability of each ray's mode sum so we can subtract termwise!
  have hsum_ray : ∀ (γ : ℝ → ℂ),
      Continuous γ →
      (∀ r : ℝ, 0 ≤ r → (γ r).re = 1 + r / Real.sqrt 2 ∧ ‖γ r‖ ≤ 1 + r) →
      (∀ r : ℝ, 0 ≤ r → 1 / (2 * Real.sqrt 2) ≤ ‖1 - (x : ℂ) * γ r‖ ∧
        1 - (x : ℂ) * γ r ∈ Complex.slitPlane) →
      Summable (fun n : ℕ ↦ c n * ∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)) := by
    intro γ hγ_cont hγ_prop hγ_lb
    let d_k : ℕ := Nat.ceil (max (-k.re) 0)
    let K_k : ℝ := (2 * Real.sqrt 2) ^ max k.re 0 * 2 ^ max (-k.re) 0 * Real.exp (|k.im| * Real.pi)
    have hδ' : 0 < δ / Real.sqrt 2 := div_pos hδ (Real.sqrt_pos.mpr zero_lt_two)
    have hdom_r : IntegrableOn (fun r : ℝ ↦ (1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r)) (Set.Ioi 0) :=
      integrableOn_one_add_pow_mul_exp hδ' d_k
    let M_r : ℝ := ∫ r in Set.Ioi (0 : ℝ), (1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r)
    have hMr_nn : 0 ≤ M_r := setIntegral_nonneg measurableSet_Ioi fun r hr ↦ by
      have : 0 ≤ r := (Set.mem_Ioi.mp hr).le; positivity
    have hgeom : Summable (fun n : ℕ ↦ (C₀ * K_k * M_r) * (Real.exp (-(1 - a) * δ)) ^ n) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by nlinarith))).mul_left _
    refine Summable.of_norm_bounded hgeom fun n ↦ ?_
    rw [norm_mul]
    have hpow_le : ∀ r : ℝ, 0 ≤ r → ‖(1 + -(x : ℂ) * γ r) ^ (-k)‖ ≤ K_k * (1 + r) ^ d_k := by
      intro r hr
      have ⟨hng, hsl⟩ := hγ_lb r hr
      have ⟨_, hgn⟩ := hγ_prop r hr
      have harg : 1 + -(x : ℂ) * γ r = 1 - (x : ℂ) * γ r := by ring
      rw [harg]
      have hcp := norm_cpow_le_rpow_mul_exp (z := 1 - (x : ℂ) * γ r) (w := -k) (Complex.slitPlane_ne_zero hsl)
      rw [Complex.neg_re, Complex.neg_im, abs_neg] at hcp
      have hrpow : ‖1 - (x : ℂ) * γ r‖ ^ (-k.re) ≤
          (2 * Real.sqrt 2) ^ max k.re 0 * 2 ^ max (-k.re) 0 * (1 + r) ^ d_k := by
        by_cases hneg : -k.re ≤ 0
        · rw [max_eq_left (by linarith : 0 ≤ k.re), max_eq_right hneg, Real.rpow_zero, mul_one]
          have h1 : ‖1 - (x : ℂ) * γ r‖ ^ (-k.re) ≤ (2 * Real.sqrt 2) ^ k.re :=
            (Real.rpow_le_rpow_of_nonpos (by positivity) hng hneg).trans_eq (by
              rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv])
          have h2 : (1 : ℝ) ≤ (1 + r) ^ d_k := one_le_pow₀ (by linarith)
          nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * Real.sqrt 2 by positivity) k.re]
        · push Not at hneg
          rw [max_eq_right (by linarith : k.re ≤ 0), max_eq_left hneg.le, Real.rpow_zero, one_mul]
          have hup : ‖1 - (x : ℂ) * γ r‖ ≤ 2 * (1 + r) := by
            calc ‖1 - (x : ℂ) * γ r‖ ≤ 1 + x * ‖γ r‖ := by
                  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] using
                    norm_sub_le (1 : ℂ) ((x : ℂ) * γ r)
              _ ≤ 1 + (1 / 2) * (1 + r) := by nlinarith [hx0, hx1, hgn]
              _ ≤ 2 * (1 + r) := by linarith
          calc ‖1 - (x : ℂ) * γ r‖ ^ (-k.re)
              ≤ (2 * (1 + r)) ^ (-k.re) := Real.rpow_le_rpow (norm_nonneg _) hup hneg.le
            _ = 2 ^ (-k.re) * (1 + r) ^ (-k.re) := Real.mul_rpow (by norm_num) (by linarith)
            _ ≤ 2 ^ (-k.re) * (1 + r) ^ (d_k : ℝ) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith)
                  ((le_max_left (-k.re) 0).trans (Nat.le_ceil _))) (by positivity)
            _ = 2 ^ (-k.re) * (1 + r) ^ d_k := by rw [Real.rpow_natCast]
      exact hcp.trans ((mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le).trans_eq (by dsimp [K_k]; ring))
    have hω_ge1 : δ ≤ ω n := (le_mul_of_one_le_right hδ.le (by exact_mod_cast Nat.succ_pos n)).trans (hω n)
    have hω_gen : δ * (n : ℝ) ≤ ω n :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hδ.le).trans (hω n)
    have hint_n : IntegrableOn (fun r : ℝ ↦ Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)) (Set.Ioi 0) := by
      refine (hdom_r.const_mul (Real.exp (-ω n) * K_k)).mono' ?_ ?_
      · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
        intro r hr
        have hsl := (hγ_lb r (Set.mem_Ioi.mp hr).le).2
        have harg : 1 + -(x : ℂ) * γ r = 1 - (x : ℂ) * γ r := by ring
        have h2 : ContinuousAt (fun t : ℝ ↦ (1 + -(x : ℂ) * γ t) ^ (-k)) r :=
          continuousAt_cpow_const_comp
            (continuousAt_const.add (continuousAt_const.mul hγ_cont.continuousAt)) (by rw [harg]; exact hsl)
        exact ((Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hγ_cont.continuousAt)).mul h2).continuousWithinAt
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
        rw [norm_mul, Complex.norm_exp]
        have hre := (hγ_prop r hr0).1
        have hre_e : (-(ω n : ℂ) * γ r).re = -ω n * (1 + r / Real.sqrt 2) := by simp [Complex.mul_re, hre]
        rw [hre_e]
        have hexp : Real.exp (-ω n * (1 + r / Real.sqrt 2)) ≤ Real.exp (-ω n) * Real.exp (-(δ / Real.sqrt 2) * r) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
          have hr_div : 0 ≤ r / Real.sqrt 2 := div_nonneg hr0 (Real.sqrt_nonneg 2)
          nlinarith [show -ω n * (1 + r / Real.sqrt 2) = -ω n - ω n * (r / Real.sqrt 2) by ring,
                     show -(δ / Real.sqrt 2) * r = -(δ * (r / Real.sqrt 2)) by ring]
        calc Real.exp (-ω n * (1 + r / Real.sqrt 2)) * ‖(1 + -(x : ℂ) * γ r) ^ (-k)‖
            ≤ (Real.exp (-ω n) * Real.exp (-(δ / Real.sqrt 2) * r)) * (K_k * (1 + r) ^ d_k) :=
              mul_le_mul hexp (hpow_le r hr0) (norm_nonneg _) (by positivity)
          _ = Real.exp (-ω n) * K_k * ((1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r)) := by ring
    have hbd_int : ‖∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)‖ ≤
        Real.exp (-ω n) * K_k * M_r := by
      have h1 := (norm_integral_le_integral_norm _).trans
        (setIntegral_mono_on hint_n.norm (hdom_r.const_mul (Real.exp (-ω n) * K_k)) measurableSet_Ioi fun r hr ↦ by
          have hr0 : 0 ≤ r := (Set.mem_Ioi.mp hr).le
          rw [norm_mul, Complex.norm_exp]
          have hre := (hγ_prop r hr0).1
          have hre_e : (-(ω n : ℂ) * γ r).re = -ω n * (1 + r / Real.sqrt 2) := by simp [Complex.mul_re, hre]
          rw [hre_e]
          have hexp : Real.exp (-ω n * (1 + r / Real.sqrt 2)) ≤ Real.exp (-ω n) * Real.exp (-(δ / Real.sqrt 2) * r) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
            have hr_div : 0 ≤ r / Real.sqrt 2 := div_nonneg hr0 (Real.sqrt_nonneg 2)
            nlinarith [show -ω n * (1 + r / Real.sqrt 2) = -ω n - ω n * (r / Real.sqrt 2) by ring,
                       show -(δ / Real.sqrt 2) * r = -(δ * (r / Real.sqrt 2)) by ring]
          calc Real.exp (-ω n * (1 + r / Real.sqrt 2)) * ‖(1 + -(x : ℂ) * γ r) ^ (-k)‖
              ≤ (Real.exp (-ω n) * Real.exp (-(δ / Real.sqrt 2) * r)) * (K_k * (1 + r) ^ d_k) :=
                mul_le_mul hexp (hpow_le r hr0) (norm_nonneg _) (by positivity)
            _ = Real.exp (-ω n) * K_k * ((1 + r) ^ d_k * Real.exp (-(δ / Real.sqrt 2) * r)) := by ring)
      rwa [integral_const_mul] at h1
    have hexp_n : Real.exp (a * ω n) * Real.exp (-ω n) ≤ (Real.exp (-(1 - a) * δ)) ^ n := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [show a * ω n + -ω n = -(1 - a) * ω n by ring]
    calc ‖c n‖ * ‖∫ r in Set.Ioi (0 : ℝ), Complex.exp (-(ω n : ℂ) * γ r) * (1 + -(x : ℂ) * γ r) ^ (-k)‖
        ≤ (C₀ * Real.exp (a * ω n)) * (Real.exp (-ω n) * K_k * M_r) :=
          mul_le_mul (hc n) hbd_int (norm_nonneg _) (by positivity)
      _ = (C₀ * K_k * M_r) * (Real.exp (a * ω n) * Real.exp (-ω n)) := by ring
      _ ≤ (C₀ * K_k * M_r) * (Real.exp (-(1 - a) * δ)) ^ n :=
          mul_le_mul_of_nonneg_left hexp_n (by positivity)
  have hsm := (hsum_ray gammaMinus
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun r hr ↦ ⟨gammaMinus_re r, by
      dsimp [gammaMinus]
      calc ‖1 + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show -Complex.I * (Real.pi : ℂ) / 4 = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]⟩)
    (fun r hr ↦ by
      have h := one_sub_txy_norm_ge_gammaMinus zero_le_one le_rfl hx0.le hx1 hr
      simp only [Complex.ofReal_one, one_mul] at h; exact ⟨h.1.trans h.2.1, h.2.2⟩)).mul_left
    (Complex.exp (-Complex.I * (Real.pi : ℂ) / 4))
  have hsp := (hsum_ray gammaPlus
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun r hr ↦ ⟨gammaPlus_re r, by
      dsimp [gammaPlus]
      calc ‖1 + (r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖
          ≤ 1 + ‖(r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)‖ := by
            simpa using norm_add_le (1 : ℂ) ((r : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4))
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
                show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, mul_one]⟩)
    (fun r hr ↦ by
      have h := one_sub_txy_norm_ge_gammaPlus zero_le_one le_rfl hx0.le hx1 hr
      simp only [Complex.ofReal_one, one_mul] at h; exact ⟨h.1.trans h.2.1, h.2.2⟩)).mul_left
    (Complex.exp (Complex.I * (Real.pi : ℂ) / 4))
  unfold PhiPlus PhiMinus
  rw [hfub_m, hfub_p, ← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub hsm hsp, ← tsum_mul_left]
  apply tsum_congr; intro n
  have h1 := hankel_single_mode_jump k (hω_pos n) hx0 hx1
  dsimp [PhiPlus, PhiMinus] at h1
  linear_combination c n * h1

/-- **Lemma 5.2 (Termwise `x`-Differentiation Matching `iteratedDeriv_mockModular_mode`)**:
Differentiating the Hankel keyhole jump `j` times with respect to `x ∈ (0, 1/2)` commutes
with the infinite mode sum and yields exact `mockJetQAt k j (ω n)` polynomials! -/
theorem hankel_series_jump_iteratedDeriv (k : ℂ) (c : ℕ → ℂ) (ω : ℕ → ℝ) {δ C₀ a : ℝ}
    (hδ : 0 < δ) (hC₀ : 0 ≤ C₀) (ha : a < 1)
    (hω : ∀ n : ℕ, δ * ((n + 1 : ℕ) : ℝ) ≤ ω n)
    (hc : ∀ n : ℕ, ‖c n‖ ≤ C₀ * Real.exp (a * ω n)) (j : ℕ) :
    ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2),
      iteratedDeriv j (fun t : ℝ ↦
        PhiPlus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(t : ℂ)) -
        PhiMinus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(t : ℂ))) x =
      -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma k) *
        ∑' n : ℕ, c n * (ω n : ℂ) ^ (k - 1) *
          ((x : ℂ) ^ (-k - 2 * (j : ℂ)) * Complex.exp (-(ω n : ℂ) / (x : ℂ)) *
            (mockJetQAt k j (ω n : ℂ)).eval (x : ℂ)) := by
  have hω_pos : ∀ n : ℕ, 0 < ω n := fun n ↦ lt_of_lt_of_le (by positivity) (hω n)
  let pref : ℂ := -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma k)
  let term : ℕ → ℕ → ℝ → ℂ := fun m n t ↦
    c n * (ω n : ℂ) ^ (k - 1) *
      iteratedDeriv m (fun u : ℝ ↦ (u : ℂ) ^ (-k) * Complex.exp (-(ω n : ℂ) / (u : ℂ))) t
  -- Uniform summable majorant for `term m n t` on any `[a₁, b₁] ⊂ (0, 1/2)`!
  have hterm_bd : ∀ (m : ℕ) {a₁ b₁ : ℝ}, 0 < a₁ → a₁ < b₁ → b₁ ≤ 1 / 2 →
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n : ℕ, ∀ t ∈ Set.Ioo a₁ b₁, ‖term m n t‖ ≤ u n := by
    intro m a₁ b₁ ha₁ hab hb₁
    obtain ⟨M_m, hMm, hQbd⟩ := norm_eval_mockJetQAt_le k m
    have hgap : 0 < 2 - a := by linarith
    -- Bound `(ω n)^{k.re - 1} * (1 + ω n)^m ≤ C_ω * exp(((2 - a) / 2) * ω n)`!
    let η : ℝ := (2 - a) / 2
    have hη_pos : 0 < η := by positivity
    let p_deg : ℕ := Nat.ceil (max (k.re - 1) 0) + m
    have hpow_exp : ∃ K_p : ℝ, 0 ≤ K_p ∧ ∀ w : ℝ, δ ≤ w →
        w ^ (k.re - 1) * (1 + w) ^ m ≤ K_p * Real.exp (η * w) := by
      have htend : Tendsto (fun w : ℝ ↦ (1 + w) ^ p_deg * Real.exp (-η * w)) atTop (𝓝 0) := by
        have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p_deg
        have hcomp := h1.comp (tendsto_atTop_add_const_left atTop η (tendsto_id.const_mul_atTop hη_pos))
        have heq : (fun w : ℝ ↦ (1 + w) ^ p_deg * Real.exp (-η * w)) =
            fun w : ℝ ↦ (Real.exp η / η ^ p_deg) * ((η + η * w) ^ p_deg * Real.exp (-(η + η * w))) := by
          ext w
          have hexp : Real.exp (-(η + η * w)) = Real.exp (-η) * Real.exp (-η * w) := by
            rw [show -(η + η * w) = -η + -η * w by ring, Real.exp_add]
          rw [hexp, show η + η * w = η * (1 + w) by ring, mul_pow, Real.exp_neg]
          field_simp [hη_pos.ne', (Real.exp_pos η).ne']
        rw [heq]; simpa using hcomp.const_mul (Real.exp η / η ^ p_deg)
      obtain ⟨W, hW⟩ := (htend.eventually (eventually_le_nhds zero_lt_one)).exists_forall_of_atTop
      let K₁ : ℝ := max 1 ((1 + max δ W) ^ p_deg)
      let K_δ : ℝ := max 1 (δ ^ (k.re - 1))
      refine ⟨K_δ * K₁, by positivity, fun w hw ↦ ?_⟩
      have hw_pos : 0 < w := lt_of_lt_of_le hδ hw
      have hw_pow : w ^ (k.re - 1) ≤ K_δ * (1 + w) ^ Nat.ceil (max (k.re - 1) 0) := by
        by_cases hneg : k.re - 1 ≤ 0
        · have h1 := Real.rpow_le_rpow_of_nonpos hδ hw hneg
          have h2 : (1 : ℝ) ≤ (1 + w) ^ Nat.ceil (max (k.re - 1) 0) := one_le_pow₀ (by linarith)
          exact h1.trans ((le_max_right 1 _).trans (by nlinarith [le_max_left (1 : ℝ) (δ ^ (k.re - 1))]))
        · push Not at hneg
          have h1 : w ^ (k.re - 1) ≤ (1 + w) ^ (k.re - 1) := Real.rpow_le_rpow hw_pos.le (by linarith) hneg.le
          have h2 : (1 + w) ^ (k.re - 1) ≤ (1 + w) ^ (Nat.ceil (max (k.re - 1) 0) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) ((le_max_left _ _).trans (Nat.le_ceil _))
          rw [Real.rpow_natCast] at h2
          exact (h1.trans h2).trans (le_mul_of_one_le_left (by positivity) (le_max_left 1 _))
      have hprod_le : w ^ (k.re - 1) * (1 + w) ^ m ≤ K_δ * (1 + w) ^ p_deg := by
        calc w ^ (k.re - 1) * (1 + w) ^ m
            ≤ (K_δ * (1 + w) ^ Nat.ceil (max (k.re - 1) 0)) * (1 + w) ^ m :=
              mul_le_mul_of_nonneg_right hw_pow (by positivity)
          _ = K_δ * (1 + w) ^ p_deg := by dsimp [p_deg]; rw [pow_add]; ring
      have hp_exp : (1 + w) ^ p_deg ≤ K₁ * Real.exp (η * w) := by
        by_cases hwW : W ≤ w
        · have h1 := hW w hwW
          have h2 : (1 + w) ^ p_deg ≤ 1 * Real.exp (η * w) := by
            have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (η * w)).le
            rwa [mul_assoc, ← Real.exp_add, show -η * w + η * w = 0 by ring, Real.exp_zero, mul_one] at this
          exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left 1 _) (Real.exp_pos _).le)
        · push Not at hwW
          have h1 : (1 + w) ^ p_deg ≤ K₁ :=
            (pow_le_pow_left₀ (by linarith) (by linarith [le_max_right δ W]) p_deg).trans (le_max_right 1 _)
          exact h1.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
      calc w ^ (k.re - 1) * (1 + w) ^ m ≤ K_δ * (1 + w) ^ p_deg := hprod_le
        _ ≤ K_δ * (K₁ * Real.exp (η * w)) := mul_le_mul_of_nonneg_left hp_exp (by positivity)
        _ = (K_δ * K₁) * Real.exp (η * w) := by ring
    obtain ⟨K_p, hKp, hKp_bd⟩ := hpow_exp
    let X_bd : ℝ := max (a₁ ^ (-k.re - 2 * (m : ℝ))) (b₁ ^ (-k.re - 2 * (m : ℝ)))
    let C_tot : ℝ := C₀ * K_p * X_bd * M_m
    refine ⟨fun n ↦ C_tot * (Real.exp (-η * δ)) ^ n,
      (summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by nlinarith))).mul_left _,
      fun n t ht ↦ ?_⟩
    have ht0 : 0 < t := lt_trans ha₁ ht.1
    have ht1 : t ≤ 1 := ht.2.le.trans (by linarith)
    dsimp [term]
    rw [iteratedDeriv_mockModular_mode k (ω n : ℂ) m t ht0, norm_mul, norm_mul, norm_mul, norm_mul]
    have hω_ge1 : δ ≤ ω n := (le_mul_of_one_le_right hδ.le (by exact_mod_cast Nat.succ_pos n)).trans (hω n)
    have hω_gen : δ * (n : ℝ) ≤ ω n :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hδ.le).trans (hω n)
    have hω_cp : ‖(ω n : ℂ) ^ (k - 1)‖ = (ω n) ^ (k.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hω_pos n)]; simp
    have ht_cp : ‖(t : ℂ) ^ (-k - 2 * (m : ℂ))‖ ≤ X_bd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-k - 2 * (m : ℂ)).re = -k.re - 2 * (m : ℝ) := by simp
      rw [hre]
      by_cases hexp : 0 ≤ -k.re - 2 * (m : ℝ)
      · exact (Real.rpow_le_rpow ht0.le ht.2.le hexp).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos ha₁ ht.1.le (not_le.mp hexp).le).trans (le_max_left _ _)
    have hexp_t : ‖Complex.exp (-(ω n : ℂ) / (t : ℂ))‖ ≤ Real.exp (-2 * ω n) := by
      rw [Complex.norm_exp]
      have hre : (-(ω n : ℂ) / (t : ℂ)).re = -(ω n / t) := by
        rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]; ring
      rw [hre]; apply Real.exp_le_exp.mpr
      have h2t : 2 ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith [ht.2, hb₁]
      nlinarith [hω_pos n, show ω n / t = ω n * (1 / t) by ring]
    have hQ := hQbd (ω n) t (hω_pos n).le ht0.le ht1
    have hcomb_exp : Real.exp (a * ω n) * Real.exp (η * ω n) * Real.exp (-2 * ω n) ≤ (Real.exp (-η * δ)) ^ n := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have heq : a * ω n + η * ω n + -2 * ω n = -η * ω n := by dsimp [η]; ring
      rw [heq]; nlinarith
    calc ‖c n‖ * ‖(ω n : ℂ) ^ (k - 1)‖ * (‖(t : ℂ) ^ (-k - 2 * (m : ℂ))‖ *
            ‖Complex.exp (-(ω n : ℂ) / (t : ℂ))‖ * ‖(mockJetQAt k m (ω n : ℂ)).eval (t : ℂ)‖)
        ≤ (C₀ * Real.exp (a * ω n)) * (ω n) ^ (k.re - 1) *
            (X_bd * Real.exp (-2 * ω n) * (M_m * (1 + ω n) ^ m)) := by
          rw [hω_cp]
          have h1 : ‖c n‖ * (ω n) ^ (k.re - 1) ≤ (C₀ * Real.exp (a * ω n)) * (ω n) ^ (k.re - 1) :=
            mul_le_mul_of_nonneg_right (hc n) (Real.rpow_nonneg (hω_pos n).le _)
          have h2 : ‖(t : ℂ) ^ (-k - 2 * (m : ℂ))‖ * ‖Complex.exp (-(ω n : ℂ) / (t : ℂ))‖ *
                ‖(mockJetQAt k m (ω n : ℂ)).eval (t : ℂ)‖ ≤
              X_bd * Real.exp (-2 * ω n) * (M_m * (1 + ω n) ^ m) :=
            mul_le_mul (mul_le_mul ht_cp hexp_t (norm_nonneg _) (by positivity)) hQ (norm_nonneg _) (by positivity)
          exact mul_le_mul h1 h2 (by positivity)
            (mul_nonneg (by positivity) (Real.rpow_nonneg (hω_pos n).le _))
      _ = C₀ * X_bd * M_m * ((ω n) ^ (k.re - 1) * (1 + ω n) ^ m) *
            (Real.exp (a * ω n) * Real.exp (-2 * ω n)) := by ring
      _ ≤ C₀ * X_bd * M_m * (K_p * Real.exp (η * ω n)) *
            (Real.exp (a * ω n) * Real.exp (-2 * ω n)) := by
          have := mul_le_mul_of_nonneg_left (hKp_bd (ω n) hω_ge1) (show 0 ≤ C₀ * X_bd * M_m by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = C_tot * (Real.exp (a * ω n) * Real.exp (η * ω n) * Real.exp (-2 * ω n)) := by dsimp [C_tot]; ring
      _ ≤ C_tot * (Real.exp (-η * δ)) ^ n := mul_le_mul_of_nonneg_left hcomb_exp (by positivity)
  -- Induction on `j` using `hasDerivAt_tsum_of_isPreconnected`!
  have hmain : ∀ m : ℕ, ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2),
      iteratedDeriv m (fun t : ℝ ↦
        PhiPlus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(t : ℂ)) -
        PhiMinus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(t : ℂ))) x =
      pref * ∑' n : ℕ, term m n x := by
    intro m
    induction m with
    | zero =>
      intro x hx
      rw [iteratedDeriv_zero, hankel_series_jump k c ω hδ hC₀ ha hω hc hx.1 hx.2.le]
      congr 1; apply tsum_congr; intro n; dsimp [term]; rw [iteratedDeriv_zero]; ring
    | succ m ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv m (fun t : ℝ ↦
          PhiPlus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(t : ℂ)) -
          PhiMinus k (fun y ↦ ∑' n : ℕ, c n * Complex.exp (-(ω n : ℂ) * y)) (-(t : ℂ))) =ᶠ[𝓝 x]
          fun t : ℝ ↦ pref * ∑' n : ℕ, term m n t := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht; exact ih t ht
      rw [hev.deriv_eq]
      let a₁ : ℝ := x / 2
      let b₁ : ℝ := (x + 1 / 2) / 2
      have ha₁ : 0 < a₁ := by dsimp [a₁]; linarith [hx.1]
      have hab : a₁ < b₁ := by dsimp [a₁, b₁]; linarith [hx.1, hx.2]
      have hb₁ : b₁ ≤ 1 / 2 := by dsimp [b₁]; linarith [hx.2]
      have hx_mem : x ∈ Set.Ioo a₁ b₁ := ⟨by dsimp [a₁]; linarith [hx.1], by dsimp [b₁]; linarith [hx.2]⟩
      obtain ⟨u_bd, hu_sum, hbd_succ⟩ := hterm_bd (m + 1) ha₁ hab hb₁
      obtain ⟨u_m, hum_sum, hbd_m⟩ := hterm_bd m ha₁ hab hb₁
      have hderiv_n : ∀ n : ℕ, ∀ t ∈ Set.Ioo a₁ b₁, HasDerivAt (term m n) (term (m + 1) n t) t := by
        intro n t ht
        have ht0 : 0 < t := lt_trans ha₁ ht.1
        have hdiff_m : DifferentiableAt ℝ (iteratedDeriv m (fun u : ℝ ↦ (u : ℂ) ^ (-k) * Complex.exp (-(ω n : ℂ) / (u : ℂ)))) t := by
          have heq_f : iteratedDeriv m (fun u : ℝ ↦ (u : ℂ) ^ (-k) * Complex.exp (-(ω n : ℂ) / (u : ℂ))) =ᶠ[𝓝 t]
              fun u : ℝ ↦ (u : ℂ) ^ (-k - 2 * (m : ℂ)) * Complex.exp (-(ω n : ℂ) / (u : ℂ)) *
                (mockJetQAt k m (ω n : ℂ)).eval (u : ℂ) := by
            filter_upwards [eventually_gt_nhds ht0] with u hu
            exact iteratedDeriv_mockModular_mode k (ω n : ℂ) m u hu
          refine DifferentiableAt.congr_of_eventuallyEq ?_ heq_f
          have hsl : (t : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl ht0)
          have h1 : DifferentiableAt ℝ (fun u : ℝ ↦ (u : ℂ) ^ (-k - 2 * (m : ℂ))) t :=
            (((hasDerivAt_id (t : ℂ)).cpow_const hsl).comp_ofReal).differentiableAt
          have h2 : DifferentiableAt ℝ (fun u : ℝ ↦ Complex.exp (-(ω n : ℂ) / (u : ℂ))) t :=
            (((((hasDerivAt_inv (Complex.ofReal_ne_zero.mpr ht0.ne')).const_mul (-(ω n : ℂ))).congr_of_eventuallyEq
              (Eventually.of_forall fun z ↦ by simp [div_eq_mul_inv])).cexp).comp_ofReal).differentiableAt
          have h3 : DifferentiableAt ℝ (fun u : ℝ ↦ (mockJetQAt k m (ω n : ℂ)).eval (u : ℂ)) t :=
            ((hasDerivAt_poly_eval (mockJetQAt k m (ω n : ℂ)) (t : ℂ)).comp_ofReal).differentiableAt
          exact (h1.mul h2).mul h3
        dsimp [term]; rw [iteratedDeriv_succ]
        exact hdiff_m.hasDerivAt.const_mul _
      have hsum_x : Summable (fun n : ℕ ↦ term m n x) :=
        Summable.of_norm_bounded hum_sum (fun n ↦ hbd_m n x hx_mem)
      have hhd := (hasDerivAt_tsum_of_isPreconnected hu_sum isOpen_Ioo isPreconnected_Ioo
        hderiv_n hbd_succ hx_mem hsum_x hx_mem).const_mul pref
      exact hhd.deriv
  intro x hx
  rw [hmain j x hx]
  congr 1; apply tsum_congr; intro n
  dsimp [term]
  rw [iteratedDeriv_mockModular_mode k (ω n : ℂ) j x hx.1]

end
end CubicTheta.AllD
