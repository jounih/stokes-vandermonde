module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.HigherOrderStrongDTrans
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Unconditional Hyperbolic Selberg–Stokes–Vandermonde Theorem

This module formalizes the **Unconditional Hyperbolic Selberg–Stokes–Vandermonde Theorem**
(Module 1 of Theory 2: Geometry–Compression Trichotomy) for any compact hyperbolic Riemann
surface `M = ℍ² / Γ` of genus `g ≥ 2`, with **zero Riemann Hypothesis assumption** and
**zero eigenvalue-simplicity assumption**.

## Mathematical Architecture
1. **Compact Hyperbolic Selberg Data (`CompactHyperbolicSelbergData`)**:
   Encapsulates an entire Selberg zeta function `Z : ℂ → ℂ` on a compact genus `g ≥ 2` hyperbolic
   surface satisfying:
   - `Z_entire`: `Z` is entire on `ℂ`,
   - `selberg_rh`: unconditional Selberg RH (self-adjointness of `-Δ_M`) — every non-real zero
     lies strictly on `Re s = 1 / 2`,
   - `smallRealZeros`: finitely many real zeros in `(0, 1]` (ground state `s = 1` and any small
     eigenvalues `0 < λ_j ≤ 1 / 4`, including `s = 1 / 2` if `λ = 1 / 4` occurs),
   - `crit_infinite`: unconditional Weyl's law — infinitely many distinct critical-line zeros
     `1 / 2 + i r` with `r > 0`,
   - `right_bound`: uniform geodesic Dirichlet-series bound on `Re s ≥ 3 / 2`,
   - `func_eq`: exact Selberg functional equation on `s.im ≠ 0`:
     `Z'(1 - s) / Z(1 - s) + Z'(s) / Z(s) = -(2g - 2) π (2s - 1) cot(π s)`,
     equivalently at `s = 1 / 2 + ξ`:
     `Z'(1 / 2 - ξ) / Z(1 / 2 - ξ) + Z'(1 / 2 + ξ) / Z(1 / 2 + ξ) = (2g - 2) · 2πξ tan(πξ)`.
2. **Entire Regularization & Pole-Subtracted Kernel (`Zreg`, `phiSelbergRaw`, `phiSelberg`)**:
   - Factors out the exact finite vanishing polynomial
     `smallPoly D s = ∏ x ∈ D.smallRealZeros, (s - x)^{m_x}` (`m_x = analyticOrderNatAt D.Z x`)
     from `D.Z` to obtain an entire quotient `Zreg D` that is nonvanishing on every
     `x ∈ D.smallRealZeros` and everywhere in `{s | 0 < s.re ∧ s.im = 0}`.
   - Defines `phiSelberg D ξ := deriv (Zreg D) (1 / 2 + ξ) / Zreg D (1 / 2 + ξ)`, which agrees
     identically with the pole-subtracted logarithmic derivative
     `phiSelbergRaw D ξ := deriv D.Z (1/2 + ξ) / D.Z (1/2 + ξ) - ∑ x ∈ D.smallRealZeros, m_x / (ξ - (x - 1/2))`
     at every `ξ` where `D.Z (1 / 2 + ξ) ≠ 0`, and analytically continues across every removable
     singularity `ξ = x - 1 / 2` (including `ξ = 0` when `λ = 1 / 4` occurs and `ξ = 1 / 2` when
     `λ₀ = 0` occurs).
3. **Unbounded Critical-Line Spectral Sequence & Simple Poles (`rSeq`, `selbergMult`)**:
   - Constructs the canonical strictly increasing enumeration `rSeq D : ℕ → ℝ` of all positive
     critical-line zero ordinates with `0 < rSeq D 0`, `StrictMono (rSeq D)`, and
     `Tendsto (rSeq D) atTop atTop` via compactness + isolated zeros.
   - Proves simple-pole principal parts `+(selbergMult D r) / (ξ - i r)` with
     `1 ≤ selbergMult D r = analyticOrderNatAt D.Z (1 / 2 + i r)` (arbitrary multiplicity).
   - Proves holomorphicity on the entire `rotatedPuncturedWedge (π / 2) α₀ ε (rSeq D)`,
     automatically avoiding all negative-real-axis trivial zeros.
4. **Elementary Flanking-Ray Growth Bounds (No Digamma Needed)**:
   - Right flanking ray `θ₀ - θ = π / 2 - π / 8` (and positive real axis `σ = 0`): `O(1)` via
     `D.right_bound`.
   - Left flanking ray `θ₀ + θ = π / 2 + π / 8`: `O(v)` via `D.func_eq`, `D.right_bound`, and
     the elementary upper-half-plane strip bound `‖Complex.tan z‖ ≤ 2` for `1 ≤ z.im`.
5. **Master Unconditional Strong Differential Transcendence Theorems**:
   Packages `phiSelberg_higherOrderBorelData D : HigherOrderBorelData ...` and proves:
   - `selberg_ogf_stronglyDTrans`: `ogfOfEGF (phiSelberg D)` is strongly D-transcendental over
     convergent meromorphic germs `ℂ({t})`,
   - `selberg_formalSeries_stronglyDTrans`: `formalSeries (phiSelberg D)` is strongly
     D-transcendental over `ℂ({t})`,
   - `selberg_laplace_no_conv_ade` and `selberg_laplace_no_rat_ade`: the regularized real-axis
     Laplace integral `G_Selberg_laplace D` satisfies no nonzero convergent-germ or rational ADE
     eventually as `u → +∞`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.SelbergHyperbolicDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.HigherOrderStokes
open PakPrimes.FishburnStrongDTrans
open PakPrimes.PakYeliussizovEGF
open PakPrimes.HigherOrderStrongDTrans
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Public Specification: `CompactHyperbolicSelbergData` -/

/-- Analytic data of the Selberg zeta function `Z_Γ` of a compact hyperbolic surface
`M = ℍ² / Γ` of genus `g ≥ 2`. Every field holds unconditionally for every cocompact
torsion-free Fuchsian group `Γ ⊂ PSL₂(ℝ)` (Selberg 1956; Hejhal 1976). -/
structure CompactHyperbolicSelbergData where
  /-- Genus `g ≥ 2` of the compact hyperbolic surface `M = ℍ² / Γ`. -/
  g : ℕ
  hg : 2 ≤ g
  /-- The entire Selberg zeta function `Z_Γ : ℂ → ℂ`. -/
  Z : ℂ → ℂ
  Z_entire : Differentiable ℂ Z
  /-- Unconditional Selberg RH (self-adjointness of `-Δ_M`): every non-real zero lies on `Re s = 1 / 2`. -/
  selberg_rh : ∀ s : ℂ, Z s = 0 → s.im ≠ 0 → s.re = 1 / 2
  /-- Finitely many real zeros of `Z` in `(0, 1]` (ground state `s = 1` and any small eigenvalues `0 < λ ≤ 1 / 4`). -/
  smallRealZeros : Finset ℝ
  smallRealZeros_mem : ∀ x ∈ smallRealZeros, 0 < x ∧ x ≤ 1
  real_zeros_classified : ∀ x : ℝ, 0 < x → Z (x : ℂ) = 0 → x ∈ smallRealZeros
  /-- Unconditional Weyl's law: infinitely many distinct critical-line zeros `1 / 2 + i r` (`r > 0`). -/
  crit_infinite : {r : ℝ | 0 < r ∧ Z (1 / 2 + I * (r : ℂ)) = 0}.Infinite
  /-- Geodesic Dirichlet-series uniform bound on `Re s ≥ 3 / 2` (positive systole). -/
  right_bound : ∃ C : ℝ, ∀ s : ℂ, 3 / 2 ≤ s.re → Z s ≠ 0 ∧ ‖deriv Z s / Z s‖ ≤ C
  /-- Exact Selberg functional equation off the real axis (`s.im ≠ 0`):
  `Z'(1 - s) / Z(1 - s) + Z'(s) / Z(s) = -(2g - 2) π (2s - 1) cot(π s)`,
  equivalently `Z'(1/2 - ξ)/Z(1/2 - ξ) + Z'(1/2 + ξ)/Z(1/2 + ξ) = (2g - 2) · 2πξ tan(πξ)`. -/
  func_eq : ∀ s : ℂ, s.im ≠ 0 → Z s ≠ 0 → Z (1 - s) ≠ 0 →
    deriv Z (1 - s) / Z (1 - s) + deriv Z s / Z s =
      -((2 * g - 2 : ℕ) : ℂ) * (Real.pi : ℂ) * (2 * s - 1) * Complex.cot ((Real.pi : ℂ) * s)

/-! ### 2. Elementary Trigonometric Strip Bounds & Shifted Functional Equation -/

/-- Elementary upper-half-plane strip bound: `‖Complex.cot w‖ ≤ 2` whenever `1 ≤ w.im`. -/
theorem norm_cot_le_two_of_one_le_im {w : ℂ} (hw : 1 ≤ w.im) :
    ‖Complex.cot w‖ ≤ 2 := by
  rw [Complex.cot, Complex.cos, Complex.sin]
  have hnum : ((Complex.exp (w * I) + Complex.exp (-w * I)) / 2) /
      ((Complex.exp (-w * I) - Complex.exp (w * I)) * I / 2) =
      (Complex.exp (w * I) + Complex.exp (-w * I)) /
        ((Complex.exp (-w * I) - Complex.exp (w * I)) * I) := by
    field_simp
  rw [hnum, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hre1 : (w * I).re = -w.im := by simp [Complex.mul_re]
  have hre2 : (-w * I).re = w.im := by simp [Complex.mul_re]
  have hn1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp, hre1]
  have hn2 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by rw [Complex.norm_exp, hre2]
  have hexp_pos : 0 < Real.exp w.im := Real.exp_pos _
  have hle_ratio : Real.exp (-w.im) ≤ Real.exp w.im / 3 := by
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hmul : Real.exp (-w.im) * 3 ≤ Real.exp w.im := by
      calc Real.exp (-w.im) * 3 ≤ Real.exp (-w.im) * Real.exp 2 :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = Real.exp (-w.im + 2) := (Real.exp_add _ _).symm
        _ ≤ Real.exp w.im := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hnum_le : ‖Complex.exp (w * I) + Complex.exp (-w * I)‖ ≤ (4 / 3 : ℝ) * Real.exp w.im := by
    calc ‖Complex.exp (w * I) + Complex.exp (-w * I)‖
        ≤ ‖Complex.exp (w * I)‖ + ‖Complex.exp (-w * I)‖ := norm_add_le _ _
      _ = Real.exp (-w.im) + Real.exp w.im := by rw [hn1, hn2]
      _ ≤ (4 / 3 : ℝ) * Real.exp w.im := by linarith
  have hden_ge : (2 / 3 : ℝ) * Real.exp w.im ≤ ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ := by
    have htri : ‖Complex.exp (-w * I)‖ - ‖Complex.exp (w * I)‖ ≤
        ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ :=
      norm_sub_norm_le (Complex.exp (-w * I)) (Complex.exp (w * I))
    rw [hn1, hn2] at htri
    linarith
  have hden_pos : 0 < (2 / 3 : ℝ) * Real.exp w.im := by positivity
  calc ‖Complex.exp (w * I) + Complex.exp (-w * I)‖ /
        ‖Complex.exp (-w * I) - Complex.exp (w * I)‖
      ≤ ((4 / 3 : ℝ) * Real.exp w.im) / ((2 / 3 : ℝ) * Real.exp w.im) :=
        div_le_div₀ (by positivity) hnum_le hden_pos hden_ge
    _ = 2 := by field_simp [hexp_pos.ne']; ring

/-- Half-period shift identity `cot(π/2 + z) = -tan(z)`. -/
theorem cot_pi_div_two_add (z : ℂ) :
    Complex.cot ((Real.pi : ℂ) / 2 + z) = -Complex.tan z := by
  rw [Complex.cot, add_comm ((Real.pi : ℂ) / 2) z, Complex.cos_add_pi_div_two,
    Complex.sin_add_pi_div_two, neg_div, Complex.tan_eq_sin_div_cos]

/-- Elementary upper-half-plane strip bound: `‖Complex.tan z‖ ≤ 2` whenever `1 ≤ z.im`. -/
theorem norm_tan_le_two_of_one_le_im {z : ℂ} (hz : 1 ≤ z.im) :
    ‖Complex.tan z‖ ≤ 2 := by
  have heq : Complex.tan z = -Complex.cot ((Real.pi : ℂ) / 2 + z) := by
    rw [cot_pi_div_two_add, neg_neg]
  rw [heq, norm_neg]
  refine norm_cot_le_two_of_one_le_im ?_
  simpa [Complex.add_im] using hz

/-- Critical-line form of the Selberg functional equation at `s = 1 / 2 + ξ`:
`Z'(1/2 - ξ)/Z(1/2 - ξ) + Z'(1/2 + ξ)/Z(1/2 + ξ) = (2g - 2) · 2πξ tan(πξ)`. -/
theorem func_eq_critical_shift (D : CompactHyperbolicSelbergData) {ξ : ℂ}
    (hξ : ξ.im ≠ 0) (hZ1 : D.Z (1 / 2 + ξ) ≠ 0) (hZ2 : D.Z (1 / 2 - ξ) ≠ 0) :
    deriv D.Z (1 / 2 - ξ) / D.Z (1 / 2 - ξ) + deriv D.Z (1 / 2 + ξ) / D.Z (1 / 2 + ξ) =
      ((2 * D.g - 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * ξ) * Complex.tan ((Real.pi : ℂ) * ξ) := by
  have hs_im : ((1 / 2 : ℂ) + ξ).im ≠ 0 := by
    simpa [Complex.add_im] using hξ
  have h1sub : (1 : ℂ) - ((1 / 2 : ℂ) + ξ) = 1 / 2 - ξ := by ring
  have hfe := D.func_eq (1 / 2 + ξ) hs_im hZ1 (by rwa [h1sub])
  rw [h1sub] at hfe
  rw [hfe]
  have hpi : (Real.pi : ℂ) * (1 / 2 + ξ) = (Real.pi : ℂ) / 2 + (Real.pi : ℂ) * ξ := by ring
  rw [hpi, cot_pi_div_two_add]
  ring

/-! ### 3. Entire Regularization Across `smallRealZeros` and the Borel Kernel `phiSelberg` -/

lemma Z_analyticOnNhd (D : CompactHyperbolicSelbergData) :
    AnalyticOnNhd ℂ D.Z Set.univ :=
  D.Z_entire.differentiableOn.analyticOnNhd isOpen_univ

private lemma entire_analyticOrderAt_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : ∃ s₀ : ℂ, f s₀ ≠ 0) (a : ℂ) :
    analyticOrderAt f a ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hf_an : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hzero := hf_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ a) htop
  obtain ⟨s₀, hs₀⟩ := hf_ne
  exact hs₀ (hzero (Set.mem_univ s₀))

lemma Z_analyticOrderAt_ne_top (D : CompactHyperbolicSelbergData) (s : ℂ) :
    analyticOrderAt D.Z s ≠ ⊤ := by
  obtain ⟨_, hC⟩ := D.right_bound
  exact entire_analyticOrderAt_ne_top D.Z_entire ⟨2, (hC 2 (by norm_num)).1⟩ s

private lemma exists_entire_factor_single {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : ∃ s₀ : ℂ, f s₀ ≠ 0) (a : ℂ) :
    ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      (∀ s : ℂ, f s = (s - a) ^ analyticOrderNatAt f a * F s) ∧
      F a ≠ 0 := by
  have hf_an : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hne_top : analyticOrderAt f a ≠ ⊤ := entire_analyticOrderAt_ne_top hf hf_ne a
  obtain ⟨g, hg_ana, hg_ne, hfg⟩ := (hf_an a (Set.mem_univ a)).analyticOrderAt_ne_top.mp hne_top
  let m : ℕ := analyticOrderNatAt f a
  let F : ℂ → ℂ := fun z => if z = a then g a else f z / (z - a) ^ m
  have hFg : F =ᶠ[𝓝 a] g := by
    filter_upwards [hfg] with z hz
    dsimp only [F]
    by_cases hza : z = a
    · subst hza; simp
    · simp only [hza, ↓reduceIte]
      have hz' : f z = (z - a) ^ m * g z := by simpa [m, smul_eq_mul] using hz
      have hpow : (z - a) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hza)
      rw [hz', mul_div_cancel_left₀ _ hpow]
  have hF_diff : Differentiable ℂ F := by
    intro z
    by_cases hza : z = a
    · subst hza
      exact (hg_ana.congr hFg.symm).differentiableAt
    · have hFz : F =ᶠ[𝓝 z] fun w => f w / (w - a) ^ m := by
        filter_upwards [isOpen_ne.mem_nhds hza] with w hwa
        simp [F, hwa]
      have hdiv : DifferentiableAt ℂ (fun w => f w / (w - a) ^ m) z :=
        (hf z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow m)
          (pow_ne_zero m (sub_ne_zero.mpr hza))
      exact hdiv.congr_of_eventuallyEq hFz
  have hF_eq : ∀ s : ℂ, f s = (s - a) ^ m * F s := by
    intro s
    by_cases hsa : s = a
    · subst hsa
      have h0 := hfg.self_of_nhds
      simpa [F, m, smul_eq_mul] using h0
    · simp only [F, hsa, ↓reduceIte]
      have hpow : (s - a) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hsa)
      rw [mul_div_cancel₀ _ hpow]
  refine ⟨F, hF_diff, hF_eq, by simpa [F] using hg_ne⟩

private lemma exists_entire_factor_finset {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : ∃ s₀ : ℂ, f s₀ ≠ 0) (S : Finset ℝ) :
    ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      (∀ s : ℂ, f s = (∏ x ∈ S, (s - (x : ℂ)) ^ analyticOrderNatAt f (x : ℂ)) * F s) ∧
      (∀ x ∈ S, F (x : ℂ) ≠ 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨f, hf, fun s => by simp, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | @insert a S ha ih =>
    obtain ⟨F₁, hF₁_diff, hF₁_eq, hF₁_ne⟩ := ih
    let Q : ℂ → ℂ := fun s => ∏ x ∈ S, (s - (x : ℂ)) ^ analyticOrderNatAt f (x : ℂ)
    have hF₁_notzero : ∃ s₀ : ℂ, F₁ s₀ ≠ 0 := by
      obtain ⟨s₀, hs₀⟩ := hf_ne
      refine ⟨s₀, fun h0 => hs₀ ?_⟩
      rw [hF₁_eq s₀, h0, mul_zero]
    have hQ_an : AnalyticAt ℂ Q (a : ℂ) := by
      refine Finset.analyticAt_fun_prod S fun x _ => ?_
      exact (analyticAt_id.sub analyticAt_const).pow _
    have hQ_ne : Q (a : ℂ) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ (sub_ne_zero.mpr ?_)
      intro heq
      have hax : a = x := Complex.ofReal_injective heq
      exact ha (hax ▸ hx)
    have hF₁_an : AnalyticAt ℂ F₁ (a : ℂ) :=
      (hF₁_diff.differentiableOn.analyticOnNhd isOpen_univ) (a : ℂ) (Set.mem_univ _)
    have hord_eq : analyticOrderNatAt F₁ (a : ℂ) = analyticOrderNatAt f (a : ℂ) := by
      have hf_eq_fn : f = Q * F₁ := funext hF₁_eq
      have hord : analyticOrderAt f (a : ℂ) = analyticOrderAt F₁ (a : ℂ) := by
        rw [hf_eq_fn, analyticOrderAt_mul hQ_an hF₁_an, hQ_an.analyticOrderAt_eq_zero.mpr hQ_ne,
          zero_add]
      simp only [analyticOrderNatAt, hord]
    obtain ⟨F₂, hF₂_diff, hF₂_eq, hF₂_ne⟩ := exists_entire_factor_single hF₁_diff hF₁_notzero (a : ℂ)
    refine ⟨F₂, hF₂_diff, fun s => ?_, fun x hx => ?_⟩
    · rw [hF₁_eq s, hF₂_eq s, hord_eq, Finset.prod_insert ha]
      ring
    · rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact hF₂_ne
      · intro h0
        apply hF₁_ne x hxS
        rw [hF₂_eq (x : ℂ), h0, mul_zero]

/-- Finite vanishing polynomial capturing all real zeros of `D.Z` in `D.smallRealZeros`
with their exact vanishing multiplicities. -/
@[expose] def smallPoly (D : CompactHyperbolicSelbergData) (s : ℂ) : ℂ :=
  ∏ x ∈ D.smallRealZeros, (s - (x : ℂ)) ^ analyticOrderNatAt D.Z (x : ℂ)

private lemma exists_Zreg (D : CompactHyperbolicSelbergData) :
    ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      (∀ s : ℂ, D.Z s = smallPoly D s * F s) ∧
      (∀ x ∈ D.smallRealZeros, F (x : ℂ) ≠ 0) := by
  obtain ⟨_, hC⟩ := D.right_bound
  exact exists_entire_factor_finset D.Z_entire ⟨2, (hC 2 (by norm_num)).1⟩ D.smallRealZeros

/-- Entire regularized Selberg zeta function obtained by dividing `D.Z` by `smallPoly D`. -/
def Zreg (D : CompactHyperbolicSelbergData) : ℂ → ℂ :=
  Classical.choose (exists_Zreg D)

lemma Zreg_differentiable (D : CompactHyperbolicSelbergData) :
    Differentiable ℂ (Zreg D) :=
  (Classical.choose_spec (exists_Zreg D)).1

lemma Zreg_analyticOnNhd (D : CompactHyperbolicSelbergData) :
    AnalyticOnNhd ℂ (Zreg D) Set.univ :=
  (Zreg_differentiable D).differentiableOn.analyticOnNhd isOpen_univ

lemma Z_eq_smallPoly_mul_Zreg (D : CompactHyperbolicSelbergData) (s : ℂ) :
    D.Z s = smallPoly D s * Zreg D s :=
  (Classical.choose_spec (exists_Zreg D)).2.1 s

lemma Zreg_ne_zero_of_mem_smallRealZeros (D : CompactHyperbolicSelbergData)
    {x : ℝ} (hx : x ∈ D.smallRealZeros) : Zreg D (x : ℂ) ≠ 0 :=
  (Classical.choose_spec (exists_Zreg D)).2.2 x hx

lemma Zreg_ne_zero_of_re_pos_im_zero (D : CompactHyperbolicSelbergData) {s : ℂ}
    (hre : 0 < s.re) (him : s.im = 0) : Zreg D s ≠ 0 := by
  have hs_real : s = (s.re : ℂ) := Complex.ext rfl (by simp [him])
  by_cases hmem : s.re ∈ D.smallRealZeros
  · rw [hs_real]
    exact Zreg_ne_zero_of_mem_smallRealZeros D hmem
  · intro h0
    have hZ0 : D.Z (s.re : ℂ) = 0 := by
      rw [← hs_real, Z_eq_smallPoly_mul_Zreg, h0, mul_zero]
    exact hmem (D.real_zeros_classified s.re hre hZ0)

lemma Zreg_ne_zero_of_re_ne_half (D : CompactHyperbolicSelbergData) {s : ℂ}
    (hre : s.re ≠ 1 / 2) (htriv : 0 < s.re ∨ s.im ≠ 0) : Zreg D s ≠ 0 := by
  by_cases him : s.im = 0
  · exact Zreg_ne_zero_of_re_pos_im_zero D (htriv.resolve_right (not_not.mpr him)) him
  · intro h0
    have hZ0 : D.Z s = 0 := by rw [Z_eq_smallPoly_mul_Zreg, h0, mul_zero]
    exact hre (D.selberg_rh s hZ0 him)

lemma Zreg_half_ne_zero (D : CompactHyperbolicSelbergData) :
    Zreg D (1 / 2 : ℂ) ≠ 0 :=
  Zreg_ne_zero_of_re_pos_im_zero D (by norm_num) (by simp)

private lemma exists_Zreg_zero_free_ball_half (D : CompactHyperbolicSelbergData) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : ℂ, ‖ξ‖ < ε → Zreg D (1 / 2 + ξ) ≠ 0 := by
  have hcont : ContinuousAt (fun ξ : ℂ => Zreg D (1 / 2 + ξ)) 0 :=
    ContinuousAt.comp (g := Zreg D) (f := fun ξ : ℂ => (1 / 2 : ℂ) + ξ)
      (Zreg_differentiable D (1 / 2 + 0)).continuousAt (continuousAt_const.add continuousAt_id)
  have hev : ∀ᶠ ξ : ℂ in 𝓝 (0 : ℂ), Zreg D (1 / 2 + ξ) ≠ 0 :=
    hcont.eventually_ne (by simpa using Zreg_half_ne_zero D)
  obtain ⟨ε, hε_pos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨ε, hε_pos, fun ξ hξ => hε (by simpa [dist_eq_norm] using hξ)⟩

/-- Raw pole-subtracted critical-line Selberg logarithmic derivative:
`Φ_Γ^{raw}(ξ) = Z'(1/2 + ξ)/Z(1/2 + ξ) - ∑_{x ∈ smallRealZeros} m_x / (ξ - (x - 1/2))`. -/
@[expose] def phiSelbergRaw (D : CompactHyperbolicSelbergData) (ξ : ℂ) : ℂ :=
  deriv D.Z (1 / 2 + ξ) / D.Z (1 / 2 + ξ) -
    ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1 / 2))

/-- Analytic continuation of `phiSelbergRaw D` across all finitely many removable singularities
`ξ = x - 1 / 2` (`x ∈ D.smallRealZeros`), defined via the entire quotient `Zreg D`:
`Φ_Γ(ξ) = Zreg'(1/2 + ξ) / Zreg(1/2 + ξ)`. -/
@[expose] def phiSelberg (D : CompactHyperbolicSelbergData) (ξ : ℂ) : ℂ :=
  deriv (Zreg D) (1 / 2 + ξ) / Zreg D (1 / 2 + ξ)

/-- Formal geodesic von Mangoldt Borel–Laplace series
`G_{Λ,Γ}(u) = ∑_{k ≥ 0} Φ_Γ^{(k)}(0) u^{-(k+1)} ∈ ℂ[[1/u]]`. -/
@[expose] def G_Selberg (D : CompactHyperbolicSelbergData) : PowerSeries ℂ :=
  formalSeries (phiSelberg D)

/-- Regularized real-axis Selberg Laplace integral
`G_{Λ,Γ}^{laplace}(u) = ∫_0^∞ e^{-u ξ} Φ_Γ(ξ) dξ` (`u > 0`). -/
@[expose] def G_Selberg_laplace (D : CompactHyperbolicSelbergData) (u : ℝ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (ξ : ℂ)) * phiSelberg D (ξ : ℂ)

private lemma deriv_finset_pow_div {S : Finset ℝ} {m : ℝ → ℕ} {s : ℂ}
    (hs : ∀ x ∈ S, m x ≠ 0 → s ≠ (x : ℂ)) :
    (∏ x ∈ S, (s - (x : ℂ)) ^ m x) ≠ 0 ∧
      deriv (fun w : ℂ => ∏ x ∈ S, (w - (x : ℂ)) ^ m x) s /
        (∏ x ∈ S, (s - (x : ℂ)) ^ m x) =
      ∑ x ∈ S, ((m x : ℕ) : ℂ) / (s - (x : ℂ)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [deriv_const]
  | @insert a S ha ih =>
    have hsS : ∀ x ∈ S, m x ≠ 0 → s ≠ (x : ℂ) := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨hQ_ne, hQ_ld⟩ := ih hsS
    let f : ℂ → ℂ := fun w => (w - (a : ℂ)) ^ m a
    let Q : ℂ → ℂ := fun w => ∏ x ∈ S, (w - (x : ℂ)) ^ m x
    have hf_diff : DifferentiableAt ℂ f s :=
      ((differentiableAt_id).sub (differentiableAt_const (a : ℂ))).pow (m a)
    have hQ_diff : DifferentiableAt ℂ Q s := by
      have hQ_an : AnalyticAt ℂ Q s :=
        Finset.analyticAt_fun_prod S fun x _ => (analyticAt_id.sub analyticAt_const).pow _
      exact hQ_an.differentiableAt
    have hf_ne : f s ≠ 0 := by
      dsimp only [f]
      by_cases hm : m a = 0
      · simp [hm]
      · exact pow_ne_zero (m a) (sub_ne_zero.mpr (hs a (Finset.mem_insert_self a S) hm))
    have hf_ld : deriv f s / f s = ((m a : ℕ) : ℂ) / (s - (a : ℂ)) := by
      dsimp only [f]
      by_cases hm : m a = 0
      · simp [hm]
      · have hsa : s - (a : ℂ) ≠ 0 := sub_ne_zero.mpr (hs a (Finset.mem_insert_self a S) hm)
        have hd : HasDerivAt (fun w : ℂ => (w - (a : ℂ)) ^ m a)
            (((m a : ℕ) : ℂ) * (s - (a : ℂ)) ^ (m a - 1)) s := by
          simpa using ((hasDerivAt_id s).sub_const (a : ℂ)).fun_pow (m a)
        rw [hd.deriv]
        have hpow_split : (s - (a : ℂ)) ^ m a = (s - (a : ℂ)) ^ (m a - 1) * (s - (a : ℂ)) := by
          conv_lhs => rw [show m a = (m a - 1) + 1 by omega, pow_succ]
        have hpow1_ne : (s - (a : ℂ)) ^ (m a - 1) ≠ 0 := pow_ne_zero _ hsa
        rw [hpow_split]
        field_simp [hsa, hpow1_ne]
    have hfn : (fun w : ℂ => ∏ x ∈ insert a S, (w - (x : ℂ)) ^ m x) = fun w => f w * Q w := by
      funext w; exact Finset.prod_insert ha
    rw [hfn, Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨mul_ne_zero hf_ne hQ_ne, ?_⟩
    rw [deriv_fun_mul hf_diff hQ_diff]
    have hQ_ne' : Q s ≠ 0 := hQ_ne
    calc (deriv f s * Q s + f s * deriv Q s) / (f s * Q s)
        = deriv f s / f s + deriv Q s / Q s := by
          field_simp [hf_ne, hQ_ne']
      _ = ((m a : ℕ) : ℂ) / (s - (a : ℂ)) + ∑ x ∈ S, ((m x : ℕ) : ℂ) / (s - (x : ℂ)) := by
          rw [hf_ld, hQ_ld]

/-- Exact identity `phiSelberg D ξ = phiSelbergRaw D ξ` at every point where `D.Z (1 / 2 + ξ) ≠ 0`. -/
theorem phiSelberg_eq_raw (D : CompactHyperbolicSelbergData) {ξ : ℂ}
    (hZ : D.Z (1 / 2 + ξ) ≠ 0) :
    phiSelberg D ξ = phiSelbergRaw D ξ := by
  let s : ℂ := 1 / 2 + ξ
  have hs_avoid : ∀ x ∈ D.smallRealZeros, analyticOrderNatAt D.Z (x : ℂ) ≠ 0 → s ≠ (x : ℂ) := by
    intro x _ hm heq
    have hne_top : analyticOrderAt D.Z (x : ℂ) ≠ ⊤ := Z_analyticOrderAt_ne_top D (x : ℂ)
    have hne_zero : analyticOrderAt D.Z (x : ℂ) ≠ 0 := by
      rw [← Nat.cast_analyticOrderNatAt hne_top]
      exact_mod_cast hm
    have hZx0 : D.Z (x : ℂ) = 0 :=
      ((Z_analyticOnNhd D (x : ℂ) (Set.mem_univ _)).analyticOrderAt_ne_zero).mp hne_zero
    exact hZ (by rw [show (1 / 2 : ℂ) + ξ = s from rfl, heq]; exact hZx0)
  obtain ⟨hP_ne, hP_ld⟩ := deriv_finset_pow_div hs_avoid
  have hP_diff : DifferentiableAt ℂ (smallPoly D) s :=
    (Finset.analyticAt_fun_prod D.smallRealZeros fun x _ =>
      (analyticAt_id.sub analyticAt_const).pow _).differentiableAt
  have hZreg_diff : DifferentiableAt ℂ (Zreg D) s := Zreg_differentiable D s
  have hZreg_ne : Zreg D s ≠ 0 := fun h0 => hZ (by rw [Z_eq_smallPoly_mul_Zreg, h0, mul_zero])
  have hZ_fn : D.Z = fun w => smallPoly D w * Zreg D w := funext (Z_eq_smallPoly_mul_Zreg D)
  have hZ_ld : deriv D.Z s / D.Z s =
      deriv (smallPoly D) s / smallPoly D s + deriv (Zreg D) s / Zreg D s := by
    have hd : deriv D.Z s = deriv (smallPoly D) s * Zreg D s + smallPoly D s * deriv (Zreg D) s := by
      rw [hZ_fn]
      exact deriv_fun_mul hP_diff hZreg_diff
    have hP_ne' : smallPoly D s ≠ 0 := hP_ne
    rw [hd, Z_eq_smallPoly_mul_Zreg D s]
    field_simp [hP_ne', hZreg_ne]
  have hsub_sum :
      ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (s - (x : ℂ)) =
        ∑ x ∈ D.smallRealZeros,
          ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1 / 2)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1; dsimp only [s]; ring
  unfold phiSelberg phiSelbergRaw
  change deriv (Zreg D) s / Zreg D s =
    deriv D.Z s / D.Z s -
      ∑ x ∈ D.smallRealZeros,
        ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1 / 2))
  rw [hZ_ld, show deriv (smallPoly D) s / smallPoly D s =
      ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (s - (x : ℂ)) from hP_ld,
    hsub_sum]
  ring

/-- `phiSelberg D` is analytic at every `ξ` where `Zreg D (1 / 2 + ξ) ≠ 0`. -/
lemma phiSelberg_analyticAt_of_Zreg_ne_zero (D : CompactHyperbolicSelbergData) {ξ : ℂ}
    (h : Zreg D (1 / 2 + ξ) ≠ 0) :
    AnalyticAt ℂ (phiSelberg D) ξ := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) ξ :=
    analyticAt_const.add analyticAt_id
  have hnum : AnalyticAt ℂ (fun w : ℂ => deriv (Zreg D) (1 / 2 + w)) ξ :=
    ((Zreg_analyticOnNhd D).deriv (1 / 2 + ξ) (Set.mem_univ _)).comp hshift
  have hden : AnalyticAt ℂ (fun w : ℂ => Zreg D (1 / 2 + w)) ξ :=
    (Zreg_analyticOnNhd D (1 / 2 + ξ) (Set.mem_univ _)).comp hshift
  exact hnum.div hden h

/-- Unconditional holomorphicity of `phiSelberg D` at `ξ = 0` (even when `λ = 1 / 4` is an
eigenvalue and `D.Z (1 / 2) = 0`). -/
theorem phiSelberg_analyticAt_zero (D : CompactHyperbolicSelbergData) :
    AnalyticAt ℂ (phiSelberg D) 0 := by
  refine phiSelberg_analyticAt_of_Zreg_ne_zero D ?_
  rw [add_zero]
  exact Zreg_half_ne_zero D

private lemma Z_eventually_ne_zero_nhdsNE (D : CompactHyperbolicSelbergData) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, D.Z w ≠ 0 := by
  rcases (Z_analyticOnNhd D z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero with
      hzero | hne
  · exfalso
    have hall := (Z_analyticOnNhd D).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hzero
    obtain ⟨_, hC⟩ := D.right_bound
    exact (hC 2 (by norm_num)).1 (hall (Set.mem_univ 2))
  · exact hne

/-- Unconditional removable singularity limit: for every `x ∈ D.smallRealZeros`,
`phiSelbergRaw D ξ` tends to `phiSelberg D (x - 1 / 2)` as `ξ → x - 1 / 2`. -/
theorem phiSelbergRaw_tendsto_of_mem_smallRealZeros (D : CompactHyperbolicSelbergData)
    {x : ℝ} (hx : x ∈ D.smallRealZeros) :
    Tendsto (phiSelbergRaw D) (𝓝[≠] ((x : ℂ) - 1 / 2))
      (𝓝 (phiSelberg D ((x : ℂ) - 1 / 2))) := by
  have hZreg_ne : Zreg D (1 / 2 + ((x : ℂ) - 1 / 2)) ≠ 0 := by
    have hadd : (1 / 2 : ℂ) + ((x : ℂ) - 1 / 2) = (x : ℂ) := by ring
    rw [hadd]
    exact Zreg_ne_zero_of_mem_smallRealZeros D hx
  have hcont : Tendsto (phiSelberg D) (𝓝[≠] ((x : ℂ) - 1 / 2))
      (𝓝 (phiSelberg D ((x : ℂ) - 1 / 2))) :=
    (phiSelberg_analyticAt_of_Zreg_ne_zero D hZreg_ne).continuousAt.continuousWithinAt
  have hZ_ne_ev : ∀ᶠ s in 𝓝[≠] (x : ℂ), D.Z s ≠ 0 := Z_eventually_ne_zero_nhdsNE D (x : ℂ)
  have hshift_tend : Tendsto (fun ξ : ℂ => (1 / 2 : ℂ) + ξ)
      (𝓝[≠] ((x : ℂ) - 1 / 2)) (𝓝[≠] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) ((x : ℂ) - 1 / 2) :=
        continuousAt_const.add continuousAt_id
      have hcw : Tendsto (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (𝓝[≠] ((x : ℂ) - 1 / 2))
          (𝓝 ((1 / 2 : ℂ) + ((x : ℂ) - 1 / 2))) :=
        hc.continuousWithinAt
      have hadd : (1 / 2 : ℂ) + ((x : ℂ) - 1 / 2) = (x : ℂ) := by ring
      rwa [hadd] at hcw
    · filter_upwards [eventually_mem_nhdsWithin] with ξ hξ
      have hξ_ne : ξ ≠ (x : ℂ) - 1 / 2 := Set.mem_compl_singleton_iff.mp hξ
      intro heq
      have heq' : (1 / 2 : ℂ) + ξ = (x : ℂ) := Set.mem_singleton_iff.mp heq
      apply hξ_ne
      linear_combination heq'
  refine hcont.congr' ?_
  filter_upwards [hshift_tend.eventually hZ_ne_ev] with ξ hZ
  exact phiSelberg_eq_raw D hZ

/-- Whenever `D.Z (1 / 2) ≠ 0` (`λ = 1 / 4` is not an eigenvalue), `phiSelberg D` and
`phiSelbergRaw D` agree on an open neighborhood of `0`, hence share identical formal series
and OGFs. -/
theorem formalSeries_phiSelberg_eq_raw (D : CompactHyperbolicSelbergData)
    (hZ0 : D.Z (1 / 2 : ℂ) ≠ 0) :
    formalSeries (phiSelberg D) = formalSeries (phiSelbergRaw D) ∧
    ogfOfEGF (phiSelberg D) = ogfOfEGF (phiSelbergRaw D) := by
  have hcont : ContinuousAt (fun ξ : ℂ => D.Z (1 / 2 + ξ)) 0 :=
    ContinuousAt.comp (g := D.Z) (f := fun ξ : ℂ => (1 / 2 : ℂ) + ξ)
      (D.Z_entire (1 / 2 + 0)).continuousAt (continuousAt_const.add continuousAt_id)
  have hev : phiSelberg D =ᶠ[𝓝 (0 : ℂ)] phiSelbergRaw D := by
    filter_upwards [hcont.eventually_ne (by simpa using hZ0)] with ξ hZ
    exact phiSelberg_eq_raw D hZ
  constructor
  · ext n
    cases n with
    | zero => simp [formalSeries]
    | succ k =>
      simp only [formalSeries, PowerSeries.coeff_mk]
      exact hev.iteratedDeriv_eq k
  · ext n
    simp only [ogfOfEGF, PowerSeries.coeff_mk]
    exact hev.iteratedDeriv_eq n

/-- Unconditional holomorphicity of `phiSelberg D` on the open right half-plane `{ξ | 0 < ξ.re}`
and on the open left half-plane away from the negative real axis `{ξ | ξ.re < 0 ∧ ξ.im ≠ 0}`. -/
theorem phiSelberg_holomorphic_on_open_halfplanes (D : CompactHyperbolicSelbergData) :
    AnalyticOnNhd ℂ (phiSelberg D) {ξ : ℂ | 0 < ξ.re} ∧
    AnalyticOnNhd ℂ (phiSelberg D) {ξ : ℂ | ξ.re < 0 ∧ ξ.im ≠ 0} := by
  refine ⟨fun ξ hξ => phiSelberg_analyticAt_of_Zreg_ne_zero D ?_,
          fun ξ hξ => phiSelberg_analyticAt_of_Zreg_ne_zero D ?_⟩
  · change 0 < ξ.re at hξ
    refine Zreg_ne_zero_of_re_ne_half D ?_ (Or.inl ?_)
    · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  · refine Zreg_ne_zero_of_re_ne_half D ?_ (Or.inr ?_)
    · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith [hξ.1]
    · simpa [Complex.add_im] using hξ.2

/-! ### 4. Critical-Line Spectral Sequence `rSeq` & Simple Poles `+selbergMult` -/

/-- Set of positive spectral parameters `r > 0` where `Z (1 / 2 + i r) = 0`. -/
@[expose] def selbergPosZeros (D : CompactHyperbolicSelbergData) : Set ℝ :=
  {r : ℝ | 0 < r ∧ D.Z (1 / 2 + I * (r : ℂ)) = 0}

/-- Spectral eigenspace multiplicity `m(r) = analyticOrderNatAt D.Z (1 / 2 + i r)`. -/
@[expose] def selbergMult (D : CompactHyperbolicSelbergData) (r : ℝ) : ℕ :=
  analyticOrderNatAt D.Z (1 / 2 + I * (r : ℂ))

/-- Every critical-line zero `1 / 2 + i r` has positive finite multiplicity `1 ≤ selbergMult D r`
(no eigenvalue-simplicity assumption). -/
theorem selbergMult_pos (D : CompactHyperbolicSelbergData) {r : ℝ}
    (hr : D.Z (1 / 2 + I * (r : ℂ)) = 0) :
    1 ≤ selbergMult D r := by
  have hana : AnalyticAt ℂ D.Z (1 / 2 + I * (r : ℂ)) :=
    Z_analyticOnNhd D _ (Set.mem_univ _)
  have hne_top : analyticOrderAt D.Z (1 / 2 + I * (r : ℂ)) ≠ ⊤ :=
    Z_analyticOrderAt_ne_top D _
  have hne_zero : analyticOrderAt D.Z (1 / 2 + I * (r : ℂ)) ≠ 0 :=
    hana.analyticOrderAt_ne_zero.mpr hr
  have hnat_ne : selbergMult D r ≠ 0 := by
    intro h0
    apply hne_zero
    rw [← Nat.cast_analyticOrderNatAt hne_top]
    exact_mod_cast h0
  omega

private lemma selbergPosZeros_inter_Icc_finite (D : CompactHyperbolicSelbergData) (R : ℝ) :
    (selbergPosZeros D ∩ Set.Icc 0 R).Finite := by
  let f : ℝ → ℂ := fun r => 1 / 2 + I * (r : ℂ)
  have hf_cont : Continuous f :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hf_inj : Function.Injective f := by
    intro a b hab
    have him := congrArg Complex.im hab
    simpa [f] using him
  let K : Set ℂ := f '' Set.Icc 0 R
  have hK_comp : IsCompact K := isCompact_Icc.image hf_cont
  have hnhds : ∀ z ∈ K, {w : ℂ | D.Z w = 0 → w = z} ∈ 𝓝 z := by
    intro z _
    have hne := Z_eventually_ne_zero_nhdsNE D z
    rw [eventually_nhdsWithin_iff] at hne
    filter_upwards [hne] with w hw hZw
    by_contra hne_wz
    exact hw hne_wz hZw
  obtain ⟨t, _, ht_cov⟩ := hK_comp.elim_nhds_subcover (fun z => {w : ℂ | D.Z w = 0 → w = z}) hnhds
  have hfin_img : (K ∩ {w : ℂ | D.Z w = 0}).Finite := by
    refine t.finite_toSet.subset fun w hw => ?_
    have hmem := ht_cov hw.1
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
    obtain ⟨z, hzt, hz⟩ := hmem
    rw [hz hw.2]
    exact hzt
  have hsub : f '' (selbergPosZeros D ∩ Set.Icc 0 R) ⊆ K ∩ {w : ℂ | D.Z w = 0} := by
    rintro _ ⟨r, ⟨hrz, hrI⟩, rfl⟩
    exact ⟨⟨r, hrI, rfl⟩, hrz.2⟩
  exact Set.Finite.of_finite_image (hfin_img.subset hsub) hf_inj.injOn

private lemma selbergPosZeros_exists_least (D : CompactHyperbolicSelbergData) {S : Set ℝ}
    (hsub : S ⊆ selbergPosZeros D) (hne : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, m ≤ x := by
  obtain ⟨x₀, hx₀⟩ := hne
  let T : Set ℝ := S ∩ Set.Icc 0 x₀
  have hT_fin : T.Finite :=
    (selbergPosZeros_inter_Icc_finite D x₀).subset (Set.inter_subset_inter_left _ hsub)
  have hx₀_pos : 0 < x₀ := (hsub hx₀).1
  have hT_ne : T.Nonempty := ⟨x₀, hx₀, hx₀_pos.le, le_rfl⟩
  let m : ℝ := hT_fin.toFinset.min' (hT_fin.toFinset_nonempty.mpr hT_ne)
  have hm_mem : m ∈ T := hT_fin.mem_toFinset.mp (Finset.min'_mem _ _)
  refine ⟨m, hm_mem.1, fun x hx => ?_⟩
  by_cases hle : x ≤ x₀
  · have hxT : x ∈ T := ⟨hx, (hsub hx).1.le, hle⟩
    exact Finset.min'_le _ _ (hT_fin.mem_toFinset.mpr hxT)
  · exact hm_mem.2.2.trans (le_of_not_ge hle)

private lemma selbergPosZeros_above_nonempty (D : CompactHyperbolicSelbergData) (a : ℝ) :
    {r ∈ selbergPosZeros D | a < r}.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : selbergPosZeros D ⊆ selbergPosZeros D ∩ Set.Icc 0 a := by
    intro r hr
    refine ⟨hr, hr.1.le, ?_⟩
    by_contra hgt
    push Not at hgt
    have : r ∈ ({x ∈ selbergPosZeros D | a < x} : Set ℝ) := ⟨hr, hgt⟩
    rw [h] at this
    exact this
  exact D.crit_infinite ((selbergPosZeros_inter_Icc_finite D a).subset hsub)

/-- Canonical strictly increasing enumeration of ALL positive critical-line spectral parameters
`0 < rSeq D 0 < rSeq D 1 < ... → +∞` with `D.Z (1 / 2 + i * rSeq D n) = 0`. -/
def rSeq (D : CompactHyperbolicSelbergData) : ℕ → ℝ
  | 0 => Classical.choose (selbergPosZeros_exists_least D Subset.rfl D.crit_infinite.nonempty)
  | n + 1 =>
    let a := rSeq D n
    Classical.choose (selbergPosZeros_exists_least D
      (S := {r ∈ selbergPosZeros D | a < r})
      (fun _ hx => hx.1) (selbergPosZeros_above_nonempty D a))

lemma rSeq_mem (D : CompactHyperbolicSelbergData) (n : ℕ) :
    rSeq D n ∈ selbergPosZeros D := by
  cases n with
  | zero =>
    exact (Classical.choose_spec
      (selbergPosZeros_exists_least D Subset.rfl D.crit_infinite.nonempty)).1
  | succ n =>
    exact (Classical.choose_spec (selbergPosZeros_exists_least D
      (S := {r ∈ selbergPosZeros D | rSeq D n < r})
      (fun _ hx => hx.1)
      (selbergPosZeros_above_nonempty D (rSeq D n)))).1.1

lemma rSeq_pos (D : CompactHyperbolicSelbergData) (n : ℕ) : 0 < rSeq D n :=
  (rSeq_mem D n).1

lemma rSeq_zero (D : CompactHyperbolicSelbergData) (n : ℕ) :
    D.Z (1 / 2 + I * (rSeq D n : ℂ)) = 0 :=
  (rSeq_mem D n).2

lemma rSeq_strictMono (D : CompactHyperbolicSelbergData) : StrictMono (rSeq D) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact (Classical.choose_spec (selbergPosZeros_exists_least D
    (S := {r ∈ selbergPosZeros D | rSeq D n < r})
    (fun _ hx => hx.1)
    (selbergPosZeros_above_nonempty D (rSeq D n)))).1.2

lemma rSeq_tendsto_atTop (D : CompactHyperbolicSelbergData) :
    Tendsto (rSeq D) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro R
  have hex : ∃ N : ℕ, R ≤ rSeq D N := by
    by_contra! hall
    have hsub : Set.range (rSeq D) ⊆ selbergPosZeros D ∩ Set.Icc 0 R := by
      rintro _ ⟨n, rfl⟩
      exact ⟨rSeq_mem D n, (rSeq_pos D n).le, (hall n).le⟩
    exact (Set.infinite_range_of_injective (rSeq_strictMono D).injective)
      ((selbergPosZeros_inter_Icc_finite D R).subset hsub)
  obtain ⟨N, hN⟩ := hex
  exact ⟨N, fun n hn => hN.trans ((rSeq_strictMono D).monotone hn)⟩

lemma rSeq_range (D : CompactHyperbolicSelbergData) :
    Set.range (rSeq D) = selbergPosZeros D := by
  ext r
  constructor
  · rintro ⟨n, rfl⟩
    exact rSeq_mem D n
  · intro hr
    classical
    have hex : ∃ n : ℕ, r ≤ rSeq D n := by
      obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp (rSeq_tendsto_atTop D)) r
      exact ⟨N, hN N le_rfl⟩
    let n : ℕ := Nat.find hex
    have hn_le : r ≤ rSeq D n := Nat.find_spec hex
    refine ⟨n, ?_⟩
    cases hne : n with
    | zero =>
      have hmin := (Classical.choose_spec
        (selbergPosZeros_exists_least D Subset.rfl D.crit_infinite.nonempty)).2 r hr
      rw [hne] at hn_le
      exact le_antisymm hmin hn_le
    | succ k =>
      have hk_lt : rSeq D k < r := by
        have hnot : ¬(r ≤ rSeq D k) := Nat.find_min hex (by omega : k < n)
        exact lt_of_not_ge hnot
      have hmin := (Classical.choose_spec (selbergPosZeros_exists_least D
        (S := {x ∈ selbergPosZeros D | rSeq D k < x})
        (fun _ hx => hx.1)
        (selbergPosZeros_above_nonempty D (rSeq D k)))).2 r ⟨hr, hk_lt⟩
      rw [hne] at hn_le
      exact le_antisymm hmin hn_le

/-- **Simple Pole Principal Part `+m(r) / (ξ - i r)` at Every Critical-Line Zero (Arbitrary Multiplicity)**:
For every `r > 0` with `D.Z (1 / 2 + i r) = 0`, `phiSelberg D ξ - selbergMult D r / (ξ - i r)`
extends continuously to `ξ = i r`, with positive integer residue `selbergMult D r ≥ 1`. -/
theorem phiSelberg_simple_pole_principalPart (D : CompactHyperbolicSelbergData) {r : ℝ}
    (hr_pos : 0 < r) (hr : D.Z (1 / 2 + I * (r : ℂ)) = 0) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun ξ : ℂ => phiSelberg D ξ - ((selbergMult D r : ℕ) : ℂ) / (ξ - I * (r : ℂ)))
        (𝓝[≠] (I * (r : ℂ))) (𝓝 L) := by
  let s₀ : ℂ := 1 / 2 + I * (r : ℂ)
  let m : ℕ := selbergMult D r
  have hm_pos : 1 ≤ m := selbergMult_pos D hr
  have hP_an : AnalyticAt ℂ (smallPoly D) s₀ :=
    Finset.analyticAt_fun_prod D.smallRealZeros fun x _ =>
      (analyticAt_id.sub analyticAt_const).pow _
  have hP_ne : smallPoly D s₀ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro heq
    have him := congrArg Complex.im heq
    simp [s₀] at him
    linarith
  have hZreg_an : AnalyticAt ℂ (Zreg D) s₀ := Zreg_analyticOnNhd D s₀ (Set.mem_univ _)
  have hZreg_ord_eq : analyticOrderAt (Zreg D) s₀ = analyticOrderAt D.Z s₀ := by
    have hfn : D.Z = smallPoly D * Zreg D := funext (Z_eq_smallPoly_mul_Zreg D)
    rw [hfn, analyticOrderAt_mul hP_an hZreg_an, hP_an.analyticOrderAt_eq_zero.mpr hP_ne, zero_add]
  have hZreg_ne_top : analyticOrderAt (Zreg D) s₀ ≠ ⊤ := by
    rw [hZreg_ord_eq]
    exact Z_analyticOrderAt_ne_top D s₀
  have hZreg_nat_eq : analyticOrderNatAt (Zreg D) s₀ = m := by
    simp only [analyticOrderNatAt, hZreg_ord_eq, m, selbergMult, s₀]
  obtain ⟨g, hg_ana, hg0, hfg⟩ := hZreg_an.analyticOrderAt_ne_top.mp hZreg_ne_top
  let h : ℂ → ℂ := fun ξ => g (1 / 2 + ξ)
  have hshift : AnalyticAt ℂ (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (I * (r : ℂ)) :=
    analyticAt_const.add analyticAt_id
  have hh_ana : AnalyticAt ℂ h (I * (r : ℂ)) :=
    AnalyticAt.comp (g := g) (f := fun ξ : ℂ => (1 / 2 : ℂ) + ξ) hg_ana hshift
  have hh0 : h (I * (r : ℂ)) ≠ 0 := hg0
  have hshift_tend : Tendsto (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (𝓝 (I * (r : ℂ))) (𝓝 s₀) :=
    hshift.continuousAt
  have hZreg_ev : (fun ξ : ℂ => Zreg D (1 / 2 + ξ)) =ᶠ[𝓝 (I * (r : ℂ))]
      fun ξ : ℂ => (ξ - I * (r : ℂ)) ^ m * h ξ := by
    filter_upwards [hshift_tend.eventually hfg] with ξ hξ
    have hsub : (1 / 2 : ℂ) + ξ - s₀ = ξ - I * (r : ℂ) := by dsimp only [s₀]; ring
    change Zreg D (1 / 2 + ξ) = (ξ - I * (r : ℂ)) ^ m * g (1 / 2 + ξ)
    have hξ' : Zreg D (1 / 2 + ξ) = (1 / 2 + ξ - s₀) ^ m * g (1 / 2 + ξ) := by
      have hξ0 : Zreg D (1 / 2 + ξ) =
          (1 / 2 + ξ - s₀) ^ analyticOrderNatAt (Zreg D) s₀ * g (1 / 2 + ξ) := by
        simpa [smul_eq_mul] using hξ
      rwa [hZreg_nat_eq] at hξ0
    rw [hξ', hsub]
  have hderiv_Zreg : ∀ᶠ ξ in 𝓝 (I * (r : ℂ)),
      deriv (Zreg D) (1 / 2 + ξ) =
        (m : ℂ) * (ξ - I * (r : ℂ)) ^ (m - 1) * h ξ + (ξ - I * (r : ℂ)) ^ m * deriv h ξ := by
    have hcomp_deriv : ∀ᶠ ξ in 𝓝 (I * (r : ℂ)),
        deriv (fun w : ℂ => Zreg D (1 / 2 + w)) ξ = deriv (Zreg D) (1 / 2 + ξ) := by
      filter_upwards with ξ
      have hd : HasDerivAt (fun w : ℂ => Zreg D (1 / 2 + w))
          (deriv (Zreg D) (1 / 2 + ξ) * 1) ξ :=
        (Zreg_differentiable D (1 / 2 + ξ)).hasDerivAt.comp ξ
          ((hasDerivAt_const ξ (1 / 2 : ℂ)).add (hasDerivAt_id ξ) |>.congr_deriv (zero_add 1))
      simpa using hd.deriv
    have hprod_deriv : ∀ᶠ ξ in 𝓝 (I * (r : ℂ)),
        deriv (fun w : ℂ => (w - I * (r : ℂ)) ^ m * h w) ξ =
          (m : ℂ) * (ξ - I * (r : ℂ)) ^ (m - 1) * h ξ + (ξ - I * (r : ℂ)) ^ m * deriv h ξ := by
      filter_upwards [hh_ana.eventually_analyticAt] with ξ hξh
      have hd1 : HasDerivAt (fun w : ℂ => (w - I * (r : ℂ)) ^ m)
          ((m : ℂ) * (ξ - I * (r : ℂ)) ^ (m - 1)) ξ := by
        simpa using ((hasDerivAt_id ξ).sub_const (I * (r : ℂ))).fun_pow m
      exact (hd1.mul hξh.differentiableAt.hasDerivAt).deriv
    filter_upwards [hZreg_ev.eventually_nhds, hcomp_deriv, hprod_deriv] with ξ hzeq hcd hpd
    have hzeq' : (fun w : ℂ => Zreg D (1 / 2 + w)) =ᶠ[𝓝 ξ]
        fun w : ℂ => (w - I * (r : ℂ)) ^ m * h w := hzeq
    rw [← hcd, Filter.EventuallyEq.deriv_eq hzeq', hpd]
  have hh_ne : ∀ᶠ ξ in 𝓝 (I * (r : ℂ)), h ξ ≠ 0 := hh_ana.continuousAt.eventually_ne hh0
  have hrem_ana : AnalyticAt ℂ (fun ξ : ℂ => deriv h ξ / h ξ) (I * (r : ℂ)) :=
    hh_ana.deriv.div hh_ana hh0
  refine ⟨deriv h (I * (r : ℂ)) / h (I * (r : ℂ)), ?_⟩
  refine hrem_ana.continuousAt.continuousWithinAt.tendsto.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    hZreg_ev.filter_mono nhdsWithin_le_nhds,
    hderiv_Zreg.filter_mono nhdsWithin_le_nhds,
    hh_ne.filter_mono nhdsWithin_le_nhds] with ξ hξ_ne hze hdz hhn
  have hsub_ne : ξ - I * (r : ℂ) ≠ 0 := sub_ne_zero.mpr hξ_ne
  have hpow_split : (ξ - I * (r : ℂ)) ^ m = (ξ - I * (r : ℂ)) ^ (m - 1) * (ξ - I * (r : ℂ)) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  have hpow1_ne : (ξ - I * (r : ℂ)) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hsub_ne
  change deriv h ξ / h ξ = deriv (Zreg D) (1 / 2 + ξ) / Zreg D (1 / 2 + ξ) -
    (m : ℂ) / (ξ - I * (r : ℂ))
  rw [hze, hdz, hpow_split]
  field_simp [hsub_ne, hpow1_ne, hhn]
  ring

/-- **Simple Pole & Nonzero Positive-Integer Residue Theorem at Any Critical-Line Zero**:
For every `r > 0` with `D.Z (1 / 2 + i r) = 0`, `(ξ - i r) * phiSelberg D ξ → +m(r) ≠ 0`
as `ξ → i r`, where `m(r) = selbergMult D r ≥ 1`. -/
theorem phiSelberg_simple_pole_at_zero (D : CompactHyperbolicSelbergData) {r : ℝ}
    (hr_pos : 0 < r) (hr : D.Z (1 / 2 + I * (r : ℂ)) = 0) :
    Filter.Tendsto (fun ξ : ℂ => (ξ - I * (r : ℂ)) * phiSelberg D ξ)
      (𝓝[≠] (I * (r : ℂ))) (𝓝 (((selbergMult D r : ℕ) : ℂ))) ∧
    (((selbergMult D r : ℕ) : ℂ)) ≠ 0 := by
  obtain ⟨L, hL⟩ := phiSelberg_simple_pole_principalPart D hr_pos hr
  have hm_ne : (((selbergMult D r : ℕ) : ℂ)) ≠ 0 := by
    have hm_pos : 1 ≤ selbergMult D r := selbergMult_pos D hr
    exact_mod_cast (show selbergMult D r ≠ 0 by omega)
  refine ⟨?_, hm_ne⟩
  have hsub_cont : ContinuousAt (fun ξ : ℂ => ξ - I * (r : ℂ)) (I * (r : ℂ)) :=
    continuousAt_id.sub continuousAt_const
  have hsub0 : Tendsto (fun ξ : ℂ => ξ - I * (r : ℂ)) (𝓝[≠] (I * (r : ℂ))) (𝓝 (0 : ℂ)) := by
    have h0 : I * (r : ℂ) - I * (r : ℂ) = 0 := sub_self _
    exact h0 ▸ hsub_cont.continuousWithinAt
  have hmul := (hsub0.mul hL).add (tendsto_const_nhds (x := ((selbergMult D r : ℕ) : ℂ)))
  rw [zero_mul, zero_add] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ξ hξ
  have hsub_ne : ξ - I * (r : ℂ) ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hξ)
  field_simp [hsub_ne]
  ring

private lemma exp_I_pi_div_two : Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ)) = I := by
  rw [show I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I by ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two,
    ← Complex.ofReal_sin, Real.sin_pi_div_two]
  simp

private lemma exp_neg_I_pi_div_two : Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ)) = -I := by
  rw [show -I * ((Real.pi / 2 : ℝ) : ℂ) = -(((Real.pi / 2 : ℝ) : ℂ) * I) by ring,
    Complex.exp_neg, show ((Real.pi / 2 : ℝ) : ℂ) * I = I * ((Real.pi / 2 : ℝ) : ℂ) by ring,
    exp_I_pi_div_two, inv_I]

/-- **Unconditional Holomorphicity on the Entire Rotated Punctured Wedge Around `θ₀ = π / 2`**:
For any `α₀` and any zero-free disk radius `ε > 0` around `0`, `phiSelberg D` is holomorphic on
`rotatedPuncturedWedge (Real.pi / 2) α₀ ε (rSeq D)` (automatically avoiding all negative-real
trivial zeros). -/
theorem phiSelberg_analyticOn_rotatedPuncturedWedge (D : CompactHyperbolicSelbergData)
    {α₀ ε : ℝ} (hball : ∀ ξ : ℂ, ‖ξ‖ < ε → Zreg D (1 / 2 + ξ) ≠ 0) :
    AnalyticOnNhd ℂ (phiSelberg D)
      (rotatedPuncturedWedge (Real.pi / 2) α₀ ε (rSeq D)) := by
  intro ξ hξ
  refine phiSelberg_analyticAt_of_Zreg_ne_zero D ?_
  rcases hξ with ⟨hwedge, hnot_pole⟩
  rw [exp_neg_I_pi_div_two] at hwedge hnot_pole
  rcases hwedge with hball_mem | ⟨him_pos, _⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_neg, Complex.norm_I, one_mul] at hball_mem
    exact hball ξ hball_mem
  · have hξ_im : 0 < ξ.im := by
      simpa [Complex.mul_re] using him_pos
    intro h0
    have hZ0 : D.Z (1 / 2 + ξ) = 0 := by rw [Z_eq_smallPoly_mul_Zreg, h0, mul_zero]
    have hs_im : ((1 / 2 : ℂ) + ξ).im ≠ 0 := by
      simpa [Complex.add_im] using hξ_im.ne'
    have hcrit := D.selberg_rh (1 / 2 + ξ) hZ0 hs_im
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hcrit
    have hξ_re : ξ.re = 0 := by linarith
    have hξ_eq : ξ = I * (ξ.im : ℂ) := Complex.ext (by simp [hξ_re]) (by simp)
    have hmem_Z : ξ.im ∈ selbergPosZeros D := ⟨hξ_im, by rwa [← hξ_eq]⟩
    rw [← rSeq_range D] at hmem_Z
    obtain ⟨m, hm⟩ := hmem_Z
    apply hnot_pole
    refine ⟨m, ?_⟩
    rw [hξ_eq, ← hm]
    have hmul : -I * (I * (rSeq D m : ℂ)) = ((-I) * I) * (rSeq D m : ℂ) := by ring
    rw [hmul]
    simp

/-! ### 5. Elementary Flanking-Ray & Real-Axis Exponential-Type Bounds (No Digamma) -/

private def smallMultSum (D : CompactHyperbolicSelbergData) : ℝ :=
  ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℝ)

private lemma smallMultSum_nonneg (D : CompactHyperbolicSelbergData) :
    0 ≤ smallMultSum D :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

private lemma norm_smallPoleSum_le (D : CompactHyperbolicSelbergData) {ξ : ℂ}
    (hdist : ∀ x ∈ D.smallRealZeros, 1 ≤ ‖ξ - ((x : ℂ) - 1 / 2)‖) :
    ‖∑ x ∈ D.smallRealZeros,
        ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1 / 2))‖ ≤
      smallMultSum D := by
  calc ‖∑ x ∈ D.smallRealZeros,
          ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1 / 2))‖
      ≤ ∑ x ∈ D.smallRealZeros,
          ‖((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1 / 2))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [norm_div, Complex.norm_natCast]
        have h1 : 1 ≤ ‖ξ - ((x : ℂ) - 1 / 2)‖ := hdist x hx
        exact div_le_self (Nat.cast_nonneg _) h1

/-- **Right-Half-Plane Ray Exponential-Type Bound**:
Along ANY ray `e^{i σ} ℝ_{≥0}` in the open right half-plane (`0 < cos σ`), including both the
positive real axis (`σ = 0`) and the right flanking ray (`σ = π / 2 - π / 8`), `phiSelberg D`
is uniformly bounded (`ExpType` with exponent `0`). -/
theorem phiSelberg_expType_right_ray (D : CompactHyperbolicSelbergData) {σ : ℝ}
    (hcos : 0 < Real.cos σ) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (phiSelberg D)) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I σ
  have hμ_re : μ.re = Real.cos σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re σ
  let R₀ : ℝ := 2 / Real.cos σ
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ (phiSelberg D) v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ (phiSelberg D) (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simpa using phiSelberg_analyticAt_zero D
      · have hre_pos : 0 < (μ * (v : ℂ)).re := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
          exact mul_pos hcos hv_pos
        exact (phiSelberg_holomorphic_on_open_halfplanes D).1 (μ * (v : ℂ)) hre_pos
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiSelberg D (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiSelberg D) (f := fun x : ℝ => μ * (x : ℂ))
        hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁⟩ := D.right_bound
  let C : ℝ := max (max M₀ 0) (max M₁ 0 + smallMultSum D)
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 0, hC_nn, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hvR : v ≤ R₀
  · exact (hM₀ v ⟨hv, hvR⟩).trans ((le_max_left M₀ 0).trans (le_max_left _ _))
  · push Not at hvR
    have hv_re : 2 < (μ * (v : ℂ)).re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have := (div_lt_iff₀ hcos).mp hvR
      linarith
    have hs_re : 3 / 2 ≤ ((1 / 2 : ℂ) + μ * (v : ℂ)).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    obtain ⟨hZ_ne, hZ_bd⟩ := hM₁ (1 / 2 + μ * (v : ℂ)) hs_re
    have hdist : ∀ x ∈ D.smallRealZeros, 1 ≤ ‖μ * (v : ℂ) - ((x : ℂ) - 1 / 2)‖ := by
      intro x hx
      have hx1 : x ≤ 1 := (D.smallRealZeros_mem x hx).2
      have h1 : (μ * (v : ℂ) - ((x : ℂ) - 1 / 2)).re ≤ ‖μ * (v : ℂ) - ((x : ℂ) - 1 / 2)‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re] at h1
      linarith
    have hphi_le : ‖phiSelberg D (μ * (v : ℂ))‖ ≤ max M₁ 0 + smallMultSum D := by
      rw [phiSelberg_eq_raw D hZ_ne, phiSelbergRaw]
      calc ‖deriv D.Z (1 / 2 + μ * (v : ℂ)) / D.Z (1 / 2 + μ * (v : ℂ)) -
              ∑ x ∈ D.smallRealZeros,
                ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (μ * (v : ℂ) - ((x : ℂ) - 1 / 2))‖
          ≤ ‖deriv D.Z (1 / 2 + μ * (v : ℂ)) / D.Z (1 / 2 + μ * (v : ℂ))‖ +
              ‖∑ x ∈ D.smallRealZeros,
                ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (μ * (v : ℂ) - ((x : ℂ) - 1 / 2))‖ :=
            norm_sub_le _ _
        _ ≤ M₁ + smallMultSum D := add_le_add hZ_bd (norm_smallPoleSum_le D hdist)
        _ ≤ max M₁ 0 + smallMultSum D := add_le_add (le_max_left M₁ 0) le_rfl
    change ‖μ * phiSelberg D (μ * (v : ℂ))‖ ≤ C
    rw [norm_mul, hμ_norm, one_mul]
    exact hphi_le.trans (le_max_right _ _)

/-- **Left-Half-Plane Flanking-Ray Exponential-Type Bound (Elementary, No Digamma)**:
Along ANY ray `e^{i σ} ℝ_{≥0}` in the open second quadrant (`cos σ < 0`, `0 < sin σ`), including
`σ = π / 2 + π / 8`, `phiSelberg D` has linear growth `O(v)` and hence `ExpType`, proved directly
from `D.func_eq`, `D.right_bound`, and `norm_tan_le_two_of_one_le_im`. -/
theorem phiSelberg_expType_left_ray (D : CompactHyperbolicSelbergData) {σ : ℝ}
    (hcos : Real.cos σ < 0) (hsin : 0 < Real.sin σ) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (phiSelberg D)) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I σ
  have hμ_re : μ.re = Real.cos σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re σ
  have hμ_im : μ.im = Real.sin σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_im σ
  let R₀ : ℝ := max (2 / (-Real.cos σ)) (1 / Real.sin σ)
  have hR₀_pos : 0 < R₀ := lt_of_lt_of_le (div_pos two_pos (neg_pos.mpr hcos)) (le_max_left _ _)
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ (phiSelberg D) v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ (phiSelberg D) (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simpa using phiSelberg_analyticAt_zero D
      · have hre_neg : (μ * (v : ℂ)).re < 0 := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
          exact mul_neg_of_neg_of_pos hcos hv_pos
        have him_ne : (μ * (v : ℂ)).im ≠ 0 := by
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hμ_im]
          exact (mul_pos hsin hv_pos).ne'
        exact (phiSelberg_holomorphic_on_open_halfplanes D).2 (μ * (v : ℂ)) ⟨hre_neg, him_ne⟩
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiSelberg D (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiSelberg D) (f := fun x : ℝ => μ * (x : ℂ))
        hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁⟩ := D.right_bound
  let K₀ : ℝ := max M₁ 0 + smallMultSum D
  let K₁ : ℝ := ((2 * D.g - 2 : ℕ) : ℝ) * (4 * Real.pi)
  have hK₀_nn : 0 ≤ K₀ := add_nonneg (le_max_right M₁ 0) (smallMultSum_nonneg D)
  have hK₁_nn : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  let C : ℝ := max (max M₀ 0) (K₀ + K₁)
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 1, hC_nn, zero_le_one, fun v hv => ?_⟩
  rw [one_mul]
  by_cases hvR : v ≤ R₀
  · calc ‖Minor.pull μ (phiSelberg D) v‖ ≤ M₀ := hM₀ v ⟨hv, hvR⟩
      _ ≤ max M₀ 0 := le_max_left _ _
      _ ≤ C := le_max_left _ _
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_left (Real.one_le_exp hv) hC_nn
  · push Not at hvR
    have hv_pos : 0 < v := lt_trans hR₀_pos hvR
    have hv_gt_cos : 2 / (-Real.cos σ) < v := lt_of_le_of_lt (le_max_left _ _) hvR
    have hv_gt_sin : 1 / Real.sin σ < v := lt_of_le_of_lt (le_max_right _ _) hvR
    let ξ : ℂ := μ * (v : ℂ)
    have hξ_re : ξ.re < -2 := by
      dsimp only [ξ]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have := (div_lt_iff₀ (neg_pos.mpr hcos)).mp hv_gt_cos
      linarith
    have hξ_im : 1 < ξ.im := by
      dsimp only [ξ]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hμ_im]
      have := (div_lt_iff₀ hsin).mp hv_gt_sin
      linarith
    have hξ_norm : ‖ξ‖ = v := by
      dsimp only [ξ]
      rw [norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
    have hrefl_re : 3 / 2 ≤ ((1 / 2 : ℂ) - ξ).re := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    obtain ⟨hZ_refl_ne, hZ_refl_bd⟩ := hM₁ (1 / 2 - ξ) hrefl_re
    have hZ_ne : D.Z (1 / 2 + ξ) ≠ 0 := by
      intro h0
      have hs_im : ((1 / 2 : ℂ) + ξ).im ≠ 0 := by
        simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add]
        linarith
      have hcrit := D.selberg_rh (1 / 2 + ξ) h0 hs_im
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hcrit
      linarith
    have hfe := func_eq_critical_shift D (by linarith) hZ_ne hZ_refl_ne
    have hld_eq : deriv D.Z (1 / 2 + ξ) / D.Z (1 / 2 + ξ) =
        ((2 * D.g - 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * ξ) * Complex.tan ((Real.pi : ℂ) * ξ) -
          deriv D.Z (1 / 2 - ξ) / D.Z (1 / 2 - ξ) := by
      linear_combination hfe
    have hpi_im : 1 ≤ ((Real.pi : ℂ) * ξ).im := by
      have him_eq : ((Real.pi : ℂ) * ξ).im = Real.pi * ξ.im := by
        simp [Complex.mul_im]
      rw [him_eq]
      nlinarith [Real.pi_gt_three]
    have htan_bd : ‖Complex.tan ((Real.pi : ℂ) * ξ)‖ ≤ 2 :=
      norm_tan_le_two_of_one_le_im hpi_im
    have htrig_bd :
        ‖((2 * D.g - 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * ξ) * Complex.tan ((Real.pi : ℂ) * ξ)‖ ≤
          K₁ * v := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, hξ_norm]
      have hfac_nn : 0 ≤ ((2 * D.g - 2 : ℕ) : ℝ) * (2 * Real.pi * v) := by positivity
      calc ((2 * D.g - 2 : ℕ) : ℝ) * (2 * Real.pi * v) * ‖Complex.tan ((Real.pi : ℂ) * ξ)‖
          ≤ ((2 * D.g - 2 : ℕ) : ℝ) * (2 * Real.pi * v) * 2 :=
            mul_le_mul_of_nonneg_left htan_bd hfac_nn
        _ = K₁ * v := by dsimp only [K₁]; ring
    have hdist : ∀ x ∈ D.smallRealZeros, 1 ≤ ‖ξ - ((x : ℂ) - 1 / 2)‖ := by
      intro x _
      have h1 : (ξ - ((x : ℂ) - 1 / 2)).im ≤ ‖ξ - ((x : ℂ) - 1 / 2)‖ :=
        (le_abs_self _).trans (Complex.abs_im_le_norm _)
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.div_ofNat_im, Complex.one_im,
        zero_div, sub_zero] at h1
      linarith
    have hphi_le : ‖phiSelberg D ξ‖ ≤ K₀ + K₁ * v := by
      rw [phiSelberg_eq_raw D hZ_ne, phiSelbergRaw, hld_eq]
      have h1 := norm_sub_le
        (((2 * D.g - 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * ξ) * Complex.tan ((Real.pi : ℂ) * ξ) -
          deriv D.Z (1 / 2 - ξ) / D.Z (1 / 2 - ξ))
        (∑ x ∈ D.smallRealZeros,
          ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1 / 2)))
      have h2 := norm_sub_le
        (((2 * D.g - 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * ξ) * Complex.tan ((Real.pi : ℂ) * ξ))
        (deriv D.Z (1 / 2 - ξ) / D.Z (1 / 2 - ξ))
      have h3 := norm_smallPoleSum_le D hdist
      have hM1 : M₁ ≤ max M₁ 0 := le_max_left M₁ 0
      dsimp only [K₀]
      linarith
    change ‖μ * phiSelberg D ξ‖ ≤ C * Real.exp v
    rw [norm_mul, hμ_norm, one_mul]
    have h1_le_exp : 1 ≤ Real.exp v := Real.one_le_exp hv
    have hv_le_exp : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
    calc ‖phiSelberg D ξ‖ ≤ K₀ + K₁ * v := hphi_le
      _ ≤ K₀ * Real.exp v + K₁ * Real.exp v :=
        add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hv_le_exp hK₁_nn)
      _ = (K₀ + K₁) * Real.exp v := by ring
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos v).le

/-- Right flanking-ray exponential-type bound at `σ = π / 2 - π / 8`. -/
theorem phiSelberg_expType_right (D : CompactHyperbolicSelbergData) :
    ExpType (Minor.pull (Complex.exp (I * ((Real.pi / 2 - Real.pi / 8 : ℝ) : ℂ))) (phiSelberg D)) := by
  have hcos : 0 < Real.cos (Real.pi / 2 - Real.pi / 8) := by
    rw [Real.cos_pi_div_two_sub]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  exact phiSelberg_expType_right_ray D hcos

/-- Left flanking-ray exponential-type bound at `σ = π / 2 + π / 8`. -/
theorem phiSelberg_expType_left (D : CompactHyperbolicSelbergData) :
    ExpType (Minor.pull (Complex.exp (I * ((Real.pi / 2 + Real.pi / 8 : ℝ) : ℂ))) (phiSelberg D)) := by
  have hcos : Real.cos (Real.pi / 2 + Real.pi / 8) < 0 := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub]
    have hsin : 0 < Real.sin (Real.pi / 8) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    linarith
  have hsin : 0 < Real.sin (Real.pi / 2 + Real.pi / 8) := by
    rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two, one_mul, zero_mul, add_zero]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact phiSelberg_expType_left_ray D hcos hsin

/-! ### 6. Packaging `HigherOrderBorelData` & Real-Axis Laplace Asymptotics -/

/-- **Unconditional `HigherOrderBorelData` Witness for Compact Hyperbolic Surfaces**:
Along the rotated critical-line ray `θ₀ = π / 2` with wedge half-angle `α₀ = π / 4` and flanking
rays `θ₀ ± π / 8`, `phiSelberg D` has simple poles (`ord _ = 1`) at `i * rSeq D m` with exact
nonzero positive integer residues `selbergMult D (rSeq D m) ∈ ℤ_{≥1}`. -/
def phiSelberg_higherOrderBorelData (D : CompactHyperbolicSelbergData) :
    HigherOrderBorelData (phiSelberg D) (Real.pi / 2) (rSeq D) (fun _ => 1)
      (fun m s => if s = 1 then ((selbergMult D (rSeq D m) : ℕ) : ℂ) else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 8
  ε := Classical.choose (exists_Zreg_zero_free_ball_half D)
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := (Classical.choose_spec (exists_Zreg_zero_free_ball_half D)).1
  ω_pos := rSeq_pos D 0
  ω_mono := rSeq_strictMono D
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by
    simp only [↓reduceIte]
    have hm_pos : 1 ≤ selbergMult D (rSeq D m) := selbergMult_pos D (rSeq_zero D m)
    exact_mod_cast (show selbergMult D (rSeq D m) ≠ 0 by omega)
  analyticOn :=
    phiSelberg_analyticOn_rotatedPuncturedWedge D
      (Classical.choose_spec (exists_Zreg_zero_free_ball_half D)).2
  pole_principalPart := fun m => by
    obtain ⟨L, hL⟩ := phiSelberg_simple_pole_principalPart D (rSeq_pos D m) (rSeq_zero D m)
    refine ⟨L, ?_⟩
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one, exp_I_pi_div_two]
    exact hL
  expType_plus := phiSelberg_expType_left D
  expType_minus := phiSelberg_expType_right D

private lemma minor_value_hasAsympExp_selberg (a : Minor) {U : Set ℂ} {d : ℂ}
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
      simpa [sub_add_cancel] using
        norm_add_le ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom) (ej.residual a).atom
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

/-- **Unconditional All-Orders Asymptotic Expansion of `G_Selberg_laplace`**:
For every derivative order `j : ℕ`, `iteratedDeriv j (G_Selberg_laplace D)` shares the exact
all-orders `1 / u` asymptotic expansion `d_u^[j] (formalSeries (phiSelberg D))` as `u → +∞`. -/
theorem G_Selberg_laplace_hasAsympExp (D : CompactHyperbolicSelbergData) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (G_Selberg_laplace D))
      (d_u^[j] (formalSeries (phiSelberg D))) := by
  obtain ⟨ε, hε_pos, hball⟩ := exists_Zreg_zero_free_ball_half D
  let U : Set ℂ := Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re}
  have hU : Domain U := by
    refine ⟨Metric.isOpen_ball.union (isOpen_lt continuous_const Complex.continuous_re),
      fun z hz t ht => ?_⟩
    rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left
      simp [Metric.mem_ball, hε_pos]
    · rcases hz with hzb | hzr
      · left
        rw [Metric.mem_ball, dist_zero_right] at hzb ⊢
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hzb
      · right
        change 0 < ((t : ℂ) * z).re
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_pos ht_pos hzr
  have hray : ContainsRay U 1 := by
    intro v hv
    rw [one_mul]
    rcases eq_or_lt_of_le hv with rfl | hv_pos
    · left; simp [Metric.mem_ball, hε_pos]
    · right; simpa using hv_pos
  let a : Minor := Minor.mk 0 (phiSelberg D)
  have ha_good : a.Good U 1 := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases hz with hzb | hzr
      · rw [Metric.mem_ball, dist_zero_right] at hzb
        exact phiSelberg_analyticAt_of_Zreg_ne_zero D (hball z hzb)
      · exact (phiSelberg_holomorphic_on_open_halfplanes D).1 z hzr
    · have hexp0 := phiSelberg_expType_right_ray D (σ := 0) (by simp)
      simpa using hexp0
  have hval : (fun u : ℝ => a.value 1 (u : ℂ)) = G_Selberg_laplace D := by
    funext u
    simp [a, Minor.value, complexLaplace, damped, Minor.pull, G_Selberg_laplace]
  have hser : a.toSeries = formalSeries (phiSelberg D) := by
    ext n
    cases n <;> simp [a, Minor.toSeries, formalSeries]
  rw [← hval, ← hser]
  exact minor_value_hasAsympExp_selberg a hU hray ha_good (by simp) j

/-! ### 7. Master Unconditional Hyperbolic Selberg–Stokes–Vandermonde Theorems -/

/-- **Master Theorem 1 (Strong `ℂ({t})` D-Transcendence of the Geodesic von Mangoldt OGF)**:
For any compact hyperbolic surface `M = ℍ² / Γ` of genus `g ≥ 2`, the ordinary generating function
`ogfOfEGF (phiSelberg D) = ∑_{n ≥ 0} Φ_Γ^{(n)}(0) t^n` is unconditionally **strongly
differentially transcendental over convergent meromorphic germs `ℂ({t})`**
(zero Riemann Hypothesis assumption, zero eigenvalue-simplicity assumption). -/
theorem selberg_ogf_stronglyDTrans (D : CompactHyperbolicSelbergData) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (phiSelberg D)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (phiSelberg_higherOrderBorelData D)

/-- **Master Theorem 2 (Strong `ℂ({t})` D-Transcendence of `formalSeries (phiSelberg D)`)**:
For any compact hyperbolic surface `M = ℍ² / Γ` of genus `g ≥ 2`, the shifted Borel–Laplace
formal series `G_Selberg D = formalSeries (phiSelberg D)` is unconditionally **strongly
differentially transcendental over convergent meromorphic germs `ℂ({t})`**. -/
theorem selberg_formalSeries_stronglyDTrans (D : CompactHyperbolicSelbergData) :
    StronglyDTransOverMeromorphicGerms (formalSeries (phiSelberg D)) :=
  stronglyDTrans_of_higher_order_borel (phiSelberg_higherOrderBorelData D)

/-- **Master Theorem 3 (`ℂ{1/u}` Analytic Differential Transcendence of `G_Selberg_laplace`)**:
The regularized real-axis Selberg Laplace integral `G_Selberg_laplace D` satisfies NO nonzero
convergent-germ algebraic differential equation over `ℂ{1/u}` eventually as `u → +∞`. -/
theorem selberg_laplace_no_conv_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg_laplace D) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) :
    Q = 0 :=
  no_conv_ade_of_higher_order_borel_asymp (phiSelberg_higherOrderBorelData D)
    (G_Selberg_laplace_hasAsympExp D) Q hQ

/-- **Master Theorem 4 (`ℂ(u)` Analytic Differential Transcendence of `G_Selberg_laplace`)**:
The regularized real-axis Selberg Laplace integral `G_Selberg_laplace D` satisfies NO nonzero
rational-coefficient algebraic differential equation over `ℂ(u)` eventually as `u → +∞`. -/
theorem selberg_laplace_no_rat_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg_laplace D) u)
        (evalRatU P (u : ℂ)) = 0) :
    P = 0 :=
  no_rat_ade_of_higher_order_borel (phiSelberg_higherOrderBorelData D)
    (G_Selberg_laplace_hasAsympExp D) P hP

/-- **Master Theorem 5 (Formal `ℂ(u)` Non-Autonomous D-Transcendence of `G_Selberg`)**:
The formal series `G_Selberg D` satisfies NO nonzero rational-coefficient ADE over `ℂ(u)`. -/
theorem selberg_formalSeries_no_rat_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (phiSelberg D)) P = 0) :
    P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade (phiSelberg_higherOrderBorelData D) P hP

/-- **Master Theorem 6 (Formal `ℂ{1/u}` Non-Autonomous `d_u`-Transcendence of `G_Selberg`)**:
The formal series `G_Selberg D` satisfies NO nonzero convergent-germ `d_u`-ADE over `ℂ{1/u}`. -/
theorem selberg_formalSeries_no_conv_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries (phiSelberg D)) Q = 0) :
    Q = 0 :=
  no_conv_ade_of_higher_order_borel (phiSelberg_higherOrderBorelData D) Q hQ

/-- **Master Theorem 7 (`ℂ[u]` Analytic Differential Transcendence of `G_Selberg_laplace`)**:
The regularized real-axis Selberg Laplace integral `G_Selberg_laplace D` satisfies NO nonzero
non-autonomous polynomial differential equation over `ℂ[u]` eventually as `u → +∞`. -/
theorem selberg_laplace_no_poly_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg_laplace D) u)
        (evalU P (u : ℂ)) = 0) :
    P = 0 :=
  no_nonautonomous_ade_of_higher_order_borel (phiSelberg_higherOrderBorelData D)
    (G_Selberg_laplace_hasAsympExp D) P hP

/-- **Master Theorem 8 (Autonomous Analytic Differential Transcendence of `G_Selberg_laplace`)**:
The regularized real-axis Selberg Laplace integral `G_Selberg_laplace D` satisfies NO nonzero
autonomous polynomial differential equation over `ℂ` eventually as `u → +∞`. -/
theorem selberg_laplace_no_autonomous_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg_laplace D) u) P = 0) :
    P = 0 :=
  no_autonomous_ade_of_higher_order_borel (phiSelberg_higherOrderBorelData D)
    (G_Selberg_laplace_hasAsympExp D) P hP

end
end PakPrimes.SelbergHyperbolicDTrans
