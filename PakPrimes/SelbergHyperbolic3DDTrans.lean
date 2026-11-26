module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.HigherOrderStrongDTrans
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Unconditional 3D Compact Hyperbolic Selberg–Stokes–Vandermonde Theorem

This module formalizes the **Unconditional 3D Compact Hyperbolic Selberg–Stokes–Vandermonde
Theorem** for any compact orientable 3-dimensional hyperbolic manifold `M = ℍ³ / Γ` (such as the
Weeks manifold), with **zero Riemann Hypothesis assumption**, **zero eigenvalue-simplicity
assumption**, and **zero trivial zeros anywhere in `ℂ`**.

## Mathematical Architecture
1. **Compact 3D Hyperbolic Selberg Data (`CompactHyperbolic3DSelbergData`)**:
   Encapsulates an entire 3D Selberg zeta function `Z : ℂ → ℂ` on a compact orientable 3D
   hyperbolic manifold `M = ℍ³ / Γ` of volume `vol > 0` satisfying:
   - `Z_entire`: `Z` is entire on `ℂ`,
   - `selberg_rh`: unconditional 3D Selberg RH (self-adjointness of `-Δ_M`) — every non-real zero
     lies strictly on the critical line `Re s = 1` (`λ = 1 + r²`),
   - `smallRealZeros`: finitely many real zeros in `[0, 2]` (covering `λ₀ = 0` at `s = 0, 2` and
     any small eigenvalues `0 < λ_j ≤ 1`, including `s = 1` if `λ = 1` occurs),
   - `real_zeros_classified`: **zero trivial zeros anywhere in `ℂ`** — every real zero of `Z`
     belongs to `smallRealZeros ⊆ [0, 2]`,
   - `crit_infinite`: unconditional 3D Weyl's law `N(λ) ~ (Vol(M) / (6π²)) λ^{3/2}` — infinitely
     many distinct critical-line zeros `1 + i r` with `r > 0`,
   - `right_bound`: uniform 3D loxodromic Dirichlet-series bound on `Re s ≥ 3`,
   - `func_eq`: exact pure-polynomial 3D Selberg functional equation
     (Elstrodt–Grunewald–Mennicke Ch. 5 Thm. 4.10, with no `tan`/`cot` factor):
     `Z'(2 - s) / Z(2 - s) + Z'(s) / Z(s) = (Vol(M) / π) (s - 1)²`,
     equivalently at `s = 1 + ξ`:
     `Z'(1 - ξ) / Z(1 - ξ) + Z'(1 + ξ) / Z(1 + ξ) = (Vol(M) / π) ξ²`.
2. **Entire Regularization & Pole-Subtracted Kernel (`Zreg3D`, `phiSelberg3DRaw`, `phiSelberg3D`)**:
   - Factors out the exact finite vanishing polynomial
     `smallPoly3D D s = ∏ x ∈ D.smallRealZeros, (s - x)^{m_x}` (`m_x = analyticOrderNatAt D.Z x`)
     from `D.Z` to obtain an entire quotient `Zreg3D D` that is nonvanishing on the entire real
     axis `ℝ` and everywhere off the critical line `{s | s.re = 1 ∧ s.im ≠ 0}`.
   - Defines `phiSelberg3D D ξ := deriv (Zreg3D D) (1 + ξ) / Zreg3D D (1 + ξ)`, which agrees
     identically with the pole-subtracted logarithmic derivative
     `phiSelberg3DRaw D ξ := deriv D.Z (1 + ξ) / D.Z (1 + ξ) - ∑ x ∈ D.smallRealZeros, m_x / (ξ - (x - 1))`
     at every `ξ` where `D.Z (1 + ξ) ≠ 0`, and analytically continues across every removable
     singularity `ξ = x - 1` (including `ξ = 0` when `λ = 1` occurs and `ξ = ±1` from `λ₀ = 0`).
3. **Unbounded Critical-Line Spectral Sequence & Simple Poles (`rSeq3D`, `selberg3DMult`)**:
   - Constructs the canonical strictly increasing enumeration `rSeq3D D : ℕ → ℝ` of all positive
     critical-line zero ordinates with `0 < rSeq3D D 0`, `StrictMono (rSeq3D D)`, and
     `Tendsto (rSeq3D D) atTop atTop` via compactness and isolated zeros.
   - Proves simple-pole principal parts `+(selberg3DMult D r) / (ξ - i r)` with
     `1 ≤ selberg3DMult D r = analyticOrderNatAt D.Z (1 + i r)` (arbitrary multiplicity).
   - Proves holomorphicity on the entire `rotatedPuncturedWedge (π / 2) α₀ ε (rSeq3D D)` (and in
     fact everywhere off the imaginary-axis spectral poles, with zero negative-real-axis poles).
4. **Elementary Flanking-Ray Growth Bounds (Pure Polynomial, No Trig Needed)**:
   - Right half-plane rays (`0 < cos σ`, including `σ = 0` and `σ = π / 2 - π / 8`): `O(1)` via
     `D.right_bound`.
   - Left half-plane rays (`cos σ < 0`, including `σ = π / 2 + π / 8`): pure quadratic `O(v²)` via
     `D.func_eq` and `D.right_bound`, yielding `ExpType` with exponent `1` via `v² ≤ 4 exp v`.
5. **Master Unconditional 3D Selberg–Stokes–Vandermonde Theorems**:
   Packages `phiSelberg3D_higherOrderBorelData D : HigherOrderBorelData ...` and proves:
   - `selberg3D_ogf_stronglyDTrans`: `ogfOfEGF (phiSelberg3D D)` is strongly D-transcendental over
     convergent meromorphic germs `ℂ({t})`,
   - `selberg3D_formalSeries_stronglyDTrans`: `formalSeries (phiSelberg3D D)` is strongly
     D-transcendental over `ℂ({t})`,
   - `selberg3D_laplace_no_conv_ade`, `selberg3D_laplace_no_rat_ade`,
     `selberg3D_laplace_no_poly_ade`, `selberg3D_laplace_no_autonomous_ade`,
     `selberg3D_formalSeries_no_rat_ade`, `selberg3D_formalSeries_no_conv_ade`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.SelbergHyperbolic3DDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.HigherOrderStokes
open PakPrimes.FishburnStrongDTrans
open PakPrimes.PakYeliussizovEGF
open PakPrimes.HigherOrderStrongDTrans
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Public Specification: `CompactHyperbolic3DSelbergData` -/

/-- Analytic data of the 3D Selberg zeta function `Z_Γ^{3D}` of a compact orientable hyperbolic
3-manifold `M = ℍ³ / Γ` of volume `vol > 0`. Every field holds unconditionally for every cocompact
torsion-free Kleinian group `Γ ⊂ PSL₂(ℂ)` (Elstrodt–Grunewald–Mennicke Ch. 5; Sarnak 1983;
Fried 1986). -/
structure CompactHyperbolic3DSelbergData where
  /-- Hyperbolic volume `Vol(M) > 0` of the compact 3-manifold `M = ℍ³ / Γ`. -/
  vol : ℝ
  hvol : 0 < vol
  /-- The entire 3D Selberg zeta function `Z_Γ^{3D} : ℂ → ℂ`. -/
  Z : ℂ → ℂ
  Z_entire : Differentiable ℂ Z
  /-- Unconditional 3D Selberg RH (self-adjointness of `-Δ_M`): every non-real zero lies on `Re s = 1`. -/
  selberg_rh : ∀ s : ℂ, Z s = 0 → s.im ≠ 0 → s.re = 1
  /-- Finitely many real zeros of `Z` in `[0, 2]` (ground state `s = 0, 2` and any small
  eigenvalues `0 < λ ≤ 1`, including `s = 1` if `λ = 1` occurs). -/
  smallRealZeros : Finset ℝ
  smallRealZeros_mem : ∀ x ∈ smallRealZeros, 0 ≤ x ∧ x ≤ 2
  /-- Zero trivial zeros anywhere on `ℝ` outside `[0, 2]`: every real zero of `Z` lies in
  `smallRealZeros`. -/
  real_zeros_classified : ∀ x : ℝ, Z (x : ℂ) = 0 → x ∈ smallRealZeros
  /-- Unconditional 3D Weyl's law: infinitely many distinct critical-line zeros `1 + i r` (`r > 0`). -/
  crit_infinite : {r : ℝ | 0 < r ∧ Z (1 + I * (r : ℂ)) = 0}.Infinite
  /-- 3D loxodromic Dirichlet-series uniform bound on `Re s ≥ 3` (positive systole). -/
  right_bound : ∃ C : ℝ, ∀ s : ℂ, 3 ≤ s.re → Z s ≠ 0 ∧ ‖deriv Z s / Z s‖ ≤ C
  /-- Exact pure-polynomial 3D Selberg functional equation (Elstrodt–Grunewald–Mennicke Ch. 5
  Thm. 4.10): `Z'(2 - s) / Z(2 - s) + Z'(s) / Z(s) = (Vol(M) / π) (s - 1)²`. -/
  func_eq : ∀ s : ℂ, Z s ≠ 0 → Z (2 - s) ≠ 0 →
    deriv Z (2 - s) / Z (2 - s) + deriv Z s / Z s =
      ((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2

/-! ### 2. Pure-Polynomial Shifted Functional Equation & Exponential-Cubic Sign Consistency -/

/-- Sign-consistency check with Elstrodt–Grunewald–Mennicke Ch. 5 Thm. 4.10: any entire function `Z`
satisfying `Z(2 - s) = exp(-(vol / (3π)) (s - 1)³ + E) Z(s)` automatically obeys the exact
logarithmic-derivative functional equation
`Z'(2 - s) / Z(2 - s) + Z'(s) / Z(s) = +(vol / π) (s - 1)²`. -/
theorem func_eq_of_exp_cubic_symmetry {Z : ℂ → ℂ} {vol : ℝ} {E : ℂ}
    (hZ : Differentiable ℂ Z)
    (hsym : ∀ s : ℂ, Z (2 - s) =
      Complex.exp (-((vol : ℂ) / (3 * (Real.pi : ℂ))) * (s - 1) ^ 3 + E) * Z s)
    {s : ℂ} (hZs : Z s ≠ 0) (hZ2s : Z (2 - s) ≠ 0) :
    deriv Z (2 - s) / Z (2 - s) + deriv Z s / Z s =
      ((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2 := by
  let g : ℂ → ℂ := fun w => -((vol : ℂ) / (3 * (Real.pi : ℂ))) * (w - 1) ^ 3 + E
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg_deriv : HasDerivAt g (-((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2) s := by
    have hpow : HasDerivAt (fun w : ℂ => (w - 1) ^ 3) (3 * (s - 1) ^ 2) s := by
      simpa using ((hasDerivAt_id s).sub_const (1 : ℂ)).fun_pow 3
    have hmul : HasDerivAt
        (fun w : ℂ => -((vol : ℂ) / (3 * (Real.pi : ℂ))) * (w - 1) ^ 3)
        (-((vol : ℂ) / (3 * (Real.pi : ℂ))) * (3 * (s - 1) ^ 2)) s :=
      hpow.const_mul _
    have hadd : HasDerivAt g (-((vol : ℂ) / (3 * (Real.pi : ℂ))) * (3 * (s - 1) ^ 2)) s := by
      simpa [g] using hmul.add_const E
    refine hadd.congr_deriv ?_
    field_simp [hpi_ne]
  have hlhs : HasDerivAt (fun w : ℂ => Z (2 - w)) (-deriv Z (2 - s)) s := by
    have hsub : HasDerivAt (fun w : ℂ => (2 : ℂ) - w) (-1 : ℂ) s :=
      ((hasDerivAt_const s (2 : ℂ)).fun_sub (hasDerivAt_id s)).congr_deriv (by ring)
    exact ((hZ (2 - s)).hasDerivAt.comp s hsub).congr_deriv (by ring)
  have hrhs : HasDerivAt (fun w : ℂ => Complex.exp (g w) * Z w)
      (Complex.exp (g s) * (-((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2) * Z s +
        Complex.exp (g s) * deriv Z s) s :=
    (hg_deriv.cexp).mul (hZ s).hasDerivAt
  have heq_fn : (fun w : ℂ => Z (2 - w)) = fun w : ℂ => Complex.exp (g w) * Z w :=
    funext hsym
  have hd_eq : -deriv Z (2 - s) =
      Complex.exp (g s) * (-((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2) * Z s +
        Complex.exp (g s) * deriv Z s := by
    have hrhs' : HasDerivAt (fun w : ℂ => Z (2 - w))
        (Complex.exp (g s) * (-((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2) * Z s +
          Complex.exp (g s) * deriv Z s) s := by
      rwa [heq_fn]
    exact hlhs.unique hrhs'
  have hexp_ne : Complex.exp (g s) ≠ 0 := Complex.exp_ne_zero _
  have hsym_s : Z (2 - s) = Complex.exp (g s) * Z s := hsym s
  have hneg : -deriv Z (2 - s) / Z (2 - s) =
      -((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2 + deriv Z s / Z s := by
    rw [hd_eq, hsym_s]
    field_simp [hexp_ne, hZs]
  have hneg' : -(deriv Z (2 - s) / Z (2 - s)) =
      -((vol : ℂ) / (Real.pi : ℂ)) * (s - 1) ^ 2 + deriv Z s / Z s := by
    rwa [neg_div] at hneg
  have hZ2s_used : Z (2 - s) ≠ 0 := hZ2s
  clear hZ2s_used
  linear_combination -hneg'

/-- Critical-line form of the 3D Selberg functional equation at `s = 1 + ξ`:
`Z'(1 - ξ) / Z(1 - ξ) + Z'(1 + ξ) / Z(1 + ξ) = (Vol(M) / π) ξ²`. -/
theorem func_eq_critical_shift (D : CompactHyperbolic3DSelbergData) {ξ : ℂ}
    (hZ1 : D.Z (1 + ξ) ≠ 0) (hZ2 : D.Z (1 - ξ) ≠ 0) :
    deriv D.Z (1 - ξ) / D.Z (1 - ξ) + deriv D.Z (1 + ξ) / D.Z (1 + ξ) =
      ((D.vol : ℂ) / (Real.pi : ℂ)) * ξ ^ 2 := by
  have h2sub : (2 : ℂ) - ((1 : ℂ) + ξ) = 1 - ξ := by ring
  have hfe := D.func_eq (1 + ξ) hZ1 (by rwa [h2sub])
  rw [h2sub] at hfe
  simpa [add_sub_cancel_left] using hfe

/-! ### 3. Entire Regularization Across `smallRealZeros` and the Borel Kernel `phiSelberg3D` -/

lemma Z_analyticOnNhd (D : CompactHyperbolic3DSelbergData) :
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

lemma Z_analyticOrderAt_ne_top (D : CompactHyperbolic3DSelbergData) (s : ℂ) :
    analyticOrderAt D.Z s ≠ ⊤ := by
  obtain ⟨_, hC⟩ := D.right_bound
  exact entire_analyticOrderAt_ne_top D.Z_entire ⟨3, (hC 3 (by norm_num)).1⟩ s

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
@[expose] def smallPoly3D (D : CompactHyperbolic3DSelbergData) (s : ℂ) : ℂ :=
  ∏ x ∈ D.smallRealZeros, (s - (x : ℂ)) ^ analyticOrderNatAt D.Z (x : ℂ)

private lemma exists_Zreg3D (D : CompactHyperbolic3DSelbergData) :
    ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      (∀ s : ℂ, D.Z s = smallPoly3D D s * F s) ∧
      (∀ x ∈ D.smallRealZeros, F (x : ℂ) ≠ 0) := by
  obtain ⟨_, hC⟩ := D.right_bound
  exact exists_entire_factor_finset D.Z_entire ⟨3, (hC 3 (by norm_num)).1⟩ D.smallRealZeros

/-- Entire regularized 3D Selberg zeta function obtained by dividing `D.Z` by `smallPoly3D D`. -/
def Zreg3D (D : CompactHyperbolic3DSelbergData) : ℂ → ℂ :=
  Classical.choose (exists_Zreg3D D)

lemma Zreg3D_differentiable (D : CompactHyperbolic3DSelbergData) :
    Differentiable ℂ (Zreg3D D) :=
  (Classical.choose_spec (exists_Zreg3D D)).1

lemma Zreg3D_analyticOnNhd (D : CompactHyperbolic3DSelbergData) :
    AnalyticOnNhd ℂ (Zreg3D D) Set.univ :=
  (Zreg3D_differentiable D).differentiableOn.analyticOnNhd isOpen_univ

lemma Z_eq_smallPoly3D_mul_Zreg3D (D : CompactHyperbolic3DSelbergData) (s : ℂ) :
    D.Z s = smallPoly3D D s * Zreg3D D s :=
  (Classical.choose_spec (exists_Zreg3D D)).2.1 s

lemma Zreg3D_ne_zero_of_mem_smallRealZeros (D : CompactHyperbolic3DSelbergData)
    {x : ℝ} (hx : x ∈ D.smallRealZeros) : Zreg3D D (x : ℂ) ≠ 0 :=
  (Classical.choose_spec (exists_Zreg3D D)).2.2 x hx

/-- Because the 3D Selberg zeta function has zero trivial zeros anywhere in `ℂ`, `Zreg3D D` is
nonvanishing on the entire real axis `{s : ℂ | s.im = 0}`. -/
lemma Zreg3D_ne_zero_of_im_zero (D : CompactHyperbolic3DSelbergData) {s : ℂ}
    (him : s.im = 0) : Zreg3D D s ≠ 0 := by
  have hs_real : s = (s.re : ℂ) := Complex.ext rfl (by simp [him])
  by_cases hmem : s.re ∈ D.smallRealZeros
  · rw [hs_real]
    exact Zreg3D_ne_zero_of_mem_smallRealZeros D hmem
  · intro h0
    have hZ0 : D.Z (s.re : ℂ) = 0 := by
      rw [← hs_real, Z_eq_smallPoly3D_mul_Zreg3D, h0, mul_zero]
    exact hmem (D.real_zeros_classified s.re hZ0)

/-- `Zreg3D D` is nonvanishing everywhere off the critical line `Re s = 1` (including the entire
negative half-plane and negative real axis). -/
lemma Zreg3D_ne_zero_of_re_ne_one (D : CompactHyperbolic3DSelbergData) {s : ℂ}
    (hre : s.re ≠ 1) : Zreg3D D s ≠ 0 := by
  by_cases him : s.im = 0
  · exact Zreg3D_ne_zero_of_im_zero D him
  · intro h0
    have hZ0 : D.Z s = 0 := by rw [Z_eq_smallPoly3D_mul_Zreg3D, h0, mul_zero]
    exact hre (D.selberg_rh s hZ0 him)

lemma Zreg3D_one_ne_zero (D : CompactHyperbolic3DSelbergData) :
    Zreg3D D (1 : ℂ) ≠ 0 :=
  Zreg3D_ne_zero_of_im_zero D (by simp)

private lemma exists_Zreg3D_zero_free_ball_one (D : CompactHyperbolic3DSelbergData) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : ℂ, ‖ξ‖ < ε → Zreg3D D (1 + ξ) ≠ 0 := by
  have hcont : ContinuousAt (fun ξ : ℂ => Zreg3D D (1 + ξ)) 0 :=
    ContinuousAt.comp (g := Zreg3D D) (f := fun ξ : ℂ => (1 : ℂ) + ξ)
      (Zreg3D_differentiable D (1 + 0)).continuousAt (continuousAt_const.add continuousAt_id)
  have hev : ∀ᶠ ξ : ℂ in 𝓝 (0 : ℂ), Zreg3D D (1 + ξ) ≠ 0 :=
    hcont.eventually_ne (by simpa using Zreg3D_one_ne_zero D)
  obtain ⟨ε, hε_pos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨ε, hε_pos, fun ξ hξ => hε (by simpa [dist_eq_norm] using hξ)⟩

/-- Raw pole-subtracted critical-line 3D Selberg logarithmic derivative:
`Φ_Γ^{3D,raw}(ξ) = Z'(1 + ξ)/Z(1 + ξ) - ∑_{x ∈ smallRealZeros} m_x / (ξ - (x - 1))`. -/
@[expose] def phiSelberg3DRaw (D : CompactHyperbolic3DSelbergData) (ξ : ℂ) : ℂ :=
  deriv D.Z (1 + ξ) / D.Z (1 + ξ) -
    ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1))

/-- Analytic continuation of `phiSelberg3DRaw D` across all finitely many removable singularities
`ξ = x - 1` (`x ∈ D.smallRealZeros`), defined via the entire quotient `Zreg3D D`:
`Φ_Γ^{3D}(ξ) = Zreg3D'(1 + ξ) / Zreg3D(1 + ξ)`. -/
@[expose] def phiSelberg3D (D : CompactHyperbolic3DSelbergData) (ξ : ℂ) : ℂ :=
  deriv (Zreg3D D) (1 + ξ) / Zreg3D D (1 + ξ)

/-- Formal 3D geodesic von Mangoldt Borel–Laplace series
`G_{Λ,Γ}^{3D}(u) = ∑_{k ≥ 0} (Φ_Γ^{3D})^{(k)}(0) u^{-(k+1)} ∈ ℂ[[1/u]]`. -/
@[expose] def G_Selberg3D (D : CompactHyperbolic3DSelbergData) : PowerSeries ℂ :=
  formalSeries (phiSelberg3D D)

/-- Regularized real-axis 3D Selberg Laplace integral
`G_{Λ,Γ}^{3D,laplace}(u) = ∫_0^∞ e^{-u ξ} Φ_Γ^{3D}(ξ) dξ` (`u > 0`). -/
@[expose] def G_Selberg3D_laplace (D : CompactHyperbolic3DSelbergData) (u : ℝ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (ξ : ℂ)) * phiSelberg3D D (ξ : ℂ)

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

/-- Exact identity `phiSelberg3D D ξ = phiSelberg3DRaw D ξ` at every point where `D.Z (1 + ξ) ≠ 0`. -/
theorem phiSelberg3D_eq_raw (D : CompactHyperbolic3DSelbergData) {ξ : ℂ}
    (hZ : D.Z (1 + ξ) ≠ 0) :
    phiSelberg3D D ξ = phiSelberg3DRaw D ξ := by
  let s : ℂ := 1 + ξ
  have hs_avoid : ∀ x ∈ D.smallRealZeros, analyticOrderNatAt D.Z (x : ℂ) ≠ 0 → s ≠ (x : ℂ) := by
    intro x _ hm heq
    have hne_top : analyticOrderAt D.Z (x : ℂ) ≠ ⊤ := Z_analyticOrderAt_ne_top D (x : ℂ)
    have hne_zero : analyticOrderAt D.Z (x : ℂ) ≠ 0 := by
      rw [← Nat.cast_analyticOrderNatAt hne_top]
      exact_mod_cast hm
    have hZx0 : D.Z (x : ℂ) = 0 :=
      ((Z_analyticOnNhd D (x : ℂ) (Set.mem_univ _)).analyticOrderAt_ne_zero).mp hne_zero
    exact hZ (by rw [show (1 : ℂ) + ξ = s from rfl, heq]; exact hZx0)
  obtain ⟨hP_ne, hP_ld⟩ := deriv_finset_pow_div hs_avoid
  have hP_diff : DifferentiableAt ℂ (smallPoly3D D) s :=
    (Finset.analyticAt_fun_prod D.smallRealZeros fun x _ =>
      (analyticAt_id.sub analyticAt_const).pow _).differentiableAt
  have hZreg_diff : DifferentiableAt ℂ (Zreg3D D) s := Zreg3D_differentiable D s
  have hZreg_ne : Zreg3D D s ≠ 0 := fun h0 => hZ (by rw [Z_eq_smallPoly3D_mul_Zreg3D, h0, mul_zero])
  have hZ_fn : D.Z = fun w => smallPoly3D D w * Zreg3D D w := funext (Z_eq_smallPoly3D_mul_Zreg3D D)
  have hZ_ld : deriv D.Z s / D.Z s =
      deriv (smallPoly3D D) s / smallPoly3D D s + deriv (Zreg3D D) s / Zreg3D D s := by
    have hd : deriv D.Z s =
        deriv (smallPoly3D D) s * Zreg3D D s + smallPoly3D D s * deriv (Zreg3D D) s := by
      rw [hZ_fn]
      exact deriv_fun_mul hP_diff hZreg_diff
    have hP_ne' : smallPoly3D D s ≠ 0 := hP_ne
    rw [hd, Z_eq_smallPoly3D_mul_Zreg3D D s]
    field_simp [hP_ne', hZreg_ne]
  have hsub_sum :
      ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (s - (x : ℂ)) =
        ∑ x ∈ D.smallRealZeros,
          ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1; dsimp only [s]; ring
  unfold phiSelberg3D phiSelberg3DRaw
  change deriv (Zreg3D D) s / Zreg3D D s =
    deriv D.Z s / D.Z s -
      ∑ x ∈ D.smallRealZeros,
        ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1))
  rw [hZ_ld, show deriv (smallPoly3D D) s / smallPoly3D D s =
      ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (s - (x : ℂ)) from hP_ld,
    hsub_sum]
  ring

/-- `phiSelberg3D D` is analytic at every `ξ` where `Zreg3D D (1 + ξ) ≠ 0`. -/
lemma phiSelberg3D_analyticAt_of_Zreg3D_ne_zero (D : CompactHyperbolic3DSelbergData) {ξ : ℂ}
    (h : Zreg3D D (1 + ξ) ≠ 0) :
    AnalyticAt ℂ (phiSelberg3D D) ξ := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) + w) ξ :=
    analyticAt_const.add analyticAt_id
  have hnum : AnalyticAt ℂ (fun w : ℂ => deriv (Zreg3D D) (1 + w)) ξ :=
    ((Zreg3D_analyticOnNhd D).deriv (1 + ξ) (Set.mem_univ _)).comp hshift
  have hden : AnalyticAt ℂ (fun w : ℂ => Zreg3D D (1 + w)) ξ :=
    (Zreg3D_analyticOnNhd D (1 + ξ) (Set.mem_univ _)).comp hshift
  exact hnum.div hden h

/-- Unconditional holomorphicity of `phiSelberg3D D` at `ξ = 0` (even when `λ = 1` is an
eigenvalue and `D.Z 1 = 0`). -/
theorem phiSelberg3D_analyticAt_zero (D : CompactHyperbolic3DSelbergData) :
    AnalyticAt ℂ (phiSelberg3D D) 0 := by
  refine phiSelberg3D_analyticAt_of_Zreg3D_ne_zero D ?_
  rw [add_zero]
  exact Zreg3D_one_ne_zero D

private lemma Z_eventually_ne_zero_nhdsNE (D : CompactHyperbolic3DSelbergData) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, D.Z w ≠ 0 := by
  rcases (Z_analyticOnNhd D z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero with
      hzero | hne
  · exfalso
    have hall := (Z_analyticOnNhd D).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hzero
    obtain ⟨_, hC⟩ := D.right_bound
    exact (hC 3 (by norm_num)).1 (hall (Set.mem_univ 3))
  · exact hne

/-- Unconditional removable singularity limit: for every `x ∈ D.smallRealZeros`,
`phiSelberg3DRaw D ξ` tends to `phiSelberg3D D (x - 1)` as `ξ → x - 1`. -/
theorem phiSelberg3DRaw_tendsto_of_mem_smallRealZeros (D : CompactHyperbolic3DSelbergData)
    {x : ℝ} (hx : x ∈ D.smallRealZeros) :
    Tendsto (phiSelberg3DRaw D) (𝓝[≠] ((x : ℂ) - 1))
      (𝓝 (phiSelberg3D D ((x : ℂ) - 1))) := by
  have hZreg_ne : Zreg3D D (1 + ((x : ℂ) - 1)) ≠ 0 := by
    have hadd : (1 : ℂ) + ((x : ℂ) - 1) = (x : ℂ) := by ring
    rw [hadd]
    exact Zreg3D_ne_zero_of_mem_smallRealZeros D hx
  have hcont : Tendsto (phiSelberg3D D) (𝓝[≠] ((x : ℂ) - 1))
      (𝓝 (phiSelberg3D D ((x : ℂ) - 1))) :=
    (phiSelberg3D_analyticAt_of_Zreg3D_ne_zero D hZreg_ne).continuousAt.continuousWithinAt
  have hZ_ne_ev : ∀ᶠ s in 𝓝[≠] (x : ℂ), D.Z s ≠ 0 := Z_eventually_ne_zero_nhdsNE D (x : ℂ)
  have hshift_tend : Tendsto (fun ξ : ℂ => (1 : ℂ) + ξ)
      (𝓝[≠] ((x : ℂ) - 1)) (𝓝[≠] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun ξ : ℂ => (1 : ℂ) + ξ) ((x : ℂ) - 1) :=
        continuousAt_const.add continuousAt_id
      have hcw : Tendsto (fun ξ : ℂ => (1 : ℂ) + ξ) (𝓝[≠] ((x : ℂ) - 1))
          (𝓝 ((1 : ℂ) + ((x : ℂ) - 1))) :=
        hc.continuousWithinAt
      have hadd : (1 : ℂ) + ((x : ℂ) - 1) = (x : ℂ) := by ring
      rwa [hadd] at hcw
    · filter_upwards [eventually_mem_nhdsWithin] with ξ hξ
      have hξ_ne : ξ ≠ (x : ℂ) - 1 := Set.mem_compl_singleton_iff.mp hξ
      intro heq
      have heq' : (1 : ℂ) + ξ = (x : ℂ) := Set.mem_singleton_iff.mp heq
      apply hξ_ne
      linear_combination heq'
  refine hcont.congr' ?_
  filter_upwards [hshift_tend.eventually hZ_ne_ev] with ξ hZ
  exact phiSelberg3D_eq_raw D hZ

/-- Whenever `D.Z 1 ≠ 0` (`λ = 1` is not an eigenvalue), `phiSelberg3D D` and `phiSelberg3DRaw D`
agree on an open neighborhood of `0`, hence share identical formal series and OGFs. -/
theorem formalSeries_phiSelberg3D_eq_raw (D : CompactHyperbolic3DSelbergData)
    (hZ0 : D.Z (1 : ℂ) ≠ 0) :
    formalSeries (phiSelberg3D D) = formalSeries (phiSelberg3DRaw D) ∧
    ogfOfEGF (phiSelberg3D D) = ogfOfEGF (phiSelberg3DRaw D) := by
  have hcont : ContinuousAt (fun ξ : ℂ => D.Z (1 + ξ)) 0 :=
    ContinuousAt.comp (g := D.Z) (f := fun ξ : ℂ => (1 : ℂ) + ξ)
      (D.Z_entire (1 + 0)).continuousAt (continuousAt_const.add continuousAt_id)
  have hev : phiSelberg3D D =ᶠ[𝓝 (0 : ℂ)] phiSelberg3DRaw D := by
    filter_upwards [hcont.eventually_ne (by simpa using hZ0)] with ξ hZ
    exact phiSelberg3D_eq_raw D hZ
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

/-- **Zero Trivial Zeros in 3D**: `phiSelberg3D D` is unconditionally holomorphic on the entire
open right half-plane `{ξ | 0 < ξ.re}`, the entire open left half-plane `{ξ | ξ.re < 0}`
(including the negative real axis!), and the entire real axis `{ξ | ξ.im = 0}`. -/
theorem phiSelberg3D_holomorphic_off_imag_axis (D : CompactHyperbolic3DSelbergData) :
    AnalyticOnNhd ℂ (phiSelberg3D D) {ξ : ℂ | ξ.re ≠ 0} ∧
    AnalyticOnNhd ℂ (phiSelberg3D D) {ξ : ℂ | ξ.im = 0} := by
  refine ⟨fun ξ hξ => phiSelberg3D_analyticAt_of_Zreg3D_ne_zero D ?_,
          fun ξ hξ => phiSelberg3D_analyticAt_of_Zreg3D_ne_zero D ?_⟩
  · refine Zreg3D_ne_zero_of_re_ne_one D ?_
    change ξ.re ≠ 0 at hξ
    simp only [Complex.add_re, Complex.one_re]
    intro heq
    exact hξ (by linarith)
  · refine Zreg3D_ne_zero_of_im_zero D ?_
    change ξ.im = 0 at hξ
    simpa [Complex.add_im] using hξ

/-! ### 4. Critical-Line Spectral Sequence `rSeq3D` & Simple Poles `+selberg3DMult` -/

/-- Set of positive 3D spectral parameters `r > 0` where `Z (1 + i r) = 0`. -/
@[expose] def selberg3DPosZeros (D : CompactHyperbolic3DSelbergData) : Set ℝ :=
  {r : ℝ | 0 < r ∧ D.Z (1 + I * (r : ℂ)) = 0}

/-- Spectral eigenspace multiplicity `m(r) = analyticOrderNatAt D.Z (1 + i r)`. -/
@[expose] def selberg3DMult (D : CompactHyperbolic3DSelbergData) (r : ℝ) : ℕ :=
  analyticOrderNatAt D.Z (1 + I * (r : ℂ))

/-- Every critical-line zero `1 + i r` has positive finite multiplicity `1 ≤ selberg3DMult D r`
(no eigenvalue-simplicity assumption). -/
theorem selberg3DMult_pos (D : CompactHyperbolic3DSelbergData) {r : ℝ}
    (hr : D.Z (1 + I * (r : ℂ)) = 0) :
    1 ≤ selberg3DMult D r := by
  have hana : AnalyticAt ℂ D.Z (1 + I * (r : ℂ)) :=
    Z_analyticOnNhd D _ (Set.mem_univ _)
  have hne_top : analyticOrderAt D.Z (1 + I * (r : ℂ)) ≠ ⊤ :=
    Z_analyticOrderAt_ne_top D _
  have hne_zero : analyticOrderAt D.Z (1 + I * (r : ℂ)) ≠ 0 :=
    hana.analyticOrderAt_ne_zero.mpr hr
  have hnat_ne : selberg3DMult D r ≠ 0 := by
    intro h0
    apply hne_zero
    rw [← Nat.cast_analyticOrderNatAt hne_top]
    exact_mod_cast h0
  omega

private lemma selberg3DPosZeros_inter_Icc_finite (D : CompactHyperbolic3DSelbergData) (R : ℝ) :
    (selberg3DPosZeros D ∩ Set.Icc 0 R).Finite := by
  let f : ℝ → ℂ := fun r => 1 + I * (r : ℂ)
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
  have hsub : f '' (selberg3DPosZeros D ∩ Set.Icc 0 R) ⊆ K ∩ {w : ℂ | D.Z w = 0} := by
    rintro _ ⟨r, ⟨hrz, hrI⟩, rfl⟩
    exact ⟨⟨r, hrI, rfl⟩, hrz.2⟩
  exact Set.Finite.of_finite_image (hfin_img.subset hsub) hf_inj.injOn

private lemma selberg3DPosZeros_exists_least (D : CompactHyperbolic3DSelbergData) {S : Set ℝ}
    (hsub : S ⊆ selberg3DPosZeros D) (hne : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, m ≤ x := by
  obtain ⟨x₀, hx₀⟩ := hne
  let T : Set ℝ := S ∩ Set.Icc 0 x₀
  have hT_fin : T.Finite :=
    (selberg3DPosZeros_inter_Icc_finite D x₀).subset (Set.inter_subset_inter_left _ hsub)
  have hx₀_pos : 0 < x₀ := (hsub hx₀).1
  have hT_ne : T.Nonempty := ⟨x₀, hx₀, hx₀_pos.le, le_rfl⟩
  let m : ℝ := hT_fin.toFinset.min' (hT_fin.toFinset_nonempty.mpr hT_ne)
  have hm_mem : m ∈ T := hT_fin.mem_toFinset.mp (Finset.min'_mem _ _)
  refine ⟨m, hm_mem.1, fun x hx => ?_⟩
  by_cases hle : x ≤ x₀
  · have hxT : x ∈ T := ⟨hx, (hsub hx).1.le, hle⟩
    exact Finset.min'_le _ _ (hT_fin.mem_toFinset.mpr hxT)
  · exact hm_mem.2.2.trans (le_of_not_ge hle)

private lemma selberg3DPosZeros_above_nonempty (D : CompactHyperbolic3DSelbergData) (a : ℝ) :
    {r ∈ selberg3DPosZeros D | a < r}.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : selberg3DPosZeros D ⊆ selberg3DPosZeros D ∩ Set.Icc 0 a := by
    intro r hr
    refine ⟨hr, hr.1.le, ?_⟩
    by_contra hgt
    push Not at hgt
    have : r ∈ ({x ∈ selberg3DPosZeros D | a < x} : Set ℝ) := ⟨hr, hgt⟩
    rw [h] at this
    exact this
  exact D.crit_infinite ((selberg3DPosZeros_inter_Icc_finite D a).subset hsub)

/-- Canonical strictly increasing enumeration of ALL positive critical-line spectral parameters
`0 < rSeq3D D 0 < rSeq3D D 1 < ... → +∞` with `D.Z (1 + i * rSeq3D D n) = 0`. -/
def rSeq3D (D : CompactHyperbolic3DSelbergData) : ℕ → ℝ
  | 0 => Classical.choose (selberg3DPosZeros_exists_least D Subset.rfl D.crit_infinite.nonempty)
  | n + 1 =>
    let a := rSeq3D D n
    Classical.choose (selberg3DPosZeros_exists_least D
      (S := {r ∈ selberg3DPosZeros D | a < r})
      (fun _ hx => hx.1) (selberg3DPosZeros_above_nonempty D a))

lemma rSeq3D_mem (D : CompactHyperbolic3DSelbergData) (n : ℕ) :
    rSeq3D D n ∈ selberg3DPosZeros D := by
  cases n with
  | zero =>
    exact (Classical.choose_spec
      (selberg3DPosZeros_exists_least D Subset.rfl D.crit_infinite.nonempty)).1
  | succ n =>
    exact (Classical.choose_spec (selberg3DPosZeros_exists_least D
      (S := {r ∈ selberg3DPosZeros D | rSeq3D D n < r})
      (fun _ hx => hx.1)
      (selberg3DPosZeros_above_nonempty D (rSeq3D D n)))).1.1

lemma rSeq3D_pos (D : CompactHyperbolic3DSelbergData) (n : ℕ) : 0 < rSeq3D D n :=
  (rSeq3D_mem D n).1

lemma rSeq3D_zero (D : CompactHyperbolic3DSelbergData) (n : ℕ) :
    D.Z (1 + I * (rSeq3D D n : ℂ)) = 0 :=
  (rSeq3D_mem D n).2

lemma rSeq3D_strictMono (D : CompactHyperbolic3DSelbergData) : StrictMono (rSeq3D D) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact (Classical.choose_spec (selberg3DPosZeros_exists_least D
    (S := {r ∈ selberg3DPosZeros D | rSeq3D D n < r})
    (fun _ hx => hx.1)
    (selberg3DPosZeros_above_nonempty D (rSeq3D D n)))).1.2

lemma rSeq3D_tendsto_atTop (D : CompactHyperbolic3DSelbergData) :
    Tendsto (rSeq3D D) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro R
  have hex : ∃ N : ℕ, R ≤ rSeq3D D N := by
    by_contra! hall
    have hsub : Set.range (rSeq3D D) ⊆ selberg3DPosZeros D ∩ Set.Icc 0 R := by
      rintro _ ⟨n, rfl⟩
      exact ⟨rSeq3D_mem D n, (rSeq3D_pos D n).le, (hall n).le⟩
    exact (Set.infinite_range_of_injective (rSeq3D_strictMono D).injective)
      ((selberg3DPosZeros_inter_Icc_finite D R).subset hsub)
  obtain ⟨N, hN⟩ := hex
  exact ⟨N, fun n hn => hN.trans ((rSeq3D_strictMono D).monotone hn)⟩

lemma rSeq3D_range (D : CompactHyperbolic3DSelbergData) :
    Set.range (rSeq3D D) = selberg3DPosZeros D := by
  ext r
  constructor
  · rintro ⟨n, rfl⟩
    exact rSeq3D_mem D n
  · intro hr
    classical
    have hex : ∃ n : ℕ, r ≤ rSeq3D D n := by
      obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp (rSeq3D_tendsto_atTop D)) r
      exact ⟨N, hN N le_rfl⟩
    let n : ℕ := Nat.find hex
    have hn_le : r ≤ rSeq3D D n := Nat.find_spec hex
    refine ⟨n, ?_⟩
    cases hne : n with
    | zero =>
      have hmin := (Classical.choose_spec
        (selberg3DPosZeros_exists_least D Subset.rfl D.crit_infinite.nonempty)).2 r hr
      rw [hne] at hn_le
      exact le_antisymm hmin hn_le
    | succ k =>
      have hk_lt : rSeq3D D k < r := by
        have hnot : ¬(r ≤ rSeq3D D k) := Nat.find_min hex (by omega : k < n)
        exact lt_of_not_ge hnot
      have hmin := (Classical.choose_spec (selberg3DPosZeros_exists_least D
        (S := {x ∈ selberg3DPosZeros D | rSeq3D D k < x})
        (fun _ hx => hx.1)
        (selberg3DPosZeros_above_nonempty D (rSeq3D D k)))).2 r ⟨hr, hk_lt⟩
      rw [hne] at hn_le
      exact le_antisymm hmin hn_le

/-- **Simple Pole Principal Part `+m(r) / (ξ - i r)` at Every Critical-Line Zero (Arbitrary
Multiplicity)**: For every `r > 0` with `D.Z (1 + i r) = 0`,
`phiSelberg3D D ξ - selberg3DMult D r / (ξ - i r)` extends continuously to `ξ = i r`, with positive
integer residue `selberg3DMult D r ≥ 1`. -/
theorem phiSelberg3D_simple_pole_principalPart (D : CompactHyperbolic3DSelbergData) {r : ℝ}
    (hr_pos : 0 < r) (hr : D.Z (1 + I * (r : ℂ)) = 0) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun ξ : ℂ => phiSelberg3D D ξ - ((selberg3DMult D r : ℕ) : ℂ) / (ξ - I * (r : ℂ)))
        (𝓝[≠] (I * (r : ℂ))) (𝓝 L) := by
  let s₀ : ℂ := 1 + I * (r : ℂ)
  let m : ℕ := selberg3DMult D r
  have hm_pos : 1 ≤ m := selberg3DMult_pos D hr
  have hP_an : AnalyticAt ℂ (smallPoly3D D) s₀ :=
    Finset.analyticAt_fun_prod D.smallRealZeros fun x _ =>
      (analyticAt_id.sub analyticAt_const).pow _
  have hP_ne : smallPoly3D D s₀ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro heq
    have him := congrArg Complex.im heq
    simp [s₀] at him
    linarith
  have hZreg_an : AnalyticAt ℂ (Zreg3D D) s₀ := Zreg3D_analyticOnNhd D s₀ (Set.mem_univ _)
  have hZreg_ord_eq : analyticOrderAt (Zreg3D D) s₀ = analyticOrderAt D.Z s₀ := by
    have hfn : D.Z = smallPoly3D D * Zreg3D D := funext (Z_eq_smallPoly3D_mul_Zreg3D D)
    rw [hfn, analyticOrderAt_mul hP_an hZreg_an, hP_an.analyticOrderAt_eq_zero.mpr hP_ne, zero_add]
  have hZreg_ne_top : analyticOrderAt (Zreg3D D) s₀ ≠ ⊤ := by
    rw [hZreg_ord_eq]
    exact Z_analyticOrderAt_ne_top D s₀
  have hZreg_nat_eq : analyticOrderNatAt (Zreg3D D) s₀ = m := by
    simp only [analyticOrderNatAt, hZreg_ord_eq, m, selberg3DMult, s₀]
  obtain ⟨g, hg_ana, hg0, hfg⟩ := hZreg_an.analyticOrderAt_ne_top.mp hZreg_ne_top
  let h : ℂ → ℂ := fun ξ => g (1 + ξ)
  have hshift : AnalyticAt ℂ (fun ξ : ℂ => (1 : ℂ) + ξ) (I * (r : ℂ)) :=
    analyticAt_const.add analyticAt_id
  have hh_ana : AnalyticAt ℂ h (I * (r : ℂ)) :=
    AnalyticAt.comp (g := g) (f := fun ξ : ℂ => (1 : ℂ) + ξ) hg_ana hshift
  have hh0 : h (I * (r : ℂ)) ≠ 0 := hg0
  have hshift_tend : Tendsto (fun ξ : ℂ => (1 : ℂ) + ξ) (𝓝 (I * (r : ℂ))) (𝓝 s₀) :=
    hshift.continuousAt
  have hZreg_ev : (fun ξ : ℂ => Zreg3D D (1 + ξ)) =ᶠ[𝓝 (I * (r : ℂ))]
      fun ξ : ℂ => (ξ - I * (r : ℂ)) ^ m * h ξ := by
    filter_upwards [hshift_tend.eventually hfg] with ξ hξ
    have hsub : (1 : ℂ) + ξ - s₀ = ξ - I * (r : ℂ) := by dsimp only [s₀]; ring
    change Zreg3D D (1 + ξ) = (ξ - I * (r : ℂ)) ^ m * g (1 + ξ)
    have hξ' : Zreg3D D (1 + ξ) = (1 + ξ - s₀) ^ m * g (1 + ξ) := by
      have hξ0 : Zreg3D D (1 + ξ) =
          (1 + ξ - s₀) ^ analyticOrderNatAt (Zreg3D D) s₀ * g (1 + ξ) := by
        simpa [smul_eq_mul] using hξ
      rwa [hZreg_nat_eq] at hξ0
    rw [hξ', hsub]
  have hderiv_Zreg : ∀ᶠ ξ in 𝓝 (I * (r : ℂ)),
      deriv (Zreg3D D) (1 + ξ) =
        (m : ℂ) * (ξ - I * (r : ℂ)) ^ (m - 1) * h ξ + (ξ - I * (r : ℂ)) ^ m * deriv h ξ := by
    have hcomp_deriv : ∀ᶠ ξ in 𝓝 (I * (r : ℂ)),
        deriv (fun w : ℂ => Zreg3D D (1 + w)) ξ = deriv (Zreg3D D) (1 + ξ) := by
      filter_upwards with ξ
      have hd : HasDerivAt (fun w : ℂ => Zreg3D D (1 + w))
          (deriv (Zreg3D D) (1 + ξ) * 1) ξ :=
        (Zreg3D_differentiable D (1 + ξ)).hasDerivAt.comp ξ
          ((hasDerivAt_const ξ (1 : ℂ)).add (hasDerivAt_id ξ) |>.congr_deriv (zero_add 1))
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
    have hzeq' : (fun w : ℂ => Zreg3D D (1 + w)) =ᶠ[𝓝 ξ]
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
  change deriv h ξ / h ξ = deriv (Zreg3D D) (1 + ξ) / Zreg3D D (1 + ξ) -
    (m : ℂ) / (ξ - I * (r : ℂ))
  rw [hze, hdz, hpow_split]
  field_simp [hsub_ne, hpow1_ne, hhn]
  ring

/-- **Simple Pole & Nonzero Positive-Integer Residue Theorem at Any Critical-Line Zero**:
For every `r > 0` with `D.Z (1 + i r) = 0`, `(ξ - i r) * phiSelberg3D D ξ → +m(r) ≠ 0`
as `ξ → i r`, where `m(r) = selberg3DMult D r ≥ 1`. -/
theorem phiSelberg3D_simple_pole_at_zero (D : CompactHyperbolic3DSelbergData) {r : ℝ}
    (hr_pos : 0 < r) (hr : D.Z (1 + I * (r : ℂ)) = 0) :
    Filter.Tendsto (fun ξ : ℂ => (ξ - I * (r : ℂ)) * phiSelberg3D D ξ)
      (𝓝[≠] (I * (r : ℂ))) (𝓝 (((selberg3DMult D r : ℕ) : ℂ))) ∧
    (((selberg3DMult D r : ℕ) : ℂ)) ≠ 0 := by
  obtain ⟨L, hL⟩ := phiSelberg3D_simple_pole_principalPart D hr_pos hr
  have hm_ne : (((selberg3DMult D r : ℕ) : ℂ)) ≠ 0 := by
    have hm_pos : 1 ≤ selberg3DMult D r := selberg3DMult_pos D hr
    exact_mod_cast (show selberg3DMult D r ≠ 0 by omega)
  refine ⟨?_, hm_ne⟩
  have hsub_cont : ContinuousAt (fun ξ : ℂ => ξ - I * (r : ℂ)) (I * (r : ℂ)) :=
    continuousAt_id.sub continuousAt_const
  have hsub0 : Tendsto (fun ξ : ℂ => ξ - I * (r : ℂ)) (𝓝[≠] (I * (r : ℂ))) (𝓝 (0 : ℂ)) := by
    have h0 : I * (r : ℂ) - I * (r : ℂ) = 0 := sub_self _
    exact h0 ▸ hsub_cont.continuousWithinAt
  have hmul := (hsub0.mul hL).add (tendsto_const_nhds (x := ((selberg3DMult D r : ℕ) : ℂ)))
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
For any `α₀` and any zero-free disk radius `ε > 0` around `0`, `phiSelberg3D D` is holomorphic on
`rotatedPuncturedWedge (Real.pi / 2) α₀ ε (rSeq3D D)`. -/
theorem phiSelberg3D_analyticOn_rotatedPuncturedWedge (D : CompactHyperbolic3DSelbergData)
    {α₀ ε : ℝ} (hball : ∀ ξ : ℂ, ‖ξ‖ < ε → Zreg3D D (1 + ξ) ≠ 0) :
    AnalyticOnNhd ℂ (phiSelberg3D D)
      (rotatedPuncturedWedge (Real.pi / 2) α₀ ε (rSeq3D D)) := by
  intro ξ hξ
  refine phiSelberg3D_analyticAt_of_Zreg3D_ne_zero D ?_
  rcases hξ with ⟨hwedge, hnot_pole⟩
  rw [exp_neg_I_pi_div_two] at hwedge hnot_pole
  rcases hwedge with hball_mem | ⟨him_pos, _⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_neg, Complex.norm_I, one_mul] at hball_mem
    exact hball ξ hball_mem
  · have hξ_im : 0 < ξ.im := by
      simpa [Complex.mul_re] using him_pos
    intro h0
    have hZ0 : D.Z (1 + ξ) = 0 := by rw [Z_eq_smallPoly3D_mul_Zreg3D, h0, mul_zero]
    have hs_im : ((1 : ℂ) + ξ).im ≠ 0 := by
      simpa [Complex.add_im] using hξ_im.ne'
    have hcrit := D.selberg_rh (1 + ξ) hZ0 hs_im
    simp only [Complex.add_re, Complex.one_re] at hcrit
    have hξ_re : ξ.re = 0 := by linarith
    have hξ_eq : ξ = I * (ξ.im : ℂ) := Complex.ext (by simp [hξ_re]) (by simp)
    have hmem_Z : ξ.im ∈ selberg3DPosZeros D := ⟨hξ_im, by rwa [← hξ_eq]⟩
    rw [← rSeq3D_range D] at hmem_Z
    obtain ⟨m, hm⟩ := hmem_Z
    apply hnot_pole
    refine ⟨m, ?_⟩
    rw [hξ_eq, ← hm]
    have hmul : -I * (I * (rSeq3D D m : ℂ)) = ((-I) * I) * (rSeq3D D m : ℂ) := by ring
    rw [hmul]
    simp

/-! ### 5. Elementary `O(1)` Right-Ray & `O(v²)` Left-Ray Exponential-Type Bounds (No Trig!) -/

private def smallMultSum3D (D : CompactHyperbolic3DSelbergData) : ℝ :=
  ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℝ)

private lemma smallMultSum3D_nonneg (D : CompactHyperbolic3DSelbergData) :
    0 ≤ smallMultSum3D D :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

private lemma norm_smallPoleSum3D_le (D : CompactHyperbolic3DSelbergData) {ξ : ℂ}
    (hdist : ∀ x ∈ D.smallRealZeros, 1 ≤ ‖ξ - ((x : ℂ) - 1)‖) :
    ‖∑ x ∈ D.smallRealZeros,
        ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1))‖ ≤
      smallMultSum3D D := by
  calc ‖∑ x ∈ D.smallRealZeros,
          ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1))‖
      ≤ ∑ x ∈ D.smallRealZeros,
          ‖((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x ∈ D.smallRealZeros, ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [norm_div, Complex.norm_natCast]
        have h1 : 1 ≤ ‖ξ - ((x : ℂ) - 1)‖ := hdist x hx
        exact div_le_self (Nat.cast_nonneg _) h1

private lemma sq_le_four_mul_exp {v : ℝ} (hv : 0 ≤ v) :
    v ^ 2 ≤ 4 * Real.exp v := by
  have h1 : v / 2 ≤ Real.exp (v / 2) := by linarith [Real.add_one_le_exp (v / 2)]
  have h2 : (v / 2) * (v / 2) ≤ Real.exp (v / 2) * Real.exp (v / 2) :=
    mul_le_mul h1 h1 (by linarith) (Real.exp_pos _).le
  have hexp : Real.exp (v / 2) * Real.exp (v / 2) = Real.exp v := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at h2
  nlinarith

/-- **Right-Half-Plane Ray `O(1)` Exponential-Type Bound**:
Along ANY ray `e^{i σ} ℝ_{≥0}` in the open right half-plane (`0 < cos σ`), including both the
positive real axis (`σ = 0`) and the right flanking ray (`σ = π / 2 - π / 8`), `phiSelberg3D D`
is uniformly bounded (`ExpType` with exponent `0`). -/
theorem phiSelberg3D_expType_right_ray (D : CompactHyperbolic3DSelbergData) {σ : ℝ}
    (hcos : 0 < Real.cos σ) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (phiSelberg3D D)) := by
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
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ (phiSelberg3D D) v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ (phiSelberg3D D) (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simpa using phiSelberg3D_analyticAt_zero D
      · have hre_ne : (μ * (v : ℂ)).re ≠ 0 := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
          exact (mul_pos hcos hv_pos).ne'
        exact (phiSelberg3D_holomorphic_off_imag_axis D).1 (μ * (v : ℂ)) hre_ne
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiSelberg3D D (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiSelberg3D D) (f := fun x : ℝ => μ * (x : ℂ))
        hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁⟩ := D.right_bound
  let C : ℝ := max (max M₀ 0) (max M₁ 0 + smallMultSum3D D)
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
    have hs_re : 3 ≤ ((1 : ℂ) + μ * (v : ℂ)).re := by
      simp only [Complex.add_re, Complex.one_re]; linarith
    obtain ⟨hZ_ne, hZ_bd⟩ := hM₁ (1 + μ * (v : ℂ)) hs_re
    have hdist : ∀ x ∈ D.smallRealZeros, 1 ≤ ‖μ * (v : ℂ) - ((x : ℂ) - 1)‖ := by
      intro x hx
      have hx2 : x ≤ 2 := (D.smallRealZeros_mem x hx).2
      have h1 : (μ * (v : ℂ) - ((x : ℂ) - 1)).re ≤ ‖μ * (v : ℂ) - ((x : ℂ) - 1)‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h1
      linarith
    have hphi_le : ‖phiSelberg3D D (μ * (v : ℂ))‖ ≤ max M₁ 0 + smallMultSum3D D := by
      rw [phiSelberg3D_eq_raw D hZ_ne, phiSelberg3DRaw]
      calc ‖deriv D.Z (1 + μ * (v : ℂ)) / D.Z (1 + μ * (v : ℂ)) -
              ∑ x ∈ D.smallRealZeros,
                ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (μ * (v : ℂ) - ((x : ℂ) - 1))‖
          ≤ ‖deriv D.Z (1 + μ * (v : ℂ)) / D.Z (1 + μ * (v : ℂ))‖ +
              ‖∑ x ∈ D.smallRealZeros,
                ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (μ * (v : ℂ) - ((x : ℂ) - 1))‖ :=
            norm_sub_le _ _
        _ ≤ M₁ + smallMultSum3D D := add_le_add hZ_bd (norm_smallPoleSum3D_le D hdist)
        _ ≤ max M₁ 0 + smallMultSum3D D := add_le_add (le_max_left M₁ 0) le_rfl
    change ‖μ * phiSelberg3D D (μ * (v : ℂ))‖ ≤ C
    rw [norm_mul, hμ_norm, one_mul]
    exact hphi_le.trans (le_max_right _ _)

/-- **Left-Half-Plane Ray Pure-Quadratic `O(v²)` Exponential-Type Bound (No Trig Needed)**:
Along ANY ray `e^{i σ} ℝ_{≥0}` in the entire open left half-plane (`cos σ < 0`, including both the
left flanking ray `σ = π / 2 + π / 8` and even the negative real axis `σ = π`!), `phiSelberg3D D`
has pure quadratic growth `O(v²)` and hence `ExpType`, proved directly from `func_eq_critical_shift`
and `D.right_bound` without any trigonometric strip bound. -/
theorem phiSelberg3D_expType_left_ray (D : CompactHyperbolic3DSelbergData) {σ : ℝ}
    (hcos : Real.cos σ < 0) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (phiSelberg3D D)) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I σ
  have hμ_re : μ.re = Real.cos σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re σ
  let R₀ : ℝ := 2 / (-Real.cos σ)
  have hR₀_pos : 0 < R₀ := div_pos two_pos (neg_pos.mpr hcos)
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ (phiSelberg3D D) v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ (phiSelberg3D D) (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simpa using phiSelberg3D_analyticAt_zero D
      · have hre_ne : (μ * (v : ℂ)).re ≠ 0 := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
          exact (mul_neg_of_neg_of_pos hcos hv_pos).ne
        exact (phiSelberg3D_holomorphic_off_imag_axis D).1 (μ * (v : ℂ)) hre_ne
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiSelberg3D D (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiSelberg3D D) (f := fun x : ℝ => μ * (x : ℂ))
        hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁⟩ := D.right_bound
  let K₀ : ℝ := max M₁ 0 + smallMultSum3D D
  let K₂ : ℝ := D.vol / Real.pi
  have hK₀_nn : 0 ≤ K₀ := add_nonneg (le_max_right M₁ 0) (smallMultSum3D_nonneg D)
  have hK₂_nn : 0 ≤ K₂ := div_nonneg D.hvol.le Real.pi_pos.le
  let C : ℝ := max (max M₀ 0) (K₀ + 4 * K₂)
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 1, hC_nn, zero_le_one, fun v hv => ?_⟩
  rw [one_mul]
  by_cases hvR : v ≤ R₀
  · calc ‖Minor.pull μ (phiSelberg3D D) v‖ ≤ M₀ := hM₀ v ⟨hv, hvR⟩
      _ ≤ max M₀ 0 := le_max_left _ _
      _ ≤ C := le_max_left _ _
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_left (Real.one_le_exp hv) hC_nn
  · push Not at hvR
    have hv_pos : 0 < v := lt_trans hR₀_pos hvR
    let ξ : ℂ := μ * (v : ℂ)
    have hξ_re : ξ.re < -2 := by
      dsimp only [ξ]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have := (div_lt_iff₀ (neg_pos.mpr hcos)).mp hvR
      linarith
    have hξ_norm : ‖ξ‖ = v := by
      dsimp only [ξ]
      rw [norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
    have hrefl_re : 3 ≤ ((1 : ℂ) - ξ).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith
    obtain ⟨hZ_refl_ne, hZ_refl_bd⟩ := hM₁ (1 - ξ) hrefl_re
    have hZ_ne : D.Z (1 + ξ) ≠ 0 := by
      intro h0
      by_cases him : ((1 : ℂ) + ξ).im = 0
      · have hs_real : (1 : ℂ) + ξ = (((1 : ℂ) + ξ).re : ℂ) :=
          Complex.ext rfl (by simp [him])
        have hmem := D.real_zeros_classified ((1 : ℂ) + ξ).re (by rwa [← hs_real])
        have hnonneg := (D.smallRealZeros_mem _ hmem).1
        simp only [Complex.add_re, Complex.one_re] at hnonneg
        linarith
      · have hcrit := D.selberg_rh (1 + ξ) h0 him
        simp only [Complex.add_re, Complex.one_re] at hcrit
        linarith
    have hfe := func_eq_critical_shift D hZ_ne hZ_refl_ne
    have hld_eq : deriv D.Z (1 + ξ) / D.Z (1 + ξ) =
        ((D.vol : ℂ) / (Real.pi : ℂ)) * ξ ^ 2 - deriv D.Z (1 - ξ) / D.Z (1 - ξ) := by
      linear_combination hfe
    have hpoly_bd : ‖((D.vol : ℂ) / (Real.pi : ℂ)) * ξ ^ 2‖ = K₂ * v ^ 2 := by
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos D.hvol, abs_of_pos Real.pi_pos, hξ_norm]
    have hdist : ∀ x ∈ D.smallRealZeros, 1 ≤ ‖ξ - ((x : ℂ) - 1)‖ := by
      intro x hx
      have hx0 : 0 ≤ x := (D.smallRealZeros_mem x hx).1
      have h1 : -(ξ - ((x : ℂ) - 1)).re ≤ ‖ξ - ((x : ℂ) - 1)‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h1
      linarith
    have hphi_le : ‖phiSelberg3D D ξ‖ ≤ K₀ + K₂ * v ^ 2 := by
      rw [phiSelberg3D_eq_raw D hZ_ne, phiSelberg3DRaw, hld_eq]
      have h1 := norm_sub_le
        (((D.vol : ℂ) / (Real.pi : ℂ)) * ξ ^ 2 - deriv D.Z (1 - ξ) / D.Z (1 - ξ))
        (∑ x ∈ D.smallRealZeros,
          ((analyticOrderNatAt D.Z (x : ℂ) : ℕ) : ℂ) / (ξ - ((x : ℂ) - 1)))
      have h2 := norm_sub_le
        (((D.vol : ℂ) / (Real.pi : ℂ)) * ξ ^ 2)
        (deriv D.Z (1 - ξ) / D.Z (1 - ξ))
      have h3 := norm_smallPoleSum3D_le D hdist
      have hM1 : M₁ ≤ max M₁ 0 := le_max_left M₁ 0
      dsimp only [K₀]
      linarith
    change ‖μ * phiSelberg3D D ξ‖ ≤ C * Real.exp v
    rw [norm_mul, hμ_norm, one_mul]
    have h1_le_exp : 1 ≤ Real.exp v := Real.one_le_exp hv
    have hv2_le_exp : v ^ 2 ≤ 4 * Real.exp v := sq_le_four_mul_exp hv
    calc ‖phiSelberg3D D ξ‖ ≤ K₀ + K₂ * v ^ 2 := hphi_le
      _ ≤ K₀ * Real.exp v + K₂ * (4 * Real.exp v) :=
        add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hv2_le_exp hK₂_nn)
      _ = (K₀ + 4 * K₂) * Real.exp v := by ring
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos v).le

/-- Right flanking-ray exponential-type bound at `σ = π / 2 - π / 8`. -/
theorem phiSelberg3D_expType_right (D : CompactHyperbolic3DSelbergData) :
    ExpType (Minor.pull (Complex.exp (I * ((Real.pi / 2 - Real.pi / 8 : ℝ) : ℂ)))
      (phiSelberg3D D)) := by
  have hcos : 0 < Real.cos (Real.pi / 2 - Real.pi / 8) := by
    rw [Real.cos_pi_div_two_sub]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  exact phiSelberg3D_expType_right_ray D hcos

/-- Left flanking-ray exponential-type bound at `σ = π / 2 + π / 8`. -/
theorem phiSelberg3D_expType_left (D : CompactHyperbolic3DSelbergData) :
    ExpType (Minor.pull (Complex.exp (I * ((Real.pi / 2 + Real.pi / 8 : ℝ) : ℂ)))
      (phiSelberg3D D)) := by
  have hcos : Real.cos (Real.pi / 2 + Real.pi / 8) < 0 := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub]
    have hsin : 0 < Real.sin (Real.pi / 8) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    linarith
  exact phiSelberg3D_expType_left_ray D hcos

/-! ### 6. Packaging `HigherOrderBorelData` & Real-Axis Laplace Asymptotics -/

/-- **Unconditional `HigherOrderBorelData` Witness for Compact 3D Hyperbolic Manifolds**:
Along the rotated critical-line ray `θ₀ = π / 2` with wedge half-angle `α₀ = π / 4` and flanking
rays `θ₀ ± π / 8`, `phiSelberg3D D` has simple poles (`ord _ = 1`) at `i * rSeq3D D m` with exact
nonzero positive integer residues `selberg3DMult D (rSeq3D D m) ∈ ℤ_{≥1}`. -/
def phiSelberg3D_higherOrderBorelData (D : CompactHyperbolic3DSelbergData) :
    HigherOrderBorelData (phiSelberg3D D) (Real.pi / 2) (rSeq3D D) (fun _ => 1)
      (fun m s => if s = 1 then ((selberg3DMult D (rSeq3D D m) : ℕ) : ℂ) else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 8
  ε := Classical.choose (exists_Zreg3D_zero_free_ball_one D)
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := (Classical.choose_spec (exists_Zreg3D_zero_free_ball_one D)).1
  ω_pos := rSeq3D_pos D 0
  ω_mono := rSeq3D_strictMono D
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by
    simp only [↓reduceIte]
    have hm_pos : 1 ≤ selberg3DMult D (rSeq3D D m) := selberg3DMult_pos D (rSeq3D_zero D m)
    exact_mod_cast (show selberg3DMult D (rSeq3D D m) ≠ 0 by omega)
  analyticOn :=
    phiSelberg3D_analyticOn_rotatedPuncturedWedge D
      (Classical.choose_spec (exists_Zreg3D_zero_free_ball_one D)).2
  pole_principalPart := fun m => by
    obtain ⟨L, hL⟩ := phiSelberg3D_simple_pole_principalPart D (rSeq3D_pos D m) (rSeq3D_zero D m)
    refine ⟨L, ?_⟩
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one, exp_I_pi_div_two]
    exact hL
  expType_plus := phiSelberg3D_expType_left D
  expType_minus := phiSelberg3D_expType_right D

private lemma minor_value_hasAsympExp_selberg3D (a : Minor) {U : Set ℂ} {d : ℂ}
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
    filter_upwards [hC, hjet_eq, ht_far.eventually rep_j, eventually_ge_atTop (1 : ℝ)] with
      u hu hje hre hu1
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
    have hsum : ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (d_u^[j] a.toSeries) * ((u : ℂ)⁻¹ ^ k) =
        (ej.residual a).atom + ∑ k ∈ Finset.range m,
          iteratedDeriv k (ej.residual a).density 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
      rw [← hser_j, Finset.sum_range_succ']
      simp only [Minor.toSeries, PowerSeries.coeff_mk, pow_zero, mul_one, add_comm]
    rw [hsum]
    exact hu

/-- **Unconditional All-Orders Asymptotic Expansion of `G_Selberg3D_laplace`**:
For every derivative order `j : ℕ`, `iteratedDeriv j (G_Selberg3D_laplace D)` shares the exact
all-orders `1 / u` asymptotic expansion `d_u^[j] (formalSeries (phiSelberg3D D))` as `u → +∞`. -/
theorem G_Selberg3D_laplace_hasAsympExp (D : CompactHyperbolic3DSelbergData) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (G_Selberg3D_laplace D))
      (d_u^[j] (formalSeries (phiSelberg3D D))) := by
  obtain ⟨ε, hε_pos, hball⟩ := exists_Zreg3D_zero_free_ball_one D
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
  let a : Minor := Minor.mk 0 (phiSelberg3D D)
  have ha_good : a.Good U 1 := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases hz with hzb | hzr
      · rw [Metric.mem_ball, dist_zero_right] at hzb
        exact phiSelberg3D_analyticAt_of_Zreg3D_ne_zero D (hball z hzb)
      · exact (phiSelberg3D_holomorphic_off_imag_axis D).1 z hzr.ne'
    · have hexp0 := phiSelberg3D_expType_right_ray D (σ := 0) (by simp)
      simpa using hexp0
  have hval : (fun u : ℝ => a.value 1 (u : ℂ)) = G_Selberg3D_laplace D := by
    funext u
    simp [a, Minor.value, complexLaplace, damped, Minor.pull, G_Selberg3D_laplace]
  have hser : a.toSeries = formalSeries (phiSelberg3D D) := by
    ext n
    cases n <;> simp [a, Minor.toSeries, formalSeries]
  rw [← hval, ← hser]
  exact minor_value_hasAsympExp_selberg3D a hU hray ha_good (by simp) j

/-! ### 7. Master Unconditional 3D Hyperbolic Selberg–Stokes–Vandermonde Theorems -/

/-- **Master Theorem 1 (Strong `ℂ({t})` D-Transcendence of the 3D Geodesic von Mangoldt OGF)**:
For any compact orientable hyperbolic 3-manifold `M = ℍ³ / Γ`, the ordinary generating function
`ogfOfEGF (phiSelberg3D D) = ∑_{n ≥ 0} (Φ_Γ^{3D})^{(n)}(0) t^n` is unconditionally **strongly
differentially transcendental over convergent meromorphic germs `ℂ({t})`**
(zero Riemann Hypothesis assumption, zero eigenvalue-simplicity assumption, zero trivial zeros). -/
theorem selberg3D_ogf_stronglyDTrans (D : CompactHyperbolic3DSelbergData) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (phiSelberg3D D)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (phiSelberg3D_higherOrderBorelData D)

/-- **Master Theorem 2 (Strong `ℂ({t})` D-Transcendence of `formalSeries (phiSelberg3D D)`)**:
For any compact orientable hyperbolic 3-manifold `M = ℍ³ / Γ`, the shifted Borel–Laplace formal
series `G_Selberg3D D = formalSeries (phiSelberg3D D)` is unconditionally **strongly differentially
transcendental over convergent meromorphic germs `ℂ({t})`**. -/
theorem selberg3D_formalSeries_stronglyDTrans (D : CompactHyperbolic3DSelbergData) :
    StronglyDTransOverMeromorphicGerms (formalSeries (phiSelberg3D D)) :=
  stronglyDTrans_of_higher_order_borel (phiSelberg3D_higherOrderBorelData D)

/-- **Master Theorem 3 (`ℂ{1/u}` Analytic Differential Transcendence of `G_Selberg3D_laplace`)**:
The regularized real-axis 3D Selberg Laplace integral `G_Selberg3D_laplace D` satisfies NO nonzero
convergent-germ algebraic differential equation over `ℂ{1/u}` eventually as `u → +∞`. -/
theorem selberg3D_laplace_no_conv_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg3D_laplace D) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) :
    Q = 0 :=
  no_conv_ade_of_higher_order_borel_asymp (phiSelberg3D_higherOrderBorelData D)
    (G_Selberg3D_laplace_hasAsympExp D) Q hQ

/-- **Master Theorem 4 (`ℂ(u)` Analytic Differential Transcendence of `G_Selberg3D_laplace`)**:
The regularized real-axis 3D Selberg Laplace integral `G_Selberg3D_laplace D` satisfies NO nonzero
rational-coefficient algebraic differential equation over `ℂ(u)` eventually as `u → +∞`. -/
theorem selberg3D_laplace_no_rat_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg3D_laplace D) u)
        (evalRatU P (u : ℂ)) = 0) :
    P = 0 :=
  no_rat_ade_of_higher_order_borel (phiSelberg3D_higherOrderBorelData D)
    (G_Selberg3D_laplace_hasAsympExp D) P hP

/-- **Master Theorem 5 (Formal `ℂ(u)` Non-Autonomous D-Transcendence of `G_Selberg3D`)**:
The formal series `G_Selberg3D D` satisfies NO nonzero rational-coefficient ADE over `ℂ(u)`. -/
theorem selberg3D_formalSeries_no_rat_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (phiSelberg3D D)) P = 0) :
    P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade (phiSelberg3D_higherOrderBorelData D) P hP

/-- **Master Theorem 6 (Formal `ℂ{1/u}` Non-Autonomous `d_u`-Transcendence of `G_Selberg3D`)**:
The formal series `G_Selberg3D D` satisfies NO nonzero convergent-germ `d_u`-ADE over `ℂ{1/u}`. -/
theorem selberg3D_formalSeries_no_conv_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries (phiSelberg3D D)) Q = 0) :
    Q = 0 :=
  no_conv_ade_of_higher_order_borel (phiSelberg3D_higherOrderBorelData D) Q hQ

/-- **Master Theorem 7 (`ℂ[u]` Analytic Differential Transcendence of `G_Selberg3D_laplace`)**:
The regularized real-axis 3D Selberg Laplace integral `G_Selberg3D_laplace D` satisfies NO nonzero
non-autonomous polynomial differential equation over `ℂ[u]` eventually as `u → +∞`. -/
theorem selberg3D_laplace_no_poly_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg3D_laplace D) u)
        (evalU P (u : ℂ)) = 0) :
    P = 0 :=
  no_nonautonomous_ade_of_higher_order_borel (phiSelberg3D_higherOrderBorelData D)
    (G_Selberg3D_laplace_hasAsympExp D) P hP

/-- **Master Theorem 8 (Autonomous Analytic Differential Transcendence of `G_Selberg3D_laplace`)**:
The regularized real-axis 3D Selberg Laplace integral `G_Selberg3D_laplace D` satisfies NO nonzero
autonomous polynomial differential equation over `ℂ` eventually as `u → +∞`. -/
theorem selberg3D_laplace_no_autonomous_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg3D_laplace D) u) P = 0) :
    P = 0 :=
  no_autonomous_ade_of_higher_order_borel (phiSelberg3D_higherOrderBorelData D)
    (G_Selberg3D_laplace_hasAsympExp D) P hP

end
end PakPrimes.SelbergHyperbolic3DDTrans
