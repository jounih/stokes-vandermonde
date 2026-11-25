module

public import PakPrimes.ThermalGasParity
public import PakPrimes.DivisorAndMacMahon
public import Mathlib.NumberTheory.ModularForms.RamanujanFormula
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Relativistic Ideal Gas Equation of State `P(ε)`, Massive Casimir Parity, and Thermal Conformal Scalar Parity on `S^{d-1} × S¹`

This module extends `PakPrimes.ThermalGasParity` and `PakPrimes.DivisorAndMacMahon` with three
unconditional physics parity theorems (fully proved, strictly `[propext, Classical.choice, Quot.sound]`):

1. **Temperature-Eliminated Equation of State `P(ε)` & Sound Speed `c_s²(ε)` in 1D & 3D:**
   For every positive mass `m > 0`, the relativistic Bose and Fermi pressures in `d = 1` and `d = 3`
   are real-analytic on `(0, ∞)` with strictly positive entropy density `P'(T) > 0`, strictly
   positive energy density `ε(T) = T P'(T) - P(T) > 0`, and strictly positive heat capacity
   `ε'(T) = T P''(T) > 0` for both Bose and Fermi gases. Any local or global temperature-eliminated
   equation of state `p(ε)` satisfying `p(ε(T)) = P(T)`, as well as its sound speed squared
   `c_s²(ε) = p'(ε)`, satisfies NO nonzero algebraic differential equation over `ℂ(ε)`.

2. **Massive Parallel-Plate Casimir Energy & Force Dimensional Parity (`d = 2` vs `d = 1, 3`):**
   Under the exact Thermal–Casimir duality `E_C^{(d)}(L, m) = -L B_m^{(d)}(1 / (2L))` and
   Force–Energy-Density duality `F_C^{(d)}(L, m) = -∂_L E_C^{(d)}(L, m) = -ε_m^{(d)}(1 / (2L))`:
   - In even dimension `d = 2`, both `casimirEnergy2D m` and `casimirForce2D m` are D-algebraic
     over `ℂ[L]`.
   - In odd dimensions `d = 1` and `d = 3` (including physical 3D space), both `casimirEnergy_d m`
     and `casimirForce_d m` are D-transcendental over `ℂ(L)`.

3. **Thermal Free Conformal Scalar Dimensional Parity on `S^{d-1} × S¹` (`d = 2, 4` vs `d = 3`):**
   - **Even `d = 2` (`S¹ × S¹`):** The quasi-modular Eisenstein series `E₂` satisfies
     Chazy's 3-monomial autonomous order-3 ODE `2 D³ E₂ - 2 E₂ D² E₂ + 3 (D E₂)² = 0`.
   - **Even `d = 4` (`S³ × S¹`):** The conformal scalar free-energy derivative
     `θ log Z_{S³}(q) = ∑_{n ≥ 1} σ₃(n) qⁿ = (E₄(q) - 1)/240` satisfies an explicit 8-monomial
     autonomous order-3 ODE over `ℤ` (proved unconditionally via Mathlib's `RamanujanFormula.lean`),
     so both `sigmaSeries 3` and the literal sphere partition series `sphereS3PartitionSeries` (`Z_{S³}(q)`)
     are **D-algebraic** over `ℂ(q)`.
   - **Odd `d = 3` (`S² × S¹`):** The literal conformal scalar free-energy derivative
     `sphereS2LogDerivSeries = L₂(x) - 4 L₂(x²)` (with `d_n = 2n + 1`, `E_n = n + 1/2` in the
     half-quantum nome `x = q^{1/2}`) and the literal sphere partition function
     `sphereS2PartitionSeries` (`Z_{S²}(x²) = M(x) / M(x²)²`) are BOTH **unconditionally
     D-transcendental over `ℂ(x)`**, proved via the meromorphic Borel transform
     `K_{S²}(ξ) = K₂(ξ) - K₂(2ξ)` with strictly positive simple-pole residues at `2π²(m+1)` and
     `PakPrimes.GeneralTheorem2.no_autonomous_ade_of_meromorphic_borel`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.ThermalGasEOS

open Complex Real Filter Set MvPolynomial MeasureTheory UpperHalfPlane
open PakPrimes.HigherOrderStokes PakPrimes.PrimeNome PakPrimes.ThermalGasParity
  PakPrimes.DivisorAndMacMahon
open scoped Topology Pointwise Manifold BigOperators

noncomputable section

/-! ### 1. Global Holomorphic Primitives on `{Re z > 0}` & Real-Analyticity of `H₁`, `H₃` -/

/-- Open right half-plane `{z : ℂ | 0 < z.re}`. -/
private def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

private lemma mem_rightHalfPlane {z : ℂ} : z ∈ rightHalfPlane ↔ 0 < z.re := Iff.rfl

private lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma convex_rightHalfPlane : Convex ℝ rightHalfPlane := by
  intro x hx y hy a b ha hb hab
  rw [mem_rightHalfPlane] at hx hy ⊢
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  by_cases ha0 : a = 0
  · subst ha0; have hb1 : b = 1 := by linarith
    subst hb1; simpa using hy
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : 0 < a * x.re := mul_pos ha_pos hx
    have h2 : 0 ≤ b * y.re := mul_nonneg hb (le_of_lt hy)
    linarith

private lemma mem_rightHalfPlane_seg {z : ℂ} (hz : z ∈ rightHalfPlane) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 : ℂ) + (t : ℂ) * (z - 1) ∈ rightHalfPlane := by
  have h1 : (1 : ℂ) ∈ rightHalfPlane := by change 0 < (1 : ℂ).re; norm_num
  have hconv := convex_rightHalfPlane h1 hz (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
  convert hconv using 1
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **Poincaré Lemma on `{Re z > 0}`**: Every function `g : ℂ → ℂ` holomorphic on `{Re z > 0}`
admits a global holomorphic primitive `G(z) = ∫ t in 0..1, (z - 1) * g(1 + t(z - 1))` satisfying
`HasDerivAt G (g z) z` for all `z` with `0 < z.re`. -/
private lemma holomorphic_primitive {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g rightHalfPlane) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G rightHalfPlane ∧
      ∀ z ∈ rightHalfPlane, HasDerivAt G (g z) z := by
  let G : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, (z - 1) * g (1 + (t : ℂ) * (z - 1))
  have hg_cont : ContinuousOn g rightHalfPlane := hg.continuousOn
  have hdg : DifferentiableOn ℂ (deriv g) rightHalfPlane := hg.deriv isOpen_rightHalfPlane
  have hdg_cont : ContinuousOn (deriv g) rightHalfPlane := hdg.continuousOn
  have hderiv : ∀ z₀ ∈ rightHalfPlane, HasDerivAt G (g z₀) z₀ := by
    intro z₀ hz₀
    have hz₀_re : 0 < z₀.re := mem_rightHalfPlane.mp hz₀
    let r : ℝ := z₀.re / 2
    have hr : 0 < r := half_pos hz₀_re
    have hcb_sub : Metric.closedBall z₀ r ⊆ rightHalfPlane := by
      intro z hz
      rw [Metric.mem_closedBall, Complex.dist_eq] at hz
      have hre : |z.re - z₀.re| ≤ r := by
        calc |z.re - z₀.re| = |(z - z₀).re| := by simp
          _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
          _ ≤ r := hz
      have hge := (abs_le.mp hre).1
      rw [mem_rightHalfPlane]
      dsimp only [r] at hge
      linarith [hz₀_re]
    let F : ℂ → ℝ → ℂ := fun z t => (z - 1) * g (1 + (t : ℂ) * (z - 1))
    let F' : ℂ → ℝ → ℂ := fun z t =>
      g (1 + (t : ℂ) * (z - 1)) + (t : ℂ) * (z - 1) * deriv g (1 + (t : ℂ) * (z - 1))
    let K : Set (ℝ × ℂ) := Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z₀ r
    have hK_compact : IsCompact K := isCompact_Icc.prod (isCompact_closedBall z₀ r)
    have hmap_K : MapsTo (fun p : ℝ × ℂ => (1 : ℂ) + (p.1 : ℂ) * (p.2 - 1)) K rightHalfPlane := by
      rintro ⟨t, z⟩ ⟨⟨ht0, ht1⟩, hz⟩
      exact mem_rightHalfPlane_seg (hcb_sub hz) ht0 ht1
    have hF'_cont_K : ContinuousOn (fun p : ℝ × ℂ => F' p.2 p.1) K := by
      have hseg : Continuous (fun p : ℝ × ℂ => (1 : ℂ) + (p.1 : ℂ) * (p.2 - 1)) := by fun_prop
      have h1 : ContinuousOn (fun p : ℝ × ℂ => g (1 + (p.1 : ℂ) * (p.2 - 1))) K :=
        hg_cont.comp hseg.continuousOn hmap_K
      have h2 : ContinuousOn (fun p : ℝ × ℂ => deriv g (1 + (p.1 : ℂ) * (p.2 - 1))) K :=
        hdg_cont.comp hseg.continuousOn hmap_K
      have h3 : ContinuousOn (fun p : ℝ × ℂ => (p.1 : ℂ) * (p.2 - 1)) K := by fun_prop
      exact h1.add (h3.mul h2)
    obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn hF'_cont_K
    have hmem_nhds : Metric.closedBall z₀ r ∈ 𝓝 z₀ := Metric.closedBall_mem_nhds z₀ hr
    have hF_cont : ∀ z ∈ Metric.closedBall z₀ r, ContinuousOn (F z) (Set.Icc 0 1) := by
      intro z hz
      have hseg : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * (z - 1)) := by fun_prop
      have hmap : MapsTo (fun t : ℝ => (1 : ℂ) + (t : ℂ) * (z - 1)) (Set.Icc 0 1) rightHalfPlane :=
        fun t ht => mem_rightHalfPlane_seg (hcb_sub hz) ht.1 ht.2
      exact continuousOn_const.mul (hg_cont.comp hseg.continuousOn hmap)
    have hF'_cont_z₀ : ContinuousOn (F' z₀) (Set.Icc 0 1) := by
      have hseg : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * (z₀ - 1)) := by fun_prop
      have hmap : MapsTo (fun t : ℝ => (1 : ℂ) + (t : ℂ) * (z₀ - 1)) (Set.Icc 0 1) rightHalfPlane :=
        fun t ht => mem_rightHalfPlane_seg hz₀ ht.1 ht.2
      exact (hg_cont.comp hseg.continuousOn hmap).add
        ((by fun_prop : ContinuousOn (fun t : ℝ => (t : ℂ) * (z₀ - 1)) (Set.Icc 0 1)).mul
          (hdg_cont.comp hseg.continuousOn hmap))
    have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (F' := F') (bound := fun _ => M) (a := (0 : ℝ)) (b := (1 : ℝ))
      (s := Metric.closedBall z₀ r) hmem_nhds
      ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · have hftc : ∫ t in (0 : ℝ)..1, F' z₀ t = g z₀ := by
        let h : ℝ → ℂ := fun t => (t : ℂ) * g (1 + (t : ℂ) * (z₀ - 1))
        have hh_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt h (F' z₀ t) t := by
          intro t ht
          rw [Set.uIcc_of_le zero_le_one] at ht
          have hmem : (1 : ℂ) + (t : ℂ) * (z₀ - 1) ∈ rightHalfPlane :=
            mem_rightHalfPlane_seg hz₀ ht.1 ht.2
          have hdg_pt : HasDerivAt g (deriv g (1 + (t : ℂ) * (z₀ - 1))) (1 + (t : ℂ) * (z₀ - 1)) :=
            (hg.differentiableAt (isOpen_rightHalfPlane.mem_nhds hmem)).hasDerivAt
          have hlin : HasDerivAt (fun s : ℝ => (1 : ℂ) + (s : ℂ) * (z₀ - 1)) (z₀ - 1) t := by
            have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
            simpa using (h1.mul_const (z₀ - 1)).const_add (1 : ℂ)
          have hcomp : HasDerivAt (fun s : ℝ => g (1 + (s : ℂ) * (z₀ - 1)))
              (deriv g (1 + (t : ℂ) * (z₀ - 1)) * (z₀ - 1)) t :=
            hdg_pt.comp t hlin
          have hprod := Complex.ofRealCLM.hasDerivAt.mul hcomp
          refine hprod.congr_deriv ?_
          dsimp only [F']; simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; ring
        have hint : IntervalIntegrable (F' z₀) volume 0 1 :=
          hF'_cont_z₀.intervalIntegrable_of_Icc zero_le_one
        have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hh_deriv hint
        simpa [h] using heq
      rw [hftc] at hdom
      exact hdom.2
    · filter_upwards [hmem_nhds] with z hz
      rw [Set.uIoc_of_le zero_le_one]
      exact ((hF_cont z hz).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · exact (hF_cont z₀ (Metric.mem_closedBall_self hr.le)).intervalIntegrable_of_Icc zero_le_one
    · rw [Set.uIoc_of_le zero_le_one]
      exact (hF'_cont_z₀.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · refine Eventually.of_forall fun t ht z hz => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact hM (t, z) ⟨Set.Ioc_subset_Icc_self ht, hz⟩
    · refine Eventually.of_forall fun t ht z hz => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hmem : (1 : ℂ) + (t : ℂ) * (z - 1) ∈ rightHalfPlane :=
        mem_rightHalfPlane_seg (hcb_sub hz) ht.1.le ht.2
      have hdg_pt : HasDerivAt g (deriv g (1 + (t : ℂ) * (z - 1))) (1 + (t : ℂ) * (z - 1)) :=
        (hg.differentiableAt (isOpen_rightHalfPlane.mem_nhds hmem)).hasDerivAt
      have hlin : HasDerivAt (fun w : ℂ => (1 : ℂ) + (t : ℂ) * (w - 1)) (t : ℂ) z := by
        simpa using ((hasDerivAt_id z).sub_const (1 : ℂ)).const_mul (t : ℂ) |>.const_add (1 : ℂ)
      have hcomp := hdg_pt.comp z hlin
      have hprod := ((hasDerivAt_id z).sub_const (1 : ℂ)).mul hcomp
      refine hprod.congr_deriv ?_
      dsimp only [F']; simp only [id_eq, Function.comp_apply]; ring
  exact ⟨G, fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt, hderiv⟩

/-- Real-analyticity lift: if `f : ℝ → ℝ` is differentiable on `(0, ∞)` and its derivative agrees
on `(0, ∞)` with a holomorphic function on `{Re z > 0}`, then `f` extends to a holomorphic
function on `{Re z > 0}` (and in particular is real-analytic on `(0, ∞)`). -/
private lemma holomorphic_ext_of_deriv {f : ℝ → ℝ} {g : ℂ → ℂ}
    (hf : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hg : DifferentiableOn ℂ g rightHalfPlane)
    (hderiv : ∀ y : ℝ, 0 < y → ((deriv f y : ℝ) : ℂ) = g (y : ℂ)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F rightHalfPlane ∧
      ∀ y : ℝ, 0 < y → (f y : ℂ) = F (y : ℂ) := by
  obtain ⟨G, hG_diff, hG_deriv⟩ := holomorphic_primitive hg
  let c : ℂ := (f 1 : ℂ) - G (1 : ℂ)
  refine ⟨fun z => G z + c, hG_diff.add (differentiableOn_const c), fun y hy => ?_⟩
  let h : ℝ → ℂ := fun t => (f t : ℂ) - (G (t : ℂ) + c)
  have hh_deriv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt h 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (f s : ℂ)) ((deriv f t : ℝ) : ℂ) t :=
      (hf t ht).hasDerivAt.ofReal_comp
    have h2 : HasDerivAt (fun s : ℝ => G (s : ℂ) + c) (g (t : ℂ)) t := by
      have hg_t := (hG_deriv (t : ℂ) (mem_rightHalfPlane.mpr (by simpa using ht))).comp_ofReal
      simpa using hg_t.add_const c
    have hsub := h1.sub h2
    rw [hderiv t ht, sub_self] at hsub
    exact hsub
  have hconst : h y = h 1 :=
    convex_Ioi (0 : ℝ) |>.is_const_of_fderivWithin_eq_zero
      (fun t ht => (hh_deriv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [fderivWithin_eq_fderiv (isOpen_Ioi.uniqueDiffWithinAt ht) (hh_deriv t ht).differentiableAt,
          (hh_deriv t ht).hasFDerivAt.fderiv]
        simp)
      hy (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
  have h1 : h 1 = 0 := by simp [h, c]
  rw [h1] at hconst
  exact sub_eq_zero.mp hconst

private lemma analyticOnNhd_of_holomorphic_rightHalfPlane {f : ℝ → ℂ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F rightHalfPlane)
    (heq : ∀ y : ℝ, 0 < y → f y = F (y : ℂ)) :
    AnalyticOnNhd ℝ f (Set.Ioi 0) := by
  intro y hy
  have hFy : AnalyticAt ℂ F (y : ℂ) :=
    hF.analyticAt (isOpen_rightHalfPlane.mem_nhds (mem_rightHalfPlane.mpr (by simpa using hy)))
  have hcomp : AnalyticAt ℝ (fun t : ℝ => F (t : ℂ)) y :=
    hFy.restrictScalars.comp (Complex.ofRealCLM.analyticAt y)
  refine hcomp.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
  exact (heq t ht).symm

/-! #### Elementary Bounds & Derivatives of `gThermal`, `H₁`, `H₃` -/

private lemma gThermal_pos_of_pos {v : ℝ} (hv : 0 < v) : 0 < gThermal v := by
  unfold gThermal
  have hsq : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have he_pos : 0 < Real.exp (-2 * Real.pi * Real.sqrt v) := Real.exp_pos _
  have he_lt : Real.exp (-2 * Real.pi * Real.sqrt v) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hlog : Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  linarith

private lemma hasDerivAt_gThermal_eos {v : ℝ} (hv : 0 < v) :
    HasDerivAt gThermal
      (-Real.pi / Real.sqrt v *
        (Real.exp (-2 * Real.pi * Real.sqrt v) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt v)))) v := by
  unfold gThermal
  have hsq_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt v)) v := Real.hasDerivAt_sqrt hv.ne'
  have hexp_arg : HasDerivAt (fun x : ℝ => -2 * Real.pi * Real.sqrt x)
      (-Real.pi / Real.sqrt v) v := by
    have := hsq.const_mul (-2 * Real.pi)
    refine this.congr_deriv ?_
    field_simp [hsq_pos.ne']
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-2 * Real.pi * Real.sqrt x))
      (Real.exp (-2 * Real.pi * Real.sqrt v) * (-Real.pi / Real.sqrt v)) v := hexp_arg.exp
  have hsub : HasDerivAt (fun x : ℝ => 1 - Real.exp (-2 * Real.pi * Real.sqrt x))
      (-(Real.exp (-2 * Real.pi * Real.sqrt v) * (-Real.pi / Real.sqrt v))) v := hexp.const_sub 1
  have hden : 1 - Real.exp (-2 * Real.pi * Real.sqrt v) ≠ 0 := by
    have : Real.exp (-2 * Real.pi * Real.sqrt v) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    linarith
  have hlog := (hsub.log hden).neg
  refine hlog.congr_deriv ?_
  field_simp [hsq_pos.ne', hden]

private lemma hasDerivAt_deriv_gThermal_eos {v : ℝ} (hv : 0 < v) :
    HasDerivAt (deriv gThermal)
      (Real.pi / (2 * v * Real.sqrt v) *
          (Real.exp (-2 * Real.pi * Real.sqrt v) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt v))) +
        Real.pi ^ 2 / v *
          (Real.exp (-2 * Real.pi * Real.sqrt v) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) ^ 2)) v := by
  have hev : deriv gThermal =ᶠ[𝓝 v] fun x : ℝ =>
      -Real.pi / Real.sqrt x *
        (Real.exp (-2 * Real.pi * Real.sqrt x) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt x))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hv] with x hx
    exact (hasDerivAt_gThermal_eos hx).deriv
  have hsq_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have he_lt : Real.exp (-2 * Real.pi * Real.sqrt v) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hden : 1 - Real.exp (-2 * Real.pi * Real.sqrt v) ≠ 0 := by linarith
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt v)) v := Real.hasDerivAt_sqrt hv.ne'
  have hA : HasDerivAt (fun x : ℝ => -Real.pi / Real.sqrt x)
      (Real.pi / (2 * v * Real.sqrt v)) v := by
    have h1 := (hsq.inv hsq_pos.ne').const_mul (-Real.pi)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [div_eq_mul_inv]) |>.congr_deriv ?_
    have hsq2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
    field_simp [hsq_pos.ne', hv.ne']
    nlinarith [hsq2]
  have hexp_arg : HasDerivAt (fun x : ℝ => -2 * Real.pi * Real.sqrt x) (-Real.pi / Real.sqrt v) v := by
    have := hsq.const_mul (-2 * Real.pi)
    refine this.congr_deriv ?_; field_simp [hsq_pos.ne']
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-2 * Real.pi * Real.sqrt x))
      (Real.exp (-2 * Real.pi * Real.sqrt v) * (-Real.pi / Real.sqrt v)) v := hexp_arg.exp
  have hB : HasDerivAt (fun x : ℝ => Real.exp (-2 * Real.pi * Real.sqrt x) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt x)))
      ((-Real.pi / Real.sqrt v) * Real.exp (-2 * Real.pi * Real.sqrt v) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) ^ 2) v := by
    have hq := hexp.div (hexp.const_sub 1) hden
    refine hq.congr_deriv ?_
    field_simp [hsq_pos.ne', hden]; ring
  have hprod := hA.mul hB
  refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
  have hsq2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  set s : ℝ := Real.sqrt v
  set e : ℝ := Real.exp (-2 * Real.pi * s)
  change Real.pi / (2 * v * s) * (e / (1 - e)) + -Real.pi / s * (-Real.pi / s * e / (1 - e) ^ 2) =
    Real.pi / (2 * v * s) * (e / (1 - e)) + Real.pi ^ 2 / v * (e / (1 - e) ^ 2)
  have hs : s ≠ 0 := hsq_pos.ne'
  have hden' : 1 - e ≠ 0 := hden
  have hv_eq : v = s ^ 2 := hsq2.symm
  rw [hv_eq]
  field_simp [hs, hden']

private lemma integrable_pow_exp_neg_abs_eos {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun p : ℝ => |p| ^ k * Real.exp (-a * |p|)) := by
  have hpos : 0 < a / 2 := half_pos ha
  have hIoi : IntegrableOn (fun p : ℝ => Real.exp (-(a / 2) * p)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hIic : IntegrableOn (fun p : ℝ => Real.exp ((a / 2) * p)) (Set.Iic 0) := by
    have hcomp := (integrableOn_exp_mul_Ioi (a := -(a / 2)) (by linarith) 0).comp_neg
    have hcongr : IntegrableOn (fun p : ℝ => Real.exp ((a / 2) * p)) (Set.Iio 0) := by
      have heq : -Set.Ioi (0 : ℝ) = Set.Iio 0 := by ext x; simp
      rw [heq] at hcomp
      exact hcomp.congr_fun (fun p _ => by simp) measurableSet_Iio
    exact hcongr.congr_set_ae MeasureTheory.Iio_ae_eq_Iic.symm
  have hexp_abs : Integrable (fun p : ℝ => Real.exp (-(a / 2) * |p|)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · exact hIic.congr_fun (fun p hp => by
        rw [abs_of_nonpos (Set.mem_Iic.mp hp)]; ring_nf) measurableSet_Iic
    · exact hIoi.congr_fun (fun p hp => by
        rw [abs_of_pos (Set.mem_Ioi.mp hp)]) measurableSet_Ioi
  have hbound : ∀ p : ℝ, ‖|p| ^ k * Real.exp (-a * |p|)‖ ≤
      ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp (-(a / 2) * |p|) := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpow := Real.pow_div_factorial_le_exp ((a / 2) * |p|) (by positivity) k
    have hmul : |p| ^ k ≤ ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * |p|) := by
      have h1 : (a / 2) ^ k * |p| ^ k / (Nat.factorial k : ℝ) ≤ Real.exp ((a / 2) * |p|) := by
        rwa [mul_pow] at hpow
      have hfac : (0 : ℝ) < Nat.factorial k := Nat.cast_pos.mpr (Nat.factorial_pos k)
      have ha2k : (0 : ℝ) < (a / 2) ^ k := pow_pos hpos k
      rw [div_le_iff₀ hfac] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ ha2k]
      nlinarith
    calc |p| ^ k * Real.exp (-a * |p|)
        ≤ ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * |p|) *
            Real.exp (-a * |p|) := mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
      _ = ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp (-(a / 2) * |p|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  exact (hexp_abs.const_mul _).mono' (by fun_prop) (Eventually.of_forall hbound)

private lemma integrable_gThermal_eos {y : ℝ} (hy : 0 < y) :
    Integrable (fun p : ℝ => gThermal (p ^ 2 + y)) := by
  let C : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹
  have hcont : Continuous (fun p : ℝ => gThermal (p ^ 2 + y)) := by
    unfold gThermal
    refine Continuous.neg (Continuous.log (by fun_prop) fun p => ?_)
    have hsq : 0 < Real.sqrt (p ^ 2 + y) := Real.sqrt_pos.mpr (by positivity)
    have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    linarith
  have hexp := (integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul C
  refine hexp.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  have hv_pos : 0 < p ^ 2 + y := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (gThermal_pos_of_pos hv_pos)]
  have hsqy : Real.sqrt y ≤ Real.sqrt (p ^ 2 + y) := Real.sqrt_le_sqrt (by linarith [sq_nonneg p])
  have hsqp : |p| ≤ Real.sqrt (p ^ 2 + y) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have ht_lt : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hv_pos]
  have hlog_bd : gThermal (p ^ 2 + y) ≤
      Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) := by
    unfold gThermal
    set t := Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))
    have hpos : 0 < (1 - t)⁻¹ := inv_pos.mpr (by linarith)
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_inv] at hlog
    have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp [show 1 - t ≠ 0 by linarith]; ring
    linarith
  have he_le1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤
      Real.exp (-2 * Real.pi * Real.sqrt y) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have he_le2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤
      Real.exp (-(2 * Real.pi) * |p|) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y) := by
    have : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy]
    linarith
  simp only [pow_zero, one_mul]
  calc gThermal (p ^ 2 + y)
      ≤ Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) := hlog_bd
    _ ≤ Real.exp (-(2 * Real.pi) * |p|) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) :=
        div_le_div_of_nonneg_right he_le2 (by linarith)
    _ ≤ Real.exp (-(2 * Real.pi) * |p|) / (1 - Real.exp (-2 * Real.pi * Real.sqrt y)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith)
    _ = C * Real.exp (-(2 * Real.pi) * |p|) := by dsimp only [C]; ring

/-- First derivative of `H₁` on `(0, ∞)`, also yielding strict negativity `H₁'(y) < 0`. -/
private lemma hasDerivAt_H1_eos {y : ℝ} (hy : 0 < y) :
    HasDerivAt H1 ((2 * Real.pi)⁻¹ * ∫ p : ℝ, deriv gThermal (p ^ 2 + y)) y := by
  let y₀ : ℝ := y / 2
  have hy₀ : 0 < y₀ := half_pos hy
  let C : ℝ := (Real.pi / Real.sqrt y₀) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹
  let bound : ℝ → ℝ := fun p => C * Real.exp (-(2 * Real.pi) * |p|)
  have hbound_int : Integrable bound := by
    simpa [bound, pow_zero, one_mul] using
      (integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul C
  have hderiv_int : HasDerivAt (fun t : ℝ => ∫ p : ℝ, gThermal (p ^ 2 + t))
      (∫ p : ℝ, deriv gThermal (p ^ 2 + y)) y := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t p => gThermal (p ^ 2 + t))
      (F' := fun t p => deriv gThermal (p ^ 2 + t))
      (bound := bound) (Metric.ball_mem_nhds y (half_pos hy)) ?_ ?_ ?_ ?_ hbound_int ?_).2
    · filter_upwards [Metric.ball_mem_nhds y (half_pos hy)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      exact (integrable_gThermal_eos (by linarith)).aestronglyMeasurable
    · exact integrable_gThermal_eos hy
    · have hcont : Continuous (fun p : ℝ => deriv gThermal (p ^ 2 + y)) := by
        have heq : (fun p : ℝ => deriv gThermal (p ^ 2 + y)) = fun p : ℝ =>
            -Real.pi / Real.sqrt (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by
          ext p; exact (hasDerivAt_gThermal_eos (by positivity)).deriv
        rw [heq]
        refine Continuous.mul (continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne')
          (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_)
        have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
        linarith
      exact hcont.aestronglyMeasurable
    · filter_upwards with p t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hv_ge : y₀ ≤ p ^ 2 + t := by dsimp only [y₀]; linarith [sq_nonneg p]
      have hv_pos : 0 < p ^ 2 + t := lt_of_lt_of_le hy₀ hv_ge
      rw [(hasDerivAt_gThermal_eos hv_pos).deriv, Real.norm_eq_abs]
      have hsq_ge : Real.sqrt y₀ ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt hv_ge
      have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + t) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have he_le1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-2 * Real.pi * Real.sqrt y₀) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have he_le2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-(2 * Real.pi) * |p|) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt y₀) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy₀]
        linarith
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) := by linarith
      have habs : |-Real.pi / Real.sqrt (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))| =
          Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by
        rw [neg_div, neg_mul, abs_neg, abs_of_nonneg (by positivity)]
      rw [habs]
      have h1 : Real.pi / Real.sqrt (p ^ 2 + t) ≤ Real.pi / Real.sqrt y₀ :=
        div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hy₀) hsq_ge
      have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ≤
          (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
        rw [inv_mul_eq_div]
        exact (div_le_div_of_nonneg_right he_le2 hden.le).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith))
      dsimp only [bound, C]
      calc _ ≤ (Real.pi / Real.sqrt y₀) *
            ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    · filter_upwards with p t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hv_pos : 0 < p ^ 2 + t := by linarith [sq_nonneg p]
      rw [(hasDerivAt_gThermal_eos hv_pos).deriv]
      exact (hasDerivAt_gThermal_eos hv_pos).comp_const_add (p ^ 2) t
  exact hderiv_int.const_mul (2 * Real.pi)⁻¹

/-- Second derivative of `H₁` on `(0, ∞)`, also proving `DifferentiableAt ℝ (deriv H1) y`. -/
private lemma hasDerivAt_deriv_H1_eos {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv H1) ((2 * Real.pi)⁻¹ * ∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + y)) y := by
  let y₀ : ℝ := y / 2
  have hy₀ : 0 < y₀ := half_pos hy
  have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
    have : Real.exp (-2 * Real.pi * Real.sqrt y₀) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy₀]
    linarith
  let C : ℝ := Real.pi / (2 * y₀ * Real.sqrt y₀) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ +
      Real.pi ^ 2 / y₀ * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹
  let bound : ℝ → ℝ := fun p => C * Real.exp (-(2 * Real.pi) * |p|)
  have hbound_int : Integrable bound := by
    simpa [bound, pow_zero, one_mul] using
      (integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul C
  have hderiv_g_int : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ => deriv gThermal (p ^ 2 + t)) := by
    intro t ht
    let Ct : ℝ := (Real.pi / Real.sqrt t) * (1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹
    have hcont : Continuous (fun p : ℝ => deriv gThermal (p ^ 2 + t)) := by
      have heq : (fun p : ℝ => deriv gThermal (p ^ 2 + t)) = fun p : ℝ =>
          -Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by
        ext p; exact (hasDerivAt_gThermal_eos (by positivity)).deriv
      rw [heq]
      refine Continuous.mul (continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne')
        (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_)
      have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + t)]
      linarith
    have hexp := (integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul Ct
    refine hexp.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have hv_pos : 0 < p ^ 2 + t := by positivity
    rw [(hasDerivAt_gThermal_eos hv_pos).deriv, Real.norm_eq_abs, neg_div, neg_mul, abs_neg]
    have hsq_ge : Real.sqrt t ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt (by linarith [sq_nonneg p])
    have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + t) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have hdent : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt t) := by
      have : Real.exp (-2 * Real.pi * Real.sqrt t) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr ht]
      linarith
    have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤ Real.exp (-2 * Real.pi * Real.sqrt t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) := by linarith
    rw [abs_of_nonneg (by positivity)]
    simp only [pow_zero, one_mul]
    have h1 : Real.pi / Real.sqrt (p ^ 2 + t) ≤ Real.pi / Real.sqrt t :=
      div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr ht) hsq_ge
    have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ≤
        (1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
      rw [inv_mul_eq_div]
      exact (div_le_div_of_nonneg_right he2 hden.le).trans
        (div_le_div_of_nonneg_left (Real.exp_pos _).le hdent (by linarith))
    dsimp only [Ct]
    calc _ ≤ (Real.pi / Real.sqrt t) *
          ((1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hderiv_int : HasDerivAt (fun t : ℝ => ∫ p : ℝ, deriv gThermal (p ^ 2 + t))
      (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + y)) y := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t p => deriv gThermal (p ^ 2 + t))
      (F' := fun t p => deriv (deriv gThermal) (p ^ 2 + t))
      (bound := bound) (Metric.ball_mem_nhds y (half_pos hy)) ?_ ?_ ?_ ?_ hbound_int ?_).2
    · filter_upwards [Metric.ball_mem_nhds y (half_pos hy)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      exact (hderiv_g_int t (by linarith)).aestronglyMeasurable
    · exact hderiv_g_int y hy
    · have hcont : Continuous (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) := by
        have heq : (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) = fun p : ℝ =>
            Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) +
            Real.pi ^ 2 / (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2) := by
          ext p; exact (hasDerivAt_deriv_gThermal_eos (by positivity)).deriv
        rw [heq]
        have hden_ne : ∀ p : ℝ, 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≠ 0 := by
          intro p
          have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
            rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
          linarith
        refine Continuous.add
          ((continuous_const.div (by fun_prop) fun p => by positivity).mul
            (Continuous.div (by fun_prop) (by fun_prop) hden_ne))
          ((continuous_const.div (by fun_prop) fun p => by positivity).mul
            (Continuous.div (by fun_prop) (by fun_prop) fun p => pow_ne_zero 2 (hden_ne p)))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hv_ge : y₀ ≤ p ^ 2 + t := by dsimp only [y₀]; linarith [sq_nonneg p]
      have hv_pos : 0 < p ^ 2 + t := lt_of_lt_of_le hy₀ hv_ge
      rw [(hasDerivAt_deriv_gThermal_eos hv_pos).deriv, Real.norm_eq_abs]
      have hsq_ge : Real.sqrt y₀ ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt hv_ge
      have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + t) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤ Real.exp (-2 * Real.pi * Real.sqrt y₀) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) := by linarith
      rw [abs_of_nonneg (by positivity)]
      have ht1 : Real.pi / (2 * (p ^ 2 + t) * Real.sqrt (p ^ 2 + t)) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) ≤
          Real.pi / (2 * y₀ * Real.sqrt y₀) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ *
            Real.exp (-(2 * Real.pi) * |p|) := by
        have ha : Real.pi / (2 * (p ^ 2 + t) * Real.sqrt (p ^ 2 + t)) ≤ Real.pi / (2 * y₀ * Real.sqrt y₀) := by
          refine div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) ?_
          have := mul_le_mul hv_ge hsq_ge (Real.sqrt_nonneg _) hv_pos.le
          linarith
        have hb : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ≤
            (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
          rw [inv_mul_eq_div]
          exact (div_le_div_of_nonneg_right he2 hden.le).trans
            (div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith))
        calc _ ≤ (Real.pi / (2 * y₀ * Real.sqrt y₀)) *
              ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
            mul_le_mul ha hb (by positivity) (by positivity)
          _ = _ := by ring
      have ht2 : Real.pi ^ 2 / (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2) ≤
          Real.pi ^ 2 / y₀ * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹ *
            Real.exp (-(2 * Real.pi) * |p|) := by
        have ha : Real.pi ^ 2 / (p ^ 2 + t) ≤ Real.pi ^ 2 / y₀ :=
          div_le_div_of_nonneg_left (by positivity) hy₀ hv_ge
        have hsq_den : (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2 ≤
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2 :=
          pow_le_pow_left₀ hden0.le (by linarith) 2
        have hb : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2 ≤
            ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
          rw [inv_mul_eq_div]
          exact (div_le_div_of_nonneg_right he2 (by positivity)).trans
            (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hsq_den)
        calc _ ≤ (Real.pi ^ 2 / y₀) *
              (((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
            mul_le_mul ha hb (by positivity) (by positivity)
          _ = _ := by ring
      dsimp only [bound, C]
      linarith
    · filter_upwards with p t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hv_pos : 0 < p ^ 2 + t := by linarith [sq_nonneg p]
      rw [(hasDerivAt_deriv_gThermal_eos hv_pos).deriv]
      exact (hasDerivAt_deriv_gThermal_eos hv_pos).comp_const_add (p ^ 2) t
  have hev : deriv H1 =ᶠ[𝓝 y] fun t : ℝ => (2 * Real.pi)⁻¹ * ∫ p : ℝ, deriv gThermal (p ^ 2 + t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact (hasDerivAt_H1_eos ht).deriv
  exact (hderiv_int.const_mul (2 * Real.pi)⁻¹).congr_of_eventuallyEq hev

/-- The Matsubara mode sum `modeSeries boseModes` is holomorphic on `{Re z > 0}`. -/
private lemma modeSeries_bose_differentiableOn :
    DifferentiableOn ℂ (modeSeries boseModes) rightHalfPlane := by
  intro z₀ hz₀
  have hz₀_re : 0 < z₀.re := mem_rightHalfPlane.mp hz₀
  let r : ℝ := z₀.re / 2
  have hr : 0 < r := half_pos hz₀_re
  have hdiff_ball : DifferentiableOn ℂ (modeSeries boseModes) (Metric.ball z₀ r) := by
    have hsumm : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 : ℝ))) := by
      have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (3 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      refine (hp.comp_injective Nat.succ_injective).congr fun n => ?_
      simp only [Function.comp, Nat.cast_succ]
      rw [Real.rpow_neg (by positivity)]
    have hterm_diff : ∀ n : ℕ, DifferentiableOn ℂ (fun z : ℂ => modeTermL (boseModes.a n) z) (Metric.ball z₀ r) := by
      intro n z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : 0 < z.re := by
        have hre : |z.re - z₀.re| < r := by
          calc |z.re - z₀.re| = |(z - z₀).re| := by simp
            _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
            _ < r := hz
        dsimp only [r] at hre; linarith [(abs_lt.mp hre).1]
      have hslit : z + (boseModes.a n : ℂ) ∈ Complex.slitPlane := by
        left
        have hre : (z + (boseModes.a n : ℂ)).re = z.re + boseModes.a n := by simp
        rw [hre]; dsimp only [boseModes]; positivity
      have h1 : HasDerivAt (fun w : ℂ => (w + (boseModes.a n : ℂ)) ^ (-(3 : ℂ) / 2)) _ z :=
        (hasDerivAt_id z |>.add_const _).cpow_const hslit
      exact h1.differentiableAt.differentiableWithinAt
    refine Complex.differentiableOn_tsum_of_summable_norm hsumm hterm_diff Metric.isOpen_ball ?_
    intro n z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hzre : 0 < z.re := by
      have hre : |z.re - z₀.re| < r := by
        calc |z.re - z₀.re| = |(z - z₀).re| := by simp
          _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
          _ < r := hz
      dsimp only [r] at hre; linarith [(abs_lt.mp hre).1]
    have ha_pos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
    have hre_ge : ((n : ℝ) + 1) ^ 2 ≤ (z + (boseModes.a n : ℂ)).re := by
      have hre : (z + (boseModes.a n : ℂ)).re = z.re + boseModes.a n := by simp
      rw [hre]; dsimp only [boseModes]; linarith
    have hnorm_ge : ((n : ℝ) + 1) ^ 2 ≤ ‖z + (boseModes.a n : ℂ)‖ :=
      hre_ge.trans (Complex.re_le_norm _)
    dsimp only [modeTermL]
    rw [show (-(3 : ℂ) / 2) = ((-(3 : ℝ) / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
    have hle : ‖z + (boseModes.a n : ℂ)‖ ^ (-(3 : ℝ) / 2) ≤
        (((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos ha_pos hnorm_ge (by norm_num)
    refine hle.trans_eq ?_
    rw [← Real.rpow_natCast ((n : ℝ) + 1) 2, ← Real.rpow_mul (by positivity)]
    congr 1; norm_num
  exact (hdiff_ball.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-- Global holomorphic extension of `H₁` to `{Re z > 0}`. -/
private lemma H1_holomorphic_ext :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F rightHalfPlane ∧
      ∀ y : ℝ, 0 < y → (H1 y : ℂ) = F (y : ℂ) := by
  let g₂ : ℂ → ℂ := fun z =>
    (1 / 4 : ℂ) * modeSeries boseModes z - 1 / (4 * z) + 1 / (8 * z ^ ((3 : ℂ) / 2))
  have hg₂_diff : DifferentiableOn ℂ g₂ rightHalfPlane := by
    have h1 : DifferentiableOn ℂ (fun z : ℂ => (1 / 4 : ℂ) * modeSeries boseModes z) rightHalfPlane :=
      modeSeries_bose_differentiableOn.const_mul _
    have h2 : DifferentiableOn ℂ (fun z : ℂ => 1 / (4 * z)) rightHalfPlane := by
      intro z hz
      have hne : z ≠ 0 := by intro h0; rw [h0] at hz; simp [rightHalfPlane] at hz
      exact ((differentiableAt_const _).div ((differentiableAt_id).const_mul 4)
        (mul_ne_zero (by norm_num) hne)).differentiableWithinAt
    have h3 : DifferentiableOn ℂ (fun z : ℂ => 1 / (8 * z ^ ((3 : ℂ) / 2))) rightHalfPlane := by
      intro z hz
      have hslit : z ∈ Complex.slitPlane := Or.inl (mem_rightHalfPlane.mp hz)
      have hne : z ≠ 0 := by intro h0; rw [h0] at hz; simp [rightHalfPlane] at hz
      have hcpow : DifferentiableAt ℂ (fun w : ℂ => w ^ ((3 : ℂ) / 2)) z :=
        ((hasDerivAt_id z).cpow_const hslit).differentiableAt
      have hcpow_ne : z ^ ((3 : ℂ) / 2) ≠ 0 := by
        intro h0; exact hne ((Complex.cpow_eq_zero_iff z ((3 : ℂ) / 2)).mp h0).1
      exact ((differentiableAt_const _).div (hcpow.const_mul 8)
        (mul_ne_zero (by norm_num) hcpow_ne)).differentiableWithinAt
    exact (h1.sub h2).add h3
  have hg₂_eq : ∀ y : ℝ, 0 < y → ((deriv (deriv H1) y : ℝ) : ℂ) = g₂ (y : ℂ) := by
    intro y hy
    have h2 := H1_deriv2 hy
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
    rw [h2]
    dsimp only [g₂, modeSeries, modeTermL, boseModes]
    push_cast
    have hcpow_y : ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ) = (y : ℂ) ^ ((3 : ℂ) / 2) := by
      rw [Complex.ofReal_cpow hy.le]; congr 1; norm_num
    have htsum_eq : (∑' n : ℕ, (((y + ((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ)) =
        ∑' n : ℕ, ((y : ℂ) + ((n : ℂ) + 1) ^ 2) ^ (-(3 : ℂ) / 2) := by
      apply tsum_congr; intro n
      have hpos : 0 ≤ y + ((n : ℝ) + 1) ^ 2 := by positivity
      rw [Complex.ofReal_cpow hpos]
      push_cast; rfl
    rw [hcpow_y, htsum_eq]
  obtain ⟨G₁, hG₁_diff, hG₁_eq⟩ :=
    holomorphic_ext_of_deriv (fun y hy => (hasDerivAt_deriv_H1_eos hy).differentiableAt) hg₂_diff hg₂_eq
  exact holomorphic_ext_of_deriv (fun y hy => (hasDerivAt_H1_eos hy).differentiableAt) hG₁_diff hG₁_eq

/-- Global holomorphic extension of `H₃` to `{Re z > 0}`. -/
private lemma H3_holomorphic_ext :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F rightHalfPlane ∧
      ∀ y : ℝ, 0 < y → (H3 y : ℂ) = F (y : ℂ) := by
  obtain ⟨G₁, hG₁_diff, hG₁_eq⟩ := H1_holomorphic_ext
  refine holomorphic_ext_of_deriv (fun y hy => (H3_deriv hy).differentiableAt)
    (hG₁_diff.const_mul (-(4 * (Real.pi : ℂ))⁻¹)) fun y hy => ?_
  rw [(H3_deriv hy).deriv]
  push_cast
  rw [hG₁_eq y hy]

/-- Real-analyticity of `bosePressure1D m`, `fermiPressure1D m`, `bosePressure3D m`, and
`fermiPressure3D m` on `(0, ∞)`. -/
theorem bosePressure1D_analyticOnNhd {m : ℝ} (hm : 0 < m) :
    AnalyticOnNhd ℝ (fun T : ℝ => (bosePressure1D m T : ℂ)) (Set.Ioi 0) := by
  obtain ⟨F, hF_diff, hF_eq⟩ := H1_holomorphic_ext
  have hH1_an : AnalyticOnNhd ℝ (fun y : ℝ => (H1 y : ℂ)) (Set.Ioi 0) :=
    analyticOnNhd_of_holomorphic_rightHalfPlane hF_diff hF_eq
  intro T hT
  have hT_pos : 0 < T := hT
  have hmap : AnalyticAt ℝ (fun t : ℝ => m ^ 2 / (2 * Real.pi * t) ^ 2) T := by
    refine analyticAt_const.div ((analyticAt_const.mul analyticAt_id).pow 2) ?_
    positivity
  have hpos : 0 < m ^ 2 / (2 * Real.pi * T) ^ 2 := by positivity
  have hcomp : AnalyticAt ℝ (fun t : ℝ => (H1 (m ^ 2 / (2 * Real.pi * t) ^ 2) : ℂ)) T :=
    AnalyticAt.comp (g := fun y : ℝ => (H1 y : ℂ)) (f := fun t : ℝ => m ^ 2 / (2 * Real.pi * t) ^ 2)
      (hH1_an _ hpos) hmap
  have hrhs : AnalyticAt ℝ (fun t : ℝ =>
      (2 * (Real.pi : ℂ)) * (t : ℂ) ^ 2 * (H1 (m ^ 2 / (2 * Real.pi * t) ^ 2) : ℂ)) T :=
    (analyticAt_const.mul ((Complex.ofRealCLM.analyticAt T).pow 2)).mul hcomp
  refine hrhs.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
  rw [bosePressure1D_eq_H1 ht]; push_cast; ring

theorem fermiPressure1D_analyticOnNhd {m : ℝ} (hm : 0 < m) :
    AnalyticOnNhd ℝ (fun T : ℝ => (fermiPressure1D m T : ℂ)) (Set.Ioi 0) := by
  intro T hT
  have h1 := bosePressure1D_analyticOnNhd hm T hT
  have h2 := bosePressure1D_analyticOnNhd (by positivity : 0 < 2 * m) T hT
  have hsub : AnalyticAt ℝ (fun t : ℝ => (bosePressure1D m t : ℂ) - (1 / 2 : ℂ) * (bosePressure1D (2 * m) t : ℂ)) T :=
    h1.sub (analyticAt_const.mul h2)
  refine hsub.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
  rw [fermiPressure1D_doubling hm ht]; push_cast; ring

theorem bosePressure3D_analyticOnNhd {m : ℝ} (hm : 0 < m) :
    AnalyticOnNhd ℝ (fun T : ℝ => (bosePressure3D m T : ℂ)) (Set.Ioi 0) := by
  obtain ⟨F, hF_diff, hF_eq⟩ := H3_holomorphic_ext
  have hH3_an : AnalyticOnNhd ℝ (fun y : ℝ => (H3 y : ℂ)) (Set.Ioi 0) :=
    analyticOnNhd_of_holomorphic_rightHalfPlane hF_diff hF_eq
  intro T hT
  have hT_pos : 0 < T := hT
  have hmap : AnalyticAt ℝ (fun t : ℝ => m ^ 2 / (2 * Real.pi * t) ^ 2) T := by
    refine analyticAt_const.div ((analyticAt_const.mul analyticAt_id).pow 2) ?_
    positivity
  have hpos : 0 < m ^ 2 / (2 * Real.pi * T) ^ 2 := by positivity
  have hcomp : AnalyticAt ℝ (fun t : ℝ => (H3 (m ^ 2 / (2 * Real.pi * t) ^ 2) : ℂ)) T :=
    AnalyticAt.comp (g := fun y : ℝ => (H3 y : ℂ)) (f := fun t : ℝ => m ^ 2 / (2 * Real.pi * t) ^ 2)
      (hH3_an _ hpos) hmap
  have hrhs : AnalyticAt ℝ (fun t : ℝ =>
      (8 * (Real.pi : ℂ) ^ 3) * (t : ℂ) ^ 4 * (H3 (m ^ 2 / (2 * Real.pi * t) ^ 2) : ℂ)) T :=
    (analyticAt_const.mul ((Complex.ofRealCLM.analyticAt T).pow 4)).mul hcomp
  refine hrhs.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
  rw [bosePressure3D_eq_H3 ht]; push_cast; ring

theorem fermiPressure3D_analyticOnNhd {m : ℝ} (hm : 0 < m) :
    AnalyticOnNhd ℝ (fun T : ℝ => (fermiPressure3D m T : ℂ)) (Set.Ioi 0) := by
  intro T hT
  have h1 := bosePressure3D_analyticOnNhd hm T hT
  have h2 := bosePressure3D_analyticOnNhd (by positivity : 0 < 2 * m) T hT
  have hsub : AnalyticAt ℝ (fun t : ℝ => (bosePressure3D m t : ℂ) - (1 / 8 : ℂ) * (bosePressure3D (2 * m) t : ℂ)) T :=
    h1.sub (analyticAt_const.mul h2)
  refine hsub.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
  rw [fermiPressure3D_doubling hm ht]; push_cast; ring

/-! #### Strict Thermodynamic Positivity: `P > 0`, `P' > 0`, `ε > 0`, `ε' = T P'' > 0` -/

/-- Thermodynamic energy density `ε(T) = T P'(T) - P(T)` at zero chemical potential. -/
@[expose] def energyDensity (P : ℝ → ℝ) (T : ℝ) : ℝ :=
  T * deriv P T - P T

/-- Equilibrium sound speed squared `c_s²(ε) = dP/dε` along the zero-chemical-potential family. -/
@[expose] def soundSpeedSq (p : ℝ → ℝ) (ε : ℝ) : ℝ :=
  deriv p ε

private lemma H1_pos {y : ℝ} (hy : 0 < y) : 0 < H1 y := by
  unfold H1
  refine mul_pos (by positivity) ?_
  exact MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (x := (0 : ℝ))
    (by
      unfold gThermal
      refine Continuous.neg (Continuous.log (by fun_prop) fun p => ?_)
      have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
      linarith)
    (integrable_gThermal_eos hy)
    (fun p => (gThermal_pos_of_pos (by positivity)).le)
    (gThermal_pos_of_pos (by positivity)).ne'

private lemma deriv_H1_neg {y : ℝ} (hy : 0 < y) : deriv H1 y < 0 := by
  rw [(hasDerivAt_H1_eos hy).deriv]
  have hneg : ∫ p : ℝ, -deriv gThermal (p ^ 2 + y) > 0 := by
    have hcont : Continuous (fun p : ℝ => -deriv gThermal (p ^ 2 + y)) := by
      have heq : (fun p : ℝ => -deriv gThermal (p ^ 2 + y)) = fun p : ℝ =>
          Real.pi / Real.sqrt (p ^ 2 + y) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by
        ext p; rw [(hasDerivAt_gThermal_eos (by positivity)).deriv]; ring
      rw [heq]
      refine Continuous.mul (continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne')
        (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_)
      have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
      linarith
    have hint : Integrable (fun p : ℝ => -deriv gThermal (p ^ 2 + y)) := by
      let Ct : ℝ := (Real.pi / Real.sqrt y) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹
      have hexp := (integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul Ct
      refine hexp.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      have hv_pos : 0 < p ^ 2 + y := by positivity
      rw [(hasDerivAt_gThermal_eos hv_pos).deriv, Real.norm_eq_abs, neg_div, neg_mul, neg_neg]
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hv_pos]
        linarith
      have hdeny : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy]
        linarith
      rw [abs_of_nonneg (by positivity)]
      simp only [pow_zero, one_mul]
      have hsq_ge : Real.sqrt y ≤ Real.sqrt (p ^ 2 + y) := Real.sqrt_le_sqrt (by linarith [sq_nonneg p])
      have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + y) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-2 * Real.pi * Real.sqrt y) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have h1 : Real.pi / Real.sqrt (p ^ 2 + y) ≤ Real.pi / Real.sqrt y :=
        div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hy) hsq_ge
      have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ≤
          (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
        rw [inv_mul_eq_div]
        exact (div_le_div_of_nonneg_right he2 hden.le).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hdeny (by linarith))
      dsimp only [Ct]
      calc _ ≤ (Real.pi / Real.sqrt y) *
            ((1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    refine MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (x := (0 : ℝ)) hcont hint (fun p => ?_) ?_
    · rw [(hasDerivAt_gThermal_eos (by positivity)).deriv, neg_div, neg_mul, neg_neg]
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
        linarith
      positivity
    · rw [(hasDerivAt_gThermal_eos (by positivity)).deriv, neg_div, neg_mul, neg_neg]
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (0 ^ 2 + y)) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt (0 ^ 2 + y)) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < 0 ^ 2 + y)]
        linarith
      positivity
  rw [MeasureTheory.integral_neg] at hneg
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  nlinarith

private lemma deriv2_H1_pos {y : ℝ} (hy : 0 < y) : 0 < deriv (deriv H1) y := by
  rw [(hasDerivAt_deriv_H1_eos hy).deriv]
  refine mul_pos (by positivity) ?_
  have hcont : Continuous (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) := by
    have heq : (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) = fun p : ℝ =>
        Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) +
        Real.pi ^ 2 / (p ^ 2 + y) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2) := by
      ext p; exact (hasDerivAt_deriv_gThermal_eos (by positivity)).deriv
    rw [heq]
    have hden_ne : ∀ p : ℝ, 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≠ 0 := by
      intro p
      have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
      linarith
    refine Continuous.add
      ((continuous_const.div (by fun_prop) fun p => by positivity).mul
        (Continuous.div (by fun_prop) (by fun_prop) hden_ne))
      ((continuous_const.div (by fun_prop) fun p => by positivity).mul
        (Continuous.div (by fun_prop) (by fun_prop) fun p => pow_ne_zero 2 (hden_ne p)))
  have hpos_pt : ∀ p : ℝ, 0 < deriv (deriv gThermal) (p ^ 2 + y) := by
    intro p
    rw [(hasDerivAt_deriv_gThermal_eos (by positivity)).deriv]
    have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) := by
      have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
      linarith
    positivity
  have hdeny : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y) := by
    have : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy]
    linarith
  let Cy : ℝ := Real.pi / (2 * y * Real.sqrt y) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ +
      Real.pi ^ 2 / y * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹
  have hint : Integrable (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) := by
    refine ((integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul Cy).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have hv_ge : y ≤ p ^ 2 + y := by linarith [sq_nonneg p]
    have hv_pos : 0 < p ^ 2 + y := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (hpos_pt p), (hasDerivAt_deriv_gThermal_eos hv_pos).deriv]
    have hsq_ge : Real.sqrt y ≤ Real.sqrt (p ^ 2 + y) := Real.sqrt_le_sqrt hv_ge
    have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + y) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-2 * Real.pi * Real.sqrt y) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) := by linarith
    simp only [pow_zero, one_mul]
    have ht1 : Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) ≤
        Real.pi / (2 * y * Real.sqrt y) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ *
          Real.exp (-(2 * Real.pi) * |p|) := by
      have ha : Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) ≤ Real.pi / (2 * y * Real.sqrt y) := by
        refine div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) ?_
        have := mul_le_mul hv_ge hsq_ge (Real.sqrt_nonneg _) hv_pos.le
        linarith
      have hb : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ≤
          (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
        rw [inv_mul_eq_div]
        exact (div_le_div_of_nonneg_right he2 hden.le).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hdeny (by linarith))
      calc _ ≤ (Real.pi / (2 * y * Real.sqrt y)) *
            ((1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
          mul_le_mul ha hb (by positivity) (by positivity)
        _ = _ := by ring
    have ht2 : Real.pi ^ 2 / (p ^ 2 + y) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2) ≤
        Real.pi ^ 2 / y * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹ *
          Real.exp (-(2 * Real.pi) * |p|) := by
      have ha : Real.pi ^ 2 / (p ^ 2 + y) ≤ Real.pi ^ 2 / y :=
        div_le_div_of_nonneg_left (by positivity) hy hv_ge
      have hsq_den : (1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2 ≤
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2 :=
        pow_le_pow_left₀ hdeny.le (by linarith) 2
      have hb : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2 ≤
          ((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
        rw [inv_mul_eq_div]
        exact (div_le_div_of_nonneg_right he2 (by positivity)).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hsq_den)
      calc _ ≤ (Real.pi ^ 2 / y) *
            (((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
          mul_le_mul ha hb (by positivity) (by positivity)
        _ = _ := by ring
    dsimp only [Cy]; linarith
  exact MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (x := (0 : ℝ)) hcont hint
    (fun p => (hpos_pt p).le) (hpos_pt 0).ne'

private lemma H3_pos {y : ℝ} (hy : 0 < y) : 0 < H3 y := by
  unfold H3
  refine mul_pos (by positivity) ?_
  have hcont : ContinuousOn (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + y)) (Set.Ioi 0) := by
    refine (continuous_pow 2).continuousOn.mul ?_
    unfold gThermal
    refine (Continuous.neg (Continuous.log (by fun_prop) fun p => ?_)).continuousOn
    have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
    linarith
  have hint : IntegrableOn (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + y)) (Set.Ioi 0) := by
    let C : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹
    have hexp : IntegrableOn (fun p : ℝ => C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|))) (Set.Ioi 0) :=
      ((integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 2).const_mul C).integrableOn
    refine hexp.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) (Eventually.of_forall fun p => ?_)
    have hv_pos : 0 < p ^ 2 + y := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg p) (gThermal_pos_of_pos hv_pos).le)]
    have hsqy : Real.sqrt y ≤ Real.sqrt (p ^ 2 + y) := Real.sqrt_le_sqrt (by linarith [sq_nonneg p])
    have hsqp : |p| ≤ Real.sqrt (p ^ 2 + y) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have ht_lt : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hv_pos]
    have hlog_bd : gThermal (p ^ 2 + y) ≤
        Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) := by
      unfold gThermal
      set t := Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))
      have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith : 0 < 1 - t))
      rw [Real.log_inv] at hlog
      have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp [show 1 - t ≠ 0 by linarith]; ring
      linarith
    have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-2 * Real.pi * Real.sqrt y) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y) := by
      have : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy]
      linarith
    have hg_le : gThermal (p ^ 2 + y) ≤ C * Real.exp (-(2 * Real.pi) * |p|) := by
      calc _ ≤ Real.exp (-(2 * Real.pi) * |p|) / (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) :=
            hlog_bd.trans (div_le_div_of_nonneg_right he2 (by linarith))
        _ ≤ Real.exp (-(2 * Real.pi) * |p|) / (1 - Real.exp (-2 * Real.pi * Real.sqrt y)) :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith)
        _ = C * Real.exp (-(2 * Real.pi) * |p|) := by dsimp only [C]; ring
    calc p ^ 2 * gThermal (p ^ 2 + y)
        ≤ p ^ 2 * (C * Real.exp (-(2 * Real.pi) * |p|)) := mul_le_mul_of_nonneg_left hg_le (sq_nonneg p)
      _ = C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|)) := by rw [sq_abs]; ring
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun p => mul_nonneg (sq_nonneg p) (gThermal_pos_of_pos (by positivity)).le) hint]
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + y)) ∩ Set.Ioi 0 := by
    intro p hp
    refine ⟨?_, hp⟩
    rw [Function.mem_support]
    exact (mul_pos (pow_pos hp 2) (gThermal_pos_of_pos (by positivity))).ne'
  exact lt_of_lt_of_le (by simp) (MeasureTheory.measure_mono hsub)

/-- Strict thermodynamic monotonicity in 1D Bose gas: for `m > 0`, `T > 0`,
`P'(T) > 0`, `ε(T) > 0`, and `ε'(T) = T P''(T) > 0`. -/
theorem bosePressure1D_thermodynamic_pos {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    0 < deriv (bosePressure1D m) T ∧
    0 < energyDensity (bosePressure1D m) T ∧
    0 < deriv (energyDensity (bosePressure1D m)) T := by
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  have heq : ∀ t : ℝ, 0 < t → bosePressure1D m t = 2 * Real.pi * t ^ 2 * H1 (c ^ 2 / t ^ 2) := by
    intro t ht; rw [bosePressure1D_eq_H1 ht]; dsimp only [c]; congr 2; field_simp
  have hd_y : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => c ^ 2 / s ^ 2) (-2 * c ^ 2 / t ^ 3) t := by
    intro t ht
    have h1 := ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht.ne')).const_mul (c ^ 2)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [div_eq_mul_inv]) |>.congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd1 : ∀ t : ℝ, 0 < t →
      HasDerivAt (bosePressure1D m)
        (4 * Real.pi * t * (H1 (c ^ 2 / t ^ 2) - (c ^ 2 / t ^ 2) * deriv H1 (c ^ 2 / t ^ 2))) t := by
    intro t ht
    have hy : 0 < c ^ 2 / t ^ 2 := by positivity
    have hH : HasDerivAt (fun s : ℝ => H1 (c ^ 2 / s ^ 2))
        (deriv H1 (c ^ 2 / t ^ 2) * (-2 * c ^ 2 / t ^ 3)) t :=
      HasDerivAt.comp (h₂ := H1) (h := fun s : ℝ => c ^ 2 / s ^ 2) t
        (hasDerivAt_H1_eos hy).differentiableAt.hasDerivAt (hd_y t ht)
    have hp := ((hasDerivAt_pow 2 t).const_mul (2 * Real.pi)).mul hH
    have hev : bosePressure1D m =ᶠ[𝓝 t] fun s => 2 * Real.pi * s ^ 2 * H1 (c ^ 2 / s ^ 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs; exact heq s hs
    refine (hp.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd2 : HasDerivAt (deriv (bosePressure1D m))
      (4 * Real.pi * (H1 (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1 (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1) (c ^ 2 / T ^ 2))) T := by
    have hy : 0 < c ^ 2 / T ^ 2 := by positivity
    have hH1 : HasDerivAt (fun s : ℝ => H1 (c ^ 2 / s ^ 2))
        (deriv H1 (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := H1) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (hasDerivAt_H1_eos hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hH1' : HasDerivAt (fun s : ℝ => deriv H1 (c ^ 2 / s ^ 2))
        (deriv (deriv H1) (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := deriv H1) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (hasDerivAt_deriv_H1_eos hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hbr := hH1.sub ((hd_y T hT).mul hH1')
    have hprod := ((hasDerivAt_id T).const_mul (4 * Real.pi)).mul hbr
    have hev : deriv (bosePressure1D m) =ᶠ[𝓝 T] fun s =>
        4 * Real.pi * s * (H1 (c ^ 2 / s ^ 2) - (c ^ 2 / s ^ 2) * deriv H1 (c ^ 2 / s ^ 2)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with s hs; exact (hd1 s hs).deriv
    refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]; field_simp [hT.ne']; ring
  have hyT : 0 < c ^ 2 / T ^ 2 := by positivity
  have hH_pos := H1_pos hyT
  have hH1_neg := deriv_H1_neg hyT
  have hH2_pos := deriv2_H1_pos hyT
  have hP1 : 0 < deriv (bosePressure1D m) T := by
    rw [(hd1 T hT).deriv]
    have : 0 < H1 (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1 (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE : 0 < energyDensity (bosePressure1D m) T := by
    unfold energyDensity
    rw [(hd1 T hT).deriv, heq T hT]
    have : T * (4 * Real.pi * T * (H1 (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1 (c ^ 2 / T ^ 2))) -
        2 * Real.pi * T ^ 2 * H1 (c ^ 2 / T ^ 2) =
        2 * Real.pi * T ^ 2 * (H1 (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H1 (c ^ 2 / T ^ 2)) := by ring
    rw [this]
    have : 0 < H1 (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H1 (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE' : 0 < deriv (energyDensity (bosePressure1D m)) T := by
    have hdE : HasDerivAt (energyDensity (bosePressure1D m))
        (T * (4 * Real.pi * (H1 (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1 (c ^ 2 / T ^ 2) +
          2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1) (c ^ 2 / T ^ 2)))) T := by
      have h1 := ((hasDerivAt_id T).mul hd2).sub (hd1 T hT)
      refine h1.congr_deriv ?_
      rw [(hd1 T hT).deriv]; simp only [id_eq]; ring
    rw [hdE.deriv]
    have hsqy : 0 < (c ^ 2 / T ^ 2) ^ 2 := by positivity
    have hterm2 : 0 < 2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1) (c ^ 2 / T ^ 2) := by positivity
    have : 0 < H1 (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1 (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1) (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  exact ⟨hP1, hE, hE'⟩

/-- Strict thermodynamic monotonicity in 3D Bose gas: for `m > 0`, `T > 0`,
`P'(T) > 0`, `ε(T) > 0`, and `ε'(T) = T P''(T) > 0`. -/
theorem bosePressure3D_thermodynamic_pos {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    0 < deriv (bosePressure3D m) T ∧
    0 < energyDensity (bosePressure3D m) T ∧
    0 < deriv (energyDensity (bosePressure3D m)) T := by
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  have heq : ∀ t : ℝ, 0 < t → bosePressure3D m t = 8 * Real.pi ^ 3 * t ^ 4 * H3 (c ^ 2 / t ^ 2) := by
    intro t ht; rw [bosePressure3D_eq_H3 ht]; dsimp only [c]; congr 2; field_simp
  have hd_y : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => c ^ 2 / s ^ 2) (-2 * c ^ 2 / t ^ 3) t := by
    intro t ht
    have h1 := ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht.ne')).const_mul (c ^ 2)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [div_eq_mul_inv]) |>.congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd_H3' : ∀ y : ℝ, 0 < y → HasDerivAt (deriv H3) (-(4 * Real.pi)⁻¹ * deriv H1 y) y := by
    intro y hy
    have hev : deriv H3 =ᶠ[𝓝 y] fun s => -(4 * Real.pi)⁻¹ * H1 s := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with s hs; exact (H3_deriv hs).deriv
    exact ((hasDerivAt_H1_eos hy).differentiableAt.hasDerivAt.const_mul (-(4 * Real.pi)⁻¹)).congr_of_eventuallyEq hev
  have hd1 : ∀ t : ℝ, 0 < t →
      HasDerivAt (bosePressure3D m)
        (16 * Real.pi ^ 3 * t ^ 3 * (2 * H3 (c ^ 2 / t ^ 2) - (c ^ 2 / t ^ 2) * deriv H3 (c ^ 2 / t ^ 2))) t := by
    intro t ht
    have hy : 0 < c ^ 2 / t ^ 2 := by positivity
    have hH : HasDerivAt (fun s : ℝ => H3 (c ^ 2 / s ^ 2))
        (deriv H3 (c ^ 2 / t ^ 2) * (-2 * c ^ 2 / t ^ 3)) t :=
      HasDerivAt.comp (h₂ := H3) (h := fun s : ℝ => c ^ 2 / s ^ 2) t
        (H3_deriv hy).differentiableAt.hasDerivAt (hd_y t ht)
    have hp := ((hasDerivAt_pow 4 t).const_mul (8 * Real.pi ^ 3)).mul hH
    have hev : bosePressure3D m =ᶠ[𝓝 t] fun s => 8 * Real.pi ^ 3 * s ^ 4 * H3 (c ^ 2 / s ^ 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs; exact heq s hs
    refine (hp.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd2 : HasDerivAt (deriv (bosePressure3D m))
      (16 * Real.pi ^ 3 * T ^ 2 * (6 * H3 (c ^ 2 / T ^ 2) - 5 * (c ^ 2 / T ^ 2) * deriv H3 (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3) (c ^ 2 / T ^ 2))) T := by
    have hy : 0 < c ^ 2 / T ^ 2 := by positivity
    have hH3 : HasDerivAt (fun s : ℝ => H3 (c ^ 2 / s ^ 2))
        (deriv H3 (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := H3) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (H3_deriv hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hH3' : HasDerivAt (fun s : ℝ => deriv H3 (c ^ 2 / s ^ 2))
        (deriv (deriv H3) (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := deriv H3) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (hd_H3' (c ^ 2 / T ^ 2) hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hbr := (hH3.const_mul 2).sub ((hd_y T hT).mul hH3')
    have hprod := ((hasDerivAt_pow 3 T).const_mul (16 * Real.pi ^ 3)).mul hbr
    have hev : deriv (bosePressure3D m) =ᶠ[𝓝 T] fun s =>
        16 * Real.pi ^ 3 * s ^ 3 * (2 * H3 (c ^ 2 / s ^ 2) - (c ^ 2 / s ^ 2) * deriv H3 (c ^ 2 / s ^ 2)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with s hs; exact (hd1 s hs).deriv
    refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply]; field_simp [hT.ne']; ring
  have hyT : 0 < c ^ 2 / T ^ 2 := by positivity
  have hH3_p := H3_pos hyT
  have hH3'_n : deriv H3 (c ^ 2 / T ^ 2) < 0 := by
    rw [(H3_deriv hyT).deriv]
    have := H1_pos hyT
    have hpi : 0 < (4 * Real.pi)⁻¹ := by positivity
    nlinarith
  have hH3''_p : 0 < deriv (deriv H3) (c ^ 2 / T ^ 2) := by
    rw [(hd_H3' (c ^ 2 / T ^ 2) hyT).deriv]
    have := deriv_H1_neg hyT
    have hpi : 0 < (4 * Real.pi)⁻¹ := by positivity
    nlinarith
  have hP1 : 0 < deriv (bosePressure3D m) T := by
    rw [(hd1 T hT).deriv]
    have : 0 < 2 * H3 (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H3 (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE : 0 < energyDensity (bosePressure3D m) T := by
    unfold energyDensity
    rw [(hd1 T hT).deriv, heq T hT]
    have : T * (16 * Real.pi ^ 3 * T ^ 3 * (2 * H3 (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H3 (c ^ 2 / T ^ 2))) -
        8 * Real.pi ^ 3 * T ^ 4 * H3 (c ^ 2 / T ^ 2) =
        8 * Real.pi ^ 3 * T ^ 4 * (3 * H3 (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H3 (c ^ 2 / T ^ 2)) := by ring
    rw [this]
    have : 0 < 3 * H3 (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H3 (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE' : 0 < deriv (energyDensity (bosePressure3D m)) T := by
    have hdE : HasDerivAt (energyDensity (bosePressure3D m))
        (T * (16 * Real.pi ^ 3 * T ^ 2 * (6 * H3 (c ^ 2 / T ^ 2) - 5 * (c ^ 2 / T ^ 2) * deriv H3 (c ^ 2 / T ^ 2) +
          2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3) (c ^ 2 / T ^ 2)))) T := by
      have h1 := ((hasDerivAt_id T).mul hd2).sub (hd1 T hT)
      refine h1.congr_deriv ?_
      rw [(hd1 T hT).deriv]; simp only [id_eq]; ring
    rw [hdE.deriv]
    have hsqy : 0 < (c ^ 2 / T ^ 2) ^ 2 := by positivity
    have hterm2 : 0 < 2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3) (c ^ 2 / T ^ 2) := by positivity
    have : 0 < 6 * H3 (c ^ 2 / T ^ 2) - 5 * (c ^ 2 / T ^ 2) * deriv H3 (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3) (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  exact ⟨hP1, hE, hE'⟩

/-! #### Strict Thermodynamic Positivity for Relativistic Fermi Gases (1D & 3D) -/

private def H1Fermi (y : ℝ) : ℝ := H1 y - (1 / 2 : ℝ) * H1 (4 * y)

private def H3Fermi (y : ℝ) : ℝ := H3 y - (1 / 8 : ℝ) * H3 (4 * y)

private lemma sqrt_four_mul {v : ℝ} : Real.sqrt (4 * v) = 2 * Real.sqrt v := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

private lemma gThermal_fermi_diff {v : ℝ} (hv : 0 < v) :
    gThermal v - gThermal (4 * v) = Real.log (1 + Real.exp (-2 * Real.pi * Real.sqrt v)) := by
  unfold gThermal
  have hsq : Real.sqrt (4 * v) = 2 * Real.sqrt v := sqrt_four_mul
  set e : ℝ := Real.exp (-2 * Real.pi * Real.sqrt v)
  have he_pos : 0 < e := Real.exp_pos _
  have he_lt : e < 1 := by
    dsimp only [e]; rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hv]
  have he2 : Real.exp (-2 * Real.pi * Real.sqrt (4 * v)) = e ^ 2 := by
    rw [hsq, sq, ← Real.exp_add]; congr 1; ring
  rw [he2]
  have hfac : 1 - e ^ 2 = (1 - e) * (1 + e) := by ring
  rw [hfac, Real.log_mul (by linarith) (by linarith)]
  ring

private lemma deriv_gThermal_fermi_diff {v : ℝ} (hv : 0 < v) :
    4 * deriv gThermal (4 * v) - deriv gThermal v =
      Real.pi / Real.sqrt v *
        (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 + Real.exp (-2 * Real.pi * Real.sqrt v))) := by
  rw [(hasDerivAt_gThermal_eos (by positivity : 0 < 4 * v)).deriv,
    (hasDerivAt_gThermal_eos hv).deriv]
  have hsq : Real.sqrt (4 * v) = 2 * Real.sqrt v := sqrt_four_mul
  set s : ℝ := Real.sqrt v
  set e : ℝ := Real.exp (-2 * Real.pi * s)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have he_pos : 0 < e := Real.exp_pos _
  have he_lt : e < 1 := by
    dsimp only [e]; rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hv]
  have he2 : Real.exp (-2 * Real.pi * (2 * s)) = e ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hsq, he2]
  have h1 : 1 - e ≠ 0 := by linarith
  have h2 : 1 + e ≠ 0 := by linarith
  have h3 : 1 - e ^ 2 ≠ 0 := by nlinarith
  field_simp [hs, h1, h2, h3]
  ring

private lemma deriv2_gThermal_fermi_diff {v : ℝ} (hv : 0 < v) :
    deriv (deriv gThermal) v - 16 * deriv (deriv gThermal) (4 * v) =
      Real.pi / (2 * v * Real.sqrt v) *
        (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 + Real.exp (-2 * Real.pi * Real.sqrt v))) +
      Real.pi ^ 2 / v *
        (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 + Real.exp (-2 * Real.pi * Real.sqrt v)) ^ 2) := by
  rw [(hasDerivAt_deriv_gThermal_eos hv).deriv,
    (hasDerivAt_deriv_gThermal_eos (by positivity : 0 < 4 * v)).deriv]
  have hsq : Real.sqrt (4 * v) = 2 * Real.sqrt v := sqrt_four_mul
  set s : ℝ := Real.sqrt v
  set e : ℝ := Real.exp (-2 * Real.pi * s)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hvne : v ≠ 0 := hv.ne'
  have he_pos : 0 < e := Real.exp_pos _
  have he_lt : e < 1 := by
    dsimp only [e]; rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hv]
  have he2 : Real.exp (-2 * Real.pi * (2 * s)) = e ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hsq, he2]
  have h1 : 1 - e ≠ 0 := by linarith
  have h2 : 1 + e ≠ 0 := by linarith
  have h3 : 1 - e ^ 2 ≠ 0 := by nlinarith
  field_simp [hs, hvne, h1, h2, h3]
  ring

private lemma hasDerivAt_H1Fermi {y : ℝ} (hy : 0 < y) :
    HasDerivAt H1Fermi (deriv H1 y - 2 * deriv H1 (4 * y)) y := by
  have h1 : HasDerivAt H1 (deriv H1 y) y := (hasDerivAt_H1_eos hy).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => H1 (4 * s)) (deriv H1 (4 * y) * 4) y := by
    have hmul : HasDerivAt (fun s : ℝ => 4 * s) 4 y := by simpa using (hasDerivAt_id y).const_mul (4 : ℝ)
    exact HasDerivAt.comp (h₂ := H1) (h := fun s : ℝ => 4 * s) y
      (hasDerivAt_H1_eos (by positivity : 0 < 4 * y)).differentiableAt.hasDerivAt hmul
  have hsub := h1.sub (h2.const_mul (1 / 2 : ℝ))
  refine hsub.congr_deriv ?_
  ring

private lemma hasDerivAt_deriv_H1Fermi {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv H1Fermi) (deriv (deriv H1) y - 8 * deriv (deriv H1) (4 * y)) y := by
  have hev : deriv H1Fermi =ᶠ[𝓝 y] fun s : ℝ => deriv H1 s - 2 * deriv H1 (4 * s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with s hs
    exact (hasDerivAt_H1Fermi hs).deriv
  have h1 : HasDerivAt (deriv H1) (deriv (deriv H1) y) y :=
    (hasDerivAt_deriv_H1_eos hy).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => deriv H1 (4 * s)) (deriv (deriv H1) (4 * y) * 4) y := by
    have hmul : HasDerivAt (fun s : ℝ => 4 * s) 4 y := by simpa using (hasDerivAt_id y).const_mul (4 : ℝ)
    exact HasDerivAt.comp (h₂ := deriv H1) (h := fun s : ℝ => 4 * s) y
      (hasDerivAt_deriv_H1_eos (by positivity : 0 < 4 * y)).differentiableAt.hasDerivAt hmul
  have hsub := h1.sub (h2.const_mul (2 : ℝ))
  refine (hsub.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

private lemma H1Fermi_pos {y : ℝ} (hy : 0 < y) : 0 < H1Fermi y := by
  unfold H1Fermi H1
  have hscale : (1 / 2 : ℝ) * (∫ p : ℝ, gThermal (p ^ 2 + 4 * y)) =
      ∫ p : ℝ, gThermal (4 * (p ^ 2 + y)) := by
    have hcomp := MeasureTheory.Measure.integral_comp_mul_left (g := fun p : ℝ => gThermal (p ^ 2 + 4 * y)) (2 : ℝ)
    simp only [abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul] at hcomp
    rw [one_div, ← hcomp]
    congr 1; ext p; congr 1; ring
  have hint1 : Integrable (fun p : ℝ => gThermal (p ^ 2 + y)) := integrable_gThermal_eos hy
  have hint2 : Integrable (fun p : ℝ => gThermal (4 * (p ^ 2 + y))) := by
    have h := (integrable_gThermal_eos (by positivity : 0 < 4 * y)).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
    exact h.congr (Eventually.of_forall fun p => by dsimp only [Function.comp]; congr 1; ring)
  have heq : (2 * Real.pi)⁻¹ * (∫ p : ℝ, gThermal (p ^ 2 + y)) -
      1 / 2 * ((2 * Real.pi)⁻¹ * (∫ p : ℝ, gThermal (p ^ 2 + 4 * y))) =
      (2 * Real.pi)⁻¹ * (∫ p : ℝ, Real.log (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by
    rw [show 1 / 2 * ((2 * Real.pi)⁻¹ * (∫ p : ℝ, gThermal (p ^ 2 + 4 * y))) =
        (2 * Real.pi)⁻¹ * ((1 / 2 : ℝ) * (∫ p : ℝ, gThermal (p ^ 2 + 4 * y))) by ring,
      hscale, ← mul_sub, ← MeasureTheory.integral_sub hint1 hint2]
    congr 2; ext p; exact gThermal_fermi_diff (by positivity)
  rw [heq]
  refine mul_pos (by positivity) ?_
  have hcont : Continuous (fun p : ℝ => Real.log (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) :=
    Continuous.log (by fun_prop) fun p => by positivity
  have hint : Integrable (fun p : ℝ => Real.log (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) :=
    (hint1.sub hint2).congr (Eventually.of_forall fun p => gThermal_fermi_diff (by positivity))
  exact MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (x := (0 : ℝ)) hcont hint
    (fun p => Real.log_nonneg (by linarith [Real.exp_pos (-2 * Real.pi * Real.sqrt (p ^ 2 + y))]))
    (Real.log_pos (by linarith [Real.exp_pos (-2 * Real.pi * Real.sqrt (0 ^ 2 + y))])).ne'

private lemma integrable_deriv_gThermal_eos {y : ℝ} (hy : 0 < y) :
    Integrable (fun p : ℝ => deriv gThermal (p ^ 2 + y)) := by
  let Ct : ℝ := (Real.pi / Real.sqrt y) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹
  have hcont : Continuous (fun p : ℝ => deriv gThermal (p ^ 2 + y)) := by
    have heq : (fun p : ℝ => deriv gThermal (p ^ 2 + y)) = fun p : ℝ =>
        -Real.pi / Real.sqrt (p ^ 2 + y) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by
      ext p; exact (hasDerivAt_gThermal_eos (by positivity)).deriv
    rw [heq]
    refine Continuous.mul (continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne')
      (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_)
    have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
    linarith
  have hexp := (integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul Ct
  refine hexp.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  have hv_pos : 0 < p ^ 2 + y := by positivity
  rw [(hasDerivAt_gThermal_eos hv_pos).deriv, Real.norm_eq_abs, neg_div, neg_mul, abs_neg]
  have hsq_ge : Real.sqrt y ≤ Real.sqrt (p ^ 2 + y) := Real.sqrt_le_sqrt (by linarith [sq_nonneg p])
  have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + y) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have hdeny : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y) := by
    have : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy]
    linarith
  have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-2 * Real.pi * Real.sqrt y) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) := by linarith
  rw [abs_of_nonneg (by positivity)]
  simp only [pow_zero, one_mul]
  have h1 : Real.pi / Real.sqrt (p ^ 2 + y) ≤ Real.pi / Real.sqrt y :=
    div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hy) hsq_ge
  have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
      (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ≤
      (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
    rw [inv_mul_eq_div]
    exact (div_le_div_of_nonneg_right he2 hden.le).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hdeny (by linarith))
  dsimp only [Ct]
  calc _ ≤ (Real.pi / Real.sqrt y) *
        ((1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

private lemma integrable_deriv2_gThermal_eos {y : ℝ} (hy : 0 < y) :
    Integrable (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) := by
  have hcont : Continuous (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) := by
    have heq : (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) = fun p : ℝ =>
        Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) +
        Real.pi ^ 2 / (p ^ 2 + y) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2) := by
      ext p; exact (hasDerivAt_deriv_gThermal_eos (by positivity)).deriv
    rw [heq]
    have hden_ne : ∀ p : ℝ, 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≠ 0 := by
      intro p
      have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
      linarith
    refine Continuous.add
      ((continuous_const.div (by fun_prop) fun p => by positivity).mul
        (Continuous.div (by fun_prop) (by fun_prop) hden_ne))
      ((continuous_const.div (by fun_prop) fun p => by positivity).mul
        (Continuous.div (by fun_prop) (by fun_prop) fun p => pow_ne_zero 2 (hden_ne p)))
  have hdeny : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y) := by
    have : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy]
    linarith
  let Cy : ℝ := Real.pi / (2 * y * Real.sqrt y) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ +
      Real.pi ^ 2 / y * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹
  refine ((integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 0).const_mul Cy).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  have hv_ge : y ≤ p ^ 2 + y := by linarith [sq_nonneg p]
  have hv_pos : 0 < p ^ 2 + y := by positivity
  rw [(hasDerivAt_deriv_gThermal_eos hv_pos).deriv, Real.norm_eq_abs]
  have hsq_ge : Real.sqrt y ≤ Real.sqrt (p ^ 2 + y) := Real.sqrt_le_sqrt hv_ge
  have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + y) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-2 * Real.pi * Real.sqrt y) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) := by linarith
  rw [abs_of_nonneg (by positivity)]
  simp only [pow_zero, one_mul]
  have ht1 : Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
      (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) ≤
      Real.pi / (2 * y * Real.sqrt y) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ *
        Real.exp (-(2 * Real.pi) * |p|) := by
    have ha : Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) ≤ Real.pi / (2 * y * Real.sqrt y) := by
      refine div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) ?_
      have := mul_le_mul hv_ge hsq_ge (Real.sqrt_nonneg _) hv_pos.le
      linarith
    have hb : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ≤
        (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
      rw [inv_mul_eq_div]
      exact (div_le_div_of_nonneg_right he2 hden.le).trans
        (div_le_div_of_nonneg_left (Real.exp_pos _).le hdeny (by linarith))
    calc _ ≤ (Real.pi / (2 * y * Real.sqrt y)) *
          ((1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
        mul_le_mul ha hb (by positivity) (by positivity)
      _ = _ := by ring
  have ht2 : Real.pi ^ 2 / (p ^ 2 + y) *
      (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2) ≤
      Real.pi ^ 2 / y * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹ *
        Real.exp (-(2 * Real.pi) * |p|) := by
    have ha : Real.pi ^ 2 / (p ^ 2 + y) ≤ Real.pi ^ 2 / y :=
      div_le_div_of_nonneg_left (by positivity) hy hv_ge
    have hsq_den : (1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2 ≤
        (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2 :=
      pow_le_pow_left₀ hdeny.le (by linarith) 2
    have hb : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2 ≤
        ((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
      rw [inv_mul_eq_div]
      exact (div_le_div_of_nonneg_right he2 (by positivity)).trans
        (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hsq_den)
    calc _ ≤ (Real.pi ^ 2 / y) *
          (((1 - Real.exp (-2 * Real.pi * Real.sqrt y)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
        mul_le_mul ha hb (by positivity) (by positivity)
      _ = _ := by ring
  dsimp only [Cy]; linarith

private lemma deriv_H1Fermi_neg {y : ℝ} (hy : 0 < y) : deriv H1Fermi y < 0 := by
  rw [(hasDerivAt_H1Fermi hy).deriv, (hasDerivAt_H1_eos hy).deriv,
    (hasDerivAt_H1_eos (by positivity : 0 < 4 * y)).deriv]
  have hscale : 2 * (∫ p : ℝ, deriv gThermal (p ^ 2 + 4 * y)) =
      ∫ p : ℝ, 4 * deriv gThermal (4 * (p ^ 2 + y)) := by
    have hcomp := MeasureTheory.Measure.integral_comp_mul_left
      (g := fun p : ℝ => deriv gThermal (p ^ 2 + 4 * y)) (2 : ℝ)
    simp only [abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul] at hcomp
    rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ p : ℝ, deriv gThermal (4 * (p ^ 2 + y))) =
        2⁻¹ * (∫ p : ℝ, deriv gThermal (p ^ 2 + 4 * y)) := by
      rw [← hcomp]; congr 1; ext p; congr 1; ring
    rw [h2]; ring
  have hint1 : Integrable (fun p : ℝ => deriv gThermal (p ^ 2 + y)) := integrable_deriv_gThermal_eos hy
  have hint2 : Integrable (fun p : ℝ => 4 * deriv gThermal (4 * (p ^ 2 + y))) := by
    have h := (integrable_deriv_gThermal_eos (by positivity : 0 < 4 * y)).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
    exact (h.const_mul 4).congr (Eventually.of_forall fun p => by dsimp only [Function.comp]; congr 2; ring)
  have hneg : 0 < -((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv gThermal (p ^ 2 + y)) -
      2 * ((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv gThermal (p ^ 2 + 4 * y)))) := by
    have heq : -((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv gThermal (p ^ 2 + y)) -
        2 * ((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv gThermal (p ^ 2 + 4 * y)))) =
        (2 * Real.pi)⁻¹ * (∫ p : ℝ,
          Real.pi / Real.sqrt (p ^ 2 + y) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
              (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))) := by
      rw [show -((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv gThermal (p ^ 2 + y)) -
          2 * ((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv gThermal (p ^ 2 + 4 * y)))) =
          (2 * Real.pi)⁻¹ * (2 * (∫ p : ℝ, deriv gThermal (p ^ 2 + 4 * y)) -
            (∫ p : ℝ, deriv gThermal (p ^ 2 + y))) by ring,
        hscale, ← MeasureTheory.integral_sub hint2 hint1]
      congr 2; ext p; exact deriv_gThermal_fermi_diff (by positivity)
    rw [heq]
    refine mul_pos (by positivity) ?_
    have hcont : Continuous (fun p : ℝ => Real.pi / Real.sqrt (p ^ 2 + y) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))) :=
      (continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne').mul
        (Continuous.div (by fun_prop) (by fun_prop) fun p => by positivity)
    have hint : Integrable (fun p : ℝ => Real.pi / Real.sqrt (p ^ 2 + y) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))) :=
      (hint2.sub hint1).congr (Eventually.of_forall fun p => deriv_gThermal_fermi_diff (by positivity))
    exact MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (x := (0 : ℝ)) hcont hint
      (fun p => by positivity) (by positivity)
  linarith

private lemma deriv2_H1Fermi_pos {y : ℝ} (hy : 0 < y) : 0 < deriv (deriv H1Fermi) y := by
  rw [(hasDerivAt_deriv_H1Fermi hy).deriv, (hasDerivAt_deriv_H1_eos hy).deriv,
    (hasDerivAt_deriv_H1_eos (by positivity : 0 < 4 * y)).deriv]
  have hscale : 8 * (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + 4 * y)) =
      ∫ p : ℝ, 16 * deriv (deriv gThermal) (4 * (p ^ 2 + y)) := by
    have hcomp := MeasureTheory.Measure.integral_comp_mul_left
      (g := fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + 4 * y)) (2 : ℝ)
    simp only [abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul] at hcomp
    rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ p : ℝ, deriv (deriv gThermal) (4 * (p ^ 2 + y))) =
        2⁻¹ * (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + 4 * y)) := by
      rw [← hcomp]; congr 1; ext p; congr 1; ring
    rw [h2]; ring
  have hint1 : Integrable (fun p : ℝ => deriv (deriv gThermal) (p ^ 2 + y)) := integrable_deriv2_gThermal_eos hy
  have hint2 : Integrable (fun p : ℝ => 16 * deriv (deriv gThermal) (4 * (p ^ 2 + y))) := by
    have h := (integrable_deriv2_gThermal_eos (by positivity : 0 < 4 * y)).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
    exact (h.const_mul 16).congr (Eventually.of_forall fun p => by dsimp only [Function.comp]; congr 2; ring)
  have heq : (2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + y)) -
      8 * ((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + 4 * y))) =
      (2 * Real.pi)⁻¹ * (∫ p : ℝ,
        (Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) +
        Real.pi ^ 2 / (p ^ 2 + y) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2))) := by
    rw [show (2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + y)) -
        8 * ((2 * Real.pi)⁻¹ * (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + 4 * y))) =
        (2 * Real.pi)⁻¹ * ((∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + y)) -
          8 * (∫ p : ℝ, deriv (deriv gThermal) (p ^ 2 + 4 * y))) by ring,
      hscale, ← MeasureTheory.integral_sub hint1 hint2]
    congr 2; ext p; exact deriv2_gThermal_fermi_diff (by positivity)
  rw [heq]
  refine mul_pos (by positivity) ?_
  have hcont : Continuous (fun p : ℝ =>
      Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) +
      Real.pi ^ 2 / (p ^ 2 + y) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2)) :=
    ((continuous_const.div (by fun_prop) fun p => by positivity).mul
      (Continuous.div (by fun_prop) (by fun_prop) fun p => by positivity)).add
    ((continuous_const.div (by fun_prop) fun p => by positivity).mul
      (Continuous.div (by fun_prop) (by fun_prop) fun p => by positivity))
  have hint : Integrable (fun p : ℝ =>
      Real.pi / (2 * (p ^ 2 + y) * Real.sqrt (p ^ 2 + y)) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) +
      Real.pi ^ 2 / (p ^ 2 + y) *
        (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
          (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2)) :=
    (hint1.sub hint2).congr (Eventually.of_forall fun p => deriv2_gThermal_fermi_diff (by positivity))
  exact MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (x := (0 : ℝ)) hcont hint
    (fun p => by positivity) (by positivity)

private lemma H3Fermi_pos {y : ℝ} (hy : 0 < y) : 0 < H3Fermi y := by
  unfold H3Fermi H3
  have hscale : (1 / 8 : ℝ) * (∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (p ^ 2 + 4 * y)) =
      ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (4 * (p ^ 2 + y)) := by
    let f : ℝ → ℝ := fun p => p ^ 2 * gThermal (p ^ 2 + 4 * y)
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    have hcomp := MeasureTheory.Measure.integral_comp_mul_left (g := (Set.Ioi (0 : ℝ)).indicator f) (2 : ℝ)
    simp only [abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul] at hcomp
    have h4 : (1 / 4 : ℝ) * (∫ p : ℝ, (Set.Ioi (0 : ℝ)).indicator f (2 * p)) =
        ∫ p : ℝ, (Set.Ioi (0 : ℝ)).indicator (fun p : ℝ => p ^ 2 * gThermal (4 * (p ^ 2 + y))) p := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext p
      by_cases hp : 0 < p
      · have hp2 : 0 < 2 * p := by linarith
        simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hp),
          Set.indicator_of_mem (Set.mem_Ioi.mpr hp2), f]
        have harg : (2 * p) ^ 2 + 4 * y = 4 * (p ^ 2 + y) := by ring
        rw [harg]; ring
      · have hp2 : ¬ (0 < 2 * p) := by linarith
        simp only [Set.indicator_of_notMem (show p ∉ Set.Ioi (0 : ℝ) from hp),
          Set.indicator_of_notMem (show 2 * p ∉ Set.Ioi (0 : ℝ) from hp2), mul_zero]
    rw [← h4, hcomp]; ring
  have hint_fn : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + t)) := by
    intro t ht
    let C : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹
    have hcont : Continuous (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + t)) := by
      refine (continuous_pow 2).mul ?_
      unfold gThermal
      refine Continuous.neg (Continuous.log (by fun_prop) fun p => ?_)
      have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + t)]
      linarith
    refine ((integrable_pow_exp_neg_abs_eos (a := 2 * Real.pi) (by positivity) 2).const_mul C).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have hv_pos : 0 < p ^ 2 + t := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg p) (gThermal_pos_of_pos hv_pos).le)]
    have hsqy : Real.sqrt t ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt (by linarith [sq_nonneg p])
    have hsqp : |p| ≤ Real.sqrt (p ^ 2 + t) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have ht_lt : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hv_pos]
    have hlog_bd : gThermal (p ^ 2 + t) ≤
        Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) := by
      unfold gThermal
      set u := Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))
      have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith : 0 < 1 - u))
      rw [Real.log_inv] at hlog
      have heq : (1 - u)⁻¹ - 1 = u / (1 - u) := by field_simp [show 1 - u ≠ 0 by linarith]; ring
      linarith
    have he1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤ Real.exp (-2 * Real.pi * Real.sqrt t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have he2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤ Real.exp (-(2 * Real.pi) * |p|) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt t) := by
      have : Real.exp (-2 * Real.pi * Real.sqrt t) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr ht]
      linarith
    have hg_le : gThermal (p ^ 2 + t) ≤ C * Real.exp (-(2 * Real.pi) * |p|) := by
      calc _ ≤ Real.exp (-(2 * Real.pi) * |p|) / (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) :=
            hlog_bd.trans (div_le_div_of_nonneg_right he2 (by linarith))
        _ ≤ Real.exp (-(2 * Real.pi) * |p|) / (1 - Real.exp (-2 * Real.pi * Real.sqrt t)) :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith)
        _ = C * Real.exp (-(2 * Real.pi) * |p|) := by dsimp only [C]; ring
    calc p ^ 2 * gThermal (p ^ 2 + t)
        ≤ p ^ 2 * (C * Real.exp (-(2 * Real.pi) * |p|)) := mul_le_mul_of_nonneg_left hg_le (sq_nonneg p)
      _ = C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|)) := by rw [sq_abs]; ring
  have hint1 : IntegrableOn (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + y)) (Set.Ioi 0) :=
    (hint_fn y hy).integrableOn
  have hint2 : IntegrableOn (fun p : ℝ => p ^ 2 * gThermal (4 * (p ^ 2 + y))) (Set.Ioi 0) := by
    have h := ((hint_fn (4 * y) (by positivity)).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul (1 / 4 : ℝ)
    exact (h.congr (Eventually.of_forall fun p => by
      dsimp only [Function.comp]
      have harg : (2 * p) ^ 2 + 4 * y = 4 * (p ^ 2 + y) := by ring
      rw [harg]; ring)).integrableOn
  have heq : (2 * Real.pi ^ 2)⁻¹ * (∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (p ^ 2 + y)) -
      1 / 8 * ((2 * Real.pi ^ 2)⁻¹ * (∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (p ^ 2 + 4 * y))) =
      (2 * Real.pi ^ 2)⁻¹ * (∫ p in Set.Ioi (0 : ℝ),
        p ^ 2 * Real.log (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by
    rw [show 1 / 8 * ((2 * Real.pi ^ 2)⁻¹ * (∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (p ^ 2 + 4 * y))) =
        (2 * Real.pi ^ 2)⁻¹ * ((1 / 8 : ℝ) * (∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (p ^ 2 + 4 * y))) by ring,
      hscale, ← mul_sub, ← MeasureTheory.integral_sub hint1 hint2]
    congr 2; ext p; rw [← mul_sub, gThermal_fermi_diff (by positivity)]
  rw [heq]
  refine mul_pos (by positivity) ?_
  have hint : IntegrableOn (fun p : ℝ => p ^ 2 * Real.log (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))
      (Set.Ioi 0) :=
    (hint1.sub hint2).congr (Eventually.of_forall fun p => by
      dsimp only [Pi.sub_apply]; rw [← mul_sub, gThermal_fermi_diff (by positivity)])
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun p => mul_nonneg (sq_nonneg p)
      (Real.log_nonneg (by linarith [Real.exp_pos (-2 * Real.pi * Real.sqrt (p ^ 2 + y))]))) hint]
  have hsub : Set.Ioi (0 : ℝ) ⊆
      Function.support (fun p : ℝ => p ^ 2 * Real.log (1 + Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) ∩
      Set.Ioi 0 := by
    intro p hp
    refine ⟨?_, hp⟩
    rw [Function.mem_support]
    exact (mul_pos (pow_pos hp 2)
      (Real.log_pos (by linarith [Real.exp_pos (-2 * Real.pi * Real.sqrt (p ^ 2 + y))]))).ne'
  exact lt_of_lt_of_le (by simp) (MeasureTheory.measure_mono hsub)

private lemma hasDerivAt_H3Fermi {y : ℝ} (hy : 0 < y) :
    HasDerivAt H3Fermi (-(4 * Real.pi)⁻¹ * H1Fermi y) y := by
  have h1 : HasDerivAt H3 (-(4 * Real.pi)⁻¹ * H1 y) y := H3_deriv hy
  have h2 : HasDerivAt (fun s : ℝ => H3 (4 * s)) ((-(4 * Real.pi)⁻¹ * H1 (4 * y)) * 4) y := by
    have hmul : HasDerivAt (fun s : ℝ => 4 * s) 4 y := by simpa using (hasDerivAt_id y).const_mul (4 : ℝ)
    exact HasDerivAt.comp (h₂ := H3) (h := fun s : ℝ => 4 * s) y
      (H3_deriv (by positivity : 0 < 4 * y)) hmul
  have hsub := h1.sub (h2.const_mul (1 / 8 : ℝ))
  refine hsub.congr_deriv ?_
  unfold H1Fermi; ring

/-- Strict thermodynamic monotonicity in 1D Fermi gas: for `m > 0`, `T > 0`,
`F'(T) > 0`, `ε(T) > 0`, and `ε'(T) = T F''(T) > 0`. -/
theorem fermiPressure1D_thermodynamic_pos {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    0 < deriv (fermiPressure1D m) T ∧
    0 < energyDensity (fermiPressure1D m) T ∧
    0 < deriv (energyDensity (fermiPressure1D m)) T := by
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  have heq : ∀ t : ℝ, 0 < t → fermiPressure1D m t = 2 * Real.pi * t ^ 2 * H1Fermi (c ^ 2 / t ^ 2) := by
    intro t ht
    rw [fermiPressure1D_doubling hm ht, bosePressure1D_eq_H1 ht, bosePressure1D_eq_H1 ht]
    unfold H1Fermi; dsimp only [c]
    have h1 : m ^ 2 / (2 * Real.pi * t) ^ 2 = (m / (2 * Real.pi)) ^ 2 / t ^ 2 := by field_simp
    have h2 : (2 * m) ^ 2 / (2 * Real.pi * t) ^ 2 = 4 * ((m / (2 * Real.pi)) ^ 2 / t ^ 2) := by field_simp; ring
    rw [h1, h2]; ring
  have hd_y : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => c ^ 2 / s ^ 2) (-2 * c ^ 2 / t ^ 3) t := by
    intro t ht
    have h1 := ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht.ne')).const_mul (c ^ 2)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [div_eq_mul_inv]) |>.congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd1 : ∀ t : ℝ, 0 < t →
      HasDerivAt (fermiPressure1D m)
        (4 * Real.pi * t * (H1Fermi (c ^ 2 / t ^ 2) - (c ^ 2 / t ^ 2) * deriv H1Fermi (c ^ 2 / t ^ 2))) t := by
    intro t ht
    have hy : 0 < c ^ 2 / t ^ 2 := by positivity
    have hH : HasDerivAt (fun s : ℝ => H1Fermi (c ^ 2 / s ^ 2))
        (deriv H1Fermi (c ^ 2 / t ^ 2) * (-2 * c ^ 2 / t ^ 3)) t :=
      HasDerivAt.comp (h₂ := H1Fermi) (h := fun s : ℝ => c ^ 2 / s ^ 2) t
        (hasDerivAt_H1Fermi hy).differentiableAt.hasDerivAt (hd_y t ht)
    have hp := ((hasDerivAt_pow 2 t).const_mul (2 * Real.pi)).mul hH
    have hev : fermiPressure1D m =ᶠ[𝓝 t] fun s => 2 * Real.pi * s ^ 2 * H1Fermi (c ^ 2 / s ^ 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs; exact heq s hs
    refine (hp.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd2 : HasDerivAt (deriv (fermiPressure1D m))
      (4 * Real.pi * (H1Fermi (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1Fermi (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1Fermi) (c ^ 2 / T ^ 2))) T := by
    have hy : 0 < c ^ 2 / T ^ 2 := by positivity
    have hH1 : HasDerivAt (fun s : ℝ => H1Fermi (c ^ 2 / s ^ 2))
        (deriv H1Fermi (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := H1Fermi) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (hasDerivAt_H1Fermi hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hH1' : HasDerivAt (fun s : ℝ => deriv H1Fermi (c ^ 2 / s ^ 2))
        (deriv (deriv H1Fermi) (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := deriv H1Fermi) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (hasDerivAt_deriv_H1Fermi hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hbr := hH1.sub ((hd_y T hT).mul hH1')
    have hprod := ((hasDerivAt_id T).const_mul (4 * Real.pi)).mul hbr
    have hev : deriv (fermiPressure1D m) =ᶠ[𝓝 T] fun s =>
        4 * Real.pi * s * (H1Fermi (c ^ 2 / s ^ 2) - (c ^ 2 / s ^ 2) * deriv H1Fermi (c ^ 2 / s ^ 2)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with s hs; exact (hd1 s hs).deriv
    refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]; field_simp [hT.ne']; ring
  have hyT : 0 < c ^ 2 / T ^ 2 := by positivity
  have hH_pos := H1Fermi_pos hyT
  have hH1_neg := deriv_H1Fermi_neg hyT
  have hH2_pos := deriv2_H1Fermi_pos hyT
  have hP1 : 0 < deriv (fermiPressure1D m) T := by
    rw [(hd1 T hT).deriv]
    have : 0 < H1Fermi (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1Fermi (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE : 0 < energyDensity (fermiPressure1D m) T := by
    unfold energyDensity
    rw [(hd1 T hT).deriv, heq T hT]
    have : T * (4 * Real.pi * T * (H1Fermi (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1Fermi (c ^ 2 / T ^ 2))) -
        2 * Real.pi * T ^ 2 * H1Fermi (c ^ 2 / T ^ 2) =
        2 * Real.pi * T ^ 2 * (H1Fermi (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H1Fermi (c ^ 2 / T ^ 2)) := by ring
    rw [this]
    have : 0 < H1Fermi (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H1Fermi (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE' : 0 < deriv (energyDensity (fermiPressure1D m)) T := by
    have hdE : HasDerivAt (energyDensity (fermiPressure1D m))
        (T * (4 * Real.pi * (H1Fermi (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1Fermi (c ^ 2 / T ^ 2) +
          2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1Fermi) (c ^ 2 / T ^ 2)))) T := by
      have h1 := ((hasDerivAt_id T).mul hd2).sub (hd1 T hT)
      refine h1.congr_deriv ?_
      rw [(hd1 T hT).deriv]; simp only [id_eq]; ring
    rw [hdE.deriv]
    have hsqy : 0 < (c ^ 2 / T ^ 2) ^ 2 := by positivity
    have hterm2 : 0 < 2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1Fermi) (c ^ 2 / T ^ 2) := by positivity
    have : 0 < H1Fermi (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H1Fermi (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H1Fermi) (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  exact ⟨hP1, hE, hE'⟩

/-- Strict thermodynamic monotonicity in 3D Fermi gas: for `m > 0`, `T > 0`,
`F'(T) > 0`, `ε(T) > 0`, and `ε'(T) = T F''(T) > 0`. -/
theorem fermiPressure3D_thermodynamic_pos {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    0 < deriv (fermiPressure3D m) T ∧
    0 < energyDensity (fermiPressure3D m) T ∧
    0 < deriv (energyDensity (fermiPressure3D m)) T := by
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  have heq : ∀ t : ℝ, 0 < t → fermiPressure3D m t = 8 * Real.pi ^ 3 * t ^ 4 * H3Fermi (c ^ 2 / t ^ 2) := by
    intro t ht
    rw [fermiPressure3D_doubling hm ht, bosePressure3D_eq_H3 ht, bosePressure3D_eq_H3 ht]
    unfold H3Fermi; dsimp only [c]
    have h1 : m ^ 2 / (2 * Real.pi * t) ^ 2 = (m / (2 * Real.pi)) ^ 2 / t ^ 2 := by field_simp
    have h2 : (2 * m) ^ 2 / (2 * Real.pi * t) ^ 2 = 4 * ((m / (2 * Real.pi)) ^ 2 / t ^ 2) := by field_simp; ring
    rw [h1, h2]; ring
  have hd_y : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => c ^ 2 / s ^ 2) (-2 * c ^ 2 / t ^ 3) t := by
    intro t ht
    have h1 := ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht.ne')).const_mul (c ^ 2)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [div_eq_mul_inv]) |>.congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd_H3F' : ∀ y : ℝ, 0 < y → HasDerivAt (deriv H3Fermi) (-(4 * Real.pi)⁻¹ * deriv H1Fermi y) y := by
    intro y hy
    have hev : deriv H3Fermi =ᶠ[𝓝 y] fun s => -(4 * Real.pi)⁻¹ * H1Fermi s := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with s hs; exact (hasDerivAt_H3Fermi hs).deriv
    exact ((hasDerivAt_H1Fermi hy).differentiableAt.hasDerivAt.const_mul (-(4 * Real.pi)⁻¹)).congr_of_eventuallyEq hev
  have hd1 : ∀ t : ℝ, 0 < t →
      HasDerivAt (fermiPressure3D m)
        (16 * Real.pi ^ 3 * t ^ 3 * (2 * H3Fermi (c ^ 2 / t ^ 2) - (c ^ 2 / t ^ 2) * deriv H3Fermi (c ^ 2 / t ^ 2))) t := by
    intro t ht
    have hy : 0 < c ^ 2 / t ^ 2 := by positivity
    have hH : HasDerivAt (fun s : ℝ => H3Fermi (c ^ 2 / s ^ 2))
        (deriv H3Fermi (c ^ 2 / t ^ 2) * (-2 * c ^ 2 / t ^ 3)) t :=
      HasDerivAt.comp (h₂ := H3Fermi) (h := fun s : ℝ => c ^ 2 / s ^ 2) t
        (hasDerivAt_H3Fermi hy).differentiableAt.hasDerivAt (hd_y t ht)
    have hp := ((hasDerivAt_pow 4 t).const_mul (8 * Real.pi ^ 3)).mul hH
    have hev : fermiPressure3D m =ᶠ[𝓝 t] fun s => 8 * Real.pi ^ 3 * s ^ 4 * H3Fermi (c ^ 2 / s ^ 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs; exact heq s hs
    refine (hp.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd2 : HasDerivAt (deriv (fermiPressure3D m))
      (16 * Real.pi ^ 3 * T ^ 2 * (6 * H3Fermi (c ^ 2 / T ^ 2) - 5 * (c ^ 2 / T ^ 2) * deriv H3Fermi (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3Fermi) (c ^ 2 / T ^ 2))) T := by
    have hy : 0 < c ^ 2 / T ^ 2 := by positivity
    have hH3 : HasDerivAt (fun s : ℝ => H3Fermi (c ^ 2 / s ^ 2))
        (deriv H3Fermi (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := H3Fermi) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (hasDerivAt_H3Fermi hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hH3' : HasDerivAt (fun s : ℝ => deriv H3Fermi (c ^ 2 / s ^ 2))
        (deriv (deriv H3Fermi) (c ^ 2 / T ^ 2) * (-2 * c ^ 2 / T ^ 3)) T :=
      HasDerivAt.comp (h₂ := deriv H3Fermi) (h := fun s : ℝ => c ^ 2 / s ^ 2) T
        (hd_H3F' (c ^ 2 / T ^ 2) hy).differentiableAt.hasDerivAt (hd_y T hT)
    have hbr := (hH3.const_mul 2).sub ((hd_y T hT).mul hH3')
    have hprod := ((hasDerivAt_pow 3 T).const_mul (16 * Real.pi ^ 3)).mul hbr
    have hev : deriv (fermiPressure3D m) =ᶠ[𝓝 T] fun s =>
        16 * Real.pi ^ 3 * s ^ 3 * (2 * H3Fermi (c ^ 2 / s ^ 2) - (c ^ 2 / s ^ 2) * deriv H3Fermi (c ^ 2 / s ^ 2)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with s hs; exact (hd1 s hs).deriv
    refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply]; field_simp [hT.ne']; ring
  have hyT : 0 < c ^ 2 / T ^ 2 := by positivity
  have hH3_p := H3Fermi_pos hyT
  have hH3'_n : deriv H3Fermi (c ^ 2 / T ^ 2) < 0 := by
    rw [(hasDerivAt_H3Fermi hyT).deriv]
    have := H1Fermi_pos hyT
    have hpi : 0 < (4 * Real.pi)⁻¹ := by positivity
    nlinarith
  have hH3''_p : 0 < deriv (deriv H3Fermi) (c ^ 2 / T ^ 2) := by
    rw [(hd_H3F' (c ^ 2 / T ^ 2) hyT).deriv]
    have := deriv_H1Fermi_neg hyT
    have hpi : 0 < (4 * Real.pi)⁻¹ := by positivity
    nlinarith
  have hP1 : 0 < deriv (fermiPressure3D m) T := by
    rw [(hd1 T hT).deriv]
    have : 0 < 2 * H3Fermi (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H3Fermi (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE : 0 < energyDensity (fermiPressure3D m) T := by
    unfold energyDensity
    rw [(hd1 T hT).deriv, heq T hT]
    have : T * (16 * Real.pi ^ 3 * T ^ 3 * (2 * H3Fermi (c ^ 2 / T ^ 2) - (c ^ 2 / T ^ 2) * deriv H3Fermi (c ^ 2 / T ^ 2))) -
        8 * Real.pi ^ 3 * T ^ 4 * H3Fermi (c ^ 2 / T ^ 2) =
        8 * Real.pi ^ 3 * T ^ 4 * (3 * H3Fermi (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H3Fermi (c ^ 2 / T ^ 2)) := by ring
    rw [this]
    have : 0 < 3 * H3Fermi (c ^ 2 / T ^ 2) - 2 * (c ^ 2 / T ^ 2) * deriv H3Fermi (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  have hE' : 0 < deriv (energyDensity (fermiPressure3D m)) T := by
    have hdE : HasDerivAt (energyDensity (fermiPressure3D m))
        (T * (16 * Real.pi ^ 3 * T ^ 2 * (6 * H3Fermi (c ^ 2 / T ^ 2) - 5 * (c ^ 2 / T ^ 2) * deriv H3Fermi (c ^ 2 / T ^ 2) +
          2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3Fermi) (c ^ 2 / T ^ 2)))) T := by
      have h1 := ((hasDerivAt_id T).mul hd2).sub (hd1 T hT)
      refine h1.congr_deriv ?_
      rw [(hd1 T hT).deriv]; simp only [id_eq]; ring
    rw [hdE.deriv]
    have hsqy : 0 < (c ^ 2 / T ^ 2) ^ 2 := by positivity
    have hterm2 : 0 < 2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3Fermi) (c ^ 2 / T ^ 2) := by positivity
    have : 0 < 6 * H3Fermi (c ^ 2 / T ^ 2) - 5 * (c ^ 2 / T ^ 2) * deriv H3Fermi (c ^ 2 / T ^ 2) +
        2 * (c ^ 2 / T ^ 2) ^ 2 * deriv (deriv H3Fermi) (c ^ 2 / T ^ 2) := by nlinarith
    positivity
  exact ⟨hP1, hE, hE'⟩

/-! ### 2. Temperature-Eliminated Equation of State `P(ε)` & Sound Speed `c_s²(ε)` Transfer -/

private lemma contDiffOn_iteratedDeriv_top {f : ℝ → ℂ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hU (by simp)

private lemma eval_congr_vars {σ : Type*} {f g : σ → ℂ} (P : MvPolynomial σ ℂ)
    (h : ∀ i ∈ P.vars, f i = g i) : MvPolynomial.eval f P = MvPolynomial.eval g P := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun s hs => ?_
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  rw [h i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨s, hs, hi⟩)]

private lemma clearDenom_rat_on_open {r : ℕ} {f : ℝ → ℂ} {U : Set ℝ}
    (hU : IsOpen U) (hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) (hP_ne : P ≠ 0)
    (hP : ∀ x ∈ U,
      (∀ β ∈ P.support, (P.coeff β).denom.eval (x : ℂ) ≠ 0) →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f x) (evalRatU P (x : ℂ)) = 0) :
    ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q ≠ 0 ∧
      ∀ x ∈ U, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f x) (evalU Q (x : ℂ)) = 0 := by
  classical
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ α ∈ P.support, MvPolynomial.monomial α
      ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)
  have hQ_coeff : ∀ α, Q.coeff α =
      (P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom := by
    intro α
    dsimp only [Q]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ P.support
    · rw [Finset.sum_eq_single α]
      · simp
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
      rw [hP0, RatFunc.num_zero, zero_mul, Finset.sum_eq_zero]
      intro β hβ
      simp [show β ≠ α from fun h => hα (h ▸ hβ)]
  have hQ_ne : Q ≠ 0 := by
    intro h0
    apply hP_ne
    ext α
    have hc := congrArg (fun R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) => R.coeff α) h0
    rw [hQ_coeff] at hc
    have hden_ne : (∏ β ∈ P.support.erase α, (P.coeff β).denom) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ => RatFunc.denom_ne_zero _
    exact RatFunc.num_eq_zero_iff.mp ((mul_eq_zero.mp hc).resolve_right hden_ne)
  let D : Polynomial ℂ := ∏ α ∈ P.support, (P.coeff α).denom
  have hQ_eval : ∀ x : ℂ, (∀ β ∈ P.support, (P.coeff β).denom.eval x ≠ 0) →
      evalU Q x = D.eval x • evalRatU P x := by
    intro x hx
    ext α
    rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, hQ_coeff,
      MvPolynomial.coeff_smul, smul_eq_mul, evalRatU, MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ P.support
    · rw [Finset.sum_eq_single α]
      · simp only [↓reduceIte, ratEval, D, Polynomial.eval_prod]
        rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval x) hα,
          Polynomial.eval_mul, Polynomial.eval_prod]
        field_simp [hx α hα]
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
      rw [hP0, RatFunc.num_zero, zero_mul, Polynomial.eval_zero, Finset.sum_eq_zero]
      · simp
      · intro β hβ
        rw [ite_eq_right_iff]
        intro hβα; subst hβα; exact absurd hβ hα
  let g : ℝ → ℂ := fun x =>
    MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f x) (evalU Q (x : ℂ))
  have hg_cont : ContinuousOn g U := by
    have hpoly : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
        ContinuousOn (fun x : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f x)
          (evalU R (x : ℂ))) U := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C p =>
        simp only [evalU, MvPolynomial.map_C, MvPolynomial.eval_C, Polynomial.coe_evalRingHom]
        exact (p.continuous.comp Complex.continuous_ofReal).continuousOn
      | add A B hA hB => simp only [evalU, map_add]; exact hA.add hB
      | mul_X A j hA =>
        simp only [evalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
        exact hA.mul ((contDiffOn_iteratedDeriv_top hU hf_smooth j.val).continuousOn)
    exact hpoly Q
  refine ⟨Q, hQ_ne, fun x hx => ?_⟩
  let roots : Finset ℂ := P.support.biUnion fun β => (P.coeff β).denom.roots.toFinset
  have hfreq : ∃ᶠ t in 𝓝 x, g t = 0 := by
    rw [Filter.frequently_iff]
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hs (hU.mem_nhds hx))
    have hIoo_inf : (Set.Ioo (x - ε) (x + ε)).Infinite := Set.Ioo_infinite (by linarith)
    have hC_inf : (Complex.ofReal '' Set.Ioo (x - ε) (x + ε)).Infinite :=
      hIoo_inf.image Complex.ofReal_injective.injOn
    obtain ⟨w, hw, hwnot⟩ := hC_inf.exists_notMem_finset roots
    obtain ⟨t, ht, rfl⟩ := hw
    have ht_ball : t ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have ht_mem := hball ht_ball
    have hden_ne : ∀ β ∈ P.support, (P.coeff β).denom.eval (t : ℂ) ≠ 0 := by
      intro β hβ h0
      apply hwnot
      exact Finset.mem_biUnion.mpr ⟨β, hβ,
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (RatFunc.denom_ne_zero _)).mpr h0)⟩
    refine ⟨t, ht_mem.1, ?_⟩
    dsimp only [g]
    rw [hQ_eval (t : ℂ) hden_ne, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      hP t ht_mem.2 hden_ne, mul_zero]
  exact isClosed_singleton.mem_of_frequently_of_tendsto hfreq (hg_cont.continuousAt (hU.mem_nhds hx))

/-- Lift `MvPolynomial (Fin (r + 1)) (Polynomial ℂ)` to `MvPolynomial ℕ ℂ` sending the
independent variable `Polynomial.X` to `MvPolynomial.X 0` and jet variable `j` to `MvPolynomial.X (j + 1)`. -/
private def liftPolyToNat {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    MvPolynomial ℕ ℂ :=
  MvPolynomial.eval₂ (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ)).toRingHom
    (fun j : Fin (r + 1) => MvPolynomial.X (j.val + 1)) Q

private lemma eval_liftPolyToNat {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (x : ℂ) (v : Fin (r + 1) → ℂ) :
    MvPolynomial.eval (fun k : ℕ => if k = 0 then x else if hlt : k - 1 < r + 1 then v ⟨k - 1, hlt⟩ else 0)
      (liftPolyToNat Q) =
      MvPolynomial.eval v (evalU Q x) := by
  induction Q using MvPolynomial.induction_on with
  | C p =>
    simp only [liftPolyToNat, evalU, MvPolynomial.eval₂_C, MvPolynomial.map_C, MvPolynomial.eval_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coe_evalRingHom]
    induction p using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Polynomial.eval_add, ha, hb]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial, map_mul, map_pow,
        MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_X, ↓reduceIte]
  | add A B hA hB =>
    rw [show liftPolyToNat (A + B) = liftPolyToNat A + liftPolyToNat B by simp [liftPolyToNat],
      map_add, hA, hB, show evalU (A + B) x = evalU A x + evalU B x by simp [evalU], map_add]
  | mul_X A j hA =>
    rw [show liftPolyToNat (A * MvPolynomial.X j) = liftPolyToNat A * MvPolynomial.X (j.val + 1) by
      simp [liftPolyToNat]]
    rw [map_mul, hA, MvPolynomial.eval_X,
      show evalU (A * MvPolynomial.X j) x = evalU A x * MvPolynomial.X j by simp [evalU],
      map_mul, MvPolynomial.eval_X]
    simp [j.isLt]

private lemma liftPolyToNat_ne_zero {r : ℕ} {Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)}
    (hQ : Q ≠ 0) : liftPolyToNat Q ≠ 0 := by
  intro h0
  apply hQ
  have hzero : ∀ (x : ℂ) (v : Fin (r + 1) → ℂ), MvPolynomial.eval v (evalU Q x) = 0 := by
    intro x v
    rw [← eval_liftPolyToNat Q x v, h0, map_zero]
  apply MvPolynomial.ext
  intro α
  change Q.coeff α = 0
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_zero]
  have hcoeff : (evalU Q x).coeff α = 0 := by
    have heval_zero : evalU Q x = 0 := MvPolynomial.funext_iff.mpr (hzero x)
    rw [heval_zero]
    simp
  simpa [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom] using hcoeff

/-- **Master Equation-of-State Differential-Algebra Transfer**:
Let `P : ℝ → ℝ` be real-analytic on `(0, ∞)` and satisfy NO nonzero ADE over `ℂ[T]`.
Suppose `p : ℝ → ℝ` is smooth on an open set `U ⊆ ℝ` containing `ε(T₀)` (where `T₀ > 0`,
`P'(T₀) ≠ 0`, `ε'(T₀) ≠ 0`) and agrees with the temperature-eliminated equation of state
`p(ε(T)) = P(T)` near `T₀`. Then:
1. `p` satisfies NO nonzero ADE over `ℂ(ε)` on `U`;
2. `c_s²(ε) = p'(ε)` satisfies NO nonzero ADE over `ℂ(ε)` on `U`. -/
theorem eos_no_rat_ade_of_pressure {P : ℝ → ℝ}
    (hP_an : AnalyticOnNhd ℝ (fun T : ℝ => (P T : ℂ)) (Set.Ioi 0))
    (hP_no_ade : ∀ {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)),
      (∀ T : ℝ, 0 < T →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (P t : ℂ)) T)
          (evalU Q (T : ℂ)) = 0) → Q = 0)
    {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hE₀_mem : energyDensity P T₀ ∈ U)
    (hP'₀_ne : deriv P T₀ ≠ 0)
    (hE'₀_ne : deriv (energyDensity P) T₀ ≠ 0)
    (heos : ∀ᶠ T in 𝓝 T₀, p (energyDensity P T) = P T) :
    ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U,
        (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) →
      R = 0 := by
  intro r R hR
  by_contra hR_ne
  have hpC_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : ℝ => (p e : ℂ)) U :=
    Complex.ofRealCLM.contDiff.contDiffOn.comp hp_smooth (Set.mapsTo_univ _ _)
  obtain ⟨Q, hQ_ne, hQ_zero⟩ := clearDenom_rat_on_open hU hpC_smooth R hR_ne hR
  -- Real-analyticity of P implies real-analyticity of energyDensity P on (0, ∞)
  have hP_real_an : AnalyticOnNhd ℝ P (Set.Ioi 0) := by
    intro t ht
    have hre : AnalyticAt ℝ (fun s : ℝ => ((P s : ℂ)).re) t :=
      AnalyticAt.comp (g := fun z : ℂ => z.re) (f := fun s : ℝ => (P s : ℂ))
        (Complex.reCLM.analyticAt (P t : ℂ)) (hP_an t ht)
    simpa using hre
  have hE_cont : ContinuousAt (energyDensity P) T₀ := by
    have h1 := (hP_real_an T₀ hT₀).deriv.continuousAt
    have h2 := (hP_real_an T₀ hT₀).continuousAt
    exact (continuousAt_id.mul h1).sub h2
  have hE'_cont : ContinuousAt (deriv (energyDensity P)) T₀ := by
    have hE_an : AnalyticAt ℝ (energyDensity P) T₀ :=
      (analyticAt_id.mul (hP_real_an T₀ hT₀).deriv).sub (hP_real_an T₀ hT₀)
    exact hE_an.deriv.continuousAt
  have hP'_cont : ContinuousAt (deriv P) T₀ := (hP_real_an T₀ hT₀).deriv.continuousAt
  -- Find an open neighborhood V of T₀ inside (0, ∞) mapped by energyDensity P into U where e' ≠ 0, P' ≠ 0
  have hev_V : ∀ᶠ T in 𝓝 T₀, 0 < T ∧ energyDensity P T ∈ U ∧ deriv (energyDensity P) T ≠ 0 ∧
      deriv P T ≠ 0 ∧ p (energyDensity P T) = P T := by
    filter_upwards [isOpen_Ioi.mem_nhds hT₀, hE_cont.preimage_mem_nhds (hU.mem_nhds hE₀_mem),
      hE'_cont.eventually_ne hE'₀_ne, hP'_cont.eventually_ne hP'₀_ne, heos] with T h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp hev_V
  let V : Set ℝ := Metric.ball T₀ δ
  have hV_open : IsOpen V := Metric.isOpen_ball
  have hV_ne : V.Nonempty := ⟨T₀, Metric.mem_ball_self hδ_pos⟩
  -- Define the jet coordinates of p(e(T)) as functions of T on V:
  -- y 0 T = (e(T) : ℂ), y (j+1) T = iteratedDeriv j (p : ℝ → ℂ) (e(T))
  let y : ℕ → ℝ → ℂ := fun k T =>
    match k with
    | 0 => (energyDensity P T : ℂ)
    | j + 1 => iteratedDeriv j (fun e : ℝ => (p e : ℂ)) (energyDensity P T)
  have hrel_y : ∃ A : MvPolynomial ℕ ℂ, A ≠ 0 ∧ ∀ T ∈ V, MvPolynomial.eval (fun k => y k T) A = 0 := by
    refine ⟨liftPolyToNat Q, liftPolyToNat_ne_zero hQ_ne, fun T hT => ?_⟩
    have hT_props := hδ_sub hT
    have hval := hQ_zero (energyDensity P T) hT_props.2.1
    rw [← eval_liftPolyToNat Q (energyDensity P T : ℂ)
      (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) (energyDensity P T))] at hval
    have heq_coord : ∀ k ∈ (liftPolyToNat Q).vars,
        y k T = (if k = 0 then (energyDensity P T : ℂ)
          else if hlt : k - 1 < r + 1 then iteratedDeriv (k - 1) (fun e : ℝ => (p e : ℂ)) (energyDensity P T) else 0) := by
      intro k hk
      cases k with
      | zero => simp [y]
      | succ j =>
        have hjlt : j < r + 1 := by
          -- vars of liftPolyToNat Q are subset of {0, ..., r+1}
          have hsub : (liftPolyToNat Q).vars ⊆ Finset.range (r + 2) := by
            clear hk hval hQ_zero hQ_ne hT_props hT
            induction Q using MvPolynomial.induction_on with
            | C q =>
              simp only [liftPolyToNat, MvPolynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
              induction q using Polynomial.induction_on' with
              | add a b ha hb =>
                rw [map_add]; exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset ha hb)
              | monomial n a =>
                simp only [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
                refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ?_ ?_)
                · simp
                · exact (MvPolynomial.vars_pow _ _).trans (by simp)
            | add A B hA hB =>
              rw [liftPolyToNat, MvPolynomial.eval₂_add]
              exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset hA hB)
            | mul_X A m hA =>
              rw [liftPolyToNat, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
              refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset hA ?_)
              simp [Finset.mem_range]; omega
          have := Finset.mem_range.mp (hsub hk); omega
        simp [y, hjlt]
    rw [eval_congr_vars (liftPolyToNat Q) heq_coord]
    exact hval
  obtain ⟨n, A, T₁, hT₁_V, hS₁_ne, hA_zero⟩ := ordinary_relation V hV_ne y hrel_y
  have hT₁_props := hδ_sub hT₁_V
  have hT₁_pos : 0 < T₁ := hT₁_props.1
  -- Key thermodynamic identity on V: p'(e(T)) * e'(T) = P'(T) = (e(T) + P(T)) / T
  have hp'_chain : ∀ T ∈ V, deriv p (energyDensity P T) * deriv (energyDensity P) T = deriv P T := by
    intro T hT
    have hTp := hδ_sub hT
    have hev_T : (fun s => p (energyDensity P s)) =ᶠ[𝓝 T] P := by
      filter_upwards [hV_open.mem_nhds hT] with s hs; exact (hδ_sub hs).2.2.2.2
    have hd_e : HasDerivAt (energyDensity P) (deriv (energyDensity P) T) T := by
      have hE_an : AnalyticAt ℝ (energyDensity P) T :=
        (analyticAt_id.mul (hP_real_an T hTp.1).deriv).sub (hP_real_an T hTp.1)
      exact hE_an.differentiableAt.hasDerivAt
    have hd_p : HasDerivAt p (deriv p (energyDensity P T)) (energyDensity P T) :=
      ((hp_smooth.contDiffAt (hU.mem_nhds hTp.2.1)).differentiableAt (by simp)).hasDerivAt
    have hcomp := hd_p.comp T hd_e
    exact (hcomp.congr_of_eventuallyEq hev_T.symm).deriv.symm
  have hp'₁_ne : deriv p (energyDensity P T₁) ≠ 0 := by
    intro h0
    have h := hp'_chain T₁ hT₁_V
    rw [h0, zero_mul] at h
    exact hT₁_props.2.2.2.1 h.symm
  -- Also note n ≥ 1 (otherwise A depends only on e(T), contradicting e'(T₁) ≠ 0!)
  let v : Fin (n + 1) → ℝ → ℂ := fun i T => y i.val T
  let top : Fin (n + 1) := Fin.last n
  let g : Fin (n + 1) → ℝ → ℂ := fun i T => MvPolynomial.eval (fun j => v j T) (MvPolynomial.pderiv i A)
  let S : ℝ → ℂ := g top
  have hE_an_V : ∀ T ∈ V, AnalyticAt ℝ (energyDensity P) T := fun T hT =>
    (analyticAt_id.mul (hP_real_an T (hδ_sub hT).1).deriv).sub (hP_real_an T (hδ_sub hT).1)
  have hv_diff : ∀ T ∈ V, ∀ i : Fin (n + 1), DifferentiableAt ℝ (v i) T := by
    intro T hT i
    have hTp := hδ_sub hT
    rcases i with ⟨k, hk⟩
    cases k with
    | zero =>
      exact Complex.ofRealCLM.differentiableAt.comp T (hE_an_V T hT).differentiableAt
    | succ j =>
      have hpj : DifferentiableAt ℝ (iteratedDeriv j (fun e : ℝ => (p e : ℂ))) (energyDensity P T) :=
        ((contDiffOn_iteratedDeriv_top hU hpC_smooth j).contDiffAt (hU.mem_nhds hTp.2.1)).differentiableAt (by simp)
      exact hpj.comp T (hE_an_V T hT).differentiableAt
  have hv_deriv_succ : ∀ T ∈ V, ∀ j : ℕ,
      _root_.deriv (fun t => iteratedDeriv j (fun e : ℝ => (p e : ℂ)) (energyDensity P t)) T =
        iteratedDeriv (j + 1) (fun e : ℝ => (p e : ℂ)) (energyDensity P T) * ((deriv (energyDensity P) T : ℝ) : ℂ) := by
    intro T hT j
    have hTp := hδ_sub hT
    have hpj : HasDerivAt (iteratedDeriv j (fun e : ℝ => (p e : ℂ)))
        (iteratedDeriv (j + 1) (fun e : ℝ => (p e : ℂ)) (energyDensity P T)) (energyDensity P T) := by
      rw [iteratedDeriv_succ]
      exact (((contDiffOn_iteratedDeriv_top hU hpC_smooth j).contDiffAt
        (hU.mem_nhds hTp.2.1)).differentiableAt (by simp)).hasDerivAt
    have hcomp := hpj.scomp T (hE_an_V T hT).differentiableAt.hasDerivAt
    have hd : _root_.deriv ((iteratedDeriv j (fun e : ℝ => (p e : ℂ))) ∘ energyDensity P) T =
        ((deriv (energyDensity P) T : ℝ) : ℂ) * iteratedDeriv (j + 1) (fun e : ℝ => (p e : ℂ)) (energyDensity P T) := by
      simpa [Complex.real_smul] using hcomp.deriv
    simpa [Function.comp_def, mul_comm] using hd
  have hvanish : ∀ T ∈ V, ∑ i : Fin (n + 1), g i T * _root_.deriv (v i) T = 0 := by
    intro T hT
    have hchain := polynomial_chain A v (fun i => _root_.deriv (v i)) T (fun i => (hv_diff T hT i).hasDerivAt)
    have hnear : (fun t => MvPolynomial.eval (fun i => v i t) A) =ᶠ[𝓝 T] fun _ => 0 := by
      filter_upwards [hV_open.mem_nhds hT] with t ht; exact hA_zero t ht
    exact hchain.deriv.symm.trans (hnear.deriv_eq.trans (deriv_const _ _))
  have hn_pos : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hv0 := hvanish T₁ hT₁_V
    rw [Fin.sum_univ_one] at hv0
    have hd0 : _root_.deriv (v 0) T₁ = ((deriv (energyDensity P) T₁ : ℝ) : ℂ) :=
      ((hE_an_V T₁ hT₁_V).differentiableAt.hasDerivAt.ofReal_comp).deriv
    rw [hd0] at hv0
    exact mul_ne_zero hS₁_ne (Complex.ofReal_ne_zero.mpr hT₁_props.2.2.1) hv0
  let invT : ℝ → ℂ := fun T => (T : ℂ)⁻¹
  let invS : ℝ → ℂ := fun T => (S T)⁻¹
  let invDp : ℝ → ℂ := fun T => ((deriv p (energyDensity P T) : ℝ) : ℂ)⁻¹
  let uState : Fin (n + 1) ⊕ Fin 4 → ℝ → ℂ :=
    Sum.elim v ![(fun T => (T : ℂ)), invT, invS, invDp]
  let Gen := Generated uState T₁
  have gv (i : Fin (n + 1)) : Gen (v i) := Generated.coord (Sum.inl i)
  have gT : Gen (fun T => (T : ℂ)) := Generated.coord (Sum.inr 0)
  have ginvT : Gen invT := Generated.coord (Sum.inr 1)
  have ginvS : Gen invS := Generated.coord (Sum.inr 2)
  have ginvDp : Gen invDp := Generated.coord (Sum.inr 3)
  have gc (c : ℂ) : Gen (fun _ => c) := Generated.const c
  have gg (i : Fin (n + 1)) : Gen (g i) := Generated.evalPoly v gv _
  -- Check e'(T) = (e(T) + p(e(T))) / (T * p'(e(T))) lies in Gen!
  have gP : Gen (fun T => (P T : ℂ)) := by
    refine (gv ⟨1, by omega⟩).congr ?_
    filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
    change (iteratedDeriv 0 (fun e : ℝ => (p e : ℂ)) (energyDensity P T)) = (P T : ℂ)
    rw [iteratedDeriv_zero, (hδ_sub hT).2.2.2.2]
  have gE' : Gen (fun T => ((deriv (energyDensity P) T : ℝ) : ℂ)) := by
    refine (((gv 0).add gP).mul (ginvT.mul ginvDp)).congr ?_
    filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
    have hTp := hδ_sub hT
    have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hTp.1.ne'
    have hch := hp'_chain T hT
    have hdp_ne : ((deriv p (energyDensity P T) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have h0' : deriv p (energyDensity P T) = 0 := Complex.ofReal_eq_zero.mp h0
      rw [h0', zero_mul] at hch
      exact hTp.2.2.2.1 hch.symm
    have hEP : (energyDensity P T : ℂ) + (P T : ℂ) = (T : ℂ) * ((deriv P T : ℝ) : ℂ) := by
      unfold energyDensity; push_cast; ring
    have hchC : ((deriv p (energyDensity P T) : ℝ) : ℂ) * ((deriv (energyDensity P) T : ℝ) : ℂ) = ((deriv P T : ℝ) : ℂ) := by
      exact_mod_cast hch
    change ((energyDensity P T : ℂ) + (P T : ℂ)) * ((T : ℂ)⁻¹ * ((deriv p (energyDensity P T) : ℝ) : ℂ)⁻¹) =
      ((deriv (energyDensity P) T : ℝ) : ℂ)
    rw [hEP, ← hchC]
    field_simp [hTne, hdp_ne]
  -- Continuity / nonvanishing of S and p'(e(T)) near T₁
  have hS_diff_V : ∀ T ∈ V, DifferentiableAt ℝ S T := fun T hT =>
    (polynomial_chain (MvPolynomial.pderiv top A) v (fun i => _root_.deriv (v i)) T
      (fun i => (hv_diff T hT i).hasDerivAt)).differentiableAt
  have hSnz : ∀ᶠ T in 𝓝 T₁, S T ≠ 0 := (hS_diff_V T₁ hT₁_V).continuousAt.eventually_ne hS₁_ne
  have hDp_nz : ∀ᶠ T in 𝓝 T₁, deriv p (energyDensity P T) ≠ 0 := by
    filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
    intro h0; have h := hp'_chain T hT; rw [h0, zero_mul] at h; exact (hδ_sub hT).2.2.2.1 h.symm
  -- Derivatives of all v i lie in Gen!
  have low (i : Fin (n + 1)) (hi : i ≠ top) : Gen (_root_.deriv (v i)) := by
    rcases i with ⟨k, hk⟩
    cases k with
    | zero =>
      refine gE'.congr ?_
      filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
      exact (((hE_an_V T hT).differentiableAt.hasDerivAt.ofReal_comp).deriv).symm
    | succ j =>
      have hjlt : j + 2 < n + 1 := by
        have hne : j + 1 ≠ n := fun h => hi (Fin.ext h); omega
      refine ((gv ⟨j + 2, hjlt⟩).mul gE').congr ?_
      filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
      exact (hv_deriv_succ T hT j).symm
  let lowSum : ℝ → ℂ := ∑ i ∈ Finset.univ.erase top, g i * _root_.deriv (v i)
  have glowSum : Gen lowSum :=
    Generated.finsetSum _ _ fun i hi => (gg i).mul (low i (Finset.mem_erase.mp hi).1)
  have dv (i : Fin (n + 1)) : Gen (_root_.deriv (v i)) := by
    by_cases hi : i = top
    · subst i
      refine (((gc (-1)).mul glowSum).mul ginvS).congr ?_
      filter_upwards [hV_open.mem_nhds hT₁_V, hSnz] with T hT hST
      have hv0 := hvanish T hT
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at hv0
      have hh : S T * _root_.deriv (v top) T + lowSum T = 0 := by
        simpa [S, lowSum, Finset.sum_apply] using hv0
      change (-1 : ℂ) * lowSum T * (S T)⁻¹ = _root_.deriv (v top) T
      field_simp [hST]; linear_combination -hh
    · exact low i hi
  -- Now also deriv (fun T => (deriv p (energyDensity P T) : ℂ)) lies in Gen!
  -- Notice (deriv p (e(T)) : ℂ) = iteratedDeriv 1 (fun e => (p e : ℂ)) (e(T)) = y 2 T!
  -- Wait: if n = 1, y 2 T = (v 1)' / e' is ALREADY in Gen because v 1 = v top has dv top in Gen,
  -- wait: (v 1)' = y 2 * e', so we don't even need y 2 in v when n = 1? Wait: we DO need (y 2)' to close invDp!
  -- Look: (y 2) = (p'(e(T)) : ℂ) ALWAYS equals (P'(T) / e'(T)) = ((e(T) + P(T)) / (T * e'(T)))...
  -- WAIT: for n = 1, A(e, p(e)) = 0, so p(e) is ALGEBRAIC in e, meaning p'(e) = -(A_e / A_p) IS ALREADY in Gen
  -- (since g 0 = A_e, g 1 = S = A_p), AND therefore deriv(p'(e(T))) = deriv(-g 0 / S) IS ALREADY IN Gen!!
  -- And for n ≥ 2, y 2 = v ⟨2, _⟩ IS a coordinate of v, so deriv(y 2) = dv ⟨2, _⟩ IS ALREADY IN Gen!!
  have gDp_deriv : Gen (_root_.deriv (fun T => ((deriv p (energyDensity P T) : ℝ) : ℂ))) := by
    have heq_y2 : (fun T => ((deriv p (energyDensity P T) : ℝ) : ℂ)) =ᶠ[𝓝 T₁]
        fun T => iteratedDeriv 1 (fun e : ℝ => (p e : ℂ)) (energyDensity P T) := by
      filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
      have hTp := hδ_sub hT
      rw [iteratedDeriv_one]
      have hd := (((hp_smooth.contDiffAt (hU.mem_nhds hTp.2.1)).differentiableAt (by simp)).hasDerivAt.ofReal_comp).deriv
      exact hd.symm
    by_cases hn2 : 2 ≤ n
    · have h2 : (fun T => ((deriv p (energyDensity P T) : ℝ) : ℂ)) =ᶠ[𝓝 T₁] v ⟨2, by omega⟩ := heq_y2
      exact (dv ⟨2, by omega⟩).congr (h2.eventuallyEq_nhds.mono fun _ hy => hy.deriv_eq.symm)
    · have hn1 : n = 1 := by omega
      -- When n = 1: v 0 = e, v 1 = p(e), and g 0 * e' + S * (p'(e) * e') = 0 => p'(e) = -g 0 * S⁻¹!
      have hdS_local : Gen (_root_.deriv S) := by
        let D (i : Fin (n + 1)) (T : ℝ) :=
          MvPolynomial.eval (fun j => v j T) (MvPolynomial.pderiv i (MvPolynomial.pderiv top A))
        have hD (i) : Gen (D i) := Generated.evalPoly v gv _
        refine (Generated.finsetSum Finset.univ _ fun i _ => (hD i).mul (dv i)).congr ?_
        filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
        simpa [D, Finset.sum_apply] using
          (polynomial_chain (MvPolynomial.pderiv top A) v (fun i => _root_.deriv (v i)) T
            (fun i => (hv_diff T hT i).hasDerivAt)).deriv.symm
      have hdg0_local : Gen (_root_.deriv (g 0)) := by
        let D0 (i : Fin (n + 1)) (T : ℝ) :=
          MvPolynomial.eval (fun j => v j T) (MvPolynomial.pderiv i (MvPolynomial.pderiv 0 A))
        have hD0 (i) : Gen (D0 i) := Generated.evalPoly v gv _
        refine (Generated.finsetSum Finset.univ _ fun i _ => (hD0 i).mul (dv i)).congr ?_
        filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
        simpa [D0, Finset.sum_apply] using
          (polynomial_chain (MvPolynomial.pderiv 0 A) v (fun i => _root_.deriv (v i)) T
            (fun i => (hv_diff T hT i).hasDerivAt)).deriv.symm
      have hDp_eq_ratio : (fun T => ((deriv p (energyDensity P T) : ℝ) : ℂ)) =ᶠ[𝓝 T₁]
          fun T => -(g 0 T) * (S T)⁻¹ := by
        filter_upwards [hV_open.mem_nhds hT₁_V, hSnz, heq_y2] with T hT hST hy2
        have hv0 := hvanish T hT
        have htop_eq : top = ⟨1, by omega⟩ := Fin.ext (by simp [top, hn1])
        have hsum2 : g 0 T * _root_.deriv (v 0) T + S T * _root_.deriv (v top) T = 0 := by
          have huniv : (Finset.univ : Finset (Fin (n + 1))) = {0, top} := by
            ext i; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
            rcases i with ⟨k, hk⟩
            have : k = 0 ∨ k = 1 := by omega
            rcases this with rfl | rfl
            · left; exact Fin.ext rfl
            · right; exact Fin.ext (by simp [top, hn1])
          have hne0 : (0 : Fin (n + 1)) ≠ top := by
            intro h; have := congrArg Fin.val h; simp [top, hn1] at this
          rw [huniv, Finset.sum_pair hne0] at hv0
          exact hv0
        have hd0 : _root_.deriv (v 0) T = ((deriv (energyDensity P) T : ℝ) : ℂ) :=
          ((hE_an_V T hT).differentiableAt.hasDerivAt.ofReal_comp).deriv
        have hd1 : _root_.deriv (v top) T =
            ((deriv p (energyDensity P T) : ℝ) : ℂ) * ((deriv (energyDensity P) T : ℝ) : ℂ) := by
          have hvt : v top = fun t => iteratedDeriv 0 (fun e : ℝ => (p e : ℂ)) (energyDensity P t) := by
            funext t; simp [v, y, htop_eq]
          rw [hvt, hv_deriv_succ T hT 0, ← hy2]
        rw [hd0, hd1] at hsum2
        have hE'ne : ((deriv (energyDensity P) T : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (hδ_sub hT).2.2.1
        have hlin : g 0 T + S T * ((deriv p (energyDensity P T) : ℝ) : ℂ) = 0 := by
          apply mul_right_cancel₀ hE'ne
          linear_combination hsum2
        field_simp [hST]; linear_combination hlin
      have hderiv_ratio : Gen (_root_.deriv (fun T => -(g 0 T) * (S T)⁻¹)) := by
        refine ((((gc (-1)).mul hdg0_local).mul ginvS).add
          (((gg 0).mul hdS_local).mul (ginvS.pow 2))).congr ?_
        filter_upwards [hV_open.mem_nhds hT₁_V, hSnz] with T hT hST
        have hg0_d : DifferentiableAt ℝ (g 0) T :=
          (polynomial_chain (MvPolynomial.pderiv 0 A) v (fun i => _root_.deriv (v i)) T
            (fun i => (hv_diff T hT i).hasDerivAt)).differentiableAt
        have hS_d := hS_diff_V T hT
        have hprod := (hg0_d.hasDerivAt.neg).mul (hS_d.hasDerivAt.inv hST)
        have hfun : (fun t => -(g 0 t) * (S t)⁻¹) = (-(g 0)) * S⁻¹ := rfl
        change (-1 : ℂ) * _root_.deriv (g 0) T * (S T)⁻¹ + g 0 T * _root_.deriv S T * ((S T)⁻¹) ^ 2 =
          _root_.deriv (fun t => -(g 0 t) * (S t)⁻¹) T
        rw [hfun, hprod.deriv]; simp only [Pi.neg_apply, Pi.inv_apply]; field_simp [hST]
      exact hderiv_ratio.congr (hDp_eq_ratio.eventuallyEq_nhds.mono fun _ hy => hy.deriv_eq.symm)
  -- Smoothness and closure of uState near T₁
  have hdS : Gen (_root_.deriv S) := by
    let D (i : Fin (n + 1)) (T : ℝ) :=
      MvPolynomial.eval (fun j => v j T) (MvPolynomial.pderiv i (MvPolynomial.pderiv top A))
    have hD (i) : Gen (D i) := Generated.evalPoly v gv _
    refine (Generated.finsetSum Finset.univ _ fun i _ => (hD i).mul (dv i)).congr ?_
    filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
    simpa [D, Finset.sum_apply] using
      (polynomial_chain (MvPolynomial.pderiv top A) v (fun i => _root_.deriv (v i)) T
        (fun i => (hv_diff T hT i).hasDerivAt)).deriv.symm
  have hsmooth : ∀ᶠ T in 𝓝 T₁, ∀ i, DifferentiableAt ℝ (uState i) T := by
    filter_upwards [hV_open.mem_nhds hT₁_V, hSnz, hDp_nz] with T hT hST hDpT i
    have hTp := hδ_sub hT
    rcases i with i | i
    · exact hv_diff T hT i
    · fin_cases i
      · exact Complex.ofRealCLM.differentiableAt
      · exact Complex.ofRealCLM.differentiableAt.inv (Complex.ofReal_ne_zero.mpr hTp.1.ne')
      · exact (hS_diff_V T hT).inv hST
      · have hdp_d : DifferentiableAt ℝ (fun t => ((deriv p (energyDensity P t) : ℝ) : ℂ)) T := by
          have hd1 : DifferentiableAt ℝ (deriv p) (energyDensity P T) :=
            ((hp_smooth.deriv_of_isOpen hU (m := (1 : ℕ∞)) (by simp)).contDiffAt
              (hU.mem_nhds hTp.2.1)).differentiableAt one_ne_zero
          exact Complex.ofRealCLM.differentiableAt.comp T (hd1.comp T (hE_an_V T hT).differentiableAt)
        exact hdp_d.inv (Complex.ofReal_ne_zero.mpr hDpT)
  have hclosed : ∀ i, Gen (_root_.deriv (uState i)) := by
    intro i
    rcases i with i | i
    · exact dv i
    · fin_cases i
      · exact (gc 1).congr (Eventually.of_forall fun T => (Complex.ofRealCLM.hasDerivAt.deriv).symm)
      · refine ((gc (-1)).mul (ginvT.pow 2)).congr ?_
        filter_upwards [hV_open.mem_nhds hT₁_V] with T hT
        have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hδ_sub hT).1.ne'
        have hi := (Complex.ofRealCLM.hasDerivAt.inv hTne).deriv
        have hfun : (fun t : ℝ => (t : ℂ)⁻¹) = (⇑Complex.ofRealCLM)⁻¹ := rfl
        change (-1 : ℂ) * ((T : ℂ)⁻¹) ^ 2 = _root_.deriv (fun t : ℝ => (t : ℂ)⁻¹) T
        rw [hfun, hi]; simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; field_simp [hTne]
      · refine (((gc (-1)).mul hdS).mul (ginvS.pow 2)).congr ?_
        filter_upwards [hV_open.mem_nhds hT₁_V, hSnz] with T hT hST
        have hi := ((hS_diff_V T hT).hasDerivAt.inv hST).deriv
        have hfun : invS = S⁻¹ := rfl
        change (-1 : ℂ) * _root_.deriv S T * ((S T)⁻¹) ^ 2 = _root_.deriv invS T
        rw [hfun, hi]; field_simp [hST]
      · refine (((gc (-1)).mul gDp_deriv).mul (ginvDp.pow 2)).congr ?_
        filter_upwards [hV_open.mem_nhds hT₁_V, hDp_nz] with T hT hDpT
        have hTp := hδ_sub hT
        have hdp_d : DifferentiableAt ℝ (fun t => ((deriv p (energyDensity P t) : ℝ) : ℂ)) T := by
          have hd1 : DifferentiableAt ℝ (deriv p) (energyDensity P T) :=
            ((hp_smooth.deriv_of_isOpen hU (m := (1 : ℕ∞)) (by simp)).contDiffAt
              (hU.mem_nhds hTp.2.1)).differentiableAt one_ne_zero
          exact Complex.ofRealCLM.differentiableAt.comp T (hd1.comp T (hE_an_V T hT).differentiableAt)
        have hneC : ((deriv p (energyDensity P T) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hDpT
        have hi := (hdp_d.hasDerivAt.inv hneC).deriv
        have hfun : invDp = (fun t => ((deriv p (energyDensity P t) : ℝ) : ℂ))⁻¹ := rfl
        change (-1 : ℂ) * _root_.deriv (fun t => ((deriv p (energyDensity P t) : ℝ) : ℂ)) T *
          (((deriv p (energyDensity P T) : ℝ) : ℂ)⁻¹) ^ 2 = _root_.deriv invDp T
        rw [hfun, hi]; field_simp [hneC]
  -- Apply autonomous_readout to read out P(T) = p(e(T))!
  obtain ⟨R₀, hR₀_ne, hR₀_nhds⟩ := autonomous_readout uState T₁ (fun T => (P T : ℂ)) gP hsmooth hclosed
  -- Extend R₀ from 𝓝 T₁ to all of (0, ∞) by real-analyticity + Identity Theorem!
  let N := Fintype.card (Fin (n + 1) ⊕ Fin 4)
  let evalR₀ : ℝ → ℂ := fun T =>
    MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val (fun t : ℝ => (P t : ℂ)) T) R₀
  have heval_an : AnalyticOnNhd ℝ evalR₀ (Set.Ioi 0) := by
    intro T hT
    clear hR₀_ne hR₀_nhds
    dsimp only [evalR₀]
    induction R₀ using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add A B hA hB => simp only [map_add]; exact hA.add hB
    | mul_X A j hA =>
      have hjet : AnalyticAt ℝ (iteratedDeriv j.val (fun t : ℝ => (P t : ℂ))) T := by
        rw [iteratedDeriv_eq_iterate]
        exact (hP_an.iterated_deriv j.val) T hT
      simp only [map_mul, MvPolynomial.eval_X]
      exact hA.mul hjet
  have heval_zero : Set.EqOn evalR₀ 0 (Set.Ioi 0) :=
    heval_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Ioi hT₁_pos
      ((Filter.Eventually.filter_mono nhdsWithin_le_nhds hR₀_nhds).frequently)
  -- Lift constant-coefficient R₀ to MvPolynomial (Fin (N + 1)) (Polynomial ℂ) and contradict hP_no_ade!
  let R₀_poly : MvPolynomial (Fin (N + 1)) (Polynomial ℂ) := MvPolynomial.map Polynomial.C R₀
  have hR₀_poly_ne : R₀_poly ≠ 0 := by
    intro h0
    apply hR₀_ne
    ext α
    have := congrArg (fun M => M.coeff α) h0
    simpa [R₀_poly, MvPolynomial.coeff_map, Polynomial.C_eq_zero] using this
  have hR₀_poly_zero : ∀ T : ℝ, 0 < T →
      MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val (fun t : ℝ => (P t : ℂ)) T)
        (evalU R₀_poly (T : ℂ)) = 0 := by
    intro T hT
    have hev_id : evalU R₀_poly (T : ℂ) = R₀ := by
      dsimp only [evalU, R₀_poly]
      rw [MvPolynomial.map_map]
      have hcomp : (Polynomial.evalRingHom (T : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
        ext; simp
      rw [hcomp, MvPolynomial.map_id]
    rw [hev_id]
    exact heval_zero hT
  exact hR₀_poly_ne (hP_no_ade R₀_poly hR₀_poly_zero)

/-- **Sound-Speed Transfer**: If `p` satisfies no nonzero ADE over `ℂ(ε)` on an open set `U`,
then its derivative `soundSpeedSq p = deriv p` also satisfies no nonzero ADE over `ℂ(ε)` on `U`. -/
theorem soundSpeedSq_no_rat_ade_of_eos {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    (hp_no_ade : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U,
        (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) →
      R = 0) :
    ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U,
        (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) →
      R = 0 := by
  intro r R hR
  let shift : Fin (r + 1) → Fin (r + 2) := Fin.succ
  let R' : MvPolynomial (Fin (r + 2)) (RatFunc ℂ) := MvPolynomial.rename shift R
  have hshift_inj : Function.Injective shift := Fin.succ_injective _
  have hR'_zero : R' = 0 := by
    refine hp_no_ade R' fun ε hε hden => ?_
    have hden_R : ∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0 := by
      intro β hβ
      let γ := Finsupp.mapDomain shift β
      have hcoeff : R'.coeff γ = R.coeff β := MvPolynomial.coeff_rename_mapDomain shift hshift_inj R β
      have hγ : γ ∈ R'.support := by
        rw [MvPolynomial.mem_support_iff, hcoeff]
        exact MvPolynomial.mem_support_iff.mp hβ
      rw [← hcoeff]
      exact hden γ hγ
    have hmap_eval : evalRatU R' (ε : ℂ) = MvPolynomial.rename shift (evalRatU R (ε : ℂ)) := by
      classical
      ext γ
      rw [evalRatU, MvPolynomial.coeff_sum]
      simp_rw [MvPolynomial.coeff_monomial]
      have hrhs : (MvPolynomial.rename shift (evalRatU R (ε : ℂ))).coeff γ =
          ∑ β ∈ R.support, if Finsupp.mapDomain shift β = γ then ratEval (R.coeff β) (ε : ℂ) else 0 := by
        rw [evalRatU, map_sum, MvPolynomial.coeff_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
      rw [hrhs]
      have hsupp : R'.support = R.support.image (Finsupp.mapDomain shift) := by
        ext α
        simp only [MvPolynomial.mem_support_iff, Finset.mem_image]
        constructor
        · intro hα
          -- R' = rename shift R = ∑ β ∈ R.support, monomial (mapDomain shift β) (R.coeff β)
          have hsum_R' : R' = ∑ β ∈ R.support, MvPolynomial.monomial (Finsupp.mapDomain shift β) (R.coeff β) := by
            dsimp only [R']
            conv_lhs => rw [R.as_sum]
            rw [map_sum]
            refine Finset.sum_congr rfl fun β _ => MvPolynomial.rename_monomial shift β (R.coeff β)
          rw [hsum_R', MvPolynomial.coeff_sum] at hα
          obtain ⟨β, hβ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
          rw [MvPolynomial.coeff_monomial] at hne
          split_ifs at hne with h
          · exact ⟨β, MvPolynomial.mem_support_iff.mp hβ, h⟩
          · exact absurd rfl hne
        · rintro ⟨β, hβ, rfl⟩
          rw [MvPolynomial.coeff_rename_mapDomain shift hshift_inj R β]
          exact hβ
      rw [hsupp, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hshift_inj h)]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [MvPolynomial.coeff_rename_mapDomain shift hshift_inj R β]
    rw [hmap_eval, MvPolynomial.eval_rename]
    have hjet : (fun j : Fin (r + 1) => iteratedDeriv (shift j).val (fun e : ℝ => (p e : ℂ)) ε) =
        fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε := by
      ext j
      change iteratedDeriv (j.val + 1) (fun e : ℝ => (p e : ℂ)) ε =
        iteratedDeriv j.val (fun e : ℝ => ((deriv p e : ℝ) : ℂ)) ε
      rw [iteratedDeriv_succ']
      have hev : deriv (fun e : ℝ => (p e : ℂ)) =ᶠ[𝓝 ε] fun e : ℝ => ((deriv p e : ℝ) : ℂ) := by
        filter_upwards [hU.mem_nhds hε] with e he
        exact (((hp_smooth.contDiffAt (hU.mem_nhds he)).differentiableAt (by simp)).hasDerivAt.ofReal_comp).deriv
      exact Filter.EventuallyEq.iteratedDeriv_eq j.val hev
    rw [show (fun x => iteratedDeriv x.val (fun e : ℝ => (p e : ℂ)) ε) ∘ shift =
        fun j : Fin (r + 1) => iteratedDeriv (shift j).val (fun e : ℝ => (p e : ℂ)) ε from rfl, hjet]
    exact hR ε hε hden_R
  exact MvPolynomial.rename_injective shift hshift_inj (by simpa [R'] using hR'_zero)

/-- **1D Relativistic Bose Equation-of-State & Sound-Speed Differential Transcendence over `ℂ(ε)`**:
For every positive mass `m > 0`, any smooth local or global equation of state `p(ε)` matching
`p(ε(T)) = bosePressure1D m T` near some `T₀ > 0`, as well as its sound speed squared
`c_s²(ε) = p'(ε)`, satisfies NO nonzero algebraic differential equation over `ℂ(ε)`. -/
theorem boseEOS1D_no_rat_ade {m : ℝ} (hm : 0 < m)
    {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hE₀_mem : energyDensity (bosePressure1D m) T₀ ∈ U)
    (heos : ∀ᶠ T in 𝓝 T₀, p (energyDensity (bosePressure1D m) T) = bosePressure1D m T) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) := by
  have hpos := bosePressure1D_thermodynamic_pos hm hT₀
  have hp_no : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0 :=
    eos_no_rat_ade_of_pressure (bosePressure1D_analyticOnNhd hm)
      (fun Q hQ => bosePressure1D_no_ade hm Q hQ) hU hp_smooth hT₀ hE₀_mem hpos.1.ne' hpos.2.2.ne' heos
  exact ⟨hp_no, soundSpeedSq_no_rat_ade_of_eos hU hp_smooth hp_no⟩

/-- **3D Relativistic Bose Equation-of-State & Sound-Speed Differential Transcendence over `ℂ(ε)`**:
For every positive mass `m > 0`, any smooth local or global equation of state `p(ε)` matching
`p(ε(T)) = bosePressure3D m T` near some `T₀ > 0`, as well as its sound speed squared
`c_s²(ε) = p'(ε)`, satisfies NO nonzero algebraic differential equation over `ℂ(ε)`. -/
theorem boseEOS3D_no_rat_ade {m : ℝ} (hm : 0 < m)
    {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hE₀_mem : energyDensity (bosePressure3D m) T₀ ∈ U)
    (heos : ∀ᶠ T in 𝓝 T₀, p (energyDensity (bosePressure3D m) T) = bosePressure3D m T) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) := by
  have hpos := bosePressure3D_thermodynamic_pos hm hT₀
  have hp_no : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0 :=
    eos_no_rat_ade_of_pressure (bosePressure3D_analyticOnNhd hm)
      (fun Q hQ => bosePressure3D_no_ade hm Q hQ) hU hp_smooth hT₀ hE₀_mem hpos.1.ne' hpos.2.2.ne' heos
  exact ⟨hp_no, soundSpeedSq_no_rat_ade_of_eos hU hp_smooth hp_no⟩

/-- **1D Relativistic Fermi Equation-of-State & Sound-Speed Differential Transcendence over `ℂ(ε)`**:
For every positive mass `m > 0`, any smooth local or global equation of state `p(ε)` matching
`p(ε(T)) = fermiPressure1D m T` near some `T₀ > 0`, as well as its sound speed squared
`c_s²(ε) = p'(ε)`, satisfies NO nonzero algebraic differential equation over `ℂ(ε)`. -/
theorem fermiEOS1D_no_rat_ade {m : ℝ} (hm : 0 < m)
    {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hE₀_mem : energyDensity (fermiPressure1D m) T₀ ∈ U)
    (heos : ∀ᶠ T in 𝓝 T₀, p (energyDensity (fermiPressure1D m) T) = fermiPressure1D m T) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) := by
  have hpos := fermiPressure1D_thermodynamic_pos hm hT₀
  have hp_no : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0 :=
    eos_no_rat_ade_of_pressure (fermiPressure1D_analyticOnNhd hm)
      (fun Q hQ => fermiPressure1D_no_ade hm Q hQ) hU hp_smooth hT₀ hE₀_mem hpos.1.ne' hpos.2.2.ne' heos
  exact ⟨hp_no, soundSpeedSq_no_rat_ade_of_eos hU hp_smooth hp_no⟩

/-- **3D Relativistic Fermi Equation-of-State & Sound-Speed Differential Transcendence over `ℂ(ε)`**:
For every positive mass `m > 0`, any smooth local or global equation of state `p(ε)` matching
`p(ε(T)) = fermiPressure3D m T` near some `T₀ > 0`, as well as its sound speed squared
`c_s²(ε) = p'(ε)`, satisfies NO nonzero algebraic differential equation over `ℂ(ε)`. -/
theorem fermiEOS3D_no_rat_ade {m : ℝ} (hm : 0 < m)
    {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hE₀_mem : energyDensity (fermiPressure3D m) T₀ ∈ U)
    (heos : ∀ᶠ T in 𝓝 T₀, p (energyDensity (fermiPressure3D m) T) = fermiPressure3D m T) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) := by
  have hpos := fermiPressure3D_thermodynamic_pos hm hT₀
  have hp_no : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0 :=
    eos_no_rat_ade_of_pressure (fermiPressure3D_analyticOnNhd hm)
      (fun Q hQ => fermiPressure3D_no_ade hm Q hQ) hU hp_smooth hT₀ hE₀_mem hpos.1.ne' hpos.2.2.ne' heos
  exact ⟨hp_no, soundSpeedSq_no_rat_ade_of_eos hU hp_smooth hp_no⟩

/-! ### 3. Massive Parallel-Plate Casimir Energy & Force Dimensional-Parity Theorem (`d = 2` vs `d = 1, 3`) -/

private lemma iteratedDeriv_ofReal_comp_eos (f : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (f t : ℂ)) x = ((iteratedDeriv k f x : ℝ) : ℂ) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun t : ℝ => (f t : ℂ)) =
        fun t : ℝ => ((iteratedDeriv k f t : ℝ) : ℂ) := funext ih
    rw [heq]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv k f) x
    · exact (hd.hasDerivAt.ofReal_comp).deriv
    · have hnd : ¬ DifferentiableAt ℝ (fun t : ℝ => ((iteratedDeriv k f t : ℝ) : ℂ)) x := by
        intro hc
        have hr : DifferentiableAt ℝ (fun t : ℝ => Complex.reCLM ((iteratedDeriv k f t : ℝ) : ℂ)) x :=
          DifferentiableAt.comp x Complex.reCLM.differentiableAt hc
        exact hd (by simpa using hr)
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, Complex.ofReal_zero]

/-- Renormalized massive parallel-plate (Dirichlet–Dirichlet) Casimir energy per unit area
via exact Thermal–Casimir duality `E_C(L) = -L · P(1 / (2L))`. -/
@[expose] def casimirEnergy (P : ℝ → ℝ) (L : ℝ) : ℝ :=
  -L * P (1 / (2 * L))

/-- Massive parallel-plate Casimir force per unit area `F_C(L) = -∂_L E_C(L)`. -/
@[expose] def casimirForce (P : ℝ → ℝ) (L : ℝ) : ℝ :=
  -deriv (casimirEnergy P) L

@[expose] def casimirEnergy1D (m L : ℝ) : ℝ := casimirEnergy (bosePressure1D m) L
@[expose] def casimirEnergy2D (m L : ℝ) : ℝ := casimirEnergy (bosePressure2D m) L
@[expose] def casimirEnergy3D (m L : ℝ) : ℝ := casimirEnergy (bosePressure3D m) L
@[expose] def casimirForce1D (m L : ℝ) : ℝ := casimirForce (bosePressure1D m) L
@[expose] def casimirForce2D (m L : ℝ) : ℝ := casimirForce (bosePressure2D m) L
@[expose] def casimirForce3D (m L : ℝ) : ℝ := casimirForce (bosePressure3D m) L

/-- **Exact Casimir Force – Thermal Energy-Density Duality**:
`F_C(L) = -ε(1 / (2L))` for every `L > 0` where `P` is differentiable at `1 / (2L)`. -/
theorem casimirForce_eq_neg_energyDensity {P : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hP : DifferentiableAt ℝ P (1 / (2 * L))) :
    casimirForce P L = -energyDensity P (1 / (2 * L)) := by
  have hinv : HasDerivAt (fun l : ℝ => 1 / (2 * l)) (-1 / (2 * L ^ 2)) L := by
    have h1 := ((hasDerivAt_id L).const_mul (2 : ℝ)).inv (by positivity : (2 : ℝ) * L ≠ 0)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun l => by simp [one_div]) |>.congr_deriv ?_
    simp only [id_eq]; field_simp [hL.ne']
  have hcomp : HasDerivAt (fun l : ℝ => P (1 / (2 * l)))
      (deriv P (1 / (2 * L)) * (-1 / (2 * L ^ 2))) L :=
    hP.hasDerivAt.comp L hinv
  have hprod : HasDerivAt (casimirEnergy P)
      ((-1 : ℝ) * P (1 / (2 * L)) + (-L) * (deriv P (1 / (2 * L)) * (-1 / (2 * L ^ 2)))) L := by
    have h0 := ((hasDerivAt_id L).neg).mul hcomp
    refine h0.congr_of_eventuallyEq (Eventually.of_forall fun l => ?_) |>.congr_deriv ?_
    · unfold casimirEnergy; simp
    · simp
  unfold casimirForce energyDensity
  rw [hprod.deriv]
  field_simp [hL.ne']; ring

/-- Real-analyticity of `bosePressure2D m` on `(0, ∞)` via complex holomorphic extension
to the open right half-plane `{Re z > 0}`. -/
theorem bosePressure2D_analyticOnNhd {m : ℝ} (hm : 0 < m) :
    AnalyticOnNhd ℝ (fun T : ℝ => (bosePressure2D m T : ℂ)) (Set.Ioi 0) := by
  let term : ℕ → ℂ → ℂ := fun k z =>
    (1 + (((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z) / (((k : ℝ) + 1 : ℝ) : ℂ) ^ 3 *
      Complex.exp (-((((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z))
  let F : ℂ → ℂ := fun z => z ^ 3 / (2 * (Real.pi : ℂ)) * ∑' k : ℕ, term k z
  have hF_diff : DifferentiableOn ℂ F rightHalfPlane := by
    have hsum_diff : DifferentiableOn ℂ (fun z => ∑' k : ℕ, term k z) rightHalfPlane := by
      intro z₀ hz₀
      have hz₀_re : 0 < z₀.re := mem_rightHalfPlane.mp hz₀
      let r : ℝ := z₀.re / 2
      have hr : 0 < r := by positivity
      let R : ℝ := ‖z₀‖ + r
      have hR : 0 < R := by
        have h0 : 0 ≤ ‖z₀‖ := norm_nonneg z₀; linarith
      let δ : ℝ := m * r / R ^ 2
      have hδ : 0 < δ := by positivity
      have hball_props : ∀ z ∈ Metric.ball z₀ r,
          r < z.re ∧ ‖z‖ ≤ R ∧ z ≠ 0 ∧ δ ≤ ((m : ℂ) / z).re := by
        intro z hz
        have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        have hre_diff : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
          simpa using Complex.abs_re_le_norm (z - z₀)
        have hre_gt : r < z.re := by
          have h1 := (abs_le.mp hre_diff).1
          dsimp only [r] at hdist ⊢; linarith
        have hnorm_le : ‖z‖ ≤ R := by
          calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by ring_nf
            _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
            _ ≤ ‖z₀‖ + r := by linarith
        have hzne : z ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hre_gt; linarith
        have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
        have hre_div : ((m : ℂ) / z).re = m * z.re / ‖z‖ ^ 2 := by
          rw [div_eq_mul_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.inv_re, Complex.normSq_eq_norm_sq, div_eq_mul_inv]
          ring
        have hre_ge : δ ≤ ((m : ℂ) / z).re := by
          rw [hre_div]
          have hz_re_pos : 0 < z.re := lt_trans hr hre_gt
          have hnum : m * r ≤ m * z.re := mul_le_mul_of_nonneg_left hre_gt.le hm.le
          have hden : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hnorm_pos.le hnorm_le 2
          calc m * r / R ^ 2 ≤ m * z.re / R ^ 2 :=
                div_le_div_of_nonneg_right hnum (sq_nonneg R)
            _ ≤ m * z.re / ‖z‖ ^ 2 :=
                div_le_div_of_nonneg_left (mul_nonneg hm.le hz_re_pos.le) (sq_pos_of_pos hnorm_pos) hden
        exact ⟨hre_gt, hnorm_le, hzne, hre_ge⟩
      let M : ℝ := 1 + m / r
      have hM : 0 < M := by positivity
      have hsumm : Summable (fun k : ℕ => M * ((k : ℝ) + 1) * Real.exp (-(((k : ℝ) + 1) * δ))) := by
        have hr_lt : ‖Real.exp (-δ)‖ < 1 := by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]
          exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ)
        have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hr_lt).comp_injective Nat.succ_injective
        refine (h1.mul_left M).congr fun k => ?_
        simp only [Function.comp_apply, pow_one, ← Real.exp_nat_mul]
        rw [Nat.cast_succ, ← mul_assoc]
        congr 2; ring
      have hdiff_ball : DifferentiableOn ℂ (fun z => ∑' k : ℕ, term k z) (Metric.ball z₀ r) := by
        refine Complex.differentiableOn_tsum_of_summable_norm hsumm (fun k => ?_) Metric.isOpen_ball ?_
        · intro z hz
          have hzne := (hball_props z hz).2.2.1
          have hinv : DifferentiableAt ℂ (fun w : ℂ => (((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / w) z :=
            (differentiableAt_const _).div differentiableAt_id hzne
          exact (((differentiableAt_const _).add hinv).div_const _).mul
            (Complex.differentiable_exp.differentiableAt.comp z hinv.neg) |>.differentiableWithinAt
        · intro k z hz
          obtain ⟨hre_gt, _, hzne, hre_ge⟩ := hball_props z hz
          have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
          have hnorm_z : r ≤ ‖z‖ := hre_gt.le.trans (Complex.re_le_norm z)
          have hpre : ‖(1 + (((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z) / (((k : ℝ) + 1 : ℝ) : ℂ) ^ 3‖ ≤
              M * ((k : ℝ) + 1) := by
            have hnum : ‖(1 : ℂ) + (((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z‖ ≤ M * ((k : ℝ) + 1) := by
              calc ‖(1 : ℂ) + (((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z‖
                  ≤ ‖(1 : ℂ)‖ + ‖(((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z‖ := norm_add_le _ _
                _ = 1 + ((k : ℝ) + 1) * m / ‖z‖ := by
                    rw [norm_one, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
                      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hm.le]
                _ ≤ 1 + ((k : ℝ) + 1) * m / r := by
                    gcongr
                _ ≤ ((k : ℝ) + 1) + ((k : ℝ) + 1) * (m / r) := by
                    rw [mul_div_assoc]; linarith
                _ = M * ((k : ℝ) + 1) := by dsimp only [M]; ring
            have hden : (1 : ℝ) ≤ ‖(((k : ℝ) + 1 : ℝ) : ℂ) ^ 3‖ := by
              rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
              exact one_le_pow₀ hk1
            rw [norm_div]
            exact (div_le_self (norm_nonneg _) hden).trans hnum
          have hexp : ‖Complex.exp (-((((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z))‖ ≤
              Real.exp (-(((k : ℝ) + 1) * δ)) := by
            rw [Complex.norm_exp]
            apply Real.exp_le_exp.mpr
            have hre_arg : (-((((k : ℝ) + 1 : ℝ) : ℂ) * (m : ℂ) / z)).re =
                -((k : ℝ) + 1) * ((m : ℂ) / z).re := by
              rw [mul_div_assoc, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
                Complex.ofReal_im, zero_mul, sub_zero]
              ring
            rw [hre_arg]
            nlinarith
          dsimp only [term]
          rw [norm_mul]
          exact mul_le_mul hpre hexp (norm_nonneg _) (by positivity)
      exact (hdiff_ball.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt
    exact ((differentiableOn_id.pow 3).div_const _).mul hsum_diff
  have hF_eq : ∀ T : ℝ, 0 < T → (bosePressure2D m T : ℂ) = F (T : ℂ) := by
    intro T hT
    dsimp only [bosePressure2D, F, term]
    push_cast
    rfl
  exact analyticOnNhd_of_holomorphic_rightHalfPlane hF_diff hF_eq

/-- Explicit order-2 quadratic differential polynomial over `ℂ[L]` satisfied by the
2D massive parallel-plate Casimir force `F_C^{(2D)}(L)`:
`m² L Y₂ + 4 m² Y₁ + 2 m³ (L Y₁ + 3 Y₀) + 4π (L Y₁ + 3 Y₀)² = 0`. -/
@[expose] def casimirForce2DPoly (m : ℂ) : MvPolynomial (Fin 3) (Polynomial ℂ) :=
  let L : Polynomial ℂ := Polynomial.X
  let Q : MvPolynomial (Fin 3) (Polynomial ℂ) := C L * X 1 + C 3 * X 0
  C (Polynomial.C (m ^ 2) * L) * X 2 + C (Polynomial.C (4 * m ^ 2)) * X 1 +
    C (Polynomial.C (2 * m ^ 3)) * Q + C (Polynomial.C (4 * (Real.pi : ℂ))) * Q ^ 2

theorem casimirForce2DPoly_ne_zero {m : ℝ} (hm : 0 < m) :
    casimirForce2DPoly (m : ℂ) ≠ 0 := by
  intro h0
  have hev := congrArg (fun P => MvPolynomial.eval (fun j : Fin 3 => if j = 2 then (1 : ℂ) else 0)
    (evalU P (1 : ℂ))) h0
  simp only [casimirForce2DPoly, evalU, map_zero, map_add, map_mul, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, ↓reduceIte,
    Fin.reduceEq, mul_one, mul_zero, add_zero, zero_pow two_ne_zero] at hev
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hm.ne') hev

/-- Explicit order-3 quadratic differential polynomial over `ℂ[L]` satisfied by the
2D massive parallel-plate Casimir energy `E_C^{(2D)}(L)` (obtained by substituting `F = -E'`). -/
@[expose] def casimirEnergy2DPoly (m : ℂ) : MvPolynomial (Fin 4) (Polynomial ℂ) :=
  let L : Polynomial ℂ := Polynomial.X
  let Q : MvPolynomial (Fin 4) (Polynomial ℂ) := -(C L * X 2 + C 3 * X 1)
  (0 : MvPolynomial (Fin 4) (Polynomial ℂ)) - C (Polynomial.C (m ^ 2) * L) * X 3 -
    C (Polynomial.C (4 * m ^ 2)) * X 2 +
    C (Polynomial.C (2 * m ^ 3)) * Q + C (Polynomial.C (4 * (Real.pi : ℂ))) * Q ^ 2

theorem casimirEnergy2DPoly_ne_zero {m : ℝ} (hm : 0 < m) :
    casimirEnergy2DPoly (m : ℂ) ≠ 0 := by
  intro h0
  have hev := congrArg (fun P => MvPolynomial.eval (fun j : Fin 4 => if j = 3 then (1 : ℂ) else 0)
    (evalU P (1 : ℂ))) h0
  simp only [casimirEnergy2DPoly, evalU, map_zero, map_sub, map_add, map_neg, map_mul, map_pow,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    ↓reduceIte, Fin.reduceEq, mul_one, mul_zero, add_zero, zero_sub, sub_zero, neg_zero,
    zero_pow two_ne_zero, neg_eq_zero] at hev
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hm.ne') hev

/-- Key closed-form geometric-series identity for the 2D massive Casimir energy:
`L · E''(L) + 3 · E'(L) = -(m³ / (2π)) · e^{-2mL} / (1 - e^{-2mL})`. -/
private lemma casimirEnergy2D_Q_eq {m L : ℝ} (hm : 0 < m) (hL : 0 < L) :
    L * iteratedDeriv 2 (casimirEnergy2D m) L + 3 * iteratedDeriv 1 (casimirEnergy2D m) L =
      -(m ^ 3 / (2 * Real.pi)) * (Real.exp (-(2 * m * L)) / (1 - Real.exp (-(2 * m * L)))) := by
  let g0 : ℕ → ℝ → ℝ := fun k x =>
    (x⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 3 + 2 * m * x⁻¹ / ((k : ℝ) + 1) ^ 2) *
      Real.exp (-(2 * ((k : ℝ) + 1) * m * x))
  let g1 : ℕ → ℝ → ℝ := fun k x =>
    (-2 * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 3 - 4 * m * x⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 2 -
      4 * m ^ 2 * x⁻¹ / ((k : ℝ) + 1)) * Real.exp (-(2 * ((k : ℝ) + 1) * m * x))
  let g2 : ℕ → ℝ → ℝ := fun k x =>
    (6 * x⁻¹ ^ 4 / ((k : ℝ) + 1) ^ 3 + 12 * m * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 2 +
      12 * m ^ 2 * x⁻¹ ^ 2 / ((k : ℝ) + 1) + 8 * m ^ 3 * x⁻¹) *
      Real.exp (-(2 * ((k : ℝ) + 1) * m * x))
  have hE_eq : ∀ x : ℝ, 0 < x → casimirEnergy2D m x = -(1 / (16 * Real.pi)) * ∑' k : ℕ, g0 k x := by
    intro x hx
    unfold casimirEnergy2D casimirEnergy bosePressure2D
    have hterm : ∀ k : ℕ, (1 + ((k : ℝ) + 1) * m / (1 / (2 * x))) / ((k : ℝ) + 1) ^ 3 *
        Real.exp (-(((k : ℝ) + 1) * m / (1 / (2 * x)))) = x ^ 2 * g0 k x := fun k => by
      dsimp only [g0]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hexp : -(((k : ℝ) + 1) * m / (1 / (2 * x))) = -(2 * ((k : ℝ) + 1) * m * x) := by
        field_simp [hx.ne']
      rw [hexp]; field_simp [hx.ne', hk1]
    simp_rw [hterm, tsum_mul_left]
    field_simp [hx.ne']; ring
  have hg0_deriv : ∀ (k : ℕ) {x : ℝ}, 0 < x → HasDerivAt (g0 k) (g1 k x) x := by
    intro k x hx
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hinv1 : HasDerivAt (fun y : ℝ => y⁻¹) (-x⁻¹ ^ 2) x :=
      (hasDerivAt_inv hx.ne').congr_deriv (by rw [inv_pow])
    have hinv2 : HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) x := by
      have h := hinv1.pow 2
      refine h.congr_deriv ?_; norm_num; ring
    have hpre : HasDerivAt (fun y : ℝ => y⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 3 + 2 * m * y⁻¹ / ((k : ℝ) + 1) ^ 2)
        ((-2 * x⁻¹ ^ 3) / ((k : ℝ) + 1) ^ 3 + 2 * m * (-x⁻¹ ^ 2) / ((k : ℝ) + 1) ^ 2) x :=
      (hinv2.div_const _).add ((hinv1.const_mul (2 * m)).div_const _)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(2 * ((k : ℝ) + 1) * m * y)))
        (Real.exp (-(2 * ((k : ℝ) + 1) * m * x)) * (-(2 * ((k : ℝ) + 1) * m))) x := by
      have hlin : HasDerivAt (fun y : ℝ => -(2 * ((k : ℝ) + 1) * m * y)) (-(2 * ((k : ℝ) + 1) * m)) x := by
        have h := (hasDerivAt_id x).const_mul (-(2 * ((k : ℝ) + 1) * m))
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp) |>.congr_deriv ?_
        ring
      exact hlin.exp
    refine (hpre.mul hexp).congr_deriv ?_
    dsimp only [g1]; field_simp [hx.ne', hk1]; ring
  have hg1_deriv : ∀ (k : ℕ) {x : ℝ}, 0 < x → HasDerivAt (g1 k) (g2 k x) x := by
    intro k x hx
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hinv1 : HasDerivAt (fun y : ℝ => y⁻¹) (-x⁻¹ ^ 2) x :=
      (hasDerivAt_inv hx.ne').congr_deriv (by rw [inv_pow])
    have hinv2 : HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) x := by
      have h := hinv1.pow 2
      refine h.congr_deriv ?_; norm_num; ring
    have hinv3 : HasDerivAt (fun y : ℝ => y⁻¹ ^ 3) (-3 * x⁻¹ ^ 4) x := by
      have h := hinv1.pow 3
      refine h.congr_deriv ?_; norm_num; ring
    have hpre : HasDerivAt (fun y : ℝ =>
        -2 * y⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 3 - 4 * m * y⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 2 -
          4 * m ^ 2 * y⁻¹ / ((k : ℝ) + 1))
        (-2 * (-3 * x⁻¹ ^ 4) / ((k : ℝ) + 1) ^ 3 - 4 * m * (-2 * x⁻¹ ^ 3) / ((k : ℝ) + 1) ^ 2 -
          4 * m ^ 2 * (-x⁻¹ ^ 2) / ((k : ℝ) + 1)) x :=
      (((hinv3.const_mul (-2)).div_const _).sub ((hinv2.const_mul (4 * m)).div_const _)).sub
        ((hinv1.const_mul (4 * m ^ 2)).div_const _)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(2 * ((k : ℝ) + 1) * m * y)))
        (Real.exp (-(2 * ((k : ℝ) + 1) * m * x)) * (-(2 * ((k : ℝ) + 1) * m))) x := by
      have hlin : HasDerivAt (fun y : ℝ => -(2 * ((k : ℝ) + 1) * m * y)) (-(2 * ((k : ℝ) + 1) * m)) x := by
        have h := (hasDerivAt_id x).const_mul (-(2 * ((k : ℝ) + 1) * m))
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp) |>.congr_deriv ?_
        ring
      exact hlin.exp
    refine (hpre.mul hexp).congr_deriv ?_
    dsimp only [g2]; field_simp [hx.ne', hk1]; ring
  let a : ℝ := L / 2
  have ha : 0 < a := by positivity
  have hL_mem : L ∈ Set.Ioi a := by change L / 2 < L; linarith
  have hgeom : Summable (fun k : ℕ => Real.exp (-(((k : ℝ) + 1) * (2 * m * a)))) := by
    have hr : 0 < Real.exp (-(2 * m * a)) := Real.exp_pos _
    have h2ma : 0 < 2 * m * a := by positivity
    have hr1 : Real.exp (-(2 * m * a)) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr h2ma)
    have h1 := (summable_geometric_of_lt_one hr.le hr1).comp_injective Nat.succ_injective
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have hexp_le : ∀ (k : ℕ) {x : ℝ}, x ∈ Set.Ioi a →
      Real.exp (-(2 * ((k : ℝ) + 1) * m * x)) ≤ Real.exp (-(((k : ℝ) + 1) * (2 * m * a))) := by
    intro k x hx
    apply Real.exp_le_exp.mpr
    have hxa : a < x := hx
    have hpos : 0 < 2 * ((k : ℝ) + 1) * m := by positivity
    have hmul : 2 * ((k : ℝ) + 1) * m * a < 2 * ((k : ℝ) + 1) * m * x :=
      mul_lt_mul_of_pos_left hxa hpos
    linarith
  let C1 : ℝ := 2 * a⁻¹ ^ 3 + 4 * m * a⁻¹ ^ 2 + 4 * m ^ 2 * a⁻¹
  let C2 : ℝ := 6 * a⁻¹ ^ 4 + 12 * m * a⁻¹ ^ 3 + 12 * m ^ 2 * a⁻¹ ^ 2 + 8 * m ^ 3 * a⁻¹
  have hg0_summ : Summable (fun k : ℕ => g0 k L) := by
    refine (hgeom.mul_left (a⁻¹ ^ 2 + 2 * m * a⁻¹)).of_norm_bounded fun k => ?_
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hinv_le : L⁻¹ ≤ a⁻¹ := inv_anti₀ ha (by dsimp only [a]; linarith)
    dsimp only [g0]
    rw [Real.norm_of_nonneg (by positivity)]
    have hpre : L⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 3 + 2 * m * L⁻¹ / ((k : ℝ) + 1) ^ 2 ≤ a⁻¹ ^ 2 + 2 * m * a⁻¹ := by
      have h1 : L⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 3 ≤ a⁻¹ ^ 2 :=
        (div_le_self (by positivity) (one_le_pow₀ hk1)).trans (pow_le_pow_left₀ (by positivity) hinv_le 2)
      have h2 : 2 * m * L⁻¹ / ((k : ℝ) + 1) ^ 2 ≤ 2 * m * a⁻¹ :=
        (div_le_self (by positivity) (one_le_pow₀ hk1)).trans (by nlinarith)
      linarith
    exact mul_le_mul hpre (hexp_le k hL_mem) (Real.exp_pos _).le (by positivity)
  have hg1_bd : ∀ (k : ℕ) (x : ℝ), x ∈ Set.Ioi a → ‖g1 k x‖ ≤ C1 * Real.exp (-(((k : ℝ) + 1) * (2 * m * a))) := by
    intro k x hx
    have hxa : a < x := hx
    have hx_pos : 0 < x := lt_trans ha hxa
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hinv_le : x⁻¹ ≤ a⁻¹ := inv_anti₀ ha hxa.le
    dsimp only [g1]
    have hrew : -2 * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 3 - 4 * m * x⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 2 -
        4 * m ^ 2 * x⁻¹ / ((k : ℝ) + 1) =
        -(2 * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 3 + 4 * m * x⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 2 +
          4 * m ^ 2 * x⁻¹ / ((k : ℝ) + 1)) := by ring
    have hneg : -2 * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 3 - 4 * m * x⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 2 -
        4 * m ^ 2 * x⁻¹ / ((k : ℝ) + 1) ≤ 0 := by
      rw [hrew]; exact neg_nonpos.mpr (by positivity)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hneg, abs_of_pos (Real.exp_pos _), hrew, neg_neg]
    have hpre : 2 * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 3 + 4 * m * x⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 2 +
        4 * m ^ 2 * x⁻¹ / ((k : ℝ) + 1) ≤ C1 := by
      have h1 : 2 * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 3 ≤ 2 * a⁻¹ ^ 3 :=
        (div_le_self (by positivity) (one_le_pow₀ hk1)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv_le 3) (by positivity))
      have h2 : 4 * m * x⁻¹ ^ 2 / ((k : ℝ) + 1) ^ 2 ≤ 4 * m * a⁻¹ ^ 2 :=
        (div_le_self (by positivity) (one_le_pow₀ hk1)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv_le 2) (by positivity))
      have h3 : 4 * m ^ 2 * x⁻¹ / ((k : ℝ) + 1) ≤ 4 * m ^ 2 * a⁻¹ :=
        (div_le_self (by positivity) hk1).trans (mul_le_mul_of_nonneg_left hinv_le (by positivity))
      dsimp only [C1]; linarith
    exact mul_le_mul hpre (hexp_le k hx) (Real.exp_pos _).le (by positivity)
  have hg2_bd : ∀ (k : ℕ) (x : ℝ), x ∈ Set.Ioi a → ‖g2 k x‖ ≤ C2 * Real.exp (-(((k : ℝ) + 1) * (2 * m * a))) := by
    intro k x hx
    have hxa : a < x := hx
    have hx_pos : 0 < x := lt_trans ha hxa
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hinv_le : x⁻¹ ≤ a⁻¹ := inv_anti₀ ha hxa.le
    dsimp only [g2]
    rw [Real.norm_of_nonneg (by positivity)]
    have hpre : 6 * x⁻¹ ^ 4 / ((k : ℝ) + 1) ^ 3 + 12 * m * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 2 +
        12 * m ^ 2 * x⁻¹ ^ 2 / ((k : ℝ) + 1) + 8 * m ^ 3 * x⁻¹ ≤ C2 := by
      have h1 : 6 * x⁻¹ ^ 4 / ((k : ℝ) + 1) ^ 3 ≤ 6 * a⁻¹ ^ 4 :=
        (div_le_self (by positivity) (one_le_pow₀ hk1)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv_le 4) (by positivity))
      have h2 : 12 * m * x⁻¹ ^ 3 / ((k : ℝ) + 1) ^ 2 ≤ 12 * m * a⁻¹ ^ 3 :=
        (div_le_self (by positivity) (one_le_pow₀ hk1)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv_le 3) (by positivity))
      have h3 : 12 * m ^ 2 * x⁻¹ ^ 2 / ((k : ℝ) + 1) ≤ 12 * m ^ 2 * a⁻¹ ^ 2 :=
        (div_le_self (by positivity) hk1).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv_le 2) (by positivity))
      have h4 : 8 * m ^ 3 * x⁻¹ ≤ 8 * m ^ 3 * a⁻¹ := mul_le_mul_of_nonneg_left hinv_le (by positivity)
      dsimp only [C2]; linarith
    exact mul_le_mul hpre (hexp_le k hx) (Real.exp_pos _).le (by positivity)
  have hsum1 : ∀ x ∈ Set.Ioi a, HasDerivAt (fun y => ∑' k : ℕ, g0 k y) (∑' k : ℕ, g1 k x) x := by
    intro x hx
    exact hasDerivAt_tsum_of_isPreconnected (hgeom.mul_left C1) isOpen_Ioi isPreconnected_Ioi
      (fun k y hy => hg0_deriv k (lt_trans ha hy)) hg1_bd hL_mem hg0_summ hx
  have hg1_summ : Summable (fun k : ℕ => g1 k L) :=
    (hgeom.mul_left C1).of_norm_bounded fun k => hg1_bd k L hL_mem
  have hsum2 : HasDerivAt (fun y => ∑' k : ℕ, g1 k y) (∑' k : ℕ, g2 k L) L :=
    hasDerivAt_tsum_of_isPreconnected (hgeom.mul_left C2) isOpen_Ioi isPreconnected_Ioi
      (fun k y hy => hg1_deriv k (lt_trans ha hy)) hg2_bd hL_mem hg1_summ hL_mem
  have hE1 : ∀ x ∈ Set.Ioi a, deriv (casimirEnergy2D m) x = -(1 / (16 * Real.pi)) * ∑' k : ℕ, g1 k x := by
    intro x hx
    have hev : casimirEnergy2D m =ᶠ[𝓝 x] fun y => -(1 / (16 * Real.pi)) * ∑' k : ℕ, g0 k y := by
      filter_upwards [isOpen_Ioi.mem_nhds (lt_trans ha hx)] with y hy; exact hE_eq y hy
    exact (((hsum1 x hx).const_mul (-(1 / (16 * Real.pi)))).congr_of_eventuallyEq hev).deriv
  have hE2 : deriv (deriv (casimirEnergy2D m)) L = -(1 / (16 * Real.pi)) * ∑' k : ℕ, g2 k L := by
    have hev : deriv (casimirEnergy2D m) =ᶠ[𝓝 L] fun y => -(1 / (16 * Real.pi)) * ∑' k : ℕ, g1 k y := by
      filter_upwards [isOpen_Ioi.mem_nhds hL_mem] with y hy; exact hE1 y hy
    exact ((hsum2.const_mul (-(1 / (16 * Real.pi)))).congr_of_eventuallyEq hev).deriv
  have hg2_summ : Summable (fun k : ℕ => g2 k L) :=
    (hgeom.mul_left C2).of_norm_bounded fun k => hg2_bd k L hL_mem
  rw [iteratedDeriv_succ, iteratedDeriv_one, hE2, hE1 L hL_mem]
  have hcomb : L * (-(1 / (16 * Real.pi)) * ∑' k : ℕ, g2 k L) +
      3 * (-(1 / (16 * Real.pi)) * ∑' k : ℕ, g1 k L) =
      -(1 / (16 * Real.pi)) * ∑' k : ℕ, (L * g2 k L + 3 * g1 k L) := by
    rw [((hg2_summ.mul_left L).tsum_add (hg1_summ.mul_left 3)), tsum_mul_left, tsum_mul_left]
    ring
  rw [hcomb]
  have hcancel : ∀ k : ℕ, L * g2 k L + 3 * g1 k L = 8 * m ^ 3 * Real.exp (-(2 * ((k : ℝ) + 1) * m * L)) := by
    intro k
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    dsimp only [g1, g2]
    field_simp [hL.ne', hk1]; ring
  simp_rw [hcancel, tsum_mul_left]
  have hr : 0 < Real.exp (-(2 * m * L)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * m * L)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hgeo_sum : (∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * m * L))) =
      Real.exp (-(2 * m * L)) / (1 - Real.exp (-(2 * m * L))) := by
    have hpow : ∀ k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * m * L)) =
        Real.exp (-(2 * m * L)) * (Real.exp (-(2 * m * L))) ^ k := fun k => by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    simp_rw [hpow, tsum_mul_left, tsum_geometric_of_lt_one hr.le hr1, div_eq_mul_inv]
  rw [hgeo_sum]
  ring

/-- **Even Dimension (`d = 2`) — Massive Casimir Force D-Algebraicity**:
For every positive mass `m > 0`, the 2D massive parallel-plate Casimir force `F_C^{(2D)}(L)`
satisfies the explicit nonzero order-2 quadratic ADE over `ℂ[L]`:
`m² L F''(L) + 4 m² F'(L) + 2 m³ (L F'(L) + 3 F(L)) + 4π (L F'(L) + 3 F(L))² = 0`. -/
theorem casimirForce2D_dAlgebraic {m : ℝ} (hm : 0 < m) :
    ∃ P : MvPolynomial (Fin 3) (Polynomial ℂ), P ≠ 0 ∧
      ∀ L : ℝ, 0 < L →
        MvPolynomial.eval
          (fun j : Fin 3 => iteratedDeriv j.val (fun l : ℝ => (casimirForce2D m l : ℂ)) L)
          (evalU P (L : ℂ)) = 0 := by
  refine ⟨casimirForce2DPoly (m : ℂ), casimirForce2DPoly_ne_zero hm, fun L hL => ?_⟩
  have hP_an : AnalyticOnNhd ℝ (bosePressure2D m) (Set.Ioi 0) := by
    intro t ht
    have hre : AnalyticAt ℝ (fun s : ℝ => ((bosePressure2D m s : ℂ)).re) t :=
      AnalyticAt.comp (g := fun z : ℂ => z.re) (f := fun s : ℝ => (bosePressure2D m s : ℂ))
        (Complex.reCLM.analyticAt (bosePressure2D m t : ℂ)) (bosePressure2D_analyticOnNhd hm t ht)
    simpa using hre
  have hE_an : AnalyticOnNhd ℝ (casimirEnergy2D m) (Set.Ioi 0) := by
    intro l hl
    have hl' : 0 < l := hl
    have hinv : AnalyticAt ℝ (fun x : ℝ => 1 / (2 * x)) l :=
      analyticAt_const.div (analyticAt_const.mul analyticAt_id) (by positivity)
    have hmem : 1 / (2 * l) ∈ Set.Ioi (0 : ℝ) := by change 0 < 1 / (2 * l); positivity
    have hcomp : AnalyticAt ℝ (fun x : ℝ => bosePressure2D m (1 / (2 * x))) l :=
      AnalyticAt.comp (g := bosePressure2D m) (f := fun x : ℝ => 1 / (2 * x)) (hP_an _ hmem) hinv
    exact (analyticAt_id.neg).mul hcomp
  have hF_an : AnalyticOnNhd ℝ (casimirForce2D m) (Set.Ioi 0) := fun l hl => (hE_an l hl).deriv.neg
  have hQF : ∀ l : ℝ, 0 < l →
      l * deriv (casimirForce2D m) l + 3 * casimirForce2D m l =
        (m ^ 3 / (2 * Real.pi)) * (Real.exp (-(2 * m * l)) / (1 - Real.exp (-(2 * m * l)))) := by
    intro l hl
    have hQ := casimirEnergy2D_Q_eq hm hl
    rw [iteratedDeriv_succ, iteratedDeriv_one] at hQ
    have hdF : deriv (casimirForce2D m) l = -deriv (deriv (casimirEnergy2D m)) l := by
      have : casimirForce2D m = -(deriv (casimirEnergy2D m)) := rfl
      rw [this, deriv.neg]
    rw [hdF]
    change l * -deriv (deriv (casimirEnergy2D m)) l + 3 * -deriv (casimirEnergy2D m) l = _
    linarith
  have hLHS : HasDerivAt (fun l : ℝ => l * deriv (casimirForce2D m) l + 3 * casimirForce2D m l)
      (L * iteratedDeriv 2 (casimirForce2D m) L + 4 * iteratedDeriv 1 (casimirForce2D m) L) L := by
    have h1 := (hasDerivAt_id L).mul (hF_an L hL).deriv.differentiableAt.hasDerivAt
    have h2 := (hF_an L hL).differentiableAt.hasDerivAt.const_mul (3 : ℝ)
    refine (h1.add h2).congr_deriv ?_
    rw [iteratedDeriv_succ, iteratedDeriv_one]; simp only [id_eq]; ring
  let r : ℝ := Real.exp (-(2 * m * L))
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h1mr : 1 - r ≠ 0 := by linarith
  have hRHS : HasDerivAt (fun l : ℝ =>
      (m ^ 3 / (2 * Real.pi)) * (Real.exp (-(2 * m * l)) / (1 - Real.exp (-(2 * m * l)))))
      (-(m ^ 4 / Real.pi) * (r / (1 - r) ^ 2)) L := by
    have hexp : HasDerivAt (fun l : ℝ => Real.exp (-(2 * m * l))) (r * (-(2 * m))) L := by
      have hlin : HasDerivAt (fun l : ℝ => -(2 * m * l)) (-(2 * m)) L := by
        have h := (hasDerivAt_id L).const_mul (-(2 * m))
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun l => by simp) |>.congr_deriv ?_
        ring
      exact hlin.exp
    have hquot := hexp.div (hexp.const_sub 1) h1mr
    refine (hquot.const_mul (m ^ 3 / (2 * Real.pi))).congr_deriv ?_
    dsimp only [r]; field_simp [h1mr]; ring
  have hev : (fun l : ℝ => l * deriv (casimirForce2D m) l + 3 * casimirForce2D m l) =ᶠ[𝓝 L]
      fun l => (m ^ 3 / (2 * Real.pi)) * (Real.exp (-(2 * m * l)) / (1 - Real.exp (-(2 * m * l)))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hL] with l hl; exact hQF l hl
  have hderiv_eq : L * iteratedDeriv 2 (casimirForce2D m) L + 4 * iteratedDeriv 1 (casimirForce2D m) L =
      -(m ^ 4 / Real.pi) * (r / (1 - r) ^ 2) :=
    (hLHS.congr_of_eventuallyEq hev.symm).unique hRHS
  have hQ_L := hQF L hL
  rw [← iteratedDeriv_one] at hQ_L
  have hreal : m ^ 2 * L * iteratedDeriv 2 (casimirForce2D m) L +
      4 * m ^ 2 * iteratedDeriv 1 (casimirForce2D m) L +
      2 * m ^ 3 * (L * iteratedDeriv 1 (casimirForce2D m) L + 3 * casimirForce2D m L) +
      4 * Real.pi * (L * iteratedDeriv 1 (casimirForce2D m) L + 3 * casimirForce2D m L) ^ 2 = 0 := by
    have h1 : m ^ 2 * L * iteratedDeriv 2 (casimirForce2D m) L +
        4 * m ^ 2 * iteratedDeriv 1 (casimirForce2D m) L =
        m ^ 2 * (L * iteratedDeriv 2 (casimirForce2D m) L + 4 * iteratedDeriv 1 (casimirForce2D m) L) := by ring
    rw [h1, hderiv_eq, hQ_L]
    change m ^ 2 * (-(m ^ 4 / Real.pi) * (r / (1 - r) ^ 2)) +
      2 * m ^ 3 * ((m ^ 3 / (2 * Real.pi)) * (r / (1 - r))) +
      4 * Real.pi * ((m ^ 3 / (2 * Real.pi)) * (r / (1 - r))) ^ 2 = 0
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi, h1mr]; ring
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simp only [casimirForce2DPoly, evalU, map_add, map_mul, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    iteratedDeriv_ofReal_comp_eos] at hcast ⊢
  simpa [iteratedDeriv_zero] using hcast

/-- **Even Dimension (`d = 2`) — Massive Casimir Energy D-Algebraicity**:
For every positive mass `m > 0`, the 2D massive parallel-plate Casimir energy `E_C^{(2D)}(L)`
satisfies the explicit nonzero order-3 quadratic ADE over `ℂ[L]`. -/
theorem casimirEnergy2D_dAlgebraic {m : ℝ} (hm : 0 < m) :
    ∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ L : ℝ, 0 < L →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy2D m l : ℂ)) L)
          (evalU P (L : ℂ)) = 0 := by
  refine ⟨casimirEnergy2DPoly (m : ℂ), casimirEnergy2DPoly_ne_zero hm, fun L hL => ?_⟩
  have hP_an : AnalyticOnNhd ℝ (bosePressure2D m) (Set.Ioi 0) := by
    intro t ht
    have hre : AnalyticAt ℝ (fun s : ℝ => ((bosePressure2D m s : ℂ)).re) t :=
      AnalyticAt.comp (g := fun z : ℂ => z.re) (f := fun s : ℝ => (bosePressure2D m s : ℂ))
        (Complex.reCLM.analyticAt (bosePressure2D m t : ℂ)) (bosePressure2D_analyticOnNhd hm t ht)
    simpa using hre
  have hE_an : AnalyticOnNhd ℝ (casimirEnergy2D m) (Set.Ioi 0) := by
    intro l hl
    have hl' : 0 < l := hl
    have hinv : AnalyticAt ℝ (fun x : ℝ => 1 / (2 * x)) l :=
      analyticAt_const.div (analyticAt_const.mul analyticAt_id) (by positivity)
    have hmem : 1 / (2 * l) ∈ Set.Ioi (0 : ℝ) := by change 0 < 1 / (2 * l); positivity
    have hcomp : AnalyticAt ℝ (fun x : ℝ => bosePressure2D m (1 / (2 * x))) l :=
      AnalyticAt.comp (g := bosePressure2D m) (f := fun x : ℝ => 1 / (2 * x)) (hP_an _ hmem) hinv
    exact (analyticAt_id.neg).mul hcomp
  have hLHS : HasDerivAt (fun l : ℝ =>
      l * iteratedDeriv 2 (casimirEnergy2D m) l + 3 * iteratedDeriv 1 (casimirEnergy2D m) l)
      (L * iteratedDeriv 3 (casimirEnergy2D m) L + 4 * iteratedDeriv 2 (casimirEnergy2D m) L) L := by
    have h2_an : AnalyticAt ℝ (iteratedDeriv 2 (casimirEnergy2D m)) L := by
      rw [iteratedDeriv_eq_iterate]; exact hE_an.iterated_deriv 2 L hL
    have h1_an : AnalyticAt ℝ (iteratedDeriv 1 (casimirEnergy2D m)) L := by
      rw [iteratedDeriv_eq_iterate]; exact hE_an.iterated_deriv 1 L hL
    have h1 := (hasDerivAt_id L).mul h2_an.differentiableAt.hasDerivAt
    have h2 := h1_an.differentiableAt.hasDerivAt.const_mul (3 : ℝ)
    refine (h1.add h2).congr_deriv ?_
    have hd3 : deriv (iteratedDeriv 2 (casimirEnergy2D m)) L = iteratedDeriv 3 (casimirEnergy2D m) L :=
      (iteratedDeriv_succ (n := 2) (f := casimirEnergy2D m) ▸ rfl)
    have hd2 : deriv (iteratedDeriv 1 (casimirEnergy2D m)) L = iteratedDeriv 2 (casimirEnergy2D m) L :=
      (iteratedDeriv_succ (n := 1) (f := casimirEnergy2D m) ▸ rfl)
    rw [hd3, hd2]; simp only [id_eq]; ring
  let r : ℝ := Real.exp (-(2 * m * L))
  have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h1mr : 1 - r ≠ 0 := by linarith
  have hRHS : HasDerivAt (fun l : ℝ =>
      -(m ^ 3 / (2 * Real.pi)) * (Real.exp (-(2 * m * l)) / (1 - Real.exp (-(2 * m * l)))))
      ((m ^ 4 / Real.pi) * (r / (1 - r) ^ 2)) L := by
    have hexp : HasDerivAt (fun l : ℝ => Real.exp (-(2 * m * l))) (r * (-(2 * m))) L := by
      have hlin : HasDerivAt (fun l : ℝ => -(2 * m * l)) (-(2 * m)) L := by
        have h := (hasDerivAt_id L).const_mul (-(2 * m))
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun l => by simp) |>.congr_deriv ?_
        ring
      exact hlin.exp
    have hquot := hexp.div (hexp.const_sub 1) h1mr
    refine (hquot.const_mul (-(m ^ 3 / (2 * Real.pi)))).congr_deriv ?_
    dsimp only [r]; field_simp [h1mr]; ring
  have hev : (fun l : ℝ => l * iteratedDeriv 2 (casimirEnergy2D m) l +
      3 * iteratedDeriv 1 (casimirEnergy2D m) l) =ᶠ[𝓝 L]
      fun l => -(m ^ 3 / (2 * Real.pi)) * (Real.exp (-(2 * m * l)) / (1 - Real.exp (-(2 * m * l)))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hL] with l hl; exact casimirEnergy2D_Q_eq hm hl
  have hderiv_eq := (hLHS.congr_of_eventuallyEq hev.symm).unique hRHS
  have hQ_L := casimirEnergy2D_Q_eq hm hL
  have hreal : (0 : ℝ) - m ^ 2 * L * iteratedDeriv 3 (casimirEnergy2D m) L -
      4 * m ^ 2 * iteratedDeriv 2 (casimirEnergy2D m) L +
      2 * m ^ 3 * (-(L * iteratedDeriv 2 (casimirEnergy2D m) L + 3 * iteratedDeriv 1 (casimirEnergy2D m) L)) +
      4 * Real.pi * (-(L * iteratedDeriv 2 (casimirEnergy2D m) L + 3 * iteratedDeriv 1 (casimirEnergy2D m) L)) ^ 2 = 0 := by
    have h1 : (0 : ℝ) - m ^ 2 * L * iteratedDeriv 3 (casimirEnergy2D m) L -
        4 * m ^ 2 * iteratedDeriv 2 (casimirEnergy2D m) L =
        -(m ^ 2 * (L * iteratedDeriv 3 (casimirEnergy2D m) L + 4 * iteratedDeriv 2 (casimirEnergy2D m) L)) := by ring
    rw [h1, hderiv_eq, hQ_L]
    change -(m ^ 2 * ((m ^ 4 / Real.pi) * (r / (1 - r) ^ 2))) +
      2 * m ^ 3 * -(-(m ^ 3 / (2 * Real.pi)) * (r / (1 - r))) +
      4 * Real.pi * (-(-(m ^ 3 / (2 * Real.pi)) * (r / (1 - r)))) ^ 2 = 0
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi, h1mr]; ring
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simp only [casimirEnergy2DPoly, evalU, map_zero, map_sub, map_add, map_neg, map_mul, map_pow,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    iteratedDeriv_ofReal_comp_eos] at hcast ⊢
  simpa using hcast

private lemma neg_fun_no_rat_ade {g : ℝ → ℝ}
    (hg_no : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L →
        (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (g l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) →
      R = 0) :
    ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L →
        (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => ((-g l) : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) →
      R = 0 := by
  intro r R hR
  let negHom : MvPolynomial (Fin (r + 1)) (RatFunc ℂ) →ₐ[RatFunc ℂ]
      MvPolynomial (Fin (r + 1)) (RatFunc ℂ) :=
    MvPolynomial.aeval (fun j : Fin (r + 1) => -MvPolynomial.X j)
  let R_neg : MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := negHom R
  have hneg_coeff : ∀ β : Fin (r + 1) →₀ ℕ,
      R_neg.coeff β = ((-1 : RatFunc ℂ) ^ (β.sum fun _ n => n)) * R.coeff β := by
    intro β
    dsimp only [R_neg, negHom]
    clear hR
    induction R using MvPolynomial.induction_on' generalizing β with
    | monomial α c =>
      simp only [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
      have hprod : (α.prod fun i e => (-MvPolynomial.X i : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ e) =
          MvPolynomial.C ((-1 : RatFunc ℂ) ^ (α.sum fun _ n => n)) *
            MvPolynomial.monomial α (1 : RatFunc ℂ) := by
        rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod, Finsupp.sum]
        have h1 : ∀ i ∈ α.support, (-MvPolynomial.X i : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ α i =
            MvPolynomial.C ((-1 : RatFunc ℂ) ^ α i) * (MvPolynomial.X i) ^ α i := fun i _ => by
          rw [show (-MvPolynomial.X i : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) =
            MvPolynomial.C (-1 : RatFunc ℂ) * MvPolynomial.X i by simp, mul_pow, ← map_pow]
        rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
        rfl
      rw [hprod, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst h; ring
      · ring
    | add A B hA hB =>
      rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply,
        hA β, hB β]
      ring
  have hR_neg_zero : R_neg = 0 := by
    refine hg_no R_neg fun L hL hden => ?_
    have hden_R : ∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0 := by
      intro β hβ
      have hβ' : β ∈ R_neg.support := by
        rw [MvPolynomial.mem_support_iff, hneg_coeff]
        exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (MvPolynomial.mem_support_iff.mp hβ)
      have hd := hden β hβ'
      rw [hneg_coeff] at hd
      have hsign : ((-1 : RatFunc ℂ) ^ (β.sum fun _ n => n)) = 1 ∨
          ((-1 : RatFunc ℂ) ^ (β.sum fun _ n => n)) = -1 := by
        rcases Nat.even_or_odd (β.sum fun _ n => n) with ⟨k, hk⟩ | ⟨k, hk⟩
        · left; rw [hk, ← two_mul, pow_mul]; norm_num
        · right; rw [hk, pow_succ, pow_mul]; norm_num
      rcases hsign with h1 | hm1
      · rwa [h1, one_mul] at hd
      · rw [hm1, neg_one_mul] at hd
        intro h0
        have hq : R.coeff β = algebraMap (Polynomial ℂ) (RatFunc ℂ) (-(-(R.coeff β)).num) /
            algebraMap (Polynomial ℂ) (RatFunc ℂ) (-(R.coeff β)).denom := by
          have h1 := congrArg Neg.neg (RatFunc.num_div_denom (-(R.coeff β)))
          rw [neg_neg] at h1
          conv_lhs => rw [← h1]
          rw [map_neg]; ring
        have hdiv : (R.coeff β).denom ∣ (-(R.coeff β)).denom :=
          (RatFunc.denom_dvd (RatFunc.denom_ne_zero (-(R.coeff β)))).mpr ⟨-(-(R.coeff β)).num, hq⟩
        rcases hdiv with ⟨u, hu⟩
        have hev := congrArg (Polynomial.eval (L : ℂ)) hu
        rw [Polynomial.eval_mul, h0, zero_mul] at hev
        exact hd hev
    have heval_eq : evalRatU R_neg (L : ℂ) =
        MvPolynomial.aeval (fun j : Fin (r + 1) => -MvPolynomial.X j) (evalRatU R (L : ℂ)) := by
      classical
      ext β
      rw [evalRatU, MvPolynomial.coeff_sum]
      simp_rw [MvPolynomial.coeff_monomial]
      have hlhs : (∑ x ∈ R_neg.support, if x = β then ratEval (R_neg.coeff x) (L : ℂ) else 0) =
          ratEval (R_neg.coeff β) (L : ℂ) := by
        by_cases hβ : β ∈ R_neg.support
        · rw [Finset.sum_eq_single β]
          · simp
          · intro b _ hb; simp [hb]
          · intro h; exact absurd hβ h
        · rw [Finset.sum_eq_zero]
          · have hc0 : R_neg.coeff β = 0 := MvPolynomial.notMem_support_iff.mp hβ
            rw [hc0]; simp [ratEval]
          · intro b hb; simp [show b ≠ β from fun h => hβ (h ▸ hb)]
      rw [hlhs]
      have hrhs : (MvPolynomial.aeval (fun j : Fin (r + 1) => -MvPolynomial.X j) (evalRatU R (L : ℂ))).coeff β =
          ((-1 : ℂ) ^ (β.sum fun _ n => n)) * (evalRatU R (L : ℂ)).coeff β := by
        clear hlhs
        generalize evalRatU R (L : ℂ) = M
        induction M using MvPolynomial.induction_on' generalizing β with
        | monomial α c =>
          simp only [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
          have hprod : (α.prod fun i e => (-MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℂ) ^ e) =
              MvPolynomial.C ((-1 : ℂ) ^ (α.sum fun _ n => n)) *
                MvPolynomial.monomial α (1 : ℂ) := by
            rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod, Finsupp.sum]
            have h1 : ∀ i ∈ α.support, (-MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℂ) ^ α i =
                MvPolynomial.C ((-1 : ℂ) ^ α i) * (MvPolynomial.X i) ^ α i := fun i _ => by
              rw [show (-MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℂ) =
                MvPolynomial.C (-1 : ℂ) * MvPolynomial.X i by simp, mul_pow, ← map_pow]
            rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
            rfl
          rw [hprod, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one,
            MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
          split_ifs with h
          · subst h; ring
          · ring
        | add A B hA hB =>
          rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply,
            hA β, hB β]
          ring
      rw [hrhs, hneg_coeff]
      have hrc : (evalRatU R (L : ℂ)).coeff β = ratEval (R.coeff β) (L : ℂ) := by
        rw [evalRatU, MvPolynomial.coeff_sum]
        simp_rw [MvPolynomial.coeff_monomial]
        by_cases hβ : β ∈ R.support
        · rw [Finset.sum_eq_single β]
          · simp
          · intro b _ hb; simp [hb]
          · intro h; exact absurd hβ h
        · rw [Finset.sum_eq_zero]
          · have hc0 : R.coeff β = 0 := MvPolynomial.notMem_support_iff.mp hβ
            rw [hc0]; simp [ratEval]
          · intro b hb; simp [show b ≠ β from fun h => hβ (h ▸ hb)]
      rw [hrc]
      rcases Nat.even_or_odd (β.sum fun _ n => n) with ⟨k, hk⟩ | ⟨k, hk⟩
      · have h1 : (-1 : RatFunc ℂ) ^ (β.sum fun _ n => n) = 1 := by
          rw [hk, ← two_mul, pow_mul]; norm_num
        have h2 : (-1 : ℂ) ^ (β.sum fun _ n => n) = 1 := by
          rw [hk, ← two_mul, pow_mul]; norm_num
        rw [h1, h2, one_mul, one_mul]
      · have h1 : (-1 : RatFunc ℂ) ^ (β.sum fun _ n => n) = -1 := by
          rw [hk, pow_succ, pow_mul]; norm_num
        have h2 : (-1 : ℂ) ^ (β.sum fun _ n => n) = -1 := by
          rw [hk, pow_succ, pow_mul]; norm_num
        rw [h1, h2, neg_one_mul, neg_one_mul]
        by_cases hβ : β ∈ R.support
        · have hd_R := hden_R β hβ
          have hβ' : β ∈ R_neg.support := by
            rw [MvPolynomial.mem_support_iff, hneg_coeff, h1, neg_one_mul]
            exact neg_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hβ)
          have hd_neg := hden β hβ'
          rw [hneg_coeff, h1, neg_one_mul] at hd_neg
          have hrel : (-(R.coeff β)).num * (R.coeff β).denom = -((R.coeff β).num * (-(R.coeff β)).denom) := by
            apply RatFunc.algebraMap_injective ℂ
            have hq1 := RatFunc.num_div_denom (-(R.coeff β))
            have hq2 := RatFunc.num_div_denom (R.coeff β)
            have hd1 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (-(R.coeff β)).denom ≠ 0 :=
              (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr (RatFunc.denom_ne_zero _)
            have hd2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (R.coeff β).denom ≠ 0 :=
              (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr (RatFunc.denom_ne_zero _)
            simp only [map_mul, map_neg]
            have heq : algebraMap (Polynomial ℂ) (RatFunc ℂ) (-(R.coeff β)).num /
                algebraMap (Polynomial ℂ) (RatFunc ℂ) (-(R.coeff β)).denom =
                -(algebraMap (Polynomial ℂ) (RatFunc ℂ) (R.coeff β).num /
                  algebraMap (Polynomial ℂ) (RatFunc ℂ) (R.coeff β).denom) := by
              rw [hq1, hq2]
            rw [div_eq_iff hd1] at heq
            have heq' := congrArg (· * algebraMap (Polynomial ℂ) (RatFunc ℂ) (R.coeff β).denom) heq
            field_simp [hd2] at heq'
            linear_combination heq'
          have hev := congrArg (Polynomial.eval (L : ℂ)) hrel
          simp only [Polynomial.eval_mul, Polynomial.eval_neg] at hev
          unfold ratEval
          field_simp [hd_neg, hd_R]
          linear_combination hev
        · have hc0 : R.coeff β = 0 := MvPolynomial.notMem_support_iff.mp hβ
          rw [hc0, neg_zero]; simp [ratEval]
    rw [heval_eq]
    have hcomp : MvPolynomial.eval (fun j : Fin (r + 1) =>
          iteratedDeriv j.val (fun e : ℝ => (g e : ℂ)) L)
          (MvPolynomial.aeval (fun j : Fin (r + 1) => -MvPolynomial.X j) (evalRatU R (L : ℂ))) =
        MvPolynomial.eval (fun j : Fin (r + 1) =>
          -iteratedDeriv j.val (fun e : ℝ => (g e : ℂ)) L)
          (evalRatU R (L : ℂ)) := by
      generalize evalRatU R (L : ℂ) = Q
      induction Q using MvPolynomial.induction_on with
      | C a => simp
      | add A B hA hB => rw [map_add, map_add, map_add, hA, hB]
      | mul_X A j hA => rw [map_mul, map_mul, map_mul, hA, MvPolynomial.aeval_X, map_neg, MvPolynomial.eval_X, MvPolynomial.eval_X]
    rw [hcomp]
    have hjet : (fun j : Fin (r + 1) =>
          -iteratedDeriv j.val (fun e : ℝ => (g e : ℂ)) L) =
        fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => ((-g l) : ℂ)) L := by
      ext j
      have hf : (fun l : ℝ => ((-g l) : ℂ)) = fun e : ℝ => -(g e : ℂ) := by
        funext l; rfl
      rw [hf, iteratedDeriv_fun_neg]
    rw [hjet]
    exact hR L hL hden_R
  ext β
  have h0 := congrArg (fun M => M.coeff β) hR_neg_zero
  rw [hneg_coeff, show (0 : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)).coeff β = 0 from rfl] at h0
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (by norm_num))

private lemma casimirEnergy_no_rat_ade {P : ℝ → ℝ}
    (hP_an : AnalyticOnNhd ℝ (fun T : ℝ => (P T : ℂ)) (Set.Ioi 0))
    (hP_no_ade : ∀ {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)),
      (∀ T : ℝ, 0 < T →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (P t : ℂ)) T)
          (evalU Q (T : ℂ)) = 0) → Q = 0) :
    ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L →
        (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy P l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) →
      R = 0 := by
  have hE_an : AnalyticOnNhd ℝ (fun l : ℝ => (casimirEnergy P l : ℂ)) (Set.Ioi 0) := by
    intro l hl
    have hl' : 0 < l := hl
    have hinv : AnalyticAt ℝ (fun x : ℝ => (1 : ℝ) / (2 * x)) l :=
      analyticAt_const.div (analyticAt_const.mul analyticAt_id) (by positivity)
    have hmem : (1 : ℝ) / (2 * l) ∈ Set.Ioi (0 : ℝ) := by change 0 < (1 : ℝ) / (2 * l); positivity
    have hcomp : AnalyticAt ℝ (fun x : ℝ => (P ((1 : ℝ) / (2 * x)) : ℂ)) l :=
      AnalyticAt.comp (g := fun t : ℝ => (P t : ℂ)) (f := fun x : ℝ => (1 : ℝ) / (2 * x))
        (hP_an _ hmem) hinv
    have heq : (fun x : ℝ => (casimirEnergy P x : ℂ)) =
        fun x : ℝ => -(x : ℂ) * (P ((1 : ℝ) / ((2 : ℝ) * x)) : ℂ) := by
      funext x; unfold casimirEnergy; push_cast; ring
    rw [heq]
    exact (Complex.ofRealCLM.analyticAt l).neg.mul hcomp
  have hE_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun l : ℝ => (casimirEnergy P l : ℂ)) (Set.Ioi 0) :=
    hE_an.contDiffOn isOpen_Ioi.uniqueDiffOn
  have hE_no : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L →
        (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy P l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) →
      R = 0 := by
    intro r R hR
    by_contra hR_ne
    obtain ⟨Q, hQ_ne, hQ_zero⟩ := clearDenom_rat_on_open isOpen_Ioi hE_smooth R hR_ne hR
    let Lmap : ℝ → ℝ := fun T => 1 / (2 * T)
    let y : ℕ → ℝ → ℂ := fun k T =>
      match k with
      | 0 => (Lmap T : ℂ)
      | j + 1 => iteratedDeriv j (fun l : ℝ => (casimirEnergy P l : ℂ)) (Lmap T)
    have hrel_y : ∃ A : MvPolynomial ℕ ℂ, A ≠ 0 ∧ ∀ T ∈ Set.Ioi (0 : ℝ), MvPolynomial.eval (fun k => y k T) A = 0 := by
      refine ⟨liftPolyToNat Q, liftPolyToNat_ne_zero hQ_ne, fun T hT => ?_⟩
      have hT' : 0 < T := hT
      have hL_pos : 0 < Lmap T := by dsimp only [Lmap]; positivity
      have hval := hQ_zero (Lmap T) hL_pos
      rw [← eval_liftPolyToNat Q (Lmap T : ℂ)
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy P l : ℂ)) (Lmap T))] at hval
      have heq_coord : ∀ k ∈ (liftPolyToNat Q).vars,
          y k T = (if k = 0 then (Lmap T : ℂ)
            else if hlt : k - 1 < r + 1 then
              iteratedDeriv (k - 1) (fun l : ℝ => (casimirEnergy P l : ℂ)) (Lmap T) else 0) := by
        intro k hk
        cases k with
        | zero => simp [y]
        | succ j =>
          have hjlt : j < r + 1 := by
            have hsub : (liftPolyToNat Q).vars ⊆ Finset.range (r + 2) := by
              clear hk hval hQ_zero hQ_ne hT hL_pos
              induction Q using MvPolynomial.induction_on with
              | C q =>
                simp only [liftPolyToNat, MvPolynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
                induction q using Polynomial.induction_on' with
                | add a b ha hb =>
                  rw [map_add]; exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset ha hb)
                | monomial n a =>
                  simp only [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
                  refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ?_ ?_)
                  · simp
                  · exact (MvPolynomial.vars_pow _ _).trans (by simp)
              | add A B hA hB =>
                rw [liftPolyToNat, MvPolynomial.eval₂_add]
                exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset hA hB)
              | mul_X A m hA =>
                rw [liftPolyToNat, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
                refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset hA ?_)
                simp [Finset.mem_range]; omega
            have := Finset.mem_range.mp (hsub hk); omega
          simp [y, hjlt]
      rw [eval_congr_vars (liftPolyToNat Q) heq_coord]
      exact hval
    obtain ⟨n, A, T₁, hT₁, hS₁_ne, hA_zero⟩ := ordinary_relation (Set.Ioi (0 : ℝ)) ⟨1, zero_lt_one⟩ y hrel_y
    let v : Fin (n + 1) → ℝ → ℂ := fun i T => y i.val T
    let top : Fin (n + 1) := Fin.last n
    let g : Fin (n + 1) → ℝ → ℂ := fun i T => MvPolynomial.eval (fun j => v j T) (MvPolynomial.pderiv i A)
    let S : ℝ → ℂ := g top
    have hL_deriv : ∀ T : ℝ, 0 < T → HasDerivAt Lmap (-1 / (2 * T ^ 2)) T := by
      intro T hT
      have h1 := ((hasDerivAt_id T).const_mul (2 : ℝ)).inv (by positivity : (2 : ℝ) * T ≠ 0)
      refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Lmap, one_div]) |>.congr_deriv ?_
      simp only [id_eq]; field_simp [hT.ne']
    have hv_diff : ∀ T : ℝ, 0 < T → ∀ i : Fin (n + 1), DifferentiableAt ℝ (v i) T := by
      intro T hT i
      have hLp : 0 < Lmap T := by dsimp only [Lmap]; positivity
      rcases i with ⟨k, hk⟩
      cases k with
      | zero => exact Complex.ofRealCLM.differentiableAt.comp T (hL_deriv T hT).differentiableAt
      | succ j =>
        have hj : DifferentiableAt ℝ (iteratedDeriv j (fun l : ℝ => (casimirEnergy P l : ℂ))) (Lmap T) := by
          rw [iteratedDeriv_eq_iterate]; exact (hE_an.iterated_deriv j (Lmap T) hLp).differentiableAt
        exact hj.comp T (hL_deriv T hT).differentiableAt
    have hvanish : ∀ T : ℝ, 0 < T → ∑ i : Fin (n + 1), g i T * _root_.deriv (v i) T = 0 := by
      intro T hT
      have hchain := polynomial_chain A v (fun i => _root_.deriv (v i)) T (fun i => (hv_diff T hT i).hasDerivAt)
      have hnear : (fun t => MvPolynomial.eval (fun i => v i t) A) =ᶠ[𝓝 T] fun _ => 0 := by
        filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht; exact hA_zero t ht
      exact hchain.deriv.symm.trans (hnear.deriv_eq.trans (deriv_const _ _))
    have hn_pos : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      have hv0 := hvanish T₁ hT₁
      rw [Fin.sum_univ_one] at hv0
      have hd0 : _root_.deriv (v 0) T₁ = ((-1 / (2 * T₁ ^ 2) : ℝ) : ℂ) :=
        ((hL_deriv T₁ hT₁).ofReal_comp).deriv
      rw [hd0] at hv0
      have hne : ((-1 / (2 * T₁ ^ 2) : ℝ) : ℂ) ≠ 0 := by
        apply Complex.ofReal_ne_zero.mpr
        have hT₁_pos : 0 < T₁ := hT₁
        have h1 : 0 < 1 / (2 * T₁ ^ 2) := by positivity
        have h2 : -1 / (2 * T₁ ^ 2) = -(1 / (2 * T₁ ^ 2)) := by ring
        linarith
      exact mul_ne_zero hS₁_ne hne hv0
    let invS : ℝ → ℂ := fun T => (S T)⁻¹
    let uState : Fin (n + 1) ⊕ Fin 2 → ℝ → ℂ := Sum.elim v ![(fun T => (T : ℂ)), invS]
    let Gen := Generated uState T₁
    have gv (i : Fin (n + 1)) : Gen (v i) := Generated.coord (Sum.inl i)
    have gT : Gen (fun T => (T : ℂ)) := Generated.coord (Sum.inr 0)
    have ginvS : Gen invS := Generated.coord (Sum.inr 1)
    have gc (c : ℂ) : Gen (fun _ => c) := Generated.const c
    have gg (i : Fin (n + 1)) : Gen (g i) := Generated.evalPoly v gv _
    have gL' : Gen (fun T => ((-1 / (2 * T ^ 2) : ℝ) : ℂ)) := by
      refine ((gc (-2)).mul ((gv 0).pow 2)).congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds hT₁] with T hT
      have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
      change (-2 : ℂ) * ((1 / (2 * T) : ℝ) : ℂ) ^ 2 = ((-1 / (2 * T ^ 2) : ℝ) : ℂ)
      push_cast; field_simp [hTne]
    have hS_diff : ∀ T : ℝ, 0 < T → DifferentiableAt ℝ S T := fun T hT =>
      (polynomial_chain (MvPolynomial.pderiv top A) v (fun i => _root_.deriv (v i)) T
        (fun i => (hv_diff T hT i).hasDerivAt)).differentiableAt
    have hSnz : ∀ᶠ T in 𝓝 T₁, S T ≠ 0 := (hS_diff T₁ hT₁).continuousAt.eventually_ne hS₁_ne
    have low (i : Fin (n + 1)) (hi : i ≠ top) : Gen (_root_.deriv (v i)) := by
      rcases i with ⟨k, hk⟩
      cases k with
      | zero =>
        refine gL'.congr ?_
        filter_upwards [isOpen_Ioi.mem_nhds hT₁] with T hT
        exact (((hL_deriv T hT).ofReal_comp).deriv).symm
      | succ j =>
        have hjlt : j + 2 < n + 1 := by
          have hne : j + 1 ≠ n := fun h => hi (Fin.ext h); omega
        refine ((gv ⟨j + 2, hjlt⟩).mul gL').congr ?_
        filter_upwards [isOpen_Ioi.mem_nhds hT₁] with T hT
        have hT' : 0 < T := hT
        have hLp : 0 < Lmap T := by dsimp only [Lmap]; positivity
        have hj : HasDerivAt (iteratedDeriv j (fun l : ℝ => (casimirEnergy P l : ℂ)))
            (iteratedDeriv (j + 1) (fun l : ℝ => (casimirEnergy P l : ℂ)) (Lmap T)) (Lmap T) := by
          rw [iteratedDeriv_succ]
          have hd : DifferentiableAt ℝ (iteratedDeriv j (fun l : ℝ => (casimirEnergy P l : ℂ))) (Lmap T) := by
            rw [iteratedDeriv_eq_iterate]; exact (hE_an.iterated_deriv j (Lmap T) hLp).differentiableAt
          exact hd.hasDerivAt
        have hcomp := hj.scomp T (hL_deriv T hT)
        have hd : _root_.deriv ((iteratedDeriv j (fun l : ℝ => (casimirEnergy P l : ℂ))) ∘ Lmap) T =
            ((-1 / (2 * T ^ 2) : ℝ) : ℂ) * iteratedDeriv (j + 1) (fun l : ℝ => (casimirEnergy P l : ℂ)) (Lmap T) := by
          simpa [Complex.real_smul] using hcomp.deriv
        simpa [v, y, Function.comp_def, mul_comm] using hd.symm
    let lowSum : ℝ → ℂ := ∑ i ∈ Finset.univ.erase top, g i * _root_.deriv (v i)
    have glowSum : Gen lowSum :=
      Generated.finsetSum _ _ fun i hi => (gg i).mul (low i (Finset.mem_erase.mp hi).1)
    have dv (i : Fin (n + 1)) : Gen (_root_.deriv (v i)) := by
      by_cases hi : i = top
      · subst i
        refine (((gc (-1)).mul glowSum).mul ginvS).congr ?_
        filter_upwards [isOpen_Ioi.mem_nhds hT₁, hSnz] with T hT hST
        have hv0 := hvanish T hT
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at hv0
        have hh : S T * _root_.deriv (v top) T + lowSum T = 0 := by
          simpa [S, lowSum, Finset.sum_apply] using hv0
        change (-1 : ℂ) * lowSum T * (S T)⁻¹ = _root_.deriv (v top) T
        field_simp [hST]; linear_combination -hh
      · exact low i hi
    have hdS : Gen (_root_.deriv S) := by
      let D (i : Fin (n + 1)) (T : ℝ) :=
        MvPolynomial.eval (fun j => v j T) (MvPolynomial.pderiv i (MvPolynomial.pderiv top A))
      have hD (i) : Gen (D i) := Generated.evalPoly v gv _
      refine (Generated.finsetSum Finset.univ _ fun i _ => (hD i).mul (dv i)).congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds hT₁] with T hT
      simpa [D, Finset.sum_apply] using
        (polynomial_chain (MvPolynomial.pderiv top A) v (fun i => _root_.deriv (v i)) T
          (fun i => (hv_diff T hT i).hasDerivAt)).deriv.symm
    have hsmooth : ∀ᶠ T in 𝓝 T₁, ∀ i, DifferentiableAt ℝ (uState i) T := by
      filter_upwards [isOpen_Ioi.mem_nhds hT₁, hSnz] with T hT hST i
      rcases i with i | i
      · exact hv_diff T hT i
      · fin_cases i
        · exact Complex.ofRealCLM.differentiableAt
        · exact (hS_diff T hT).inv hST
    have hclosed : ∀ i, Gen (_root_.deriv (uState i)) := by
      intro i
      rcases i with i | i
      · exact dv i
      · fin_cases i
        · exact (gc 1).congr (Eventually.of_forall fun T => (Complex.ofRealCLM.hasDerivAt.deriv).symm)
        · refine (((gc (-1)).mul hdS).mul (ginvS.pow 2)).congr ?_
          filter_upwards [isOpen_Ioi.mem_nhds hT₁, hSnz] with T hT hST
          have hi := ((hS_diff T hT).hasDerivAt.inv hST).deriv
          have hfun : invS = S⁻¹ := rfl
          change (-1 : ℂ) * _root_.deriv S T * ((S T)⁻¹) ^ 2 = _root_.deriv invS T
          rw [hfun, hi]; field_simp [hST]
    -- Read out P(T) = -2 * T * E(1 / (2 * T)) = -2 * T * v 1!
    have gP : Gen (fun T => (P T : ℂ)) := by
      refine (((gc (-2)).mul gT).mul (gv ⟨1, by omega⟩)).congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds hT₁] with T hT
      have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
      change (-2 : ℂ) * (T : ℂ) * iteratedDeriv 0 (fun l : ℝ => (casimirEnergy P l : ℂ)) (1 / (2 * T)) = (P T : ℂ)
      rw [iteratedDeriv_zero]
      unfold casimirEnergy
      have hinv : 1 / (2 * (1 / (2 * T))) = T := by field_simp [hT.ne']
      rw [hinv]; push_cast; field_simp [hTne]
    obtain ⟨R₀, hR₀_ne, hR₀_nhds⟩ := autonomous_readout uState T₁ (fun T => (P T : ℂ)) gP hsmooth hclosed
    let N := Fintype.card (Fin (n + 1) ⊕ Fin 2)
    let evalR₀ : ℝ → ℂ := fun T =>
      MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val (fun t : ℝ => (P t : ℂ)) T) R₀
    have heval_an : AnalyticOnNhd ℝ evalR₀ (Set.Ioi 0) := by
      intro T hT
      clear hR₀_ne hR₀_nhds
      dsimp only [evalR₀]
      induction R₀ using MvPolynomial.induction_on with
      | C a => simpa using analyticAt_const
      | add A B hA hB => simp only [map_add]; exact hA.add hB
      | mul_X A j hA =>
        have hjet : AnalyticAt ℝ (iteratedDeriv j.val (fun t : ℝ => (P t : ℂ))) T := by
          rw [iteratedDeriv_eq_iterate]; exact (hP_an.iterated_deriv j.val) T hT
        simp only [map_mul, MvPolynomial.eval_X]
        exact hA.mul hjet
    have heval_zero : Set.EqOn evalR₀ 0 (Set.Ioi 0) :=
      heval_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Ioi hT₁
        ((Filter.Eventually.filter_mono nhdsWithin_le_nhds hR₀_nhds).frequently)
    let R₀_poly : MvPolynomial (Fin (N + 1)) (Polynomial ℂ) := MvPolynomial.map Polynomial.C R₀
    have hR₀_poly_ne : R₀_poly ≠ 0 := by
      intro h0; apply hR₀_ne; ext α
      have := congrArg (fun M => M.coeff α) h0
      simpa [R₀_poly, MvPolynomial.coeff_map, Polynomial.C_eq_zero] using this
    have hR₀_poly_zero : ∀ T : ℝ, 0 < T →
        MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val (fun t : ℝ => (P t : ℂ)) T)
          (evalU R₀_poly (T : ℂ)) = 0 := by
      intro T hT
      have hev_id : evalU R₀_poly (T : ℂ) = R₀ := by
        dsimp only [evalU, R₀_poly]
        rw [MvPolynomial.map_map]
        have hcomp : (Polynomial.evalRingHom (T : ℂ)).comp Polynomial.C = RingHom.id ℂ := by ext; simp
        rw [hcomp, MvPolynomial.map_id]
      rw [hev_id]; exact heval_zero hT
    exact hR₀_poly_ne (hP_no_ade R₀_poly hR₀_poly_zero)
  exact fun {r} => hE_no

/-- **General Thermal-to-Casimir Differential-Transcendence Transfer**:
If `P : ℝ → ℝ` is real-analytic on `(0, ∞)` and satisfies no nonzero ADE over `ℂ[T]`,
then BOTH the dual Casimir energy `E(L) = -L P(1/(2L))` AND the Casimir force `F(L) = -E'(L)`
satisfy NO nonzero ADE over `ℂ(L)` on `(0, ∞)`. -/
theorem casimirEnergy_and_force_no_rat_ade {P : ℝ → ℝ}
    (hP_an : AnalyticOnNhd ℝ (fun T : ℝ => (P T : ℂ)) (Set.Ioi 0))
    (hP_no_ade : ∀ {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)),
      (∀ T : ℝ, 0 < T →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (P t : ℂ)) T)
          (evalU Q (T : ℂ)) = 0) → Q = 0) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L →
        (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy P l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) →
      R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L →
        (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirForce P l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) →
      R = 0) := by
  have hE_no := @casimirEnergy_no_rat_ade P hP_an hP_no_ade
  have hE_real_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (casimirEnergy P) (Set.Ioi 0) := by
    have hE_an : AnalyticOnNhd ℝ (fun l : ℝ => (casimirEnergy P l : ℂ)) (Set.Ioi 0) := by
      intro l hl
      have hl' : 0 < l := hl
      have hinv : AnalyticAt ℝ (fun x : ℝ => (1 : ℝ) / (2 * x)) l :=
        analyticAt_const.div (analyticAt_const.mul analyticAt_id) (by positivity)
      have hcomp : AnalyticAt ℝ (fun x : ℝ => (P (1 / (2 * x)) : ℂ)) l :=
        AnalyticAt.comp (g := fun T : ℝ => (P T : ℂ)) (f := fun x : ℝ => (1 : ℝ) / (2 * x))
          (hP_an (1 / (2 * l)) (show (0 : ℝ) < 1 / (2 * l) by positivity)) hinv
      have heq : (fun x : ℝ => (casimirEnergy P x : ℂ)) = fun x : ℝ => -(x : ℂ) * (P (1 / (2 * x)) : ℂ) := by
        funext x; unfold casimirEnergy; push_cast; ring
      rw [heq]
      exact (Complex.ofRealCLM.analyticAt l).neg.mul hcomp
    have hre : AnalyticOnNhd ℝ (casimirEnergy P) (Set.Ioi 0) := by
      intro l hl
      have h1 : AnalyticAt ℝ (fun x : ℝ => ((casimirEnergy P x : ℂ)).re) l :=
        AnalyticAt.comp (g := fun z : ℂ => z.re) (f := fun x : ℝ => (casimirEnergy P x : ℂ))
          (Complex.reCLM.analyticAt (casimirEnergy P l : ℂ)) (hE_an l hl)
      simpa using h1
    exact hre.contDiffOn isOpen_Ioi.uniqueDiffOn
  have hE'_no : ∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L →
        (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (soundSpeedSq (casimirEnergy P) l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) →
      R = 0 := fun {r} R hR =>
    soundSpeedSq_no_rat_ade_of_eos isOpen_Ioi hE_real_smooth
      (fun {r'} R' hR' => hE_no R' fun L hL => hR' L hL)
      R (fun L hL => hR L hL)
  refine ⟨hE_no, fun {r} R hR => neg_fun_no_rat_ade (g := soundSpeedSq (casimirEnergy P)) hE'_no R fun L hL hden => ?_⟩
  have hf : (fun l : ℝ => ((-soundSpeedSq (casimirEnergy P) l) : ℂ)) =
      fun l : ℝ => (casimirForce P l : ℂ) := by
    funext l; unfold casimirForce soundSpeedSq; push_cast; rfl
  rw [hf]
  exact hR L hL hden

/-- **Odd Dimensions (`d = 1` and `d = 3`) — Massive Casimir Energy & Force Differential Transcendence**:
For every positive mass `m > 0`, the massive parallel-plate Casimir energy `E_C^{(d)}(L)` and
Casimir force `F_C^{(d)}(L)` satisfy NO nonzero ADE over `ℂ(L)` in `d = 1` and `d = 3`. -/
theorem casimir1D_no_rat_ade {m : ℝ} (hm : 0 < m) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy1D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirForce1D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) :=
  casimirEnergy_and_force_no_rat_ade (bosePressure1D_analyticOnNhd hm) (fun Q hQ => bosePressure1D_no_ade hm Q hQ)

theorem casimir3D_no_rat_ade {m : ℝ} (hm : 0 < m) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy3D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirForce3D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) :=
  casimirEnergy_and_force_no_rat_ade (bosePressure3D_analyticOnNhd hm) (fun Q hQ => bosePressure3D_no_ade hm Q hQ)

/-! ### 4A. Thermal Conformal Scalar on `S¹ × S¹` and `S³ × S¹`: D-Algebraicity -/

open UpperHalfPlane hiding I
open EisensteinSeries ModularForm Derivative

/-- **Thermal Conformal Scalar on `S¹ × S¹` (`d = 2`) — Chazy Order-3 ODE for `E₂`**:
The quasi-modular Eisenstein series `E₂` (controlling `q ∂_q log Z_{S¹}(q)`) satisfies
Chazy's 3-monomial autonomous order-3 ODE `2 D³ E₂ - 2 E₂ D² E₂ + 3 (D E₂)² = 0` on `ℍ`. -/
theorem circleS1ChazyODE :
    ∀ z : ℍ,
      2 * (D^[3] E2 z) - 2 * E2 z * (D^[2] E2 z) + 3 * (D E2 z) ^ 2 = 0 := by
  have hE2 : MDiff E2 := E2_mdifferentiable
  have hE4 : MDiff (E₄ : ℍ → ℂ) := E₄.holo'
  have hE6 : MDiff (E₆ : ℍ → ℂ) := E₆.holo'
  have hD1 : D E2 = (12⁻¹ : ℂ) • (E2 ^ 2 - (E₄ : ℍ → ℂ)) := normalizedDerivOfComplex_E₂
  have hD2 : D^[2] E2 = fun z : ℍ =>
      ((E2 z) ^ 3 - 3 * E2 z * E₄ z + 2 * E₆ z) / 72 := by
    change D (D E2) = _
    rw [hD1, normalizedDerivOfComplex_smul _ _ ((hE2.pow 2).sub hE4),
      normalizedDerivOfComplex_sub _ _ (hE2.pow 2) hE4,
      normalizedDerivOfComplex_pow _ 2 hE2, normalizedDerivOfComplex_E₂,
      normalizedDerivOfComplex_E₄]
    ext z
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      Nat.cast_ofNat, smul_eq_mul, show ((2 : ℍ → ℂ) z) = 2 from rfl]
    ring
  have hD3 : D^[3] E2 = fun z : ℍ =>
      ((E2 z) ^ 4 - 6 * (E2 z) ^ 2 * E₄ z + 8 * E2 z * E₆ z - 3 * (E₄ z) ^ 2) / 288 := by
    change D (D^[2] E2) = _
    rw [hD2]
    have hsplit : (fun z : ℍ => ((E2 z) ^ 3 - 3 * E2 z * E₄ z + 2 * E₆ z) / 72) =
        (72⁻¹ : ℂ) • (E2 ^ 3 - (3 : ℂ) • (E2 * (E₄ : ℍ → ℂ)) + (2 : ℂ) • (E₆ : ℍ → ℂ)) := by
      ext z; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]; ring
    rw [hsplit,
      normalizedDerivOfComplex_smul _ _ (((hE2.pow 3).sub ((hE2.mul hE4).const_smul 3)).add (hE6.const_smul 2)),
      normalizedDerivOfComplex_add _ _ ((hE2.pow 3).sub ((hE2.mul hE4).const_smul 3)) (hE6.const_smul 2),
      normalizedDerivOfComplex_sub _ _ (hE2.pow 3) ((hE2.mul hE4).const_smul 3),
      normalizedDerivOfComplex_pow _ 3 hE2,
      normalizedDerivOfComplex_smul _ _ (hE2.mul hE4),
      normalizedDerivOfComplex_mul _ _ hE2 hE4,
      normalizedDerivOfComplex_smul _ _ hE6,
      normalizedDerivOfComplex_E₂, normalizedDerivOfComplex_E₄, normalizedDerivOfComplex_E₆]
    ext z
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      Nat.cast_ofNat, smul_eq_mul, show ((3 : ℍ → ℂ) z) = 3 from rfl]
    ring
  intro z
  rw [hD3, hD2, hD1]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
  ring

/-- Exact 8-monomial autonomous order-3 differential polynomial annihilating the weight-4
Eisenstein series `E₄ = 1 + 240 ∑ σ₃(n) q^n` (governing the free conformal scalar on `S³ × S¹`
on `S³ × S¹`):
`80 Y₀³ Y₂² - 200 Y₀² Y₁² Y₂ - 80 Y₀² Y₃² + 125 Y₀ Y₁⁴ + 720 Y₀ Y₁ Y₂ Y₃ - 576 Y₀ Y₂³ - 600 Y₁³ Y₃ + 540 Y₁² Y₂²`. -/
@[expose] def sphereS3E4Poly : MvPolynomial (Fin 4) ℂ :=
  80 * X 0 ^ 3 * X 2 ^ 2 - 200 * X 0 ^ 2 * X 1 ^ 2 * X 2 - 80 * X 0 ^ 2 * X 3 ^ 2 +
    125 * X 0 * X 1 ^ 4 + 720 * X 0 * X 1 * X 2 * X 3 - 576 * X 0 * X 2 ^ 3 -
    600 * X 1 ^ 3 * X 3 + 540 * X 1 ^ 2 * X 2 ^ 2

theorem sphereS3E4Poly_ne_zero : sphereS3E4Poly ≠ 0 := by
  intro h0
  have hev := congrArg (MvPolynomial.eval ![1, 0, 0, 1]) h0
  simp [sphereS3E4Poly] at hev

/-- **Thermal Conformal Scalar on `S³ × S¹` (`d = 4`) — Autonomous Order-3 ODE for `E₄` on `ℍ`**:
The weight-4 Eisenstein series `E₄` satisfies the 8-monomial autonomous order-3 polynomial ODE
`sphereS3E4Poly(E₄, D E₄, D² E₄, D³ E₄) = 0` at every `z ∈ ℍ`. -/
theorem sphereS3E4_ode_upperHalfPlane :
    ∀ z : ℍ,
      MvPolynomial.eval (fun j : Fin 4 => (D^[j.val] (E₄ : ℍ → ℂ)) z) sphereS3E4Poly = 0 := by
  have hE2 : MDiff E2 := E2_mdifferentiable
  have hE4 : MDiff (E₄ : ℍ → ℂ) := E₄.holo'
  have hE6 : MDiff (E₆ : ℍ → ℂ) := E₆.holo'
  have hD1 : D (E₄ : ℍ → ℂ) = fun z : ℍ => (E2 z * E₄ z - E₆ z) / 3 := by
    rw [normalizedDerivOfComplex_E₄]; ext z; simp [div_eq_mul_inv, mul_comm]
  have hD2 : D^[2] (E₄ : ℍ → ℂ) = fun z : ℍ =>
      (5 * (E2 z) ^ 2 * E₄ z - 10 * E2 z * E₆ z + 5 * (E₄ z) ^ 2) / 36 := by
    change D (D (E₄ : ℍ → ℂ)) = _
    rw [normalizedDerivOfComplex_E₄,
      normalizedDerivOfComplex_smul _ _ ((hE2.mul hE4).sub hE6),
      normalizedDerivOfComplex_sub _ _ (hE2.mul hE4) hE6,
      normalizedDerivOfComplex_mul _ _ hE2 hE4,
      normalizedDerivOfComplex_E₂, normalizedDerivOfComplex_E₄, normalizedDerivOfComplex_E₆]
    ext z
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    ring
  have hD3 : D^[3] (E₄ : ℍ → ℂ) = fun z : ℍ =>
      (5 * (E2 z) ^ 3 * E₄ z - 15 * (E2 z) ^ 2 * E₆ z + 15 * E2 z * (E₄ z) ^ 2 - 5 * E₄ z * E₆ z) / 72 := by
    change D (D^[2] (E₄ : ℍ → ℂ)) = _
    rw [hD2]
    have hsplit : (fun z : ℍ => (5 * (E2 z) ^ 2 * E₄ z - 10 * E2 z * E₆ z + 5 * (E₄ z) ^ 2) / 36) =
        (36⁻¹ : ℂ) • ((5 : ℂ) • (E2 ^ 2 * (E₄ : ℍ → ℂ)) - (10 : ℂ) • (E2 * (E₆ : ℍ → ℂ)) +
          (5 : ℂ) • ((E₄ : ℍ → ℂ) ^ 2)) := by
      ext z; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]; ring
    rw [hsplit,
      normalizedDerivOfComplex_smul _ _
        ((((hE2.pow 2).mul hE4).const_smul 5).sub ((hE2.mul hE6).const_smul 10) |>.add ((hE4.pow 2).const_smul 5)),
      normalizedDerivOfComplex_add _ _
        ((((hE2.pow 2).mul hE4).const_smul 5).sub ((hE2.mul hE6).const_smul 10)) ((hE4.pow 2).const_smul 5),
      normalizedDerivOfComplex_sub _ _ (((hE2.pow 2).mul hE4).const_smul 5) ((hE2.mul hE6).const_smul 10),
      normalizedDerivOfComplex_smul _ _ ((hE2.pow 2).mul hE4),
      normalizedDerivOfComplex_mul _ _ (hE2.pow 2) hE4,
      normalizedDerivOfComplex_pow _ 2 hE2,
      normalizedDerivOfComplex_smul _ _ (hE2.mul hE6),
      normalizedDerivOfComplex_mul _ _ hE2 hE6,
      normalizedDerivOfComplex_smul _ _ (hE4.pow 2),
      normalizedDerivOfComplex_pow _ 2 hE4,
      normalizedDerivOfComplex_E₂, normalizedDerivOfComplex_E₄, normalizedDerivOfComplex_E₆]
    ext z
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      Nat.cast_ofNat, smul_eq_mul, show ((2 : ℍ → ℂ) z) = 2 from rfl]
    ring
  intro z
  simp only [sphereS3E4Poly, map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X,
    Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl,
    Function.iterate_zero, id_eq, Function.iterate_one]
  rw [hD3, hD2, hD1]
  ring

/-- Pure arithmetic proof of `bernoulli 4 = -1 / 30` (using `sum_bernoulli`, zero `decide +kernel`). -/
private lemma bernoulli_four_eq : bernoulli 4 = -(1 / 30 : ℚ) := by
  have h5 := sum_bernoulli 5
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h5
  have hb0 : bernoulli 0 = 1 := bernoulli_zero
  have hb1 : bernoulli 1 = -(1 / 2 : ℚ) := by rw [bernoulli_one]; norm_num
  have hb2 : bernoulli 2 = 1 / 6 := by rw [bernoulli_two]; norm_num
  have hb3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by omega)
  rw [hb0, hb1, hb2, hb3] at h5
  norm_num [Nat.choose] at h5
  linarith

/-- Formal Euler operator `θ S = X * derivative S` on `PowerSeries ℂ`. -/
@[expose] def thetaPS (S : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.derivative S

private lemma thetaPS_polyBound {S : PowerSeries ℂ} (hS : PolyCoeffBound S) :
    PolyCoeffBound (thetaPS S) := by
  rcases hS with ⟨C, d, hC, hbd⟩
  refine ⟨C, d + 1, hC, fun n => ?_⟩
  cases n with
  | zero =>
    simp only [thetaPS, PowerSeries.coeff_zero_X_mul, norm_zero]
    positivity
  | succ k =>
    rw [thetaPS, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    rw [norm_mul, show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; rfl,
      Complex.norm_natCast, mul_comm]
    have h1 := hbd (k + 1)
    have hle : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1 := by linarith
    calc ((k + 1 : ℕ) : ℝ) * ‖PowerSeries.coeff (k + 1) S‖
        ≤ ((k + 1 : ℕ) : ℝ) * (C * (((k + 1 : ℕ) : ℝ) + 1) ^ d) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ ≤ (((k + 1 : ℕ) : ℝ) + 1) * (C * (((k + 1 : ℕ) : ℝ) + 1) ^ d) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = C * (((k + 1 : ℕ) : ℝ) + 1) ^ (d + 1) := by rw [pow_succ]; ring

private lemma polyBound_add {F G : PowerSeries ℂ} (hF : PolyCoeffBound F) (hG : PolyCoeffBound G) :
    PolyCoeffBound (F + G) := by
  rcases hF with ⟨CF, dF, hCF, hbF⟩
  rcases hG with ⟨CG, dG, hCG, hbG⟩
  refine ⟨CF + CG, max dF dG, by positivity, fun n => ?_⟩
  rw [map_add]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  calc ‖PowerSeries.coeff n F + PowerSeries.coeff n G‖
      ≤ ‖PowerSeries.coeff n F‖ + ‖PowerSeries.coeff n G‖ := norm_add_le _ _
    _ ≤ CF * ((n : ℝ) + 1) ^ dF + CG * ((n : ℝ) + 1) ^ dG := add_le_add (hbF n) (hbG n)
    _ ≤ CF * ((n : ℝ) + 1) ^ max dF dG + CG * ((n : ℝ) + 1) ^ max dF dG :=
        add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (le_max_left _ _)) hCF)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (le_max_right _ _)) hCG)
    _ = (CF + CG) * ((n : ℝ) + 1) ^ max dF dG := by ring

private lemma polyBound_const (c : ℂ) : PolyCoeffBound (PowerSeries.C c) := by
  refine ⟨‖c‖, 0, norm_nonneg c, fun n => ?_⟩
  cases n with
  | zero => simp
  | succ k => simp

private lemma polyBound_const_mul (c : ℂ) {F : PowerSeries ℂ} (hF : PolyCoeffBound F) :
    PolyCoeffBound (PowerSeries.C c * F) := by
  rcases hF with ⟨CF, dF, hCF, hbF⟩
  refine ⟨‖c‖ * CF, dF, by positivity, fun n => ?_⟩
  rw [PowerSeries.coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖PowerSeries.coeff n F‖ ≤ ‖c‖ * (CF * ((n : ℝ) + 1) ^ dF) :=
        mul_le_mul_of_nonneg_left (hbF n) (norm_nonneg c)
    _ = ‖c‖ * CF * ((n : ℝ) + 1) ^ dF := by ring

private lemma polyBound_mul {F G : PowerSeries ℂ} (hF : PolyCoeffBound F) (hG : PolyCoeffBound G) :
    PolyCoeffBound (F * G) := by
  rcases hF with ⟨CF, dF, hCF, hbF⟩
  rcases hG with ⟨CG, dG, hCG, hbG⟩
  refine ⟨CF * CG, dF + dG + 1, by positivity, fun n => ?_⟩
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i F * PowerSeries.coeff j G) n]
  calc ‖∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff (n - k) G‖
      ≤ ∑ k ∈ Finset.range (n + 1), ‖PowerSeries.coeff k F * PowerSeries.coeff (n - k) G‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n + 1), (CF * ((n : ℝ) + 1) ^ dF) * (CG * ((n : ℝ) + 1) ^ dG) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1 : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkn
        have h2 : ((n - k : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          exact_mod_cast Nat.succ_le_succ (Nat.sub_le n k)
        rw [norm_mul]
        exact mul_le_mul
          ((hbF k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 dF) hCF))
          ((hbG (n - k)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 dG) hCG))
          (norm_nonneg _) (by positivity)
    _ = ((Finset.range (n + 1)).card : ℝ) * ((CF * ((n : ℝ) + 1) ^ dF) * (CG * ((n : ℝ) + 1) ^ dG)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = CF * CG * ((n : ℝ) + 1) ^ (dF + dG + 1) := by
        rw [Finset.card_range, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]; ring

private lemma polyBound_X : PolyCoeffBound (PowerSeries.X : PowerSeries ℂ) := by
  refine ⟨1, 0, zero_le_one, fun n => ?_⟩
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

private lemma value_eq_zero_of_exp_neg_ray {S : PowerSeries ℂ} (hS : DiskCoeffBound S)
    (hzero : ∀ t : ℝ, 0 < t → value S (Complex.exp (-(t : ℂ))) = 0) : S = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strongRecOn with
  | ind n ih =>
    -- Subtract off terms < n (all 0 by ih), divide by exp(-n t), let t → +∞!
    have hq_lt : ∀ t : ℝ, 0 < t → ‖Complex.exp (-(t : ℂ))‖ < 1 := fun t ht => by
      rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
    have hcoeff_bd : ∀ t : ℝ, 1 ≤ t →
        ‖PowerSeries.coeff n S‖ ≤
          (∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) * Real.exp (-t) := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have hqt : Complex.exp (-(t : ℂ)) = (Real.exp (-t) : ℂ) := by
        rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_exp]
      have habs : AbsAt S (Complex.exp (-(t : ℂ))) := by
        simpa [seriesJet] using seriesJet_abs hS 0 (hq_lt t ht_pos)
      have hsumm : Summable (term S (Complex.exp (-(t : ℂ)))) := habs.of_norm
      have hsplit := hsumm.sum_add_tsum_nat_add (n + 1)
      have hsum_head : ∑ k ∈ Finset.range (n + 1), term S (Complex.exp (-(t : ℂ))) k =
          PowerSeries.coeff n S * (Complex.exp (-(t : ℂ))) ^ n := by
        rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk => by
          simp [term, ih k (Finset.mem_range.mp hk)]), zero_add, term]
      have hval0 : value S (Complex.exp (-(t : ℂ))) = 0 := hzero t ht_pos
      unfold value at hval0
      rw [← hsplit, hsum_head] at hval0
      have hpow_ne : (Complex.exp (-(t : ℂ))) ^ n ≠ 0 := pow_ne_zero n (Complex.exp_ne_zero _)
      have hnorm_eq : ‖PowerSeries.coeff n S‖ * (Real.exp (-t)) ^ n =
          ‖∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖ := by
        have h1 : PowerSeries.coeff n S * (Complex.exp (-(t : ℂ))) ^ n =
            -(∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))) := eq_neg_of_add_eq_zero_left hval0
        have h2 := congrArg norm h1
        rw [norm_mul, norm_pow, norm_neg] at h2
        have hnexp : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
          rw [hqt, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        rw [hnexp] at h2
        exact h2
      have habs1 : AbsAt S (Real.exp (-1) : ℂ) := by
        simpa [seriesJet] using seriesJet_abs hS 0 (q := (Real.exp (-1) : ℂ)) (by
          rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          exact Real.exp_lt_one_iff.mpr (by norm_num))
      have hdom : Summable (fun k : ℕ => ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) := by
        have h1 : Summable (fun k : ℕ => ‖term S (Real.exp (-1) : ℂ) (k + (n + 1))‖) :=
          (summable_nat_add_iff (f := fun j => ‖term S (Real.exp (-1) : ℂ) j‖) (n + 1)).2 habs1
        have h2 : Summable (fun k : ℕ =>
            (‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ (k + (n + 1))) *
              ((Real.exp (-1)) ^ (n + 1))⁻¹) := by
          refine (h1.mul_right ((Real.exp (-1)) ^ (n + 1))⁻¹).congr fun k => ?_
          simp only [term, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        refine h2.congr fun k => ?_
        have hne : (Real.exp (-1)) ^ (n + 1) ≠ 0 := pow_ne_zero _ (Real.exp_pos _).ne'
        rw [pow_add]; field_simp [hne]
      have htail_norm : Summable (fun k : ℕ => ‖term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖) :=
        (summable_nat_add_iff (n + 1)).2 habs
      have hle_tail : ‖∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖ ≤
          (Real.exp (-t)) ^ n * ((∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) *
            Real.exp (-t)) := by
        have hstep : ∀ k : ℕ, ‖term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖ ≤
            (Real.exp (-t)) ^ n * Real.exp (-t) *
              (‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) := fun k => by
          dsimp only [term]
          rw [norm_mul, norm_pow, hqt, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          have hpow_split : (Real.exp (-t)) ^ (k + (n + 1)) =
              (Real.exp (-t)) ^ n * Real.exp (-t) * (Real.exp (-t)) ^ k := by
            rw [pow_add, pow_succ]; ring
          rw [hpow_split]
          have he : Real.exp (-t) ^ k ≤ Real.exp (-1) ^ k :=
            pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) k
          have hnn : 0 ≤ ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-t) ^ n * Real.exp (-t)) := by positivity
          calc ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-t) ^ n * Real.exp (-t) * Real.exp (-t) ^ k)
              = (‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-t) ^ n * Real.exp (-t))) * Real.exp (-t) ^ k := by ring
            _ ≤ (‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-t) ^ n * Real.exp (-t))) * Real.exp (-1) ^ k :=
                mul_le_mul_of_nonneg_left he hnn
            _ = Real.exp (-t) ^ n * Real.exp (-t) * (‖PowerSeries.coeff (k + (n + 1)) S‖ * Real.exp (-1) ^ k) := by ring
        calc ‖∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖
            ≤ ∑' k : ℕ, ‖term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖ := norm_tsum_le_tsum_norm htail_norm
          _ ≤ ∑' k : ℕ, Real.exp (-t) ^ n * Real.exp (-t) *
                (‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) :=
              htail_norm.tsum_le_tsum hstep (hdom.mul_left _)
          _ = Real.exp (-t) ^ n * Real.exp (-t) *
                ∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k := tsum_mul_left
          _ = _ := by ring
      rw [← hnorm_eq] at hle_tail
      have hpos : 0 < (Real.exp (-t)) ^ n := pow_pos (Real.exp_pos _) n
      exact le_of_mul_le_mul_right (by linarith) hpos
    -- Let t → +∞!
    set C := ∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k
    have htend : Tendsto (fun t : ℝ => C * Real.exp (-t)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
    have hnorm0 : ‖PowerSeries.coeff n S‖ ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htend (Filter.eventually_atTop.mpr ⟨(1 : ℝ), hcoeff_bd⟩)
    exact norm_le_zero_iff.mp hnorm0

/-- Formal `q`-series of `E₄`: `1 + 240 · L₃(q) = 1 + 240 ∑_{n ≥ 1} σ₃(n) q^n`. -/
@[expose] def E4Series : PowerSeries ℂ :=
  1 + PowerSeries.C (240 : ℂ) * sigmaSeries 3

private lemma E4Series_polyBound : PolyCoeffBound E4Series :=
  polyBound_add (by simpa using polyBound_const (1 : ℂ))
    (polyBound_const_mul 240 (sigmaSeries_polyBound 3))

private lemma E4Series_theta_ray (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (D^[k] (E₄ : ℍ → ℂ)) ⟨(Complex.I / (2 * (Real.pi : ℂ))) * (t : ℂ), by
      have hre : ((Complex.I / (2 * (Real.pi : ℂ))) * (t : ℂ)).im = t / (2 * Real.pi) := by
        rw [div_eq_mul_inv, mul_assoc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
        have h1 : (((2 * (Real.pi : ℂ))⁻¹ * (t : ℂ))).re = (2 * Real.pi)⁻¹ * t := by
          have : (2 * (Real.pi : ℂ))⁻¹ * (t : ℂ) = (((2 * Real.pi)⁻¹ * t : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.ofReal_re]
        rw [h1]; ring
      rw [hre]; positivity⟩ =
      value (thetaPS^[k] E4Series) (Complex.exp (-(t : ℂ))) := by
  let τ : ℝ → ℍ := fun s =>
    if hs : 0 < s then
      ⟨(Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ), by
        have hre : ((Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ)).im = s / (2 * Real.pi) := by
          rw [div_eq_mul_inv, mul_assoc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
          have h1 : (((2 * (Real.pi : ℂ))⁻¹ * (s : ℂ))).re = (2 * Real.pi)⁻¹ * s := by
            have : (2 * (Real.pi : ℂ))⁻¹ * (s : ℂ) = (((2 * Real.pi)⁻¹ * s : ℝ) : ℂ) := by push_cast; ring
            rw [this, Complex.ofReal_re]
          rw [h1]; ring
        rw [hre]; positivity⟩
    else ⟨Complex.I, by simp⟩
  suffices h : ∀ s : ℝ, 0 < s → (D^[k] (E₄ : ℍ → ℂ)) (τ s) = value (thetaPS^[k] E4Series) (Complex.exp (-(s : ℂ))) by
    simpa [τ, ht] using h t ht
  induction k with
  | zero =>
    intro s hs
    simp only [Function.iterate_zero, id_eq]
    have hτ_val : (τ s : ℂ) = (Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ) := by simp [τ, hs]
    have hq_val : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ s : ℂ)) = Complex.exp (-(s : ℂ)) := by
      rw [hτ_val]
      congr 1
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp [hpi]
      rw [Complex.I_sq]; ring
    have hq_exp := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) (τ s)
    change (E (by simp : 3 ≤ 4) (τ s) : ℂ) = value E4Series (Complex.exp (-(s : ℂ)))
    rw [hq_exp, bernoulli_four_eq]
    rw [show (1 : ℂ) - 2 * ↑(4 : ℕ) / ↑(-(1 / 30 : ℚ)) *
        ∑' n : ℕ+, (ArithmeticFunction.sigma (4 - 1) n : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ s : ℂ)) ^ (n : ℤ) =
        1 + 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma (4 - 1) n : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ s : ℂ)) ^ (n : ℤ) by
      push_cast; ring]
    have hq_lt : ‖Complex.exp (-(s : ℂ))‖ < 1 := by
      rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
    have hsum_eq : (∑' n : ℕ+, (ArithmeticFunction.sigma (4 - 1) n : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ s : ℂ)) ^ (n : ℤ)) =
        value (sigmaSeries 3) (Complex.exp (-(s : ℂ))) := by
      rw [hq_val]
      have hnat : (∑' n : ℕ+, (ArithmeticFunction.sigma (4 - 1) n : ℂ) *
          Complex.exp (-(s : ℂ)) ^ (n : ℤ)) =
          ∑' n : ℕ, term (sigmaSeries 3) (Complex.exp (-(s : ℂ))) n := by
        rw [← tsum_zero_pnat_eq_tsum_nat
          ((by simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound 3).to_diskCoeffBound 0 hq_lt :
            AbsAt (sigmaSeries 3) (Complex.exp (-(s : ℂ)))).of_norm)]
        simp only [term, sigmaSeries, PowerSeries.coeff_mk, ↓reduceIte, zero_mul, zero_add]
        refine tsum_congr fun n => ?_
        simp only [zpow_natCast, show (n : ℕ) ≠ 0 from n.ne_zero, ↓reduceIte,
          ArithmeticFunction.sigma_apply]
        push_cast; rfl
      exact hnat
    rw [hsum_eq]
    have hE4_val : value E4Series (Complex.exp (-(s : ℂ))) =
        1 + 240 * value (sigmaSeries 3) (Complex.exp (-(s : ℂ))) := by
      let P : MvPolynomial (Fin 1) ℂ := 1 + 240 * MvPolynomial.X 0
      have hP_eq : MvPolynomial.aeval (fun _ : Fin 1 => sigmaSeries 3) P = E4Series := by
        simp [P, E4Series, map_ofNat]
      have h := (polynomial_value P (S := fun _ : Fin 1 => sigmaSeries 3) (q := Complex.exp (-(s : ℂ)))
        (fun _ => by simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound 3).to_diskCoeffBound 0 hq_lt)).2
      rw [hP_eq] at h
      simpa [P] using h
    rw [hE4_val]
  | succ k ih =>
    intro s hs
    have hD_mdiff : MDiff (D^[k] (E₄ : ℍ → ℂ)) := by
      clear ih
      induction k with
      | zero => exact E₄.holo'
      | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact normalizedDerivOfComplex_mdifferentiable ihm
    have hθ_poly : PolyCoeffBound (thetaPS^[k] E4Series) := by
      clear ih hD_mdiff
      induction k with
      | zero => exact E4Series_polyBound
      | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact thetaPS_polyBound ihm
    -- Differentiate both sides of ih at s!
    have hLHS : HasDerivAt (fun u : ℝ => (D^[k] (E₄ : ℍ → ℂ)) (τ u))
        (-(D^[k + 1] (E₄ : ℍ → ℂ)) (τ s)) s := by
      have hτs : (τ s : ℂ) = (Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ) := by simp [τ, hs]
      have hF_diff : DifferentiableAt ℂ ((D^[k] (E₄ : ℍ → ℂ)) ∘ UpperHalfPlane.ofComplex)
          ((Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ)) := by
        rw [← hτs]; exact UpperHalfPlane.mdifferentiableAt_iff.mp (hD_mdiff (τ s))
      have hlin : HasDerivAt (fun u : ℝ => (Complex.I / (2 * (Real.pi : ℂ))) * (u : ℂ))
          (Complex.I / (2 * (Real.pi : ℂ))) s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I / (2 * (Real.pi : ℂ)))
      have hcomp := hF_diff.hasDerivAt.comp s hlin
      have hev : (fun u : ℝ => (D^[k] (E₄ : ℍ → ℂ)) (τ u)) =ᶠ[𝓝 s]
          fun u : ℝ => ((D^[k] (E₄ : ℍ → ℂ)) ∘ UpperHalfPlane.ofComplex)
            ((Complex.I / (2 * (Real.pi : ℂ))) * (u : ℂ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
        have hu' : 0 < u := hu
        have hτu : (τ u : ℂ) = (Complex.I / (2 * (Real.pi : ℂ))) * (u : ℂ) := by simp [τ, hu']
        rw [Function.comp_apply, ← hτu, UpperHalfPlane.ofComplex_apply]
      refine (hcomp.congr_of_eventuallyEq hev).congr_deriv ?_
      rw [Function.iterate_succ_apply', normalizedDerivOfComplex, ← hτs]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp [hpi, Complex.I_ne_zero]
      rw [Complex.I_sq]; ring
    have hRHS : HasDerivAt (fun u : ℝ => value (thetaPS^[k] E4Series) (Complex.exp (-(u : ℂ))))
        (-value (thetaPS^[k + 1] E4Series) (Complex.exp (-(s : ℂ)))) s := by
      have hq_lt : ‖Complex.exp (-(s : ℂ))‖ < 1 := by
        rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
        exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
      have hval_deriv := seriesJet_deriv hθ_poly.to_diskCoeffBound 0 hq_lt
      have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ))) (-Complex.exp (-(s : ℂ))) s := by
        have hlin : HasDerivAt (fun u : ℝ => -(u : ℂ)) (-1 : ℂ) s := by
          have h := (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-1 : ℂ)
          refine h.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp) |>.congr_deriv ?_
          simp
        simpa using hlin.cexp
      have hcomp := hval_deriv.comp s hexp
      refine hcomp.congr_deriv ?_
      have hmul_val : value (thetaPS^[k + 1] E4Series) (Complex.exp (-(s : ℂ))) =
          Complex.exp (-(s : ℂ)) * value (PowerSeries.derivative (thetaPS^[k] E4Series)) (Complex.exp (-(s : ℂ))) := by
        rw [Function.iterate_succ_apply', thetaPS]
        let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 * MvPolynomial.X 1
        have h1 := (polynomial_value P (S := ![PowerSeries.X, PowerSeries.derivative (thetaPS^[k] E4Series)])
          (q := Complex.exp (-(s : ℂ))) (fun i => by
            fin_cases i
            · exact (nome_abs _).1
            · simpa [seriesJet] using seriesJet_abs hθ_poly.to_diskCoeffBound 1 hq_lt)).2
        simpa [P, (nome_abs _).2] using h1
      rw [hmul_val]; simp [seriesJet]; ring
    have hev : (fun u : ℝ => (D^[k] (E₄ : ℍ → ℂ)) (τ u)) =ᶠ[𝓝 s]
        fun u : ℝ => value (thetaPS^[k] E4Series) (Complex.exp (-(u : ℂ))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu; exact ih u hu
    have heq := (hLHS.congr_of_eventuallyEq hev.symm).unique hRHS
    exact neg_inj.mp heq

/-- Formal power-series ODE for `E4Series = 1 + 240 L₃`: `sphereS3E4Poly(E₄, θ E₄, θ² E₄, θ³ E₄) = 0`
identically in `PowerSeries ℂ`. -/
theorem E4Series_formal_ode :
    MvPolynomial.aeval (fun j : Fin 4 => thetaPS^[j.val] E4Series) sphereS3E4Poly = 0 := by
  let S : PowerSeries ℂ := MvPolynomial.aeval (fun j : Fin 4 => thetaPS^[j.val] E4Series) sphereS3E4Poly
  have hθ_poly : ∀ j : ℕ, PolyCoeffBound (thetaPS^[j] E4Series) := fun j => by
    induction j with
    | zero => exact E4Series_polyBound
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact thetaPS_polyBound ih
  have hS_poly : PolyCoeffBound S := by
    dsimp only [S]
    induction sphereS3E4Poly using MvPolynomial.induction_on with
    | C c =>
      simpa [PowerSeries.algebraMap_eq] using polyBound_const c
    | add A B hA hB =>
      rw [map_add]; exact polyBound_add hA hB
    | mul_X A j hA =>
      rw [map_mul, MvPolynomial.aeval_X]; exact polyBound_mul hA (hθ_poly j.val)
  refine value_eq_zero_of_exp_neg_ray hS_poly.to_diskCoeffBound fun t ht => ?_
  have hq_lt : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hval := (polynomial_value sphereS3E4Poly (S := fun j : Fin 4 => thetaPS^[j.val] E4Series)
    (q := Complex.exp (-(t : ℂ))) (fun j => by
      simpa [seriesJet] using seriesJet_abs (hθ_poly j.val).to_diskCoeffBound 0 hq_lt)).2
  rw [hval]
  let τt : ℍ := ⟨(Complex.I / (2 * (Real.pi : ℂ))) * (t : ℂ), by
    have hre : ((Complex.I / (2 * (Real.pi : ℂ))) * (t : ℂ)).im = t / (2 * Real.pi) := by
      rw [div_eq_mul_inv, mul_assoc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
      have h1 : (((2 * (Real.pi : ℂ))⁻¹ * (t : ℂ))).re = (2 * Real.pi)⁻¹ * t := by
        have : (2 * (Real.pi : ℂ))⁻¹ * (t : ℂ) = (((2 * Real.pi)⁻¹ * t : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [h1]; ring
    rw [hre]; positivity⟩
  have hcoord : (fun j : Fin 4 => value (thetaPS^[j.val] E4Series) (Complex.exp (-(t : ℂ)))) =
      fun j : Fin 4 => (D^[j.val] (E₄ : ℍ → ℂ)) τt := by
    ext j; exact (E4Series_theta_ray j.val ht).symm
  rw [hcoord]
  exact sphereS3E4_ode_upperHalfPlane τt

/-- **Thermal Conformal Scalar on `S³ × S¹` (`d = 4`) — D-Algebraicity of Free-Energy Derivative `L₃(q) = ∑ σ₃(n) q^n`**:
For the free conformal scalar on `S³ × S¹`, `q ∂_q log Z_{S³}(q) = ∑_{n ≥ 1} σ₃(n) q^n = sigmaSeries 3`
is algebraically differentially dependent (D-algebraic) over `ℂ(q)`, witnessed by an explicit
nonzero order-3 polynomial relation in `seriesCoordinates (sigmaSeries 3)`. -/
theorem sphereS3LogDeriv_dAlgebraic :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (sigmaSeries 3)) := by
  rw [algebraicIndependent_iff]
  push Not
  -- Express (E₄, θ E₄, θ² E₄, θ³ E₄) as polynomials in (q, L₃, L₃', L₃'', L₃''') = seriesCoordinates (sigmaSeries 3)!
  let sub : Fin 4 → MvPolynomial ℕ ℂ :=
    ![1 + 240 * X 1,
      240 * (X 0 * X 2),
      240 * (X 0 ^ 2 * X 3 + X 0 * X 2),
      240 * (X 0 ^ 3 * X 4 + 3 * X 0 ^ 2 * X 3 + X 0 * X 2)]
  let Q : MvPolynomial ℕ ℂ := MvPolynomial.aeval sub sphereS3E4Poly
  refine ⟨Q, ?_, ?_⟩
  · -- Show aeval (seriesCoordinates (sigmaSeries 3)) Q = 0 using E4Series_formal_ode!
    have hcomp : MvPolynomial.aeval (seriesCoordinates (sigmaSeries 3)) Q =
        MvPolynomial.aeval (fun j : Fin 4 => MvPolynomial.aeval (seriesCoordinates (sigmaSeries 3)) (sub j))
          sphereS3E4Poly := by
      dsimp only [Q]
      rw [← AlgHom.comp_apply]
      congr 1
      apply MvPolynomial.algHom_ext
      intro j; simp
    rw [hcomp]
    have hmatch : (fun j : Fin 4 => MvPolynomial.aeval (seriesCoordinates (sigmaSeries 3)) (sub j)) =
        fun j : Fin 4 => thetaPS^[j.val] E4Series := by
      have hderiv_C : ∀ c : ℂ, PowerSeries.derivative (PowerSeries.C c) = 0 := fun c => by
        ext n; simp
      have hderiv_X : PowerSeries.derivative (PowerSeries.X : PowerSeries ℂ) = 1 := by
        ext n; simp [PowerSeries.coeff_one]
      have hderiv_mul : ∀ F G : PowerSeries ℂ,
          PowerSeries.derivative (F * G) = PowerSeries.derivative F * G + F * PowerSeries.derivative G := fun F G => by
        rw [(PowerSeries.derivative (R := ℂ)).leibniz F G]; simp [smul_eq_mul]; ring
      have hθ0 : thetaPS^[0] E4Series = 1 + PowerSeries.C (240 : ℂ) * sigmaSeries 3 := rfl
      have hθ1 : thetaPS E4Series =
          PowerSeries.C (240 : ℂ) * (PowerSeries.X * PowerSeries.derivative (sigmaSeries 3)) := by
        rw [thetaPS, E4Series, map_add, Derivation.map_one_eq_zero, zero_add, hderiv_mul, hderiv_C]
        ring
      have hθ2 : thetaPS^[2] E4Series =
          PowerSeries.C (240 : ℂ) * (PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] (sigmaSeries 3)) +
            PowerSeries.X * PowerSeries.derivative (sigmaSeries 3)) := by
        rw [Function.iterate_succ_apply', Function.iterate_one, hθ1, thetaPS]
        rw [hderiv_mul, hderiv_C, zero_mul, zero_add, hderiv_mul, hderiv_X, one_mul,
          Function.iterate_succ_apply', Function.iterate_one]
        ring
      have hθ3 : thetaPS^[3] E4Series =
          PowerSeries.C (240 : ℂ) * (PowerSeries.X ^ 3 * (PowerSeries.derivative^[3] (sigmaSeries 3)) +
            3 * PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] (sigmaSeries 3)) +
            PowerSeries.X * PowerSeries.derivative (sigmaSeries 3)) := by
        rw [Function.iterate_succ_apply', hθ2, thetaPS]
        have hdX2 : PowerSeries.derivative (PowerSeries.X ^ 2 : PowerSeries ℂ) = 2 * PowerSeries.X := by
          rw [sq, hderiv_mul, hderiv_X]; ring
        rw [hderiv_mul, hderiv_C, zero_mul, zero_add, map_add, hderiv_mul, hderiv_mul,
          hdX2, hderiv_X, one_mul,
          show PowerSeries.derivative (PowerSeries.derivative^[2] (sigmaSeries 3)) =
            PowerSeries.derivative^[3] (sigmaSeries 3) from (Function.iterate_succ_apply' _ 2 _).symm,
          show PowerSeries.derivative (PowerSeries.derivative (sigmaSeries 3)) =
            PowerSeries.derivative^[2] (sigmaSeries 3) from (Function.iterate_succ_apply' _ 1 _).symm]
        ring
      ext j
      fin_cases j
      · simp [sub, hθ0, seriesCoordinates, seriesJet, map_ofNat]
      · simp [sub, hθ1, seriesCoordinates, seriesJet, map_ofNat]
      · simp [sub, hθ2, seriesCoordinates, seriesJet, map_ofNat]
      · simp [sub, hθ3, seriesCoordinates, seriesJet, map_ofNat]
    rw [hmatch]
    exact E4Series_formal_ode
  · -- Nonvanishing of Q: evaluate at (X 0 = 1, X 1 = 0, X 2 = 0, X 3 = 0, X 4 = 1)!
    intro h0
    let pt : ℕ → ℂ := fun k => if k = 0 ∨ k = 4 then 1 else 0
    have hev := congrArg (MvPolynomial.eval pt) h0
    have hcomp : MvPolynomial.eval pt Q =
        MvPolynomial.eval (fun j : Fin 4 => MvPolynomial.eval pt (sub j)) sphereS3E4Poly := by
      dsimp only [Q]
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, ← AlgHom.comp_apply]
      congr 1
      apply MvPolynomial.algHom_ext
      intro j; simp
    rw [hcomp, map_zero] at hev
    have hpt : (fun j : Fin 4 => MvPolynomial.eval pt (sub j)) = ![1, 0, 0, 240] := by
      ext j; fin_cases j <;> simp [sub, pt]
    rw [hpt] at hev
    simp [sphereS3E4Poly] at hev

/-- Coefficients of the free conformal scalar partition function on `S³ × S¹`:
`Z_{S³}(q) = ∏_{n ≥ 1} (1 - q^n)^{-n²}`, uniquely determined by `Z(0) = 1` and `q Z'(q) = L₃(q) Z(q)`. -/
@[expose] def sphereS3Coeff : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ k ∈ Finset.range (n + 1), (sigmaNat 3 (k + 1) : ℝ) * sphereS3Coeff (n - k)

/-- Formal thermal partition function `Z_{S³}(q) = ∏_{n ≥ 1} (1 - q^n)^{-n²}` of the free
conformal scalar on `S³ × S¹`. -/
@[expose] def sphereS3PartitionSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (sphereS3Coeff n : ℂ)

theorem sphereS3PartitionSeries_constantCoeff :
    PowerSeries.constantCoeff sphereS3PartitionSeries = 1 := by
  simp [sphereS3PartitionSeries, sphereS3Coeff]

theorem sphereS3PartitionSeries_ode :
    PowerSeries.X * PowerSeries.derivative sphereS3PartitionSeries =
      sigmaSeries 3 * sphereS3PartitionSeries := by
  ext n
  cases n with
  | zero =>
    simp [PowerSeries.coeff_mul, sigmaSeries]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul]
    simp only [sphereS3PartitionSeries, PowerSeries.coeff_mk, sphereS3Coeff]
    have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    push_cast
    rw [mul_comm, ← mul_assoc, mul_one_div_cancel hm1, one_mul]
    conv_rhs =>
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (sigmaSeries 3) * (sphereS3Coeff j : ℂ)) (m + 1),
        Finset.sum_range_succ']
    simp only [sigmaSeries, PowerSeries.coeff_mk, ↓reduceIte, zero_mul, add_zero,
      Nat.succ_ne_zero, Nat.add_sub_add_right, sigmaNat]
    push_cast; rfl

/-- **Thermal Conformal Scalar on `S³ × S¹` (`d = 4`) — D-Algebraicity of the Full Partition Function `Z_{S³}(q)`**:
The conformal scalar thermal partition function `Z_{S³}(q) = ∏_{n ≥ 1} (1 - q^n)^{-n²}` on
`S³ × S¹` is D-algebraic over `ℂ(q)`, witnessed by an explicit nonzero order-4 algebraic
differential equation obtained by substituting `L₃ = q Z' / Z` into the order-3 `E₄` ODE. -/
theorem sphereS3PartitionSeries_dAlgebraic :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates sphereS3PartitionSeries) := by
  rw [algebraicIndependent_iff]
  push Not
  -- Define formal derivation θ_poly on MvPolynomial ℕ ℂ matching q d/dq on (q, Z, Z', Z'', Z''', Z'''')
  let qv : MvPolynomial ℕ ℂ := X 0
  let zv : MvPolynomial ℕ ℂ := X 1
  let z1 : MvPolynomial ℕ ℂ := X 2
  let z2 : MvPolynomial ℕ ℂ := X 3
  let z3 : MvPolynomial ℕ ℂ := X 4
  let z4 : MvPolynomial ℕ ℂ := X 5
  -- Let A₁ = q Z', A₂ = θ(A₁) = q² Z'' + q Z', A₃ = θ(A₂), A₄ = θ(A₃)
  let A1 : MvPolynomial ℕ ℂ := qv * z1
  let A2 : MvPolynomial ℕ ℂ := qv ^ 2 * z2 + qv * z1
  let A3 : MvPolynomial ℕ ℂ := qv ^ 3 * z3 + 3 * qv ^ 2 * z2 + qv * z1
  let A4 : MvPolynomial ℕ ℂ := qv ^ 4 * z4 + 6 * qv ^ 3 * z3 + 7 * qv ^ 2 * z2 + qv * z1
  -- Numerators N_k = Z^{k+1} * (θ^k E₄):
  -- Y₀ = 1 + 240 L₃ = (Z + 240 A₁) / Z  =>  N₀ = Z + 240 A₁
  -- Y₁ = 240 θ L₃ = 240 (Z A₂ - A₁²) / Z²  =>  N₁ = 240 (Z A₂ - A₁²)
  -- Y₂ = 240 θ² L₃ = 240 (Z² A₃ - 3 Z A₁ A₂ + 2 A₁³) / Z³  =>  N₂ = 240 (Z² A₃ - 3 Z A₁ A₂ + 2 A₁³)
  -- Y₃ = 240 θ³ L₃ = 240 (Z³ A₄ - 4 Z² A₁ A₃ - 3 Z² A₂² + 12 Z A₁² A₂ - 6 A₁⁴) / Z⁴
  let N0 : MvPolynomial ℕ ℂ := zv + 240 * A1
  let N1 : MvPolynomial ℕ ℂ := 240 * (zv * A2 - A1 ^ 2)
  let N2 : MvPolynomial ℕ ℂ := 240 * (zv ^ 2 * A3 - 3 * zv * A1 * A2 + 2 * A1 ^ 3)
  let N3 : MvPolynomial ℕ ℂ := 240 * (zv ^ 3 * A4 - 4 * zv ^ 2 * A1 * A3 - 3 * zv ^ 2 * A2 ^ 2 +
    12 * zv * A1 ^ 2 * A2 - 6 * A1 ^ 4)
  -- Homogenized Z^10 * sphereS3E4Poly(N₀/Z, N₁/Z², N₂/Z³, N₃/Z⁴):
  let QZ : MvPolynomial ℕ ℂ :=
    80 * zv * N0 ^ 3 * N2 ^ 2 - 200 * zv * N0 ^ 2 * N1 ^ 2 * N2 - 80 * N0 ^ 2 * N3 ^ 2 +
      125 * zv * N0 * N1 ^ 4 + 720 * N0 * N1 * N2 * N3 - 576 * N0 * N2 ^ 3 -
      600 * N1 ^ 3 * N3 + 540 * N1 ^ 2 * N2 ^ 2
  refine ⟨QZ, ?_, ?_⟩
  · -- Verify aeval (seriesCoordinates sphereS3PartitionSeries) QZ = Z^10 * E4Series_formal_ode = 0!
    let Z := sphereS3PartitionSeries
    let L := sigmaSeries 3
    let ev : MvPolynomial ℕ ℂ →ₐ[ℂ] PowerSeries ℂ := MvPolynomial.aeval (seriesCoordinates Z)
    have hderiv_X : PowerSeries.derivative (PowerSeries.X : PowerSeries ℂ) = 1 := by
      ext n; simp [PowerSeries.coeff_one]
    have hderiv_mul : ∀ F G : PowerSeries ℂ,
        PowerSeries.derivative (F * G) = PowerSeries.derivative F * G + F * PowerSeries.derivative G := fun F G => by
      rw [(PowerSeries.derivative (R := ℂ)).leibniz F G]; simp [smul_eq_mul]; ring
    have hθ_mul : ∀ F G : PowerSeries ℂ, thetaPS (F * G) = thetaPS F * G + F * thetaPS G := fun F G => by
      simp only [thetaPS, hderiv_mul]; ring
    have hθ_add : ∀ F G : PowerSeries ℂ, thetaPS (F + G) = thetaPS F + thetaPS G := fun F G => by
      simp only [thetaPS, map_add]; ring
    have hθ_sub : ∀ F G : PowerSeries ℂ, thetaPS (F - G) = thetaPS F - thetaPS G := fun F G => by
      simp only [thetaPS, map_sub]; ring
    have hθ_C : ∀ c : ℂ, thetaPS (PowerSeries.C c) = 0 := fun c => by
      have : PowerSeries.derivative (PowerSeries.C c) = 0 := by ext n; simp
      simp [thetaPS, this]
    have hθ_Z : thetaPS Z = L * Z := sphereS3PartitionSeries_ode
    have hA1 : ev A1 = thetaPS Z := by
      simp [ev, A1, qv, z1, thetaPS, seriesCoordinates, seriesJet]
    have hA2 : ev A2 = thetaPS^[2] Z := by
      have : thetaPS^[2] Z = PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] Z) +
          PowerSeries.X * PowerSeries.derivative Z := by
        rw [Function.iterate_succ_apply', Function.iterate_one, thetaPS, thetaPS,
          hderiv_mul, hderiv_X, one_mul, Function.iterate_succ_apply', Function.iterate_one]; ring
      simp [ev, A2, qv, z1, z2, this, seriesCoordinates, seriesJet]
    have hA3 : ev A3 = thetaPS^[3] Z := by
      have h2 : thetaPS^[2] Z = PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] Z) +
          PowerSeries.X * PowerSeries.derivative Z := by
        rw [Function.iterate_succ_apply', Function.iterate_one, thetaPS, thetaPS,
          hderiv_mul, hderiv_X, one_mul, Function.iterate_succ_apply', Function.iterate_one]; ring
      have hdX2 : PowerSeries.derivative (PowerSeries.X ^ 2 : PowerSeries ℂ) = 2 * PowerSeries.X := by
        rw [sq, hderiv_mul, hderiv_X]; ring
      have h3 : thetaPS^[3] Z = PowerSeries.X ^ 3 * (PowerSeries.derivative^[3] Z) +
          3 * PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] Z) +
          PowerSeries.X * PowerSeries.derivative Z := by
        rw [Function.iterate_succ_apply', h2, thetaPS, map_add, hderiv_mul, hderiv_mul, hdX2, hderiv_X,
          show PowerSeries.derivative (PowerSeries.derivative^[2] Z) = PowerSeries.derivative^[3] Z from
            (Function.iterate_succ_apply' _ 2 _).symm,
          show PowerSeries.derivative (PowerSeries.derivative Z) = PowerSeries.derivative^[2] Z from
            (Function.iterate_succ_apply' _ 1 _).symm]
        ring
      simp [ev, A3, qv, z1, z2, z3, h3, seriesCoordinates, seriesJet]
    have hA4 : ev A4 = thetaPS^[4] Z := by
      have h2 : thetaPS^[2] Z = PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] Z) +
          PowerSeries.X * PowerSeries.derivative Z := by
        rw [Function.iterate_succ_apply', Function.iterate_one, thetaPS, thetaPS,
          hderiv_mul, hderiv_X, one_mul, Function.iterate_succ_apply', Function.iterate_one]; ring
      have hdX2 : PowerSeries.derivative (PowerSeries.X ^ 2 : PowerSeries ℂ) = 2 * PowerSeries.X := by
        rw [sq, hderiv_mul, hderiv_X]; ring
      have hdX3 : PowerSeries.derivative (PowerSeries.X ^ 3 : PowerSeries ℂ) = 3 * PowerSeries.X ^ 2 := by
        rw [pow_succ, hderiv_mul, hdX2, hderiv_X]; ring
      have h3 : thetaPS^[3] Z = PowerSeries.X ^ 3 * (PowerSeries.derivative^[3] Z) +
          3 * PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] Z) +
          PowerSeries.X * PowerSeries.derivative Z := by
        rw [Function.iterate_succ_apply', h2, thetaPS, map_add, hderiv_mul, hderiv_mul, hdX2, hderiv_X,
          show PowerSeries.derivative (PowerSeries.derivative^[2] Z) = PowerSeries.derivative^[3] Z from
            (Function.iterate_succ_apply' _ 2 _).symm,
          show PowerSeries.derivative (PowerSeries.derivative Z) = PowerSeries.derivative^[2] Z from
            (Function.iterate_succ_apply' _ 1 _).symm]
        ring
      have hderiv_3 : PowerSeries.derivative (3 : PowerSeries ℂ) = 0 := by
        rw [show (3 : PowerSeries ℂ) = PowerSeries.C 3 from rfl]
        ext n; simp
      have h4 : thetaPS^[4] Z = PowerSeries.X ^ 4 * (PowerSeries.derivative^[4] Z) +
          6 * PowerSeries.X ^ 3 * (PowerSeries.derivative^[3] Z) +
          7 * PowerSeries.X ^ 2 * (PowerSeries.derivative^[2] Z) +
          PowerSeries.X * PowerSeries.derivative Z := by
        rw [Function.iterate_succ_apply', h3, thetaPS, map_add, map_add, hderiv_mul, hderiv_mul,
          hderiv_mul, hderiv_mul, hderiv_3, zero_mul, zero_add, hdX3, hdX2, hderiv_X,
          show PowerSeries.derivative (PowerSeries.derivative^[3] Z) = PowerSeries.derivative^[4] Z from
            (Function.iterate_succ_apply' _ 3 _).symm,
          show PowerSeries.derivative (PowerSeries.derivative^[2] Z) = PowerSeries.derivative^[3] Z from
            (Function.iterate_succ_apply' _ 2 _).symm,
          show PowerSeries.derivative (PowerSeries.derivative Z) = PowerSeries.derivative^[2] Z from
            (Function.iterate_succ_apply' _ 1 _).symm]
        ring
      simp [ev, A4, qv, z1, z2, z3, z4, h4, seriesCoordinates, seriesJet]
    -- Compute thetaPS^k Z in terms of L, thetaPS L, thetaPS^2 L, thetaPS^3 L!
    have hZ1 : thetaPS Z = L * Z := hθ_Z
    have hZ2 : thetaPS^[2] Z = (thetaPS L + L ^ 2) * Z := by
      rw [Function.iterate_succ_apply', Function.iterate_one, hθ_Z, hθ_mul, hθ_Z]; ring
    have hZ3 : thetaPS^[3] Z = (thetaPS^[2] L + 3 * L * thetaPS L + L ^ 3) * Z := by
      rw [Function.iterate_succ_apply', hZ2, hθ_mul, hθ_add, hθ_Z]
      have hL2 : thetaPS (L ^ 2) = 2 * L * thetaPS L := by rw [sq, hθ_mul]; ring
      rw [hL2, Function.iterate_succ_apply', Function.iterate_one]; ring
    have hZ4 : thetaPS^[4] Z =
        (thetaPS^[3] L + 4 * L * thetaPS^[2] L + 3 * (thetaPS L) ^ 2 + 6 * L ^ 2 * thetaPS L + L ^ 4) * Z := by
      rw [Function.iterate_succ_apply', hZ3, hθ_mul, hθ_add, hθ_add, hθ_Z]
      have h3L : thetaPS (3 * L * thetaPS L) = 3 * (thetaPS L) ^ 2 + 3 * L * thetaPS^[2] L := by
        rw [mul_assoc, show (3 : PowerSeries ℂ) = PowerSeries.C 3 from rfl, hθ_mul, hθ_C, zero_mul, zero_add,
          hθ_mul, Function.iterate_succ_apply', Function.iterate_one]; ring
      have hL3 : thetaPS (L ^ 3) = 3 * L ^ 2 * thetaPS L := by
        rw [pow_succ, hθ_mul, sq, hθ_mul]; ring
      rw [h3L, hL3, show thetaPS (thetaPS^[2] L) = thetaPS^[3] L from (Function.iterate_succ_apply' _ 2 L).symm]
      ring
    -- Relate ev N_k = Z^{k+1} * (thetaPS^k E4Series)!
    have hE4_0 : thetaPS^[0] E4Series = 1 + 240 * L := by
      simp [E4Series, L, map_ofNat]
    have hE4_1 : thetaPS^[1] E4Series = 240 * thetaPS L := by
      rw [Function.iterate_one, E4Series, hθ_add,
        show (1 : PowerSeries ℂ) = PowerSeries.C 1 from rfl, hθ_C, zero_add, hθ_mul, hθ_C, zero_mul, zero_add]
      simp [L, map_ofNat]
    have hE4_2 : thetaPS^[2] E4Series = 240 * thetaPS^[2] L := by
      rw [Function.iterate_succ_apply', hE4_1, show (240 : PowerSeries ℂ) = PowerSeries.C 240 from rfl,
        hθ_mul, hθ_C, zero_mul, zero_add, Function.iterate_succ_apply', Function.iterate_one]
    have hE4_3 : thetaPS^[3] E4Series = 240 * thetaPS^[3] L := by
      rw [Function.iterate_succ_apply', hE4_2, show (240 : PowerSeries ℂ) = PowerSeries.C 240 from rfl,
        hθ_mul, hθ_C, zero_mul, zero_add, show thetaPS (thetaPS^[2] L) = thetaPS^[3] L from
          (Function.iterate_succ_apply' _ 2 L).symm]
    have hzv : ev zv = Z := by simp [ev, zv, seriesCoordinates, seriesJet]
    have hN0 : ev N0 = Z * (thetaPS^[0] E4Series) := by
      simp only [N0, map_add, map_mul, map_ofNat, hzv, hA1, hZ1, hE4_0]; ring
    have hN1 : ev N1 = Z ^ 2 * (thetaPS^[1] E4Series) := by
      simp only [N1, map_sub, map_mul, map_pow, map_ofNat, hzv, hA1, hA2, hZ1, hZ2, hE4_1]; ring
    have hN2 : ev N2 = Z ^ 3 * (thetaPS^[2] E4Series) := by
      simp only [N2, map_add, map_sub, map_mul, map_pow, map_ofNat, hzv, hA1, hA2, hA3, hZ1, hZ2, hZ3, hE4_2]; ring
    have hN3 : ev N3 = Z ^ 4 * (thetaPS^[3] E4Series) := by
      simp only [N3, map_add, map_sub, map_mul, map_pow, map_ofNat, hzv, hA1, hA2, hA3, hA4,
        hZ1, hZ2, hZ3, hZ4, hE4_3]; ring
    have hode := E4Series_formal_ode
    simp only [sphereS3E4Poly, map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.aeval_X,
      Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl] at hode
    change ev QZ = 0
    simp only [QZ, map_add, map_sub, map_mul, map_pow, map_ofNat, hzv, hN0, hN1, hN2, hN3]
    linear_combination Z ^ 10 * hode
  · -- Nonvanishing of QZ: evaluate at (q = 1, Z = 1, Z' = 0, Z'' = 0, Z''' = 0, Z'''' = 1)!
    intro h0
    let pt : ℕ → ℂ := fun k => if k = 0 ∨ k = 1 ∨ k = 5 then 1 else 0
    have hev := congrArg (MvPolynomial.eval pt) h0
    simp [QZ, N0, N1, N2, N3, A1, A2, A3, A4, qv, zv, z1, z2, z3, z4, pt] at hev

/-! ### 4B. Thermal Conformal Scalar on `S² × S¹` (`d = 3`): Unconditional Differential Transcendence -/

open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2

/-- Odd-divisor square-sum coefficient `σ₂^{odd}(n) = ∑_{d ∣ n, 2 ∤ d} d²` governing
the free conformal scalar on `S² × S¹` in `x = q^{1/2}`:
`x ∂_x log Z_{S²}(x²) = ∑_{k ≥ 0} (2k + 1)² x^{2k+1} / (1 - x^{2k+1}) = L₂(x) - 4 L₂(x²)`. -/
@[expose] def sphereS2LogDerivCoeff (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∑ d ∈ n.divisors.filter (fun d => d % 2 = 1), d ^ 2

/-- Formal free-energy derivative series `x ∂_x log Z_{S²}(x²) = L₂(x) - 4 L₂(x²)` of the
free conformal scalar on `S² × S¹` in the half-integer nome `x = q^{1/2}`. -/
@[expose] def sphereS2LogDerivSeries : PowerSeries ℂ :=
  sigmaSeries 2 - PowerSeries.C (4 : ℂ) * PowerSeries.expand 2 (by omega) (sigmaSeries 2)

/-- Exact odd-divisor identity: the `n`-th coefficient of `L₂(x) - 4 L₂(x²)` equals
`∑_{d ∣ n, 2 ∤ d} d²` (in particular, every coefficient is a nonnegative integer `≤ σ₂(n)`). -/
theorem coeff_sphereS2LogDerivSeries (n : ℕ) :
    PowerSeries.coeff n sphereS2LogDerivSeries = (sphereS2LogDerivCoeff n : ℂ) := by
  dsimp only [sphereS2LogDerivSeries, sphereS2LogDerivCoeff]
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
  cases n with
  | zero =>
    simp [sigmaSeries]
  | succ m =>
    set N := m + 1
    have hN : N ≠ 0 := Nat.succ_ne_zero m
    simp only [hN, ↓reduceIte, sigmaSeries, PowerSeries.coeff_mk]
    have hsplit : ∑ d ∈ N.divisors, d ^ 2 =
        ∑ d ∈ N.divisors.filter (fun d => d % 2 = 1), d ^ 2 +
        ∑ d ∈ N.divisors.filter (fun d => ¬ d % 2 = 1), d ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not N.divisors (fun d => d % 2 = 1) (fun d => d ^ 2)).symm
    by_cases h2 : 2 ∣ N
    · rcases h2 with ⟨r, hr⟩
      have hr_ne : r ≠ 0 := by intro h0; rw [h0, mul_zero] at hr; exact hN hr
      have hdiv_eq : N / 2 = r := by rw [hr, Nat.mul_div_cancel_left r (by omega)]
      have heven_sum : ∑ d ∈ N.divisors.filter (fun d => ¬ d % 2 = 1), d ^ 2 =
          4 * ∑ e ∈ r.divisors, e ^ 2 := by
        rw [Finset.mul_sum]
        symm
        refine Finset.sum_nbij (fun e => 2 * e) ?_ ?_ ?_ ?_
        · intro e he
          simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
          refine ⟨⟨?_, hN⟩, by omega⟩
          rcases he.1 with ⟨c, hc⟩
          exact ⟨c, by rw [hr, hc]; ring⟩
        · intro e₁ _ e₂ _ h; dsimp only at h; omega
        · intro d hd
          simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
          refine ⟨d / 2, ?_, by dsimp only; omega⟩
          simp only [Finset.mem_coe, Nat.mem_divisors]
          refine ⟨?_, hr_ne⟩
          rcases hd.1.1 with ⟨c, hc⟩
          have hd2 : d = 2 * (d / 2) := by omega
          have h2r : 2 * r = 2 * ((d / 2) * c) := by
            calc 2 * r = N := hr.symm
              _ = d * c := hc
              _ = (2 * (d / 2)) * c := by rw [← hd2]
              _ = 2 * ((d / 2) * c) := by ring
          exact ⟨c, Nat.mul_left_cancel (by omega : 0 < 2) h2r⟩
        · intro e _; ring
      have hdvd : 2 ∣ N := ⟨r, hr⟩
      simp only [hdvd, ↓reduceIte, hdiv_eq, hr_ne]
      have hnat : ∑ d ∈ N.divisors, d ^ 2 =
          ∑ d ∈ N.divisors.filter (fun d => d % 2 = 1), d ^ 2 + 4 * ∑ e ∈ r.divisors, e ^ 2 := by
        rw [hsplit, heven_sum]
      have hC := congrArg (fun k : ℕ => (k : ℂ)) hnat
      push_cast at hC ⊢
      linear_combination hC
    · simp only [h2, ↓reduceIte, mul_zero, sub_zero]
      have hempty : N.divisors.filter (fun d => ¬ d % 2 = 1) = ∅ := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false, not_and, not_not]
        intro ⟨hdvd, _⟩
        by_contra hodd
        have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
        exact h2 (dvd_trans h2d hdvd)
      rw [hempty, Finset.sum_empty, add_zero] at hsplit
      have hC := congrArg (fun k : ℕ => (k : ℂ)) hsplit
      push_cast at hC ⊢
      exact hC

private lemma sphereS2LogDerivCoeff_le (n : ℕ) : sphereS2LogDerivCoeff n ≤ sigmaNat 2 n := by
  dsimp only [sphereS2LogDerivCoeff, sigmaNat]
  split_ifs
  · exact Nat.zero_le _
  · exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem sphereS2LogDerivSeries_polyBound : PolyCoeffBound sphereS2LogDerivSeries := by
  obtain ⟨C, d, hC, hbd⟩ := sigmaSeries_polyBound 2
  refine ⟨C, d, hC, fun n => ?_⟩
  rw [coeff_sphereS2LogDerivSeries, Complex.norm_natCast]
  have h1 : (sphereS2LogDerivCoeff n : ℝ) ≤ (sigmaNat 2 n : ℝ) := by exact_mod_cast sphereS2LogDerivCoeff_le n
  have h2 := hbd n
  cases n with
  | zero =>
    simp only [sphereS2LogDerivCoeff, ↓reduceIte, Nat.cast_zero]
    positivity
  | succ m =>
    have hcoeff : ‖PowerSeries.coeff (m + 1) (sigmaSeries 2)‖ = (sigmaNat 2 (m + 1) : ℝ) := by
      rw [sigmaSeries, PowerSeries.coeff_mk]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      have hsum : (∑ d ∈ (m + 1).divisors, (d : ℂ) ^ 2) = (sigmaNat 2 (m + 1) : ℂ) := by
        simp [sigmaNat]
      rw [hsum, Complex.norm_natCast]
    rw [hcoeff] at h2
    exact h1.trans h2

/-- Coefficients of the free conformal scalar partition function on `S² × S¹`
in the half-integer nome `x = q^{1/2}`:
`Z_{S²}(x²) = ∏_{k ≥ 0} (1 - x^{2k+1})^{-(2k+1)} = M(x) / M(x²)²`,
uniquely determined by `Z(0) = 1` and `x Z'(x) = (L₂(x) - 4 L₂(x²)) Z(x)`. -/
@[expose] def sphereS2Coeff : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ k ∈ Finset.range (n + 1), (sphereS2LogDerivCoeff (k + 1) : ℝ) * sphereS2Coeff (n - k)

/-- Formal thermal partition function `Z_{S²}(x²) = ∏_{k ≥ 0} (1 - x^{2k+1})^{-(2k+1)}` of
the free conformal scalar on `S² × S¹` in `x = q^{1/2}`. -/
@[expose] def sphereS2PartitionSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (sphereS2Coeff n : ℂ)

theorem sphereS2PartitionSeries_constantCoeff :
    PowerSeries.constantCoeff sphereS2PartitionSeries = 1 := by
  simp [sphereS2PartitionSeries, sphereS2Coeff]

theorem sphereS2PartitionSeries_ode :
    PowerSeries.X * PowerSeries.derivative sphereS2PartitionSeries =
      sphereS2LogDerivSeries * sphereS2PartitionSeries := by
  ext n
  cases n with
  | zero =>
    simp [PowerSeries.coeff_mul, coeff_sphereS2LogDerivSeries, sphereS2LogDerivCoeff]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul]
    simp only [sphereS2PartitionSeries, PowerSeries.coeff_mk, sphereS2Coeff]
    have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    push_cast
    rw [mul_comm, ← mul_assoc, mul_one_div_cancel hm1, one_mul]
    conv_rhs =>
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i sphereS2LogDerivSeries * (sphereS2Coeff j : ℂ)) (m + 1),
        Finset.sum_range_succ']
    simp only [coeff_sphereS2LogDerivSeries, sphereS2LogDerivCoeff, ↓reduceIte, Nat.cast_zero, zero_mul,
      add_zero, Nat.succ_ne_zero, Nat.add_sub_add_right]

private lemma sphereS2Coeff_nonneg_and_le (n : ℕ) :
    0 ≤ sphereS2Coeff n ∧ sphereS2Coeff n ≤ macmahonCoeff n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      simp [sphereS2Coeff, macmahonCoeff_zero]
    | succ m =>
      rw [sphereS2Coeff]
      have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hmac : macmahonCoeff (m + 1) = (1 / ((m + 1 : ℕ) : ℝ)) *
          ∑ k ∈ Finset.range (m + 1), (sigmaNat 2 (k + 1) : ℝ) * macmahonCoeff (m - k) := by
        rw [← macmahonCoeff_succ m]; field_simp [hm_pos.ne']
      rw [hmac]
      constructor
      · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k hk => ?_)
        have hk_lt : m - k < m + 1 := by omega
        exact mul_nonneg (Nat.cast_nonneg _) (ih (m - k) hk_lt).1
      · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by positivity)
        have hk_lt : m - k < m + 1 := by omega
        exact mul_le_mul (by exact_mod_cast sphereS2LogDerivCoeff_le (k + 1)) (ih (m - k) hk_lt).2
          (ih (m - k) hk_lt).1 (Nat.cast_nonneg _)

theorem sphereS2PartitionSeries_diskBound : DiskCoeffBound sphereS2PartitionSeries := by
  intro r hr0 hr1
  obtain ⟨C, hC, hbd⟩ := macmahonSeries_diskBound r hr0 hr1
  refine ⟨C, hC, fun n => ?_⟩
  have h1 := sphereS2Coeff_nonneg_and_le n
  have h2 := hbd n
  simp only [sphereS2PartitionSeries, macmahonSeries, PowerSeries.coeff_mk, Complex.norm_real,
    Real.norm_of_nonneg h1.1, Real.norm_of_nonneg (macmahonCoeff_nonneg n)] at h2 ⊢
  exact h1.2.trans h2

theorem sphereS2PartitionSeries_qRay_ne_zero (u : ℝ) :
    value sphereS2PartitionSeries (qRay u) ≠ 0 := by
  have hq_pos : 0 < Real.exp (-Real.exp (-u)) := Real.exp_pos _
  have habs : AbsAt sphereS2PartitionSeries (qRay u) := by
    simpa [seriesJet] using seriesJet_abs sphereS2PartitionSeries_diskBound 0 (qRay_disk u)
  have hre : (value sphereS2PartitionSeries (qRay u)).re =
      ∑' n : ℕ, sphereS2Coeff n * (Real.exp (-Real.exp (-u))) ^ n := by
    unfold value
    rw [Complex.re_tsum habs.of_norm]
    refine tsum_congr fun n => ?_
    simp only [term, sphereS2PartitionSeries, PowerSeries.coeff_mk, qRay]
    have hpow : ((Real.exp (-Real.exp (-u)) : ℂ)) ^ n = (((Real.exp (-Real.exp (-u))) ^ n : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hpow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsumm_real : Summable (fun n : ℕ => sphereS2Coeff n * (Real.exp (-Real.exp (-u))) ^ n) := by
    refine habs.of_norm_bounded fun n => ?_
    simp only [term, sphereS2PartitionSeries, PowerSeries.coeff_mk, qRay, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (sphereS2Coeff_nonneg_and_le n).1,
      Real.norm_of_nonneg hq_pos.le, le_refl]
  have hge1 : (1 : ℝ) ≤ (value sphereS2PartitionSeries (qRay u)).re := by
    rw [hre]
    have h0 : (1 : ℝ) = sphereS2Coeff 0 * (Real.exp (-Real.exp (-u))) ^ 0 := by simp [sphereS2Coeff]
    rw [h0]
    exact hsumm_real.le_tsum 0 fun k _ => mul_nonneg (sphereS2Coeff_nonneg_and_le k).1 (pow_nonneg hq_pos.le k)
  intro h0
  rw [h0, Complex.zero_re] at hge1
  linarith

/-- **Exact Holographic MacMahon Factorization on `S² × S¹`**:
`Z_{S²}(x²) · M(x²)² = M(x)` identically in `PowerSeries ℂ`, expressing the thermal partition
function of the 3D free conformal scalar on the 2-sphere as an exact ratio of MacMahon plane
partition generating functions. -/
theorem sphereS2PartitionSeries_macmahon_identity :
    sphereS2PartitionSeries * (PowerSeries.expand 2 (by omega) macmahonSeries) ^ 2 = macmahonSeries := by
  let M := macmahonSeries
  let M2 := PowerSeries.expand 2 (by omega) M
  let F := sphereS2PartitionSeries * M2 ^ 2
  have hderiv_mul : ∀ A B : PowerSeries ℂ,
      PowerSeries.derivative (A * B) = PowerSeries.derivative A * B + A * PowerSeries.derivative B := fun A B => by
    rw [(PowerSeries.derivative (R := ℂ)).leibniz A B]; simp [smul_eq_mul]; ring
  have hθ_expand2 : ∀ G : PowerSeries ℂ,
      thetaPS (PowerSeries.expand 2 (by omega) G) =
        PowerSeries.C (2 : ℂ) * PowerSeries.expand 2 (by omega) (thetaPS G) := by
    intro G
    ext n
    cases n with
    | zero =>
      simp [thetaPS, PowerSeries.coeff_C_mul]
    | succ m =>
      rw [thetaPS, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      by_cases h2 : 2 ∣ (m + 1)
      · rcases h2 with ⟨r, hr⟩
        have hr_pos : 1 ≤ r := by omega
        have hdiv : (m + 1) / 2 = r := by rw [hr, Nat.mul_div_cancel_left r (by omega)]
        simp only [show 2 ∣ (m + 1) from ⟨r, hr⟩, ↓reduceIte, hdiv]
        cases r with
        | zero => omega
        | succ k =>
          rw [thetaPS, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
          have hcast : ((m : ℂ) + 1) = 2 * ((k : ℂ) + 1) := by exact_mod_cast hr
          rw [hcast]; ring
      · simp [h2]
  have hθ_M2 : thetaPS M2 = PowerSeries.C (2 : ℂ) * PowerSeries.expand 2 (by omega) (sigmaSeries 2) * M2 := by
    dsimp only [M2]
    rw [hθ_expand2 M]
    have hM_ode : thetaPS M = sigmaSeries 2 * M := macmahonSeries_ode
    rw [hM_ode, map_mul, mul_assoc]
  have hθ_sphereS2 : thetaPS sphereS2PartitionSeries = sphereS2LogDerivSeries * sphereS2PartitionSeries :=
    sphereS2PartitionSeries_ode
  have hθ_F : thetaPS F = sigmaSeries 2 * F := by
    dsimp only [F]
    have hθ_mul : ∀ A B : PowerSeries ℂ, thetaPS (A * B) = thetaPS A * B + A * thetaPS B := fun A B => by
      simp only [thetaPS, hderiv_mul]; ring
    rw [hθ_mul, sq, hθ_mul, hθ_sphereS2, hθ_M2]
    dsimp only [sphereS2LogDerivSeries]
    have h2 : PowerSeries.C (2 : ℂ) = 2 := map_ofNat PowerSeries.C 2
    have h4 : PowerSeries.C (4 : ℂ) = 4 := map_ofNat PowerSeries.C 4
    rw [h2, h4]; ring
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    dsimp only [F, M2, M]
    rw [map_mul, map_pow, PowerSeries.constantCoeff_expand, sphereS2PartitionSeries_constantCoeff,
      macmahonSeries_constantCoeff]
    ring
  ext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      exact hF0.trans macmahonSeries_constantCoeff.symm
    | succ m =>
      have hF_c := congrArg (PowerSeries.coeff (m + 1)) hθ_F
      have hM_c := congrArg (PowerSeries.coeff (m + 1)) macmahonSeries_ode
      conv_lhs at hF_c => rw [thetaPS, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      conv_rhs at hF_c => rw [PowerSeries.coeff_mul]
      conv_lhs at hM_c => rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      conv_rhs at hM_c => rw [PowerSeries.coeff_mul]
      have hsum_eq : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
            PowerSeries.coeff p.1 (sigmaSeries 2) * PowerSeries.coeff p.2 F =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
            PowerSeries.coeff p.1 (sigmaSeries 2) * PowerSeries.coeff p.2 M := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (sigmaSeries 2) * PowerSeries.coeff j F),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (sigmaSeries 2) * PowerSeries.coeff j M)]
        conv_lhs => rw [Finset.sum_range_succ']
        conv_rhs => rw [Finset.sum_range_succ']
        simp only [sigmaSeries, PowerSeries.coeff_mk, ↓reduceIte, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hlt : m + 1 - (k + 1) < m + 1 := by omega
        rw [ih _ hlt]
      have hmul_eq : PowerSeries.coeff (m + 1) F * ((m : ℂ) + 1) =
          PowerSeries.coeff (m + 1) M * ((m : ℂ) + 1) := by
        rw [hF_c, hsum_eq, ← hM_c]
      exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m : ((m : ℂ) + 1) ≠ 0) hmul_eq

/-! #### 4B.2. Cauchy-Estimate Proof of `ExpDecaySmooth (hFun 1)` and Bernoulli Derivatives -/

private lemma expAux_hasFPowerSeriesOnBall_eos :
    HasFPowerSeriesOnBall expAux
      (.ofScalars ℂ (fun n : ℕ => ((n + 1).factorial : ℂ)⁻¹)) 0 ⊤ := by
  let c : ℕ → ℂ := fun n => ((n + 1).factorial : ℂ)⁻¹
  have hc_ne : ∀ᶠ n : ℕ in atTop, c n ≠ 0 := Eventually.of_forall fun n => by
    dsimp [c]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hc_lim : Tendsto (fun n : ℕ => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => ‖c n.succ‖ / ‖c n‖) = fun n : ℕ => ((n : ℝ) + 2)⁻¹ := by
      funext n
      dsimp [c]
      rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast,
        Nat.factorial_succ, Nat.cast_mul]
      have h1 : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((n + 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [h1, h2]
      push_cast; ring
    rw [heq]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hrad : (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤ :=
    FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ c hc_ne hc_lim
  have hball : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum c)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 ⊤ := by
    rw [← hrad]
    exact (FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
      (hrad ▸ (by simp : (0 : ENNReal) < ⊤))
  refine hball.congr fun z _ => ?_
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  refine tsum_congr fun n => ?_
  dsimp [c]; simp [div_eq_mul_inv, mul_comm]

private lemma expAux_analytic_eos (z : ℂ) : AnalyticAt ℂ expAux z :=
  expAux_hasFPowerSeriesOnBall_eos.analyticOnNhd z (by simp)

private lemma expAux_zero_eos : expAux 0 = 1 := by
  rw [expAux, tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

private lemma expAux_mul_sub_eos (z : ℂ) : z * expAux z = Complex.exp z - 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have hsum : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have hsum_tail : HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1).factorial : ℂ)) (Complex.exp z - 1) := by
    have hsplit := (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ n / (n.factorial : ℂ)) 1).mpr hsum
    simpa [Finset.sum_range_one] using hsplit
  have hsum_aux : HasSum (fun n : ℕ => z ^ n / ((n + 1).factorial : ℂ)) (z⁻¹ * (Complex.exp z - 1)) := by
    refine (hsum_tail.mul_left z⁻¹).congr_fun fun n => ?_
    rw [pow_succ']
    field_simp [hz]
  rw [expAux, hsum_aux.tsum_eq]
  field_simp [hz]

private lemma expAux_ne_zero_of_abs_im_lt {z : ℂ} (him : |z.im| < 2 * Real.pi) : expAux z ≠ 0 := by
  by_cases hz : z = 0
  · subst hz; rw [expAux_zero_eos]; exact one_ne_zero
  intro h0
  have hmul := expAux_mul_sub_eos z
  rw [h0, mul_zero] at hmul
  have hexp1 : Complex.exp z = 1 := sub_eq_zero.mp hmul.symm
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp1
  have hk_ne : k ≠ 0 := by
    intro h; rw [h, Int.cast_zero, zero_mul] at hk; exact hz hk
  have him_eq : z.im = (k : ℝ) * (2 * Real.pi) := by
    rw [hk, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero]
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
    rw [h2pi]
  rw [him_eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at him
  have hk_ge : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    exact_mod_cast h1
  nlinarith [Real.pi_pos]

private lemma iteratedDeriv_ofReal_comp_analytic {F : ℂ → ℂ} (hF : ∀ x : ℝ, AnalyticAt ℂ F (x : ℂ))
    (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => F (t : ℂ)) x = iteratedDeriv k F (x : ℂ) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun t : ℝ => F (t : ℂ)) = fun t : ℝ => iteratedDeriv k F (t : ℂ) :=
      funext ih
    rw [heq]
    have hd : DifferentiableAt ℂ (iteratedDeriv k F) (x : ℂ) := by
      have han : AnalyticAt ℂ (iteratedDeriv k F) (x : ℂ) := by
        rw [iteratedDeriv_eq_iterate]
        have hopen : ∀ y : ℝ, ∃ U : Set ℂ, IsOpen U ∧ (y : ℂ) ∈ U ∧ AnalyticOnNhd ℂ F U := fun y => by
          obtain ⟨r, hr, hball⟩ := (hF y).exists_ball_analyticOnNhd
          exact ⟨Metric.ball (y : ℂ) r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball⟩
        obtain ⟨U, _, hxU, hFU⟩ := hopen x
        exact hFU.iterated_deriv k (x : ℂ) hxU
      exact han.differentiableAt
    exact (hd.hasDerivAt.comp_ofReal).deriv

private lemma hFun_one_expDecaySmooth : ExpDecaySmooth (hFun 1) := by
  let hC : ℂ → ℂ := fun z => z * qComplex z
  have hC_an : ∀ z : ℂ, |z.im| < 2 * Real.pi → AnalyticAt ℂ hC z := fun z hz =>
    analyticAt_id.mul ((expAux_analytic_eos z).inv (expAux_ne_zero_of_abs_im_lt hz))
  have hC_real : ∀ x : ℝ, hFun 1 x = hC (x : ℂ) := fun x => by
    simp [hFun, qFun, hC]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (hFun 1) := by
    have heq : hFun 1 = fun x : ℝ => hC (x : ℂ) := funext hC_real
    rw [heq]
    rw [contDiff_iff_contDiffAt]
    intro x
    have han : AnalyticAt ℂ hC (x : ℂ) := hC_an (x : ℂ) (by simp; positivity)
    exact (han.restrictScalars (𝕜 := ℝ)).contDiffAt.comp x Complex.ofRealCLM.contDiff.contDiffAt
  -- Bound ‖hC z‖ on closedBall 0 3 (compact inside {|Im z| < 2π})
  have hcont_cb : ContinuousOn (fun z : ℂ => ‖hC z‖) (Metric.closedBall (0 : ℂ) 3) := by
    intro z hz
    have hnorm : ‖z‖ ≤ 3 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have him : |z.im| < 2 * Real.pi :=
      ((Complex.abs_im_le_norm z).trans hnorm).trans_lt (by linarith [Real.pi_gt_three])
    exact (hC_an z him).continuousAt.norm.continuousWithinAt
  obtain ⟨zm, _, hzm⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self (by norm_num)⟩ hcont_cb
  let M0 : ℝ := ‖hC zm‖
  have hM0 : 0 ≤ M0 := norm_nonneg _
  -- Universal bound for x ≥ 0 and z ∈ sphere x 1: ‖hC z‖ ≤ B * exp(-x / 2)
  let B : ℝ := max (M0 * Real.exp 1) (100 * Real.exp 1)
  have hB : 0 ≤ B := le_trans (by positivity) (le_max_right _ _)
  have hsphere_bd : ∀ (x : ℝ), 0 ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) 1,
      ‖hC z‖ ≤ B * Real.exp (-(1 / 2 : ℝ) * x) := by
    intro x hx z hz
    have hdist : ‖z - (x : ℂ)‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    by_cases hx2 : x ≤ 2
    · have hz3 : z ∈ Metric.closedBall (0 : ℂ) 3 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖z‖ = ‖(x : ℂ) + (z - (x : ℂ))‖ := by ring_nf
          _ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := norm_add_le _ _
          _ = x + 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx, hdist]
          _ ≤ 3 := by linarith
      have h1 : ‖hC z‖ ≤ M0 := hzm hz3
      have hexp : 1 ≤ Real.exp 1 * Real.exp (-(1 / 2 : ℝ) * x) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      calc ‖hC z‖ ≤ M0 := h1
        _ ≤ M0 * (Real.exp 1 * Real.exp (-(1 / 2 : ℝ) * x)) := by nlinarith
        _ = (M0 * Real.exp 1) * Real.exp (-(1 / 2 : ℝ) * x) := by ring
        _ ≤ B * Real.exp (-(1 / 2 : ℝ) * x) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · push Not at hx2
      have hre_diff : |z.re - x| ≤ 1 := by
        calc |z.re - x| = |(z - (x : ℂ)).re| := by simp
          _ ≤ ‖z - (x : ℂ)‖ := Complex.abs_re_le_norm _
          _ = 1 := hdist
      have hz_re : x - 1 ≤ z.re := by linarith [(abs_le.mp hre_diff).1]
      have hz_re1 : 1 ≤ z.re := by linarith
      have hz_ne : z ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hz_re1; linarith
      have hexp_ge : (1 / 2 : ℝ) * Real.exp z.re ≤ ‖Complex.exp z - 1‖ := by
        have h1 : Real.exp z.re - 1 ≤ ‖Complex.exp z - 1‖ := by
          have := norm_sub_norm_le (Complex.exp z) (1 : ℂ)
          rwa [Complex.norm_exp, norm_one] at this
        have h2 : (2 : ℝ) ≤ Real.exp z.re := by
          have := Real.add_one_le_exp z.re; linarith
        linarith
      have hden_ge : (1 / 2 : ℝ) * Real.exp (x - 1) ≤ ‖Complex.exp z - 1‖ :=
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz_re) (by norm_num)).trans hexp_ge
      have hC_eq : hC z = z ^ 2 / (Complex.exp z - 1) := by
        have him : |z.im| < 2 * Real.pi := by
          have h1 : |z.im| ≤ 1 := by
            calc |z.im| = |(z - (x : ℂ)).im| := by simp
              _ ≤ ‖z - (x : ℂ)‖ := Complex.abs_im_le_norm _
              _ = 1 := hdist
          linarith [Real.pi_gt_three]
        have hne_aux : expAux z ≠ 0 := expAux_ne_zero_of_abs_im_lt him
        have hmul := expAux_mul_sub_eos z
        have hne_e : Complex.exp z - 1 ≠ 0 := by rw [← hmul]; exact mul_ne_zero hz_ne hne_aux
        dsimp only [hC, qComplex]
        rw [← hmul]
        field_simp [hz_ne, hne_aux]
      have hz_norm : ‖z‖ ≤ x + 1 := by
        calc ‖z‖ = ‖(x : ℂ) + (z - (x : ℂ))‖ := by ring_nf
          _ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := norm_add_le _ _
          _ = x + 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx, hdist]
      have hpoly_exp : 2 * (x + 1) ^ 2 ≤ 100 * Real.exp (x / 2) := by
        -- Since exp(t) ≥ 1 + t + t²/2 for t ≥ 0, at t = x/2: 1 + x/2 + x²/8 ≤ exp(x/2)
        have ht : 0 ≤ x / 2 := by linarith
        have h2 := Real.sum_le_exp_of_nonneg ht 3
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
          pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
          Nat.factorial_two, Nat.cast_ofNat] at h2
        nlinarith
      rw [hC_eq, norm_div, norm_pow]
      calc ‖z‖ ^ 2 / ‖Complex.exp z - 1‖
          ≤ (x + 1) ^ 2 / ((1 / 2 : ℝ) * Real.exp (x - 1)) := by
            exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg z) hz_norm 2)
              (by positivity) hden_ge
        _ = (2 * (x + 1) ^ 2) * Real.exp 1 * Real.exp (-x) := by
            rw [Real.exp_sub]; field_simp [(Real.exp_pos x).ne', (Real.exp_pos 1).ne']
            rw [Real.exp_neg]; field_simp [(Real.exp_pos x).ne']
        _ ≤ (100 * Real.exp (x / 2)) * Real.exp 1 * Real.exp (-x) := by
            gcongr
        _ = (100 * Real.exp 1) * Real.exp (-(1 / 2 : ℝ) * x) := by
            calc (100 * Real.exp (x / 2)) * Real.exp 1 * Real.exp (-x)
                = (100 * Real.exp 1) * (Real.exp (x / 2) * Real.exp (-x)) := by ring
              _ = (100 * Real.exp 1) * Real.exp (-(1 / 2 : ℝ) * x) := by
                  rw [← Real.exp_add]; congr 2; ring
        _ ≤ B * Real.exp (-(1 / 2 : ℝ) * x) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  refine ⟨hcd, fun r => ⟨(r.factorial : ℝ) * B, 1 / 2, by positivity, by norm_num, fun x hx => ?_⟩⟩
  have heq_f : hFun 1 = fun t : ℝ => hC (t : ℂ) := funext hC_real
  rw [heq_f, iteratedDeriv_ofReal_comp_analytic (fun t => hC_an (t : ℂ) (by simp; positivity))]
  have hdiff_cl : DiffContOnCl ℂ hC (Metric.ball (x : ℂ) 1) := by
    have hsub : ∀ z ∈ Metric.closedBall (x : ℂ) 1, |z.im| < 2 * Real.pi := by
      intro z hz
      have hd : ‖z - (x : ℂ)‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have h1 : |z.im| ≤ 1 := by
        calc |z.im| = |(z - (x : ℂ)).im| := by simp
          _ ≤ ‖z - (x : ℂ)‖ := Complex.abs_im_le_norm _
          _ ≤ 1 := hd
      linarith [Real.pi_gt_three]
    refine ⟨fun z hz => (hC_an z (hsub z (Metric.ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt,
      fun z hz => ?_⟩
    rw [closure_ball (x : ℂ) one_ne_zero] at hz
    exact (hC_an z (hsub z hz)).continuousAt.continuousWithinAt
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r zero_lt_one
    hdiff_cl (hsphere_bd x hx)
  simpa [mul_assoc] using hcauchy

/-! #### 4B.3. Meromorphic Borel Transform `K_{S²}(ξ) = K_even 1 ξ - K_even 1 (2 ξ)` & All-Orders Asymptotics -/

/-- Meromorphic Borel transform `K_{S²}(ξ) = K₂(ξ) - K₂(2 ξ)` for the 3D free conformal scalar
on `S² × S¹`, with simple poles at `ω_k = 2π²(k + 1)` (`k ∈ ℕ`). -/
@[expose] def K_S2 (ξ : ℂ) : ℂ := K_even 1 ξ - K_even 1 (2 * ξ)

/-- Pole locations `ω_k = 2π²(k + 1)` of `K_{S²}` along the positive real axis. -/
@[expose] def ω_S2 (k : ℕ) : ℝ := 2 * Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ)

/-- Exact simple-pole residues of `K_{S²}` at `ω_k = 2π²(k + 1)`:
`+4π² σ₂(k+1)` when `k+1` is odd, and `+4π² (σ₂(k+1) - 2 σ₂((k+1)/2))` when `k+1` is even. -/
@[expose] def res_S2 (k : ℕ) : ℂ :=
  4 * (Real.pi : ℂ) ^ 2 *
    if Even (k + 1) then
      (sigmaNat 2 (k + 1) : ℂ) - 2 * (sigmaNat 2 ((k + 1) / 2) : ℂ)
    else (sigmaNat 2 (k + 1) : ℂ)

/-- Scaled Euler–Maclaurin remainder `f_{S²}(u) = f₂(u) - (1/2) f₂(u/2)` matching `formalSeries K_S2`. -/
@[expose] def f_S2 (u : ℝ) : ℂ := f_even 1 u - (1 / 2 : ℂ) * f_even 1 (u / 2)

private lemma sigmaNat_pos_eos {k n : ℕ} (hn : 1 ≤ n) : 1 ≤ sigmaNat k n := by
  simp only [sigmaNat, show n ≠ 0 by omega, ↓reduceIte]
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  have hle := Finset.single_le_sum (f := fun d : ℕ => d ^ k) (fun _ _ => Nat.zero_le _) h1
  simpa using hle

private lemma four_mul_sigmaNat_le_two_mul {m : ℕ} (hm : 1 ≤ m) :
    4 * sigmaNat 2 m ≤ sigmaNat 2 (2 * m) := by
  simp only [sigmaNat, show m ≠ 0 by omega, show 2 * m ≠ 0 by omega, ↓reduceIte]
  have hsub : m.divisors.image (fun d => 2 * d) ⊆ (2 * m).divisors := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨d, hd, rfl⟩
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨mul_dvd_mul_left 2 hd.1, by omega⟩
  have hinj : Function.Injective (fun d : ℕ => 2 * d) := fun a b h => by dsimp only at h; omega
  calc 4 * ∑ d ∈ m.divisors, d ^ 2
      = ∑ d ∈ m.divisors, (2 * d) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring
    _ = ∑ x ∈ m.divisors.image (fun d => 2 * d), x ^ 2 :=
        (Finset.sum_image (f := fun x : ℕ => x ^ 2) (fun a _ b _ h => hinj h)).symm
    _ ≤ ∑ x ∈ (2 * m).divisors, x ^ 2 :=
        Finset.sum_le_sum_of_subset hsub

private lemma res_S2_ne_zero (k : ℕ) : res_S2 k ≠ 0 := by
  dsimp only [res_S2]
  have hpi : (4 * (Real.pi : ℂ) ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  refine mul_ne_zero hpi ?_
  split_ifs with hev
  · rcases hev with ⟨r, hr⟩
    have hr1 : 1 ≤ r := by omega
    have hdiv : (k + 1) / 2 = r := by omega
    have h2r : k + 1 = 2 * r := by omega
    rw [hdiv, h2r]
    have hge : 4 * sigmaNat 2 r ≤ sigmaNat 2 (2 * r) := four_mul_sigmaNat_le_two_mul hr1
    have hpos : 1 ≤ sigmaNat 2 r := sigmaNat_pos_eos hr1
    have hlt : 2 * sigmaNat 2 r < sigmaNat 2 (2 * r) := by omega
    have hR : (2 * (sigmaNat 2 r : ℝ)) < (sigmaNat 2 (2 * r) : ℝ) := by exact_mod_cast hlt
    intro h0
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero, Complex.zero_re] at hre
    linarith
  · exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (sigmaNat_pos_eos (Nat.succ_pos k)))

private lemma summable_sigmaNat_div_pow_two :
    Summable (fun n : ℕ => (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := by
  have h2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))
  -- σ₂(m) ≤ m * m² = m³? No, ∑_{d ∣ m} d² = m² ∑_{d ∣ m} 1/d² ≤ m² * 2!
  -- Even simpler: σ₂(n+1)/(n+1)⁴ = (1/(n+1)²) ∑_{d ∣ n+1} (d/(n+1))²? Wait: ∑_{d ∣ m} 1/d² ≤ 2!
  -- Actually bound σ₂(m)/m⁴ by (1/m²) * (∑_{d=1}^m 1/d²) ≤ 2/m²!
  have hbound : ∀ m : ℕ, 1 ≤ m → (sigmaNat 2 m : ℝ) / (m : ℝ) ^ 4 ≤ 2 * ((m : ℝ) ^ (-(2 : ℝ))) := by
    intro m hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    -- Every divisor d ∣ m has m/d ∣ m, so σ₂(m) / m² = ∑_{d ∣ m} 1 / d²!
    have hdiv_sum : (sigmaNat 2 m : ℝ) / (m : ℝ) ^ 2 = ∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ) ^ 2 := by
      simp only [sigmaNat, show m ≠ 0 by omega, ↓reduceIte]
      rw [Nat.cast_sum, Finset.sum_div]
      symm
      refine Finset.sum_nbij (fun d => m / d) ?_ ?_ ?_ ?_
      · intro d hd
        rw [Nat.mem_divisors] at hd ⊢
        exact ⟨Nat.div_dvd_of_dvd hd.1, hd.2⟩
      · intro d₁ hd₁ d₂ hd₂ heq
        dsimp only at heq
        have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₁)
        have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₂)
        have hpos : 0 < m / d₁ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd₁))
          (Nat.pos_of_mem_divisors hd₁)
        have hmul : d₁ * (m / d₁) = d₂ * (m / d₁) := by rw [h1, heq, h2]
        exact Nat.eq_of_mul_eq_mul_right hpos hmul
      · intro e he
        rw [Finset.mem_coe, Nat.mem_divisors] at he
        refine ⟨m / e, ?_, Nat.div_div_self he.1 he.2⟩
        rw [Finset.mem_coe, Nat.mem_divisors]
        exact ⟨Nat.div_dvd_of_dvd he.1, he.2⟩
      · intro d hd
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
        have hmd_pos : (0 : ℝ) < ((m / d : ℕ) : ℝ) := by
          exact_mod_cast Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd))
            (Nat.pos_of_mem_divisors hd)
        have hmul : ((m / d : ℕ) : ℝ) * (d : ℝ) = (m : ℝ) := by
          exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
        rw [Nat.cast_pow, ← hmul]
        field_simp [hd_pos.ne', hmd_pos.ne']
    -- Bound ∑_{d ∈ m.divisors} 1/d² ≤ ∑_{k=0}^{m-1} 1/(k+1)² ≤ 2 (telescoping 1/(k+1)² ≤ 1/k - 1/(k+1))!
    have htele : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
      intro N
      have hstep : ∀ M : ℕ, ∑ k ∈ Finset.range (M + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤
          2 - 1 / ((M : ℝ) + 1) := by
        intro M
        induction M with
        | zero => simp; norm_num
        | succ r ih =>
          rw [Finset.sum_range_succ]
          have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
          have hr2 : (0 : ℝ) < (r : ℝ) + 2 := by positivity
          have h1 : (1 : ℝ) / ((r : ℝ) + 2) ^ 2 ≤ 1 / ((r : ℝ) + 1) - 1 / ((r : ℝ) + 2) := by
            have h2 : 1 / ((r : ℝ) + 1) - 1 / ((r : ℝ) + 2) = 1 / (((r : ℝ) + 1) * ((r : ℝ) + 2)) := by
              field_simp [hr1.ne', hr2.ne']; ring
            rw [h2]
            apply div_le_div_of_nonneg_left zero_le_one (by positivity)
            nlinarith
          have hcast : ((r + 1 : ℕ) : ℝ) + 1 = (r : ℝ) + 2 := by push_cast; ring
          rw [hcast]
          linarith
      cases N with
      | zero => simp
      | succ M =>
        have := hstep M
        have : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
        linarith
    have hsub_le : ∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
      have hsub : m.divisors ⊆ (Finset.range m).image (fun x : ℕ => x + 1) := by
        intro d hd
        have hd_pos := Nat.pos_of_mem_divisors hd
        have hd_le := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
        exact Finset.mem_image.mpr ⟨d - 1, Finset.mem_range.mpr (by omega), by omega⟩
      calc ∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ) ^ 2
          ≤ ∑ d ∈ (Finset.range m).image (fun x : ℕ => x + 1), (1 : ℝ) / (d : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = ∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
            rw [Finset.sum_image (fun a _ b _ h => by omega)]
            refine Finset.sum_congr rfl fun k _ => by push_cast; rfl
        _ ≤ 2 := htele m
    rw [Real.rpow_neg hm_pos.le, Real.rpow_two]
    have hpow4 : (m : ℝ) ^ 4 = (m : ℝ) ^ 2 * (m : ℝ) ^ 2 := by ring
    rw [hpow4, ← div_div, hdiv_sum]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsub_le (by positivity)
  refine (h2.mul_left 2).of_norm_bounded fun n => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hbound (n + 1) (Nat.succ_pos n)

private lemma A_freq_pos_eos (n : ℕ) : 0 < A_freq n := by
  dsimp only [A_freq]; positivity

private lemma A_freq_tail_diff_norm_ge_eos (w : ℂ) (R : ℝ) :
    ∃ N : ℕ, ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w R →
      A_freq (k + N) / 2 ≤ ‖(A_freq (k + N) : ℂ) - z‖ ∧
      A_freq (k + N) / 2 ≤ ‖(A_freq (k + N) : ℂ) + z‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖w‖ + |R| + 1) / (2 * Real.pi ^ 2))
  refine ⟨N, fun k z hz => ?_⟩
  have hdist : ‖z - w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz_le : ‖z‖ ≤ ‖w‖ + |R| := by
    calc ‖z‖ = ‖w + (z - w)‖ := by ring_nf
      _ ≤ ‖w‖ + ‖z - w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + |R| := by linarith [le_abs_self R]
  have hA_ge : 2 * (‖w‖ + |R|) ≤ A_freq (k + N) := by
    have h1 : ‖w‖ + |R| + 1 < (N : ℝ) * (2 * Real.pi ^ 2) := (div_lt_iff₀ (by positivity)).mp hN
    have h2 : (N : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ k + N + 1)
    dsimp only [A_freq]
    nlinarith [Real.pi_pos]
  have hAnorm : ‖(A_freq (k + N) : ℂ)‖ = A_freq (k + N) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos _).le]
  constructor
  · have := norm_sub_norm_le (A_freq (k + N) : ℂ) z
    rw [hAnorm] at this; linarith
  · have := norm_sub_norm_le (A_freq (k + N) : ℂ) (-z)
    rw [sub_neg_eq_add, hAnorm, norm_neg] at this; linarith

private lemma K_even_one_analyticAt {w : ℂ} (hw_pos : w ∈ borelWedge (Real.pi / 4) (2 * Real.pi ^ 2))
    (hw_ne : ∀ n : ℕ, w ≠ (A_freq n : ℂ)) : AnalyticAt ℂ (K_even 1) w := by
  obtain ⟨N, hN⟩ := A_freq_tail_diff_norm_ge_eos w 1
  let term : ℕ → ℂ → ℂ := fun n z =>
    ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) * ((A_freq n : ℂ) ^ 2 - z ^ 2)⁻¹
  let head : ℂ → ℂ := fun z => ∑ n ∈ Finset.range N, term n z
  let tail : ℂ → ℂ := fun z => ∑' k : ℕ, term (k + N) z
  let cbd : ℝ := 4 / (4 * Real.pi ^ 2) ^ 2
  have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w 1 →
      ‖term (k + N) z‖ ≤ cbd * ((sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 4) := by
    intro k z hz
    obtain ⟨hsub, hadd⟩ := hN k z hz
    have hA_pos : 0 < A_freq (k + N) := A_freq_pos_eos (k + N)
    have hsq : (A_freq (k + N) : ℂ) ^ 2 - z ^ 2 = ((A_freq (k + N) : ℂ) - z) * ((A_freq (k + N) : ℂ) + z) := by ring
    dsimp only [term]
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast, norm_inv, hsq, norm_mul]
    have hprod : (A_freq (k + N) / 2) * (A_freq (k + N) / 2) ≤
        ‖(A_freq (k + N) : ℂ) - z‖ * ‖(A_freq (k + N) : ℂ) + z‖ :=
      mul_le_mul hsub hadd (by positivity) (by positivity)
    have hinv := inv_anti₀ (by positivity) hprod
    have h1 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 2)
    refine h1.trans_eq ?_
    dsimp only [cbd, A_freq]
    have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    have hn0 : ((k + N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hpi0, hn0]; ring
  have htail_diff : DifferentiableOn ℂ tail (Metric.ball w 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (((summable_nat_add_iff N).2 summable_sigmaNat_div_pow_two).mul_left cbd)
      (fun k => ?_) Metric.isOpen_ball htail_bd
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.inv ((differentiableOn_const _).sub (differentiableOn_id.pow 2)) fun z hz h0 => ?_
    have hsq : (A_freq (k + N) : ℂ) ^ 2 - z ^ 2 = ((A_freq (k + N) : ℂ) - z) * ((A_freq (k + N) : ℂ) + z) := by ring
    rw [hsq, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · have h1 := (hN k z hz).1; rw [h0, norm_zero] at h1; linarith [A_freq_pos_eos (k + N)]
    · have h1 := (hN k z hz).2; rw [h0, norm_zero] at h1; linarith [A_freq_pos_eos (k + N)]
  have htail_ana : AnalyticAt ℂ tail w :=
    (htail_diff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self zero_lt_one)
  have hhead_ana : AnalyticAt ℂ head w := by
    refine Finset.analyticAt_fun_sum (Finset.range N) fun n _ => ?_
    refine AnalyticAt.mul analyticAt_const ?_
    refine (analyticAt_const.sub (analyticAt_id.pow 2)).inv ?_
    have hsq : (A_freq n : ℂ) ^ 2 - w ^ 2 = ((A_freq n : ℂ) - w) * ((A_freq n : ℂ) + w) := by ring
    change (A_freq n : ℂ) ^ 2 - w ^ 2 ≠ 0
    rw [hsq]
    refine mul_ne_zero (sub_ne_zero.mpr (hw_ne n).symm) ?_
    intro h0
    have hw_eq : w = -(A_freq n : ℂ) := eq_neg_of_add_eq_zero_right h0
    rcases hw_pos with hball | hsec
    · have hlt : ‖w‖ < 2 * Real.pi ^ 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hball
      rw [hw_eq, norm_neg, Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos n).le] at hlt
      dsimp only [A_freq] at hlt
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith [Real.pi_pos]
    · have hre : 0 < w.re := hsec.1
      rw [hw_eq, Complex.neg_re, Complex.ofReal_re] at hre
      linarith [A_freq_pos_eos n]
  have hev : K_even 1 =ᶠ[𝓝 w] fun z =>
      (-1 : ℂ) ^ 2 * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ 1) * z ^ 3 * (head z + tail z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one)] with z hz
    have hts : Summable (fun k : ℕ => term (k + N) z) :=
      (((summable_nat_add_iff N).2 summable_sigmaNat_div_pow_two).mul_left cbd).of_norm_bounded fun k =>
        htail_bd k z hz
    have hsum_all := (summable_nat_add_iff (f := fun n => term n z) N).1 hts
    have hs_eq : S_even 1 z = head z + tail z := (hsum_all.sum_add_tsum_nat_add N).symm
    simp only [K_even]
    exact congrArg (fun s => (-1 : ℂ) ^ 2 * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ 1) * z ^ 3 * s) hs_eq
  exact ((analyticAt_const.mul (analyticAt_id.pow 3)).mul (hhead_ana.add htail_ana)).congr hev.symm

private lemma K_even_one_simple_pole (k : ℕ) :
    Tendsto (fun z : ℂ => (z - (A_freq k : ℂ)) * K_even 1 z) (𝓝[≠] (A_freq k : ℂ))
      (𝓝 (-8 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ))) := by
  let w : ℂ := (A_freq k : ℂ)
  let R : ℝ := 2 * Real.pi ^ 2
  have hR : 0 < R := by positivity
  obtain ⟨N₀, hN₀⟩ := A_freq_tail_diff_norm_ge_eos w R
  let N₁ : ℕ := max N₀ (k + 1)
  have hN₁ : ∀ (j : ℕ) (z : ℂ), z ∈ Metric.ball w R →
      A_freq (j + N₁) / 2 ≤ ‖(A_freq (j + N₁) : ℂ) - z‖ ∧
      A_freq (j + N₁) / 2 ≤ ‖(A_freq (j + N₁) : ℂ) + z‖ := by
    intro j z hz
    have hj := hN₀ (j + (N₁ - N₀)) z hz
    have hidx : j + (N₁ - N₀) + N₀ = j + N₁ := by omega
    simpa only [hidx] using hj
  let term : ℕ → ℂ → ℂ := fun n z =>
    ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) * ((A_freq n : ℂ) ^ 2 - z ^ 2)⁻¹
  let mid : ℂ → ℂ := fun z => ∑ n ∈ (Finset.range N₁).erase k, term n z
  let tail : ℂ → ℂ := fun z => ∑' j : ℕ, term (j + N₁) z
  let cbd : ℝ := 4 / (4 * Real.pi ^ 2) ^ 2
  have htail_bd : ∀ (j : ℕ) (z : ℂ), z ∈ Metric.ball w R →
      ‖term (j + N₁) z‖ ≤ cbd * ((sigmaNat 2 (j + N₁ + 1) : ℝ) / ((j + N₁ + 1 : ℕ) : ℝ) ^ 4) := by
    intro j z hz
    obtain ⟨hsub, hadd⟩ := hN₁ j z hz
    have hA_pos : 0 < A_freq (j + N₁) := A_freq_pos_eos (j + N₁)
    have hsq : (A_freq (j + N₁) : ℂ) ^ 2 - z ^ 2 = ((A_freq (j + N₁) : ℂ) - z) * ((A_freq (j + N₁) : ℂ) + z) := by ring
    dsimp only [term]
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast, norm_inv, hsq, norm_mul]
    have hprod : (A_freq (j + N₁) / 2) * (A_freq (j + N₁) / 2) ≤
        ‖(A_freq (j + N₁) : ℂ) - z‖ * ‖(A_freq (j + N₁) : ℂ) + z‖ :=
      mul_le_mul hsub hadd (by positivity) (by positivity)
    have hinv := inv_anti₀ (by positivity) hprod
    have h1 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (sigmaNat 2 (j + N₁ + 1) : ℝ) / ((j + N₁ + 1 : ℕ) : ℝ) ^ 2)
    refine h1.trans_eq ?_
    dsimp only [cbd, A_freq]
    have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    have hn0 : ((j + N₁ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hpi0, hn0]; ring
  have htail_diff : DifferentiableOn ℂ tail (Metric.ball w R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (((summable_nat_add_iff N₁).2 summable_sigmaNat_div_pow_two).mul_left cbd)
      (fun j => ?_) Metric.isOpen_ball htail_bd
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.inv ((differentiableOn_const _).sub (differentiableOn_id.pow 2)) fun z hz h0 => ?_
    have hsq : (A_freq (j + N₁) : ℂ) ^ 2 - z ^ 2 = ((A_freq (j + N₁) : ℂ) - z) * ((A_freq (j + N₁) : ℂ) + z) := by ring
    rw [hsq, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · have h1 := (hN₁ j z hz).1; rw [h0, norm_zero] at h1; linarith [A_freq_pos_eos (j + N₁)]
    · have h1 := (hN₁ j z hz).2; rw [h0, norm_zero] at h1; linarith [A_freq_pos_eos (j + N₁)]
  have htail_cont : ContinuousAt tail w :=
    (htail_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))).continuousAt
  have hmid_cont : ContinuousAt mid w := by
    have hana : AnalyticAt ℂ mid w := by
      refine Finset.analyticAt_fun_sum ((Finset.range N₁).erase k) fun n hn => ?_
      have hnk : n ≠ k := (Finset.mem_erase.mp hn).1
      refine AnalyticAt.mul analyticAt_const ((analyticAt_const.sub (analyticAt_id.pow 2)).inv ?_)
      have hsq : (A_freq n : ℂ) ^ 2 - w ^ 2 = ((A_freq n : ℂ) - w) * ((A_freq n : ℂ) + w) := by ring
      change (A_freq n : ℂ) ^ 2 - w ^ 2 ≠ 0
      rw [hsq]
      refine mul_ne_zero ?_ ?_
      · intro h0
        have h0' : (A_freq n : ℂ) = (A_freq k : ℂ) := sub_eq_zero.mp h0
        have h1 : A_freq n = A_freq k := Complex.ofReal_injective h0'
        dsimp only [A_freq] at h1
        have hpi : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
        have h2 : ((n + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := mul_left_cancel₀ hpi h1
        have h3 : n + 1 = k + 1 := by exact_mod_cast h2
        exact hnk (by omega)
      · intro h0
        have hre := congrArg Complex.re h0
        simp only [w, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
        linarith [A_freq_pos_eos n, A_freq_pos_eos k]
    exact hana.continuousAt
  let C1 : ℂ := (-1 : ℂ) ^ 2 * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ 1)
  let Pk : ℂ → ℂ := fun z =>
    -(C1 * ((sigmaNat 2 (k + 1) : ℂ) / ((k + 1 : ℕ) : ℂ) ^ 2) * z ^ 3 / (w + z))
  have h2w_ne : w + w ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith [A_freq_pos_eos k]
  have hPk_cont : ContinuousAt Pk w :=
    ((continuousAt_const.mul (continuousAt_id.pow 3)).div (continuousAt_const.add continuousAt_id) h2w_ne).neg
  have hPk_val : Pk w = -8 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ) := by
    dsimp only [Pk, C1, w, A_freq]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    push_cast
    field_simp [hpi, hk1]; ring
  have hev : (fun z : ℂ => (z - w) * K_even 1 z) =ᶠ[𝓝[≠] w]
      fun z => (z - w) * (C1 * z ^ 3 * (mid z + tail z)) + Pk z := by
    have hball : Metric.ball w R \ {w} ∈ 𝓝[≠] w := by
      rw [Set.sdiff_eq, Set.inter_comm]
      exact inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
    filter_upwards [hball] with z ⟨hz_ball, hz_ne⟩
    have hts : Summable (fun j : ℕ => term (j + N₁) z) :=
      (((summable_nat_add_iff N₁).2 summable_sigmaNat_div_pow_two).mul_left cbd).of_norm_bounded fun j =>
        htail_bd j z hz_ball
    have hsum_all := (summable_nat_add_iff (f := fun n => term n z) N₁).1 hts
    have hk_mem : k ∈ Finset.range N₁ := Finset.mem_range.mpr (by omega)
    have hsplit : S_even 1 z = term k z + mid z + tail z := by
      have h1 := (hsum_all.sum_add_tsum_nat_add N₁).symm
      have her := (Finset.add_sum_erase (Finset.range N₁) (fun n => term n z) hk_mem).symm
      rw [S_even]; exact h1.trans (by rw [her, add_assoc])
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr hz_ne
    have haddz : w + z ≠ 0 := by
      intro h0
      have hlt : ‖z - w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
      have hz_eq : z = -w := eq_neg_of_add_eq_zero_right h0
      rw [hz_eq] at hlt
      have h2 : ‖-2 * w‖ < R := by convert hlt using 1; congr 1; ring
      rw [norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num, Complex.norm_real,
        Real.norm_of_nonneg (A_freq_pos_eos k).le] at h2
      dsimp only [R, A_freq] at h2
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith [Real.pi_pos]
    have hterm_k : (z - w) * (C1 * z ^ 3 * term k z) = Pk z := by
      have hsq : (A_freq k : ℂ) ^ 2 - z ^ 2 = -(z - w) * (w + z) := by dsimp only [w]; ring
      dsimp only [term, Pk]; rw [hsq]; field_simp [hzw, haddz]
    change (z - w) * (C1 * z ^ 3 * S_even 1 z) = _
    rw [hsplit, mul_add, mul_add, mul_add, mul_add, hterm_k]; ring
  have hlim : Tendsto (fun z : ℂ => (z - w) * (C1 * z ^ 3 * (mid z + tail z)) + Pk z) (𝓝[≠] w)
      (𝓝 (0 + (-8 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ)))) := by
    have hcont : ContinuousAt (fun z : ℂ => (z - w) * (C1 * z ^ 3 * (mid z + tail z)) + Pk z) w :=
      ((continuousAt_id.sub continuousAt_const).mul
        ((continuousAt_const.mul (continuousAt_id.pow 3)).mul (hmid_cont.add htail_cont))).add hPk_cont
    simpa [sub_self, zero_mul, hPk_val] using hcont.continuousWithinAt.tendsto
  rw [zero_add] at hlim
  exact hlim.congr' hev.symm

private lemma K_even_one_expType_ray (s : ℝ) (hs : s = Real.pi / 6 ∨ s = -(Real.pi / 6)) :
    ExpType (Minor.pull (Complex.exp (Complex.I * (s : ℂ))) (K_even 1)) := by
  let C_sum : ℝ := (4 / (4 * Real.pi ^ 2) ^ 2) *
    ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4
  let C : ℝ := ‖(-1 : ℂ) ^ 2 * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ 1)‖ * (6 : ℝ) * C_sum
  refine ⟨C, 1, by positivity, zero_le_one, fun v hv => ?_⟩
  let μ : ℂ := Complex.exp (Complex.I * (s : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I s
  have hsin_abs : |Real.sin s| = 1 / 2 := by
    rcases hs with rfl | rfl
    · rw [Real.sin_pi_div_six]; norm_num
    · rw [Real.sin_neg, abs_neg, Real.sin_pi_div_six]; norm_num
  have hcos_nn : 0 ≤ Real.cos s := by
    rcases hs with rfl | rfl
    · rw [Real.cos_pi_div_six]; positivity
    · rw [Real.cos_neg, Real.cos_pi_div_six]; positivity
  have hsub_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) - μ * (v : ℂ)‖ := fun n => by
    have hinv_norm : ‖Complex.exp (-Complex.I * (s : ℂ))‖ = 1 := by
      rw [show -Complex.I * (s : ℂ) = ((-s : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I (-s)
    have hmul : Complex.exp (-Complex.I * (s : ℂ)) * ((A_freq n : ℂ) - μ * (v : ℂ)) =
        (A_freq n : ℂ) * Complex.exp (-Complex.I * (s : ℂ)) - (v : ℂ) := by
      dsimp only [μ]; rw [mul_sub, ← mul_assoc, ← Complex.exp_add]
      have : -Complex.I * (s : ℂ) + Complex.I * (s : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero, one_mul]; ring
    have him : ((A_freq n : ℂ) * Complex.exp (-Complex.I * (s : ℂ)) - (v : ℂ)).im = -A_freq n * Real.sin s := by
      rw [show -Complex.I * (s : ℂ) = ((-s : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I]
      simp only [Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Real.sin_neg]
      ring
    calc A_freq n / 2 = |A_freq n * Real.sin s| := by
          rw [abs_mul, abs_of_pos (A_freq_pos_eos n), hsin_abs]; ring
      _ = |-A_freq n * Real.sin s| := by rw [neg_mul, abs_neg]
      _ = |((A_freq n : ℂ) * Complex.exp (-Complex.I * (s : ℂ)) - (v : ℂ)).im| := by rw [him]
      _ ≤ ‖(A_freq n : ℂ) * Complex.exp (-Complex.I * (s : ℂ)) - (v : ℂ)‖ := Complex.abs_im_le_norm _
      _ = ‖Complex.exp (-Complex.I * (s : ℂ)) * ((A_freq n : ℂ) - μ * (v : ℂ))‖ := by rw [hmul]
      _ = ‖(A_freq n : ℂ) - μ * (v : ℂ)‖ := by rw [norm_mul, hinv_norm, one_mul]
  have hadd_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) + μ * (v : ℂ)‖ := fun n => by
    have hre : ((A_freq n : ℂ) + μ * (v : ℂ)).re = A_freq n + v * Real.cos s := by
      dsimp only [μ]
      rw [mul_comm Complex.I (s : ℂ), Complex.exp_ofReal_mul_I]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have h1 : A_freq n + v * Real.cos s ≤ ‖(A_freq n : ℂ) + μ * (v : ℂ)‖ := by
      rw [← hre]; exact Complex.re_le_norm _
    have h2 : 0 ≤ v * Real.cos s := mul_nonneg hv hcos_nn
    linarith [A_freq_pos_eos n]
  let cbd : ℝ := 4 / (4 * Real.pi ^ 2) ^ 2
  have hterm_bd : ∀ n : ℕ,
      ‖((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) * ((A_freq n : ℂ) ^ 2 - (μ * (v : ℂ)) ^ 2)⁻¹‖ ≤
        cbd * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := fun n => by
    have hA_pos : 0 < A_freq n := A_freq_pos_eos n
    have hsq : (A_freq n : ℂ) ^ 2 - (μ * (v : ℂ)) ^ 2 = ((A_freq n : ℂ) - μ * (v : ℂ)) * ((A_freq n : ℂ) + μ * (v : ℂ)) := by ring
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast, norm_inv, hsq, norm_mul]
    have hprod := mul_le_mul (hsub_ge n) (hadd_ge n) (by positivity) (by positivity)
    have hinv := inv_anti₀ (by positivity) hprod
    have h1 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)
    refine h1.trans_eq ?_
    dsimp only [cbd, A_freq]
    have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hpi0, hn0]; ring
  have hdom := summable_sigmaNat_div_pow_two.mul_left cbd
  have hsn : Summable (fun n : ℕ =>
      ‖((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) * ((A_freq n : ℂ) ^ 2 - (μ * (v : ℂ)) ^ 2)⁻¹‖) :=
    hdom.of_norm_bounded fun n => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hterm_bd n
  have hS_bd : ‖S_even 1 (μ * (v : ℂ))‖ ≤ C_sum := by
    dsimp only [S_even, C_sum]
    calc ‖∑' n : ℕ, _‖ ≤ ∑' n : ℕ, ‖_‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' n : ℕ, cbd * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := hsn.tsum_le_tsum hterm_bd hdom
      _ = cbd * ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 := tsum_mul_left
  have hv_pow : v ^ 3 ≤ 6 * Real.exp v := by
    have h1 := Real.pow_div_factorial_le_exp v hv 3
    have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hfac] at h1; linarith
  change ‖μ * K_even 1 (μ * (v : ℂ))‖ ≤ C * Real.exp (1 * v)
  rw [norm_mul, hμ_norm, one_mul, K_even, norm_mul, norm_mul, norm_mul,
    norm_pow (μ * (v : ℂ)), norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_of_nonneg hv,
    ← norm_mul]
  calc ‖(-1 : ℂ) ^ 2 * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ 1)‖ * v ^ 3 * ‖S_even 1 (μ * (v : ℂ))‖
      ≤ ‖(-1 : ℂ) ^ 2 * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ 1)‖ * (6 * Real.exp v) * C_sum := by gcongr
    _ = C * Real.exp (1 * v) := by dsimp only [C]; rw [one_mul]; ring

/-- Complete meromorphic Borel data for `K_{S²}(ξ) = K₂(ξ) - K₂(2 ξ)` along `[0, ∞)`
with simple poles at `ω_k = 2π²(k + 1)` and strictly positive residues `res_S2 k ≠ 0`. -/
private def K_S2_borelData : MeromorphicBorelData K_S2 ω_S2 res_S2 where
  θ₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := Real.pi ^ 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hθ₀_lt := by linarith [Real.pi_pos]
  hε_pos := by positivity
  ω_pos := by dsimp only [ω_S2]; positivity
  ω_mono := fun a b hab => by
    dsimp only [ω_S2]
    have hlt : ((a + 1 : ℕ) : ℝ) < ((b + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_lt_succ hab
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  res_ne_zero := res_S2_ne_zero
  analyticOn := fun w hw => by
    have hw_wedge : w ∈ borelWedge (Real.pi / 4) (2 * Real.pi ^ 2) := by
      rcases hw.1 with hball | hsec
      · left; rw [Metric.mem_ball, dist_zero_right] at hball ⊢
        have hpi2 : 0 < Real.pi ^ 2 := by positivity
        linarith
      · right; exact hsec
    have h2w_wedge : 2 * w ∈ borelWedge (Real.pi / 4) (2 * Real.pi ^ 2) := by
      rcases hw.1 with hball | hsec
      · left; rw [Metric.mem_ball, dist_zero_right] at hball ⊢
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
      · right
        refine ⟨?_, ?_⟩
        · simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; linarith [hsec.1]
        · simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero,
            Complex.mul_re, sub_zero, abs_mul, abs_of_pos (zero_lt_two : (0 : ℝ) < 2)]
          linarith [hsec.2]
    have hw_ne1 : ∀ n : ℕ, w ≠ (A_freq n : ℂ) := by
      intro n h0; apply hw.2; refine ⟨2 * n + 1, ?_⟩
      rw [h0]; dsimp only [ω_S2, A_freq]; push_cast; ring
    have hw_ne2 : ∀ n : ℕ, 2 * w ≠ (A_freq n : ℂ) := by
      intro n h0; apply hw.2; refine ⟨n, ?_⟩
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      have hdiv : w = (A_freq n : ℂ) / 2 := by rw [← h0]; field_simp [h2]
      rw [hdiv]; dsimp only [ω_S2, A_freq]; push_cast; field_simp [h2]; ring
    have ha1 := K_even_one_analyticAt hw_wedge hw_ne1
    have ha2 : AnalyticAt ℂ (fun z : ℂ => K_even 1 (2 * z)) w :=
      AnalyticAt.comp (g := K_even 1) (f := fun z : ℂ => 2 * z)
        (K_even_one_analyticAt h2w_wedge hw_ne2) (analyticAt_const.mul analyticAt_id)
    exact ha1.sub ha2
  simple_pole := fun k => by
    have h2_tend : Tendsto (fun z : ℂ => 2 * z) (𝓝[≠] (ω_S2 k : ℂ)) (𝓝[≠] (A_freq k : ℂ)) := by
      have h2w : (2 : ℂ) * (ω_S2 k : ℂ) = (A_freq k : ℂ) := by
        dsimp only [ω_S2, A_freq]; push_cast; ring
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · rw [← h2w]
        exact ((continuousAt_const.mul continuousAt_id).tendsto).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        intro h0
        apply hz
        have h2 : (2 : ℂ) ≠ 0 := by norm_num
        rw [← h2w] at h0
        exact mul_left_cancel₀ h2 h0
    have hpart2 : Tendsto (fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 (2 * z)) (𝓝[≠] (ω_S2 k : ℂ))
        (𝓝 (-4 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ))) := by
      have hcomp := (K_even_one_simple_pole k).comp h2_tend
      have hscaled := hcomp.const_mul (1 / 2 : ℂ)
      have heq : (fun z : ℂ => (1 / 2 : ℂ) * ((2 * z - (A_freq k : ℂ)) * K_even 1 (2 * z))) =
          fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 (2 * z) := by
        funext z
        have h2w : (A_freq k : ℂ) = 2 * (ω_S2 k : ℂ) := by dsimp only [ω_S2, A_freq]; push_cast; ring
        rw [h2w]; ring
      rw [show (fun x => (1 / 2 : ℂ) * (((fun z => (z - (A_freq k : ℂ)) * K_even 1 z) ∘ (fun z => 2 * z)) x)) =
        fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 (2 * z) from heq] at hscaled
      have hlim : (1 / 2 : ℂ) * (-8 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ)) =
          -4 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ) := by ring
      rwa [hlim] at hscaled
    by_cases hev : Even (k + 1)
    · rcases hev with ⟨r, hr⟩
      have hr1 : 1 ≤ r := by omega
      have hdiv : (k + 1) / 2 = r := by omega
      have hω_eq : (ω_S2 k : ℂ) = (A_freq (r - 1) : ℂ) := by
        dsimp only [ω_S2, A_freq]
        have hr_sub : r - 1 + 1 = r := by omega
        rw [hr_sub]
        have hk2 : ((k : ℂ) + 1) = 2 * (r : ℂ) := by exact_mod_cast (show k + 1 = 2 * r by omega)
        push_cast; rw [hk2]; ring
      have hpart1 : Tendsto (fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 z) (𝓝[≠] (ω_S2 k : ℂ))
          (𝓝 (-8 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 ((k + 1) / 2) : ℂ))) := by
        rw [hω_eq, hdiv, show r = r - 1 + 1 by omega]
        exact K_even_one_simple_pole (r - 1)
      have hsub := hpart1.sub hpart2
      have hfun : (fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 z - (z - (ω_S2 k : ℂ)) * K_even 1 (2 * z)) =
          fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_S2 z := by
        funext z; dsimp only [K_S2]; ring
      rw [hfun] at hsub
      have hres : -8 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 ((k + 1) / 2) : ℂ) -
          -4 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ) = res_S2 k := by
        dsimp only [res_S2]; simp only [show Even (k + 1) from ⟨r, hr⟩, ↓reduceIte]; ring
      rwa [hres] at hsub
    · have hw_wedge : (ω_S2 k : ℂ) ∈ borelWedge (Real.pi / 4) (2 * Real.pi ^ 2) := by
        have hpos : 0 < ω_S2 k := by dsimp only [ω_S2]; positivity
        exact Or.inr ⟨by simpa using hpos, by simpa [Real.tan_pi_div_four] using hpos⟩
      have hw_ne : ∀ n : ℕ, (ω_S2 k : ℂ) ≠ (A_freq n : ℂ) := by
        intro n h0
        have h1 : ω_S2 k = A_freq n := by exact_mod_cast h0
        dsimp only [ω_S2, A_freq] at h1
        have hpi : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
        have h2 : ((k + 1 : ℕ) : ℝ) = 2 * ((n + 1 : ℕ) : ℝ) :=
          mul_left_cancel₀ hpi (by linarith)
        have h3 : k + 1 = 2 * (n + 1) := by exact_mod_cast h2
        exact hev ⟨n + 1, by omega⟩
      have ha1 := (K_even_one_analyticAt hw_wedge hw_ne).continuousAt
      have hpart1 : Tendsto (fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 z) (𝓝[≠] (ω_S2 k : ℂ)) (𝓝 0) := by
        have hcont : ContinuousAt (fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 z) (ω_S2 k : ℂ) :=
          (continuousAt_id.sub continuousAt_const).mul ha1
        simpa [sub_self, zero_mul] using hcont.continuousWithinAt.tendsto
      have hsub := hpart1.sub hpart2
      have hfun : (fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_even 1 z - (z - (ω_S2 k : ℂ)) * K_even 1 (2 * z)) =
          fun z : ℂ => (z - (ω_S2 k : ℂ)) * K_S2 z := by
        funext z; dsimp only [K_S2]; ring
      rw [hfun] at hsub
      have hres : (0 : ℂ) - -4 * (Real.pi : ℂ) ^ 2 * (sigmaNat 2 (k + 1) : ℂ) = res_S2 k := by
        dsimp only [res_S2]; simp only [hev, ↓reduceIte]; ring
      rwa [hres] at hsub
  expType_plus := by
    obtain ⟨C, a, hC, ha, hbd⟩ := K_even_one_expType_ray (Real.pi / 6) (Or.inl rfl)
    refine ⟨2 * C, 2 * a, by positivity, by positivity, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (Complex.I * ((Real.pi / 6 : ℝ) : ℂ))
    have h1 := hbd v hv
    have h2 := hbd (2 * v) (by positivity)
    change ‖μ * (K_even 1 (μ * (v : ℂ)) - K_even 1 (2 * (μ * (v : ℂ))))‖ ≤ 2 * C * Real.exp (2 * a * v)
    rw [mul_sub]
    have harg : 2 * (μ * (v : ℂ)) = μ * ((2 * v : ℝ) : ℂ) := by push_cast; ring
    have he1 : Real.exp (a * v) ≤ Real.exp (2 * a * v) := Real.exp_le_exp.mpr (by nlinarith)
    have he2 : Real.exp (a * (2 * v)) = Real.exp (2 * a * v) := by congr 1; ring
    calc ‖μ * K_even 1 (μ * (v : ℂ)) - μ * K_even 1 (2 * (μ * (v : ℂ)))‖
        ≤ ‖μ * K_even 1 (μ * (v : ℂ))‖ + ‖μ * K_even 1 (μ * ((2 * v : ℝ) : ℂ))‖ := by
          rw [harg]; exact norm_sub_le _ _
      _ ≤ C * Real.exp (a * v) + C * Real.exp (a * (2 * v)) := add_le_add h1 h2
      _ ≤ C * Real.exp (2 * a * v) + C * Real.exp (2 * a * v) := by
          rw [he2]; exact add_le_add (mul_le_mul_of_nonneg_left he1 hC) le_rfl
      _ = 2 * C * Real.exp (2 * a * v) := by ring
  expType_minus := by
    obtain ⟨C, a, hC, ha, hbd⟩ := K_even_one_expType_ray (-(Real.pi / 6)) (Or.inr rfl)
    refine ⟨2 * C, 2 * a, by positivity, by positivity, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (-Complex.I * ((Real.pi / 6 : ℝ) : ℂ))
    have hμ_eq : μ = Complex.exp (Complex.I * ((-(Real.pi / 6) : ℝ) : ℂ)) := by
      dsimp only [μ]; congr 1; push_cast; ring
    have h1 := hbd v hv
    have h2 := hbd (2 * v) (by positivity)
    change ‖μ * (K_even 1 (μ * (v : ℂ)) - K_even 1 (2 * (μ * (v : ℂ))))‖ ≤ 2 * C * Real.exp (2 * a * v)
    rw [hμ_eq, mul_sub]
    have harg : 2 * (Complex.exp (Complex.I * ((-(Real.pi / 6) : ℝ) : ℂ)) * (v : ℂ)) =
        Complex.exp (Complex.I * ((-(Real.pi / 6) : ℝ) : ℂ)) * ((2 * v : ℝ) : ℂ) := by push_cast; ring
    have he1 : Real.exp (a * v) ≤ Real.exp (2 * a * v) := Real.exp_le_exp.mpr (by nlinarith)
    have he2 : Real.exp (a * (2 * v)) = Real.exp (2 * a * v) := by congr 1; ring
    calc ‖_ - _‖
        ≤ ‖Complex.exp (Complex.I * ((-(Real.pi / 6) : ℝ) : ℂ)) *
            K_even 1 (Complex.exp (Complex.I * ((-(Real.pi / 6) : ℝ) : ℂ)) * (v : ℂ))‖ +
          ‖Complex.exp (Complex.I * ((-(Real.pi / 6) : ℝ) : ℂ)) *
            K_even 1 (Complex.exp (Complex.I * ((-(Real.pi / 6) : ℝ) : ℂ)) * ((2 * v : ℝ) : ℂ))‖ := by
          rw [harg]; exact norm_sub_le _ _
      _ ≤ C * Real.exp (a * v) + C * Real.exp (a * (2 * v)) := add_le_add h1 h2
      _ ≤ C * Real.exp (2 * a * v) + C * Real.exp (2 * a * v) := by
          rw [he2]; exact add_le_add (mul_le_mul_of_nonneg_left he1 hC) le_rfl
      _ = 2 * C * Real.exp (2 * a * v) := by ring

/-! Now match `formalSeries (K_even 1)` to `emSeries (hFun 1)` and derive `f_S2_hasAsympExp`. -/

private lemma summable_nat_inv_pow_eos (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => ((n : ℂ) ^ k)⁻¹) := by
  have hk_gt : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hR : Summable (fun n : ℕ => ((n : ℝ) ^ (-(k : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine hR.of_norm_bounded fun n => ?_
  rw [norm_inv, norm_pow, Complex.norm_natCast]
  cases n with
  | zero =>
    have hk0 : k ≠ 0 := by omega
    have hkr : -(k : ℝ) ≠ 0 := by linarith
    simp [hk0, Real.zero_rpow hkr]
  | succ m =>
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]

private lemma tsum_sigmaNat_two_div_pow (p : ℕ) (hp : 1 ≤ p) :
    (∑' n : ℕ, ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 + 2 * p))) =
      riemannZeta ((2 * p : ℕ) : ℂ) * riemannZeta ((2 + 2 * p : ℕ) : ℂ) := by
  have hC1 : Summable (fun n : ℕ => ((n : ℂ) ^ (2 * p))⁻¹) := summable_nat_inv_pow_eos (2 * p) (by omega)
  have hC2 : Summable (fun n : ℕ => ((n : ℂ) ^ (2 + 2 * p))⁻¹) := summable_nat_inv_pow_eos (2 + 2 * p) (by omega)
  have hsb : Summable (fun a : ℕ+ => ((a : ℂ) ^ (2 * p))⁻¹) := hC1.subtype _
  have hsab : Summable (fun b : ℕ+ => ((b : ℂ) ^ (2 + 2 * p))⁻¹) := hC2.subtype _
  have hprod_sum : Summable (fun x : ℕ+ × ℕ+ => ((x.1 : ℂ) ^ (2 * p))⁻¹ * ((x.2 : ℂ) ^ (2 + 2 * p))⁻¹) :=
    (Summable.mul_of_nonneg hsb.norm hsab.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).of_norm_bounded
      fun x => by rw [norm_mul]
  have hzeta1 : riemannZeta ((2 * p : ℕ) : ℂ) = ∑' a : ℕ+, ((a : ℂ) ^ (2 * p))⁻¹ := by
    rw [zeta_nat_eq_tsum_of_gt_one (by omega : 1 < 2 * p)]
    simp_rw [one_div]
    rw [← tsum_zero_pnat_eq_tsum_nat]
    · simp [show 2 * p ≠ 0 by omega]
    · exact hC1
  have hzeta2 : riemannZeta ((2 + 2 * p : ℕ) : ℂ) = ∑' b : ℕ+, ((b : ℂ) ^ (2 + 2 * p))⁻¹ := by
    rw [zeta_nat_eq_tsum_of_gt_one (by omega : 1 < 2 + 2 * p)]
    simp_rw [one_div]
    rw [← tsum_zero_pnat_eq_tsum_nat]
    · simp
    · exact hC2
  rw [hzeta1, hzeta2, tsum_mul_tsum_of_summable_norm hsb.norm hsab.norm]
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  have hsig_summ : Summable (fun x : (n : ℕ+) × Nat.divisorsAntidiagonal n =>
      (((sigmaAntidiagonalEquivProd x).1 : ℂ) ^ (2 * p))⁻¹ *
      (((sigmaAntidiagonalEquivProd x).2 : ℂ) ^ (2 + 2 * p))⁻¹) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hprod_sum
  rw [Summable.tsum_sigma hsig_summ]
  let ePN : ℕ ≃ ℕ+ :=
    { toFun := fun n : ℕ => (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)
      invFun := fun m : ℕ+ => (m : ℕ) - 1
      left_inv := fun n => by simp
      right_inv := fun m => Subtype.ext (Nat.sub_add_cancel m.pos) }
  rw [← ePN.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype, Finset.univ_eq_attach]
  have hsum_anti : ∑ x ∈ (ePN n : ℕ).divisorsAntidiagonal.attach,
      (((sigmaAntidiagonalEquivProd ⟨ePN n, x⟩).1 : ℂ) ^ (2 * p))⁻¹ *
      (((sigmaAntidiagonalEquivProd ⟨ePN n, x⟩).2 : ℂ) ^ (2 + 2 * p))⁻¹ =
      ∑ x ∈ (n + 1).divisorsAntidiagonal, ((x.1 : ℂ) ^ (2 * p))⁻¹ * ((x.2 : ℂ) ^ (2 + 2 * p))⁻¹ :=
    Finset.sum_attach (n + 1).divisorsAntidiagonal
      (fun x => ((x.1 : ℂ) ^ (2 * p))⁻¹ * ((x.2 : ℂ) ^ (2 + 2 * p))⁻¹)
  rw [hsum_anti, Nat.sum_divisorsAntidiagonal (fun d e => ((d : ℂ) ^ (2 * p))⁻¹ * ((e : ℂ) ^ (2 + 2 * p))⁻¹)]
  simp only [sigmaNat, Nat.succ_ne_zero, ↓reduceIte]
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  have hdiv_mul : ((d : ℕ) : ℂ) * (((n + 1) / d : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  have hne_n : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hdiv_eq : (((n + 1) / d : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) / (d : ℂ) := by
    field_simp [hd_pos]; rw [mul_comm]; exact hdiv_mul
  rw [hdiv_eq, div_pow, pow_add (d : ℂ) 2 (2 * p), Nat.cast_pow]
  field_simp [hd_pos, hne_n]

private lemma iteratedDeriv_qComplex_zero_eos (n : ℕ) :
    iteratedDeriv n qComplex 0 = (bernoulli n : ℂ) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hq_an : AnalyticAt ℂ qComplex 0 :=
      (expAux_analytic_eos 0).inv (by rw [expAux_zero_eos]; exact one_ne_zero)
    have hexp_an : AnalyticAt ℂ (fun z : ℂ => Complex.exp z - 1) 0 := by fun_prop
    have heq_nhds : (fun z : ℂ => qComplex z * (Complex.exp z - 1)) =ᶠ[𝓝 (0 : ℂ)] id := by
      have hne : ∀ᶠ z in 𝓝 (0 : ℂ), expAux z ≠ 0 :=
        (expAux_analytic_eos 0).continuousAt.eventually_ne (by rw [expAux_zero_eos]; exact one_ne_zero)
      filter_upwards [hne] with z hz
      dsimp only [qComplex, id]; rw [← expAux_mul_sub_eos z]; field_simp [hz]
    have hderiv_eq : iteratedDeriv (n + 1) (fun z : ℂ => qComplex z * (Complex.exp z - 1)) 0 =
        iteratedDeriv (n + 1) id (0 : ℂ) := heq_nhds.iteratedDeriv_eq (n + 1)
    rw [iteratedDeriv_fun_mul hq_an.contDiffAt hexp_an.contDiffAt] at hderiv_eq
    have hcexp0 : ∀ k : ℕ, iteratedDeriv k Complex.exp 0 = 1 := fun k => by
      induction k with
      | zero => simp
      | succ k ihk => rw [iteratedDeriv_succ', Complex.deriv_exp]; exact ihk
    have hexp_deriv : ∀ m : ℕ, iteratedDeriv m (fun z : ℂ => Complex.exp z - 1) 0 =
        if m = 0 then 0 else 1 := fun m => by
      cases m with
      | zero => simp
      | succ k =>
        rw [iteratedDeriv_succ']
        have h1 : deriv (fun z : ℂ => Complex.exp z - 1) = Complex.exp := by ext z; simp
        rw [h1, hcexp0 k]; simp
    have h_lhs : (∑ k ∈ Finset.range (n + 1 + 1),
        ((n + 1).choose k : ℂ) * iteratedDeriv k qComplex 0 *
          iteratedDeriv (n + 1 - k) (fun z : ℂ => Complex.exp z - 1) 0) =
        ∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℂ) * iteratedDeriv k qComplex 0 := by
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, hexp_deriv 0, ↓reduceIte, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkne : n + 1 - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
      simp [hexp_deriv (n + 1 - k), hkne]
    have h_rhs : iteratedDeriv (n + 1) (id : ℂ → ℂ) 0 = if n = 0 then 1 else 0 := by
      cases n with
      | zero => simp
      | succ m =>
        rw [iteratedDeriv_succ']
        have hid : deriv (id : ℂ → ℂ) = fun _ => 1 := by ext z; simp
        rw [hid, iteratedDeriv_const]
    rw [h_lhs, h_rhs] at hderiv_eq
    have hbern : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℂ) * (bernoulli k : ℂ)) =
        if n = 0 then 1 else 0 := by
      have hb := congrArg (fun q : ℚ => (q : ℂ)) (sum_bernoulli (n + 1))
      cases n with
      | zero => simp
      | succ m =>
        have hne1 : m + 1 + 1 ≠ 1 := by omega
        simp only [hne1, ↓reduceIte, Rat.cast_zero, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast] at hb
        simpa [Nat.succ_ne_zero] using hb
    have hdiff : ∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose k : ℂ) * (iteratedDeriv k qComplex 0 - (bernoulli k : ℂ)) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, hderiv_eq, hbern, sub_self]
    rw [Finset.sum_range_succ] at hdiff
    have htail : ∑ k ∈ Finset.range n,
        ((n + 1).choose k : ℂ) * (iteratedDeriv k qComplex 0 - (bernoulli k : ℂ)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [ih k (Finset.mem_range.mp hk), sub_self, mul_zero]
    rw [htail, zero_add, Nat.choose_succ_self_right] at hdiff
    have hne0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hne0)

private lemma iteratedDeriv_hFun_one_zero (r : ℕ) :
    iteratedDeriv r (hFun 1) 0 =
      if r = 0 then 0 else (r : ℂ) * (bernoulli (r - 1) : ℂ) := by
  have heq : hFun 1 = fun x : ℝ => (x : ℂ) * qComplex (x : ℂ) := by funext x; simp [hFun, qFun]
  rw [heq]
  have hC_an : ∀ x : ℝ, AnalyticAt ℂ (fun z : ℂ => z * qComplex z) (x : ℂ) := fun x =>
    analyticAt_id.mul ((expAux_analytic_eos (x : ℂ)).inv (expAux_ne_zero_of_abs_im_lt (by simp; positivity)))
  rw [iteratedDeriv_ofReal_comp_analytic hC_an, Complex.ofReal_zero]
  have hq_an : AnalyticAt ℂ qComplex 0 :=
    (expAux_analytic_eos 0).inv (by rw [expAux_zero_eos]; exact one_ne_zero)
  change iteratedDeriv r (fun z : ℂ => id z * qComplex z) 0 = _
  rw [iteratedDeriv_fun_mul (analyticAt_id.contDiffAt) hq_an.contDiffAt]
  cases r with
  | zero => simp
  | succ k =>
    have hid : ∀ i : ℕ, iteratedDeriv i (id : ℂ → ℂ) 0 = if i = 1 then 1 else 0 := fun i => by
      cases i with
      | zero => simp
      | succ j =>
        rw [iteratedDeriv_succ']
        have h1 : deriv (id : ℂ → ℂ) = fun _ => 1 := by ext z; simp
        rw [h1]
        cases j with
        | zero => simp
        | succ m => simp [iteratedDeriv_const]
    rw [Finset.sum_eq_single 1]
    · simp [hid 1, iteratedDeriv_qComplex_zero_eos k]
    · intro i _ hi; simp [hid i, hi]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot

private lemma formalSeries_K_even_one :
    formalSeries (K_even 1) =
      PowerSeries.X * (emSeries (hFun 1) + PowerSeries.C (1 / 12 : ℂ) * PowerSeries.X) := by
  -- Compute Taylor coefficients of S_even 1 at 0 via Cauchy integral / uniform analyticity on ball 0 (2π²)!
  let R : ℝ := 2 * Real.pi ^ 2
  have hR : 0 < R := by positivity
  let term : ℕ → ℂ → ℂ := fun n z =>
    ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) * ((A_freq n : ℂ) ^ 2 - z ^ 2)⁻¹
  have hA_low : ∀ (n : ℕ) {z : ℂ}, z ∈ Metric.ball (0 : ℂ) R →
      2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ ‖(A_freq n : ℂ) - z‖ ∧
      2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ ‖(A_freq n : ℂ) + z‖ := by
    intro n z hz
    have hlt : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hAn : ‖(A_freq n : ℂ)‖ = 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos n).le]; rfl
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    constructor
    · have := norm_sub_norm_le (A_freq n : ℂ) z; rw [hAn] at this; dsimp only [R] at hlt; nlinarith [Real.pi_pos]
    · have := norm_sub_norm_le (A_freq n : ℂ) (-z); rw [sub_neg_eq_add, hAn, norm_neg] at this
      dsimp only [R] at hlt; nlinarith [Real.pi_pos]
  have hterm_bd0 : ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball (0 : ℂ) R →
      ‖term n z‖ ≤ (1 / (2 * Real.pi ^ 2) ^ 2) * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := by
    intro n z hz
    obtain ⟨h1, h2⟩ := hA_low n hz
    have hsq : (A_freq n : ℂ) ^ 2 - z ^ 2 = ((A_freq n : ℂ) - z) * ((A_freq n : ℂ) + z) := by ring
    dsimp only [term]
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast, norm_inv, hsq, norm_mul]
    have hpos : 0 < 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by positivity
    have hinv := inv_anti₀ (by positivity) (mul_le_mul h1 h2 hpos.le (norm_nonneg _))
    refine (mul_le_mul_of_nonneg_left hinv (by positivity)).trans_eq ?_
    have hpi : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hpi, hn0]
  have hS_an : AnalyticOnNhd ℂ (S_even 1) (Metric.ball (0 : ℂ) R) := by
    refine (Complex.differentiableOn_tsum_of_summable_norm
      (summable_sigmaNat_div_pow_two.mul_left _) (fun n => ?_) Metric.isOpen_ball hterm_bd0).analyticOnNhd
      Metric.isOpen_ball
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.inv ((differentiableOn_const _).sub (differentiableOn_id.pow 2)) fun z hz h0 => ?_
    obtain ⟨h1, h2⟩ := hA_low n hz
    have hsq : (A_freq n : ℂ) ^ 2 - z ^ 2 = ((A_freq n : ℂ) - z) * ((A_freq n : ℂ) + z) := by ring
    rw [hsq, mul_eq_zero] at h0
    have hpos : 0 < 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by positivity
    rcases h0 with h0 | h0
    · rw [h0, norm_zero] at h1; linarith
    · rw [h0, norm_zero] at h2; linarith
  -- Compute iteratedDeriv s (S_even 1) 0 via Cauchy's formula / geometric series expansion on ball 0 (R/2)!
  -- Even simpler: S_even 1 z = ∑_{p=0}^∞ c_p z^{2p} on ball 0 R, so HasFPowerSeriesOnBall gives ALL derivatives at 0!
  let aCoeff : ℕ → ℂ := fun s =>
    if Even s then
      ∑' n : ℕ, ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) / (A_freq n : ℂ) ^ (s + 2)
    else 0
  have hS_series : ∀ z ∈ Metric.ball (0 : ℂ) R,
      HasSum (fun s : ℕ => aCoeff s * z ^ s) (S_even 1 z) := by
    intro z hz
    have hz_lt : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
    -- Double sum over (n, m) of (σ₂(n+1)/(n+1)²) * z^{2m} / A_n^{2m+2} is absolutely summable!
    let f : ℕ × ℕ → ℂ := fun p =>
      ((sigmaNat 2 (p.1 + 1) : ℂ) / ((p.1 + 1 : ℕ) : ℂ) ^ 2) * (z ^ (2 * p.2) / (A_freq p.1 : ℂ) ^ (2 * p.2 + 2))
    have hq_lt : ‖z‖ / (4 * Real.pi ^ 2) < 1 / 2 := by
      dsimp only [R] at hz_lt
      have h4 : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
      exact (div_lt_iff₀ h4).mpr (by linarith)
    have hf_norm : Summable (fun p : ℕ × ℕ => ‖f p‖) := by
      have hgeom : Summable (fun m : ℕ => ((1 / 2 : ℝ) ^ 2) ^ m) :=
        summable_geometric_of_lt_one (by positivity) (by norm_num)
      have hprod := Summable.mul_of_nonneg (summable_sigmaNat_div_pow_two.mul_left (1 / (4 * Real.pi ^ 2) ^ 2))
        hgeom (fun _ => by positivity) (fun _ => by positivity)
      refine hprod.of_norm_bounded fun ⟨n, m⟩ => ?_
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      dsimp only [f]
      rw [norm_mul, norm_div, norm_div, Complex.norm_natCast, norm_pow, norm_pow, norm_pow,
        Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos n).le]
      have hA_ge : 4 * Real.pi ^ 2 ≤ A_freq n := by
        dsimp only [A_freq]
        have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        nlinarith [Real.pi_pos]
      have hrat : ‖z‖ / A_freq n ≤ 1 / 2 :=
        (div_le_div_of_nonneg_left (norm_nonneg z) (by positivity) hA_ge).trans hq_lt.le
      have hpow_le : (‖z‖ / A_freq n) ^ (2 * m) ≤ ((1 / 2 : ℝ) ^ 2) ^ m := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (by positivity)
          (pow_le_pow_left₀ (div_nonneg (norm_nonneg z) (A_freq_pos_eos n).le) hrat 2) m
      have hsplit : ‖z‖ ^ (2 * m) / A_freq n ^ (2 * m + 2) =
          (1 / A_freq n ^ 2) * (‖z‖ / A_freq n) ^ (2 * m) := by
        rw [pow_add, div_pow]; field_simp [(A_freq_pos_eos n).ne']
      rw [hsplit]
      have hA2 : 1 / A_freq n ^ 2 = (1 / (4 * Real.pi ^ 2) ^ 2) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        dsimp only [A_freq]
        have hpi : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
        have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hpi, hn0]
      rw [hA2]
      calc ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) *
            ((1 / (4 * Real.pi ^ 2) ^ 2) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) * (‖z‖ / A_freq n) ^ (2 * m))
          = (1 / (4 * Real.pi ^ 2) ^ 2 * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4)) *
              (‖z‖ / A_freq n) ^ (2 * m) := by ring
        _ ≤ (1 / (4 * Real.pi ^ 2) ^ 2 * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4)) *
              ((1 / 2 : ℝ) ^ 2) ^ m := mul_le_mul_of_nonneg_left hpow_le (by positivity)
    have hf_summ : Summable f := hf_norm.of_norm
    have hrow : ∀ n : ℕ, ∑' m : ℕ, f (n, m) = term n z := fun n => by
      dsimp only [f, term]
      have hqA : ‖z ^ 2 / (A_freq n : ℂ) ^ 2‖ < 1 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos n).le]
        have hA_ge : 4 * Real.pi ^ 2 ≤ A_freq n := by
          dsimp only [A_freq]
          have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          nlinarith [Real.pi_pos]
        have h1 : ‖z‖ / A_freq n < 1 / 2 := (div_le_div_of_nonneg_left (norm_nonneg z) (by positivity) hA_ge).trans_lt hq_lt
        rw [← div_pow]
        nlinarith [div_nonneg (norm_nonneg z) (A_freq_pos_eos n).le]
      have hterm_eq : ∀ m : ℕ,
          ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) * (z ^ (2 * m) / (A_freq n : ℂ) ^ (2 * m + 2)) =
            (((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) / (A_freq n : ℂ) ^ 2) *
              (z ^ 2 / (A_freq n : ℂ) ^ 2) ^ m := fun m => by
        rw [pow_add, pow_mul, pow_mul, div_pow]
        have hA0 : (A_freq n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (A_freq_pos_eos n).ne'
        field_simp [hA0]
      simp_rw [hterm_eq, tsum_mul_left, tsum_geometric_of_norm_lt_one hqA]
      have hA0 : (A_freq n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (A_freq_pos_eos n).ne'
      have hsub0 : (A_freq n : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
        have h1 := (hA_low n hz).1; have h2 := (hA_low n hz).2
        have hpos : 0 < 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by positivity
        rw [show (A_freq n : ℂ) ^ 2 - z ^ 2 = ((A_freq n : ℂ) - z) * ((A_freq n : ℂ) + z) by ring]
        exact mul_ne_zero (fun h0 => by rw [h0, norm_zero] at h1; linarith)
          (fun h0 => by rw [h0, norm_zero] at h2; linarith)
      have h1mz : 1 - z ^ 2 / (A_freq n : ℂ) ^ 2 ≠ 0 := by
        intro h0; apply hsub0; field_simp [hA0] at h0; simpa using h0
      field_simp [hA0, hsub0, h1mz]
    have hcol : ∀ m : ℕ, ∑' n : ℕ, f (n, m) = aCoeff (2 * m) * z ^ (2 * m) := fun m => by
      dsimp only [f, aCoeff]
      simp only [even_two_mul, ↓reduceIte]
      rw [← tsum_mul_right]
      refine tsum_congr fun n => ?_; ring
    have htsum_eq : ∑' m : ℕ, aCoeff (2 * m) * z ^ (2 * m) = S_even 1 z := by
      simp_rw [← hcol]
      have hcomm := Summable.tsum_comm' (f := fun n m => f (n, m)) hf_summ
        (fun n => hf_summ.comp_injective (fun a b h => by simpa using h))
        (fun m => hf_summ.comp_injective (fun a b h => by simpa using h))
      rw [hcomm]
      simp_rw [hrow]; rfl
    have hhas : HasSum (fun m : ℕ => aCoeff (2 * m) * z ^ (2 * m)) (S_even 1 z) := by
      rw [← htsum_eq]
      have hbound_m : Summable (fun m : ℕ =>
          (1 / (4 * Real.pi ^ 2) ^ 2 * ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) *
            ((1 / 2 : ℝ) ^ 2) ^ m) :=
        (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
      refine Summable.hasSum ?_
      refine hbound_m.of_norm_bounded fun m => ?_
      rw [← hcol m]
      have hsn_m : Summable (fun n : ℕ => ‖f (n, m)‖) :=
        hf_norm.comp_injective (fun a b h => by simpa using h)
      have hdom_m : Summable (fun n : ℕ =>
          (1 / (4 * Real.pi ^ 2) ^ 2 * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4)) *
            ((1 / 2 : ℝ) ^ 2) ^ m) :=
        (summable_sigmaNat_div_pow_two.mul_left _).mul_right _
      calc ‖∑' n : ℕ, f (n, m)‖ ≤ ∑' n : ℕ, ‖f (n, m)‖ := norm_tsum_le_tsum_norm hsn_m
        _ ≤ ∑' n : ℕ, (1 / (4 * Real.pi ^ 2) ^ 2 * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4)) *
              ((1 / 2 : ℝ) ^ 2) ^ m := by
            refine hsn_m.tsum_le_tsum (fun n => ?_) hdom_m
            dsimp only [f]
            rw [norm_mul, norm_div, norm_div, Complex.norm_natCast, norm_pow, norm_pow, norm_pow,
              Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos n).le]
            have hA_ge : 4 * Real.pi ^ 2 ≤ A_freq n := by
              dsimp only [A_freq]
              have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
              nlinarith [Real.pi_pos]
            have hrat : ‖z‖ / A_freq n ≤ 1 / 2 :=
              (div_le_div_of_nonneg_left (norm_nonneg z) (by positivity) hA_ge).trans hq_lt.le
            have hpow_le : (‖z‖ / A_freq n) ^ (2 * m) ≤ ((1 / 2 : ℝ) ^ 2) ^ m := by
              rw [pow_mul]
              exact pow_le_pow_left₀ (by positivity)
                (pow_le_pow_left₀ (div_nonneg (norm_nonneg z) (A_freq_pos_eos n).le) hrat 2) m
            have hsplit : ‖z‖ ^ (2 * m) / A_freq n ^ (2 * m + 2) =
                (1 / A_freq n ^ 2) * (‖z‖ / A_freq n) ^ (2 * m) := by
              rw [pow_add, div_pow]; field_simp [(A_freq_pos_eos n).ne']
            have hA2 : 1 / A_freq n ^ 2 = (1 / (4 * Real.pi ^ 2) ^ 2) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
              dsimp only [A_freq]
              have hpi : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
              have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
              field_simp [hpi, hn0]
            rw [hsplit, hA2]
            calc ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) *
                  ((1 / (4 * Real.pi ^ 2) ^ 2) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) * (‖z‖ / A_freq n) ^ (2 * m))
                = (1 / (4 * Real.pi ^ 2) ^ 2 * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4)) *
                    (‖z‖ / A_freq n) ^ (2 * m) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ = _ := by rw [tsum_mul_right, tsum_mul_left]
    -- Push HasSum from even indices (2*m) to all s : ℕ (odd indices are 0)
    have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b h => by dsimp only at h; omega
    have hcomp := (hinj.hasSum_iff (f := fun s : ℕ => aCoeff s * z ^ s)
      (fun s hs => by
        have hodd : ¬ Even s := by
          intro ⟨m, hm⟩; exact hs ⟨m, by dsimp only; omega⟩
        simp [aCoeff, hodd])).mp hhas
    exact hcomp
  have hS_fps : HasFPowerSeriesOnBall (S_even 1) (.ofScalars ℂ aCoeff) 0 (ENNReal.ofReal R) := by
    refine ⟨?_, by simp [hR], fun {y} hy => ?_⟩
    · rw [ENNReal.ofReal_eq_coe_nnreal hR.le]
      refine FormalMultilinearSeries.le_radius_of_bound (.ofScalars ℂ aCoeff)
        (1 / (4 * Real.pi ^ 2) ^ 2 *
          ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4)
        (r := ⟨R, hR.le⟩) fun s => ?_
      rw [FormalMultilinearSeries.ofScalars_norm]
      by_cases hs : Even s
      · rcases hs with ⟨m, rfl⟩
        have hsn_m : Summable (fun n : ℕ =>
            ‖((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) / (A_freq n : ℂ) ^ (m + m + 2)‖) := by
          refine (summable_sigmaNat_div_pow_two.mul_left (1 / (4 * Real.pi ^ 2) ^ (m + m + 2))).of_norm_bounded fun n => ?_
          rw [Real.norm_of_nonneg (norm_nonneg _), norm_div, norm_div, Complex.norm_natCast, norm_pow,
            norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos n).le]
          dsimp only [A_freq]
          rw [mul_pow]
          have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          have hpow_ge : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ (m + m + 2) :=
            pow_le_pow_right₀ hn1 (by omega)
          have hpi : (4 * Real.pi ^ 2 : ℝ) ^ (m + m + 2) > 0 := by positivity
          have hn2 : ((n + 1 : ℕ) : ℝ) ^ 2 > 0 := by positivity
          calc (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 /
                ((4 * Real.pi ^ 2) ^ (m + m + 2) * ((n + 1 : ℕ) : ℝ) ^ (m + m + 2))
              ≤ (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 /
                ((4 * Real.pi ^ 2) ^ (m + m + 2) * ((n + 1 : ℕ) : ℝ) ^ 2) := by gcongr
            _ = 1 / (4 * Real.pi ^ 2) ^ (m + m + 2) * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := by
                field_simp [hpi.ne', hn2.ne']
        have hdom_m := summable_sigmaNat_div_pow_two.mul_left (1 / (4 * Real.pi ^ 2) ^ (m + m + 2))
        have ha_le : ‖aCoeff (m + m)‖ ≤
            1 / (4 * Real.pi ^ 2) ^ (m + m + 2) * ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 := by
          dsimp only [aCoeff]; simp only [show Even (m + m) from ⟨m, rfl⟩, ↓reduceIte]
          calc ‖∑' n : ℕ, _‖ ≤ ∑' n : ℕ, ‖_‖ := norm_tsum_le_tsum_norm hsn_m
            _ ≤ ∑' n : ℕ, 1 / (4 * Real.pi ^ 2) ^ (m + m + 2) * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := by
                refine hsn_m.tsum_le_tsum (fun n => ?_) hdom_m
                rw [norm_div, norm_div, Complex.norm_natCast, norm_pow, norm_pow, Complex.norm_natCast,
                  Complex.norm_real, Real.norm_of_nonneg (A_freq_pos_eos n).le]
                dsimp only [A_freq]; rw [mul_pow]
                have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
                have hpow_ge : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ (m + m + 2) :=
                  pow_le_pow_right₀ hn1 (by omega)
                have hpi : (4 * Real.pi ^ 2 : ℝ) ^ (m + m + 2) > 0 := by positivity
                have hn2 : ((n + 1 : ℕ) : ℝ) ^ 2 > 0 := by positivity
                calc (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 /
                      ((4 * Real.pi ^ 2) ^ (m + m + 2) * ((n + 1 : ℕ) : ℝ) ^ (m + m + 2))
                    ≤ (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 /
                      ((4 * Real.pi ^ 2) ^ (m + m + 2) * ((n + 1 : ℕ) : ℝ) ^ 2) := by gcongr
                  _ = 1 / (4 * Real.pi ^ 2) ^ (m + m + 2) * ((sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := by
                      field_simp [hpi.ne', hn2.ne']
            _ = _ := tsum_mul_left
        have hR_le : R ^ (m + m) / (4 * Real.pi ^ 2) ^ (m + m + 2) ≤ 1 / (4 * Real.pi ^ 2) ^ 2 := by
          dsimp only [R]
          have hpow : (2 * Real.pi ^ 2) ^ (m + m) ≤ (4 * Real.pi ^ 2) ^ (m + m) :=
            pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) (m + m)
          rw [pow_add (4 * Real.pi ^ 2) (m + m) 2]
          have h1 : (4 * Real.pi ^ 2) ^ (m + m) > 0 := by positivity
          have h2 : (4 * Real.pi ^ 2) ^ 2 > 0 := by positivity
          rw [div_le_div_iff₀ (by positivity) h2]; nlinarith
        calc ‖aCoeff (m + m)‖ * R ^ (m + m)
            ≤ (1 / (4 * Real.pi ^ 2) ^ (m + m + 2) * ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) *
                R ^ (m + m) := mul_le_mul_of_nonneg_right ha_le (by positivity)
          _ = (R ^ (m + m) / (4 * Real.pi ^ 2) ^ (m + m + 2)) *
                ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 := by ring
          _ ≤ (1 / (4 * Real.pi ^ 2) ^ 2) * ∑' n : ℕ, (sigmaNat 2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 :=
              mul_le_mul_of_nonneg_right hR_le (tsum_nonneg fun _ => by positivity)
      · dsimp only [aCoeff]; simp only [hs, ↓reduceIte, norm_zero, zero_mul]
        exact mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity)
    · have hy_ball : y ∈ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm, ← ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_lt_ofReal_iff hR] at hy
        exact hy
      have hs := hS_series y hy_ball
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hs
  have hS_deriv : ∀ s : ℕ, iteratedDeriv s (S_even 1) 0 = (s.factorial : ℂ) * aCoeff s := fun s => by
    have h1 := hS_fps.factorial_smul (y := (1 : ℂ)) (n := s)
    rw [iteratedDeriv_eq_iteratedFDeriv]
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, nsmul_eq_mul] using h1.symm
  -- Compute iteratedDeriv r (K_even 1) 0 from K_even 1 z = (1/π²) * z^3 * S_even 1 z!
  have hK_deriv : ∀ r : ℕ, iteratedDeriv r (K_even 1) 0 =
      if r < 3 then 0
      else (1 / (Real.pi : ℂ) ^ 2) * (r.factorial : ℂ) * aCoeff (r - 3) := fun r => by
    have hprod_eq : K_even 1 = fun z : ℂ => (1 / (Real.pi : ℂ) ^ 2) * (z ^ 3 * S_even 1 z) := by
      funext z; dsimp only [K_even]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp [hpi]; ring
    rw [hprod_eq, iteratedDeriv_const_mul_field]
    have hpow_c : ContDiffAt ℂ r (fun z : ℂ => z ^ 3) 0 := (analyticAt_id.pow 3).contDiffAt.of_le le_top
    have hS_c : ContDiffAt ℂ r (S_even 1) 0 := (hS_an 0 (Metric.mem_ball_self hR)).contDiffAt.of_le le_top
    rw [iteratedDeriv_fun_mul hpow_c hS_c]
    have hid : ∀ i : ℕ, iteratedDeriv i (fun z : ℂ => z ^ 3) 0 = if i = 3 then (6 : ℂ) else 0 := fun i => by
      rw [iteratedDeriv_fun_pow_zero]
      split_ifs <;> simp [Nat.factorial]
    split_ifs with hlt
    · have hz : ∑ i ∈ Finset.range (r + 1), (r.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ 3) 0 *
          iteratedDeriv (r - i) (S_even 1) 0 = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi_lt : i < 3 := (Finset.mem_range.mp hi).trans_le (by omega)
        simp [hid i, hi_lt.ne]
      rw [hz, mul_zero]
    · have hle : 3 ≤ r := by omega
      rw [Finset.sum_eq_single 3]
      · rw [hid 3, hS_deriv (r - 3)]
        simp only [↓reduceIte]
        have hch := congrArg (fun k : ℕ => (k : ℂ)) (Nat.choose_mul_factorial_mul_factorial hle)
        push_cast at hch
        have hfac3 : ((3 : ℕ).factorial : ℂ) = 6 := by norm_num [Nat.factorial]
        rw [hfac3] at hch
        linear_combination (1 / (Real.pi : ℂ) ^ 2) * aCoeff (r - 3) * hch
      · intro i _ hine; simp [hid i, hine]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  ext n
  cases n with
  | zero =>
    simp [formalSeries, PowerSeries.coeff_mul]
  | succ r =>
    have hL : PowerSeries.coeff (r + 1) (formalSeries (K_even 1)) = iteratedDeriv r (K_even 1) 0 := by
      simp [formalSeries]
    rw [hL, PowerSeries.coeff_succ_X_mul, map_add, emSeries, PowerSeries.coeff_mk,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X, hK_deriv r]
    by_cases hr0 : r = 0
    · subst hr0; simp [emTerm, iteratedDeriv_hFun_one_zero]
    · by_cases hr1 : r = 1
      · subst hr1
        simp only [show (1 : ℕ) < 3 by omega, ↓reduceIte, emTerm, iteratedDeriv_hFun_one_zero,
          one_ne_zero, Nat.sub_self, bernoulli_zero, Rat.cast_one, mul_one]
        have hb2 : (bernoulli 2 : ℂ) = 1 / 6 := by rw [bernoulli_two]; norm_num
        rw [hb2]; norm_num
      · by_cases heven_r : Even r
        · obtain ⟨q, rfl⟩ := heven_r
          have hodd_rp1 : Odd (q + q + 1) := ⟨q, by omega⟩
          have hbern0 : bernoulli (q + q + 1) = 0 := bernoulli_eq_zero_of_odd hodd_rp1 (by omega)
          have hne1 : q + q ≠ 1 := by omega
          simp only [hne1, ↓reduceIte, mul_zero, add_zero, emTerm, hbern0, Rat.cast_zero, zero_div, zero_mul]
          split_ifs with hlt
          · rfl
          · have hodd_sub : ¬ Even (q + q - 3) := by
              intro ⟨t, ht⟩; omega
            simp [aCoeff, hodd_sub]
        · obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp heven_r
          have hk1 : 1 ≤ k := by omega
          have hnot_lt : ¬ (2 * k + 1 < 3) := by omega
          have hne1 : 2 * k + 1 ≠ 1 := by omega
          have hne0 : 2 * k + 1 ≠ 0 := by omega
          simp only [hnot_lt, hne1, ↓reduceIte, mul_zero, add_zero, emTerm, iteratedDeriv_hFun_one_zero,
            hne0]
          have hsub3 : 2 * k + 1 - 3 = 2 * (k - 1) := by omega
          rw [hsub3]
          dsimp only [aCoeff]
          simp only [even_two_mul, ↓reduceIte]
          have hsum_eq : (∑' n : ℕ, ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) /
                (A_freq n : ℂ) ^ (2 * (k - 1) + 2)) =
              (1 / (4 * (Real.pi : ℂ) ^ 2) ^ (2 * k)) *
                ∑' n : ℕ, ((sigmaNat 2 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 + 2 * k)) := by
            rw [← tsum_mul_left]
            refine tsum_congr fun n => ?_
            have hAn : (A_freq n : ℂ) = (4 * (Real.pi : ℂ) ^ 2) * ((n + 1 : ℕ) : ℂ) := by
              dsimp only [A_freq]; push_cast; ring
            have h2k : 2 * (k - 1) + 2 = 2 * k := by omega
            rw [h2k, hAn, mul_pow, pow_add ((n + 1 : ℕ) : ℂ) 2 (2 * k)]
            have hpi : (4 * (Real.pi : ℂ) ^ 2) ^ (2 * k) ≠ 0 :=
              pow_ne_zero _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
            have hn2 : ((n + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
            have hnk : ((n + 1 : ℕ) : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
            field_simp [hpi, hn2, hnk]
          rw [hsum_eq, tsum_sigmaNat_two_div_pow k hk1]
          have hzp := riemannZeta_two_mul_nat (by omega : k ≠ 0)
          have hzk1 := riemannZeta_two_mul_nat (by omega : k + 1 ≠ 0)
          have hk_cast : ((2 * k : ℕ) : ℂ) = 2 * (k : ℂ) := by push_cast; ring
          have hk1_cast : ((2 + 2 * k : ℕ) : ℂ) = 2 * ((k + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [hk_cast, hzp, hk1_cast, hzk1]
          have hsub1 : 2 * k + 1 - 1 = 2 * k := by omega
          have hadd1 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
          rw [hsub1, hadd1]
          have hneg : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
            rw [pow_succ, pow_mul]; norm_num
          have hsign : (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ (k + 1 + 1) = -1 := by
            rw [← pow_add, show k + 1 + (k + 1 + 1) = 2 * (k + 1) + 1 by omega, pow_succ, pow_mul]
            norm_num
          have hpow2 : (2 : ℂ) ^ (2 * k - 1) * (2 : ℂ) ^ (2 * (k + 1) - 1) = (4 : ℂ) ^ (2 * k) := by
            rw [← pow_add, show (2 * k - 1) + (2 * (k + 1) - 1) = 2 * (2 * k) by omega, pow_mul]
            norm_num
          have hpowpi : (Real.pi : ℂ) ^ (2 * k) * (Real.pi : ℂ) ^ (2 * (k + 1)) =
              (Real.pi : ℂ) ^ 2 * ((Real.pi : ℂ) ^ 2) ^ (2 * k) := by
            rw [← pow_add, ← pow_mul, ← pow_add]; congr 1; omega
          have hfac1 : ((2 * k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have hfac2 : ((2 * (k + 1)).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
          have h4k : (4 * (Real.pi : ℂ) ^ 2) ^ (2 * k) ≠ 0 :=
            pow_ne_zero _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi0))
          have hfac_rel : ((2 * k + 1).factorial : ℂ) = ((2 * k + 1 : ℕ) : ℂ) * ((2 * k).factorial : ℂ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          rw [hneg, hfac_rel]
          field_simp [hfac1, hfac2, hpi0, h4k]
          rw [mul_pow ((Real.pi : ℂ) ^ 2) (4 : ℂ) (2 * k)]
          calc (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) *
                (bernoulli (2 * k) : ℂ) * (-1 : ℂ) ^ (k + 1 + 1) * (2 : ℂ) ^ (2 * (k + 1) - 1) *
                (Real.pi : ℂ) ^ (2 * (k + 1)) * (bernoulli (2 * (k + 1)) : ℂ)
              = (((-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ (k + 1 + 1)) *
                ((2 : ℂ) ^ (2 * k - 1) * (2 : ℂ) ^ (2 * (k + 1) - 1)) *
                ((Real.pi : ℂ) ^ (2 * k) * (Real.pi : ℂ) ^ (2 * (k + 1)))) *
                (bernoulli (2 * k) : ℂ) * (bernoulli (2 * (k + 1)) : ℂ) := by ring
            _ = (-1 : ℂ) * (4 : ℂ) ^ (2 * k) * ((Real.pi : ℂ) ^ 2 * ((Real.pi : ℂ) ^ 2) ^ (2 * k)) *
                (bernoulli (2 * k) : ℂ) * (bernoulli (2 * (k + 1)) : ℂ) := by
                rw [hsign, hpow2, hpowpi]
            _ = _ := by ring

/-! Direct Leibniz-rule proof of `f_even_one_hasAsympExp` and `f_S2_hasAsympExp` (zero integral boilerplate!). -/

private lemma hasAsympExp_inv_pow_eos (k : ℕ) :
    HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹ ^ k) (PowerSeries.X ^ k) := by
  intro M
  by_cases h : k < M
  · refine ⟨0, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [Finset.sum_eq_single k]
    · simp [PowerSeries.coeff_X_pow]
    · intro j _ hjk; simp [PowerSeries.coeff_X_pow, hjk]
    · intro hnot; exact absurd (Finset.mem_range.mpr h) hnot
  · refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hz : ∑ j ∈ Finset.range M, PowerSeries.coeff j (PowerSeries.X ^ k : PowerSeries ℂ) * (u : ℂ)⁻¹ ^ j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_ne : j ≠ k := by have := Finset.mem_range.mp hj; omega
      simp [PowerSeries.coeff_X_pow, hj_ne]
    rw [hz, sub_zero, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      inv_pow, one_div]
    exact inv_anti₀ (pow_pos (by linarith) M) (pow_le_pow_right₀ hu (by omega))

private lemma d_u_add (A B : PowerSeries ℂ) : d_u (A + B) = d_u A + d_u B := by
  simp only [d_u, map_add]; ring

private lemma d_u_mul (A B : PowerSeries ℂ) : d_u (A * B) = d_u A * B + A * d_u B := by
  have hleib : PowerSeries.derivative (A * B) = PowerSeries.derivative A * B + A * PowerSeries.derivative B := by
    rw [(PowerSeries.derivative (R := ℂ)).leibniz A B]; simp [smul_eq_mul]; ring
  simp only [d_u, hleib]; ring

private lemma d_u_C_mul (c : ℂ) (A : PowerSeries ℂ) : d_u (PowerSeries.C c * A) = PowerSeries.C c * d_u A := by
  have hC : PowerSeries.derivative (PowerSeries.C c) = 0 := by ext n; simp
  rw [d_u_mul]; simp [d_u, hC]

private lemma d_u_iterate_add (j : ℕ) (A B : PowerSeries ℂ) :
    d_u^[j] (A + B) = d_u^[j] A + d_u^[j] B := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, d_u_add]

private lemma d_u_iterate_C_mul (j : ℕ) (c : ℂ) (A : PowerSeries ℂ) :
    d_u^[j] (PowerSeries.C c * A) = PowerSeries.C c * d_u^[j] A := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, d_u_C_mul]

private lemma d_u_iterate_mul (j : ℕ) (A B : PowerSeries ℂ) :
    d_u^[j] (A * B) = ∑ i ∈ Finset.range (j + 1),
      PowerSeries.C (j.choose i : ℂ) * (d_u^[i] A * d_u^[j - i] B) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    have hsum : d_u (∑ i ∈ Finset.range (j + 1), PowerSeries.C (j.choose i : ℂ) * (d_u^[i] A * d_u^[j - i] B)) =
        ∑ i ∈ Finset.range (j + 1), PowerSeries.C (j.choose i : ℂ) *
          (d_u^[i + 1] A * d_u^[j - i] B + d_u^[i] A * d_u^[j - i + 1] B) := by
      have hlin : ∀ s : Finset ℕ, ∀ f : ℕ → PowerSeries ℂ, d_u (∑ i ∈ s, f i) = ∑ i ∈ s, d_u (f i) := by
        intro s f
        classical
        induction s using Finset.induction_on with
        | empty => simp [d_u]
        | @insert a s ha ihs => rw [Finset.sum_insert ha, d_u_add, ihs, Finset.sum_insert ha]
      rw [hlin]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [d_u_C_mul, d_u_mul, Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [hsum]
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun i => PowerSeries.C ((j + 1).choose i : ℂ) * (d_u^[i] A * d_u^[j + 1 - i] B)) (j + 1)]
    simp only [Nat.add_sub_add_right]
    rw [Finset.sum_range_succ (fun i => PowerSeries.C ((j + 1).choose (i + 1) : ℂ) * (d_u^[i + 1] A * d_u^[j - i] B)) j]
    rw [Finset.sum_range_succ (fun i => PowerSeries.C (j.choose i : ℂ) * (d_u^[i + 1] A * d_u^[j - i] B)) j]
    rw [Finset.sum_range_succ' (fun i => PowerSeries.C (j.choose i : ℂ) * (d_u^[i] A * d_u^[j - i + 1] B)) j]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.sub_self, Nat.sub_zero,
      Nat.cast_one, map_one, one_mul]
    have hmid : ∑ k ∈ Finset.range j, PowerSeries.C ((j + 1).choose (k + 1) : ℂ) * (d_u^[k + 1] A * d_u^[j - k] B) =
        ∑ k ∈ Finset.range j, PowerSeries.C (j.choose k : ℂ) * (d_u^[k + 1] A * d_u^[j - k] B) +
        ∑ k ∈ Finset.range j, PowerSeries.C (j.choose (k + 1) : ℂ) * (d_u^[k + 1] A * d_u^[j - (k + 1) + 1] B) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : k < j := Finset.mem_range.mp hk
      have hsub : j - (k + 1) + 1 = j - k := by omega
      rw [hsub, Nat.choose_succ_succ, Nat.cast_add, map_add]
      ring
    rw [hmid]; ring

private lemma d_u_iterate_X (i : ℕ) :
    d_u^[i] (PowerSeries.X : PowerSeries ℂ) = PowerSeries.C ((-1 : ℂ) ^ i * (i.factorial : ℂ)) * PowerSeries.X ^ (i + 1) := by
  have hdX : PowerSeries.derivative (PowerSeries.X : PowerSeries ℂ) = 1 := by ext n; simp [PowerSeries.coeff_one]
  have hd_pow : ∀ k : ℕ, d_u (PowerSeries.X ^ (k + 1) : PowerSeries ℂ) =
      PowerSeries.C (-((k + 1 : ℕ) : ℂ)) * PowerSeries.X ^ (k + 2) := fun k => by
    induction k with
    | zero => simp [d_u, hdX]
    | succ m ihm =>
      rw [pow_succ, d_u_mul, ihm]
      have h1 : d_u (PowerSeries.X : PowerSeries ℂ) = PowerSeries.C (-1 : ℂ) * PowerSeries.X ^ 2 := by
        simp [d_u, hdX]
      rw [h1]
      have hcast : PowerSeries.C (-((m + 1 + 1 : ℕ) : ℂ)) =
          PowerSeries.C (-((m + 1 : ℕ) : ℂ)) + PowerSeries.C (-1 : ℂ) := by
        rw [← map_add]; congr 1; push_cast; ring
      rw [hcast]; ring
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, d_u_C_mul, hd_pow i, ← mul_assoc, ← map_mul]
    congr 2
    rw [pow_succ, Nat.factorial_succ]; push_cast; ring

private lemma d_u_iterate_X_sq (i : ℕ) :
    d_u^[i] (PowerSeries.X ^ 2 : PowerSeries ℂ) =
      PowerSeries.C ((-1 : ℂ) ^ i * ((i + 1).factorial : ℂ)) * PowerSeries.X ^ (i + 2) := by
  have hdX : PowerSeries.derivative (PowerSeries.X : PowerSeries ℂ) = 1 := by ext n; simp [PowerSeries.coeff_one]
  have hd_pow : ∀ k : ℕ, d_u (PowerSeries.X ^ (k + 1) : PowerSeries ℂ) =
      PowerSeries.C (-((k + 1 : ℕ) : ℂ)) * PowerSeries.X ^ (k + 2) := fun k => by
    induction k with
    | zero => simp [d_u, hdX]
    | succ m ihm =>
      rw [pow_succ, d_u_mul, ihm]
      have h1 : d_u (PowerSeries.X : PowerSeries ℂ) = PowerSeries.C (-1 : ℂ) * PowerSeries.X ^ 2 := by
        simp [d_u, hdX]
      rw [h1]
      have hcast : PowerSeries.C (-((m + 1 + 1 : ℕ) : ℂ)) =
          PowerSeries.C (-((m + 1 : ℕ) : ℂ)) + PowerSeries.C (-1 : ℂ) := by
        rw [← map_add]; congr 1; push_cast; ring
      rw [hcast]; ring
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, d_u_C_mul, hd_pow (i + 1), ← mul_assoc, ← map_mul]
    congr 2
    rw [show i + 1 + 1 = i + 2 by omega, pow_succ, Nat.factorial_succ (i + 1)]
    push_cast; ring

private lemma iteratedDeriv_inv_pow_real_eos (a i : ℕ) (ha : a = 1 ∨ a = 2) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv i (fun v : ℝ => (v : ℂ)⁻¹ ^ a) u =
      if a = 1 then (-1 : ℂ) ^ i * (i.factorial : ℂ) * (u : ℂ)⁻¹ ^ (i + 1)
      else (-1 : ℂ) ^ i * ((i + 1).factorial : ℂ) * (u : ℂ)⁻¹ ^ (i + 2) := by
  have h1 : ∀ k : ℕ, ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun v : ℝ => (v : ℂ)⁻¹) x = (-1 : ℂ) ^ k * (k.factorial : ℂ) * (x : ℂ)⁻¹ ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (fun v : ℝ => (v : ℂ)⁻¹) =ᶠ[𝓝 x]
          fun y : ℝ => (-1 : ℂ) ^ k * (k.factorial : ℂ) * (y : ℂ)⁻¹ ^ (k + 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy; exact ih y hy
      rw [hev.deriv_eq]
      have hne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
      have hinv : HasDerivAt (fun y : ℝ => (y : ℂ)⁻¹) (-((x : ℂ)⁻¹ ^ 2)) x := by
        have h := Complex.ofRealCLM.hasDerivAt (x := x) |>.inv hne
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => rfl) |>.congr_deriv ?_
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; field_simp [hne]
      have hpow : HasDerivAt (fun y : ℝ => (-1 : ℂ) ^ k * (k.factorial : ℂ) * (y : ℂ)⁻¹ ^ (k + 1))
          ((-1 : ℂ) ^ k * (k.factorial : ℂ) * (((k + 1 : ℕ) : ℂ) * (x : ℂ)⁻¹ ^ (k + 1 - 1) * -((x : ℂ)⁻¹ ^ 2))) x :=
        (hinv.pow (k + 1)).const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
      rw [hpow.deriv, pow_succ (-1 : ℂ) k, Nat.factorial_succ]
      push_cast; ring
  rcases ha with rfl | rfl
  · simp only [↓reduceIte, pow_one]; exact h1 i u hu
  · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    have h2 : (fun v : ℝ => (v : ℂ)⁻¹ ^ 2) =ᶠ[𝓝 u] fun v : ℝ => -deriv (fun y : ℝ => (y : ℂ)⁻¹) v := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
      have := h1 1 v hv; rw [iteratedDeriv_one] at this; rw [this]; ring
    rw [h2.iteratedDeriv_eq i, iteratedDeriv_fun_neg, ← iteratedDeriv_succ', h1 (i + 1) u hu]
    rw [pow_succ (-1 : ℂ) i]; ring

private lemma f_even_one_hasAsympExp (j : ℕ) :
    HasAsympExp (iteratedDeriv j (f_even 1)) (d_u^[j] (formalSeries (K_even 1))) := by
  rw [formalSeries_K_even_one, mul_add, d_u_iterate_add]
  let c2 : ℂ := ∫ y in Ioi (0 : ℝ), hFun 1 y
  let g : ℝ → ℂ := fun u => sumScale (hFun 1) u - (u : ℂ) * c2
  have hg_asymp : ∀ k : ℕ, HasAsympExp (iteratedDeriv k g) (d_u^[k] (emSeries (hFun 1))) :=
    fun k => sumScale_iteratedDeriv_hasAsympExp hFun_one_expDecaySmooth k
  have hf_eq : f_even 1 = fun u : ℝ => (u : ℂ)⁻¹ * g u + (1 / 12 : ℂ) * (u : ℂ)⁻¹ ^ 2 := by
    funext u; dsimp only [f_even, g, c2]
    have hb2 : (bernoulli 2 : ℂ) = 1 / 6 := by rw [bernoulli_two]; norm_num
    rw [hb2]; norm_num
  -- Real-analyticity of g on (0, ∞) via value_sigmaSeries_exp_neg + scaledRay_analytic!
  have hg_an : AnalyticOnNhd ℝ g (Set.Ioi 0) := by
    have hg_eq : ∀ u : ℝ, 0 < u →
        g u = (u : ℂ)⁻¹ ^ 2 * value (sigmaSeries 2) (qRay (Real.log u)) - (u : ℂ) * c2 := by
      intro u hu
      have hq_eq : qRay (Real.log u) = Complex.exp (-((u⁻¹ : ℝ) : ℂ)) := by
        unfold qRay; rw [Real.exp_neg (Real.log u), Real.exp_log hu, Complex.ofReal_exp]; push_cast; rfl
      have hval := value_sigmaSeries_exp_neg 2 (inv_pos.mpr hu)
      have hterm : ∀ d : ℕ,
          (((d + 1 : ℕ) : ℂ) ^ 2 / (Complex.exp (((d + 1 : ℕ) : ℂ) * ((u⁻¹ : ℝ) : ℂ)) - 1)) =
            (u : ℂ) ^ 2 * hFun 1 ((d + 1 : ℝ) / u) := fun d => by
        have hdu : (d + 1 : ℝ) / u ≠ 0 := div_ne_zero (by positivity) hu.ne'
        have hduc : (((d + 1 : ℝ) / u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdu
        have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
        have hexp_nz : expAux (((d + 1 : ℝ) / u : ℝ) : ℂ) ≠ 0 :=
          expAux_ne_zero_of_abs_im_lt (by simp; positivity)
        have hmul := expAux_mul_sub_eos (((d + 1 : ℝ) / u : ℝ) : ℂ)
        dsimp only [hFun, qFun, qComplex]
        have hq_eq' : (expAux (((d + 1 : ℝ) / u : ℝ) : ℂ))⁻¹ =
            (((d + 1 : ℝ) / u : ℝ) : ℂ) / (Complex.exp (((d + 1 : ℝ) / u : ℝ) : ℂ) - 1) := by
          rw [← hmul]; field_simp [hduc, hexp_nz]
        rw [hq_eq']
        push_cast
        have harg : ((d : ℂ) + 1) * (u : ℂ)⁻¹ = ((d : ℂ) + 1) / (u : ℂ) := by ring
        rw [harg]; field_simp [huc]
      have hsum : value (sigmaSeries 2) (qRay (Real.log u)) = (u : ℂ) ^ 2 * sumScale (hFun 1) u := by
        rw [hq_eq, hval]; simp_rw [hterm]; exact tsum_mul_left
      dsimp only [g]
      rw [hsum]
      have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
      field_simp [huc]
    intro u hu
    have hlog : AnalyticAt ℝ Real.log u := _root_.analyticAt_log hu
    have hval_an : AnalyticAt ℝ (fun v : ℝ => value (sigmaSeries 2) (qRay (Real.log v))) u :=
      AnalyticAt.comp (g := fun y : ℝ => value (sigmaSeries 2) (qRay y)) (f := Real.log)
        (by simpa [analyticCoordinates, seriesJet] using
          ray_source_analytic (sigmaSeries_polyBound 2).to_diskCoeffBound 1 (Real.log u)) hlog
    have hinv_an : AnalyticAt ℝ (fun v : ℝ => (v : ℂ)⁻¹ ^ 2) u :=
      ((Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr (ne_of_gt hu))).pow 2
    have hrhs_an : AnalyticAt ℝ (fun v : ℝ => (v : ℂ)⁻¹ ^ 2 * value (sigmaSeries 2) (qRay (Real.log v)) - (v : ℂ) * c2) u :=
      (hinv_an.mul hval_an).sub ((Complex.ofRealCLM.analyticAt u).mul analyticAt_const)
    refine hrhs_an.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv; exact (hg_eq v hv).symm
  -- First part: HasAsympExp (iteratedDeriv j (u⁻¹ * g u)) (d_u^[j] (X * emSeries (hFun 1)))
  have hpart1 : HasAsympExp (iteratedDeriv j (fun u : ℝ => (u : ℂ)⁻¹ * g u))
      (d_u^[j] (PowerSeries.X * emSeries (hFun 1))) := by
    rw [d_u_iterate_mul]
    have hsum_asymp : HasAsympExp
        (fun u : ℝ => ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (u : ℂ)⁻¹ ^ (i + 1)) *
            iteratedDeriv (j - i) g u)
        (∑ i ∈ Finset.range (j + 1),
          PowerSeries.C (j.choose i : ℂ) * (d_u^[i] PowerSeries.X * d_u^[j - i] (emSeries (hFun 1)))) := by
      have hterm : ∀ i : ℕ, HasAsympExp
          (fun u : ℝ => (j.choose i : ℂ) * ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (u : ℂ)⁻¹ ^ (i + 1)) *
            iteratedDeriv (j - i) g u)
          (PowerSeries.C (j.choose i : ℂ) * (d_u^[i] PowerSeries.X * d_u^[j - i] (emSeries (hFun 1)))) := fun i => by
        rw [d_u_iterate_X i]
        have h1 := ((HasAsympExp.const ((-1 : ℂ) ^ i * (i.factorial : ℂ))).mul
          (hasAsympExp_inv_pow_eos (i + 1))).mul (hg_asymp (j - i))
        have h2 := (HasAsympExp.const (j.choose i : ℂ)).mul h1
        simpa [mul_assoc] using h2
      induction (Finset.range (j + 1)) using Finset.induction_on with
      | empty => simpa using HasAsympExp.const 0
      | @insert a s ha ihs =>
        have hfn : (fun u : ℝ => ∑ i ∈ insert a s,
            (j.choose i : ℂ) * ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (u : ℂ)⁻¹ ^ (i + 1)) *
              iteratedDeriv (j - i) g u) =
            fun u : ℝ => (j.choose a : ℂ) * ((-1 : ℂ) ^ a * (a.factorial : ℂ) * (u : ℂ)⁻¹ ^ (a + 1)) *
              iteratedDeriv (j - a) g u +
              ∑ i ∈ s, (j.choose i : ℂ) * ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (u : ℂ)⁻¹ ^ (i + 1)) *
                iteratedDeriv (j - i) g u := by
          funext u; exact Finset.sum_insert ha
        rw [hfn, Finset.sum_insert ha]
        exact (hterm a).add ihs
    intro M
    obtain ⟨C, hC⟩ := hsum_asymp M
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
    have hinv_cd : ContDiffAt ℝ j (fun v : ℝ => (v : ℂ)⁻¹) u :=
      ((Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr hu_pos.ne')).contDiffAt.of_le le_top
    have hg_cd : ContDiffAt ℝ j g u := (hg_an u hu_pos).contDiffAt.of_le le_top
    have heq : iteratedDeriv j (fun v : ℝ => (v : ℂ)⁻¹ * g v) u =
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * ((-1 : ℂ) ^ i * (i.factorial : ℂ) * (u : ℂ)⁻¹ ^ (i + 1)) *
            iteratedDeriv (j - i) g u := by
      rw [iteratedDeriv_fun_mul hinv_cd hg_cd]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := iteratedDeriv_inv_pow_real_eos 1 i (Or.inl rfl) hu_pos
      simp only [pow_one, ↓reduceIte] at h1
      rw [h1]
    rw [heq]; exact hu_bd
  -- Second part: HasAsympExp (iteratedDeriv j ((1/12) * u⁻¹^2)) (d_u^[j] (X * (C (1/12) * X)))
  have hpart2 : HasAsympExp (iteratedDeriv j (fun u : ℝ => (1 / 12 : ℂ) * (u : ℂ)⁻¹ ^ 2))
      (d_u^[j] (PowerSeries.X * (PowerSeries.C (1 / 12 : ℂ) * PowerSeries.X))) := by
    have hrew : PowerSeries.X * (PowerSeries.C (1 / 12 : ℂ) * PowerSeries.X) =
        PowerSeries.C (1 / 12 : ℂ) * PowerSeries.X ^ 2 := by ring
    rw [hrew, d_u_iterate_C_mul, d_u_iterate_X_sq]
    have hbase := (HasAsympExp.const ((1 / 12 : ℂ) * ((-1 : ℂ) ^ j * ((j + 1).factorial : ℂ)))).mul
      (hasAsympExp_inv_pow_eos (j + 2))
    intro M
    obtain ⟨C, hC⟩ := hbase M
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_inv_pow_real_eos 2 j (Or.inr rfl) hu_pos]
    simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    simpa [map_mul, mul_assoc] using hu_bd
  -- Combine via add!
  have hadd := hpart1.add hpart2
  intro M
  obtain ⟨C, hC⟩ := hadd M
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
  have h1_cd : ContDiffAt ℝ j (fun v : ℝ => (v : ℂ)⁻¹ * g v) u :=
    (((Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr hu_pos.ne')).mul
      (hg_an u hu_pos)).contDiffAt.of_le le_top
  have h2_cd : ContDiffAt ℝ j (fun v : ℝ => (1 / 12 : ℂ) * (v : ℂ)⁻¹ ^ 2) u :=
    (analyticAt_const.mul (((Complex.ofRealCLM.analyticAt u).inv
      (Complex.ofReal_ne_zero.mpr hu_pos.ne')).pow 2)).contDiffAt.of_le le_top
  have heq : iteratedDeriv j (f_even 1) u =
      iteratedDeriv j (fun v : ℝ => (v : ℂ)⁻¹ * g v) u +
      iteratedDeriv j (fun v : ℝ => (1 / 12 : ℂ) * (v : ℂ)⁻¹ ^ 2) u := by
    rw [hf_eq]; exact iteratedDeriv_fun_add h1_cd h2_cd
  rw [heq]; exact hu_bd

/-- Formal scaling operator sending `∑_{n ≥ 1} a_n w^n` to `∑_{n ≥ 1} 2^{n-1} a_n w^n`
(corresponding to `K(ξ) ↦ K(2 ξ)` and `(1/2) f(u/2)`). -/
private def scale2Series (S : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (2 : ℂ) ^ (n - 1) * PowerSeries.coeff n S

private lemma d_u_scale2Series (S : PowerSeries ℂ) :
    d_u (scale2Series S) = PowerSeries.C (1 / 2 : ℂ) * scale2Series (d_u S) := by
  ext n
  cases n with
  | zero => simp [d_u, scale2Series]
  | succ m =>
    cases m with
    | zero =>
      simp [d_u, scale2Series, sq, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
    | succ k =>
      simp only [d_u, scale2Series, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_neg,
        sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [pow_succ]; ring

private lemma d_u_iterate_scale2Series (j : ℕ) (S : PowerSeries ℂ) :
    d_u^[j] (scale2Series S) = PowerSeries.C ((1 / 2 : ℂ) ^ j) * scale2Series (d_u^[j] S) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, d_u_C_mul,
      d_u_scale2Series, ← mul_assoc, ← map_mul, pow_succ]

private lemma iteratedDeriv_comp_const_mul_analytic {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : 𝕜 → F} {c x : 𝕜} (hf : AnalyticAt 𝕜 f (c * x)) (n : ℕ) :
    iteratedDeriv n (fun y => f (c * y)) x = (c ^ n) • iteratedDeriv n f (c * x) := by
  obtain ⟨r, hr, hball⟩ := hf.exists_ball_analyticOnNhd
  have hev : ∀ k : ℕ, ∀ᶠ y in 𝓝 x,
      iteratedDeriv k (fun z => f (c * z)) y = (c ^ k) • iteratedDeriv k f (c * y) := by
    intro k
    induction k with
    | zero => exact Eventually.of_forall fun y => by simp
    | succ k ih =>
      have hmem : ∀ᶠ y in 𝓝 x, c * y ∈ Metric.ball (c * x) r :=
        (continuousAt_const.mul continuousAt_id).eventually
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
      filter_upwards [ih.eventually_nhds, hmem] with y hy_ev hy_ball
      have hy_ev' : (fun z => iteratedDeriv k (fun w => f (c * w)) z) =ᶠ[𝓝 y]
          (fun z => (c ^ k) • iteratedDeriv k f (c * z)) := hy_ev
      rw [iteratedDeriv_succ, hy_ev'.deriv_eq, iteratedDeriv_succ]
      have hdiff : DifferentiableAt 𝕜 (iteratedDeriv k f) (c * y) := by
        rw [iteratedDeriv_eq_iterate]
        exact ((hball.iterated_deriv k) (c * y) hy_ball).differentiableAt
      have hmul : HasDerivAt (fun z : 𝕜 => c * z) c y := by
        simpa using (hasDerivAt_id y).const_mul c
      have hcomp : HasDerivAt (fun z : 𝕜 => (c ^ k) • iteratedDeriv k f (c * z))
          ((c ^ k) • (c • deriv (iteratedDeriv k f) (c * y))) y :=
        (hdiff.hasDerivAt.scomp y hmul).const_smul (c ^ k)
      rw [hcomp.deriv, ← mul_smul, ← pow_succ]
  exact (hev n).self_of_nhds

private lemma formalSeries_K_S2_eq :
    formalSeries K_S2 = formalSeries (K_even 1) - scale2Series (formalSeries (K_even 1)) := by
  have hK_an : AnalyticAt ℂ (K_even 1) 0 :=
    K_even_one_analyticAt (Or.inl (Metric.mem_ball_self (by positivity))) (fun n h0 => by
      have := congrArg Complex.re h0; simp at this; linarith [A_freq_pos_eos n])
  ext n
  cases n with
  | zero => simp [formalSeries, scale2Series]
  | succ r =>
    simp only [formalSeries, scale2Series, PowerSeries.coeff_mk, map_sub, Nat.succ_ne_zero,
      ↓reduceIte, Nat.add_sub_cancel]
    have h2 : iteratedDeriv r (fun ξ : ℂ => K_even 1 (2 * ξ)) 0 =
        (2 : ℂ) ^ r * iteratedDeriv r (K_even 1) 0 := by
      have := iteratedDeriv_comp_const_mul_analytic (f := K_even 1) (c := (2 : ℂ)) (x := (0 : ℂ))
        (by simpa using hK_an) r
      simpa [smul_eq_mul] using this
    have hsub : iteratedDeriv r K_S2 0 =
        iteratedDeriv r (K_even 1) 0 - iteratedDeriv r (fun ξ : ℂ => K_even 1 (2 * ξ)) 0 := by
      have hc1 : ContDiffAt ℂ r (K_even 1) 0 := hK_an.contDiffAt.of_le le_top
      have hc2 : ContDiffAt ℂ r (fun ξ : ℂ => K_even 1 (2 * ξ)) 0 :=
        (AnalyticAt.comp (g := K_even 1) (f := fun ξ : ℂ => 2 * ξ)
          (by simpa using hK_an) (analyticAt_const.mul analyticAt_id)).contDiffAt.of_le le_top
      exact iteratedDeriv_fun_sub hc1 hc2
    rw [hsub, h2]

private lemma f_S2_hasAsympExp (j : ℕ) :
    HasAsympExp (iteratedDeriv j f_S2) (d_u^[j] (formalSeries K_S2)) := by
  have hsub_du : d_u^[j] (formalSeries K_S2) =
      d_u^[j] (formalSeries (K_even 1)) - PowerSeries.C ((1 / 2 : ℂ) ^ j) *
        scale2Series (d_u^[j] (formalSeries (K_even 1))) := by
    rw [formalSeries_K_S2_eq, sub_eq_add_neg, d_u_iterate_add,
      show -(scale2Series (formalSeries (K_even 1))) = PowerSeries.C (-1 : ℂ) * scale2Series (formalSeries (K_even 1)) by simp,
      d_u_iterate_C_mul, d_u_iterate_scale2Series]
    simp [sub_eq_add_neg]
  rw [hsub_du]
  -- Real-analyticity of f_even 1 on (0, ∞)!
  have hf1_an : AnalyticOnNhd ℝ (f_even 1) (Set.Ioi 0) := by
    let c2 : ℂ := ∫ y in Ioi (0 : ℝ), hFun 1 y
    have hf1_eq : ∀ u : ℝ, 0 < u →
        f_even 1 u = (u : ℂ)⁻¹ ^ 3 * value (sigmaSeries 2) (qRay (Real.log u)) - c2 +
          (1 / 12 : ℂ) * (u : ℂ)⁻¹ ^ 2 := by
      intro u hu
      have hq_eq : qRay (Real.log u) = Complex.exp (-((u⁻¹ : ℝ) : ℂ)) := by
        unfold qRay; rw [Real.exp_neg (Real.log u), Real.exp_log hu, Complex.ofReal_exp]; push_cast; rfl
      have hval := value_sigmaSeries_exp_neg 2 (inv_pos.mpr hu)
      have hterm : ∀ d : ℕ,
          (((d + 1 : ℕ) : ℂ) ^ 2 / (Complex.exp (((d + 1 : ℕ) : ℂ) * ((u⁻¹ : ℝ) : ℂ)) - 1)) =
            (u : ℂ) ^ 2 * hFun 1 ((d + 1 : ℝ) / u) := fun d => by
        have hdu : (d + 1 : ℝ) / u ≠ 0 := div_ne_zero (by positivity) hu.ne'
        have hduc : (((d + 1 : ℝ) / u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdu
        have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
        have hexp_nz : expAux (((d + 1 : ℝ) / u : ℝ) : ℂ) ≠ 0 :=
          expAux_ne_zero_of_abs_im_lt (by simp; positivity)
        have hmul := expAux_mul_sub_eos (((d + 1 : ℝ) / u : ℝ) : ℂ)
        dsimp only [hFun, qFun, qComplex]
        have hq_eq' : (expAux (((d + 1 : ℝ) / u : ℝ) : ℂ))⁻¹ =
            (((d + 1 : ℝ) / u : ℝ) : ℂ) / (Complex.exp (((d + 1 : ℝ) / u : ℝ) : ℂ) - 1) := by
          rw [← hmul]; field_simp [hduc, hexp_nz]
        rw [hq_eq']; push_cast
        have harg : ((d : ℂ) + 1) * (u : ℂ)⁻¹ = ((d : ℂ) + 1) / (u : ℂ) := by ring
        rw [harg]; field_simp [huc]
      have hsum : value (sigmaSeries 2) (qRay (Real.log u)) = (u : ℂ) ^ 2 * sumScale (hFun 1) u := by
        rw [hq_eq, hval]; simp_rw [hterm]; exact tsum_mul_left
      dsimp only [f_even, c2]
      have hb2 : (bernoulli 2 : ℂ) = 1 / 6 := by rw [bernoulli_two]; norm_num
      have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
      rw [hsum, hb2, inv_pow, inv_pow]; field_simp [huc]; ring
    intro u hu
    have hlog := _root_.analyticAt_log hu
    have hval_an : AnalyticAt ℝ (fun v : ℝ => value (sigmaSeries 2) (qRay (Real.log v))) u :=
      AnalyticAt.comp (g := fun y : ℝ => value (sigmaSeries 2) (qRay y)) (f := Real.log)
        (by simpa [analyticCoordinates, seriesJet] using
          ray_source_analytic (sigmaSeries_polyBound 2).to_diskCoeffBound 1 (Real.log u)) hlog
    have hinv_an := (Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr (ne_of_gt hu))
    have hrhs_an : AnalyticAt ℝ
        (fun v : ℝ => (v : ℂ)⁻¹ ^ 3 * value (sigmaSeries 2) (qRay (Real.log v)) - c2 +
          (1 / 12 : ℂ) * (v : ℂ)⁻¹ ^ 2) u :=
      (((hinv_an.pow 3).mul hval_an).sub (analyticAt_const (v := c2))).add
        ((analyticAt_const (v := (1 / 12 : ℂ))).mul (hinv_an.pow 2))
    refine hrhs_an.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv; exact (hf1_eq v hv).symm
  have h1 := f_even_one_hasAsympExp j
  -- Prove HasAsympExp for (1/2) * f_even 1 (u / 2) and its j-th derivative!
  have h2 : HasAsympExp (iteratedDeriv j (fun u : ℝ => (1 / 2 : ℂ) * f_even 1 (u / 2)))
      (PowerSeries.C ((1 / 2 : ℂ) ^ j) * scale2Series (d_u^[j] (formalSeries (K_even 1)))) := by
    have hcoeff0 : PowerSeries.coeff 0 (d_u^[j] (formalSeries (K_even 1))) = 0 := by
      cases j with
      | zero => simp [formalSeries]
      | succ k => rw [Function.iterate_succ_apply']; simp [d_u]
    intro M
    obtain ⟨C, hC⟩ := h1 M
    refine ⟨|C| * 2 ^ (M + j + 1), ?_⟩
    have hC_half : ∀ᶠ u : ℝ in atTop,
        ‖iteratedDeriv j (f_even 1) (u / 2) -
          ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] (formalSeries (K_even 1))) * ((u / 2 : ℝ) : ℂ)⁻¹ ^ k‖ ≤
          C / (u / 2) ^ M :=
      (tendsto_id.atTop_div_const zero_lt_two).eventually hC
    filter_upwards [hC_half, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
    have hd_half : iteratedDeriv j (fun v : ℝ => (1 / 2 : ℂ) * f_even 1 (v / 2)) u =
        (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j (f_even 1) (u / 2) := by
      rw [iteratedDeriv_const_mul_field]
      have heq : (fun v : ℝ => f_even 1 (v / 2)) = fun v : ℝ => f_even 1 ((1 / 2 : ℝ) * v) := by
        funext v; ring_nf
      have han_u : AnalyticAt ℝ (f_even 1) ((1 / 2 : ℝ) * u) :=
        hf1_an ((1 / 2 : ℝ) * u) (show (0 : ℝ) < (1 / 2 : ℝ) * u by positivity)
      rw [heq, iteratedDeriv_comp_const_mul_analytic han_u j, Complex.real_smul,
        show (1 / 2 : ℝ) * u = u / 2 by ring, pow_succ', mul_assoc]
      push_cast; ring
    have hsum_eq : ∑ k ∈ Finset.range M,
          PowerSeries.coeff k (PowerSeries.C ((1 / 2 : ℂ) ^ j) *
            scale2Series (d_u^[j] (formalSeries (K_even 1)))) * (u : ℂ)⁻¹ ^ k =
        (1 / 2 : ℂ) ^ (j + 1) *
          ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] (formalSeries (K_even 1))) *
            ((u / 2 : ℝ) : ℂ)⁻¹ ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [PowerSeries.coeff_C_mul, scale2Series, PowerSeries.coeff_mk]
      cases k with
      | zero => simp [hcoeff0]
      | succ m =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have hu2 : ((u / 2 : ℝ) : ℂ)⁻¹ = 2 * (u : ℂ)⁻¹ := by
          push_cast; have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
          field_simp [huc]
        rw [hu2, mul_pow, pow_succ (2 : ℂ) m, pow_succ (1 / 2 : ℂ) j]
        ring
    rw [hd_half, hsum_eq, ← mul_sub, norm_mul, norm_pow,
      show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have hdiv_pos : (0 : ℝ) < (u / 2) ^ M := by positivity
    calc (1 / 2 : ℝ) ^ (j + 1) * ‖iteratedDeriv j (f_even 1) (u / 2) - _‖
        ≤ (1 / 2 : ℝ) ^ (j + 1) * (C / (u / 2) ^ M) :=
          mul_le_mul_of_nonneg_left hu_bd (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ (j + 1) * (|C| / (u / 2) ^ M) := by
          gcongr; exact le_abs_self C
      _ = (|C| * (2 : ℝ) ^ M / (2 : ℝ) ^ (j + 1)) / u ^ M := by
          rw [div_pow, div_pow, one_pow]; field_simp [hu_pos.ne']
      _ ≤ (|C| * 2 ^ (M + j + 1)) / u ^ M := by
          gcongr
          have h1 : (2 : ℝ) ^ M / (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ M :=
            div_le_self (by positivity) (one_le_pow₀ (by norm_num))
          have h2 : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (M + j + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C)
  -- Subtract h2 from h1 using real-analyticity of f_even 1 on (0, ∞)!
  have hsub_asymp : HasAsympExp
      (fun u => iteratedDeriv j (f_even 1) u - iteratedDeriv j (fun v => (1 / 2 : ℂ) * f_even 1 (v / 2)) u)
      (d_u^[j] (formalSeries (K_even 1)) -
        PowerSeries.C ((1 / 2 : ℂ) ^ j) * scale2Series (d_u^[j] (formalSeries (K_even 1)))) := by
    have hneg := (HasAsympExp.const (-1 : ℂ)).mul h2
    have hadd := h1.add hneg
    simpa [sub_eq_add_neg] using hadd
  intro M
  obtain ⟨C, hC⟩ := hsub_asymp M
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
  have hc1 : ContDiffAt ℝ j (f_even 1) u := (hf1_an u hu_pos).contDiffAt.of_le le_top
  have hc2 : ContDiffAt ℝ j (fun v : ℝ => (1 / 2 : ℂ) * f_even 1 (v / 2)) u := by
    have hcomp : AnalyticAt ℝ (fun v : ℝ => f_even 1 (v / 2)) u :=
      AnalyticAt.comp (g := f_even 1) (f := fun v : ℝ => v / 2)
        (hf1_an (u / 2) (show (0 : ℝ) < u / 2 by positivity)) (analyticAt_id.div analyticAt_const two_ne_zero)
    exact (analyticAt_const.mul hcomp).contDiffAt.of_le le_top
  have heq : iteratedDeriv j f_S2 u =
      iteratedDeriv j (f_even 1) u - iteratedDeriv j (fun v : ℝ => (1 / 2 : ℂ) * f_even 1 (v / 2)) u :=
    iteratedDeriv_fun_sub hc1 hc2
  rw [heq]; exact hu_bd

/-! #### 4B.4. Direct `u > 0` Autonomous-Readout Transfer & Unconditional `S² × S¹` Parity Theorems -/

private lemma scaledRay_sphereS2LogDeriv_eq {u : ℝ} (hu : 0 < u) :
    scaledRay sphereS2LogDerivSeries (Real.log u) =
      (u : ℂ) ^ 2 * f_S2 u + ((∫ y in Ioi (0 : ℝ), hFun 1 y) / 2) * (u : ℂ) ^ 2 + (1 / 12 : ℂ) := by
  have ht_eq : tRay (Real.log u) = (u : ℂ)⁻¹ := by
    unfold tRay; rw [Real.exp_neg, Real.exp_log hu]; push_cast; rfl
  have hq_eq : qRay (Real.log u) = Complex.exp (-((u⁻¹ : ℝ) : ℂ)) := by
    unfold qRay; rw [Real.exp_neg (Real.log u), Real.exp_log hu, Complex.ofReal_exp]; push_cast; rfl
  have hq_lt : ‖qRay (Real.log u)‖ < 1 := qRay_disk (Real.log u)
  -- value sphereS2LogDerivSeries q = value (sigmaSeries 2) q - 4 * value (sigmaSeries 2) (q^2)!
  have hexp2_val : value (PowerSeries.expand 2 (by omega) (sigmaSeries 2)) (qRay (Real.log u)) =
      value (sigmaSeries 2) ((qRay (Real.log u)) ^ 2) := by
    have habs_sq : AbsAt (sigmaSeries 2) ((qRay (Real.log u)) ^ 2) := by
      have hsq_lt : ‖(qRay (Real.log u)) ^ 2‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq_lt two_ne_zero
      simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound 2).to_diskCoeffBound 0 hsq_lt
    unfold value
    have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b h => by dsimp only at h; omega
    have hs_even : HasSum
        (fun m : ℕ => term (PowerSeries.expand 2 (by omega) (sigmaSeries 2)) (qRay (Real.log u)) (2 * m))
        (∑' m : ℕ, term (sigmaSeries 2) ((qRay (Real.log u)) ^ 2) m) := by
      have hfun : (fun m : ℕ => term (PowerSeries.expand 2 (by omega) (sigmaSeries 2)) (qRay (Real.log u)) (2 * m)) =
          fun m : ℕ => term (sigmaSeries 2) ((qRay (Real.log u)) ^ 2) m := by
        funext m; simp [term, PowerSeries.coeff_expand_mul, pow_mul]
      rw [hfun]; exact (habs_sq.of_norm).hasSum
    have hcomp := (hinj.hasSum_iff
      (f := fun n : ℕ => term (PowerSeries.expand 2 (by omega) (sigmaSeries 2)) (qRay (Real.log u)) n)
      (fun n hn => by
        have hndvd : ¬ 2 ∣ n := by intro ⟨m, hm⟩; exact hn ⟨m, hm.symm⟩
        simp [term, PowerSeries.coeff_expand_of_not_dvd 2 (by omega) _ hndvd])).mp hs_even
    exact hcomp.tsum_eq
  have hval_split : value sphereS2LogDerivSeries (qRay (Real.log u)) =
      value (sigmaSeries 2) (qRay (Real.log u)) - 4 * value (sigmaSeries 2) ((qRay (Real.log u)) ^ 2) := by
    let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 - 4 * MvPolynomial.X 1
    have hP_eq : MvPolynomial.aeval ![sigmaSeries 2, PowerSeries.expand 2 (by omega) (sigmaSeries 2)] P =
        sphereS2LogDerivSeries := by
      simp [P, sphereS2LogDerivSeries, map_ofNat]
    have habs_e2 : AbsAt (PowerSeries.expand 2 (by omega) (sigmaSeries 2)) (qRay (Real.log u)) := by
      have hpb : PolyCoeffBound (PowerSeries.expand 2 (by omega) (sigmaSeries 2)) := by
        obtain ⟨C, d, hC, hbd⟩ := sigmaSeries_polyBound 2
        refine ⟨C, d, hC, fun n => ?_⟩
        rw [PowerSeries.coeff_expand]
        split_ifs with h2
        · have hle : ((n / 2 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.div_le_self n 2)
          exact (hbd (n / 2)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle d) hC)
        · rw [norm_zero]; positivity
      simpa [seriesJet] using seriesJet_abs hpb.to_diskCoeffBound 0 hq_lt
    have h := (polynomial_value P (S := ![sigmaSeries 2, PowerSeries.expand 2 (by omega) (sigmaSeries 2)])
      (q := qRay (Real.log u)) (fun i => by
        fin_cases i
        · simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound 2).to_diskCoeffBound 0 hq_lt
        · exact habs_e2)).2
    rw [hP_eq] at h
    simpa [P, hexp2_val] using h
  -- Rewrite value (sigmaSeries 2) (exp(-1/v)) = v^2 * sumScale (hFun 1) v for both v = u and v = u/2!
  have hsig_v : ∀ v : ℝ, 0 < v →
      value (sigmaSeries 2) (Complex.exp (-((v⁻¹ : ℝ) : ℂ))) = (v : ℂ) ^ 2 * sumScale (hFun 1) v := by
    intro v hv
    rw [value_sigmaSeries_exp_neg 2 (inv_pos.mpr hv)]
    have hterm : ∀ d : ℕ,
        (((d + 1 : ℕ) : ℂ) ^ 2 / (Complex.exp (((d + 1 : ℕ) : ℂ) * ((v⁻¹ : ℝ) : ℂ)) - 1)) =
          (v : ℂ) ^ 2 * hFun 1 ((d + 1 : ℝ) / v) := fun d => by
      have hdv : (d + 1 : ℝ) / v ≠ 0 := div_ne_zero (by positivity) hv.ne'
      have hdvc : (((d + 1 : ℝ) / v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdv
      have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
      have hexp_nz : expAux (((d + 1 : ℝ) / v : ℝ) : ℂ) ≠ 0 :=
        expAux_ne_zero_of_abs_im_lt (by simp; positivity)
      have hmul := expAux_mul_sub_eos (((d + 1 : ℝ) / v : ℝ) : ℂ)
      dsimp only [hFun, qFun, qComplex]
      have hq_eq' : (expAux (((d + 1 : ℝ) / v : ℝ) : ℂ))⁻¹ =
          (((d + 1 : ℝ) / v : ℝ) : ℂ) / (Complex.exp (((d + 1 : ℝ) / v : ℝ) : ℂ) - 1) := by
        rw [← hmul]; field_simp [hdvc, hexp_nz]
      rw [hq_eq']; push_cast
      have harg : ((d : ℂ) + 1) * (v : ℂ)⁻¹ = ((d : ℂ) + 1) / (v : ℂ) := by ring
      rw [harg]; field_simp [hvc]
    simp_rw [hterm]; exact tsum_mul_left
  have hq2_eq : (qRay (Real.log u)) ^ 2 = Complex.exp (-(((u / 2)⁻¹ : ℝ) : ℂ)) := by
    rw [hq_eq, ← Complex.exp_nat_mul]; congr 1; push_cast
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    field_simp [huc]
  dsimp only [scaledRay, f_S2, f_even]
  rw [ht_eq, hval_split, hq2_eq, hq_eq, hsig_v u hu, hsig_v (u / 2) (by positivity)]
  have hb2 : (bernoulli 2 : ℂ) = 1 / 6 := by rw [bernoulli_two]; norm_num
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [hb2]; push_cast; field_simp [huc]; ring

private lemma sphereS2LogDerivSeries_no_autonomous_ode {J : ℕ} (P : MvPolynomial (Fin J) ℂ) (hP_ne : P ≠ 0)
    (hP_zero : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay sphereS2LogDerivSeries) y) P = 0) :
    False := by
  have hG_an : ∀ y : ℝ, AnalyticAt ℝ (scaledRay sphereS2LogDerivSeries) y :=
    scaledRay_analytic sphereS2LogDerivSeries_polyBound.to_diskCoeffBound
  have hG_on : AnalyticOnNhd ℝ (scaledRay sphereS2LogDerivSeries) Set.univ := fun z _ => hG_an z
  -- Extend P from atTop to all y ∈ ℝ by real-analyticity!
  have hP_all : ∀ y : ℝ,
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay sphereS2LogDerivSeries) y) P = 0 := by
    let evP : ℝ → ℂ := fun y =>
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay sphereS2LogDerivSeries) y) P
    have hev_an : AnalyticOnNhd ℝ evP Set.univ := by
      intro y _
      clear hP_ne hP_zero
      dsimp only [evP]
      induction P using MvPolynomial.induction_on with
      | C a => simpa using analyticAt_const
      | add A B hA hB => simp only [map_add]; exact hA.add hB
      | mul_X A j hA =>
        have hjet : AnalyticAt ℝ (iteratedDeriv j.val (scaledRay sphereS2LogDerivSeries)) y := by
          rw [iteratedDeriv_eq_iterate]
          exact (hG_on.iterated_deriv j.val) y (Set.mem_univ y)
        simp only [map_mul, MvPolynomial.eval_X]; exact hA.mul hjet
    obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.mp hP_zero
    have hfreq : ∃ᶠ y in 𝓝[≠] (y₀ + 1), evP y = 0 := by
      have hev : ∀ᶠ y in 𝓝 (y₀ + 1), evP y = 0 := by
        filter_upwards [isOpen_Ioi.mem_nhds (by linarith : y₀ < y₀ + 1)] with y hy
        exact hy₀ y (le_of_lt hy)
      exact (hev.filter_mono nhdsWithin_le_nhds).frequently
    have hzero := hev_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ (y₀ + 1)) hfreq
    intro y; exact hzero (Set.mem_univ y)
  -- Pull back to u ∈ (0, ∞) via y = log u!
  let yCoord : ℕ → ℝ → ℂ := fun k u =>
    iteratedDeriv k (scaledRay sphereS2LogDerivSeries) (Real.log u)
  have hrel : ∃ A : MvPolynomial ℕ ℂ, A ≠ 0 ∧ ∀ u ∈ Set.Ioi (0 : ℝ), MvPolynomial.eval (fun k => yCoord k u) A = 0 := by
    refine ⟨MvPolynomial.rename Fin.val P, ?_, fun u _ => ?_⟩
    · intro h0; exact hP_ne (MvPolynomial.rename_injective Fin.val Fin.val_injective (by simpa using h0))
    · rw [MvPolynomial.eval_rename]; exact hP_all (Real.log u)
  obtain ⟨n, A, u₁, hu₁, hS₁_ne, hA_zero⟩ := ordinary_relation (Set.Ioi (0 : ℝ)) ⟨1, zero_lt_one⟩ yCoord hrel
  let v : Fin (n + 1) → ℝ → ℂ := fun i u => yCoord i.val u
  let top : Fin (n + 1) := Fin.last n
  let g : Fin (n + 1) → ℝ → ℂ := fun i u => MvPolynomial.eval (fun j => v j u) (MvPolynomial.pderiv i A)
  let S : ℝ → ℂ := g top
  have hv_deriv : ∀ u : ℝ, 0 < u → ∀ k : ℕ,
      HasDerivAt (fun x : ℝ => yCoord k x) ((u : ℂ)⁻¹ * yCoord (k + 1) u) u := by
    intro u hu k
    have hjet : HasDerivAt (iteratedDeriv k (scaledRay sphereS2LogDerivSeries))
        (iteratedDeriv (k + 1) (scaledRay sphereS2LogDerivSeries) (Real.log u)) (Real.log u) := by
      rw [iteratedDeriv_succ]
      have han : AnalyticAt ℝ (iteratedDeriv k (scaledRay sphereS2LogDerivSeries)) (Real.log u) := by
        rw [iteratedDeriv_eq_iterate]
        exact (hG_on.iterated_deriv k) (Real.log u) (Set.mem_univ _)
      exact han.differentiableAt.hasDerivAt
    have hcomp := hjet.scomp u (Real.hasDerivAt_log hu.ne')
    refine hcomp.congr_deriv ?_
    rw [Complex.real_smul]; push_cast; rfl
  have hvanish : ∀ u : ℝ, 0 < u → ∑ i : Fin (n + 1), g i u * _root_.deriv (v i) u = 0 := by
    intro u hu
    have hchain := polynomial_chain A v (fun i => _root_.deriv (v i)) u
      (fun i => (hv_deriv u hu i.val).differentiableAt.hasDerivAt)
    have hnear : (fun x => MvPolynomial.eval (fun i => v i x) A) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx; exact hA_zero x hx
    exact hchain.deriv.symm.trans (hnear.deriv_eq.trans (deriv_const _ _))
  let invU : ℝ → ℂ := fun u => (u : ℂ)⁻¹
  let invS : ℝ → ℂ := fun u => (S u)⁻¹
  let uState : Fin (n + 1) ⊕ Fin 2 → ℝ → ℂ := Sum.elim v ![invU, invS]
  let Gen := Generated uState u₁
  have gv (i : Fin (n + 1)) : Gen (v i) := Generated.coord (Sum.inl i)
  have ginvU : Gen invU := Generated.coord (Sum.inr 0)
  have ginvS : Gen invS := Generated.coord (Sum.inr 1)
  have gc (c : ℂ) : Gen (fun _ => c) := Generated.const c
  have gg (i : Fin (n + 1)) : Gen (g i) := Generated.evalPoly v gv _
  have hS_diff : ∀ u : ℝ, 0 < u → DifferentiableAt ℝ S u := fun u hu =>
    (polynomial_chain (MvPolynomial.pderiv top A) v (fun i => _root_.deriv (v i)) u
      (fun i => (hv_deriv u hu i.val).differentiableAt.hasDerivAt)).differentiableAt
  have hSnz : ∀ᶠ u in 𝓝 u₁, S u ≠ 0 := (hS_diff u₁ hu₁).continuousAt.eventually_ne hS₁_ne
  have low (i : Fin (n + 1)) (hi : i ≠ top) : Gen (_root_.deriv (v i)) := by
    rcases i with ⟨k, hk⟩
    have hklt : k + 1 < n + 1 := by
      have hne : k ≠ n := fun h => hi (Fin.ext h); omega
    refine (ginvU.mul (gv ⟨k + 1, hklt⟩)).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu₁] with u hu
    exact ((hv_deriv u hu k).deriv).symm
  let lowSum : ℝ → ℂ := ∑ i ∈ Finset.univ.erase top, g i * _root_.deriv (v i)
  have glowSum : Gen lowSum :=
    Generated.finsetSum _ _ fun i hi => (gg i).mul (low i (Finset.mem_erase.mp hi).1)
  have dv (i : Fin (n + 1)) : Gen (_root_.deriv (v i)) := by
    by_cases hi : i = top
    · subst i
      refine (((gc (-1)).mul glowSum).mul ginvS).congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds hu₁, hSnz] with u hu hSu
      have hv0 := hvanish u hu
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at hv0
      have hh : S u * _root_.deriv (v top) u + lowSum u = 0 := by
        simpa [S, lowSum, Finset.sum_apply] using hv0
      change (-1 : ℂ) * lowSum u * (S u)⁻¹ = _root_.deriv (v top) u
      field_simp [hSu]; linear_combination -hh
    · exact low i hi
  have hdS : Gen (_root_.deriv S) := by
    let Dp (i : Fin (n + 1)) (u : ℝ) :=
      MvPolynomial.eval (fun j => v j u) (MvPolynomial.pderiv i (MvPolynomial.pderiv top A))
    have hDp (i) : Gen (Dp i) := Generated.evalPoly v gv _
    refine (Generated.finsetSum Finset.univ _ fun i _ => (hDp i).mul (dv i)).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu₁] with u hu
    simpa [Dp, Finset.sum_apply] using
      (polynomial_chain (MvPolynomial.pderiv top A) v (fun i => _root_.deriv (v i)) u
        (fun i => (hv_deriv u hu i.val).differentiableAt.hasDerivAt)).deriv.symm
  have hsmooth : ∀ᶠ u in 𝓝 u₁, ∀ i, DifferentiableAt ℝ (uState i) u := by
    filter_upwards [isOpen_Ioi.mem_nhds hu₁, hSnz] with u hu hSu i
    rcases i with i | i
    · exact (hv_deriv u hu i.val).differentiableAt
    · fin_cases i
      · exact Complex.ofRealCLM.differentiableAt.inv (Complex.ofReal_ne_zero.mpr hu.ne')
      · exact (hS_diff u hu).inv hSu
  have hclosed : ∀ i, Gen (_root_.deriv (uState i)) := by
    intro i
    rcases i with i | i
    · exact dv i
    · fin_cases i
      · refine ((gc (-1)).mul (ginvU.pow 2)).congr ?_
        filter_upwards [isOpen_Ioi.mem_nhds hu₁] with u hu
        have hne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
        have hi := (Complex.ofRealCLM.hasDerivAt.inv hne).deriv
        have hfun : invU = (⇑Complex.ofRealCLM)⁻¹ := rfl
        change (-1 : ℂ) * ((u : ℂ)⁻¹) ^ 2 = _root_.deriv invU u
        rw [hfun, hi]; simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; field_simp [hne]
      · refine (((gc (-1)).mul hdS).mul (ginvS.pow 2)).congr ?_
        filter_upwards [isOpen_Ioi.mem_nhds hu₁, hSnz] with u hu hSu
        have hi := ((hS_diff u hu).hasDerivAt.inv hSu).deriv
        have hfun : invS = S⁻¹ := rfl
        change (-1 : ℂ) * _root_.deriv S u * ((S u)⁻¹) ^ 2 = _root_.deriv invS u
        rw [hfun, hi]; field_simp [hSu]
  -- Read out f_S2(u) = (u⁻¹)² * (v 0 u - 1/12) - c₂ / 2!
  let c2 : ℂ := ∫ y in Ioi (0 : ℝ), hFun 1 y
  have gfS2 : Gen f_S2 := by
    refine (((ginvU.pow 2).mul ((gv 0).sub (gc (1 / 12 : ℂ)))).sub (gc (c2 / 2))).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu₁] with u hu
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have heq := scaledRay_sphereS2LogDeriv_eq hu
    change ((u : ℂ)⁻¹) ^ 2 * (scaledRay sphereS2LogDerivSeries (Real.log u) - 1 / 12) - c2 / 2 = f_S2 u
    rw [heq]; dsimp only [c2]; field_simp [huc]; ring
  obtain ⟨R₀, hR₀_ne, hR₀_nhds⟩ := autonomous_readout uState u₁ f_S2 gfS2 hsmooth hclosed
  -- Extend R₀ to all u > 0 by real-analyticity of f_S2 on (0, ∞)!
  have hfS2_an : AnalyticOnNhd ℝ f_S2 (Set.Ioi 0) := by
    intro u hu
    have hlog := _root_.analyticAt_log hu
    have hv0_an : AnalyticAt ℝ (fun x : ℝ => scaledRay sphereS2LogDerivSeries (Real.log x)) u :=
      AnalyticAt.comp (g := scaledRay sphereS2LogDerivSeries) (f := Real.log) (hG_an (Real.log u)) hlog
    have hinv_an := (Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr (ne_of_gt hu))
    have hrhs_an : AnalyticAt ℝ
        (fun x : ℝ => (x : ℂ)⁻¹ ^ 2 * (scaledRay sphereS2LogDerivSeries (Real.log x) - (1 / 12 : ℂ)) - c2 / 2) u :=
      ((hinv_an.pow 2).mul (hv0_an.sub (analyticAt_const (v := (1 / 12 : ℂ))))).sub
        (analyticAt_const (v := c2 / 2))
    refine hrhs_an.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have heq := scaledRay_sphereS2LogDeriv_eq hx
    change ((x : ℂ)⁻¹) ^ 2 * (scaledRay sphereS2LogDerivSeries (Real.log x) - 1 / 12) - c2 / 2 = f_S2 x
    rw [heq]; dsimp only [c2]; field_simp [hxc]; ring
  let N := Fintype.card (Fin (n + 1) ⊕ Fin 2)
  let evalR₀ : ℝ → ℂ := fun u =>
    MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f_S2 u) R₀
  have heval_an : AnalyticOnNhd ℝ evalR₀ (Set.Ioi 0) := by
    intro u hu
    clear hR₀_ne hR₀_nhds
    dsimp only [evalR₀]
    induction R₀ using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add A B hA hB => simp only [map_add]; exact hA.add hB
    | mul_X A j hA =>
      have hjet : AnalyticAt ℝ (iteratedDeriv j.val f_S2) u := by
        rw [iteratedDeriv_eq_iterate]; exact (hfS2_an.iterated_deriv j.val) u hu
      simp only [map_mul, MvPolynomial.eval_X]; exact hA.mul hjet
  have heval_zero : Set.EqOn evalR₀ 0 (Set.Ioi 0) :=
    heval_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Ioi hu₁
      ((Filter.Eventually.filter_mono nhdsWithin_le_nhds hR₀_nhds).frequently)
  have hR₀_atTop : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f_S2 u) R₀ = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu; exact heval_zero hu
  exact hR₀_ne (no_autonomous_ade_of_meromorphic_borel K_S2_borelData f_S2_hasAsympExp R₀ hR₀_atTop)

/-- **Thermal Conformal Scalar on `S² × S¹` (`d = 3`) — Unconditional Differential Transcendence of Free-Energy Derivative**:
For the free conformal scalar on `S² × S¹`, `x ∂_x log Z_{S²}(x²) = L₂(x) - 4 L₂(x²)`
satisfies NO nonzero algebraic differential equation over `ℂ(x)`. -/
theorem sphereS2LogDerivSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates sphereS2LogDerivSeries) := by
  by_contra hdep
  obtain ⟨J, P, hP_ne, hP_zero⟩ :=
    autonomous_transfer_disk sphereS2LogDerivSeries_polyBound.to_diskCoeffBound hdep
  exact sphereS2LogDerivSeries_no_autonomous_ode P hP_ne hP_zero

/-- **Thermal Conformal Scalar on `S² × S¹` (`d = 3`) — Unconditional Differential Transcendence of the Partition Function**:
For the free conformal scalar on `S² × S¹`, the thermal partition function
`Z_{S²}(x²) = ∏_{k ≥ 0} (1 - x^{2k+1})^{-(2k+1)} = M(x) / M(x²)²`
satisfies NO nonzero algebraic differential equation over `ℂ(x)`. -/
theorem sphereS2PartitionSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates sphereS2PartitionSeries) := by
  by_contra hdep
  obtain ⟨J, R, hR_ne, hR_zero⟩ := autonomous_transfer_log_deriv
    sphereS2PartitionSeries_diskBound sphereS2LogDerivSeries_polyBound.to_diskCoeffBound
    sphereS2PartitionSeries_ode sphereS2PartitionSeries_qRay_ne_zero hdep
  exact sphereS2LogDerivSeries_no_autonomous_ode R hR_ne hR_zero

/-- **Unified Thermal Free Conformal Scalar on `S^{d-1} × S¹` Dimensional-Parity Theorem**:
For a free conformally coupled scalar field on `S^{d-1} × S¹_β` :
1. **Even `d = 2` (`S¹ × S¹`):** Quasi-modular Eisenstein series `E₂` satisfies Chazy's
   autonomous order-3 ODE `2 D³ E₂ - 2 E₂ D² E₂ + 3 (D E₂)² = 0`.
2. **Even `d = 4` (`S³ × S¹`):** Both the free-energy derivative `L₃(q) = ∑ σ₃(n) q^n`
   and the full thermal partition function `Z_{S³}(q) = ∏_{n ≥ 1} (1 - q^n)^{-n²}` are
   **D-algebraic** over `ℂ(q)` (via the weight-4 Eisenstein series `E₄`).
3. **Odd `d = 3` (`S² × S¹`):** Both the free-energy derivative
   `x ∂_x log Z_{S²}(x²) = L₂(x) - 4 L₂(x²)` and the full thermal partition function
   `Z_{S²}(x²) = M(x) / M(x²)²` are unconditionally **D-transcendental** over `ℂ(x)`. -/
theorem conformalScalar_sphere_parity :
    (∀ z : ℍ, 2 * (D^[3] E2 z) - 2 * E2 z * (D^[2] E2 z) + 3 * (D E2 z) ^ 2 = 0) ∧
    (¬ AlgebraicIndependent ℂ (seriesCoordinates (sigmaSeries 3))) ∧
    (¬ AlgebraicIndependent ℂ (seriesCoordinates sphereS3PartitionSeries)) ∧
    AlgebraicIndependent ℂ (seriesCoordinates sphereS2LogDerivSeries) ∧
    AlgebraicIndependent ℂ (seriesCoordinates sphereS2PartitionSeries) :=
  ⟨circleS1ChazyODE, sphereS3LogDeriv_dAlgebraic, sphereS3PartitionSeries_dAlgebraic,
    sphereS2LogDerivSeries_algebraicIndependent, sphereS2PartitionSeries_algebraicIndependent⟩

end
end PakPrimes.ThermalGasEOS
