module

public import PakPrimes.BorelStokesVandermonde
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # General Theorem 2: End-to-End Meromorphic Borel–Stokes–Vandermonde Differential Transcendence

This module proves **General Theorem 2** completely end-to-end from genuine complex-analytic
hypotheses on a general meromorphic Borel transform `φ : ℂ → ℂ`, a strictly increasing positive
pole sequence `ω : ℕ → ℝ`, and nonzero simple-pole residues `res : ℕ → ℂ`:

1. **Specifications (`formalSeries`, `borelWedge`, `puncturedWedge`, `MeromorphicBorelData`)**:
   Only genuine analytic hypotheses are assumed:
   - `0 < ω 0` and `StrictMono ω`,
   - `∀ m, res m ≠ 0`,
   - `φ` is analytic on an open punctured wedge `B(0, ε) ∪ {Re z > 0, |Im z| < tan θ₀ · Re z} \ range ω`,
   - `(z - ω m) * φ z → res m` as `z → ω m` (`z ≠ ω m`) for every `m : ℕ`,
   - `φ` has exponential type along two tilted rays `exp (± i θ)` (`0 < θ < θ₀ < π / 2`).
2. **Triangle Cauchy–Goursat & Residue Formula (`triIntegral`, `triIntegral_eq_zero_of_analyticOn`,
   `triIntegral_inv_sub`)**:
   Establishes Cauchy's theorem and the `2πi` simple-pole residue formula on triangles
   `0 → R(1 - i tan θ) → R(1 + i tan θ) → 0` with vertical cut `Re z = R`.
3. **End-to-End Assembly (`borel_stokes_vandermonde_no_autonomous_ade`,
   `no_autonomous_ade_of_meromorphic_borel`)**:
   Constructs the lateral Borel minors, proves Borel algebra / Watson asymptotics / flatness bridge,
   derives the exact Stokes jump asymptotic expansion to arbitrary finite order `R_n = (ω n + ω (n+1))/2`
   with zero `cos θ` loss, and invokes `stokes_vandermonde_general_eq_zero`.
4. **Non-Vacuity Sanity Check (`gHat_no_autonomous_ade_via_general_theorem_2`)**:
   Instantiates General Theorem 2 directly on `φ(ξ) = Γ(1 - ξ)` with `ω m = m + 1` and
   `res m = (-1)^(m + 1) / m!` to recover `gHat_no_autonomous_ade`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.GeneralTheorem2

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open scoped Topology Interval

noncomputable section

/-! ### 1. Public Specifications -/

/-- Formal Borel–Laplace series `∑_{k ≥ 0} φ^{(k)}(0) u^{-k-1}` in `w = 1/u`. -/
@[expose] def formalSeries (φ : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => match n with
    | 0 => 0
    | k + 1 => iteratedDeriv k φ 0

/-- Open sectoral neighborhood around `[0, ∞)`: `B(0, ε) ∪ {z : Re z > 0, |Im z| < tan θ₀ · Re z}`. -/
@[expose] def borelWedge (θ₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ |z.im| < Real.tan θ₀ * z.re}

/-- Punctured open wedge avoiding all pole points `ω m`. -/
@[expose] def puncturedWedge (θ₀ ε : ℝ) (ω : ℕ → ℝ) : Set ℂ :=
  borelWedge θ₀ ε \ Set.range (fun m : ℕ => (ω m : ℂ))

/-- Genuine complex-analytic hypotheses for a meromorphic Borel transform `φ` with simple poles
at `0 < ω 0 < ω 1 < ...` and nonzero residues `res m ≠ 0`. -/
structure MeromorphicBorelData (φ : ℂ → ℂ) (ω : ℕ → ℝ) (res : ℕ → ℂ) where
  θ₀ : ℝ
  θ : ℝ
  ε : ℝ
  hθ_pos : 0 < θ
  hθ_lt : θ < θ₀
  hθ₀_lt : θ₀ < Real.pi / 2
  hε_pos : 0 < ε
  ω_pos : 0 < ω 0
  ω_mono : StrictMono ω
  res_ne_zero : ∀ m : ℕ, res m ≠ 0
  analyticOn : AnalyticOnNhd ℂ φ (puncturedWedge θ₀ ε ω)
  simple_pole : ∀ m : ℕ,
    Filter.Tendsto (fun z : ℂ => (z - (ω m : ℂ)) * φ z) (𝓝[≠] (ω m : ℂ)) (𝓝 (res m))
  expType_plus : ExpType (Minor.pull (Complex.exp (I * (θ : ℂ))) φ)
  expType_minus : ExpType (Minor.pull (Complex.exp (-I * (θ : ℂ))) φ)

/-! ### 2. Triangle Cauchy–Goursat Theorem and Residue Integral -/

/-- Closed triangle `{x + i y : 0 ≤ x ≤ R, |y| ≤ m · x}`. -/
@[expose] def closedTri (R m : ℝ) : Set ℂ :=
  {z : ℂ | 0 ≤ z.re ∧ z.re ≤ R ∧ |z.im| ≤ m * z.re}

/-- Counter-clockwise boundary integral of `F` around the triangle
`0 → R(1 - i m) → R(1 + i m) → 0`. -/
@[expose] def triIntegral (F : ℂ → ℂ) (R m : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) +
    I * (∫ y : ℝ in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * I)) -
    (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))))

private def TriBdIntegrable (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R

private lemma triIntegral_add {F G : ℂ → ℂ} {R m : ℝ}
    (hF : TriBdIntegrable F R m) (hG : TriBdIntegrable G R m) :
    triIntegral (fun z => F z + G z) R m = triIntegral F R m + triIntegral G R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (F ((x : ℂ) * (1 - I * (m : ℂ))) +
      G ((x : ℂ) * (1 - I * (m : ℂ))))) = fun x : ℝ =>
      (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ))) +
      (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := by
    funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (F ((x : ℂ) * (1 + I * (m : ℂ))) +
      G ((x : ℂ) * (1 + I * (m : ℂ))))) = fun x : ℝ =>
      (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))) +
      (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := by
    funext x; ring
  rw [h1, h2, intervalIntegral.integral_add hF.1 hG.1,
    intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2 hG.2.2]
  ring

private lemma triIntegral_const_mul (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) := by
    funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) := by
    funext x; ring
  rw [h1, h2, intervalIntegral.integral_const_mul c, intervalIntegral.integral_const_mul c,
    intervalIntegral.integral_const_mul c]
  ring

private lemma triIntegral_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntegrable (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert i s hi ih =>
    have hFi : TriBdIntegrable (F i) R m := hF i (Finset.mem_insert_self i s)
    have hFs : ∀ j ∈ s, TriBdIntegrable (F j) R m := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum_int : TriBdIntegrable (fun z => ∑ j ∈ s, F j z) R m := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 - I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 - I * (m : ℂ)) * F j ((x : ℂ) * (1 - I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]
        exact IntervalIntegrable.sum s fun j hj => (hFs j hj).1
      · have heq : (fun y : ℝ => ∑ j ∈ s, F j ((R : ℂ) + (y : ℂ) * I)) =
            ∑ j ∈ s, fun y : ℝ => F j ((R : ℂ) + (y : ℂ) * I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]
        exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.1
      · have heq : (fun x : ℝ => (1 + I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 + I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 + I * (m : ℂ)) * F j ((x : ℂ) * (1 + I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]
        exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.2
    have hfn : (fun z => ∑ j ∈ insert i s, F j z) = fun z => F i z + ∑ j ∈ s, F j z := by
      funext z; rw [Finset.sum_insert hi]
    rw [hfn, triIntegral_add hFi hsum_int, ih hFs, Finset.sum_insert hi]

private lemma triIntegral_congr {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 - I * (m : ℂ))) = G ((x : ℂ) * (1 - I * (m : ℂ))))
    (h2 : ∀ y ∈ Icc (-m * R) (m * R), F ((R : ℂ) + (y : ℂ) * I) = G ((R : ℂ) + (y : ℂ) * I))
    (h3 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 + I * (m : ℂ))) = G ((x : ℂ) * (1 + I * (m : ℂ)))) :
    triIntegral F R m = triIntegral G R m := by
  unfold triIntegral
  have hmR : -m * R ≤ m * R := by nlinarith
  have i1 : (∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR] at hx
    rw [h1 x hx]
  have i2 : (∫ y : ℝ in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-m * R)..(m * R), G ((R : ℂ) + (y : ℂ) * I) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hmR] at hy
    rw [h2 y hy]
  have i3 : (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR] at hx
    rw [h3 x hx]
  rw [i1, i2, i3]

private lemma triBdIntegrable_of_continuousOn {F : ℂ → ℂ} {R m : ℝ}
    (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntegrable F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma mem_closedTri_mul_one_add {R m x t : ℝ} (_hR : 0 ≤ R) (_hm : 0 ≤ m)
    (hx : x ∈ Icc 0 R) (ht : t ∈ Icc (-m) m) :
    (x : ℂ) * (1 + I * (t : ℂ)) ∈ closedTri R m := by
  have hre : ((x : ℂ) * (1 + I * (t : ℂ))).re = x := by
    simp [Complex.mul_re]
  have him : ((x : ℂ) * (1 + I * (t : ℂ))).im = x * t := by
    simp [Complex.mul_im]
  refine ⟨by rw [hre]; exact hx.1, by rw [hre]; exact hx.2, ?_⟩
  rw [hre, him, abs_mul, abs_of_nonneg hx.1, mul_comm m x]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) hx.1

/-- **Triangle Cauchy–Goursat Theorem**: if `F` is analytic on an open neighborhood `U`
of the closed triangle `closedTri R m`, then `triIntegral F R m = 0`. -/
lemma triIntegral_eq_zero_of_analyticOn {F : ℂ → ℂ} {R m : ℝ} {U : Set ℂ}
    (hR : 0 ≤ R) (hm : 0 ≤ m) (hU : IsOpen U) (hsub : closedTri R m ⊆ U)
    (hF : AnalyticOnNhd ℂ F U) :
    triIntegral F R m = 0 := by
  rcases eq_or_lt_of_le hR with rfl | _
  · simp [triIntegral]
  let H (x t : ℝ) : ℂ := (x : ℂ) * F ((x : ℂ) * (1 + I * (t : ℂ)))
  let Hx (x t : ℝ) : ℂ :=
    F ((x : ℂ) * (1 + I * (t : ℂ))) +
      (x : ℂ) * (1 + I * (t : ℂ)) * deriv F ((x : ℂ) * (1 + I * (t : ℂ)))
  let Φ (x : ℝ) : ℂ := I * ∫ t in (-m)..m, H x t
  have hm_le : -m ≤ m := by linarith
  have hS_open : IsOpen {p : ℝ × ℝ | (p.1 : ℂ) * (1 + I * (p.2 : ℂ)) ∈ U} :=
    hU.preimage (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * (1 + I * (p.2 : ℂ)))
  have hΦ_deriv : ∀ x₀ ∈ Icc 0 R, HasDerivAt Φ
      ((1 + I * (m : ℂ)) * F ((x₀ : ℂ) * (1 + I * (m : ℂ))) -
        (1 - I * (m : ℂ)) * F ((x₀ : ℂ) * (1 - I * (m : ℂ)))) x₀ := by
    intro x₀ hx₀
    have hprod_sub : ({x₀} : Set ℝ) ×ˢ uIcc (-m) m ⊆
        {p : ℝ × ℝ | (p.1 : ℂ) * (1 + I * (p.2 : ℂ)) ∈ U} := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      rw [mem_singleton_iff] at hx
      subst hx
      rw [uIcc_of_le hm_le] at ht
      exact hsub (mem_closedTri_mul_one_add hR hm hx₀ ht)
    obtain ⟨u, v, hu_open, _, hx₀u, hv_sub, huv_sub⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_uIcc hS_open hprod_sub
    obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
      Metric.nhds_basis_closedBall.mem_iff.mp (hu_open.mem_nhds (hx₀u (mem_singleton x₀)))
    have hbox_sub : ∀ p ∈ Metric.closedBall x₀ δ ×ˢ uIcc (-m) m,
        (p.1 : ℂ) * (1 + I * (p.2 : ℂ)) ∈ U :=
      fun _ hp => huv_sub ⟨hδ_ball hp.1, hv_sub hp.2⟩
    have hmap_cont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (1 + I * (p.2 : ℂ))) := by fun_prop
    have hF_cont_box : ContinuousOn (fun p : ℝ × ℝ => F ((p.1 : ℂ) * (1 + I * (p.2 : ℂ))))
        (Metric.closedBall x₀ δ ×ˢ uIcc (-m) m) :=
      hF.continuousOn.comp hmap_cont.continuousOn (fun p hp => hbox_sub p hp)
    have hdF_cont_box : ContinuousOn (fun p : ℝ × ℝ => deriv F ((p.1 : ℂ) * (1 + I * (p.2 : ℂ))))
        (Metric.closedBall x₀ δ ×ˢ uIcc (-m) m) :=
      hF.deriv.continuousOn.comp hmap_cont.continuousOn (fun p hp => hbox_sub p hp)
    have hHx_cont : ContinuousOn Hx.uncurry (Metric.closedBall x₀ δ ×ˢ uIcc (-m) m) :=
      hF_cont_box.add (hmap_cont.continuousOn.mul hdF_cont_box)
    obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ δ).prod isCompact_uIcc).exists_bound_of_continuousOn hHx_cont
    have hH_cont_on : ∀ x ∈ Metric.closedBall x₀ δ, ContinuousOn (H x) (uIcc (-m) m) := fun x hx =>
      continuousOn_const.mul (hF_cont_box.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hx, ht⟩))
    have hHx_cont_x₀ : ContinuousOn (Hx x₀) (uIcc (-m) m) :=
      hHx_cont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨Metric.mem_closedBall_self hδ_pos.le, ht⟩)
    have h_int_deriv : HasDerivAt (fun x => ∫ t in (-m)..m, H x t) (∫ t in (-m)..m, Hx x₀ t) x₀ := by
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := H) (F' := Hx) (x₀ := x₀) (s := Metric.ball x₀ δ) (bound := fun _ => B)
        (Metric.ball_mem_nhds x₀ hδ_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
      · filter_upwards [Metric.ball_mem_nhds x₀ hδ_pos] with x hx
        exact ((hH_cont_on x (Metric.ball_subset_closedBall hx)).aestronglyMeasurable
          measurableSet_uIcc).mono_measure (Measure.restrict_mono uIoc_subset_uIcc le_rfl)
      · exact (hH_cont_on x₀ (Metric.mem_closedBall_self hδ_pos.le)).intervalIntegrable
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
            ((x : ℂ) * (1 + I * (t : ℂ))) := (hF _ hmemU).differentiableAt.hasDerivAt
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
      have hK_deriv : ∀ t ∈ uIcc (-m) m, HasDerivAt K (I * Hx x₀ t) t := by
        intro t ht
        have hmemU : (x₀ : ℂ) * (1 + I * (t : ℂ)) ∈ U :=
          hbox_sub (x₀, t) ⟨Metric.mem_closedBall_self hδ_pos.le, ht⟩
        have hd_lin : HasDerivAt (fun s : ℝ => (1 : ℂ) + I * (s : ℂ)) I t := by
          have h1 : HasDerivAt (fun s : ℝ => I * (s : ℂ)) I t := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul I
          simpa using h1.const_add (1 : ℂ)
        have hd_arg : HasDerivAt (fun s : ℝ => (x₀ : ℂ) * (1 + I * (s : ℂ))) ((x₀ : ℂ) * I) t :=
          hd_lin.const_mul (x₀ : ℂ)
        have hd_F : HasDerivAt F (deriv F ((x₀ : ℂ) * (1 + I * (t : ℂ))))
            ((x₀ : ℂ) * (1 + I * (t : ℂ))) := (hF _ hmemU).differentiableAt.hasDerivAt
        exact (hd_lin.mul (hd_F.comp t hd_arg)).congr_deriv
          (by dsimp only [Hx, Function.comp_apply]; ring)
      have hK_int : IntervalIntegrable (fun t => I * Hx x₀ t) volume (-m) m :=
        (continuousOn_const.mul hHx_cont_x₀).intervalIntegrable
      have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hK_deriv hK_int
      rw [hev]
      dsimp only [K]
      simp only [Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg]
    simpa only [Φ, h_ftc_t] using h_int_deriv.const_mul I
  have h_sub_int : IntervalIntegrable (fun x : ℝ =>
      (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R ∧
      IntervalIntegrable (fun x : ℝ =>
        (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R := by
    refine ⟨?_, ?_⟩
    · exact (continuousOn_const.mul (hF.continuousOn.comp (by fun_prop) fun x hx =>
        hsub (mem_closedTri_mul_one_add hR hm hx ⟨hm_le, le_rfl⟩))).intervalIntegrable_of_Icc hR
    · refine (continuousOn_const.mul (hF.continuousOn.comp (by fun_prop) fun x hx => ?_)).intervalIntegrable_of_Icc hR
      have heq : (x : ℂ) * (1 - I * (m : ℂ)) = (x : ℂ) * (1 + I * ((-m : ℝ) : ℂ)) := by
        push_cast; ring
      rw [heq]
      exact hsub (mem_closedTri_mul_one_add hR hm hx ⟨le_rfl, hm_le⟩)
  have hΦ_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hΦ_deriv x (by simpa [uIcc_of_le hR] using hx))
    (h_sub_int.1.sub h_sub_int.2)
  have hΦ0 : Φ 0 = 0 := by simp [Φ, H]
  have hΦR : Φ R = I * (∫ y in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * I)) := by
    dsimp only [Φ, H]
    congr 1
    have heq : (fun t : ℝ => (R : ℂ) * F ((R : ℂ) * (1 + I * (t : ℂ)))) =
        fun t : ℝ => R • F ((R : ℂ) + ((R * t : ℝ) : ℂ) * I) := by
      funext t
      rw [Complex.real_smul]
      congr 2
      push_cast; ring
    rw [heq, intervalIntegral.integral_smul]
    have hcomp := intervalIntegral.smul_integral_comp_mul_left
      (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) R (a := -m) (b := m)
    rw [show R * -m = -m * R by ring, show R * m = m * R by ring] at hcomp
    exact hcomp
  rw [intervalIntegral.integral_sub h_sub_int.1 h_sub_int.2, hΦ0, sub_zero, hΦR] at hΦ_ftc
  unfold triIntegral
  linear_combination -hΦ_ftc

private lemma inv_real_add_mul_I' {u v : ℝ} (huv : u ^ 2 + v ^ 2 ≠ 0) :
    ((u : ℂ) + (v : ℂ) * I)⁻¹ =
      ((u / (u ^ 2 + v ^ 2) : ℝ) : ℂ) - ((v / (u ^ 2 + v ^ 2) : ℝ) : ℂ) * I := by
  have huvc : ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) ≠ 0 := by exact_mod_cast huv
  symm
  apply eq_inv_of_mul_eq_one_left
  push_cast
  field_simp [huvc]
  rw [show ((u : ℂ) - (v : ℂ) * I) * ((u : ℂ) + (v : ℂ) * I) =
    (u : ℂ) ^ 2 - (v : ℂ) ^ 2 * I ^ 2 by ring, Complex.I_sq]
  ring

private lemma odd_intervalIntegral_zero' {f : ℝ → ℝ} {b : ℝ}
    (hf : ∀ y : ℝ, f (-y) = -f y) :
    ∫ y in (-b)..b, f y = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg f (a := -b) (b := b)
  simp only [neg_neg, hf, intervalIntegral.integral_neg] at hcomp
  linarith

private lemma arctan_div_integral' (a b d : ℝ) (hd : d ≠ 0) :
    ∫ t in a..b, d / (d ^ 2 + t ^ 2) = Real.arctan (b / d) - Real.arctan (a / d) := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun x : ℝ => Real.arctan (x / d)) (d / (d ^ 2 + t ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x / d) d⁻¹ t := by
      simpa using (hasDerivAt_id t).div_const d
    have h2 := h1.arctan
    convert h2 using 1
    have hden : d ^ 2 + t ^ 2 ≠ 0 := by positivity
    have hden1 : 1 + (t / d) ^ 2 ≠ 0 := by positivity
    field_simp [hd, hden, hden1]
  have hcont : Continuous (fun t : ℝ => d / (d ^ 2 + t ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_pow 2)) fun t => by positivity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)

private lemma arctan_tri_identity {c m R : ℝ} (hc : 0 < c) (hm : 0 < m) (hR : c < R) :
    Real.arctan (((1 + m ^ 2) * R - c) / (m * c)) + Real.arctan (m * R / (R - c)) +
      Real.arctan (1 / m) = Real.pi := by
  let g (r : ℝ) : ℝ :=
    Real.arctan (((1 + m ^ 2) * r - c) / (m * c)) + Real.arctan (m * r / (r - c))
  have hg_diff : DifferentiableOn ℝ g (Ioi c) := by
    intro r hr
    have hrc : r - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
    refine (DifferentiableAt.add ?_ ?_).differentiableWithinAt
    · exact (((differentiableAt_id.const_mul _).sub_const _).div_const _).arctan
    · exact ((differentiableAt_id.const_mul m).div (differentiableAt_id.sub_const c) hrc).arctan
  have hg_deriv : (Ioi c).EqOn (deriv g) 0 := by
    intro r hr
    change deriv g r = 0
    have hrc : r - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
    have hmc : m * c ≠ 0 := by positivity
    have hd1 : HasDerivAt (fun t : ℝ => Real.arctan (((1 + m ^ 2) * t - c) / (m * c)))
        (m * c / ((r - c) ^ 2 + m ^ 2 * r ^ 2)) r := by
      have hlin : HasDerivAt (fun t : ℝ => ((1 + m ^ 2) * t - c) / (m * c))
          ((1 + m ^ 2) / (m * c)) r := by
        have h := ((hasDerivAt_id r).const_mul (1 + m ^ 2)).sub_const c
        simpa using h.div_const (m * c)
      convert hlin.arctan using 1
      have hD : (r - c) ^ 2 + m ^ 2 * r ^ 2 ≠ 0 := by
        have hpos : 0 < (r - c) ^ 2 + m ^ 2 * r ^ 2 := by positivity
        exact hpos.ne'
      have hden1 : 1 + (((1 + m ^ 2) * r - c) / (m * c)) ^ 2 ≠ 0 := by positivity
      have h1m : 1 + m ^ 2 ≠ 0 := by positivity
      field_simp [hmc, hD, hden1]
      ring
    have hd2 : HasDerivAt (fun t : ℝ => Real.arctan (m * t / (t - c)))
        (-(m * c / ((r - c) ^ 2 + m ^ 2 * r ^ 2))) r := by
      have hnum : HasDerivAt (fun t : ℝ => m * t) m r := by
        simpa using (hasDerivAt_id r).const_mul m
      have hden : HasDerivAt (fun t : ℝ => t - c) 1 r := by
        simpa using (hasDerivAt_id r).sub_const c
      have hquo : HasDerivAt (fun t : ℝ => m * t / (t - c)) (-m * c / (r - c) ^ 2) r := by
        convert hnum.div hden hrc using 1
        field_simp [hrc]
        ring
      convert hquo.arctan using 1
      have hD : (r - c) ^ 2 + m ^ 2 * r ^ 2 ≠ 0 := by
        have hpos : 0 < (r - c) ^ 2 + m ^ 2 * r ^ 2 := by positivity
        exact hpos.ne'
      have hden2 : 1 + (m * r / (r - c)) ^ 2 ≠ 0 := by positivity
      field_simp [hrc, hD, hden2]
    exact (hd1.add hd2).deriv.trans (by ring)
  have hg_const : ∀ r > c, g r = g R := fun r hr =>
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi c).isPreconnected hg_diff hg_deriv hr hR
  have hg_lim : Tendsto g atTop (𝓝 (Real.pi / 2 + Real.arctan m)) := by
    have ht1 : Tendsto (fun r : ℝ => Real.arctan (((1 + m ^ 2) * r - c) / (m * c)))
        atTop (𝓝 (Real.pi / 2)) := by
      refine (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_
      have h_lin : Tendsto (fun r : ℝ => ((1 + m ^ 2) / (m * c)) * r + (-(c / (m * c))))
          atTop atTop :=
        (tendsto_id.const_mul_atTop (by positivity : 0 < (1 + m ^ 2) / (m * c))).atTop_add
          tendsto_const_nhds
      refine h_lin.congr fun r => ?_
      ring
    have ht2 : Tendsto (fun r : ℝ => Real.arctan (m * r / (r - c))) atTop (𝓝 (Real.arctan m)) := by
      refine Real.continuous_arctan.continuousAt.tendsto.comp ?_
      have h_div : Tendsto (fun r : ℝ => m / (1 - c / r)) atTop (𝓝 (m / (1 - 0))) := by
        refine tendsto_const_nhds.div (tendsto_const_nhds.sub ?_) (by norm_num)
        exact tendsto_const_nhds.div_atTop tendsto_id
      rw [sub_zero, div_one] at h_div
      refine h_div.congr' ?_
      filter_upwards [eventually_gt_atTop c] with r hr
      have hr0 : r ≠ 0 := (lt_trans hc hr).ne'
      have hrc : r - c ≠ 0 := (sub_pos.mpr hr).ne'
      field_simp [hr0, hrc]
    exact ht1.add ht2
  have hg_ev : Tendsto (fun _ : ℝ => g R) atTop (𝓝 (Real.pi / 2 + Real.arctan m)) :=
    hg_lim.congr' (by
      filter_upwards [eventually_gt_atTop c] with r hr
      exact hg_const r hr)
  have hgR : g R = Real.pi / 2 + Real.arctan m := tendsto_nhds_unique tendsto_const_nhds hg_ev
  have harctan_inv : Real.arctan (1 / m) = Real.pi / 2 - Real.arctan m := by
    simpa [one_div] using Real.arctan_inv_of_pos hm
  dsimp only [g] at hgR
  linarith

/-- **Triangle Residue Formula** for `(z - c)⁻¹` when `0 < c < R` and `0 < m`. -/
lemma triIntegral_inv_sub {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) :
    triIntegral (fun z : ℂ => (z - (c : ℂ))⁻¹) R m = 2 * (Real.pi : ℂ) * I := by
  let D (x : ℝ) : ℝ := (x - c) ^ 2 + m ^ 2 * x ^ 2
  have hD_pos : ∀ x : ℝ, 0 < D x := by
    intro x
    by_cases hx : x = 0
    · subst hx; dsimp only [D]
      exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (by linarith))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · have h1 : 0 ≤ (x - c) ^ 2 := sq_nonneg _
      have h2 : 0 < m ^ 2 * x ^ 2 := mul_pos (sq_pos_of_pos hm) (sq_pos_of_ne_zero hx)
      dsimp only [D]; linarith
  have hne_line : ∀ (s : ℝ), s ≠ 0 → ∀ x : ℝ, (x : ℂ) * (1 + I * (s : ℂ)) - (c : ℂ) ≠ 0 := by
    intro s hs x h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.one_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.one_im,
      mul_one, Complex.zero_re, Complex.zero_im] at hre him
    have him0 : x = 0 := by
      have : x * s = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hs
    subst him0
    linarith
  have hne_minus : ∀ x : ℝ, (x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ) ≠ 0 := by
    intro x h0
    apply hne_line (-m) (neg_ne_zero.mpr hm.ne') x
    convert h0 using 2; push_cast; ring
  have hne_plus : ∀ x : ℝ, (x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ) ≠ 0 := hne_line m hm.ne'
  have hc_m : Continuous (fun x : ℝ => (1 - I * (m : ℂ)) * ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) :=
    continuous_const.mul (Continuous.inv₀ (by fun_prop) hne_minus)
  have hc_p : Continuous (fun x : ℝ => (1 + I * (m : ℂ)) * ((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) :=
    continuous_const.mul (Continuous.inv₀ (by fun_prop) hne_plus)
  have h_diag : (∫ x : ℝ in (0 : ℝ)..R,
      (1 - I * (m : ℂ)) * ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) -
      (∫ x : ℝ in (0 : ℝ)..R,
      (1 + I * (m : ℂ)) * ((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) =
      ((2 * (Real.arctan (((1 + m ^ 2) * R - c) / (m * c)) + Real.arctan (1 / m)) : ℝ) : ℂ) * I := by
    rw [← intervalIntegral.integral_sub (hc_m.intervalIntegrable 0 R) (hc_p.intervalIntegrable 0 R)]
    have hcongr : (fun x : ℝ =>
        (1 - I * (m : ℂ)) * ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹ -
        (1 + I * (m : ℂ)) * ((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) =
        fun x : ℝ => ((2 * (m * c / D x) : ℝ) : ℂ) * I := by
      funext x
      have h1 := hne_minus x
      have h2 := hne_plus x
      have hDc : (D x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hD_pos x).ne'
      have hden : ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ)) *
          ((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ)) = (D x : ℂ) := by
        calc _ = ((x : ℂ) - (c : ℂ)) ^ 2 - (I * (m : ℂ) * (x : ℂ)) ^ 2 := by ring
          _ = ((x : ℂ) - (c : ℂ)) ^ 2 + (m : ℂ) ^ 2 * (x : ℂ) ^ 2 := by
              rw [mul_pow, mul_pow, Complex.I_sq]; ring
          _ = (D x : ℂ) := by dsimp only [D]; push_cast; ring
      have hnum : (1 - I * (m : ℂ)) * ((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ)) -
          (1 + I * (m : ℂ)) * ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ)) =
          2 * (m : ℂ) * (c : ℂ) * I := by ring
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_sub_div _ _ h1 h2,
        mul_comm ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ)) (1 + I * (m : ℂ)), hnum, hden]
      push_cast; ring
    rw [hcongr, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul]
    have h_int : ∫ x : ℝ in (0 : ℝ)..R, m * c / D x =
        Real.arctan (((1 + m ^ 2) * R - c) / (m * c)) + Real.arctan (1 / m) := by
      have hderiv : ∀ x ∈ uIcc (0 : ℝ) R,
          HasDerivAt (fun t : ℝ => Real.arctan (((1 + m ^ 2) * t - c) / (m * c))) (m * c / D x) x := by
        intro x _
        have hlin : HasDerivAt (fun t : ℝ => ((1 + m ^ 2) * t - c) / (m * c))
            ((1 + m ^ 2) / (m * c)) x := by
          have h := ((hasDerivAt_id x).const_mul (1 + m ^ 2)).sub_const c
          simpa using h.div_const (m * c)
        convert hlin.arctan using 1
        have hmc : m * c ≠ 0 := by positivity
        have hDx : D x ≠ 0 := (hD_pos x).ne'
        have hden : 1 + (((1 + m ^ 2) * x - c) / (m * c)) ^ 2 ≠ 0 := by positivity
        have h1m : 1 + m ^ 2 ≠ 0 := by positivity
        have hD_alg : (m * c) ^ 2 + ((1 + m ^ 2) * x - c) ^ 2 = (1 + m ^ 2) * D x := by
          dsimp only [D]; ring
        symm
        calc 1 / (1 + (((1 + m ^ 2) * x - c) / (m * c)) ^ 2) * ((1 + m ^ 2) / (m * c))
            = ((1 + m ^ 2) * (m * c)) / ((m * c) ^ 2 + ((1 + m ^ 2) * x - c) ^ 2) := by
              field_simp [hmc, hden]
          _ = ((1 + m ^ 2) * (m * c)) / ((1 + m ^ 2) * D x) := by rw [hD_alg]
          _ = m * c / D x := by field_simp [h1m, hDx]
      have hcont : Continuous (fun x : ℝ => m * c / D x) :=
        continuous_const.div (by unfold D; fun_prop) (fun x => (hD_pos x).ne')
      have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 R)
      rw [hev]
      have h0 : Real.arctan (((1 + m ^ 2) * 0 - c) / (m * c)) = -Real.arctan (1 / m) := by
        rw [← Real.arctan_neg]
        congr 1
        have hmc : m * c ≠ 0 := by positivity
        field_simp [hmc]
        ring
      rw [h0, sub_neg_eq_add]
    rw [h_int]
  let d : ℝ := R - c
  have hd : 0 < d := sub_pos.mpr hR
  have h_vert : I * (∫ y : ℝ in (-m * R)..(m * R), ((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) =
      ((2 * Real.arctan (m * R / (R - c)) : ℝ) : ℂ) * I := by
    rw [← intervalIntegral.integral_const_mul]
    have hcongr : (fun y : ℝ => I * ((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) =
        fun y : ℝ => ((y / (d ^ 2 + y ^ 2) : ℝ) : ℂ) + ((d / (d ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
      funext y
      have he : (R : ℂ) + (y : ℂ) * I - (c : ℂ) = ((d : ℂ) + (y : ℂ) * I) := by
        dsimp only [d]; push_cast; ring
      rw [he, inv_real_add_mul_I' (u := d) (v := y)
        (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg y)))]
      push_cast
      rw [show I * ((d / (d ^ 2 + y ^ 2) : ℂ) - (y / (d ^ 2 + y ^ 2) : ℂ) * I) =
        (d / (d ^ 2 + y ^ 2) : ℂ) * I - (y / (d ^ 2 + y ^ 2) : ℂ) * I ^ 2 by ring,
        Complex.I_sq]
      ring
    rw [hcongr]
    have hiA : IntervalIntegrable (fun y : ℝ => ((y / (d ^ 2 + y ^ 2) : ℝ) : ℂ))
        volume (-m * R) (m * R) :=
      (Complex.continuous_ofReal.comp (continuous_id.div (continuous_const.add (continuous_pow 2))
        fun y => ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg y)))).intervalIntegrable
          (-m * R) (m * R)
    have hiB : IntervalIntegrable (fun y : ℝ => ((d / (d ^ 2 + y ^ 2) : ℝ) : ℂ) * I)
        volume (-m * R) (m * R) :=
      ((Complex.continuous_ofReal.comp (continuous_const.div (continuous_const.add (continuous_pow 2))
        fun y => ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg y)))).mul
          continuous_const).intervalIntegrable (-m * R) (m * R)
    rw [intervalIntegral.integral_add hiA hiB, intervalIntegral.integral_ofReal]
    have h_odd : ∫ y in (-m * R)..(m * R), y / (d ^ 2 + y ^ 2) = 0 := by
      rw [show -m * R = -(m * R) by ring]
      exact odd_intervalIntegral_zero' fun y => by rw [neg_sq]; ring
    rw [h_odd, Complex.ofReal_zero, zero_add, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, arctan_div_integral' (-m * R) (m * R) d hd.ne']
    have hneg : Real.arctan (-m * R / d) = -Real.arctan (m * R / d) := by
      rw [← Real.arctan_neg]; congr 1; ring
    rw [hneg, sub_neg_eq_add, ← two_mul]
  unfold triIntegral
  calc (∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) +
        I * (∫ y : ℝ in (-m * R)..(m * R), ((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) -
        (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * ((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹)
      = ((∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * ((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) -
          (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * ((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹)) +
          I * (∫ y : ℝ in (-m * R)..(m * R), ((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) := by ring
    _ = ((2 * (Real.arctan (((1 + m ^ 2) * R - c) / (m * c)) + Real.arctan (1 / m)) : ℝ) : ℂ) * I +
          ((2 * Real.arctan (m * R / (R - c)) : ℝ) : ℂ) * I := by rw [h_diag, h_vert]
    _ = ((2 * (Real.arctan (((1 + m ^ 2) * R - c) / (m * c)) + Real.arctan (m * R / (R - c)) +
          Real.arctan (1 / m)) : ℝ) : ℂ) * I := by push_cast; ring
    _ = 2 * (Real.pi : ℂ) * I := by
          rw [arctan_tri_identity hc hm hR]
          push_cast; ring

/-! ### 3. Lateral Star Domains, Borel Algebra, and Bridge -/

private def ε₀ {φ ω res} (h : MeromorphicBorelData φ ω res) : ℝ :=
  min h.ε (ω 0 / 2)

private lemma ε₀_pos {φ ω res} (h : MeromorphicBorelData φ ω res) : 0 < ε₀ h :=
  lt_min h.hε_pos (half_pos h.ω_pos)

private lemma ε₀_le_ε {φ ω res} (h : MeromorphicBorelData φ ω res) : ε₀ h ≤ h.ε :=
  min_le_left _ _

private lemma ε₀_lt_ω {φ ω res} (h : MeromorphicBorelData φ ω res) (m : ℕ) : ε₀ h < ω m := by
  have h1 : ε₀ h ≤ ω 0 / 2 := min_le_right _ _
  have h2 : ω 0 / 2 < ω 0 := half_lt_self h.ω_pos
  have h3 : ω 0 ≤ ω m := h.ω_mono.monotone (Nat.zero_le m)
  linarith

private lemma tan_pos_of_mem {α : ℝ} (h1 : 0 < α) (h2 : α < Real.pi / 2) : 0 < Real.tan α :=
  Real.tan_pos_of_pos_of_lt_pi_div_two h1 h2

private lemma tan_lt_tan {φ ω res} (h : MeromorphicBorelData φ ω res) :
    Real.tan h.θ < Real.tan h.θ₀ :=
  Real.strictMonoOn_tan
    ⟨by linarith [h.hθ_pos, Real.pi_pos], h.hθ_lt.trans h.hθ₀_lt⟩
    ⟨by linarith [h.hθ_pos, h.hθ_lt, Real.pi_pos], h.hθ₀_lt⟩
    h.hθ_lt

private lemma cos_pos_θ {φ ω res} (h : MeromorphicBorelData φ ω res) : 0 < Real.cos h.θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.hθ_pos, Real.pi_pos], h.hθ_lt.trans h.hθ₀_lt⟩

private lemma sin_pos_θ {φ ω res} (h : MeromorphicBorelData φ ω res) : 0 < Real.sin h.θ :=
  Real.sin_pos_of_pos_of_lt_pi h.hθ_pos (h.hθ_lt.trans (h.hθ₀_lt.trans (by linarith [Real.pi_pos])))

private def dPlusG {φ ω res} (h : MeromorphicBorelData φ ω res) : ℂ :=
  Complex.exp (I * (h.θ : ℂ))

private def dMinusG {φ ω res} (h : MeromorphicBorelData φ ω res) : ℂ :=
  Complex.exp (-I * (h.θ : ℂ))

private lemma dPlusG_eq {φ ω res} (h : MeromorphicBorelData φ ω res) :
    dPlusG h = (Real.cos h.θ : ℂ) + (Real.sin h.θ : ℂ) * I := by
  unfold dPlusG
  rw [mul_comm I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma dMinusG_eq {φ ω res} (h : MeromorphicBorelData φ ω res) :
    dMinusG h = (Real.cos h.θ : ℂ) - (Real.sin h.θ : ℂ) * I := by
  unfold dMinusG
  rw [show -I * (h.θ : ℂ) = ((-h.θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

private lemma dPlusG_re {φ ω res} (h : MeromorphicBorelData φ ω res) :
    (dPlusG h).re = Real.cos h.θ := by
  rw [dPlusG_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

private lemma dPlusG_im {φ ω res} (h : MeromorphicBorelData φ ω res) :
    (dPlusG h).im = Real.sin h.θ := by
  rw [dPlusG_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]

private lemma dMinusG_re {φ ω res} (h : MeromorphicBorelData φ ω res) :
    (dMinusG h).re = Real.cos h.θ := by
  rw [dMinusG_eq]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

private lemma dMinusG_im {φ ω res} (h : MeromorphicBorelData φ ω res) :
    (dMinusG h).im = -Real.sin h.θ := by
  rw [dMinusG_eq]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]

private lemma norm_dPlusG {φ ω res} (h : MeromorphicBorelData φ ω res) : ‖dPlusG h‖ = 1 := by
  unfold dPlusG
  rw [mul_comm I]
  exact Complex.norm_exp_ofReal_mul_I h.θ

private lemma norm_dMinusG {φ ω res} (h : MeromorphicBorelData φ ω res) : ‖dMinusG h‖ = 1 := by
  unfold dMinusG
  rw [show -I * (h.θ : ℂ) = ((-h.θ : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-h.θ)

private def wedgePlus (θ₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < Real.tan θ₀ * z.re}

private def wedgeMinus (θ₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -Real.tan θ₀ * z.re < z.im}

private lemma isOpen_wedgePlus (θ₀ ε : ℝ) : IsOpen (wedgePlus θ₀ ε) :=
  Metric.isOpen_ball.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re))))

private lemma isOpen_wedgeMinus (θ₀ ε : ℝ) : IsOpen (wedgeMinus θ₀ ε) :=
  Metric.isOpen_ball.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt (continuous_const.mul Complex.continuous_re) Complex.continuous_im)))

private lemma star_wedgePlus (θ₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ z ∈ wedgePlus θ₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ wedgePlus θ₀ ε := by
  intro z hz t ht
  rcases hz with hz_ball | ⟨hre, him, htan⟩
  · left
    rw [Metric.mem_ball, dist_zero_right] at hz_ball ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz_ball
  · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left; simpa [Metric.mem_ball, dist_zero_right] using hε
    · right
      refine ⟨?_, ?_, ?_⟩
      · simpa [Complex.mul_re] using mul_pos ht_pos hre
      · simpa [Complex.mul_im] using mul_pos ht_pos him
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.mul_im, add_zero]
        nlinarith [ht_pos, htan]

private lemma star_wedgeMinus (θ₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ z ∈ wedgeMinus θ₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ wedgeMinus θ₀ ε := by
  intro z hz t ht
  rcases hz with hz_ball | ⟨hre, him, htan⟩
  · left
    rw [Metric.mem_ball, dist_zero_right] at hz_ball ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz_ball
  · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left; simpa [Metric.mem_ball, dist_zero_right] using hε
    · right
      refine ⟨?_, ?_, ?_⟩
      · simpa [Complex.mul_re] using mul_pos ht_pos hre
      · simpa [Complex.mul_im] using mul_neg_of_pos_of_neg ht_pos him
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.mul_im, add_zero]
        nlinarith [ht_pos, htan]

private lemma wedgePlus_domain (θ₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : Domain (wedgePlus θ₀ ε) :=
  ⟨isOpen_wedgePlus θ₀ ε, star_wedgePlus θ₀ hε⟩

private lemma wedgeMinus_domain (θ₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : Domain (wedgeMinus θ₀ ε) :=
  ⟨isOpen_wedgeMinus θ₀ ε, star_wedgeMinus θ₀ hε⟩

private lemma isPreconnected_wedgePlus {φ ω res} (h : MeromorphicBorelData φ ω res) :
    IsPreconnected (wedgePlus h.θ₀ (ε₀ h)) := by
  let S₁ : Set ℂ := Metric.ball (0 : ℂ) (ε₀ h)
  let S₂ : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < Real.tan h.θ₀ * z.re}
  have h1 : IsPreconnected S₁ := (convex_ball (0 : ℂ) (ε₀ h)).isPreconnected
  have h2 : IsPreconnected S₂ := by
    refine Convex.isPreconnected ?_
    intro x hx y hy a b ha hb hab
    simp only [S₂, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · refine ⟨add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.1) (mul_nonneg hb hy.1.le),
        add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.2.1) (mul_nonneg hb hy.2.1.le), ?_⟩
      have h1' : a * x.im < a * (Real.tan h.θ₀ * x.re) := mul_lt_mul_of_pos_left hx.2.2 ha_pos
      have h2' : b * y.im ≤ b * (Real.tan h.θ₀ * y.re) := mul_le_mul_of_nonneg_left hy.2.2.le hb
      linarith
  refine h1.union' ?_ h2
  refine ⟨((ε₀ h / 2 : ℝ) : ℂ) * dPlusG h, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos (ε₀_pos h)), norm_dPlusG h, mul_one]
    linarith [ε₀_pos h]
  · have hre : 0 < (((ε₀ h / 2 : ℝ) : ℂ) * dPlusG h).re := by
      simp [Complex.mul_re, dPlusG_re h]
      exact mul_pos (half_pos (ε₀_pos h)) (cos_pos_θ h)
    have him : 0 < (((ε₀ h / 2 : ℝ) : ℂ) * dPlusG h).im := by
      simp [Complex.mul_im, dPlusG_im h]
      exact mul_pos (half_pos (ε₀_pos h)) (sin_pos_θ h)
    have htan : (((ε₀ h / 2 : ℝ) : ℂ) * dPlusG h).im <
        Real.tan h.θ₀ * (((ε₀ h / 2 : ℝ) : ℂ) * dPlusG h).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero, dPlusG_re h, dPlusG_im h]
      have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
        rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θ h).ne']
      rw [hsin_eq]
      have hc0 : 0 < (ε₀ h / 2) * Real.cos h.θ := mul_pos (half_pos (ε₀_pos h)) (cos_pos_θ h)
      calc (ε₀ h / 2) * (Real.tan h.θ * Real.cos h.θ)
          = Real.tan h.θ * ((ε₀ h / 2) * Real.cos h.θ) := by ring
        _ < Real.tan h.θ₀ * ((ε₀ h / 2) * Real.cos h.θ) := mul_lt_mul_of_pos_right (tan_lt_tan h) hc0
    exact ⟨hre, him, htan⟩

private lemma isPreconnected_wedgeMinus {φ ω res} (h : MeromorphicBorelData φ ω res) :
    IsPreconnected (wedgeMinus h.θ₀ (ε₀ h)) := by
  let S₁ : Set ℂ := Metric.ball (0 : ℂ) (ε₀ h)
  let S₂ : Set ℂ := {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -Real.tan h.θ₀ * z.re < z.im}
  have h1 : IsPreconnected S₁ := (convex_ball (0 : ℂ) (ε₀ h)).isPreconnected
  have h2 : IsPreconnected S₂ := by
    refine Convex.isPreconnected ?_
    intro x hx y hy a b ha hb hab
    simp only [S₂, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · refine ⟨add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.1) (mul_nonneg hb hy.1.le), ?_, ?_⟩
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg ha_pos hx.2.1)
          (mul_nonpos_of_nonneg_of_nonpos hb hy.2.1.le)
      · have h1' : a * (-Real.tan h.θ₀ * x.re) < a * x.im := mul_lt_mul_of_pos_left hx.2.2 ha_pos
        have h2' : b * (-Real.tan h.θ₀ * y.re) ≤ b * y.im := mul_le_mul_of_nonneg_left hy.2.2.le hb
        linarith
  refine h1.union' ?_ h2
  refine ⟨((ε₀ h / 2 : ℝ) : ℂ) * dMinusG h, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos (ε₀_pos h)), norm_dMinusG h, mul_one]
    linarith [ε₀_pos h]
  · have hre : 0 < (((ε₀ h / 2 : ℝ) : ℂ) * dMinusG h).re := by
      simp [Complex.mul_re, dMinusG_re h]
      exact mul_pos (half_pos (ε₀_pos h)) (cos_pos_θ h)
    have him : (((ε₀ h / 2 : ℝ) : ℂ) * dMinusG h).im < 0 := by
      simp [Complex.mul_im, dMinusG_im h]
      exact mul_pos (half_pos (ε₀_pos h)) (sin_pos_θ h)
    have htan : -Real.tan h.θ₀ * (((ε₀ h / 2 : ℝ) : ℂ) * dMinusG h).re <
        (((ε₀ h / 2 : ℝ) : ℂ) * dMinusG h).im := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero, dMinusG_re h, dMinusG_im h]
      have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
        rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θ h).ne']
      rw [hsin_eq]
      have hc0 : 0 < (ε₀ h / 2) * Real.cos h.θ := mul_pos (half_pos (ε₀_pos h)) (cos_pos_θ h)
      calc -Real.tan h.θ₀ * ((ε₀ h / 2) * Real.cos h.θ)
          < -Real.tan h.θ * ((ε₀ h / 2) * Real.cos h.θ) :=
            mul_lt_mul_of_pos_right (neg_lt_neg (tan_lt_tan h)) hc0
        _ = (ε₀ h / 2) * -(Real.tan h.θ * Real.cos h.θ) := by ring
    exact ⟨hre, him, htan⟩

private lemma wedgePlus_containsRay {φ ω res} (h : MeromorphicBorelData φ ω res) :
    ContainsRay (wedgePlus h.θ₀ (ε₀ h)) (dPlusG h) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa [Metric.mem_ball, dist_zero_right] using ε₀_pos h
  · right
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.mul_im, dPlusG_re h, dPlusG_im h]
    rw [zero_add]
    refine ⟨mul_pos (cos_pos_θ h) hv_pos, mul_pos (sin_pos_θ h) hv_pos, ?_⟩
    have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θ h).ne']
    rw [hsin_eq]
    have hvc : 0 < Real.cos h.θ * v := mul_pos (cos_pos_θ h) hv_pos
    calc Real.tan h.θ * Real.cos h.θ * v
        = Real.tan h.θ * (Real.cos h.θ * v) := by ring
      _ < Real.tan h.θ₀ * (Real.cos h.θ * v) := mul_lt_mul_of_pos_right (tan_lt_tan h) hvc

private lemma wedgeMinus_containsRay {φ ω res} (h : MeromorphicBorelData φ ω res) :
    ContainsRay (wedgeMinus h.θ₀ (ε₀ h)) (dMinusG h) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa [Metric.mem_ball, dist_zero_right] using ε₀_pos h
  · right
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.mul_im, dMinusG_re h, dMinusG_im h]
    rw [zero_add]
    refine ⟨mul_pos (cos_pos_θ h) hv_pos, ?_, ?_⟩
    · nlinarith [hv_pos, sin_pos_θ h]
    · have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
        rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θ h).ne']
      rw [hsin_eq]
      have hvc : 0 < Real.cos h.θ * v := mul_pos (cos_pos_θ h) hv_pos
      calc -Real.tan h.θ₀ * (Real.cos h.θ * v)
          < -Real.tan h.θ * (Real.cos h.θ * v) :=
            mul_lt_mul_of_pos_right (neg_lt_neg (tan_lt_tan h)) hvc
        _ = -(Real.tan h.θ * Real.cos h.θ) * v := by ring

private lemma wedgePlus_subset_punctured {φ ω res} (h : MeromorphicBorelData φ ω res) :
    wedgePlus h.θ₀ (ε₀ h) ⊆ puncturedWedge h.θ₀ h.ε ω := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hz_ball | ⟨hre, him, htan⟩
    · left
      rw [Metric.mem_ball] at hz_ball ⊢
      exact hz_ball.trans_le (ε₀_le_ε h)
    · right
      exact ⟨hre, by rw [abs_of_pos him]; exact htan⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hz_ball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m)))] at hz_ball
      linarith [ε₀_lt_ω h m]
    · simp at him

private lemma wedgeMinus_subset_punctured {φ ω res} (h : MeromorphicBorelData φ ω res) :
    wedgeMinus h.θ₀ (ε₀ h) ⊆ puncturedWedge h.θ₀ h.ε ω := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hz_ball | ⟨hre, him, htan⟩
    · left
      rw [Metric.mem_ball] at hz_ball ⊢
      exact hz_ball.trans_le (ε₀_le_ε h)
    · right
      exact ⟨hre, by rw [abs_of_neg him]; linarith⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hz_ball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m)))] at hz_ball
      linarith [ε₀_lt_ω h m]
    · simp at him

private def aPhi (φ : ℂ → ℂ) : Minor := ⟨0, φ⟩

private lemma aPhi_toSeries (φ : ℂ → ℂ) : (aPhi φ).toSeries = formalSeries φ := by
  ext n
  cases n <;> simp [aPhi, Minor.toSeries, formalSeries]

private lemma aPhi_good_plus {φ ω res} (h : MeromorphicBorelData φ ω res) :
    (aPhi φ).Good (wedgePlus h.θ₀ (ε₀ h)) (dPlusG h) :=
  ⟨h.analyticOn.mono (wedgePlus_subset_punctured h), h.expType_plus⟩

private lemma aPhi_good_minus {φ ω res} (h : MeromorphicBorelData φ ω res) :
    (aPhi φ).Good (wedgeMinus h.θ₀ (ε₀ h)) (dMinusG h) :=
  ⟨h.analyticOn.mono (wedgeMinus_subset_punctured h), h.expType_minus⟩

private lemma analyticAt_eqOn_zero_of_iteratedDeriv_zero' {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) :
    EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz
    simpa [smul_eq_mul] using hz
  have hdn : iteratedDeriv n f 0 = (n.factorial : ℂ) * g 0 := by
    rw [hloc.iteratedDeriv_eq n]
    have hmul := iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ))
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0).contDiffAt hg.contDiffAt
    rw [hmul]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ n) (0 : ℂ) * iteratedDeriv (n - i) g 0 =
          if i = n then (n.factorial : ℂ) * g 0 else 0 := by
      intro i _
      rw [iteratedDeriv_fun_pow_zero]
      split_ifs with hin
      · subst hin; simp [Nat.choose_self]
      · simp
    rw [Finset.sum_congr rfl hterm]
    simp
  have hzero := hderiv n
  rw [hdn] at hzero
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) hzero

private lemma formalEval_zero_implies_lateral_zero {φ ω res} (h : MeromorphicBorelData φ ω res)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval (formalSeries φ) P = 0) :
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ)) u) P = 0) ∧
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ)) u) P = 0) := by
  let Up := wedgePlus h.θ₀ (ε₀ h)
  let Um := wedgeMinus h.θ₀ (ε₀ h)
  have hUp_dom : Domain Up := wedgePlus_domain h.θ₀ (ε₀_pos h)
  have hUm_dom : Domain Um := wedgeMinus_domain h.θ₀ (ε₀_pos h)
  have hrayP : ContainsRay Up (dPlusG h) := wedgePlus_containsRay h
  have hrayM : ContainsRay Um (dMinusG h) := wedgeMinus_containsRay h
  have hgoodP : (aPhi φ).Good Up (dPlusG h) := aPhi_good_plus h
  have hgoodM : (aPhi φ).Good Um (dMinusG h) := aPhi_good_minus h
  have hreP : 0 < (dPlusG h).re := by rw [dPlusG_re h]; exact cos_pos_θ h
  have hreM : 0 < (dMinusG h).re := by rw [dMinusG_re h]; exact cos_pos_θ h
  obtain ⟨e, hs, he⟩ := BorelExpr.exists_of_mvPolynomial P
  have hres_series : (e.residual (aPhi φ)).toSeries = 0 := by
    rw [hs Up (dPlusG h) (aPhi φ) hUp_dom hrayP hgoodP, aPhi_toSeries, hP]
  have hatom : (e.residual (aPhi φ)).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series
    simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual (aPhi φ)).density 0 = 0 := by
    intro k
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series
    simpa [Minor.toSeries] using this
  have hplus_dens : EqOn (e.residual (aPhi φ)).density 0 Up :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zero' (isPreconnected_wedgePlus h)
      (by simpa using hrayP 0 le_rfl) (e.represents hUp_dom hrayP hgoodP).1.1 hderiv_zero
  have hminus_dens : EqOn (e.residual (aPhi φ)).density 0 Um :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zero' (isPreconnected_wedgeMinus h)
      (by simpa using hrayM 0 le_rfl) (e.represents hUm_dom hrayM hgoodM).1.1 hderiv_zero
  constructor
  · have hrep := (tendsto_coe_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
    filter_upwards [hrep, he Up (dPlusG h) (aPhi φ) hUp_dom hrayP hgoodP hreP] with u hu_rep hu_ev
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hplus_dens (hrayP v hv.le)]
  · have hrep := (tendsto_coe_far hreM).eventually (e.represents hUm_dom hrayM hgoodM).2
    filter_upwards [hrep, he Um (dMinusG h) (aPhi φ) hUm_dom hrayM hgoodM hreM] with u hu_rep hu_ev
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hminus_dens (hrayM v hv.le)]

private lemma eval_lateral_flat_implies_formalEval_zero {φ ω res} (h : MeromorphicBorelData φ ω res)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℂ)
    (hQ : ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ)) u) Q‖ ≤
        C * Real.exp (-δ₀ * u)) :
    formalEval (formalSeries φ) Q = 0 := by
  let Up := wedgePlus h.θ₀ (ε₀ h)
  have hUp_dom : Domain Up := wedgePlus_domain h.θ₀ (ε₀_pos h)
  have hrayP : ContainsRay Up (dPlusG h) := wedgePlus_containsRay h
  have hgoodP : (aPhi φ).Good Up (dPlusG h) := aPhi_good_plus h
  have hreP : 0 < (dPlusG h).re := by rw [dPlusG_re h]; exact cos_pos_θ h
  obtain ⟨C, hC⟩ := hQ
  obtain ⟨e, hs, he⟩ := BorelExpr.exists_of_mvPolynomial Q
  have hrep := (tendsto_coe_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have hflat : ∀ M : ℕ, ∃ C_M : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖(e.residual (aPhi φ)).value (dPlusG h) (u : ℂ)‖ ≤ C_M / u ^ (M + 1) := by
    intro M
    refine ⟨max C 0 * (((M + 1).factorial : ℝ) / δ₀ ^ (M + 1)), ?_⟩
    filter_upwards [hC, hrep, he Up (dPlusG h) (aPhi φ) hUp_dom hrayP hgoodP hreP,
      eventually_gt_atTop (0 : ℝ)] with u huC hurep huev hupos
    rw [← hurep, huev]
    have hexp : Real.exp (-δ₀ * u) ≤ ((M + 1).factorial : ℝ) / (δ₀ ^ (M + 1) * u ^ (M + 1)) := by
      have harg := Real.pow_div_factorial_le_exp (δ₀ * u) (by positivity) (M + 1)
      have hfac : 0 < ((M + 1).factorial : ℝ) := by positivity
      have hpow : 0 < (δ₀ * u) ^ (M + 1) := pow_pos (by positivity) (M + 1)
      calc Real.exp (-δ₀ * u) = (Real.exp (δ₀ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
        _ ≤ ((δ₀ * u) ^ (M + 1) / ((M + 1).factorial : ℝ))⁻¹ :=
            inv_anti₀ (div_pos hpow hfac) harg
        _ = ((M + 1).factorial : ℝ) / (δ₀ ^ (M + 1) * u ^ (M + 1)) := by
            rw [inv_div, mul_pow]
    calc ‖MvPolynomial.eval (fun j : Fin (r + 1) =>
            iteratedDeriv j.val (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ)) u) Q‖
        ≤ C * Real.exp (-δ₀ * u) := huC
      _ ≤ max C 0 * Real.exp (-δ₀ * u) := mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 * (((M + 1).factorial : ℝ) / (δ₀ ^ (M + 1) * u ^ (M + 1))) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right C 0)
      _ = (max C 0 * (((M + 1).factorial : ℝ) / δ₀ ^ (M + 1))) / u ^ (M + 1) := by ring
  have hzero := Minor.toSeries_eq_zero_of_flat (e.residual (aPhi φ)) hUp_dom hrayP
    (e.represents hUp_dom hrayP hgoodP).1 hreP hflat
  rwa [hs Up (dPlusG h) (aPhi φ) hUp_dom hrayP hgoodP, aPhi_toSeries] at hzero

private lemma lateral_bounded_derivatives {φ ω res} (h : MeromorphicBorelData φ ω res) (j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ)) u‖ ≤ C := by
  let Up := wedgePlus h.θ₀ (ε₀ h)
  have hUp_dom : Domain Up := wedgePlus_domain h.θ₀ (ε₀_pos h)
  have hrayP : ContainsRay Up (dPlusG h) := wedgePlus_containsRay h
  have hgoodP : (aPhi φ).Good Up (dPlusG h) := aPhi_good_plus h
  have hreP : 0 < (dPlusG h).re := by rw [dPlusG_re h]; exact cos_pos_θ h
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have ha := (e.represents hUp_dom hrayP hgoodP).1
  obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := Minor.value_asymptotic (e.residual (aPhi φ)) hUp_dom hrayP ha hreP 0
  have hrep := (tendsto_coe_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have heq := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhi φ) hUp_dom hrayP hgoodP hreP j).1
  refine ⟨‖(e.residual (aPhi φ)).atom‖ + C₀, ?_⟩
  filter_upwards [hC₀, hrep, heq, eventually_ge_atTop (1 : ℝ)] with u hu0 hurep hueq hu1
  have heq' : iteratedDeriv j (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ)) u =
      (e.residual (aPhi φ)).value (dPlusG h) (u : ℂ) := hueq.symm.trans hurep
  rw [heq']
  have hu0' : ‖(e.residual (aPhi φ)).value (dPlusG h) (u : ℂ) - (e.residual (aPhi φ)).atom‖ ≤ C₀ := by
    simpa using hu0.trans (div_le_self hC₀_nonneg (one_le_pow₀ hu1))
  calc ‖(e.residual (aPhi φ)).value (dPlusG h) (u : ℂ)‖
      = ‖((e.residual (aPhi φ)).value (dPlusG h) (u : ℂ) - (e.residual (aPhi φ)).atom) +
          (e.residual (aPhi φ)).atom‖ := by congr 1; ring
    _ ≤ ‖(e.residual (aPhi φ)).value (dPlusG h) (u : ℂ) - (e.residual (aPhi φ)).atom‖ +
          ‖(e.residual (aPhi φ)).atom‖ := norm_add_le _ _
    _ ≤ ‖(e.residual (aPhi φ)).atom‖ + C₀ := by linarith

private lemma lateral_eventually_differentiable {φ ω res} (h : MeromorphicBorelData φ ω res) (k : ℕ) :
    (∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ
      (iteratedDeriv k (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ))) u) ∧
    (∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ
      (iteratedDeriv k (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ))) u) :=
  ⟨(BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhi φ) (wedgePlus_domain h.θ₀ (ε₀_pos h))
      (wedgePlus_containsRay h) (aPhi_good_plus h) (by rw [dPlusG_re h]; exact cos_pos_θ h) k).2,
   (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhi φ) (wedgeMinus_domain h.θ₀ (ε₀_pos h))
      (wedgeMinus_containsRay h) (aPhi_good_minus h) (by rw [dMinusG_re h]; exact cos_pos_θ h) k).2⟩

private lemma coeff_zero_d_u_iter_series {φ : ℂ → ℂ} (k : ℕ) :
    PowerSeries.coeff 0 (d_u^[k] (formalSeries φ)) = 0 := by
  cases k with
  | zero => simp [formalSeries]
  | succ k =>
    rw [Function.iterate_succ_apply']
    simp [d_u]

private lemma coeff_zero_formalEval_series {φ : ℂ → ℂ} {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) :
    PowerSeries.coeff 0 (formalEval (formalSeries φ) P) = MvPolynomial.eval 0 P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [formalEval]
  | add A B hA hB =>
    rw [formalEval, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hA hB
  | mul_X A j hA =>
    simp only [formalEval, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, Pi.zero_apply,
      mul_zero] at hA ⊢
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_d_u_iter_series j.val, mul_zero]

/-! ### 4. Stokes Jump Expansion for General Meromorphic `φ` -/

private lemma jet_residual_density (φ : ℂ → ℂ) (j : ℕ) (z : ℂ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhi φ)).density z =
      (-z) ^ j * φ z := by
  induction j with
  | zero => simp [aPhi, BorelExpr.residual]
  | succ j ih =>
    rw [Function.iterate_succ_apply', BorelExpr.residual, Minor.jet]
    dsimp only
    rw [ih, pow_succ']
    ring

private lemma jet_residual_atom (φ : ℂ → ℂ) (j : ℕ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhi φ)).atom = 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [Function.iterate_succ_apply', BorelExpr.residual, Minor.jet]

private lemma iteratedDeriv_lateral_eq_laplace {φ ω res} (_h : MeromorphicBorelData φ ω res)
    {U : Set ℂ} {d : ℂ} (hU : Domain U) (ray : ContainsRay U d)
    (ha : (aPhi φ).Good U d) (hd : 0 < d.re) (j : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhi φ).value d (t : ℂ)) u =
        ∫ v in Ioi (0 : ℝ), d * ((-(d * (v : ℂ))) ^ j *
          Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ))) := by
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have he_rep := (tendsto_coe_far hd).eventually (e.represents hU ray ha).2
  have he_deriv := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhi φ) hU ray ha hd j).1
  filter_upwards [he_rep, he_deriv] with u hurep hud
  rw [← hud, hurep, Minor.value, jet_residual_atom φ j, zero_add]
  unfold complexLaplace
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [damped, Minor.pull, jet_residual_density φ j]
  have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
  rw [hexp]
  ring

private def cutR {φ ω res} (_h : MeromorphicBorelData φ ω res) (n : ℕ) : ℝ :=
  (ω n + ω (n + 1)) / 2

private lemma cutR_pos {φ ω res} (h : MeromorphicBorelData φ ω res) (n : ℕ) :
    0 < cutR h n := by
  have h1 : 0 < ω n := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le n))
  have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  dsimp only [cutR]; linarith

private lemma ω_lt_cutR {φ ω res} (h : MeromorphicBorelData φ ω res) {m n : ℕ} (hm : m ≤ n) :
    ω m < cutR h n := by
  have h1 : ω m ≤ ω n := h.ω_mono.monotone hm
  have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  dsimp only [cutR]; linarith

private lemma cutR_lt_ω {φ ω res} (h : MeromorphicBorelData φ ω res) {m n : ℕ} (hm : n + 1 ≤ m) :
    cutR h n < ω m := by
  have h1 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  have h2 : ω (n + 1) ≤ ω m := h.ω_mono.monotone hm
  dsimp only [cutR]; linarith

private lemma closedTri_subset_cutOpen {φ ω res} (h : MeromorphicBorelData φ ω res) (n : ℕ) :
    closedTri (cutR h n) (Real.tan h.θ) ⊆
      borelWedge h.θ₀ (ε₀ h) ∩ {z : ℂ | z.re < ω (n + 1)} := by
  intro z hz
  have hlt_next : z.re < ω (n + 1) := lt_of_le_of_lt hz.2.1 (cutR_lt_ω h le_rfl)
  refine ⟨?_, hlt_next⟩
  rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
  · left
    have him0 : z.im = 0 := by
      have habs : |z.im| ≤ 0 := by simpa [← hz0] using hz.2.2
      exact abs_nonpos_iff.mp habs
    have hz_eq : z = 0 := Complex.ext hz0.symm him0
    simpa [hz_eq, Metric.mem_ball, dist_zero_right] using ε₀_pos h
  · right
    refine ⟨hzpos, lt_of_le_of_lt hz.2.2 ?_⟩
    exact mul_lt_mul_of_pos_right (tan_lt_tan h) hzpos

private lemma poleSub_analyticOn_cutOpen {φ ω res} (h : MeromorphicBorelData φ ω res) (n : ℕ) :
    let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1), res m / (z - (ω m : ℂ))
    let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      by classical exact if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
    AnalyticOnNhd ℂ ψn (borelWedge h.θ₀ (ε₀ h) ∩ {z : ℂ | z.re < ω (n + 1)}) := by
  classical
  intro Sn Pset ψn
  let Un : Set ℂ := borelWedge h.θ₀ (ε₀ h) ∩ {z : ℂ | z.re < ω (n + 1)}
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
      · left; exact Metric.ball_subset_ball (ε₀_le_ε h) hw_ball
      · right; exact hw_sec
    · rintro ⟨m, rfl⟩
      have hm_lt : ω m < ω (n + 1) := by simpa using hwU.2
      have hm_idx : m < n + 1 := h.ω_mono.lt_iff_lt.mp hm_lt
      exact hwP ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr hm_idx), rfl⟩
  have hSn_an : ∀ z ∈ Un \ Pset, AnalyticAt ℂ Sn z := by
    intro z hz
    refine Finset.analyticAt_fun_sum _ fun m hm => ?_
    refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
    intro h0
    apply hz.2
    exact ⟨m, Finset.mem_coe.mpr hm, (sub_eq_zero.mp h0).symm⟩
  intro z hzU
  by_cases hzP : z ∈ Pset
  · obtain ⟨k, hk_mem, rfl⟩ := hzP
    have hk : k < n + 1 := Finset.mem_range.mp hk_mem
    let hkFun : ℂ → ℂ := Function.update (fun ζ => (ζ - (ω k : ℂ)) * φ ζ) (ω k : ℂ) (res k)
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
      have hsub_open : Vk \ {(ω k : ℂ)} ⊆ Un \ Pset := by
        intro ζ hζ
        exact ⟨hζ.1.1, fun hP => hζ.2 (by
          by_contra hne
          exact hζ.1.2 ⟨hP, hne⟩)⟩
      have hφ_an : AnalyticAt ℂ φ w := h.analyticOn w (hUn_sub (hsub_open hw))
      have hdiff_mul : DifferentiableAt ℂ (fun ζ => (ζ - (ω k : ℂ)) * φ ζ) w :=
        (differentiableAt_id.sub_const _).mul hφ_an.differentiableAt
      have heq : hkFun =ᶠ[𝓝 w] fun ζ => (ζ - (ω k : ℂ)) * φ ζ := by
        filter_upwards [isOpen_ne.mem_nhds hw.2] with ζ hζ
        exact Function.update_of_ne hζ _ _
      exact hdiff_mul.congr_of_eventuallyEq heq
    have hhk_cont : ContinuousAt hkFun (ω k : ℂ) :=
      continuousAt_update_same.mpr (h.simple_pole k)
    have hhk_an : AnalyticAt ℂ hkFun (ω k : ℂ) :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hhk_diff_punc hhk_cont
    obtain ⟨ρ, hρ_pos, hρ_diff⟩ := Metric.eventually_nhds_iff.mp hhk_an.eventually_analyticAt
    have hgk_diff : DifferentiableOn ℂ (dslope hkFun (ω k : ℂ)) (Metric.ball (ω k : ℂ) ρ) :=
      (Complex.differentiableOn_dslope (Metric.ball_mem_nhds _ hρ_pos)).mpr
        (fun w hw => (hρ_diff (Metric.mem_ball.mp hw)).differentiableAt.differentiableWithinAt)
    have hgk_an : AnalyticAt ℂ (dslope hkFun (ω k : ℂ)) (ω k : ℂ) :=
      hgk_diff.analyticAt (Metric.ball_mem_nhds _ hρ_pos)
    let Gk (w : ℂ) : ℂ :=
      dslope hkFun (ω k : ℂ) w -
        ∑ m ∈ (Finset.range (n + 1)).erase k, res m / (w - (ω m : ℂ))
    have hGk_an : AnalyticAt ℂ Gk (ω k : ℂ) := by
      refine hgk_an.sub (Finset.analyticAt_fun_sum _ fun m hm => ?_)
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
      intro h0
      exact h.ω_mono.injective.ne hmk.symm (by exact_mod_cast sub_eq_zero.mp h0)
    have hGk_eq_punc : ∀ᶠ w in 𝓝[≠] (ω k : ℂ), φ w - Sn w = Gk w := by
      filter_upwards [hmem_punc] with w hw
      have hw_ne : w ≠ (ω k : ℂ) := hw.2
      have hsub_ne : w - (ω k : ℂ) ≠ 0 := sub_ne_zero.mpr hw_ne
      have hslope_eq : dslope hkFun (ω k : ℂ) w = φ w - res k / (w - (ω k : ℂ)) := by
        rw [dslope_of_ne hkFun hw_ne, slope_def_field]
        have h1 : hkFun w = (w - (ω k : ℂ)) * φ w := Function.update_of_ne hw_ne _ _
        have h2 : hkFun (ω k : ℂ) = res k := Function.update_self _ _ _
        rw [h1, h2]
        field_simp [hsub_ne]
      have hsum_split : Sn w = res k / (w - (ω k : ℂ)) +
          ∑ m ∈ (Finset.range (n + 1)).erase k, res m / (w - (ω m : ℂ)) := by
        dsimp only [Sn]
        rw [← Finset.add_sum_erase (Finset.range (n + 1)) (fun m => res m / (w - (ω m : ℂ)))
          (Finset.mem_range.mpr hk)]
      dsimp only [Gk]
      rw [hslope_eq, hsum_split]
      ring
    have hlim_eq : Filter.limUnder (𝓝[≠] (ω k : ℂ)) (fun w => φ w - Sn w) = Gk (ω k : ℂ) :=
      (hGk_an.continuousAt.continuousWithinAt.tendsto.congr' (hGk_eq_punc.mono fun _ => Eq.symm)).limUnder_eq
    have hψ_loc : ψn =ᶠ[𝓝 (ω k : ℂ)] Gk := by
      have hmem_nhds : Vk ∩ {w : ℂ | w ≠ (ω k : ℂ) → φ w - Sn w = Gk w} ∈ 𝓝 (ω k : ℂ) :=
        inter_mem (hVk_open.mem_nhds hwk_Vk) (eventually_nhdsWithin_iff.mp hGk_eq_punc)
      filter_upwards [hmem_nhds] with w ⟨hwVk, hw_imp⟩
      by_cases hwk : w = (ω k : ℂ)
      · subst hwk
        have hmemP : (ω k : ℂ) ∈ Pset := ⟨k, Finset.mem_coe.mpr (Finset.mem_range.mpr hk), rfl⟩
        dsimp only [ψn]
        rw [ite_eq_left_iff.mpr (fun hnot => absurd hmemP hnot), hlim_eq]
      · have hw_not_P : w ∉ Pset := fun hP => hwVk.2 ⟨hP, hwk⟩
        dsimp only [ψn]
        rw [ite_eq_right_iff.mpr (fun hmem => absurd hmem hw_not_P)]
        exact hw_imp hwk
    exact hGk_an.congr hψ_loc.symm
  · have hopen : IsOpen (Un \ Pset) := hUn_open.sdiff hP_closed
    have hmem : Un \ Pset ∈ 𝓝 z := hopen.mem_nhds ⟨hzU, hzP⟩
    have hdiff_an : AnalyticAt ℂ (fun w => φ w - Sn w) z :=
      (h.analyticOn z (hUn_sub ⟨hzU, hzP⟩)).sub (hSn_an z ⟨hzU, hzP⟩)
    have heq : ψn =ᶠ[𝓝 z] fun w => φ w - Sn w := by
      filter_upwards [hmem] with w hw
      dsimp only [ψn]
      exact ite_eq_right_iff.mpr (fun hmemP => absurd hmemP hw.2)
    exact hdiff_an.congr heq.symm

private lemma triBd_avoid_poles {φ ω res} (h : MeromorphicBorelData φ ω res) (n : ℕ) :
    (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 - I * (Real.tan h.θ : ℂ)) ≠ (ω m : ℂ)) ∧
    (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 + I * (Real.tan h.θ : ℂ)) ≠ (ω m : ℂ)) ∧
    (∀ y : ℝ, ∀ m : ℕ, (cutR h n : ℂ) + (y : ℂ) * I ≠ (ω m : ℂ)) := by
  have hm_pos : 0 < Real.tan h.θ := tan_pos_of_mem h.hθ_pos (h.hθ_lt.trans h.hθ₀_lt)
  refine ⟨?_, ?_, ?_⟩
  · intro x m h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
    have hx0 : x = 0 := by
      have : x * (-Real.tan h.θ) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right (neg_ne_zero.mpr hm_pos.ne')
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    linarith
  · intro x m h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
    have hx0 : x = 0 := by
      have : x * Real.tan h.θ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hm_pos.ne'
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    linarith
  · intro y m h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, Complex.ofReal_im] at hre
    have hre' : cutR h n = ω m := by simpa using hre
    rcases le_or_gt m n with hmn | hnm
    · exact (ω_lt_cutR h hmn).ne hre'.symm
    · exact (cutR_lt_ω h hnm).ne hre'

private lemma triIntegral_φ_kernel {φ ω res} (h : MeromorphicBorelData φ ω res)
    (n j : ℕ) (u : ℝ) :
    triIntegral (fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z) (cutR h n) (Real.tan h.θ) =
      ∑ m ∈ Finset.range (n + 1), (2 * (Real.pi : ℂ) * I * res m) * (-(ω m : ℂ)) ^ j *
        Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
  classical
  let R : ℝ := cutR h n
  let mθ : ℝ := Real.tan h.θ
  have hR_pos : 0 < R := cutR_pos h n
  have hm_pos : 0 < mθ := tan_pos_of_mem h.hθ_pos (h.hθ_lt.trans h.hθ₀_lt)
  let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1), res m / (z - (ω m : ℂ))
  let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
  let ψn (z : ℂ) : ℂ :=
    if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
  let Un : Set ℂ := borelWedge h.θ₀ (ε₀ h) ∩ {z : ℂ | z.re < ω (n + 1)}
  have hUn_open : IsOpen Un :=
    (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)))).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hψ_an : AnalyticOnNhd ℂ ψn Un := poleSub_analyticOn_cutOpen h n
  let Fψ (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * ψn z
  have hFψ_an : AnalyticOnNhd ℂ Fψ Un :=
    ((analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)).mul
      hψ_an
  have htri_ψ : triIntegral Fψ R mθ = 0 :=
    triIntegral_eq_zero_of_analyticOn hR_pos.le hm_pos.le hUn_open
      (closedTri_subset_cutOpen h n) hFψ_an
  have h_avoid := triBd_avoid_poles h n
  let termM (m : ℕ) (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * (res m / (z - (ω m : ℂ)))
  have h_pole_term : ∀ m ∈ Finset.range (n + 1),
      triIntegral (termM m) R mθ =
        (2 * (Real.pi : ℂ) * I * res m) * (-(ω m : ℂ)) ^ j * Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
    intro m hm
    let gm (z : ℂ) : ℂ := res m * (-z) ^ j * Complex.exp (-z * (u : ℂ))
    have hgm_an : AnalyticOnNhd ℂ gm univ :=
      (analyticOnNhd_const.mul (analyticOnNhd_id.neg.pow j)).mul
        ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)
    have hslope_an : AnalyticOnNhd ℂ (dslope gm (ω m : ℂ)) univ := by
      have hd : DifferentiableOn ℂ (dslope gm (ω m : ℂ)) univ :=
        (Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 (ω m : ℂ))).mpr
          hgm_an.differentiableOn
      exact hd.analyticOnNhd isOpen_univ
    have htri_slope : triIntegral (dslope gm (ω m : ℂ)) R mθ = 0 :=
      triIntegral_eq_zero_of_analyticOn hR_pos.le hm_pos.le isOpen_univ (subset_univ _) hslope_an
    have htri_inv : triIntegral (fun z => gm (ω m : ℂ) * (z - (ω m : ℂ))⁻¹) R mθ =
        gm (ω m : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [triIntegral_const_mul]
      congr 1
      exact triIntegral_inv_sub
        (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m)))
        (ω_lt_cutR h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
        hm_pos
    have h_slope_int : TriBdIntegrable (dslope gm (ω m : ℂ)) R mθ :=
      triBdIntegrable_of_continuousOn hR_pos.le hm_pos.le
        (hslope_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
        (hslope_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
        (hslope_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
    have h_inv_int : TriBdIntegrable (fun z => gm (ω m : ℂ) * (z - (ω m : ℂ))⁻¹) R mθ :=
      triBdIntegrable_of_continuousOn hR_pos.le hm_pos.le
        (Continuous.continuousOn (continuous_const.mul
          (Continuous.inv₀ (by fun_prop) fun x h0 => h_avoid.1 x m (sub_eq_zero.mp h0))))
        (Continuous.continuousOn (continuous_const.mul
          (Continuous.inv₀ (by fun_prop) fun y h0 => h_avoid.2.2 y m (sub_eq_zero.mp h0))))
        (Continuous.continuousOn (continuous_const.mul
          (Continuous.inv₀ (by fun_prop) fun x h0 => h_avoid.2.1 x m (sub_eq_zero.mp h0))))
    have h_decomp_pt : ∀ z : ℂ, z ≠ (ω m : ℂ) →
        termM m z = dslope gm (ω m : ℂ) z + gm (ω m : ℂ) * (z - (ω m : ℂ))⁻¹ := by
      intro z hz
      have hsub : z - (ω m : ℂ) ≠ 0 := sub_ne_zero.mpr hz
      rw [dslope_of_ne gm hz, slope_def_field]
      dsimp only [termM, gm]
      field_simp [hsub]
      ring
    have h_congr := triIntegral_congr
      (F := termM m)
      (G := fun z => dslope gm (ω m : ℂ) z + gm (ω m : ℂ) * (z - (ω m : ℂ))⁻¹)
      hR_pos.le hm_pos.le
      (fun x _ => h_decomp_pt ((x : ℂ) * (1 - I * (mθ : ℂ))) (by dsimp only [mθ]; exact h_avoid.1 x m))
      (fun y _ => h_decomp_pt ((R : ℂ) + (y : ℂ) * I) (by dsimp only [R]; exact h_avoid.2.2 y m))
      (fun x _ => h_decomp_pt ((x : ℂ) * (1 + I * (mθ : ℂ))) (by dsimp only [mθ]; exact h_avoid.2.1 x m))
    rw [h_congr, triIntegral_add h_slope_int h_inv_int, htri_slope, zero_add, htri_inv]
    dsimp only [gm]
    ring
  have h_Fψ_int : TriBdIntegrable Fψ R mθ :=
    triBdIntegrable_of_continuousOn hR_pos.le hm_pos.le
      (hFψ_an.continuousOn.comp (by fun_prop) fun x hx => by
        refine closedTri_subset_cutOpen h n ?_
        have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by
          push_cast; ring
        rw [heq]
        exact mem_closedTri_mul_one_add hR_pos.le hm_pos.le hx ⟨le_rfl, by linarith⟩)
      (hFψ_an.continuousOn.comp (by fun_prop) fun y hy => by
        refine closedTri_subset_cutOpen h n ?_
        refine ⟨by simp [hR_pos.le], by simp [R], ?_⟩
        rw [show -mθ * R = -(mθ * R) by ring] at hy
        simpa [R, mθ] using abs_le.mpr hy)
      (hFψ_an.continuousOn.comp (by fun_prop) fun x hx =>
        closedTri_subset_cutOpen h n (mem_closedTri_mul_one_add hR_pos.le hm_pos.le hx ⟨by linarith, le_rfl⟩))
  have h_term_int : ∀ m ∈ Finset.range (n + 1), TriBdIntegrable (termM m) R mθ := by
    intro m _
    refine triBdIntegrable_of_continuousOn hR_pos.le hm_pos.le
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div (by fun_prop) fun x h0 => h_avoid.1 x m (sub_eq_zero.mp h0))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div (by fun_prop) fun y h0 => h_avoid.2.2 y m (sub_eq_zero.mp h0))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div (by fun_prop) fun x h0 => h_avoid.2.1 x m (sub_eq_zero.mp h0))))
  have h_sum_int : TriBdIntegrable (fun z => ∑ m ∈ Finset.range (n + 1), termM m z) R mθ := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) *
          ∑ m ∈ Finset.range (n + 1), termM m ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
          ∑ m ∈ Finset.range (n + 1), fun x : ℝ =>
            (1 - I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]
      exact IntervalIntegrable.sum _ fun m hm => (h_term_int m hm).1
    · have heq : (fun y : ℝ => ∑ m ∈ Finset.range (n + 1), termM m ((R : ℂ) + (y : ℂ) * I)) =
          ∑ m ∈ Finset.range (n + 1), fun y : ℝ => termM m ((R : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]
      exact IntervalIntegrable.sum _ fun m hm => (h_term_int m hm).2.1
    · have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) *
          ∑ m ∈ Finset.range (n + 1), termM m ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
          ∑ m ∈ Finset.range (n + 1), fun x : ℝ =>
            (1 + I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]
      exact IntervalIntegrable.sum _ fun m hm => (h_term_int m hm).2.2
  have h_pt_eq : ∀ z : ℂ, z ∉ Pset →
      (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z =
        Fψ z + ∑ m ∈ Finset.range (n + 1), termM m z := by
    intro z hz
    dsimp only [Fψ, ψn, termM, Sn]
    rw [ite_eq_right_iff.mpr (fun hmem => absurd hmem hz), ← Finset.mul_sum]
    ring
  have h_not_Pset_minus : ∀ x : ℝ, (x : ℂ) * (1 - I * (mθ : ℂ)) ∉ Pset := by
    rintro x ⟨m, _, hm_eq⟩
    exact h_avoid.1 x m hm_eq.symm
  have h_not_Pset_plus : ∀ x : ℝ, (x : ℂ) * (1 + I * (mθ : ℂ)) ∉ Pset := by
    rintro x ⟨m, _, hm_eq⟩
    exact h_avoid.2.1 x m hm_eq.symm
  have h_not_Pset_vert : ∀ y : ℝ, (R : ℂ) + (y : ℂ) * I ∉ Pset := by
    rintro y ⟨m, _, hm_eq⟩
    exact h_avoid.2.2 y m hm_eq.symm
  have h_main_congr := triIntegral_congr
    (F := fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z)
    (G := fun z => Fψ z + ∑ m ∈ Finset.range (n + 1), termM m z)
    hR_pos.le hm_pos.le
    (fun x _ => h_pt_eq ((x : ℂ) * (1 - I * (mθ : ℂ))) (h_not_Pset_minus x))
    (fun y _ => h_pt_eq ((R : ℂ) + (y : ℂ) * I) (h_not_Pset_vert y))
    (fun x _ => h_pt_eq ((x : ℂ) * (1 + I * (mθ : ℂ))) (h_not_Pset_plus x))
  rw [h_main_congr, triIntegral_add h_Fψ_int h_sum_int, htri_ψ, zero_add,
    triIntegral_sum _ _ R mθ h_term_int]
  exact Finset.sum_congr rfl h_pole_term

private lemma exp_tail_bound {φ ω res} (h : MeromorphicBorelData φ ω res)
    {U : Set ℂ} {d : ℂ} (hd_norm : ‖d‖ = 1) (hd_re : d.re = Real.cos h.θ)
    (hExp : ExpType (Minor.pull d φ))
    (hGood : (aPhi φ).Good U d)
    (hRay : ContainsRay U d)
    (hDom : Domain U)
    (n j : ℕ) :
    ∃ K : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖∫ v in Ioi (cutR h n / Real.cos h.θ), d * ((-(d * (v : ℂ))) ^ j *
        Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))‖ ≤
        K * Real.exp (-cutR h n * u) := by
  obtain ⟨Cexp, Dexp, hCexp, hDexp, hexp_bd⟩ := hExp
  have hcos : 0 < Real.cos h.θ := cos_pos_θ h
  let v₀ : ℝ := cutR h n / Real.cos h.θ
  have hv₀_pos : 0 < v₀ := div_pos (cutR_pos h n) hcos
  have h_base_int : IntegrableOn (fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (show -(1 / 4 : ℝ) < 0 by norm_num) 0).const_mul
      ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j)).mono'
      ((by fun_prop : Continuous fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le)]
    have hpow := Real.pow_div_factorial_le_exp ((1 / 4 : ℝ) * v) (by positivity) j
    have h1 : 0 < (1 / 4 : ℝ) ^ j := by positivity
    have h2 : 0 < (j.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvj : v ^ j ≤ ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v) := by
      calc v ^ j ≤ (Real.exp ((1 / 4 : ℝ) * v) * j.factorial) / (1 / 4 : ℝ) ^ j :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v) := by ring
    calc v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
        ≤ (((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v)) *
            Real.exp (-(1 / 2 : ℝ) * v) := mul_le_mul_of_nonneg_right hvj (Real.exp_pos _).le
      _ = ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp (-(1 / 4 : ℝ) * v) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  let Ij : ℝ := ∫ v in Ioi (0 : ℝ), v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
  have hIj_nonneg : 0 ≤ Ij :=
    setIntegral_nonneg measurableSet_Ioi fun v hv =>
      mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le
  let K : ℝ := Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Ij
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have hej_good : (ej.residual (aPhi φ)).Good _ d := (ej.represents hDom hRay hGood).1
  have hej_int := (tendsto_coe_far (by rw [hd_re]; exact hcos)).eventually (hej_good.integrable hRay)
  refine ⟨K, ?_⟩
  filter_upwards [hej_int, eventually_ge_atTop ((Dexp + 1) / Real.cos h.θ)] with u hu_int hu_ge
  have hu_re : Dexp + 1 ≤ u * Real.cos h.θ := (div_le_iff₀ hcos).mp hu_ge
  have hu_pos : 0 < u := by
    have : 0 < Dexp + 1 := by linarith
    nlinarith
  let Ftail (v : ℝ) : ℂ := d * ((-(d * (v : ℂ))) ^ j *
    Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))
  have h_eq_damped : ∀ v : ℝ,
      damped ((u : ℂ) * d) (Minor.pull d (ej.residual (aPhi φ)).density) v = Ftail v := by
    intro v
    rw [damped, Minor.pull, jet_residual_density φ j]
    have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
    rw [hexp]
    dsimp only [Ftail]
    ring
  have hF_int_Ioi0 : IntegrableOn Ftail (Ioi 0) :=
    hu_int.congr_fun (fun v _ => h_eq_damped v) measurableSet_Ioi
  have hF_int_tail : IntegrableOn Ftail (Ioi v₀) :=
    hF_int_Ioi0.mono_set (Ioi_subset_Ioi hv₀_pos.le)
  let bnd (v : ℝ) : ℝ :=
    (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutR h n * u)) *
      (v ^ j * Real.exp (-(1 / 2 : ℝ) * v))
  have hbnd_int : IntegrableOn bnd (Ioi 0) :=
    h_base_int.const_mul (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutR h n * u))
  have h_pt_le : ∀ v ∈ Ioi v₀, ‖Ftail v‖ ≤ bnd v := by
    intro v hv
    change v₀ < v at hv
    have hv0 : 0 ≤ v := le_trans hv₀_pos.le hv.le
    have hF_rew : Ftail v = (-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) *
        Minor.pull d φ v := by
      dsimp only [Ftail, Minor.pull]; ring
    rw [hF_rew, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, hd_norm, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
    have hexp_re : (-(d * (v : ℂ)) * (u : ℂ)).re = -(u * Real.cos h.θ) * v := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, hd_re]
      ring
    rw [Complex.norm_exp, hexp_re]
    have hpull := hexp_bd v hv0
    have h_exp_split : Real.exp (-(u * Real.cos h.θ) * v) * (Cexp * Real.exp (Dexp * v)) =
        Cexp * Real.exp (-(u * Real.cos h.θ - Dexp) * v) := by
      rw [mul_left_comm _ Cexp, ← Real.exp_add]; congr 2; ring
    have h_exp_le : Real.exp (-(u * Real.cos h.θ - Dexp) * v) ≤
        Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutR h n * u) * Real.exp (-(1 / 2 : ℝ) * v) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h_rem_pos : 0 ≤ u * Real.cos h.θ - Dexp - 1 / 2 := by linarith
      have h_v0_mul : (u * Real.cos h.θ - Dexp - 1 / 2) * v₀ ≤
          (u * Real.cos h.θ - Dexp - 1 / 2) * v :=
        mul_le_mul_of_nonneg_left hv.le h_rem_pos
      have hv₀_eq : Real.cos h.θ * v₀ = cutR h n := by
        dsimp only [v₀]
        field_simp [hcos.ne']
      nlinarith [hv₀_eq]
    calc v ^ j * Real.exp (-(u * Real.cos h.θ) * v) * ‖Minor.pull d φ v‖
        ≤ v ^ j * Real.exp (-(u * Real.cos h.θ) * v) * (Cexp * Real.exp (Dexp * v)) :=
          mul_le_mul_of_nonneg_left hpull (by positivity)
      _ = Cexp * (v ^ j * Real.exp (-(u * Real.cos h.θ - Dexp) * v)) := by
          rw [mul_assoc, h_exp_split]; ring
      _ ≤ Cexp * (v ^ j * (Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutR h n * u) *
            Real.exp (-(1 / 2 : ℝ) * v))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_exp_le (pow_nonneg hv0 _)) hCexp
      _ = bnd v := by dsimp only [bnd]; ring
  calc ‖∫ v in Ioi v₀, Ftail v‖
      ≤ ∫ v in Ioi v₀, ‖Ftail v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi v₀, bnd v :=
        setIntegral_mono_on hF_int_tail.norm (hbnd_int.mono_set (Ioi_subset_Ioi hv₀_pos.le))
          measurableSet_Ioi h_pt_le
    _ ≤ ∫ v in Ioi 0, bnd v :=
        setIntegral_mono_set hbnd_int
          ((ae_restrict_mem measurableSet_Ioi).mono fun v (hv : 0 < v) => by
            dsimp only [bnd]
            exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le))
          (Eventually.of_forall fun _ hx => Ioi_subset_Ioi hv₀_pos.le hx)
    _ = K * Real.exp (-cutR h n * u) := by
        dsimp only [bnd, K, Ij]
        rw [integral_const_mul]
        ring

private lemma stokes_jump_expansion_meromorphic {φ ω res} (h : MeromorphicBorelData φ ω res)
    (n j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ) -
          (aPhi φ).value (dPlusG h) (t : ℂ)) u -
        ∑ m ∈ Finset.range (n + 1), (2 * (Real.pi : ℂ) * I * res m) * (-(ω m : ℂ)) ^ j *
          Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
        C * Real.exp (-cutR h n * u) := by
  let R : ℝ := cutR h n
  let mθ : ℝ := Real.tan h.θ
  let v₀ : ℝ := R / Real.cos h.θ
  have hR_pos : 0 < R := cutR_pos h n
  have hcos : 0 < Real.cos h.θ := cos_pos_θ h
  have hm_pos : 0 < mθ := tan_pos_of_mem h.hθ_pos (h.hθ_lt.trans h.hθ₀_lt)
  have hv₀_pos : 0 < v₀ := div_pos hR_pos hcos
  have hreP : 0 < (dPlusG h).re := by rw [dPlusG_re h]; exact hcos
  have hreM : 0 < (dMinusG h).re := by rw [dMinusG_re h]; exact hcos
  let Up := wedgePlus h.θ₀ (ε₀ h)
  let Um := wedgeMinus h.θ₀ (ε₀ h)
  have hUp_dom := wedgePlus_domain h.θ₀ (ε₀_pos h)
  have hUm_dom := wedgeMinus_domain h.θ₀ (ε₀_pos h)
  have hrayP := wedgePlus_containsRay h
  have hrayM := wedgeMinus_containsRay h
  have hgoodP := aPhi_good_plus h
  have hgoodM := aPhi_good_minus h
  have h_sub_deriv : ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ) -
          (aPhi φ).value (dPlusG h) (t : ℂ)) u =
        iteratedDeriv j (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ)) u -
          iteratedDeriv j (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ)) u :=
    eventually_iteratedDeriv_sub
      (fun i _ => (lateral_eventually_differentiable h i).2)
      (fun i _ => (lateral_eventually_differentiable h i).1)
  have h_lapP := iteratedDeriv_lateral_eq_laplace h hUp_dom hrayP hgoodP hreP j
  have h_lapM := iteratedDeriv_lateral_eq_laplace h hUm_dom hrayM hgoodM hreM j
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have h_intP := (tendsto_coe_far hreP).eventually
    ((ej.represents hUp_dom hrayP hgoodP).1.integrable hrayP)
  have h_intM := (tendsto_coe_far hreM).eventually
    ((ej.represents hUm_dom hrayM hgoodM).1.integrable hrayM)
  have hne_dm : dMinusG h ≠ dPlusG h := by
    intro heq
    have him := congrArg Complex.im heq
    rw [dMinusG_im h, dPlusG_im h] at him
    linarith [sin_pos_θ h]
  obtain ⟨Km, hKm⟩ := exp_tail_bound h (norm_dMinusG h) (dMinusG_re h) h.expType_minus
    hgoodM hrayM hUm_dom n j
  obtain ⟨Kp, hKp⟩ := exp_tail_bound h (norm_dPlusG h) (dPlusG_re h) h.expType_plus
    hgoodP hrayP hUp_dom n j
  -- Vertical edge bound on `φ (R + I * y)` for `y ∈ [-mθ * R, mθ * R]`
  have h_vert_sub : ∀ y ∈ Icc (-mθ * R) (mθ * R), (R : ℂ) + (y : ℂ) * I ∈ puncturedWedge h.θ₀ h.ε ω := by
    intro y hy
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add]
      rw [show -mθ * R = -(mθ * R) by ring] at hy
      have hy_abs : |y| ≤ mθ * R := abs_le.mpr hy
      have htan := tan_lt_tan h
      exact ⟨hR_pos, lt_of_le_of_lt hy_abs (mul_lt_mul_of_pos_right htan hR_pos)⟩
    · rintro ⟨m, hm_eq⟩
      exact (triBd_avoid_poles h n).2.2 y m hm_eq.symm
  have hφ_vert_cont : ContinuousOn (fun y : ℝ => φ ((R : ℂ) + (y : ℂ) * I)) (Icc (-mθ * R) (mθ * R)) :=
    h.analyticOn.continuousOn.comp (by fun_prop) h_vert_sub
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ_vert_cont
  let Kv : ℝ := (2 * mθ * R) * ((R / Real.cos h.θ) ^ j * max Mφ 0)
  have h_vert_bd : ∀ u : ℝ,
      ‖I * (∫ y : ℝ in (-mθ * R)..(mθ * R),
        (-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I))‖ ≤ Kv * Real.exp (-R * u) := by
    intro u
    rw [norm_mul, Complex.norm_I, one_mul]
    have hpt : ∀ y ∈ uIoc (-mθ * R) (mθ * R),
        ‖(-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I)‖ ≤
          ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by
      intro y hy
      rw [uIoc_of_le (by nlinarith : -mθ * R ≤ mθ * R)] at hy
      have hy_cc : y ∈ Icc (-mθ * R) (mθ * R) := ⟨hy.1.le, hy.2⟩
      have hnorm_z : ‖-((R : ℂ) + (y : ℂ) * I)‖ ≤ R / Real.cos h.θ := by
        rw [norm_neg, Complex.norm_def]
        have hy_sq : y ^ 2 ≤ mθ ^ 2 * R ^ 2 := by
          have hy_cc' : y ∈ Icc (-(mθ * R)) (mθ * R) := by
            simpa [neg_mul] using hy_cc
          have : |y| ≤ mθ * R := abs_le.mpr hy_cc'
          have h1 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
          rw [h1]
          calc |y| ^ 2 ≤ (mθ * R) ^ 2 := sq_le_sq' (by linarith [abs_nonneg y]) this
            _ = mθ ^ 2 * R ^ 2 := by ring
        have hnsq : Complex.normSq ((R : ℂ) + (y : ℂ) * I) ≤ (R / Real.cos h.θ) ^ 2 := by
          rw [Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
            mul_one, zero_add]
          have hsec : 1 + mθ ^ 2 = (Real.cos h.θ) ^ (-2 : ℤ) := by
            dsimp only [mθ]
            rw [Real.tan_eq_sin_div_cos, zpow_neg, zpow_two]
            have hc := hcos.ne'
            have hid := Real.sin_sq_add_cos_sq h.θ
            field_simp [hc]
            linarith
          calc R * R + y * y = R ^ 2 + y ^ 2 := by ring
            _ ≤ R ^ 2 + mθ ^ 2 * R ^ 2 := by linarith
            _ = R ^ 2 * (1 + mθ ^ 2) := by ring
            _ = R ^ 2 * (Real.cos h.θ) ^ (-2 : ℤ) := by rw [hsec]
            _ = (R / Real.cos h.θ) ^ 2 := by rw [zpow_neg, zpow_two, div_pow]; ring
        exact Real.sqrt_le_iff.mpr ⟨div_nonneg hR_pos.le hcos.le, hnsq⟩
      have hexp_norm : ‖Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ))‖ = Real.exp (-R * u) := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
      have hφ_le : ‖φ ((R : ℂ) + (y : ℂ) * I)‖ ≤ max Mφ 0 :=
        (hMφ y hy_cc).trans (le_max_left _ _)
      rw [norm_mul, norm_mul, norm_pow, hexp_norm]
      calc ‖-((R : ℂ) + (y : ℂ) * I)‖ ^ j * Real.exp (-R * u) * ‖φ ((R : ℂ) + (y : ℂ) * I)‖
          ≤ (R / Real.cos h.θ) ^ j * Real.exp (-R * u) * max Mφ 0 := by
            gcongr
        _ = ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    calc ‖∫ y : ℝ in (-mθ * R)..(mθ * R), _‖
        ≤ ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) * |mθ * R - -mθ * R| := hle
      _ = Kv * Real.exp (-R * u) := by
          have habs : |mθ * R - -mθ * R| = 2 * mθ * R := by
            rw [show mθ * R - -mθ * R = 2 * mθ * R by ring, abs_of_pos (by positivity)]
          rw [habs]
          dsimp only [Kv]
          ring
  refine ⟨Kv + Km + Kp, ?_⟩
  filter_upwards [h_sub_deriv, h_lapP, h_lapM, h_intP, h_intM, hKp, hKm] with
    u hsub hlp hlm hip him hkp_bd hkm_bd
  let Fkern (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z
  have heq_p : ∀ v : ℝ, damped ((u : ℂ) * dPlusG h) (Minor.pull (dPlusG h) (ej.residual (aPhi φ)).density) v =
      dPlusG h * Fkern (dPlusG h * (v : ℂ)) := by
    intro v
    rw [damped, Minor.pull, jet_residual_density φ j]
    have hexp : -((u : ℂ) * dPlusG h) * (v : ℂ) = -(dPlusG h * (v : ℂ)) * (u : ℂ) := by ring
    rw [hexp]
    dsimp only [Fkern]
    ring
  have heq_m : ∀ v : ℝ, damped ((u : ℂ) * dMinusG h) (Minor.pull (dMinusG h) (ej.residual (aPhi φ)).density) v =
      dMinusG h * Fkern (dMinusG h * (v : ℂ)) := by
    intro v
    rw [damped, Minor.pull, jet_residual_density φ j]
    have hexp : -((u : ℂ) * dMinusG h) * (v : ℂ) = -(dMinusG h * (v : ℂ)) * (u : ℂ) := by ring
    rw [hexp]
    dsimp only [Fkern]
    ring
  have hintP_Ioi : IntegrableOn (fun v : ℝ => dPlusG h * Fkern (dPlusG h * (v : ℂ))) (Ioi 0) :=
    hip.congr_fun (fun v _ => heq_p v) measurableSet_Ioi
  have hintM_Ioi : IntegrableOn (fun v : ℝ => dMinusG h * Fkern (dMinusG h * (v : ℂ))) (Ioi 0) :=
    him.congr_fun (fun v _ => heq_m v) measurableSet_Ioi
  have hsplitP : (∫ v in (0 : ℝ)..v₀, dPlusG h * Fkern (dPlusG h * (v : ℂ))) +
      (∫ v in Ioi v₀, dPlusG h * Fkern (dPlusG h * (v : ℂ))) =
      ∫ v in Ioi (0 : ℝ), dPlusG h * Fkern (dPlusG h * (v : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintP_Ioi (hintP_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hsplitM : (∫ v in (0 : ℝ)..v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ))) +
      (∫ v in Ioi v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ))) =
      ∫ v in Ioi (0 : ℝ), dMinusG h * Fkern (dMinusG h * (v : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintM_Ioi (hintM_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hcovP : ∫ v in (0 : ℝ)..v₀, dPlusG h * Fkern (dPlusG h * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dPlusG h * Fkern (dPlusG h * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 + I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dPlusG h := by
      rw [dPlusG_eq h]
      dsimp only [mθ]
      rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have harg_eq : ∀ x : ℝ, (x : ℂ) * (1 + I * (mθ : ℂ)) = dPlusG h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
      intro x
      rw [hmul_eq]
      push_cast
      ring
    have heq_int : (fun x : ℝ => (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dPlusG h * Fkern (dPlusG h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      rw [harg_eq x, Complex.real_smul, hmul_eq]
      push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have hcovM : ∫ v in (0 : ℝ)..v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dMinusG h * Fkern (dMinusG h * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 - I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dMinusG h := by
      rw [dMinusG_eq h]
      dsimp only [mθ]
      rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have harg_eq : ∀ x : ℝ, (x : ℂ) * (1 - I * (mθ : ℂ)) = dMinusG h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
      intro x
      rw [hmul_eq]
      push_cast
      ring
    have heq_int : (fun x : ℝ => (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dMinusG h * Fkern (dMinusG h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      rw [harg_eq x, Complex.real_smul, hmul_eq]
      push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have htri := triIntegral_φ_kernel h n j u
  have h_id : iteratedDeriv j (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ) -
        (aPhi φ).value (dPlusG h) (t : ℂ)) u -
      ∑ m ∈ Finset.range (n + 1), (2 * (Real.pi : ℂ) * I * res m) * (-(ω m : ℂ)) ^ j *
        Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
      -(I * (∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))) +
        (∫ v in Ioi v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ))) -
        (∫ v in Ioi v₀, dPlusG h * Fkern (dPlusG h * (v : ℂ))) := by
    rw [hsub, hlm, hlp, ← htri]
    change (∫ v in Ioi (0 : ℝ), dMinusG h * Fkern (dMinusG h * (v : ℂ))) -
        (∫ v in Ioi (0 : ℝ), dPlusG h * Fkern (dPlusG h * (v : ℂ))) -
        triIntegral Fkern R mθ = _
    rw [← hsplitM, ← hsplitP, hcovM, hcovP]
    unfold triIntegral
    ring
  rw [h_id]
  have hv_le := h_vert_bd u
  calc ‖-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)) +
          (∫ v in Ioi v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ))) -
          (∫ v in Ioi v₀, dPlusG h * Fkern (dPlusG h * (v : ℂ)))‖
      ≤ ‖-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))‖ +
          ‖∫ v in Ioi v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ))‖ +
          ‖∫ v in Ioi v₀, dPlusG h * Fkern (dPlusG h * (v : ℂ))‖ := by
        linarith [norm_sub_le (-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)) +
            (∫ v in Ioi v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ))))
            (∫ v in Ioi v₀, dPlusG h * Fkern (dPlusG h * (v : ℂ))),
          norm_add_le (-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)))
            (∫ v in Ioi v₀, dMinusG h * Fkern (dMinusG h * (v : ℂ)))]
    _ ≤ Kv * Real.exp (-R * u) + Km * Real.exp (-R * u) + Kp * Real.exp (-R * u) := by
        rw [norm_neg]
        exact add_le_add (add_le_add hv_le hkm_bd) hkp_bd
    _ = (Kv + Km + Kp) * Real.exp (-cutR h n * u) := by ring

/-! ### 5. End-to-End General Theorem 2 -/

/-- **General Theorem 2 (End-to-End Meromorphic Borel–Stokes–Vandermonde Differential Transcendence)**:
Given ANY Borel transform `φ : ℂ → ℂ` analytic on an open punctured wedge containing `[0, ∞)`
with simple poles at `0 < ω 0 < ω 1 < ...`, nonzero residues `res m ≠ 0`, and exponential type
along two tilted rays `exp (±i θ)`, its formal Laplace series `∑_{k ≥ 0} φ^{(k)}(0) u^{-k-1}`
satisfies NO nonzero autonomous polynomial differential equation over `ℂ`. -/
theorem borel_stokes_vandermonde_no_autonomous_ade
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {res : ℕ → ℂ}
    (h : MeromorphicBorelData φ ω res)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval (formalSeries φ) P = 0) : P = 0 := by
  classical
  by_contra hP_ne
  have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q.totalDegree = d ∧ Q ≠ 0 ∧ formalEval (formalSeries φ) Q = 0 :=
    ⟨P.totalDegree, P, rfl, hP_ne, hP⟩
  let Pmin := Classical.choose (Nat.find_spec hex)
  have hPmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hPmin_deg : Pmin.totalDegree = Nat.find hex := hPmin_spec.1
  have hPmin_ne : Pmin ≠ 0 := hPmin_spec.2.1
  have hPmin_zero : formalEval (formalSeries φ) Pmin = 0 := hPmin_spec.2.2
  have hPmin_min : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 → Q.totalDegree < Pmin.totalDegree → ¬ formalEval (formalSeries φ) Q = 0 := by
    intro Q hQ_ne hQ_deg hQ_zero
    rw [hPmin_deg] at hQ_deg
    exact Nat.find_min hex hQ_deg ⟨Q, rfl, hQ_ne, hQ_zero⟩
  have hPmin_const : MvPolynomial.eval 0 Pmin = 0 := by
    rw [← coeff_zero_formalEval_series, hPmin_zero, map_zero]
  let gapMin : ℝ := (Finset.range (r + 1)).inf'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r)) (fun n => (ω (n + 1) - ω n) / 2)
  let δ₀ : ℝ := min (ω 0) gapMin
  have hgap_pos : 0 < gapMin := by
    rw [Finset.lt_inf'_iff]
    intro n _
    have hlt : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
    linarith
  have hδ₀_pos : 0 < δ₀ := lt_min h.ω_pos hgap_pos
  have hω_low : ∀ m : ℕ, δ₀ ≤ ω m := fun m =>
    (min_le_left (ω 0) gapMin).trans (h.ω_mono.monotone (Nat.zero_le m))
  have hδ_le_cut : ∀ n : ℕ, n < r + 1 → ω n + δ₀ ≤ cutR h n := by
    intro n hn
    have h1 : δ₀ ≤ gapMin := min_le_right _ _
    have h2 : gapMin ≤ (ω (n + 1) - ω n) / 2 :=
      Finset.inf'_le (fun k => (ω (k + 1) - ω k) / 2) (Finset.mem_range.mpr hn)
    dsimp only [cutR]
    linarith
  let c : ℕ → ℂ := fun m => 2 * (Real.pi : ℂ) * I * res m
  have hc_ne : ∀ m : ℕ, m < r + 1 → c m ≠ 0 := by
    intro m _
    dsimp only [c]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) (h.res_ne_zero m)
  obtain ⟨hpos, hneg⟩ := formalEval_zero_implies_lateral_zero h Pmin hPmin_zero
  have h_exp : ∀ (n : ℕ) (j : Fin (r + 1)), n < r + 1 →
      ∃ C : ℝ, ∀ᶠ u in atTop,
        ‖iteratedDeriv j.val (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ) -
            (aPhi φ).value (dPlusG h) (t : ℂ)) u -
          ∑ m ∈ Finset.range (n + 1), c m * (-(ω m : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
          C * Real.exp (-(ω n + δ₀) * u) := by
    intro n j hn
    obtain ⟨C, hC⟩ := stokes_jump_expansion_meromorphic h n j.val
    refine ⟨max C 0, ?_⟩
    filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with u hu hu0
    have h_exp_mono : Real.exp (-cutR h n * u) ≤ Real.exp (-(ω n + δ₀) * u) := by
      rw [Real.exp_le_exp]
      nlinarith [hδ_le_cut n hn, hu0]
    calc _ ≤ C * Real.exp (-cutR h n * u) := hu
      _ ≤ max C 0 * Real.exp (-cutR h n * u) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (-(ω n + δ₀) * u) :=
          mul_le_mul_of_nonneg_left h_exp_mono (le_max_right C 0)
  have h0 : Pmin = 0 := stokes_vandermonde_general_eq_zero
    (fun Q => formalEval (formalSeries φ) Q = 0) Pmin hPmin_min hPmin_const
    ω δ₀ hδ₀_pos hω_low h.ω_mono c hc_ne
    (fun t : ℝ => (aPhi φ).value (dPlusG h) (t : ℂ))
    (fun t : ℝ => (aPhi φ).value (dMinusG h) (t : ℂ))
    (fun k _ => lateral_eventually_differentiable h k)
    hpos hneg (fun j => lateral_bounded_derivatives h j.val)
    h_exp
    (fun Q hQ => eval_lateral_flat_implies_formalEval_zero h hδ₀_pos Q hQ)
  exact hPmin_ne h0

/-- **Asymptotic-Transfer General Theorem 2**:
Any function `f : ℝ → ℂ` whose derivatives share the all-orders `1/u` asymptotic expansion
`d_u^[j] (formalSeries φ)` satisfies NO nonzero autonomous polynomial differential equation over `ℂ`. -/
theorem no_autonomous_ade_of_meromorphic_borel
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {res : ℕ → ℂ}
    (h : MeromorphicBorelData φ ω res)
    {f : ℝ → ℂ}
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] (formalSeries φ)))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P = 0) :
    P = 0 := by
  have hexp : HasAsympExp
      (fun u => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P)
      (formalEval (formalSeries φ) P) :=
    HasAsympExp.mvPolynomial (fun j => hf_asymp j.val) P
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in Filter.atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P‖ ≤ C / u ^ M := by
    intro M
    refine ⟨0, ?_⟩
    filter_upwards [hP] with u hu
    simp [hu]
  exact borel_stokes_vandermonde_no_autonomous_ade h P (hexp.eq_zero_of_flat hflat)

/-! ### 6. Non-Vacuity Sanity Check: Instantiation on `φ(ξ) = Γ(1 - ξ)` -/

/-- Exact simple-pole residue of `φ(ξ) = Γ(1 - ξ)` at `ξ = m + 1`: `(-1)^{m + 1} / m!`. -/
@[expose] def gammaRes (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ (m + 1) / (m.factorial : ℂ)

private lemma prod_range_sub_succ (m : ℕ) :
    ∏ j ∈ Finset.range m, ((j + 1 : ℂ) - ((m + 1 : ℕ) : ℂ)) =
      (-1 : ℂ) ^ m * (m.factorial : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmem : ∀ j ∈ Finset.range (m + 1),
        ((j + 1 : ℂ) - ((m + 1 + 1 : ℕ) : ℂ)) = -(((m + 1 - j : ℕ) : ℂ)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have : m + 1 + 1 = (m + 1 - j) + (j + 1) := by omega
      push_cast [this]
      ring
    trans ∏ j ∈ Finset.range (m + 1), -(((m + 1 - j : ℕ) : ℂ))
    · exact Finset.prod_congr rfl fun j hj => by simpa using hmem j hj
    · rw [Finset.prod_neg, Finset.card_range]
      congr 1
      have hreflect := Finset.prod_range_reflect (fun k : ℕ => ((k + 1 : ℕ) : ℂ)) (m + 1)
      have hcongr : ∏ j ∈ Finset.range (m + 1), (((m + 1 - j : ℕ) : ℂ)) =
          ∏ j ∈ Finset.range (m + 1), (((m + 1 - 1 - j + 1 : ℕ) : ℂ)) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        congr 1; omega
      rw [hcongr, hreflect]
      clear hcongr hreflect hmem ih
      induction (m + 1) with
      | zero => simp
      | succ k ihk =>
        rw [Finset.prod_range_succ, ihk, Nat.factorial_succ]
        push_cast; ring

/-- Genuine `MeromorphicBorelData` witness for `φ(ξ) = Γ(1 - ξ)` with `ω m = m + 1`
and `res m = (-1)^(m + 1) / m!`. -/
@[expose] def gammaBorelData :
    MeromorphicBorelData phi (fun m : ℕ => (m + 1 : ℝ)) gammaRes where
  θ₀ := Real.pi / 3
  θ := theta4
  ε := 1 / 2
  hθ_pos := theta4_pos
  hθ_lt := by unfold theta4; linarith [Real.pi_pos]
  hθ₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by norm_num
  ω_mono := fun a b hab => by dsimp only; exact_mod_cast Nat.succ_lt_succ hab
  res_ne_zero := fun m => by
    unfold gammaRes
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero m)
  analyticOn := fun z hz => by
    refine phi_analyticAt_of_avoids_posNat fun n hn heq => ?_
    apply hz.2
    refine ⟨n - 1, ?_⟩
    have h1 : (((n - 1 : ℕ) + 1 : ℝ) : ℂ) = (n : ℂ) := by
      exact_mod_cast (show (n - 1) + 1 = n by omega)
    simpa [heq] using h1
  simple_pole := fun m => by
    have hball : Metric.ball ((m + 1 : ℝ) : ℂ) (1 / 2) \ {((m + 1 : ℝ) : ℂ)} ∈
        𝓝[≠] ((m + 1 : ℝ) : ℂ) := by
      rw [Set.sdiff_eq, Set.inter_comm]
      exact inter_mem_nhdsWithin _
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
    let rhs (z : ℂ) : ℂ :=
      -Complex.Gamma ((m + 2 : ℂ) - z) / ∏ j ∈ Finset.range m, ((j + 1 : ℂ) - z)
    have h_eq : ∀ᶠ z in 𝓝[≠] ((m + 1 : ℝ) : ℂ),
        (z - ((m + 1 : ℝ) : ℂ)) * phi z = rhs z := by
      filter_upwards [hball] with z ⟨hz_ball, hz_ne⟩
      have h_avoid : ∀ n : ℕ, 1 ≤ n → z ≠ (n : ℂ) := by
        intro n hn hzn
        rcases eq_or_ne n (m + 1) with rfl | hne
        · exact hz_ne (by simpa using hzn)
        · have hdist_n : (1 : ℝ) ≤ ‖((n : ℂ) - ((m + 1 : ℝ) : ℂ))‖ := by
            have hdiff_nat : (1 : ℤ) ≤ |((n : ℤ) - (m + 1 : ℤ))| := by
              have : (n : ℤ) - (m + 1 : ℤ) ≠ 0 := by omega
              exact Int.one_le_abs this
            have hcast : ((n : ℂ) - ((m + 1 : ℝ) : ℂ)) = (((((n : ℤ) - (m + 1 : ℤ)) : ℤ) : ℝ) : ℂ) := by
              push_cast; ring
            rw [hcast, Complex.norm_real, Real.norm_eq_abs]
            exact_mod_cast hdiff_nat
          rw [Metric.mem_ball, dist_eq_norm, hzn] at hz_ball
          linarith
      have hfall := Gamma_one_sub_mul_falling m h_avoid
      rw [Finset.prod_range_succ] at hfall
      have hz_sub : ((m + 1 : ℝ) : ℂ) - z ≠ 0 := by
        intro h0
        exact hz_ne (Set.mem_singleton_iff.mpr (by linear_combination -h0))
      have hden_ne : (∏ j ∈ Finset.range m, ((j + 1 : ℂ) - z)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j _ h0
        exact h_avoid (j + 1) (by omega) (by push_cast; linear_combination -h0)
      have hphi_eq : phi z = rhs z / (z - ((m + 1 : ℝ) : ℂ)) := by
        dsimp only [phi, rhs]
        have hm_eq : (m : ℂ) + 1 - z = -(z - ((m + 1 : ℝ) : ℂ)) := by push_cast; ring
        have hz_sub' : z - ((m + 1 : ℝ) : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne
        rw [hm_eq] at hfall
        field_simp [hden_ne, hz_sub']
        linear_combination -hfall
      rw [hphi_eq, mul_div_cancel₀ _ (sub_ne_zero.mpr hz_ne)]
    have h_gam_diff : DifferentiableAt ℂ Complex.Gamma ((m + 2 : ℂ) - ((m + 1 : ℝ) : ℂ)) := by
      refine Complex.differentiableAt_Gamma _ fun k hk => ?_
      have : (m + 2 : ℂ) - ((m + 1 : ℝ) : ℂ) = 1 := by push_cast; ring
      rw [this] at hk
      have hre := congrArg Complex.re hk
      simp at hre
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h_prod_ne : (∏ j ∈ Finset.range m, ((j + 1 : ℂ) - ((m + 1 : ℝ) : ℂ))) ≠ 0 := by
      have hcast : ((m + 1 : ℝ) : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast, prod_range_sub_succ m]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero m)
    have h_prod_cont : ∀ s : Finset ℕ, ContinuousAt (fun z : ℂ => ∏ j ∈ s, ((j + 1 : ℂ) - z))
        ((m + 1 : ℝ) : ℂ) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using continuousAt_const
      | @insert j s hj ih =>
        have heq : (fun z : ℂ => ∏ k ∈ insert j s, ((k + 1 : ℂ) - z)) =
            fun z => ((j + 1 : ℂ) - z) * ∏ k ∈ s, ((k + 1 : ℂ) - z) := by
          funext z; rw [Finset.prod_insert hj]
        rw [heq]
        exact (continuousAt_const.sub continuousAt_id).mul ih
    have h_rhs_cont : ContinuousAt rhs ((m + 1 : ℝ) : ℂ) := by
      refine ContinuousAt.div ?_ (h_prod_cont (Finset.range m)) h_prod_ne
      exact (h_gam_diff.continuousAt.comp (continuousAt_const.sub continuousAt_id)).neg
    have h_rhs_val : rhs ((m + 1 : ℝ) : ℂ) = gammaRes m := by
      dsimp only [rhs, gammaRes]
      have h1 : (m + 2 : ℂ) - ((m + 1 : ℝ) : ℂ) = 1 := by push_cast; ring
      have hcast : ((m + 1 : ℝ) : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h1, Complex.Gamma_one, hcast, prod_range_sub_succ m]
      have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hpow_ne : (-1 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
      have hpow2 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      have hnum : (-1 : ℂ) ^ m * (-1 : ℂ) ^ (m + 1) = -1 := by
        rw [pow_succ, ← mul_assoc, hpow2, one_mul]
      calc -1 / ((-1 : ℂ) ^ m * (m.factorial : ℂ))
          = ((-1 : ℂ) ^ m * (-1 : ℂ) ^ (m + 1)) / ((-1 : ℂ) ^ m * (m.factorial : ℂ)) := by
            rw [hnum]
        _ = (-1 : ℂ) ^ (m + 1) / (m.factorial : ℂ) := by
            rw [mul_div_mul_left _ _ hpow_ne]
    have htend : Tendsto rhs (𝓝[≠] ((m + 1 : ℝ) : ℂ)) (𝓝 (gammaRes m)) := by
      rw [← h_rhs_val]
      exact h_rhs_cont.continuousWithinAt.tendsto
    exact htend.congr' (EventuallyEq.symm h_eq)
  expType_plus := by
    simpa [dPlus, aGamma] using aGamma_good_UPlus.2
  expType_minus := by
    simpa [dMinus, aGamma] using aGamma_good_UMinus.2

/-- **Non-Vacuity Instantiation**: recovers `gHat_no_autonomous_ade` directly from General Theorem 2
applied to `φ(ξ) = Γ(1 - ξ)`. -/
theorem gHat_no_autonomous_ade_via_general_theorem_2 {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval gHat P = 0) : P = 0 := by
  have hg : formalSeries phi = gHat := by
    ext n
    cases n <;> simp [formalSeries, gHat]
  rw [← hg] at hP
  exact borel_stokes_vandermonde_no_autonomous_ade gammaBorelData P hP

end
end PakPrimes.GeneralTheorem2
