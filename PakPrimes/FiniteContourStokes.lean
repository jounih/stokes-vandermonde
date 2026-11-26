module

public import PakPrimes.HigherOrderStrongDTrans
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Vandermonde

/-! # Finite-Contour Simple-Pole Transfer Engine over `ℂ({t})`

This module formalizes the **4-lemma Finite-Contour Simple-Pole Transfer Engine** (scalar and
multi-series joint versions) for single-valued plane-meromorphic Borel minors with simple poles,
with **ZERO growth assumption at `∞`**, **ZERO global wedge assumption**, and **ZERO single-ray
collinearity assumption**:

1. **Section 1 — Truncated Laplace Transform & Simplex Splitting (Lemma 1)**:
   For `z ∈ ℂ` with `0 < z.re` and `u > 0`, defines the straight-segment truncated Laplace transform
   `truncLaplace F z u := z * ∫ t in (0 : ℝ)..1, exp (-u * z * t) * F (t * z)` and `truncVal a z u`.
   Proves the exact binary simplex splitting bound:
   `‖truncLaplace F z u * truncLaplace G z u - truncLaplace (complexConvolution F G) z u‖ ≤ (‖z‖^2 * MF * MG / 2) * exp (-z.re * u)`.
2. **Section 2 — Convergent Coefficients, Polynomial Transfer & Truncated Watson Expansion (Lemma 2)**:
   Proves `‖evalConv a u⁻¹ - truncVal (convMinor a) z u‖ ≤ K * exp (-z.re * u)` for every
   `a ∈ ConvergentPowerSeries`, inducts on `MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries`
   over any open star-shaped pole-free tube `U` containing `[0, z]`, applies the identity theorem to
   obtain `O(exp (-z.re * u))` evaluation error on any vanishing formal relation, and proves
   all-orders truncated Watson asymptotics `HasAsympExp (truncLaplace F z) (formalSeries F)` +
   exponential flatness.
3. **Section 3 — `PlaneSimplePoleData`, Finite Ray Geometry & Triangle Residue Jump (Lemma 3)**:
   Defines `PlaneSimplePoleData b` (holomorphic at `0`, locally finite simple poles with nonzero
   residues, NO growth condition at `∞`). For any finite family `b : Fin d → ℂ → ℂ` and any target
   positive real pole `s > 0`, constructs a cutoff `T > s` before the next real pole, a narrow
   aperture `m > 0`, open star-shaped pole-free flanking tubes `U_±` around `[0, T(1 ± i m)]`, and
   an open neighborhood `U_tri` of `closedTri T m` enclosing only the collinear real poles in `(0, s]`,
   and proves the exact simple-pole triangle residue jump modulo `O(exp (-T * u))`.
4. **Section 4 — Minimal-Degree Descent, Rotation Pullback & Matrix Contradiction (Lemma 4)**:
   Defines directional derivative `D_vec_conv`, proves strict degree drop and exact shift invariance,
   inducts along finitely many collinear poles on the positive real axis, rotates any complex pole
   `ω ≠ 0` to `‖ω‖ > 0` via the degree-preserving automorphism `rotConvPolyGen`, extracts the
   lowest-`w`-order nonconstant polynomial `coeffWGen k₀ Qmin`, and derives a contradiction whenever
   the pole residue-jet vectors span `ℂ^{d(r+1)}`.
5. **Section 5 — Scalar Finite-Pole Count Bound, Strong `ℂ({t})` D-Transcendence & Entire Log-Derivative Bridge**:
   Specializes to `d = 1` via complex Vandermonde: a nonzero order-`r` ADE over `ℂ{w}` forces at
   most `r` distinct poles; infinitely many poles force `StronglyDTransOverMeromorphicGerms` for both
   `ogfOfEGF b` and `formalSeries b`; constructs `entireLogDeriv_planeSimplePoleData` unconditionally
   for `-E'(c + w) / E(c + w)` of ANY entire function `E` with `E c ≠ 0`.
6. **Section 6 — Joint Multi-Series Strong `ℂ({t})` Differential Independence**:
   Defines `JointlyStronglyDTransOverConvergent` and `JointlyStronglyDTransOverMeromorphicGerms`,
   proves denominator clearing from `ℂ({t})` to `ℂ{t}` and the block-triangular `X * F_i → F_i`
   transfer via `triangular_aeval_injective`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.FiniteContourStokes

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
  PakPrimes.FishburnStrongDTrans PakPrimes.PakYeliussizovEGF PakPrimes.HigherOrderStrongDTrans
  PakPrimes.PrimeNome
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Truncated Laplace Transform & Segment Product Simplex Splitting (Lemma 1) -/

/-- Truncated Laplace transform of `F` along the straight segment `[0, z]`:
`J_z(F)(u) = z * ∫ t in (0 : ℝ)..1, exp (-u * z * t) * F (t * z)`. -/
@[expose] def truncLaplace (F : ℂ → ℂ) (z : ℂ) (u : ℝ) : ℂ :=
  z * ∫ t : ℝ in (0 : ℝ)..1, Complex.exp (-(u : ℂ) * z * (t : ℂ)) * F ((t : ℂ) * z)

/-- Truncated minor evaluation along `[0, z]`: `a.atom + J_z(a.density)(u)`. -/
@[expose] def truncVal (a : Minor) (z : ℂ) (u : ℝ) : ℂ :=
  a.atom + truncLaplace a.density z u

lemma truncLaplace_zero (z : ℂ) (u : ℝ) : truncLaplace (fun _ => 0) z u = 0 := by
  simp [truncLaplace]

lemma truncLaplace_const_mul (c : ℂ) (F : ℂ → ℂ) (z : ℂ) (u : ℝ) :
    truncLaplace (fun w => c * F w) z u = c * truncLaplace F z u := by
  unfold truncLaplace
  have heq : (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) * (c * F ((t : ℂ) * z))) =
      fun t : ℝ => c * (Complex.exp (-(u : ℂ) * z * (t : ℂ)) * F ((t : ℂ) * z)) := by
    funext t; ring
  rw [heq, intervalIntegral.integral_const_mul]
  ring

lemma truncLaplace_add {F G : ℂ → ℂ} {z : ℂ} (u : ℝ)
    (hF : ContinuousOn (fun t : ℝ => F ((t : ℂ) * z)) (Icc 0 1))
    (hG : ContinuousOn (fun t : ℝ => G ((t : ℂ) * z)) (Icc 0 1)) :
    truncLaplace (fun w => F w + G w) z u = truncLaplace F z u + truncLaplace G z u := by
  unfold truncLaplace
  have hexp : ContinuousOn (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ))) (Icc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ))).continuousOn
  have hiF : IntervalIntegrable (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) * F ((t : ℂ) * z))
      volume 0 1 := (hexp.mul hF).intervalIntegrable_of_Icc zero_le_one
  have hiG : IntervalIntegrable (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) * G ((t : ℂ) * z))
      volume 0 1 := (hexp.mul hG).intervalIntegrable_of_Icc zero_le_one
  have heq : (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) * (F ((t : ℂ) * z) + G ((t : ℂ) * z))) =
      fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) * F ((t : ℂ) * z) +
        Complex.exp (-(u : ℂ) * z * (t : ℂ)) * G ((t : ℂ) * z) := by
    funext t; ring
  rw [heq, intervalIntegral.integral_add hiF hiG, mul_add]

lemma norm_exp_neg_mul_real (z : ℂ) (u t : ℝ) :
    ‖Complex.exp (-(u : ℂ) * z * (t : ℂ))‖ = Real.exp (-(u * z.re * t)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

lemma truncLaplace_norm_le {F : ℂ → ℂ} {z : ℂ} {u M : ℝ}
    (hz : 0 ≤ z.re) (hu : 0 ≤ u) (_hM : 0 ≤ M)
    (hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖F ((t : ℂ) * z)‖ ≤ M) :
    ‖truncLaplace F z u‖ ≤ ‖z‖ * M := by
  unfold truncLaplace
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg z)
  have h1 : ‖∫ t : ℝ in (0 : ℝ)..1, Complex.exp (-(u : ℂ) * z * (t : ℂ)) * F ((t : ℂ) * z)‖ ≤
      M * |(1 : ℝ) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    rw [norm_mul, norm_exp_neg_mul_real]
    have hexp_le : Real.exp (-(u * z.re * t)) ≤ 1 := by
      have huz : 0 ≤ u * z.re := mul_nonneg hu hz
      exact Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    calc Real.exp (-(u * z.re * t)) * ‖F ((t : ℂ) * z)‖
        ≤ 1 * M := mul_le_mul hexp_le (hbd t ⟨ht.1.le, ht.2⟩) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  simpa using h1

lemma truncVal_norm_le {a : Minor} {z : ℂ} {u M : ℝ}
    (hz : 0 ≤ z.re) (hu : 0 ≤ u) (hM : 0 ≤ M)
    (hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖a.density ((t : ℂ) * z)‖ ≤ M) :
    ‖truncVal a z u‖ ≤ ‖a.atom‖ + ‖z‖ * M :=
  (norm_add_le _ _).trans (add_le_add le_rfl (truncLaplace_norm_le hz hu hM hbd))

lemma truncVal_plus {a b : Minor} {z : ℂ} (u : ℝ)
    (ha : ContinuousOn (fun t : ℝ => a.density ((t : ℂ) * z)) (Icc 0 1))
    (hb : ContinuousOn (fun t : ℝ => b.density ((t : ℂ) * z)) (Icc 0 1)) :
    truncVal (a.plus b) z u = truncVal a z u + truncVal b z u := by
  simp only [truncVal, Minor.plus]
  rw [truncLaplace_add u ha hb]
  ring

private lemma continuousOn_segment_of_analyticOn {U : Set ℂ} (hU : Domain U) {z : ℂ} (hz : z ∈ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) :
    ContinuousOn (fun t : ℝ => F ((t : ℂ) * z)) (Icc 0 1) :=
  hF.continuousOn.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
    (fun t ht => hU.star z hz t ht)

private lemma exists_segment_bound {F : ℂ → ℂ} {z : ℂ}
    (hF : ContinuousOn (fun t : ℝ => F ((t : ℂ) * z)) (Icc 0 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖F ((t : ℂ) * z)‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

/-- **Lemma 1 (Segment Product & Binary Simplex Splitting)**:
For `F, G` continuous along `[0, z]` with uniform bounds `MF, MG` and `0 ≤ z.re`, `0 ≤ u`,
`‖J_z(F)(u) * J_z(G)(u) - J_z(F * G)(u)‖ ≤ (‖z‖^2 * MF * MG / 2) * exp (-z.re * u)`. -/
theorem truncLaplace_mul_sub_convolution_le {F G : ℂ → ℂ} {z : ℂ} {u MF MG : ℝ}
    (hz : 0 ≤ z.re) (hu : 0 ≤ u) (hMF : 0 ≤ MF) (hMG : 0 ≤ MG)
    (hFc : ContinuousOn (fun t : ℝ => F ((t : ℂ) * z)) (Icc 0 1))
    (hGc : ContinuousOn (fun t : ℝ => G ((t : ℂ) * z)) (Icc 0 1))
    (hFbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖F ((t : ℂ) * z)‖ ≤ MF)
    (hGbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖G ((t : ℂ) * z)‖ ≤ MG) :
    ‖truncLaplace F z u * truncLaplace G z u -
      truncLaplace (complexConvolution F G) z u‖ ≤
      ‖z‖ ^ 2 * MF * MG * Real.exp (-z.re * u) / 2 := by
  let f : ℝ → ℂ := fun a => Complex.exp (-(u : ℂ) * z * (a : ℂ)) * F ((a : ℂ) * z)
  let g : ℝ → ℂ := fun b => Complex.exp (-(u : ℂ) * z * (b : ℂ)) * G ((b : ℂ) * z)
  have hexp_c : ContinuousOn (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ))) (Icc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ))).continuousOn
  have hf_c : ContinuousOn f (Icc 0 1) := hexp_c.mul hFc
  have hg_c : ContinuousOn g (Icc 0 1) := hexp_c.mul hGc
  have hf_int : IntegrableOn f (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (hf_c.intervalIntegrable_of_Icc zero_le_one)
  have hg_int : IntegrableOn g (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (hg_c.intervalIntegrable_of_Icc zero_le_one)
  -- Product of integrals as iterated integral over [0, 1] × [0, 1]
  have hprod_eq : (∫ a in (0 : ℝ)..1, f a) * (∫ b in (0 : ℝ)..1, g b) =
      ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, f a * g b := by
    have hinner : ∀ a : ℝ, (∫ b in (0 : ℝ)..1, f a * g b) = f a * ∫ b in (0 : ℝ)..1, g b :=
      fun a => intervalIntegral.integral_const_mul (f a) g
    simp_rw [hinner, intervalIntegral.integral_mul_const]
  -- Split inner integral at b = 1 - a
  have hsplit_inner : ∀ a ∈ Icc (0 : ℝ) 1,
      (∫ b in (0 : ℝ)..1, f a * g b) =
        (∫ b in (0 : ℝ)..(1 - a), f a * g b) + (∫ b in (1 - a)..1, f a * g b) := by
    intro a ha
    have hsub1 : uIcc (0 : ℝ) (1 - a) ⊆ Icc 0 1 := by
      rw [uIcc_of_le (sub_nonneg.mpr ha.2)]
      intro b hb; exact ⟨hb.1, by linarith [ha.1, hb.2]⟩
    have hsub2 : uIcc (1 - a) 1 ⊆ Icc 0 1 := by
      rw [uIcc_of_le (sub_le_self 1 ha.1)]
      intro b hb; exact ⟨by linarith [ha.2, hb.1], hb.2⟩
    have hi1 : IntervalIntegrable (fun b => f a * g b) volume 0 (1 - a) :=
      ((continuousOn_const.mul hg_c).mono hsub1).intervalIntegrable
    have hi2 : IntervalIntegrable (fun b => f a * g b) volume (1 - a) 1 :=
      ((continuousOn_const.mul hg_c).mono hsub2).intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  -- Continuity of the two split pieces in a ∈ [0, 1]
  have hfg_bd : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ‖f a * g b‖ ≤ MF * MG := by
    intro a ha b hb
    have huz : 0 ≤ u * z.re := mul_nonneg hu hz
    rw [norm_mul]
    have hfa : ‖f a‖ ≤ MF := by
      dsimp only [f]
      rw [norm_mul, norm_exp_neg_mul_real]
      exact (mul_le_mul (Real.exp_le_one_iff.mpr (by nlinarith [ha.1])) (hFbd a ha)
        (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
    have hgb : ‖g b‖ ≤ MG := by
      dsimp only [g]
      rw [norm_mul, norm_exp_neg_mul_real]
      exact (mul_le_mul (Real.exp_le_one_iff.mpr (by nlinarith [hb.1])) (hGbd b hb)
        (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
    exact mul_le_mul hfa hgb (norm_nonneg _) hMF
  -- Express lower and upper parts as indicator integrals on Ioc 0 1 × Ioc 0 1
  let lowerSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 + p.2 ≤ 1}
  let upperSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | 1 < p.1 + p.2}
  have hlow_meas : MeasurableSet lowerSet :=
    measurableSet_le (continuous_fst.add continuous_snd).measurable measurable_const
  have hup_meas : MeasurableSet upperSet :=
    measurableSet_lt measurable_const (continuous_fst.add continuous_snd).measurable
  have hprod_int : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    hf_int.mul_prod hg_int
  have hlow_int : Integrable (lowerSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    hprod_int.indicator hlow_meas
  have hup_int : Integrable (upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    hprod_int.indicator hup_meas
  have hprod_split : (∫ a in (0 : ℝ)..1, f a) * (∫ b in (0 : ℝ)..1, g b) =
      (∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, lowerSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)) +
      (∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)) := by
    rw [hprod_eq]
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    rw [← MeasureTheory.integral_prod _ hprod_int, ← MeasureTheory.integral_prod _ hlow_int,
      ← MeasureTheory.integral_prod _ hup_int, ← MeasureTheory.integral_add hlow_int hup_int]
    refine MeasureTheory.integral_congr_ae (ae_of_all _ fun p => ?_)
    by_cases hp : p.1 + p.2 ≤ 1
    · have hp1 : p ∈ lowerSet := hp
      have hp2 : p ∉ upperSet := not_lt.mpr hp
      simp [Set.indicator_of_mem hp1, Set.indicator_of_notMem hp2]
    · have hp1 : p ∉ lowerSet := hp
      have hp2 : p ∈ upperSet := lt_of_not_ge hp
      simp [Set.indicator_of_notMem hp1, Set.indicator_of_mem hp2]
  -- Evaluate the lower simplex integral = z⁻¹ * J_z(complexConvolution F G)(u) (after multiplying by z^2)
  have hlower_eq : z ^ 2 * (∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1,
        lowerSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)) =
      truncLaplace (complexConvolution F G) z u := by
    -- Inner integral over b ∈ Ioc 0 (1 - a), substitute s = a + b to get ∫ s in Ioc a 1
    have hinner_a : ∀ a ∈ Ioc (0 : ℝ) 1,
        (∫ b in Ioc (0 : ℝ) 1, lowerSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)) =
        ∫ s in Ioc (0 : ℝ) 1, ({p : ℝ × ℝ | p.1 < p.2}).indicator
          (fun p : ℝ × ℝ => Complex.exp (-(u : ℂ) * z * (p.2 : ℂ)) *
            F ((p.1 : ℂ) * z) * G (((p.2 - p.1 : ℝ) : ℂ) * z)) (a, s) := by
      intro a ha
      have h1a_nn : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
      have h1a_le : 1 - a ≤ 1 := sub_le_self 1 ha.1.le
      have hLHS : (∫ b in Ioc (0 : ℝ) 1, lowerSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)) =
          ∫ b in (0 : ℝ)..(1 - a), f a * g b := by
        rw [intervalIntegral.integral_of_le h1a_nn]
        have hset : Ioc (0 : ℝ) (1 - a) = Ioc (0 : ℝ) 1 ∩ {b : ℝ | a + b ≤ 1} := by
          ext b; simp only [mem_Ioc, mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨hb0, hb1⟩; exact ⟨⟨hb0, by linarith [ha.1]⟩, by linarith⟩
          · rintro ⟨⟨hb0, _⟩, hab⟩; exact ⟨hb0, by linarith⟩
        rw [hset, ← MeasureTheory.setIntegral_indicator (s := Ioc (0 : ℝ) 1) (t := {b : ℝ | a + b ≤ 1})
          (measurableSet_le (measurable_const.add measurable_id) measurable_const)]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun b _ => ?_
        by_cases hab : a + b ≤ 1
        · simp [lowerSet, hab]
        · simp [lowerSet, hab]
      have hRHS : (∫ s in Ioc (0 : ℝ) 1, ({p : ℝ × ℝ | p.1 < p.2}).indicator
            (fun p : ℝ × ℝ => Complex.exp (-(u : ℂ) * z * (p.2 : ℂ)) *
              F ((p.1 : ℂ) * z) * G (((p.2 - p.1 : ℝ) : ℂ) * z)) (a, s)) =
          ∫ s in a..1, Complex.exp (-(u : ℂ) * z * (s : ℂ)) *
            F ((a : ℂ) * z) * G (((s - a : ℝ) : ℂ) * z) := by
        rw [intervalIntegral.integral_of_le ha.2]
        have hset : Ioc a 1 = Ioc (0 : ℝ) 1 ∩ {s : ℝ | a < s} := by
          ext s; simp only [mem_Ioc, mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨has, hs1⟩; exact ⟨⟨lt_trans ha.1 has, hs1⟩, has⟩
          · rintro ⟨⟨_, hs1⟩, has⟩; exact ⟨has, hs1⟩
        rw [hset, ← MeasureTheory.setIntegral_indicator (s := Ioc (0 : ℝ) 1) (t := {s : ℝ | a < s})
          (measurableSet_lt measurable_const measurable_id)]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
        by_cases has : a < s
        · simp [has]
        · simp [has]
      rw [hLHS, hRHS]
      have hsub := intervalIntegral.integral_comp_sub_left
        (fun s : ℝ => Complex.exp (-(u : ℂ) * z * (s : ℂ)) * F ((a : ℂ) * z) * G (((s - a : ℝ) : ℂ) * z))
        a (a := (0 : ℝ)) (b := 1 - a)
      -- Wait: use integral_comp_add_left with s = a + b
      have hadd := intervalIntegral.integral_comp_add_left
        (fun s : ℝ => Complex.exp (-(u : ℂ) * z * (s : ℂ)) * F ((a : ℂ) * z) * G (((s - a : ℝ) : ℂ) * z))
        a (a := (0 : ℝ)) (b := 1 - a)
      simp only [add_zero, add_sub_cancel] at hadd
      rw [← hadd]
      refine intervalIntegral.integral_congr fun b _ => ?_
      dsimp only [f, g]
      have hexp : Complex.exp (-(u : ℂ) * z * (a : ℂ)) * Complex.exp (-(u : ℂ) * z * (b : ℂ)) =
          Complex.exp (-(u : ℂ) * z * ((a + b : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have hsub_eq : a + b - a = b := by ring
      rw [hsub_eq, ← hexp]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hinner_a]
    -- Apply Fubini to swap ∫ a in Ioc 0 1 and ∫ s in Ioc 0 1
    let triSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < p.2}
    let K : ℝ × ℝ → ℂ := fun p =>
      Complex.exp (-(u : ℂ) * z * (p.2 : ℂ)) * F ((p.1 : ℂ) * z) * G (((p.2 - p.1 : ℝ) : ℂ) * z)
    have htri_meas : MeasurableSet triSet := measurableSet_lt measurable_fst measurable_snd
    have hK_int : Integrable (triSet.indicator K)
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
      have hcont_on : ContinuousOn K ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) := by
        have h1 : ContinuousOn (fun p : ℝ × ℝ => Complex.exp (-(u : ℂ) * z * (p.2 : ℂ)))
            ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) :=
          (by fun_prop : Continuous fun p : ℝ × ℝ => Complex.exp (-(u : ℂ) * z * (p.2 : ℂ))).continuousOn
        have h2 : ContinuousOn (fun p : ℝ × ℝ => F ((p.1 : ℂ) * z))
            ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) :=
          hFc.comp continuous_fst.continuousOn (fun p hp => hp.1.1)
        have h3 : ContinuousOn (fun p : ℝ × ℝ => G (((p.2 - p.1 : ℝ) : ℂ) * z))
            ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}) :=
          hGc.comp (continuous_snd.sub continuous_fst).continuousOn fun p hp =>
            ⟨sub_nonneg.mpr hp.2, by linarith [hp.1.1.1, hp.1.2.2]⟩
        exact (h1.mul h2).mul h3
      have hmeas_K : AEStronglyMeasurable (triSet.indicator K)
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
        have hcont_open : ContinuousOn K ((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∩ triSet) :=
          hcont_on.mono fun p hp =>
            ⟨⟨Ioo_subset_Icc_self hp.1.1, Ioo_subset_Icc_self hp.1.2⟩,
              show p.1 ≤ p.2 from le_of_lt hp.2⟩
        have hopen : IsOpen ((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∩ triSet) :=
          (isOpen_Ioo.prod isOpen_Ioo).inter (isOpen_lt continuous_fst continuous_snd)
        have hmeas_ind : AEStronglyMeasurable ((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∩ triSet).indicator K)
            ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
          (aestronglyMeasurable_indicator_iff hopen.measurableSet).mpr
            (hcont_open.aestronglyMeasurable hopen.measurableSet)
        refine hmeas_ind.congr ?_
        have hIoo_ae : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))),
            p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
          have h1 : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
            rw [ae_restrict_iff' measurableSet_Ioc]
            have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
              rw [ae_iff]; simp
            filter_upwards [hne1] with x hx hmem
            exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
          exact (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
            (measurableSet_Ioo.prod measurableSet_Ioo)).mpr (by
            filter_upwards [h1] with a ha
            filter_upwards [h1] with b hb
            exact ⟨ha, hb⟩)
        filter_upwards [hIoo_ae] with p hp
        by_cases hpt : p ∈ triSet
        · simp [Set.indicator_of_mem (show p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∩ triSet from ⟨hp, hpt⟩),
            Set.indicator_of_mem hpt]
        · simp [Set.indicator_of_notMem (show p ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∩ triSet from fun h => hpt h.2),
            Set.indicator_of_notMem hpt]
      have hdom : Integrable (fun _ : ℝ × ℝ => MF * MG)
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
        integrable_const _
      refine hdom.mono' hmeas_K ?_
      have hmem_ae : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))),
          p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
        have h1 : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioc (0 : ℝ) 1 :=
          ae_restrict_mem measurableSet_Ioc
        exact (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
          (measurableSet_Ioc.prod measurableSet_Ioc)).mpr (by
          filter_upwards [h1] with a ha
          filter_upwards [h1] with b hb
          exact ⟨ha, hb⟩)
      have huz : 0 ≤ u * z.re := mul_nonneg hu hz
      filter_upwards [hmem_ae] with p hp
      by_cases hpt : p ∈ triSet
      · rw [Set.indicator_of_mem hpt]
        dsimp only [K]
        rw [norm_mul, norm_mul, norm_exp_neg_mul_real]
        have hexp1 : Real.exp (-(u * z.re * p.2)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hp.2.1])
        have hF1 : ‖F ((p.1 : ℂ) * z)‖ ≤ MF := hFbd p.1 ⟨hp.1.1.le, hp.1.2⟩
        have hG1 : ‖G (((p.2 - p.1 : ℝ) : ℂ) * z)‖ ≤ MG :=
          hGbd (p.2 - p.1) ⟨sub_nonneg.mpr (le_of_lt hpt), by linarith [hp.1.1, hp.2.2]⟩
        calc Real.exp (-(u * z.re * p.2)) * ‖F ((p.1 : ℂ) * z)‖ * ‖G (((p.2 - p.1 : ℝ) : ℂ) * z)‖
            ≤ 1 * MF * MG := by
              refine mul_le_mul (mul_le_mul hexp1 hF1 (norm_nonneg _) zero_le_one) hG1 (norm_nonneg _) (by positivity)
          _ = MF * MG := by ring
      · rw [Set.indicator_of_notMem hpt, norm_zero]; positivity
    rw [MeasureTheory.integral_integral_swap (f := fun a s => triSet.indicator K (a, s)) hK_int]
    -- Now outer variable is s ∈ Ioc 0 1, inner is a ∈ Ioc 0 s
    unfold truncLaplace
    rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hinner_s : (∫ a in Ioc (0 : ℝ) 1, triSet.indicator K (a, s)) =
        Complex.exp (-(u : ℂ) * z * (s : ℂ)) *
          ∫ a in (0 : ℝ)..s, F ((a : ℂ) * z) * G (((s - a : ℝ) : ℂ) * z) := by
      have hset : Ioo (0 : ℝ) s = Ioc (0 : ℝ) 1 ∩ {a : ℝ | a < s} := by
        ext a; simp only [mem_Ioo, mem_Ioc, mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨ha0, has⟩; exact ⟨⟨ha0, has.le.trans hs.2⟩, has⟩
        · rintro ⟨⟨ha0, _⟩, has⟩; exact ⟨ha0, has⟩
      have hIoc_s : (∫ a in Ioc (0 : ℝ) 1, triSet.indicator K (a, s)) =
          ∫ a in Ioc (0 : ℝ) s, K (a, s) := by
        conv_rhs =>
          rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, hset,
            ← MeasureTheory.setIntegral_indicator (s := Ioc (0 : ℝ) 1) (t := {a : ℝ | a < s})
              (measurableSet_lt measurable_id measurable_const)]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
        by_cases has : a < s
        · simp [triSet, has]
        · simp [triSet, has]
      rw [hIoc_s, intervalIntegral.integral_of_le hs.1.le, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
      dsimp only [K]; ring
    rw [hinner_s]
    have hscale := intervalIntegral.smul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := 1)
      (fun a : ℝ => F ((a : ℂ) * z) * G (((s - a : ℝ) : ℂ) * z)) s
    rw [mul_zero, mul_one] at hscale
    have hscale' : (∫ a in (0 : ℝ)..s, F ((a : ℂ) * z) * G (((s - a : ℝ) : ℂ) * z)) =
        (s : ℂ) * ∫ t in Ioc (0 : ℝ) 1, F ((t : ℂ) * ((s : ℂ) * z)) * G (((1 - t : ℝ) : ℂ) * ((s : ℂ) * z)) := by
      rw [← hscale, intervalIntegral.integral_of_le zero_le_one]
      change (s : ℂ) * _ = (s : ℂ) * _
      congr 1
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      have h1 : ((s * t : ℝ) : ℂ) * z = (t : ℂ) * ((s : ℂ) * z) := by push_cast; ring
      have h2 : ((s - s * t : ℝ) : ℂ) * z = ((1 - t : ℝ) : ℂ) * ((s : ℂ) * z) := by push_cast; ring
      rw [h1, h2]
    rw [hscale']
    unfold complexConvolution
    ring
  -- Combine product split and lower_eq: difference is z^2 * upper integral
  have hdiff_eq : truncLaplace F z u * truncLaplace G z u -
      truncLaplace (complexConvolution F G) z u =
      z ^ 2 * ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1,
        upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b) := by
    have hlhs : truncLaplace F z u * truncLaplace G z u =
        z ^ 2 * ((∫ a in (0 : ℝ)..1, f a) * (∫ b in (0 : ℝ)..1, g b)) := by
      unfold truncLaplace; dsimp only [f, g]; ring
    rw [hlhs, hprod_split, mul_add, hlower_eq]
    ring
  rw [hdiff_eq, norm_mul, norm_pow]
  have hupper_norm : ‖∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1,
        upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)‖ ≤
      MF * MG * Real.exp (-z.re * u) / 2 := by
    have hstep1 : ‖∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1,
          upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)‖ ≤
        ∫ a in Ioc (0 : ℝ) 1, ‖∫ b in Ioc (0 : ℝ) 1,
          upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have hinner_bd : ∀ a ∈ Ioc (0 : ℝ) 1,
        ‖∫ b in Ioc (0 : ℝ) 1, upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)‖ ≤
          a * (MF * MG * Real.exp (-z.re * u)) := by
      intro a ha
      have hset : Ioc (1 - a) 1 = Ioc (0 : ℝ) 1 ∩ {b : ℝ | 1 < a + b} := by
        ext b; simp only [mem_Ioc, mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨hb1, hb2⟩; exact ⟨⟨by linarith [ha.2], hb2⟩, by linarith⟩
        · rintro ⟨⟨_, hb2⟩, hab⟩; exact ⟨by linarith, hb2⟩
      have hIoc_u : (∫ b in Ioc (0 : ℝ) 1, upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)) =
          ∫ b in (1 - a)..1, f a * g b := by
        rw [intervalIntegral.integral_of_le (sub_le_self 1 ha.1.le), hset,
          ← MeasureTheory.setIntegral_indicator (s := Ioc (0 : ℝ) 1) (t := {b : ℝ | 1 < a + b})
            (measurableSet_lt measurable_const (measurable_const.add measurable_id))]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun b _ => ?_
        by_cases hab : 1 < a + b
        · simp [upperSet, hab]
        · simp [upperSet, hab]
      rw [hIoc_u]
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 1 - a) (b := 1) (C := MF * MG * Real.exp (-z.re * u))
        (f := fun b => f a * g b) fun b hb => by
        rw [uIoc_of_le (sub_le_self 1 ha.1.le)] at hb
        have hb01 : b ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.2, hb.1], hb.2⟩
        have hab1 : 1 ≤ a + b := by linarith [hb.1]
        dsimp only [f, g]
        have hexp_eq : Complex.exp (-(u : ℂ) * z * (a : ℂ)) * F ((a : ℂ) * z) *
            (Complex.exp (-(u : ℂ) * z * (b : ℂ)) * G ((b : ℂ) * z)) =
            Complex.exp (-(u : ℂ) * z * ((a + b : ℝ) : ℂ)) * (F ((a : ℂ) * z) * G ((b : ℂ) * z)) := by
          have he : Complex.exp (-(u : ℂ) * z * (a : ℂ)) * Complex.exp (-(u : ℂ) * z * (b : ℂ)) =
              Complex.exp (-(u : ℂ) * z * ((a + b : ℝ) : ℂ)) := by
            rw [← Complex.exp_add]; congr 1; push_cast; ring
          rw [← he]; ring
        rw [hexp_eq, norm_mul, norm_mul, norm_exp_neg_mul_real]
        have hexp_le : Real.exp (-(u * z.re * (a + b))) ≤ Real.exp (-z.re * u) := by
          refine Real.exp_le_exp.mpr ?_
          have hnn : 0 ≤ u * z.re := mul_nonneg hu hz
          nlinarith
        have hFG : ‖F ((a : ℂ) * z)‖ * ‖G ((b : ℂ) * z)‖ ≤ MF * MG :=
          mul_le_mul (hFbd a ⟨ha.1.le, ha.2⟩) (hGbd b hb01) (norm_nonneg _) hMF
        calc Real.exp (-(u * z.re * (a + b))) * (‖F ((a : ℂ) * z)‖ * ‖G ((b : ℂ) * z)‖)
            ≤ Real.exp (-z.re * u) * (MF * MG) :=
              mul_le_mul hexp_le hFG (by positivity) (Real.exp_pos _).le
          _ = MF * MG * Real.exp (-z.re * u) := by ring
      have hlen : |(1 : ℝ) - (1 - a)| = a := by
        rw [sub_sub_cancel, abs_of_pos ha.1]
      rw [hlen] at hbound
      linarith
    have hint_lhs : IntegrableOn (fun a : ℝ => ‖∫ b in Ioc (0 : ℝ) 1,
          upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)‖) (Ioc (0 : ℝ) 1) volume :=
      (hup_int.integral_prod_left).norm
    have hint_rhs : IntegrableOn (fun a : ℝ => a * (MF * MG * Real.exp (-z.re * u)))
        (Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((continuous_id.mul continuous_const).intervalIntegrable 0 1)
    have hstep2 : (∫ a in Ioc (0 : ℝ) 1, ‖∫ b in Ioc (0 : ℝ) 1,
          upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)‖) ≤
        ∫ a in Ioc (0 : ℝ) 1, a * (MF * MG * Real.exp (-z.re * u)) :=
      MeasureTheory.setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioc hinner_bd
    have hstep3 : (∫ a in Ioc (0 : ℝ) 1, a * (MF * MG * Real.exp (-z.re * u))) =
        MF * MG * Real.exp (-z.re * u) / 2 := by
      rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_mul_const]
      have ha1 : (∫ a in (0 : ℝ)..1, a) = 1 / 2 := by
        simp [integral_id]
      rw [ha1]; ring
    exact hstep1.trans (hstep2.trans_eq hstep3)
  calc ‖z‖ ^ 2 * ‖∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1,
          upperSet.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (a, b)‖
      ≤ ‖z‖ ^ 2 * (MF * MG * Real.exp (-z.re * u) / 2) :=
        mul_le_mul_of_nonneg_left hupper_norm (sq_nonneg _)
    _ = ‖z‖ ^ 2 * MF * MG * Real.exp (-z.re * u) / 2 := by ring

/-- Truncated minor product error bound:
`‖truncVal a z u * truncVal b z u - truncVal (a.times b) z u‖ ≤ (‖z‖^2 * Ma * Mb / 2) * exp (-z.re * u)`. -/
theorem truncVal_times_sub_le {a b : Minor} {z : ℂ} {u Ma Mb : ℝ}
    (hz : 0 ≤ z.re) (hu : 0 ≤ u) (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb)
    (hac : ContinuousOn (fun t : ℝ => a.density ((t : ℂ) * z)) (Icc 0 1))
    (hbc : ContinuousOn (fun t : ℝ => b.density ((t : ℂ) * z)) (Icc 0 1))
    (hconv_c : ContinuousOn (fun t : ℝ => complexConvolution a.density b.density ((t : ℂ) * z)) (Icc 0 1))
    (habd : ∀ t ∈ Icc (0 : ℝ) 1, ‖a.density ((t : ℂ) * z)‖ ≤ Ma)
    (hbbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖b.density ((t : ℂ) * z)‖ ≤ Mb) :
    ‖truncVal a z u * truncVal b z u - truncVal (a.times b) z u‖ ≤
      ‖z‖ ^ 2 * Ma * Mb * Real.exp (-z.re * u) / 2 := by
  have htimes_eq : truncVal (a.times b) z u =
      a.atom * b.atom + a.atom * truncLaplace b.density z u +
      b.atom * truncLaplace a.density z u +
      truncLaplace (complexConvolution a.density b.density) z u := by
    unfold truncVal Minor.times
    dsimp only
    have hc_ab : ContinuousOn (fun t : ℝ => a.atom * b.density ((t : ℂ) * z)) (Icc 0 1) :=
      continuousOn_const.mul hbc
    have hc_ba : ContinuousOn (fun t : ℝ => b.atom * a.density ((t : ℂ) * z)) (Icc 0 1) :=
      continuousOn_const.mul hac
    have hc_sum : ContinuousOn (fun t : ℝ => a.atom * b.density ((t : ℂ) * z) +
        b.atom * a.density ((t : ℂ) * z)) (Icc 0 1) := hc_ab.add hc_ba
    rw [truncLaplace_add (F := fun w => a.atom * b.density w + b.atom * a.density w)
        (G := complexConvolution a.density b.density) u hc_sum hconv_c,
      truncLaplace_add (F := fun w => a.atom * b.density w) (G := fun w => b.atom * a.density w) u hc_ab hc_ba,
      truncLaplace_const_mul, truncLaplace_const_mul]
    ring
  have hsub_eq : truncVal a z u * truncVal b z u - truncVal (a.times b) z u =
      truncLaplace a.density z u * truncLaplace b.density z u -
        truncLaplace (complexConvolution a.density b.density) z u := by
    rw [htimes_eq]
    unfold truncVal
    ring
  rw [hsub_eq]
  exact truncLaplace_mul_sub_convolution_le hz hu hMa hMb hac hbc habd hbbd

/-! ### 2. Convergent Coefficients, Polynomial Finite-Contour Transfer & Truncated Watson Expansion (Lemma 2) -/

/-- General coefficient-evaluated multivariate polynomial over `ConvergentPowerSeries` for any
index type `ι`. -/
@[expose] def evalConvMvPolyGen {ι : Type*}
    (Q : MvPolynomial ι ConvergentPowerSeries) (z : ℂ) : MvPolynomial ι ℂ :=
  ∑ α ∈ Q.support, MvPolynomial.monomial α (evalConv (Q.coeff α) z)

lemma evalConvMvPolyGen_coeff {ι : Type*}
    (Q : MvPolynomial ι ConvergentPowerSeries) (z : ℂ) (α : ι →₀ ℕ) :
    (evalConvMvPolyGen Q z).coeff α = evalConv (Q.coeff α) z := by
  classical
  unfold evalConvMvPolyGen
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ Q.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, evalConv_zero]
    exact Finset.sum_eq_zero fun β hβ => by simp [show β ≠ α from fun h => hα (h ▸ hβ)]

lemma evalConvMvPolyGen_C {ι : Type*} (a : ConvergentPowerSeries) (z : ℂ) :
    evalConvMvPolyGen (MvPolynomial.C a : MvPolynomial ι ConvergentPowerSeries) z =
      MvPolynomial.C (evalConv a z) := by
  classical
  ext α
  rw [evalConvMvPolyGen_coeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs <;> simp [evalConv_zero]

lemma evalConvMvPolyGen_add_eventually {ι : Type*}
    (P Q : MvPolynomial ι ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPolyGen (P + Q) (u : ℂ)⁻¹ =
        evalConvMvPolyGen P (u : ℂ)⁻¹ + evalConvMvPolyGen Q (u : ℂ)⁻¹ := by
  classical
  let S : Finset (ι →₀ ℕ) := P.support ∪ Q.support
  have hall : ∀ᶠ u : ℝ in atTop, ∀ α ∈ S,
      evalConv (P.coeff α + Q.coeff α) (u : ℂ)⁻¹ =
        evalConv (P.coeff α) (u : ℂ)⁻¹ + evalConv (Q.coeff α) (u : ℂ)⁻¹ := by
    rw [Filter.eventually_all_finset]
    intro α _
    exact evalConv_add_eventually (P.coeff α) (Q.coeff α)
  filter_upwards [hall] with u hu
  ext α
  rw [evalConvMvPolyGen_coeff, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add,
    Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply,
    evalConvMvPolyGen_coeff, evalConvMvPolyGen_coeff]
  by_cases hα : α ∈ S
  · exact hu α hα
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp fun h => hα (Finset.mem_union_left _ h)
    have hQ0 : Q.coeff α = 0 := MvPolynomial.notMem_support_iff.mp fun h => hα (Finset.mem_union_right _ h)
    simp [hP0, hQ0, evalConv_zero]

lemma evalConvMvPolyGen_mul_X {ι : Type*}
    (Q : MvPolynomial ι ConvergentPowerSeries) (j : ι) (z : ℂ) :
    evalConvMvPolyGen (Q * MvPolynomial.X j) z =
      evalConvMvPolyGen Q z * MvPolynomial.X j := by
  classical
  ext α
  rw [evalConvMvPolyGen_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs with h
  · rw [evalConvMvPolyGen_coeff]
  · exact evalConv_zero z

lemma evalConvMvPolyGen_pderiv {ι : Type*} [DecidableEq ι] (j : ι)
    (Q : MvPolynomial ι ConvergentPowerSeries) (z : ℂ) :
    evalConvMvPolyGen (MvPolynomial.pderiv j Q) z =
      MvPolynomial.pderiv j (evalConvMvPolyGen Q z) := by
  ext α
  rw [evalConvMvPolyGen_coeff, MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv,
    evalConvMvPolyGen_coeff]
  have hcast : ((α j : ConvergentPowerSeries) + 1) = (((α j + 1 : ℕ) : ConvergentPowerSeries)) := by
    push_cast; rfl
  have hcastC : ((α j : ℂ) + 1) = (((α j + 1 : ℕ) : ℂ)) := by push_cast; rfl
  rw [hcast, hcastC, evalConv_mul_natCast]

lemma evalConvMvPolyGen_hasAsympExp {ι : Type*}
    {f : ι → ℝ → ℂ} {S : ι → PowerSeries ℂ}
    (hf : ∀ p : ι, HasAsympExp (f p) (S p))
    (Q : MvPolynomial ι ConvergentPowerSeries) :
    HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun p : ι => f p u) (evalConvMvPolyGen Q (u : ℂ)⁻¹))
      (MvPolynomial.eval₂ toPS S Q) := by
  have hfn : (fun u : ℝ => MvPolynomial.eval (fun p : ι => f p u)
        (evalConvMvPolyGen Q (u : ℂ)⁻¹)) =
      fun u : ℝ => ∑ α ∈ Q.support,
        evalConv (Q.coeff α) (u : ℂ)⁻¹ * ∏ p ∈ α.support, f p u ^ α p := by
    funext u
    unfold evalConvMvPolyGen
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.eval_monomial]
    rfl
  have hser : MvPolynomial.eval₂ toPS S Q =
      ∑ α ∈ Q.support, (Q.coeff α).val * ∏ p ∈ α.support, S p ^ α p := by
    rw [MvPolynomial.eval₂_eq]
    rfl
  rw [hfn, hser]
  refine HasAsympExp.sum_finset Q.support fun α _ => ?_
  exact (evalConv_hasAsympExp (Q.coeff α)).mul
    (HasAsympExp.prod_finset α.support fun p _ => HasAsympExp.pow_nat (hf p) (α p))

/-- **Lemma 2A (Convergent Coefficient Truncation Error)**:
For any `a ∈ ConvergentPowerSeries` and `z ∈ ℂ` with `0 < z.re`,
`evalConv a u⁻¹ - truncVal (convMinor a) z u = O(exp (-z.re * u))` as `u → +∞`. -/
theorem evalConv_sub_truncVal_convMinor_le (a : ConvergentPowerSeries) {z : ℂ} (hz : 0 < z.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ u : ℝ in atTop,
      ‖evalConv a (u : ℂ)⁻¹ - truncVal (convMinor a) z u‖ ≤ K * Real.exp (-z.re * u) := by
  obtain ⟨C, D, hC, hD, hbd⟩ := convMinor_expType a z
  have hfar : Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far z) := by
    rw [BorelStokesVandermonde.far, tendsto_comap_iff]
    have heq : ((fun p : ℂ => (p * z).re) ∘ fun u : ℝ => (u : ℂ)) = fun u : ℝ => u * z.re := by
      funext u; simp [Complex.mul_re]
    rw [heq]; exact tendsto_id.atTop_mul_const hz
  have hval_ev := hfar.eventually (convMinor_value_eventually a z)
  have hgood := convMinor_good a Set.univ z
  have hray : ContainsRay Set.univ z := fun _ _ => Set.mem_univ _
  have hint_ev := hfar.eventually (hgood.integrable hray)
  refine ⟨C * Real.exp D, by positivity, ?_⟩
  filter_upwards [hval_ev, hint_ev, eventually_gt_atTop ((D + 1) / z.re)] with u hu_val hu_int hu_gt
  have hu_re : D + 1 < u * z.re := by
    have := (div_lt_iff₀ hz).mp hu_gt
    linarith
  have hu_pos : 0 < u := by nlinarith
  have hdiff_eq : evalConv a (u : ℂ)⁻¹ - truncVal (convMinor a) z u =
      ∫ v in Ioi (1 : ℝ), damped ((u : ℂ) * z) (Minor.pull z (convMinor a).density) v := by
    rw [← hu_val]
    unfold Minor.value truncVal complexLaplace truncLaplace
    have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := by
      ext v; simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro hv; by_cases hv1 : v ≤ 1; exact Or.inl ⟨hv, hv1⟩; exact Or.inr (lt_of_not_ge hv1)
      · rintro (⟨hv, _⟩ | hv); exact hv; linarith
    have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
      Set.disjoint_left.mpr fun v hv1 hv2 => not_lt_of_ge hv1.2 hv2
    have hi1 : IntegrableOn (damped ((u : ℂ) * z) (Minor.pull z (convMinor a).density))
        (Ioc (0 : ℝ) 1) volume := hu_int.mono_set (fun v hv => hv.1)
    have hi2 : IntegrableOn (damped ((u : ℂ) * z) (Minor.pull z (convMinor a).density))
        (Ioi (1 : ℝ)) volume := hu_int.mono_set (fun v hv => lt_trans zero_lt_one hv)
    rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hi1 hi2]
    have hIoc_eq : (∫ v in Ioc (0 : ℝ) 1, damped ((u : ℂ) * z) (Minor.pull z (convMinor a).density) v) =
        z * ∫ t in (0 : ℝ)..1, Complex.exp (-(u : ℂ) * z * (t : ℂ)) * (convMinor a).density ((t : ℂ) * z) := by
      rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      unfold damped Minor.pull
      have harg : (t : ℂ) * z = z * (t : ℂ) := mul_comm _ _
      rw [harg]
      have hexp : -((u : ℂ) * z) * (t : ℂ) = -(u : ℂ) * z * (t : ℂ) := by ring
      rw [hexp]; ring
    rw [hIoc_eq]; ring
  rw [hdiff_eq]
  let α : ℝ := u * z.re - D
  have hα_gt : 1 < α := by dsimp only [α]; linarith
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  have hdom_int : IntegrableOn (fun v : ℝ => C * Real.exp (-α * v)) (Ioi (1 : ℝ)) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) 1).const_mul C
  have hle1 : ‖∫ v in Ioi (1 : ℝ), damped ((u : ℂ) * z) (Minor.pull z (convMinor a).density) v‖ ≤
      ∫ v in Ioi (1 : ℝ), C * Real.exp (-α * v) := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    refine MeasureTheory.setIntegral_mono_on
      (hu_int.mono_set (fun v hv => lt_trans zero_lt_one hv)).norm hdom_int measurableSet_Ioi fun v hv => ?_
    rw [damped_norm]
    have hre : ((u : ℂ) * z).re = u * z.re := by simp [Complex.mul_re]
    rw [hre]
    calc Real.exp (-(u * z.re) * v) * ‖Minor.pull z (convMinor a).density v‖
        ≤ Real.exp (-(u * z.re) * v) * (C * Real.exp (D * v)) :=
          mul_le_mul_of_nonneg_left (hbd v (lt_trans zero_lt_one hv).le) (Real.exp_pos _).le
      _ = C * Real.exp (-α * v) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; dsimp only [α]; ring
  have hint_eval : (∫ v in Ioi (1 : ℝ), C * Real.exp (-α * v)) = C * (Real.exp (-α) / α) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) 1]
    simp [div_neg, neg_div]
  refine hle1.trans ?_
  rw [hint_eval]
  have hdiv_le : Real.exp (-α) / α ≤ Real.exp (-α) :=
    div_le_self (Real.exp_pos _).le hα_gt.le
  calc C * (Real.exp (-α) / α) ≤ C * Real.exp (-α) := mul_le_mul_of_nonneg_left hdiv_le hC
    _ = (C * Real.exp D) * Real.exp (-z.re * u) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp only [α]; ring

/-- Joint formal `d_u`-evaluation of a polynomial `Q ∈ ℂ{w}[Y_{i,j}]` on `d` formal series
`S : Fin d → PowerSeries ℂ`. -/
@[expose] def formalEvalConvJoint {d r : ℕ} (S : Fin d → PowerSeries ℂ)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries) : PowerSeries ℂ :=
  MvPolynomial.eval₂ toPS (fun p : Fin d × Fin (r + 1) => d_u^[p.2.val] (S p.1)) Q

/-- Truncated jet vector `v_z(b)(u)_{i,j} = J_z((-w)^j b_i(w))(u)`. -/
@[expose] def truncJet {d r : ℕ} (b : Fin d → ℂ → ℂ) (z : ℂ) (u : ℝ)
    (p : Fin d × Fin (r + 1)) : ℂ :=
  truncVal (Minor.jet^[p.2.val] ⟨0, b p.1⟩) z u

private lemma minor_jetIter_atom (b : ℂ → ℂ) (j : ℕ) :
    (Minor.jet^[j] ⟨0, b⟩).atom = 0 := by
  induction j with
  | zero => rfl
  | succ j _ => rw [Function.iterate_succ_apply']; rfl

private lemma minor_jetIter_density (b : ℂ → ℂ) (j : ℕ) (w : ℂ) :
    (Minor.jet^[j] ⟨0, b⟩).density w = (-w) ^ j * b w := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change -w * (Minor.jet^[j] ⟨0, b⟩).density w = (-w) ^ (j + 1) * b w
    rw [ih, pow_succ']
    ring

lemma truncJet_eq_truncLaplace {d r : ℕ} (b : Fin d → ℂ → ℂ) (z : ℂ) (u : ℝ)
    (p : Fin d × Fin (r + 1)) :
    truncJet b z u p = truncLaplace (fun w => (-w) ^ p.2.val * b p.1 w) z u := by
  unfold truncJet truncVal
  rw [minor_jetIter_atom, zero_add]
  have hd : (Minor.jet^[p.2.val] ⟨0, b p.1⟩).density = fun w => (-w) ^ p.2.val * b p.1 w :=
    funext (minor_jetIter_density (b p.1) p.2.val)
  rw [hd]

private lemma minor_jetIter_analyticOn {U : Set ℂ} {b : ℂ → ℂ} (hb : AnalyticOnNhd ℂ b U) (j : ℕ) :
    AnalyticOnNhd ℂ (Minor.jet^[j] ⟨0, b⟩).density U := by
  have hd : (Minor.jet^[j] ⟨0, b⟩).density = fun w => (-w) ^ j * b w :=
    funext (minor_jetIter_density b j)
  rw [hd]
  exact (analyticOnNhd_id.neg.pow j).mul hb

private lemma minor_jetIter_toSeries {b : ℂ → ℂ} (hb : AnalyticAt ℂ b 0) (j : ℕ) :
    (Minor.jet^[j] ⟨0, b⟩).toSeries = d_u^[j] (formalSeries b) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply' Minor.jet j ⟨0, b⟩,
      Function.iterate_succ_apply' d_u j (formalSeries b)]
    have hgj : AnalyticAt ℂ (Minor.jet^[j] ⟨0, b⟩).density 0 := by
      have hd : (Minor.jet^[j] ⟨0, b⟩).density = fun w => (-w) ^ j * b w :=
        funext (minor_jetIter_density b j)
      rw [hd]
      exact (analyticAt_id.neg.pow j).mul hb
    exact (Minor.toSeries_jet hgj).trans (congrArg d_u ih)

private lemma isPreconnected_of_domain {U : Set ℂ} (hU : Domain U) (h0 : (0 : ℂ) ∈ U) :
    IsPreconnected U := by
  refine isPreconnected_iff_subset_of_disjoint_closed.mpr fun s t hs ht hUst hst => ?_
  have hseg : ∀ z ∈ U, (z ∈ s ↔ (0 : ℂ) ∈ s) := fun z hz => by
    let γ : ℝ → ℂ := fun r => (r : ℂ) * z
    have hγ_cont : Continuous γ := Complex.continuous_ofReal.mul continuous_const
    have hγ_sub : γ '' Icc (0 : ℝ) 1 ⊆ U := by
      rintro w ⟨r, hr, rfl⟩; exact hU.star z hz r hr
    have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image γ hγ_cont.continuousOn
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

private lemma analyticOnNhd_eqOn_zero_of_iteratedDeriv_zero_FC {U : Set ℂ} {f : ℂ → ℂ}
    (hpre : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) : Set.EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz; simpa [smul_eq_mul] using hz
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
    rw [Finset.sum_congr rfl hterm]; simp
  have hzero := hderiv n
  rw [hdn] at hzero
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) hzero

/-- **Polynomial Induction for Truncated Minors on a Star-Shaped Tube**:
Every `Q ∈ ℂ{w}[Y_{i,j}]` is represented modulo `O(exp (-z.re * u))` by a single minor `m` analytic
on the open star-shaped tube `U` containing `[0, z]`, whose formal series equals
`formalEvalConvJoint (fun i => formalSeries (b i)) Q`. -/
theorem exists_truncMinor_of_mvPoly {d r : ℕ} {U : Set ℂ} {z : ℂ} {b : Fin d → ℂ → ℂ}
    (hU : Domain U) (h0 : (0 : ℂ) ∈ U) (hzU : z ∈ U) (hz : 0 < z.re)
    (hb : ∀ i : Fin d, AnalyticOnNhd ℂ (b i) U)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries) :
    ∃ m : Minor,
      AnalyticOnNhd ℂ m.density U ∧
      m.toSeries = formalEvalConvJoint (fun i => formalSeries (b i)) Q ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ u : ℝ in atTop,
        ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q (u : ℂ)⁻¹) - truncVal m z u‖ ≤
          K * Real.exp (-z.re * u) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨K, hK, hbd⟩ := evalConv_sub_truncVal_convMinor_le c hz
    refine ⟨convMinor c, (convMinor_density_entire c).mono (Set.subset_univ U), ?_, K, hK, ?_⟩
    · rw [convMinor_toSeries]
      simp [formalEvalConvJoint]
    · filter_upwards [hbd] with u hu
      simpa [evalConvMvPolyGen_C] using hu
  | add Q₁ Q₂ h₁ h₂ =>
    obtain ⟨m₁, hm₁_an, hm₁_ser, K₁, hK₁, hbd₁⟩ := h₁
    obtain ⟨m₂, hm₂_an, hm₂_ser, K₂, hK₂, hbd₂⟩ := h₂
    refine ⟨m₁.plus m₂, hm₁_an.add hm₂_an, ?_, K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    · rw [Minor.toSeries_plus (hm₁_an 0 h0) (hm₂_an 0 h0), hm₁_ser, hm₂_ser]
      simp [formalEvalConvJoint]
    · have hc₁ := continuousOn_segment_of_analyticOn hU hzU hm₁_an
      have hc₂ := continuousOn_segment_of_analyticOn hU hzU hm₂_an
      filter_upwards [hbd₁, hbd₂, evalConvMvPolyGen_add_eventually Q₁ Q₂] with u hu₁ hu₂ hadd
      rw [hadd, map_add, truncVal_plus u hc₁ hc₂]
      calc ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) +
              MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₂ (u : ℂ)⁻¹) -
              (truncVal m₁ z u + truncVal m₂ z u)‖
          = ‖(MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) - truncVal m₁ z u) +
              (MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₂ (u : ℂ)⁻¹) - truncVal m₂ z u)‖ := by
            congr 1; ring
        _ ≤ ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) - truncVal m₁ z u‖ +
            ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₂ (u : ℂ)⁻¹) - truncVal m₂ z u‖ :=
            norm_add_le _ _
        _ ≤ K₁ * Real.exp (-z.re * u) + K₂ * Real.exp (-z.re * u) := add_le_add hu₁ hu₂
        _ = (K₁ + K₂) * Real.exp (-z.re * u) := by ring
  | mul_X Q₁ p h₁ =>
    obtain ⟨m₁, hm₁_an, hm₁_ser, K₁, hK₁, hbd₁⟩ := h₁
    let mp : Minor := Minor.jet^[p.2.val] ⟨0, b p.1⟩
    have hmp_an : AnalyticOnNhd ℂ mp.density U := minor_jetIter_analyticOn (hb p.1) p.2.val
    have hconv_an : AnalyticOnNhd ℂ (complexConvolution m₁.density mp.density) U :=
      complexConvolution_analytic hU.isOpen hU.star hm₁_an hmp_an
    have htimes_an : AnalyticOnNhd ℂ (m₁.times mp).density U :=
      ((analyticOnNhd_const.mul hmp_an).add (analyticOnNhd_const.mul hm₁_an)).add hconv_an
    have hc₁ := continuousOn_segment_of_analyticOn hU hzU hm₁_an
    have hcp := continuousOn_segment_of_analyticOn hU hzU hmp_an
    have hcc := continuousOn_segment_of_analyticOn hU hzU hconv_an
    obtain ⟨M₁, hM₁, hM₁_bd⟩ := exists_segment_bound hc₁
    obtain ⟨Mp, hMp, hMp_bd⟩ := exists_segment_bound hcp
    let Bp : ℝ := ‖mp.atom‖ + ‖z‖ * Mp
    have hBp : 0 ≤ Bp := by positivity
    let K_new : ℝ := K₁ * Bp + ‖z‖ ^ 2 * M₁ * Mp / 2
    refine ⟨m₁.times mp, htimes_an, ?_, K_new, by positivity, ?_⟩
    · rw [Minor.toSeries_times (hm₁_an 0 h0) (hmp_an 0 h0), hm₁_ser,
        minor_jetIter_toSeries (hb p.1 0 h0) p.2.val]
      simp [formalEvalConvJoint]
    · filter_upwards [hbd₁, eventually_ge_atTop (0 : ℝ)] with u hu₁ hu0
      rw [evalConvMvPolyGen_mul_X, map_mul, MvPolynomial.eval_X]
      have hvp_eq : truncJet b z u p = truncVal mp z u := rfl
      rw [hvp_eq]
      have hvp_bd : ‖truncVal mp z u‖ ≤ Bp := truncVal_norm_le hz.le hu0 hMp hMp_bd
      have hprod_err := truncVal_times_sub_le hz.le hu0 hM₁ hMp hc₁ hcp hcc hM₁_bd hMp_bd
      have hsplit : MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) *
            truncVal mp z u - truncVal (m₁.times mp) z u =
          (MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) - truncVal m₁ z u) *
            truncVal mp z u +
          (truncVal m₁ z u * truncVal mp z u - truncVal (m₁.times mp) z u) := by ring
      rw [hsplit]
      calc ‖(MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) - truncVal m₁ z u) *
              truncVal mp z u +
            (truncVal m₁ z u * truncVal mp z u - truncVal (m₁.times mp) z u)‖
          ≤ ‖(MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) - truncVal m₁ z u) *
              truncVal mp z u‖ +
            ‖truncVal m₁ z u * truncVal mp z u - truncVal (m₁.times mp) z u‖ := norm_add_le _ _
        _ = ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q₁ (u : ℂ)⁻¹) - truncVal m₁ z u‖ *
              ‖truncVal mp z u‖ +
            ‖truncVal m₁ z u * truncVal mp z u - truncVal (m₁.times mp) z u‖ := by rw [norm_mul]
        _ ≤ (K₁ * Real.exp (-z.re * u)) * Bp + ‖z‖ ^ 2 * M₁ * Mp * Real.exp (-z.re * u) / 2 :=
            add_le_add (mul_le_mul hu₁ hvp_bd (norm_nonneg _) (by positivity)) hprod_err
        _ = K_new * Real.exp (-z.re * u) := by dsimp only [K_new]; ring

/-- **Finite-Contour Transfer Theorem (Codex Lemmas 1 + 2)**:
If `b : Fin d → ℂ → ℂ` are analytic on an open star-shaped tube `U` containing `[0, z]` (`z.re > 0`)
and `formalEvalConvJoint (fun i => formalSeries (b i)) Q = 0`, then evaluating `Q` on the truncated
endpoint jet `truncJet b z u` has exponentially small error `O(exp (-z.re * u))`. -/
theorem finite_contour_transfer_joint {d r : ℕ} {U : Set ℂ} {z : ℂ} {b : Fin d → ℂ → ℂ}
    (hU : Domain U) (h0 : (0 : ℂ) ∈ U) (hzU : z ∈ U) (hz : 0 < z.re)
    (hb : ∀ i : Fin d, AnalyticOnNhd ℂ (b i) U)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConvJoint (fun i => formalSeries (b i)) Q = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen Q (u : ℂ)⁻¹)‖ ≤
        K * Real.exp (-z.re * u) := by
  obtain ⟨m, hm_an, hm_ser, K, hK, hbd⟩ := exists_truncMinor_of_mvPoly hU h0 hzU hz hb Q
  rw [hQ] at hm_ser
  have hatom : m.atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hm_ser
    simpa [Minor.toSeries] using this
  have hderiv : ∀ k : ℕ, iteratedDeriv k m.density 0 = 0 := fun k => by
    have := congrArg (PowerSeries.coeff (k + 1)) hm_ser
    simpa [Minor.toSeries] using this
  have hzero : Set.EqOn m.density 0 U :=
    analyticOnNhd_eqOn_zero_of_iteratedDeriv_zero_FC (isPreconnected_of_domain hU h0) h0 hm_an hderiv
  have htrunc0 : ∀ u : ℝ, truncVal m z u = 0 := fun u => by
    unfold truncVal truncLaplace
    rw [hatom, zero_add]
    have h0int : (∫ t : ℝ in (0 : ℝ)..1, Complex.exp (-(u : ℂ) * z * (t : ℂ)) * m.density ((t : ℂ) * z)) = 0 := by
      have heq : EqOn (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) * m.density ((t : ℂ) * z))
          (fun _ => 0) (uIcc (0 : ℝ) 1) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hmem : (t : ℂ) * z ∈ U := hU.star z hzU t ht
        simp [hzero hmem]
      rw [intervalIntegral.integral_congr heq]
      simp
    rw [h0int, mul_zero]
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbd] with u hu
  simpa [htrunc0 u] using hu

/-- Elementary exponential-vs-polynomial tail bound: for `α > 0` and any `M : ℕ`,
`exp (-α * u) ≤ (M! / α^M) / u^M` for all `u > 0`. -/
lemma exp_neg_le_div_pow {α : ℝ} (hα : 0 < α) (M : ℕ) {u : ℝ} (hu : 0 < u) :
    Real.exp (-α * u) ≤ ((M.factorial : ℝ) / α ^ M) / u ^ M := by
  have hpow := Real.pow_div_factorial_le_exp (α * u) (by positivity) M
  have hαu : 0 < (α * u) ^ M := pow_pos (mul_pos hα hu) M
  have hfac : 0 < (M.factorial : ℝ) := by positivity
  have hexp_pos : 0 < Real.exp (α * u) := Real.exp_pos _
  rw [show -α * u = -(α * u) by ring, Real.exp_neg]
  have h1 : (Real.exp (α * u))⁻¹ ≤ (M.factorial : ℝ) / (α * u) ^ M := by
    rw [le_div_iff₀ hαu, inv_mul_le_iff₀ hexp_pos]
    rw [div_le_iff₀ hfac] at hpow
    linarith
  refine h1.trans_eq ?_
  rw [mul_pow, div_div]

private lemma realLaplace_monomial_Ioi_FC (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-α * v) * v ^ k = (k.factorial : ℝ) / α ^ (k + 1) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hcast : (fun v : ℝ => ((Real.exp (-α * v) * v ^ k : ℝ) : ℂ)) =
      fun v : ℝ => Complex.exp (-(α : ℂ) * (v : ℂ)) * (v : ℂ) ^ k := by
    funext v; push_cast; rfl
  rw [hcast, Minor.complexLaplace_monomial k (by simp [hα])]
  push_cast; rfl

private lemma integrableOn_exp_neg_mul_pow_Ioi_FC (k : ℕ) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun v : ℝ => Real.exp (-α * v) * v ^ k) (Ioi (0 : ℝ)) volume := by
  have hdom : IntegrableOn (fun v : ℝ => ((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (-(α / 2) * v))
      (Ioi (0 : ℝ)) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hdom.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow k)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv0.le k))]
    have hpow := Real.pow_div_factorial_le_exp (α / 2 * v) (by positivity) k
    have h1 : 0 < (α / 2) ^ k := pow_pos (by positivity) k
    have h2 : 0 < (k.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvk : v ^ k ≤ ((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (α / 2 * v) := by
      calc v ^ k ≤ (Real.exp (α / 2 * v) * (k.factorial : ℝ)) / (α / 2) ^ k :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc Real.exp (-α * v) * v ^ k
        ≤ Real.exp (-α * v) * (((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (α / 2 * v)) :=
          mul_le_mul_of_nonneg_left hvk (Real.exp_pos _).le
      _ = ((k.factorial : ℝ) / (α / 2) ^ k) * Real.exp (-(α / 2) * v) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

private lemma continuous_finset_sum_aux {α : Type*} (s : Finset α) {f : α → ℝ → ℂ}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | @insert a s ha ih =>
    have heq : (fun t => ∑ i ∈ insert a s, f i t) = fun t => f a t + ∑ i ∈ s, f i t := by
      funext t; exact Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma integral_finset_sum_aux {α : Type*} (s : Finset α) {μ : Measure ℝ}
    {f : α → ℝ → ℂ} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ t, (∑ i ∈ s, f i t) ∂μ = ∑ i ∈ s, ∫ t, f i t ∂μ := by
  classical
  have hboth : Integrable (fun t => ∑ i ∈ s, f i t) μ ∧
      ∫ t, (∑ i ∈ s, f i t) ∂μ = ∑ i ∈ s, ∫ t, f i t ∂μ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      have ⟨hint_s, heq_s⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hint_a := hf a (Finset.mem_insert_self a s)
      have heq : (fun t => ∑ i ∈ insert a s, f i t) = fun t => f a t + ∑ i ∈ s, f i t := by
        funext t; exact Finset.sum_insert ha
      refine ⟨by rw [heq]; exact hint_a.add hint_s, ?_⟩
      rw [heq, MeasureTheory.integral_add hint_a hint_s, heq_s, Finset.sum_insert ha]
  exact hboth.2

/-- **Lemma 2B (Truncated Watson Asymptotic Expansion)**:
If `F` is analytic at `0`, continuous on the closed segment `[0, z]`, and `0 < z.re`, then
`truncLaplace F z` has all-orders `1/u` asymptotic expansion equal to `formalSeries F`. -/
theorem truncLaplace_hasAsympExp {F : ℂ → ℂ} {z : ℂ}
    (hF0 : AnalyticAt ℂ F 0)
    (hFc : ContinuousOn (fun t : ℝ => F ((t : ℂ) * z)) (Icc 0 1))
    (hz : 0 < z.re) :
    HasAsympExp (fun u : ℝ => truncLaplace F z u) (formalSeries F) := by
  have hz_ne : z ≠ 0 := fun h => by simp [h] at hz
  have hzn_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  intro M
  cases M with
  | zero =>
    obtain ⟨MF, hMF, hMF_bd⟩ := exists_segment_bound hFc
    refine ⟨‖z‖ * MF, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    simpa using truncLaplace_norm_le hz.le hu hMF hMF_bd
  | succ N =>
    -- Expand F to order N at 0: F(w) = ∑_{k < N} (F^(k)(0)/k!) w^k + w^N * R(w)
    obtain ⟨R, hRa, hReq⟩ := hF0.exists_eq_sum_add_pow_mul N
    have hR_cont : ContinuousAt R 0 := hRa.continuousAt
    obtain ⟨δ_r, hδr_pos, hR_loc⟩ := Metric.eventually_nhds_iff.mp
      (hR_cont.eventually (Metric.ball_mem_nhds (R 0) one_pos))
    let K_R : ℝ := ‖R 0‖ + 1
    have hKR : 0 ≤ K_R := by positivity
    let δ : ℝ := min 1 (δ_r / (2 * ‖z‖))
    have hδ_pos : 0 < δ := lt_min one_pos (by positivity)
    have hδ_le : δ ≤ 1 := min_le_left _ _
    let P_trunc (w : ℂ) : ℂ := ∑ k ∈ Finset.range N, (w ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0
    have hP_cont : ContinuousOn (fun t : ℝ => P_trunc ((t : ℂ) * z)) (Icc 0 1) :=
      (continuous_finset_sum_aux _ fun k _ => by fun_prop).continuousOn
    obtain ⟨M_diff, hM_diff, hM_diff_bd⟩ := exists_segment_bound (F := fun w => F w - P_trunc w) (hFc.sub hP_cont)
    -- Bound on ‖F(tz) - P_trunc(tz)‖ for t ∈ [0, δ]
    have hhead_bd : ∀ t ∈ Icc (0 : ℝ) δ,
        ‖F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z)‖ ≤ K_R * (‖z‖ * t) ^ N := by
      intro t ht
      have hdist : dist ((t : ℂ) * z) 0 < δ_r := by
        rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
        have ht_le : t ≤ δ_r / (2 * ‖z‖) := ht.2.trans (min_le_right _ _)
        have : t * ‖z‖ ≤ δ_r / 2 := by
          calc t * ‖z‖ ≤ (δ_r / (2 * ‖z‖)) * ‖z‖ := mul_le_mul_of_nonneg_right ht_le hzn_pos.le
            _ = δ_r / 2 := by field_simp [hzn_pos.ne']
        linarith
      have hF_eq := hReq ((t : ℂ) * z)
      have hR_ball := hR_loc hdist
      have hR_norm : ‖R ((t : ℂ) * z)‖ ≤ K_R := by
        have hd : ‖R ((t : ℂ) * z) - R 0‖ < 1 := by simpa [dist_eq_norm] using hR_ball
        calc ‖R ((t : ℂ) * z)‖ = ‖R 0 + (R ((t : ℂ) * z) - R 0)‖ := by congr 1; ring
          _ ≤ ‖R 0‖ + ‖R ((t : ℂ) * z) - R 0‖ := norm_add_le _ _
          _ ≤ ‖R 0‖ + 1 := by linarith
      have hsub : F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z) = ((t : ℂ) * z) ^ N * R ((t : ℂ) * z) := by
        simp only [P_trunc, smul_eq_mul] at hF_eq ⊢
        rw [hF_eq, add_sub_cancel_left]
      rw [hsub, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      calc (t * ‖z‖) ^ N * ‖R ((t : ℂ) * z)‖ ≤ (t * ‖z‖) ^ N * K_R :=
            mul_le_mul_of_nonneg_left hR_norm (pow_nonneg (mul_nonneg ht.1 (norm_nonneg z)) N)
        _ = K_R * (‖z‖ * t) ^ N := by ring
    -- Exact polynomial Laplace identity on (0, ∞) minus tail on (1, ∞)
    let C_poly_tail : ℝ := ∑ k ∈ Finset.range N,
      ‖z‖ ^ (k + 1) * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
        ((k.factorial : ℝ) / (z.re / 4) ^ k) * (4 / z.re)
    have hC_poly_tail : 0 ≤ C_poly_tail :=
      Finset.sum_nonneg fun _ _ => by positivity
    let C₁ : ℝ := ‖z‖ ^ (N + 1) * K_R * (N.factorial : ℝ) / z.re ^ (N + 1)
    let C₂ : ℝ := ‖z‖ * M_diff * (((N + 1).factorial : ℝ) / (z.re * δ) ^ (N + 1))
    let C₃ : ℝ := C_poly_tail * (((N + 1).factorial : ℝ) / (z.re / 2) ^ (N + 1))
    refine ⟨C₁ + C₂ + C₃, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu1
    have hu : 0 < u := lt_of_lt_of_le one_pos hu1
    -- Partial sum of formalSeries F up to N + 1
    have hsum_eq : ∑ k ∈ Finset.range (N + 1), PowerSeries.coeff k (formalSeries F) * ((u : ℂ)⁻¹ ^ k) =
        ∑ k ∈ Finset.range N, iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
      rw [Finset.sum_range_succ']
      simp [formalSeries]
    rw [hsum_eq]
    -- Split truncLaplace F z u = truncLaplace P_trunc z u + truncLaplace (F - P_trunc) z u
    have hlin : truncLaplace F z u =
        truncLaplace P_trunc z u + truncLaplace (fun w => F w - P_trunc w) z u := by
      have hF_eq : F = fun w => P_trunc w + (F w - P_trunc w) := by funext w; ring
      conv_lhs => rw [hF_eq]
      exact truncLaplace_add u hP_cont (hFc.sub hP_cont)
    -- Bound 1: ‖truncLaplace P_trunc z u - ∑_{k < N} F^(k)(0) u^{-(k+1)}‖ ≤ C₃ / u^{N+1}
    have hpoly_err : ‖truncLaplace P_trunc z u -
        ∑ k ∈ Finset.range N, iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖ ≤ C₃ / u ^ (N + 1) := by
      have hterm_full : ∀ k : ℕ,
          z * (∫ v in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
            ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0)) =
          iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := fun k => by
        have hrew : (fun v : ℝ => Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
              ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0)) =
            fun v : ℝ => (z ^ k / (k.factorial : ℂ) * iteratedDeriv k F 0) *
              (Complex.exp (-((u : ℂ) * z) * (v : ℂ)) * (v : ℂ) ^ k) := by
          funext v
          have hexp : -(u : ℂ) * z * (v : ℂ) = -((u : ℂ) * z) * (v : ℂ) := by ring
          rw [mul_pow, hexp]; ring
        rw [hrew, MeasureTheory.integral_const_mul,
          Minor.complexLaplace_monomial k (by simp [Complex.mul_re]; exact mul_pos hu hz)]
        have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
        rw [mul_pow, inv_pow]
        field_simp [hfac, hz_ne, huC]
        ring
      have hpoly_split : truncLaplace P_trunc z u -
          ∑ k ∈ Finset.range N, iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1)) =
          -∑ k ∈ Finset.range N,
            z * ∫ v in Ioi (1 : ℝ), Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
              ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0) := by
        have hsum_int : truncLaplace P_trunc z u =
            ∑ k ∈ Finset.range N, z * ∫ v in Ioc (0 : ℝ) 1, Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
              ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0) := by
          unfold truncLaplace P_trunc
          rw [intervalIntegral.integral_of_le zero_le_one, ← Finset.mul_sum]
          congr 1
          have hfn : (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
                ∑ k ∈ Finset.range N, (((t : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0) =
              fun t : ℝ => ∑ k ∈ Finset.range N, Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
                ((((t : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0) := by
            funext t; rw [Finset.mul_sum]
          rw [hfn, integral_finset_sum_aux]
          intro k _
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
            ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
              ((((t : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0)).intervalIntegrable 0 1)
        rw [hsum_int]
        have hfull_sum : ∑ k ∈ Finset.range N, iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1)) =
            ∑ k ∈ Finset.range N, z * ∫ v in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
              ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0) :=
          Finset.sum_congr rfl fun k _ => (hterm_full k).symm
        rw [hfull_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hint_k : IntegrableOn (fun v : ℝ => Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
              ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0)) (Ioi (0 : ℝ)) volume := by
          have hdom := (integrableOn_exp_neg_mul_pow_Ioi_FC k (mul_pos hu hz)).const_mul
            (‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖)
          refine hdom.mono' (by fun_prop : Continuous fun v : ℝ => _).aestronglyMeasurable.restrict ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          have hv0 : 0 < v := hv
          rw [norm_mul, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg hv0.le, Complex.norm_natCast, norm_exp_neg_mul_real, mul_pow]
          have hexp : -(u * z.re * v) = -(u * z.re) * v := by ring
          have hrew : Real.exp (-(u * z.re * v)) * (v ^ k * ‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖) =
              ‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖ * (Real.exp (-(u * z.re) * v) * v ^ k) := by
            rw [hexp]; ring
          exact hrew.le
        have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := by
          ext v; simp only [mem_Ioi, mem_union, mem_Ioc]
          constructor
          · intro hv; by_cases hv1 : v ≤ 1; exact Or.inl ⟨hv, hv1⟩; exact Or.inr (lt_of_not_ge hv1)
          · rintro (⟨hv, _⟩ | hv); exact hv; linarith
        have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
          Set.disjoint_left.mpr fun v hv1 hv2 => not_lt_of_ge hv1.2 hv2
        rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
          (hint_k.mono_set fun v hv => hv.1) (hint_k.mono_set fun v hv => lt_trans zero_lt_one hv)]
        ring
      rw [hpoly_split, norm_neg]
      have hterm_bd : ∀ k ∈ Finset.range N,
          ‖z * ∫ v in Ioi (1 : ℝ), Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
            ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0)‖ ≤
          ‖z‖ ^ (k + 1) * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
            ((k.factorial : ℝ) / (z.re / 4) ^ k) * (4 / z.re) * Real.exp (-(z.re / 2) * u) := by
        intro k _
        rw [norm_mul]
        have hdom_k : IntegrableOn (fun v : ℝ =>
            (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
              ((k.factorial : ℝ) / (z.re / 4) ^ k)) *
              (Real.exp (-(z.re / 2) * u) * Real.exp (-(z.re / 4) * v))) (Ioi (1 : ℝ)) volume :=
          ((integrableOn_exp_mul_Ioi (by linarith) 1).const_mul _).const_mul _
        have hint_k1 : IntegrableOn (fun v : ℝ => Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
              ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0)) (Ioi (1 : ℝ)) volume := by
          have hdom : IntegrableOn (fun v : ℝ => ‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖ *
              (Real.exp (-(u * z.re) * v) * v ^ k)) (Ioi (0 : ℝ)) volume :=
            (integrableOn_exp_neg_mul_pow_Ioi_FC k (mul_pos hu hz)).const_mul
              (‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖)
          refine (IntegrableOn.mono_set hdom fun v hv => lt_trans zero_lt_one hv).mono'
            (by fun_prop : Continuous fun v : ℝ => _).aestronglyMeasurable.restrict ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          have hv0 : 0 < v := lt_trans zero_lt_one hv
          rw [norm_mul, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg hv0.le, Complex.norm_natCast, norm_exp_neg_mul_real, mul_pow]
          have hexp : -(u * z.re * v) = -(u * z.re) * v := by ring
          have hrew : Real.exp (-(u * z.re * v)) * (v ^ k * ‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖) =
              ‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖ * (Real.exp (-(u * z.re) * v) * v ^ k) := by
            rw [hexp]; ring
          exact hrew.le
        have hle_int : ‖∫ v in Ioi (1 : ℝ), Complex.exp (-(u : ℂ) * z * (v : ℂ)) *
              ((((v : ℂ) * z) ^ k / (k.factorial : ℂ)) * iteratedDeriv k F 0)‖ ≤
            ∫ v in Ioi (1 : ℝ),
              (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
                ((k.factorial : ℝ) / (z.re / 4) ^ k)) *
                (Real.exp (-(z.re / 2) * u) * Real.exp (-(z.re / 4) * v)) := by
          refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
          refine MeasureTheory.setIntegral_mono_on hint_k1.norm hdom_k measurableSet_Ioi fun v hv => ?_
          have hv1 : 1 < v := hv
          have hv0 : 0 < v := lt_trans zero_lt_one hv1
          rw [norm_mul, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg hv0.le, Complex.norm_natCast, norm_exp_neg_mul_real, mul_pow]
          have hvk : v ^ k ≤ ((k.factorial : ℝ) / (z.re / 4) ^ k) * Real.exp ((z.re / 4) * v) := by
            have hpow := Real.pow_div_factorial_le_exp (z.re / 4 * v) (by positivity) k
            have h1 : 0 < (z.re / 4) ^ k := pow_pos (by positivity) k
            have h2 : 0 < (k.factorial : ℝ) := by positivity
            rw [mul_pow, div_le_iff₀ h2] at hpow
            calc v ^ k ≤ (Real.exp (z.re / 4 * v) * (k.factorial : ℝ)) / (z.re / 4) ^ k :=
                  (le_div_iff₀ h1).mpr (by linarith)
              _ = _ := by ring
          have hexp_split : Real.exp (-(u * z.re * v)) * Real.exp ((z.re / 4) * v) ≤
              Real.exp (-(z.re / 2) * u) * Real.exp (-(z.re / 4) * v) := by
            rw [← Real.exp_add, ← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            have huv : u + v ≤ 2 * (u * v) := by nlinarith [hu1, hv1]
            have hmul := mul_le_mul_of_nonneg_left huv hz.le
            linarith
          calc Real.exp (-(u * z.re * v)) * (v ^ k * ‖z‖ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k F 0‖)
              = (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ))) *
                  (Real.exp (-(u * z.re * v)) * v ^ k) := by ring
            _ ≤ (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ))) *
                  (Real.exp (-(u * z.re * v)) * (((k.factorial : ℝ) / (z.re / 4) ^ k) * Real.exp ((z.re / 4) * v))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvk (Real.exp_pos _).le) (by positivity)
            _ = (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
                  ((k.factorial : ℝ) / (z.re / 4) ^ k)) *
                  (Real.exp (-(u * z.re * v)) * Real.exp ((z.re / 4) * v)) := by ring
            _ ≤ (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
                  ((k.factorial : ℝ) / (z.re / 4) ^ k)) *
                  (Real.exp (-(z.re / 2) * u) * Real.exp (-(z.re / 4) * v)) :=
                mul_le_mul_of_nonneg_left hexp_split (by positivity)
        have hdom_eval : (∫ v in Ioi (1 : ℝ),
              (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
                ((k.factorial : ℝ) / (z.re / 4) ^ k)) *
                (Real.exp (-(z.re / 2) * u) * Real.exp (-(z.re / 4) * v))) ≤
            (‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
              ((k.factorial : ℝ) / (z.re / 4) ^ k)) *
              (Real.exp (-(z.re / 2) * u) * (4 / z.re)) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            integral_exp_mul_Ioi (by linarith) 1]
          have htail_le : -Real.exp (-(z.re / 4) * 1) / -(z.re / 4) ≤ 4 / z.re := by
            rw [neg_div_neg_eq, mul_one]
            calc Real.exp (-(z.re / 4)) / (z.re / 4) ≤ 1 / (z.re / 4) :=
                  div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)
              _ = 4 / z.re := by ring
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail_le (Real.exp_pos _).le) (by positivity)
        calc ‖z‖ * ‖∫ v in Ioi (1 : ℝ), _‖
            ≤ ‖z‖ * ((‖z‖ ^ k * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
                ((k.factorial : ℝ) / (z.re / 4) ^ k)) *
                (Real.exp (-(z.re / 2) * u) * (4 / z.re))) :=
              mul_le_mul_of_nonneg_left (hle_int.trans hdom_eval) (norm_nonneg z)
          _ = ‖z‖ ^ (k + 1) * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
                ((k.factorial : ℝ) / (z.re / 4) ^ k) * (4 / z.re) * Real.exp (-(z.re / 2) * u) := by
              rw [pow_succ']; ring
      calc ‖∑ k ∈ Finset.range N, z * ∫ v in Ioi (1 : ℝ), _‖
          ≤ ∑ k ∈ Finset.range N, ‖z * ∫ v in Ioi (1 : ℝ), _‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range N,
              ‖z‖ ^ (k + 1) * (‖iteratedDeriv k F 0‖ / (k.factorial : ℝ)) *
                ((k.factorial : ℝ) / (z.re / 4) ^ k) * (4 / z.re) * Real.exp (-(z.re / 2) * u) :=
            Finset.sum_le_sum hterm_bd
        _ = C_poly_tail * Real.exp (-(z.re / 2) * u) := by
            dsimp only [C_poly_tail]; rw [Finset.sum_mul]
        _ ≤ C_poly_tail * ((((N + 1).factorial : ℝ) / (z.re / 2) ^ (N + 1)) / u ^ (N + 1)) :=
            mul_le_mul_of_nonneg_left (exp_neg_le_div_pow (half_pos hz) (N + 1) hu) hC_poly_tail
        _ = C₃ / u ^ (N + 1) := by dsimp only [C₃]; ring
    -- Bound 2: ‖truncLaplace (F - P_trunc) z u‖ ≤ (C₁ + C₂) / u^{N+1}
    have hrem_err : ‖truncLaplace (fun w => F w - P_trunc w) z u‖ ≤ (C₁ + C₂) / u ^ (N + 1) := by
      unfold truncLaplace
      rw [norm_mul]
      have hcont_rem : ContinuousOn (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
          (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))) (Icc 0 1) :=
        (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ))).continuousOn.mul
          (hFc.sub hP_cont)
      have hi1 : IntervalIntegrable (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
          (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))) volume 0 δ :=
        (hcont_rem.mono (by rw [uIcc_of_le hδ_pos.le]; exact Icc_subset_Icc_right hδ_le)).intervalIntegrable
      have hi2 : IntervalIntegrable (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
          (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))) volume δ 1 :=
        (hcont_rem.mono (by rw [uIcc_of_le hδ_le]; exact Icc_subset_Icc_left hδ_pos.le)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
      -- Head [0, δ]
      have hhead : ‖z‖ * ‖∫ t in (0 : ℝ)..δ, Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
            (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))‖ ≤ C₁ / u ^ (N + 1) := by
        rw [intervalIntegral.integral_of_le hδ_pos.le]
        have hi1' : IntegrableOn (fun t : ℝ => Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
            (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))) (Ioc (0 : ℝ) δ) volume :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ_pos.le).mp hi1
        have hdom_all : IntegrableOn (fun t : ℝ => (K_R * ‖z‖ ^ N) * (Real.exp (-(u * z.re) * t) * t ^ N))
            (Ioi (0 : ℝ)) volume :=
          (integrableOn_exp_neg_mul_pow_Ioi_FC N (mul_pos hu hz)).const_mul (K_R * ‖z‖ ^ N)
        have hle1 : ‖∫ t in Ioc (0 : ℝ) δ, Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
              (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))‖ ≤
            ∫ t in Ioc (0 : ℝ) δ, (K_R * ‖z‖ ^ N) * (Real.exp (-(u * z.re) * t) * t ^ N) := by
          refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
          refine MeasureTheory.setIntegral_mono_on hi1'.norm
            (IntegrableOn.mono_set hdom_all fun t ht => ht.1) measurableSet_Ioc fun t ht => ?_
          rw [norm_mul, norm_exp_neg_mul_real]
          have hb := hhead_bd t ⟨ht.1.le, ht.2⟩
          rw [mul_pow] at hb
          have hexp : -(u * z.re * t) = -(u * z.re) * t := by ring
          calc Real.exp (-(u * z.re * t)) * ‖F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z)‖
              ≤ Real.exp (-(u * z.re * t)) * (K_R * (‖z‖ ^ N * t ^ N)) :=
                mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
            _ = (K_R * ‖z‖ ^ N) * (Real.exp (-(u * z.re) * t) * t ^ N) := by rw [hexp]; ring
        have hle2 : (∫ t in Ioc (0 : ℝ) δ, (K_R * ‖z‖ ^ N) * (Real.exp (-(u * z.re) * t) * t ^ N)) ≤
            ∫ t in Ioi (0 : ℝ), (K_R * ‖z‖ ^ N) * (Real.exp (-(u * z.re) * t) * t ^ N) := by
          refine MeasureTheory.setIntegral_mono_set hdom_all ?_ (Eventually.of_forall fun t ht => ht.1)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le N))
        have heval : (∫ t in Ioi (0 : ℝ), (K_R * ‖z‖ ^ N) * (Real.exp (-(u * z.re) * t) * t ^ N)) =
            (K_R * ‖z‖ ^ N) * ((N.factorial : ℝ) / (u * z.re) ^ (N + 1)) := by
          rw [MeasureTheory.integral_const_mul, realLaplace_monomial_Ioi_FC N (mul_pos hu hz)]
        calc ‖z‖ * ‖∫ t in Ioc (0 : ℝ) δ, _‖
            ≤ ‖z‖ * ((K_R * ‖z‖ ^ N) * ((N.factorial : ℝ) / (u * z.re) ^ (N + 1))) :=
              mul_le_mul_of_nonneg_left ((hle1.trans hle2).trans_eq heval) (norm_nonneg z)
          _ = C₁ / u ^ (N + 1) := by dsimp only [C₁]; rw [mul_pow, pow_succ']; ring
      -- Tail [δ, 1]
      have htail : ‖z‖ * ‖∫ t in δ..1, Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
            (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))‖ ≤ C₂ / u ^ (N + 1) := by
        have hbd2 := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := δ) (b := 1) (C := M_diff * Real.exp (-(z.re * δ) * u))
          (f := fun t => Complex.exp (-(u : ℂ) * z * (t : ℂ)) * (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z)))
          fun t ht => by
          rw [uIoc_of_le hδ_le] at ht
          rw [norm_mul, norm_exp_neg_mul_real]
          have hexp_le : Real.exp (-(u * z.re * t)) ≤ Real.exp (-(z.re * δ) * u) := by
            have huz : 0 < u * z.re := mul_pos hu hz
            exact Real.exp_le_exp.mpr (by nlinarith [ht.1])
          have hdiff_le : ‖F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z)‖ ≤ M_diff :=
            hM_diff_bd t ⟨le_trans hδ_pos.le ht.1.le, ht.2⟩
          calc Real.exp (-(u * z.re * t)) * ‖F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z)‖
              ≤ Real.exp (-(z.re * δ) * u) * M_diff :=
                mul_le_mul hexp_le hdiff_le (norm_nonneg _) (Real.exp_pos _).le
            _ = M_diff * Real.exp (-(z.re * δ) * u) := mul_comm _ _
        have hlen : |(1 : ℝ) - δ| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hδ_le)]; linarith
        have hbd2' : ‖∫ t in δ..1, Complex.exp (-(u : ℂ) * z * (t : ℂ)) *
              (F ((t : ℂ) * z) - P_trunc ((t : ℂ) * z))‖ ≤
            M_diff * Real.exp (-(z.re * δ) * u) :=
          hbd2.trans (mul_le_of_le_one_right (by positivity) hlen)
        calc ‖z‖ * ‖∫ t in δ..1, _‖
            ≤ ‖z‖ * (M_diff * Real.exp (-(z.re * δ) * u)) :=
              mul_le_mul_of_nonneg_left hbd2' (norm_nonneg z)
          _ ≤ ‖z‖ * (M_diff * ((((N + 1).factorial : ℝ) / (z.re * δ) ^ (N + 1)) / u ^ (N + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (exp_neg_le_div_pow (mul_pos hz hδ_pos) (N + 1) hu) hM_diff)
                (norm_nonneg z)
          _ = C₂ / u ^ (N + 1) := by dsimp only [C₂]; ring
      calc ‖z‖ * ‖(∫ t in (0 : ℝ)..δ, _) + (∫ t in δ..1, _)‖
          ≤ ‖z‖ * (‖∫ t in (0 : ℝ)..δ, _‖ + ‖∫ t in δ..1, _‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg z)
        _ = ‖z‖ * ‖∫ t in (0 : ℝ)..δ, _‖ + ‖z‖ * ‖∫ t in δ..1, _‖ := mul_add _ _ _
        _ ≤ C₁ / u ^ (N + 1) + C₂ / u ^ (N + 1) := add_le_add hhead htail
        _ = (C₁ + C₂) / u ^ (N + 1) := by ring
    -- Combine both bounds
    rw [hlin]
    calc ‖truncLaplace P_trunc z u + truncLaplace (fun w => F w - P_trunc w) z u -
            ∑ k ∈ Finset.range N, iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖
        = ‖(truncLaplace P_trunc z u - ∑ k ∈ Finset.range N, iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1))) +
            truncLaplace (fun w => F w - P_trunc w) z u‖ := by congr 1; ring
      _ ≤ ‖truncLaplace P_trunc z u - ∑ k ∈ Finset.range N, iteratedDeriv k F 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖ +
          ‖truncLaplace (fun w => F w - P_trunc w) z u‖ := norm_add_le _ _
      _ ≤ C₃ / u ^ (N + 1) + (C₁ + C₂) / u ^ (N + 1) := add_le_add hpoly_err hrem_err
      _ = (C₁ + C₂ + C₃) / u ^ (N + 1) := by ring

/-- Truncated jet asymptotic expansion `truncJet b z · (i, j) ~ d_u^j (formalSeries (b i))`. -/
lemma truncJet_hasAsympExp {d r : ℕ} {U : Set ℂ} {z : ℂ} {b : Fin d → ℂ → ℂ}
    (hU : Domain U) (h0 : (0 : ℂ) ∈ U) (hzU : z ∈ U) (hz : 0 < z.re)
    (hb : ∀ i : Fin d, AnalyticOnNhd ℂ (b i) U)
    (p : Fin d × Fin (r + 1)) :
    HasAsympExp (fun u : ℝ => truncJet b z u p) (d_u^[p.2.val] (formalSeries (b p.1))) := by
  have hmp_an : AnalyticOnNhd ℂ (Minor.jet^[p.2.val] ⟨0, b p.1⟩).density U :=
    minor_jetIter_analyticOn (hb p.1) p.2.val
  have hfn : (fun u : ℝ => truncJet b z u p) =
      fun u : ℝ => truncLaplace (Minor.jet^[p.2.val] ⟨0, b p.1⟩).density z u := by
    funext u; unfold truncJet truncVal; rw [minor_jetIter_atom, zero_add]
  have hser : formalSeries (Minor.jet^[p.2.val] ⟨0, b p.1⟩).density =
      d_u^[p.2.val] (formalSeries (b p.1)) := by
    rw [← minor_jetIter_toSeries (hb p.1 0 h0) p.2.val]
    ext n
    cases n with
    | zero => simp [formalSeries, Minor.toSeries, minor_jetIter_atom]
    | succ k => simp [formalSeries, Minor.toSeries]
  rw [hfn, ← hser]
  exact truncLaplace_hasAsympExp (hmp_an 0 h0) (continuousOn_segment_of_analyticOn hU hzU hmp_an) hz

/-- Exponential flatness forces formal vanishing: if `eval (truncJet b z u) (evalConvMvPolyGen P u⁻¹)`
is `O(exp (-δ * u))` with `δ > 0`, then `formalEvalConvJoint (fun i => formalSeries (b i)) P = 0`. -/
theorem formalEvalConvJoint_eq_zero_of_exp_decay {d r : ℕ} {U : Set ℂ} {z : ℂ} {b : Fin d → ℂ → ℂ}
    (hU : Domain U) (h0 : (0 : ℂ) ∈ U) (hzU : z ∈ U) (hz : 0 < z.re)
    (hb : ∀ i : Fin d, AnalyticOnNhd ℂ (b i) U)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries)
    {C δ : ℝ} (hδ : 0 < δ)
    (hdecay : ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen P (u : ℂ)⁻¹)‖ ≤
        C * Real.exp (-δ * u)) :
    formalEvalConvJoint (fun i => formalSeries (b i)) P = 0 := by
  have hasymp := evalConvMvPolyGen_hasAsympExp (truncJet_hasAsympExp hU h0 hzU hz hb) P
  refine hasymp.eq_zero_of_flat fun M => ?_
  refine ⟨max C 0 * ((M.factorial : ℝ) / δ ^ M), ?_⟩
  filter_upwards [hdecay, eventually_gt_atTop (0 : ℝ)] with u hu hpos
  calc ‖MvPolynomial.eval (truncJet b z u) (evalConvMvPolyGen P (u : ℂ)⁻¹)‖
      ≤ C * Real.exp (-δ * u) := hu
    _ ≤ max C 0 * Real.exp (-δ * u) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
    _ ≤ max C 0 * (((M.factorial : ℝ) / δ ^ M) / u ^ M) :=
        mul_le_mul_of_nonneg_left (exp_neg_le_div_pow hδ M hpos) (le_max_right C 0)
    _ = max C 0 * ((M.factorial : ℝ) / δ ^ M) / u ^ M := by ring

/-! ### 3. `PlaneSimplePoleData`, Finite Ray Geometry & Triangle Residue Jump (Lemma 3) -/

/-- Single-valued meromorphic function on `ℂ` with isolated simple poles (holomorphic at `0`),
with **ZERO growth assumption at `∞`** and **ZERO global wedge assumption**. -/
structure PlaneSimplePoleData (b : ℂ → ℂ) where
  /-- Set of pole locations `P ⊆ ℂ`. -/
  poles : Set ℂ
  /-- Simple-pole residue at each location `ω ∈ poles`. -/
  res : ℂ → ℂ
  /-- `0` is not a pole (so `b` is holomorphic at `0`). -/
  zero_not_mem : (0 : ℂ) ∉ poles
  /-- Local finiteness: every closed disk around `0` contains only finitely many poles. -/
  finite_on_closedBall : ∀ R : ℝ, (Metric.closedBall (0 : ℂ) R ∩ poles).Finite
  /-- `b` is holomorphic on `ℂ \ poles`. -/
  analyticOn : AnalyticOnNhd ℂ b polesᶜ
  /-- Every pole in `poles` has nonzero simple residue. -/
  res_ne_zero : ∀ ω ∈ poles, res ω ≠ 0
  /-- Exact simple-pole limit `(z - ω) * b z → res ω` as `z → ω` (`z ≠ ω`). -/
  simple_pole : ∀ ω ∈ poles,
    Filter.Tendsto (fun z : ℂ => (z - ω) * b z) (𝓝[≠] ω) (𝓝 (res ω))

/-- Extended residue function: `res ω` if `ω ∈ h.poles`, and `0` if `b` is analytic at `ω`. -/
@[expose] def PlaneSimplePoleData.extRes {b : ℂ → ℂ} (h : PlaneSimplePoleData b) (ω : ℂ) : ℂ :=
  by classical exact if ω ∈ h.poles then h.res ω else 0

/-- Joint simple-pole residue-jet vector `v_λ(i, j) = extRes_i(λ) * (-λ)^j`. -/
@[expose] def jointVec {d r : ℕ} {b : Fin d → ℂ → ℂ} (h : ∀ i, PlaneSimplePoleData (b i))
    (ω : ℂ) (p : Fin d × Fin (r + 1)) : ℂ :=
  (h p.1).extRes ω * (-ω) ^ p.2.val

/-- Union of pole sets of a finite family `b : Fin d → ℂ → ℂ`. -/
@[expose] def unionPoles {d : ℕ} {b : Fin d → ℂ → ℂ} (h : ∀ i, PlaneSimplePoleData (b i)) : Set ℂ :=
  ⋃ i : Fin d, (h i).poles

lemma zero_not_mem_unionPoles {d : ℕ} {b : Fin d → ℂ → ℂ} (h : ∀ i, PlaneSimplePoleData (b i)) :
    (0 : ℂ) ∉ unionPoles h := by
  simp only [unionPoles, mem_iUnion, not_exists]
  exact fun i => (h i).zero_not_mem

lemma finite_on_closedBall_unionPoles {d : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i)) (R : ℝ) :
    (Metric.closedBall (0 : ℂ) R ∩ unionPoles h).Finite := by
  have heq : Metric.closedBall (0 : ℂ) R ∩ unionPoles h =
      ⋃ i : Fin d, Metric.closedBall (0 : ℂ) R ∩ (h i).poles := by
    simp [unionPoles, Set.inter_iUnion]
  rw [heq]
  exact Set.finite_iUnion fun i => (h i).finite_on_closedBall R

/-- Open upper flanking sector truncated at `Re z < T'`. -/
private def finiteWedgePlus (m' ε T' : ℝ) : Set ℂ :=
  (Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < m' * z.re}) ∩
    {z : ℂ | z.re < T'}

/-- Open lower flanking sector truncated at `Re z < T'`. -/
private def finiteWedgeMinus (m' ε T' : ℝ) : Set ℂ :=
  (Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -(m' * z.re) < z.im}) ∩
    {z : ℂ | z.re < T'}

/-- Open symmetric triangle neighborhood truncated at `Re z < T'`. -/
private def finiteWedgeTri (m' ε T' : ℝ) : Set ℂ :=
  (Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ |z.im| < m' * z.re}) ∩
    {z : ℂ | z.re < T'}

private lemma finiteWedgePlus_domain {m' ε T' : ℝ} (hε : 0 < ε) (hT' : 0 < T') :
    Domain (finiteWedgePlus m' ε T') := by
  refine ⟨(Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re))))).inter
    (isOpen_lt Complex.continuous_re continuous_const), fun z hz t ht => ?_⟩
  have hre_t : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
  have him_t : ((t : ℂ) * z).im = t * z.im := by simp [Complex.mul_im]
  refine ⟨?_, ?_⟩
  · rcases hz.1 with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball, dist_zero_right] at hball ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · left; simpa [Metric.mem_ball] using hε
      · right
        change 0 < ((t : ℂ) * z).re ∧ 0 < ((t : ℂ) * z).im ∧ ((t : ℂ) * z).im < m' * ((t : ℂ) * z).re
        rw [hre_t, him_t]
        exact ⟨mul_pos ht0 hre, mul_pos ht0 him, by nlinarith⟩
  · rw [mem_ofPred_eq, hre_t]
    rcases le_or_gt z.re 0 with hle | hpos
    · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos ht.1 hle) hT'
    · exact lt_of_le_of_lt (mul_le_of_le_one_left hpos.le ht.2) hz.2

private lemma finiteWedgeMinus_domain {m' ε T' : ℝ} (hε : 0 < ε) (hT' : 0 < T') :
    Domain (finiteWedgeMinus m' ε T') := by
  refine ⟨(Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter
      (isOpen_lt (continuous_const.mul Complex.continuous_re).neg Complex.continuous_im)))).inter
    (isOpen_lt Complex.continuous_re continuous_const), fun z hz t ht => ?_⟩
  have hre_t : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
  have him_t : ((t : ℂ) * z).im = t * z.im := by simp [Complex.mul_im]
  refine ⟨?_, ?_⟩
  · rcases hz.1 with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball, dist_zero_right] at hball ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · left; simpa [Metric.mem_ball] using hε
      · right
        change 0 < ((t : ℂ) * z).re ∧ ((t : ℂ) * z).im < 0 ∧ -(m' * ((t : ℂ) * z).re) < ((t : ℂ) * z).im
        rw [hre_t, him_t]
        exact ⟨mul_pos ht0 hre, mul_neg_of_pos_of_neg ht0 him, by nlinarith⟩
  · rw [mem_ofPred_eq, hre_t]
    rcases le_or_gt z.re 0 with hle | hpos
    · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos ht.1 hle) hT'
    · exact lt_of_le_of_lt (mul_le_of_le_one_left hpos.le ht.2) hz.2

private lemma isOpen_finiteWedgeTri (m' ε T' : ℝ) : IsOpen (finiteWedgeTri m' ε T') :=
  (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im)
      (continuous_const.mul Complex.continuous_re)))).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- **Finite Ray Geometry Construction**:
Given a target positive real radius `s > 0`, constructs `T, T', m, m', ε > 0` such that:
- `s < T < T'`, `0 < m < m'`,
- `closedTri T m ⊆ finiteWedgeTri m' ε T'`,
- `finiteWedgeTri m' ε T' ∩ unionPoles h` equals the finite set of real poles in `(0, s]`,
- `finiteWedgePlus m' ε T'` and `finiteWedgeMinus m' ε T'` are disjoint from `unionPoles h`,
- `T * (1 + I * m) ∈ finiteWedgePlus m' ε T'` and `T * (1 - I * m) ∈ finiteWedgeMinus m' ε T'`. -/
private lemma exists_finite_triangle_geometry {d : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i)) {s : ℝ} (hs : 0 < s) :
    ∃ (T T' m m' ε : ℝ) (S_ray : Finset ℝ),
      s < T ∧ T < T' ∧ 0 < m ∧ m < m' ∧ 0 < ε ∧ ε < T' ∧
      (∀ x : ℝ, x ∈ S_ray ↔ 0 < x ∧ x ≤ s ∧ (x : ℂ) ∈ unionPoles h) ∧
      closedTri T m ⊆ finiteWedgeTri m' ε T' ∧
      finiteWedgeTri m' ε T' ∩ unionPoles h = (fun x : ℝ => (x : ℂ)) '' (S_ray : Set ℝ) ∧
      Disjoint (finiteWedgePlus m' ε T') (unionPoles h) ∧
      Disjoint (finiteWedgeMinus m' ε T') (unionPoles h) ∧
      (T : ℂ) * (1 + I * (m : ℂ)) ∈ finiteWedgePlus m' ε T' ∧
      (T : ℂ) * (1 - I * (m : ℂ)) ∈ finiteWedgeMinus m' ε T' := by
  classical
  -- Fix enclosing closed disk of radius 2 * (s + 1)
  let R₀ : ℝ := 2 * (s + 1)
  have hPfin : (Metric.closedBall (0 : ℂ) R₀ ∩ unionPoles h).Finite :=
    finite_on_closedBall_unionPoles h R₀
  let P_box : Finset ℂ := hPfin.toFinset
  have hP_box_mem : ∀ w : ℂ, w ∈ P_box ↔ ‖w‖ ≤ R₀ ∧ w ∈ unionPoles h := fun w => by
    simp [P_box, Metric.mem_closedBall, dist_zero_right]
  -- Choose T' strictly between s and the next real pole in (s, s + 1]
  let P_after : Finset ℝ :=
    (P_box.filter (fun w => s < w.re ∧ w.re ≤ s + 1 ∧ w.im = 0)).image Complex.re
  let T_next : ℝ := if hne : P_after.Nonempty then P_after.min' hne else s + 1
  have hs_lt_Tnext : s < T_next := by
    dsimp only [T_next]
    split_ifs with hne
    · have hmem := P_after.min'_mem hne
      obtain ⟨w, hw, hw_eq⟩ := Finset.mem_image.mp hmem
      rw [← hw_eq]
      exact (Finset.mem_filter.mp hw).2.1
    · linarith
  have hTnext_le : T_next ≤ s + 1 := by
    dsimp only [T_next]
    split_ifs with hne
    · have hmem := P_after.min'_mem hne
      obtain ⟨w, hw, hw_eq⟩ := Finset.mem_image.mp hmem
      rw [← hw_eq]
      exact (Finset.mem_filter.mp hw).2.2.1
    · exact le_rfl
  let T : ℝ := (s + T_next) / 2
  let T' : ℝ := (T + T_next) / 2
  have hs_lt_T : s < T := by dsimp only [T]; linarith
  have hT_lt_T' : T < T' := by dsimp only [T, T']; linarith
  have hT'_lt_Tnext : T' < T_next := by dsimp only [T, T']; linarith
  have hT'_le_s1 : T' ≤ s + 1 := le_trans hT'_lt_Tnext.le hTnext_le
  have hT_pos : 0 < T := lt_trans hs hs_lt_T
  have hT'_pos : 0 < T' := lt_trans hT_pos hT_lt_T'
  -- Choose ε > 0 strictly smaller than T' and every pole norm in P_box
  let P_norms : Finset ℝ := P_box.image norm
  let ε₀ : ℝ := if hne : P_norms.Nonempty then P_norms.min' hne else 1
  have hε₀_pos : 0 < ε₀ := by
    dsimp only [ε₀]
    split_ifs with hne
    · obtain ⟨w, hw, hwn⟩ := Finset.mem_image.mp (P_norms.min'_mem hne)
      rw [← hwn, norm_pos_iff]
      intro hw0
      exact zero_not_mem_unionPoles h (hw0 ▸ (hP_box_mem w).mp hw).2
    · exact one_pos
  let ε : ℝ := min (T' / 2) (ε₀ / 2)
  have hε_pos : 0 < ε := lt_min (half_pos hT'_pos) (half_pos hε₀_pos)
  have hε_lt_T' : ε < T' := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hT'_pos)
  -- Choose m' > 0 small enough to exclude all off-axis poles in P_box with 0 < Re w < T'
  let P_off : Finset ℂ := P_box.filter (fun w => 0 < w.re ∧ w.re < T' ∧ w.im ≠ 0)
  let P_slopes : Finset ℝ := P_off.image (fun w => |w.im| / w.re)
  let m_lim : ℝ := if hne : P_slopes.Nonempty then P_slopes.min' hne else 1
  have hm_lim_pos : 0 < m_lim := by
    dsimp only [m_lim]
    split_ifs with hne
    · obtain ⟨w, hw, hws⟩ := Finset.mem_image.mp (P_slopes.min'_mem hne)
      rw [← hws]
      have hwf := (Finset.mem_filter.mp hw).2
      exact div_pos (abs_pos.mpr hwf.2.2) hwf.1
    · exact one_pos
  let m' : ℝ := min 1 (m_lim / 2)
  let m : ℝ := m' / 2
  have hm'_pos : 0 < m' := lt_min one_pos (half_pos hm_lim_pos)
  have hm'_le_one : m' ≤ 1 := min_le_left _ _
  have hm_pos : 0 < m := half_pos hm'_pos
  have hm_lt_m' : m < m' := half_lt_self hm'_pos
  -- Finite set of real poles in (0, s]
  let S_ray : Finset ℝ :=
    (P_box.filter (fun w => 0 < w.re ∧ w.re ≤ s ∧ w.im = 0)).image Complex.re
  have hS_ray_iff : ∀ x : ℝ, x ∈ S_ray ↔ 0 < x ∧ x ≤ s ∧ (x : ℂ) ∈ unionPoles h := by
    intro x
    simp only [S_ray, Finset.mem_image, Finset.mem_filter, hP_box_mem]
    constructor
    · rintro ⟨w, ⟨⟨_, hwP⟩, hwre0, hwres, hwim⟩, rfl⟩
      have hw_eq : (w.re : ℂ) = w := Complex.ext rfl (by simp [hwim])
      exact ⟨hwre0, hwres, hw_eq.symm ▸ hwP⟩
    · rintro ⟨hx0, hxs, hxP⟩
      refine ⟨(x : ℂ), ⟨⟨?_, hxP⟩, by simpa using hx0, by simpa using hxs, by simp⟩, by simp⟩
      rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]
      dsimp only [R₀]; linarith
  -- Every point of finiteWedgeTri m' ε T' lies inside closedBall 0 R₀
  have htri_in_R₀ : ∀ z ∈ finiteWedgeTri m' ε T', ‖z‖ ≤ R₀ := by
    intro z hz
    rcases hz.1 with hball | ⟨hre, him⟩
    · rw [Metric.mem_ball, dist_zero_right] at hball
      have : ε ≤ s + 1 := le_trans hε_lt_T'.le hT'_le_s1
      dsimp only [R₀]; linarith
    · have hre_le : z.re ≤ s + 1 := le_trans hz.2.le hT'_le_s1
      have him_le : |z.im| ≤ z.re := le_trans him.le (mul_le_of_le_one_left hre.le hm'_le_one)
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ = z.re + |z.im| := by rw [abs_of_pos hre]
        _ ≤ 2 * (s + 1) := by linarith
  -- No pole lies in Metric.ball 0 ε
  have hball_no_pole : ∀ z ∈ Metric.ball (0 : ℂ) ε, z ∉ unionPoles h := by
    intro z hz hP
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hzR : ‖z‖ ≤ R₀ := by
      have : ε ≤ s + 1 := le_trans hε_lt_T'.le hT'_le_s1
      dsimp only [R₀]; linarith
    have hzbox : z ∈ P_box := (hP_box_mem z).mpr ⟨hzR, hP⟩
    have hne : P_norms.Nonempty := ⟨‖z‖, Finset.mem_image.mpr ⟨z, hzbox, rfl⟩⟩
    have hle : ε₀ ≤ ‖z‖ := by
      dsimp only [ε₀]; simp only [hne, ↓reduceDIte]
      exact P_norms.min'_le ‖z‖ (Finset.mem_image.mpr ⟨z, hzbox, rfl⟩)
    have hε_le : ε ≤ ε₀ / 2 := min_le_right _ _
    linarith
  -- No off-axis pole lies in finiteWedgeTri m' ε T'
  have htri_poles_eq :
      finiteWedgeTri m' ε T' ∩ unionPoles h = (fun x : ℝ => (x : ℂ)) '' (S_ray : Set ℝ) := by
    ext w
    simp only [mem_inter_iff, mem_image, Finset.mem_coe, hS_ray_iff]
    constructor
    · rintro ⟨hw_tri, hw_P⟩
      have hw_box : w ∈ P_box := (hP_box_mem w).mpr ⟨htri_in_R₀ w hw_tri, hw_P⟩
      rcases hw_tri.1 with hball | ⟨hre, him⟩
      · exact absurd hw_P (hball_no_pole w hball)
      · have hw_im0 : w.im = 0 := by
          by_contra him_ne
          have hwoff : w ∈ P_off :=
            Finset.mem_filter.mpr ⟨hw_box, hre, hw_tri.2, him_ne⟩
          have hne : P_slopes.Nonempty :=
            ⟨|w.im| / w.re, Finset.mem_image.mpr ⟨w, hwoff, rfl⟩⟩
          have hle : m_lim ≤ |w.im| / w.re := by
            dsimp only [m_lim]; simp only [hne, ↓reduceDIte]
            exact P_slopes.min'_le _ (Finset.mem_image.mpr ⟨w, hwoff, rfl⟩)
          have hm'_le : m' ≤ m_lim / 2 := min_le_right _ _
          have hdiv : |w.im| / w.re < m' := (div_lt_iff₀ hre).mpr him
          linarith
        have hw_le_s : w.re ≤ s := by
          by_contra hgt
          push Not at hgt
          have hwaft : w.re ∈ P_after :=
            Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr
              ⟨hw_box, hgt, le_trans hw_tri.2.le hT'_le_s1, hw_im0⟩, rfl⟩
          have hne : P_after.Nonempty := ⟨w.re, hwaft⟩
          have hle : T_next ≤ w.re := by
            dsimp only [T_next]; simp only [hne, ↓reduceDIte]
            exact P_after.min'_le _ hwaft
          have hwre_lt : w.re < T' := hw_tri.2
          linarith
        refine ⟨w.re, ⟨hre, hw_le_s, ?_⟩, Complex.ext rfl (by simp [hw_im0])⟩
        have hw_eq : (w.re : ℂ) = w := Complex.ext rfl (by simp [hw_im0])
        rwa [hw_eq]
    · rintro ⟨x, ⟨hx0, hxs, hxP⟩, rfl⟩
      refine ⟨⟨Or.inr ⟨by simpa using hx0, by simp [mul_pos hm'_pos hx0]⟩, ?_⟩, hxP⟩
      simpa using lt_trans (lt_of_le_of_lt hxs hs_lt_T) hT_lt_T'
  refine ⟨T, T', m, m', ε, S_ray, hs_lt_T, hT_lt_T', hm_pos, hm_lt_m', hε_pos, hε_lt_T',
    hS_ray_iff, ?_, htri_poles_eq, ?_, ?_, ?_, ?_⟩
  · -- closedTri T m ⊆ finiteWedgeTri m' ε T'
    intro z hz
    refine ⟨?_, lt_of_le_of_lt hz.2.1 hT_lt_T'⟩
    rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
    · left
      have him0 : z.im = 0 := abs_nonpos_iff.mp (by simpa [← hz0] using hz.2.2)
      have hzeq : z = 0 := Complex.ext hz0.symm him0
      simpa [hzeq, Metric.mem_ball] using hε_pos
    · right
      exact ⟨hzpos, lt_of_le_of_lt hz.2.2 (mul_lt_mul_of_pos_right hm_lt_m' hzpos)⟩
  · -- Disjoint (finiteWedgePlus m' ε T') (unionPoles h)
    rw [Set.disjoint_left]
    intro w hw hP
    have hsub : finiteWedgePlus m' ε T' ⊆ finiteWedgeTri m' ε T' := fun z hz => by
      refine ⟨?_, hz.2⟩
      rcases hz.1 with hb | ⟨hre, him, hlt⟩
      · exact Or.inl hb
      · exact Or.inr ⟨hre, by rwa [abs_of_pos him]⟩
    have hmem : w ∈ finiteWedgeTri m' ε T' ∩ unionPoles h := ⟨hsub hw, hP⟩
    rw [htri_poles_eq] at hmem
    obtain ⟨x, _, rfl⟩ := hmem
    rcases hw.1 with hb | ⟨_, him, _⟩
    · exact hball_no_pole (x : ℂ) hb hP
    · simp at him
  · -- Disjoint (finiteWedgeMinus m' ε T') (unionPoles h)
    rw [Set.disjoint_left]
    intro w hw hP
    have hsub : finiteWedgeMinus m' ε T' ⊆ finiteWedgeTri m' ε T' := fun z hz => by
      refine ⟨?_, hz.2⟩
      rcases hz.1 with hb | ⟨hre, him, hlt⟩
      · exact Or.inl hb
      · exact Or.inr ⟨hre, by rw [abs_of_neg him]; linarith⟩
    have hmem : w ∈ finiteWedgeTri m' ε T' ∩ unionPoles h := ⟨hsub hw, hP⟩
    rw [htri_poles_eq] at hmem
    obtain ⟨x, _, rfl⟩ := hmem
    rcases hw.1 with hb | ⟨_, him, _⟩
    · exact hball_no_pole (x : ℂ) hb hP
    · simp at him
  · -- T * (1 + I * m) ∈ finiteWedgePlus m' ε T'
    have hre : ((T : ℂ) * (1 + I * (m : ℂ))).re = T := by simp [Complex.mul_re]
    have him : ((T : ℂ) * (1 + I * (m : ℂ))).im = T * m := by simp [Complex.mul_im]
    exact ⟨Or.inr ⟨by rw [hre]; exact hT_pos, by rw [him]; exact mul_pos hT_pos hm_pos,
      by rw [hre, him]; nlinarith⟩, by rw [mem_ofPred_eq, hre]; exact hT_lt_T'⟩
  · -- T * (1 - I * m) ∈ finiteWedgeMinus m' ε T'
    have hre : ((T : ℂ) * (1 - I * (m : ℂ))).re = T := by simp [Complex.mul_re]
    have him : ((T : ℂ) * (1 - I * (m : ℂ))).im = -(T * m) := by simp [Complex.mul_im]
    exact ⟨Or.inr ⟨by rw [hre]; exact hT_pos,
      by rw [him]; exact neg_lt_zero.mpr (mul_pos hT_pos hm_pos),
      by rw [hre, him]; nlinarith⟩, by rw [mem_ofPred_eq, hre]; exact hT_lt_T'⟩

private def TriBdIntFC (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R

private lemma triIntegral_add_FC {F G : ℂ → ℂ} {R m : ℝ}
    (hF : TriBdIntFC F R m) (hG : TriBdIntFC G R m) :
    triIntegral (fun z => F z + G z) R m = triIntegral F R m + triIntegral G R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (F ((x : ℂ) * (1 - I * (m : ℂ))) +
      G ((x : ℂ) * (1 - I * (m : ℂ))))) = fun x : ℝ =>
      (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ))) +
      (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (F ((x : ℂ) * (1 + I * (m : ℂ))) +
      G ((x : ℂ) * (1 + I * (m : ℂ))))) = fun x : ℝ =>
      (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))) +
      (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_add hF.1 hG.1,
    intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2 hG.2.2]
  ring

private lemma triIntegral_const_mul_FC (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_const_mul c, intervalIntegral.integral_const_mul c,
    intervalIntegral.integral_const_mul c]
  ring

private lemma triIntegral_sum_FC {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntFC (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert i s hi ih =>
    have hFi := hF i (Finset.mem_insert_self i s)
    have hFs : ∀ j ∈ s, TriBdIntFC (F j) R m := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum_int : TriBdIntFC (fun z => ∑ j ∈ s, F j z) R m := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 - I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 - I * (m : ℂ)) * F j ((x : ℂ) * (1 - I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).1
      · have heq : (fun y : ℝ => ∑ j ∈ s, F j ((R : ℂ) + (y : ℂ) * I)) =
            ∑ j ∈ s, fun y : ℝ => F j ((R : ℂ) + (y : ℂ) * I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.1
      · have heq : (fun x : ℝ => (1 + I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 + I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 + I * (m : ℂ)) * F j ((x : ℂ) * (1 + I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.2
    have hfn : (fun z => ∑ j ∈ insert i s, F j z) = fun z => F i z + ∑ j ∈ s, F j z := by
      funext z; rw [Finset.sum_insert hi]
    rw [hfn, triIntegral_add_FC hFi hsum_int, ih hFs, Finset.sum_insert hi]

private lemma triIntegral_congr_FC {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 - I * (m : ℂ))) = G ((x : ℂ) * (1 - I * (m : ℂ))))
    (h2 : ∀ y ∈ Icc (-m * R) (m * R), F ((R : ℂ) + (y : ℂ) * I) = G ((R : ℂ) + (y : ℂ) * I))
    (h3 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 + I * (m : ℂ))) = G ((x : ℂ) * (1 + I * (m : ℂ)))) :
    triIntegral F R m = triIntegral G R m := by
  unfold triIntegral
  have hmR : -m * R ≤ m * R := by nlinarith
  have i1 : (∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) :=
    intervalIntegral.integral_congr fun x hx => by rw [uIcc_of_le hR] at hx; rw [h1 x hx]
  have i2 : (∫ y : ℝ in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-m * R)..(m * R), G ((R : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_congr fun y hy => by rw [uIcc_of_le hmR] at hy; rw [h2 y hy]
  have i3 : (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) :=
    intervalIntegral.integral_congr fun x hx => by rw [uIcc_of_le hR] at hx; rw [h3 x hx]
  rw [i1, i2, i3]

private lemma triBdInt_of_continuousOn_FC {F : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntFC F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma triBd_avoid_real_FC {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) :
    (∀ x : ℝ, (x : ℂ) * (1 - I * (m : ℂ)) ≠ (c : ℂ)) ∧
    (∀ x : ℝ, (x : ℂ) * (1 + I * (m : ℂ)) ≠ (c : ℂ)) ∧
    (∀ y : ℝ, (R : ℂ) + (y : ℂ) * I ≠ (c : ℂ)) := by
  refine ⟨fun x h0 => ?_, fun x h0 => ?_, fun y h0 => ?_⟩
  · have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add,
      Complex.I_re, zero_sub] at him
    have hx0 : x = 0 := (mul_eq_zero.mp (by linarith)).resolve_right hm.ne'
    have hre := congrArg Complex.re h0
    simp [hx0] at hre
    linarith
  · have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add,
      Complex.I_re] at him
    have hx0 : x = 0 := (mul_eq_zero.mp (by linarith)).resolve_right hm.ne'
    have hre := congrArg Complex.re h0
    simp [hx0] at hre
    linarith
  · have hre := congrArg Complex.re h0
    simp at hre
    linarith

/-- **Lemma 3 (Simple-Pole Triangle Residue Jump)**:
If `b` is analytic on `U \ S_ray` where `U` is an open neighborhood of `closedTri T m`, every
`x ∈ S_ray` lies in `(0, T)` and has simple-pole residue `res_ext x` (or `0` if analytic at `x`),
then for `z_± = T * (1 ± I * m)` and every `j : ℕ`, there is `C_conn ≥ 0` such that for all `u ≥ 0`:
`‖J_{z_-}((-w)^j b)(u) - J_{z_+}((-w)^j b)(u) - ∑ x ∈ S_ray, 2πi * res_ext x * (-x)^j * exp(-x u)‖ ≤ C_conn * exp (-T * u)`. -/
theorem finite_triangle_simple_pole_jump {b : ℂ → ℂ} (hb : PlaneSimplePoleData b)
    {U : Set ℂ} {T m : ℝ} {S_ray : Finset ℝ}
    (hT : 0 < T) (hm : 0 < m) (hU : IsOpen U) (hsub : closedTri T m ⊆ U)
    (hS_in : ∀ x ∈ S_ray, 0 < x ∧ x < T)
    (hU_poles : U ∩ hb.poles ⊆ (fun x : ℝ => (x : ℂ)) '' (S_ray : Set ℝ))
    (j : ℕ) :
    ∃ C_conn : ℝ, 0 ≤ C_conn ∧ ∀ u : ℝ, 0 ≤ u →
      ‖truncLaplace (fun w => (-w) ^ j * b w) ((T : ℂ) * (1 - I * (m : ℂ))) u -
        truncLaplace (fun w => (-w) ^ j * b w) ((T : ℂ) * (1 + I * (m : ℂ))) u -
        ∑ x ∈ S_ray, 2 * (Real.pi : ℂ) * I * hb.extRes (x : ℂ) *
          (-(x : ℂ)) ^ j * Complex.exp (-(x : ℂ) * (u : ℂ))‖ ≤
        C_conn * Real.exp (-T * u) := by
  classical
  -- Filter S_ray to actual poles of b
  let S_p : Finset ℝ := S_ray.filter (fun x => (x : ℂ) ∈ hb.poles)
  let Pset : Set ℂ := (fun x : ℝ => (x : ℂ)) '' (S_p : Set ℝ)
  let Sn (z : ℂ) : ℂ := ∑ x ∈ S_p, hb.res (x : ℂ) / (z - (x : ℂ))
  let ψ (z : ℂ) : ℂ :=
    if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => b w - Sn w) else b z - Sn z
  have hP_fin : Pset.Finite := (Finset.finite_toSet S_p).image _
  have hP_closed : IsClosed Pset := hP_fin.isClosed
  have hU_sdiff : U \ Pset ⊆ hb.polesᶜ := by
    intro w ⟨hwU, hwP⟩ hw_pol
    obtain ⟨x, hxS, rfl⟩ := hU_poles ⟨hwU, hw_pol⟩
    exact hwP ⟨x, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hxS, hw_pol⟩), rfl⟩
  have hSn_an : ∀ z ∈ U \ Pset, AnalyticAt ℂ Sn z := by
    intro z hz
    refine Finset.analyticAt_fun_sum S_p fun x hx => ?_
    refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
    intro h0
    exact hz.2 ⟨x, Finset.mem_coe.mpr hx, (sub_eq_zero.mp h0).symm⟩
  -- Analyticity of pole-subtracted remainder ψ on all of U
  have hψ_an : AnalyticOnNhd ℂ ψ U := by
    intro z hzU
    by_cases hzP : z ∈ Pset
    · obtain ⟨x₀, hx₀_mem, rfl⟩ := hzP
      have hx₀_p : x₀ ∈ S_p := Finset.mem_coe.mp hx₀_mem
      have hx₀_pol : (x₀ : ℂ) ∈ hb.poles := (Finset.mem_filter.mp hx₀_p).2
      let Qx : Set ℂ := Pset \ {(x₀ : ℂ)}
      have hQx_closed : IsClosed Qx := (hP_fin.subset Set.sdiff_subset).isClosed
      have hU_nhds : U \ Qx ∈ 𝓝 (x₀ : ℂ) :=
        (hU.sdiff hQx_closed).mem_nhds ⟨hzU, fun h => h.2 rfl⟩
      -- (w - x₀) * (b w - Sn w) → 0 as w → x₀, w ≠ x₀
      have hlim_zero : Tendsto (fun w : ℂ => (w - (x₀ : ℂ)) * (b w - Sn w)) (𝓝[≠] (x₀ : ℂ)) (𝓝 0) := by
        have hrem_an : AnalyticAt ℂ (fun w : ℂ => ∑ x ∈ S_p.erase x₀, hb.res (x : ℂ) / (w - (x : ℂ))) (x₀ : ℂ) := by
          refine Finset.analyticAt_fun_sum _ fun x hx => ?_
          refine analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
          intro h0
          have hxe : x₀ = x := Complex.ofReal_injective (sub_eq_zero.mp h0)
          exact (Finset.mem_erase.mp hx).1 hxe.symm
        have hlim_other : Tendsto (fun w : ℂ => (w - (x₀ : ℂ)) *
            ∑ x ∈ S_p.erase x₀, hb.res (x : ℂ) / (w - (x : ℂ))) (𝓝[≠] (x₀ : ℂ)) (𝓝 0) := by
          have hsub0 : Tendsto (fun w : ℂ => w - (x₀ : ℂ)) (𝓝[≠] (x₀ : ℂ)) (𝓝 0) := by
            have hc : ContinuousAt (fun w : ℂ => w - (x₀ : ℂ)) (x₀ : ℂ) :=
              continuousAt_id.sub continuousAt_const
            simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(x₀ : ℂ)}ᶜ))
          have hrem_lim : Tendsto (fun w : ℂ => ∑ x ∈ S_p.erase x₀, hb.res (x : ℂ) / (w - (x : ℂ)))
              (𝓝[≠] (x₀ : ℂ)) (𝓝 (∑ x ∈ S_p.erase x₀, hb.res (x : ℂ) / ((x₀ : ℂ) - (x : ℂ)))) :=
            hrem_an.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(x₀ : ℂ)}ᶜ))
          simpa using hsub0.mul hrem_lim
        have hlim_main : Tendsto (fun w : ℂ => (w - (x₀ : ℂ)) * b w - hb.res (x₀ : ℂ))
            (𝓝[≠] (x₀ : ℂ)) (𝓝 0) := by
          simpa using (hb.simple_pole (x₀ : ℂ) hx₀_pol).sub_const (hb.res (x₀ : ℂ))
        have hdiff_lim : Tendsto (fun w : ℂ => ((w - (x₀ : ℂ)) * b w - hb.res (x₀ : ℂ)) -
            (w - (x₀ : ℂ)) * ∑ x ∈ S_p.erase x₀, hb.res (x : ℂ) / (w - (x : ℂ)))
            (𝓝[≠] (x₀ : ℂ)) (𝓝 0) := by
          simpa using hlim_main.sub hlim_other
        refine hdiff_lim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ (x₀ : ℂ))
        have hsub_ne : w - (x₀ : ℂ) ≠ 0 := sub_ne_zero.mpr hw
        have hSn_split : Sn w = hb.res (x₀ : ℂ) / (w - (x₀ : ℂ)) +
            ∑ x ∈ S_p.erase x₀, hb.res (x : ℂ) / (w - (x : ℂ)) :=
          (Finset.add_sum_erase S_p (fun x => hb.res (x : ℂ) / (w - (x : ℂ))) hx₀_p).symm
        rw [hSn_split]
        field_simp [hsub_ne]
        ring
      have hlo : (fun w : ℂ => (b w - Sn w) - (b (x₀ : ℂ) - Sn (x₀ : ℂ))) =o[𝓝[≠] (x₀ : ℂ)]
          fun w : ℂ => (w - (x₀ : ℂ))⁻¹ := by
        rw [Asymptotics.isLittleO_iff_tendsto']
        · have hconst0 : Tendsto (fun w : ℂ => (w - (x₀ : ℂ)) * (b (x₀ : ℂ) - Sn (x₀ : ℂ)))
              (𝓝[≠] (x₀ : ℂ)) (𝓝 0) := by
            have hc : ContinuousAt (fun w : ℂ => (w - (x₀ : ℂ)) * (b (x₀ : ℂ) - Sn (x₀ : ℂ))) (x₀ : ℂ) :=
              (continuousAt_id.sub continuousAt_const).mul continuousAt_const
            simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(x₀ : ℂ)}ᶜ))
          have hsub_lim : Tendsto (fun w : ℂ => (w - (x₀ : ℂ)) * (b w - Sn w) -
              (w - (x₀ : ℂ)) * (b (x₀ : ℂ) - Sn (x₀ : ℂ))) (𝓝[≠] (x₀ : ℂ)) (𝓝 0) := by
            simpa using hlim_zero.sub hconst0
          refine hsub_lim.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with w _
          rw [div_inv_eq_mul]; ring
        · filter_upwards [self_mem_nhdsWithin] with w hw h0
          exact absurd (inv_eq_zero.mp h0) (sub_ne_zero.mpr hw)
      have hupd_diff := Complex.differentiableOn_update_limUnder_of_isLittleO (f := fun w => b w - Sn w)
        hU_nhds (fun w hw => ?_) hlo
      · have hupd_an : AnalyticAt ℂ (Function.update (fun w => b w - Sn w) (x₀ : ℂ)
            (Filter.limUnder (𝓝[≠] (x₀ : ℂ)) (fun w => b w - Sn w))) (x₀ : ℂ) :=
          (hupd_diff.analyticOnNhd (hU.sdiff hQx_closed)) (x₀ : ℂ) ⟨hzU, fun h => h.2 rfl⟩
        refine hupd_an.congr ?_
        filter_upwards [hU_nhds] with w hw
        by_cases hwe : w = (x₀ : ℂ)
        · subst hwe; simp [ψ, Pset, hx₀_p]
        · have hwP : w ∉ Pset := fun h => hw.2 ⟨h, hwe⟩
          simp [ψ, hwP, hwe]
      · have hw_ne : w ≠ (x₀ : ℂ) := hw.2
        have hwP : w ∉ Pset := fun h => hw.1.2 ⟨h, hw_ne⟩
        exact ((hb.analyticOn w (hU_sdiff ⟨hw.1.1, hwP⟩)).sub
          (hSn_an w ⟨hw.1.1, hwP⟩)).differentiableAt.differentiableWithinAt
    · have hnhds : U \ Pset ∈ 𝓝 z := (hU.sdiff hP_closed).mem_nhds ⟨hzU, hzP⟩
      refine ((hb.analyticOn z (hU_sdiff ⟨hzU, hzP⟩)).sub (hSn_an z ⟨hzU, hzP⟩)).congr ?_
      filter_upwards [hnhds] with w hw
      simp [ψ, hw.2]
  -- Vertical connector bound: b is continuous on the compact segment {T + y * I : y ∈ [-mT, mT]}
  have hvert_in : ∀ y ∈ Icc (-m * T) (m * T), ((T : ℂ) + (y : ℂ) * I) ∈ U \ Pset := by
    intro y hy
    refine ⟨hsub ⟨by simp [hT.le], by simp, ?_⟩, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, Complex.add_im, Complex.ofReal_im, Complex.mul_im, mul_one,
        zero_add]
      exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · rintro ⟨x, hx, heq⟩
      have hre := congrArg Complex.re heq
      simp at hre
      have hxlt := (hS_in x (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1).2
      linarith
  have hvert_cont : ContinuousOn (fun y : ℝ => (-((T : ℂ) + (y : ℂ) * I)) ^ j * b ((T : ℂ) + (y : ℂ) * I))
      (Icc (-m * T) (m * T)) :=
    ((by fun_prop : Continuous fun y : ℝ => (-((T : ℂ) + (y : ℂ) * I)) ^ j).continuousOn).mul
      (hb.analyticOn.continuousOn.comp (by fun_prop : Continuous fun y : ℝ => (T : ℂ) + (y : ℂ) * I).continuousOn
        (fun y hy => hU_sdiff (hvert_in y hy)))
  obtain ⟨M_v, hMv_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hvert_cont
  let Mv : ℝ := max M_v 0
  have hMv_nn : 0 ≤ Mv := le_max_right _ _
  refine ⟨Mv * (2 * m * T), by positivity, fun u hu => ?_⟩
  -- Evaluate triIntegral of (-w)^j * exp(-w u) * b(w) on closedTri T m
  let Fkern (w : ℂ) : ℂ := (-w) ^ j * Complex.exp (-w * (u : ℂ)) * b w
  let Fψ (w : ℂ) : ℂ := (-w) ^ j * Complex.exp (-w * (u : ℂ)) * ψ w
  let termX (x : ℝ) (w : ℂ) : ℂ :=
    (-w) ^ j * Complex.exp (-w * (u : ℂ)) * (hb.res (x : ℂ) / (w - (x : ℂ)))
  have hFψ_an : AnalyticOnNhd ℂ Fψ U :=
    ((analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)).mul hψ_an
  have htri_ψ : triIntegral Fψ T m = 0 :=
    triIntegral_eq_zero_of_analyticOn hT.le hm.le hU hsub hFψ_an
  have htri_term : ∀ x ∈ S_p,
      triIntegral (termX x) T m =
        2 * (Real.pi : ℂ) * I * hb.res (x : ℂ) * (-(x : ℂ)) ^ j * Complex.exp (-(x : ℂ) * (u : ℂ)) := by
    intro x hx
    have hx_in := hS_in x (Finset.mem_filter.mp hx).1
    have h_av := triBd_avoid_real_FC hx_in.1 hx_in.2 hm
    let g (w : ℂ) : ℂ := (-w) ^ j * Complex.exp (-w * (u : ℂ)) * hb.res (x : ℂ)
    have hg_an : AnalyticOnNhd ℂ g univ :=
      ((analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)).mul
        analyticOnNhd_const
    have hdslope_an : AnalyticOnNhd ℂ (dslope g (x : ℂ)) univ :=
      ((Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 (x : ℂ))).mpr
        hg_an.differentiableOn).analyticOnNhd isOpen_univ
    have htri_slope : triIntegral (dslope g (x : ℂ)) T m = 0 :=
      triIntegral_eq_zero_of_analyticOn hT.le hm.le isOpen_univ (subset_univ _) hdslope_an
    have htri_inv : triIntegral (fun w => g (x : ℂ) * (w - (x : ℂ))⁻¹) T m =
        g (x : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [triIntegral_const_mul_FC, triIntegral_inv_sub hx_in.1 hx_in.2 hm]
    have hsplit : ∀ w : ℂ, w ≠ (x : ℂ) → termX x w = dslope g (x : ℂ) w + g (x : ℂ) * (w - (x : ℂ))⁻¹ := by
      intro w hw
      have hsl := sub_smul_dslope g (x : ℂ) w
      rw [smul_eq_mul] at hsl
      have hne : w - (x : ℂ) ≠ 0 := sub_ne_zero.mpr hw
      dsimp only [termX, g]
      have h1 : (-w) ^ j * Complex.exp (-w * (u : ℂ)) * (hb.res (x : ℂ) / (w - (x : ℂ))) =
          g w / (w - (x : ℂ)) := by dsimp only [g]; ring
      rw [h1, ← sub_add_cancel (g w) (g (x : ℂ)), ← hsl, add_div, mul_div_cancel_left₀ _ hne,
        div_eq_mul_inv]
    have hslope_int : TriBdIntFC (dslope g (x : ℂ)) T m :=
      triBdInt_of_continuousOn_FC hT.le hm.le
        (hdslope_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
        (hdslope_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
        (hdslope_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
    have hinv_int : TriBdIntFC (fun w => g (x : ℂ) * (w - (x : ℂ))⁻¹) T m :=
      triBdInt_of_continuousOn_FC hT.le hm.le
        (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun t h0 =>
          h_av.1 t (sub_eq_zero.mp h0))))
        (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y h0 =>
          h_av.2.2 y (sub_eq_zero.mp h0))))
        (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun t h0 =>
          h_av.2.1 t (sub_eq_zero.mp h0))))
    have hcongr := triIntegral_congr_FC (F := termX x)
      (G := fun w => dslope g (x : ℂ) w + g (x : ℂ) * (w - (x : ℂ))⁻¹) hT.le hm.le
      (fun t _ => hsplit _ (h_av.1 t))
      (fun y _ => hsplit _ (h_av.2.2 y))
      (fun t _ => hsplit _ (h_av.2.1 t))
    rw [hcongr, triIntegral_add_FC hslope_int hinv_int, htri_slope, zero_add, htri_inv]
    dsimp only [g]; ring
  -- Integrability of Fψ and termX on the triangle boundary
  have hmem_tri_minus : ∀ t ∈ Icc (0 : ℝ) T, (t : ℂ) * (1 - I * (m : ℂ)) ∈ U := fun t ht => by
    refine hsub ⟨by simp [Complex.mul_re, ht.1], by simp [Complex.mul_re, ht.2], ?_⟩
    have hre : ((t : ℂ) * (1 - I * (m : ℂ))).re = t := by simp [Complex.mul_re]
    have him : ((t : ℂ) * (1 - I * (m : ℂ))).im = -(t * m) := by simp [Complex.mul_im]
    rw [hre, him, abs_neg, abs_mul, abs_of_nonneg ht.1, abs_of_pos hm]; ring_nf; rfl
  have hmem_tri_plus : ∀ t ∈ Icc (0 : ℝ) T, (t : ℂ) * (1 + I * (m : ℂ)) ∈ U := fun t ht => by
    refine hsub ⟨by simp [Complex.mul_re, ht.1], by simp [Complex.mul_re, ht.2], ?_⟩
    have hre : ((t : ℂ) * (1 + I * (m : ℂ))).re = t := by simp [Complex.mul_re]
    have him : ((t : ℂ) * (1 + I * (m : ℂ))).im = t * m := by simp [Complex.mul_im]
    rw [hre, him, abs_mul, abs_of_nonneg ht.1, abs_of_pos hm]; ring_nf; rfl
  have hFψ_int : TriBdIntFC Fψ T m :=
    triBdInt_of_continuousOn_FC hT.le hm.le
      (hFψ_an.continuousOn.comp (by fun_prop) hmem_tri_minus)
      (hFψ_an.continuousOn.comp (by fun_prop) fun y hy => (hvert_in y hy).1)
      (hFψ_an.continuousOn.comp (by fun_prop) hmem_tri_plus)
  have hterm_int : ∀ x ∈ S_p, TriBdIntFC (termX x) T m := fun x hx => by
    have hx_in := hS_in x (Finset.mem_filter.mp hx).1
    have h_av := triBd_avoid_real_FC hx_in.1 hx_in.2 hm
    refine triBdInt_of_continuousOn_FC hT.le hm.le
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div (by fun_prop) fun t h0 => h_av.1 t (sub_eq_zero.mp h0))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div (by fun_prop) fun y h0 => h_av.2.2 y (sub_eq_zero.mp h0))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div (by fun_prop) fun t h0 => h_av.2.1 t (sub_eq_zero.mp h0))))
  have hsum_int : TriBdIntFC (fun w => ∑ x ∈ S_p, termX x w) T m := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun t : ℝ => (1 - I * (m : ℂ)) * ∑ x ∈ S_p, termX x ((t : ℂ) * (1 - I * (m : ℂ)))) =
          ∑ x ∈ S_p, fun t : ℝ => (1 - I * (m : ℂ)) * termX x ((t : ℂ) * (1 - I * (m : ℂ))) := by
        funext t; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun x hx => (hterm_int x hx).1
    · have heq : (fun y : ℝ => ∑ x ∈ S_p, termX x ((T : ℂ) + (y : ℂ) * I)) =
          ∑ x ∈ S_p, fun y : ℝ => termX x ((T : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun x hx => (hterm_int x hx).2.1
    · have heq : (fun t : ℝ => (1 + I * (m : ℂ)) * ∑ x ∈ S_p, termX x ((t : ℂ) * (1 + I * (m : ℂ)))) =
          ∑ x ∈ S_p, fun t : ℝ => (1 + I * (m : ℂ)) * termX x ((t : ℂ) * (1 + I * (m : ℂ))) := by
        funext t; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun x hx => (hterm_int x hx).2.2
  have hbd_notP : (∀ t ∈ Icc (0 : ℝ) T, (t : ℂ) * (1 - I * (m : ℂ)) ∉ Pset) ∧
      (∀ y ∈ Icc (-m * T) (m * T), (T : ℂ) + (y : ℂ) * I ∉ Pset) ∧
      (∀ t ∈ Icc (0 : ℝ) T, (t : ℂ) * (1 + I * (m : ℂ)) ∉ Pset) := by
    refine ⟨fun t _ ⟨x, hx, heq⟩ => ?_, fun y hy => (hvert_in y hy).2, fun t _ ⟨x, hx, heq⟩ => ?_⟩
    · have hx_in := hS_in x (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      exact (triBd_avoid_real_FC hx_in.1 hx_in.2 hm).1 t heq.symm
    · have hx_in := hS_in x (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      exact (triBd_avoid_real_FC hx_in.1 hx_in.2 hm).2.1 t heq.symm
  have hpt_eq : ∀ w : ℂ, w ∉ Pset → Fkern w = Fψ w + ∑ x ∈ S_p, termX x w := fun w hw => by
    dsimp only [Fkern, Fψ, ψ, termX, Sn]
    rw [ite_eq_right_iff.mpr (fun h => absurd h hw), ← Finset.mul_sum]
    ring
  have htri_eval : triIntegral Fkern T m =
      ∑ x ∈ S_ray, 2 * (Real.pi : ℂ) * I * hb.extRes (x : ℂ) *
        (-(x : ℂ)) ^ j * Complex.exp (-(x : ℂ) * (u : ℂ)) := by
    rw [triIntegral_congr_FC (F := Fkern) (G := fun w => Fψ w + ∑ x ∈ S_p, termX x w) hT.le hm.le
        (fun t ht => hpt_eq _ (hbd_notP.1 t ht))
        (fun y hy => hpt_eq _ (hbd_notP.2.1 y hy))
        (fun t ht => hpt_eq _ (hbd_notP.2.2 t ht)),
      triIntegral_add_FC hFψ_int hsum_int, htri_ψ, zero_add,
      triIntegral_sum_FC S_p termX T m hterm_int,
      Finset.sum_congr rfl htri_term]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold PlaneSimplePoleData.extRes
    split_ifs <;> ring
  -- Relate the two slanted sides of triIntegral Fkern T m to truncLaplace
  have hside_eq : ∀ c : ℂ,
      (∫ x : ℝ in (0 : ℝ)..T, c * Fkern ((x : ℂ) * c)) =
        truncLaplace (fun w => (-w) ^ j * b w) ((T : ℂ) * c) u := fun c => by
    unfold truncLaplace Fkern
    have hcomp := intervalIntegral.smul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := 1) (fun x : ℝ => c * ((-(x : ℂ) * c) ^ j *
        Complex.exp (-((x : ℂ) * c) * (u : ℂ)) * b ((x : ℂ) * c))) T
    rw [mul_zero, mul_one] at hcomp
    have hcomp' : (∫ x : ℝ in (0 : ℝ)..T, c * ((-((x : ℂ) * c)) ^ j *
        Complex.exp (-((x : ℂ) * c) * (u : ℂ)) * b ((x : ℂ) * c))) =
        (T : ℂ) * ∫ t : ℝ in (0 : ℝ)..1, c * ((-(((T * t : ℝ) : ℂ) * c)) ^ j *
          Complex.exp (-(((T * t : ℝ) : ℂ) * c) * (u : ℂ)) * b (((T * t : ℝ) : ℂ) * c)) := by
      have hsub := intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1) (fun x : ℝ => c * ((-((x : ℂ) * c)) ^ j *
          Complex.exp (-((x : ℂ) * c) * (u : ℂ)) * b ((x : ℂ) * c))) T
      rw [mul_zero, mul_one] at hsub
      exact hsub.symm
    rw [hcomp', intervalIntegral.integral_const_mul, ← mul_assoc]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    have harg : ((T * t : ℝ) : ℂ) * c = (t : ℂ) * ((T : ℂ) * c) := by push_cast; ring
    have hexp : -(((t : ℂ) * ((T : ℂ) * c)) * (u : ℂ)) = -(u : ℂ) * ((T : ℂ) * c) * (t : ℂ) := by ring
    rw [harg]
    have h2 : -((t : ℂ) * ((T : ℂ) * c)) * (u : ℂ) = -(u : ℂ) * ((T : ℂ) * c) * (t : ℂ) := by ring
    rw [h2]; ring
  have hdiff_conn : truncLaplace (fun w => (-w) ^ j * b w) ((T : ℂ) * (1 - I * (m : ℂ))) u -
      truncLaplace (fun w => (-w) ^ j * b w) ((T : ℂ) * (1 + I * (m : ℂ))) u -
      ∑ x ∈ S_ray, 2 * (Real.pi : ℂ) * I * hb.extRes (x : ℂ) *
        (-(x : ℂ)) ^ j * Complex.exp (-(x : ℂ) * (u : ℂ)) =
      -(I * ∫ y : ℝ in (-m * T)..(m * T), Fkern ((T : ℂ) + (y : ℂ) * I)) := by
    rw [← htri_eval]
    unfold triIntegral
    rw [hside_eq (1 - I * (m : ℂ)), hside_eq (1 + I * (m : ℂ))]
    ring
  rw [hdiff_conn, norm_neg, norm_mul, Complex.norm_I, one_mul]
  have hconn_bd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -m * T) (b := m * T) (C := Mv * Real.exp (-T * u))
    (f := fun y : ℝ => Fkern ((T : ℂ) + (y : ℂ) * I)) fun y hy => by
    rw [uIoc_of_le (by nlinarith : -m * T ≤ m * T)] at hy
    dsimp only [Fkern]
    have hrew : (-((T : ℂ) + (y : ℂ) * I)) ^ j *
          Complex.exp (-((T : ℂ) + (y : ℂ) * I) * (u : ℂ)) * b ((T : ℂ) + (y : ℂ) * I) =
        Complex.exp (-((T : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          ((-((T : ℂ) + (y : ℂ) * I)) ^ j * b ((T : ℂ) + (y : ℂ) * I)) := by ring
    rw [hrew, norm_mul, Complex.norm_exp]
    have hre : (-((T : ℂ) + (y : ℂ) * I) * (u : ℂ)).re = -T * u := by
      simp [Complex.mul_re]
    rw [hre]
    calc Real.exp (-T * u) * ‖(-((T : ℂ) + (y : ℂ) * I)) ^ j * b ((T : ℂ) + (y : ℂ) * I)‖
        ≤ Real.exp (-T * u) * Mv :=
          mul_le_mul_of_nonneg_left ((hMv_bd y ⟨hy.1.le, hy.2⟩).trans (le_max_left _ _))
            (Real.exp_pos _).le
      _ = Mv * Real.exp (-T * u) := mul_comm _ _
  have hlen : |(m * T) - (-m * T)| = 2 * m * T := by
    rw [show m * T - -m * T = 2 * m * T by ring, abs_of_pos (by positivity)]
  rw [hlen] at hconn_bd
  linarith

/-! ### 4. Minimal-Degree Descent, Rotation Pullback & Matrix Contradiction (Lemma 4) -/

/-- Directional derivative operator `D_vec_conv v Q = ∑ p, C (convC (v p)) * pderiv p Q` over `ℂ{w}`. -/
@[expose] def D_vec_conv {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (Q : MvPolynomial ι ConvergentPowerSeries) : MvPolynomial ι ConvergentPowerSeries :=
  ∑ p : ι, MvPolynomial.C (convC (v p)) * MvPolynomial.pderiv p Q

/-- Directional derivative operator `D_vec v P = ∑ p, C (v p) * pderiv p P` over `ℂ`. -/
@[expose] def D_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ p : ι, MvPolynomial.C (v p) * MvPolynomial.pderiv p P

lemma degree_pderiv_conv_lt {ι : Type*} [DecidableEq ι] (p : ι)
    (Q : MvPolynomial ι ConvergentPowerSeries) (hpos : 0 < Q.totalDegree) :
    (MvPolynomial.pderiv p Q).totalDegree < Q.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_lt_iff hpos |>.mpr fun α hα => ?_
  have hne : (MvPolynomial.pderiv p Q).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  rw [MvPolynomial.coeff_pderiv] at hne
  have hmem : α + Finsupp.single p 1 ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0; exact hne (by rw [h0, zero_mul])
  have hle : (α + Finsupp.single p 1).sum (fun _ e => e) ≤ Q.totalDegree :=
    MvPolynomial.le_totalDegree hmem
  have hsum : (α + Finsupp.single p 1).sum (fun _ e => e) = α.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl]
  omega

private lemma totalDegree_finset_sum_le {ι κ R : Type*} [CommSemiring R] (s : Finset κ)
    (f : κ → MvPolynomial ι R) :
    (∑ k ∈ s, f k).totalDegree ≤ s.sup (fun k => (f k).totalDegree) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sup_insert]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl ih)

lemma degree_D_vec_conv_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (Q : MvPolynomial ι ConvergentPowerSeries) (hpos : 0 < Q.totalDegree) :
    (D_vec_conv v Q).totalDegree < Q.totalDegree := by
  unfold D_vec_conv
  refine lt_of_le_of_lt (totalDegree_finset_sum_le _ _) ?_
  refine (Finset.sup_lt_iff hpos).mpr fun p _ => ?_
  calc (MvPolynomial.C (convC (v p)) * MvPolynomial.pderiv p Q).totalDegree
      ≤ (MvPolynomial.C (convC (v p))).totalDegree + (MvPolynomial.pderiv p Q).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = (MvPolynomial.pderiv p Q).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
    _ < Q.totalDegree := degree_pderiv_conv_lt p Q hpos

private lemma evalConv_convC_mul (c : ℂ) (a : ConvergentPowerSeries) (z : ℂ) :
    evalConv (convC c * a) z = c * evalConv a z := by
  unfold evalConv
  have hterm : ∀ n : ℕ, PowerSeries.coeff n (convC c * a).val * z ^ n =
      c * (PowerSeries.coeff n a.val * z ^ n) := fun n => by
    change PowerSeries.coeff n (PowerSeries.C c * a.val) * z ^ n = _
    rw [PowerSeries.coeff_C_mul]; ring
  simp_rw [hterm, tsum_mul_left]

lemma evalConvMvPolyGen_C_mul {ι : Type*} (c : ℂ)
    (Q : MvPolynomial ι ConvergentPowerSeries) (z : ℂ) :
    evalConvMvPolyGen (MvPolynomial.C (convC c) * Q) z =
      MvPolynomial.C c * evalConvMvPolyGen Q z := by
  ext α
  rw [evalConvMvPolyGen_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
    evalConvMvPolyGen_coeff, evalConv_convC_mul]

lemma evalConvMvPolyGen_sum_eventually {ι κ : Type*} (s : Finset κ)
    (f : κ → MvPolynomial ι ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPolyGen (∑ k ∈ s, f k) (u : ℂ)⁻¹ =
        ∑ k ∈ s, evalConvMvPolyGen (f k) (u : ℂ)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine Eventually.of_forall fun u => ?_
    ext α
    simp [evalConvMvPolyGen_coeff, evalConv_zero]
  | @insert k s hk ih =>
    filter_upwards [ih, evalConvMvPolyGen_add_eventually (f k) (∑ j ∈ s, f j)] with u hu hadd
    rw [Finset.sum_insert hk, hadd, hu, Finset.sum_insert hk]

lemma evalConvMvPolyGen_D_vec_conv_eventually {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (Q : MvPolynomial ι ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPolyGen (D_vec_conv v Q) (u : ℂ)⁻¹ =
        D_vec v (evalConvMvPolyGen Q (u : ℂ)⁻¹) := by
  unfold D_vec_conv D_vec
  filter_upwards [evalConvMvPolyGen_sum_eventually Finset.univ
    (fun p : ι => MvPolynomial.C (convC (v p)) * MvPolynomial.pderiv p Q)] with u hu
  rw [hu]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [evalConvMvPolyGen_C_mul, evalConvMvPolyGen_pderiv]

private lemma D_vec_C {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (c : ℂ) :
    D_vec v (MvPolynomial.C c : MvPolynomial ι ℂ) = 0 := by
  simp [D_vec]

private lemma D_vec_add {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (P Q : MvPolynomial ι ℂ) : D_vec v (P + Q) = D_vec v P + D_vec v Q := by
  unfold D_vec
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => by rw [map_add, mul_add]

private lemma D_vec_mul_X {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ)
    (P : MvPolynomial ι ℂ) (q : ι) :
    D_vec v (P * MvPolynomial.X q) = D_vec v P * MvPolynomial.X q + MvPolynomial.C (v q) * P := by
  unfold D_vec
  rw [Finset.sum_mul]
  have hterm : ∀ p : ι,
      MvPolynomial.C (v p) * MvPolynomial.pderiv p (P * MvPolynomial.X q) =
        MvPolynomial.C (v p) * MvPolynomial.pderiv p P * MvPolynomial.X q +
          if p = q then MvPolynomial.C (v q) * P else 0 := fun p => by
    rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
    by_cases hpq : p = q
    · subst hpq; simp; ring
    · have hqp : q ≠ p := fun h => hpq h.symm
      simp [hpq, hqp]; ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp

private lemma hasDerivAt_eval_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ) (x v : ι → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => MvPolynomial.eval (fun p => x p + s * v p) P)
      (MvPolynomial.eval (fun p => x p + t * v p) (D_vec v P)) t := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [D_vec_C, map_zero]
    simpa using hasDerivAt_const t c
  | add A B hA hB =>
    rw [D_vec_add, map_add]
    have hfn : (fun s : ℂ => MvPolynomial.eval (fun p => x p + s * v p) (A + B)) =
        fun s : ℂ => MvPolynomial.eval (fun p => x p + s * v p) A +
          MvPolynomial.eval (fun p => x p + s * v p) B := by funext s; simp
    rw [hfn]
    exact hA.add hB
  | mul_X A q hA =>
    rw [D_vec_mul_X, map_add, map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    have hX : HasDerivAt (fun s : ℂ => x q + s * v q) (v q) t := by
      simpa using ((hasDerivAt_id t).mul_const (v q)).const_add (x q)
    have hmul := hA.mul hX
    have hfn : (fun s : ℂ => MvPolynomial.eval (fun p => x p + s * v p) (A * MvPolynomial.X q)) =
        fun s : ℂ => MvPolynomial.eval (fun p => x p + s * v p) A * (x q + s * v q) := by
      funext s; simp
    rw [hfn]
    refine hmul.congr_deriv ?_
    ring

/-- **Exact Shift Invariance**: if `D_vec v P = 0` over `ℂ`, then `P(x + t v) = P(x)` identically. -/
theorem shift_invariant_of_D_vec_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (P : MvPolynomial ι ℂ) (hD : D_vec v P = 0)
    (x : ι → ℂ) (t : ℂ) :
    MvPolynomial.eval (fun p => x p + t * v p) P = MvPolynomial.eval x P := by
  let g : ℂ → ℂ := fun s => MvPolynomial.eval (fun p => x p + s * v p) P
  have hderiv : ∀ s : ℂ, HasDerivAt g 0 s := fun s => by
    simpa [hD] using hasDerivAt_eval_shift P x v s
  have hconst := is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0
  simpa [g] using hconst

/-- Finite-sum exact shift invariance for a `Finset` of vectors annihilating `P`. -/
theorem shift_invariant_finset_of_D_vec_eq_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset κ) (v : κ → ι → ℂ) (P : MvPolynomial ι ℂ)
    (hD : ∀ k ∈ S, D_vec (v k) P = 0) (c : κ → ℂ) (x : ι → ℂ) :
    MvPolynomial.eval (fun p => x p + ∑ k ∈ S, c k * v k p) P = MvPolynomial.eval x P := by
  classical
  induction S using Finset.induction_on generalizing x with
  | empty => simp
  | @insert k S hk ih =>
    have hD_k := hD k (Finset.mem_insert_self k S)
    have hD_S : ∀ j ∈ S, D_vec (v j) P = 0 := fun j hj => hD j (Finset.mem_insert_of_mem hj)
    have hrew : (fun p : ι => x p + ∑ j ∈ insert k S, c j * v j p) =
        fun p : ι => (x p + ∑ j ∈ S, c j * v j p) + c k * v k p := by
      funext p; rw [Finset.sum_insert hk]; ring
    rw [hrew, shift_invariant_of_D_vec_eq_zero (v k) P hD_k _ (c k), ih hD_S x]

private lemma eval_bdd_on_ball_gen {ι : Type*} (P : MvPolynomial ι ℂ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ι → ℂ, (∀ p, ‖x p‖ ≤ M) → ‖MvPolynomial.eval x P‖ ≤ B := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg c, fun _ _ => by simp⟩
  | add A B hA hB =>
    obtain ⟨BA, hBA, hAb⟩ := hA
    obtain ⟨BB, hBB, hBb⟩ := hB
    exact ⟨BA + BB, add_nonneg hBA hBB, fun x hx => by
      rw [map_add]; exact (norm_add_le _ _).trans (add_le_add (hAb x hx) (hBb x hx))⟩
  | mul_X A q hA =>
    obtain ⟨BA, hBA, hAb⟩ := hA
    exact ⟨BA * M, mul_nonneg hBA hM, fun x hx => by
      rw [map_mul, MvPolynomial.eval_X, norm_mul]
      exact mul_le_mul (hAb x hx) (hx q) (norm_nonneg _) hBA⟩

private lemma eval_shift_taylor_bound_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x v : ι → ℂ) (a : ℂ),
      (∀ p, ‖x p‖ ≤ M) → (∀ p, ‖v p‖ ≤ M) → ‖a‖ ≤ 1 →
      ‖MvPolynomial.eval (fun p => x p + a * v p) P - MvPolynomial.eval x P -
        a * MvPolynomial.eval x (D_vec v P)‖ ≤ C * ‖a‖ ^ 2 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, le_rfl, fun x v a _ _ _ => ?_⟩
    simp [D_vec_C]
  | add A B hA hB =>
    obtain ⟨CA, hCA, hAb⟩ := hA
    obtain ⟨CB, hCB, hBb⟩ := hB
    refine ⟨CA + CB, add_nonneg hCA hCB, fun x v a hx hv ha => ?_⟩
    rw [map_add, map_add, D_vec_add, map_add]
    have hsplit : MvPolynomial.eval (fun p => x p + a * v p) A +
          MvPolynomial.eval (fun p => x p + a * v p) B -
          (MvPolynomial.eval x A + MvPolynomial.eval x B) -
          a * (MvPolynomial.eval x (D_vec v A) + MvPolynomial.eval x (D_vec v B)) =
        (MvPolynomial.eval (fun p => x p + a * v p) A - MvPolynomial.eval x A -
          a * MvPolynomial.eval x (D_vec v A)) +
        (MvPolynomial.eval (fun p => x p + a * v p) B - MvPolynomial.eval x B -
          a * MvPolynomial.eval x (D_vec v B)) := by ring
    rw [hsplit]
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ CA * ‖a‖ ^ 2 + CB * ‖a‖ ^ 2 := add_le_add (hAb x v a hx hv ha) (hBb x v a hx hv ha)
      _ = (CA + CB) * ‖a‖ ^ 2 := by ring
  | mul_X A q hA =>
    obtain ⟨CA, hCA, hAb⟩ := hA
    choose Bp hBp_nn hBp using fun p : ι => eval_bdd_on_ball_gen (MvPolynomial.pderiv p A) hM
    let B_der : ℝ := ∑ p : ι, Bp p * M
    have hB_der : 0 ≤ B_der := Finset.sum_nonneg fun p _ => mul_nonneg (hBp_nn p) hM
    refine ⟨CA * (2 * M) + B_der * M, by positivity, fun x v a hx hv ha => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, map_mul, MvPolynomial.eval_X, D_vec_mul_X, map_add,
      map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    have hsplit : MvPolynomial.eval (fun p => x p + a * v p) A * (x q + a * v q) -
          MvPolynomial.eval x A * x q -
          a * (MvPolynomial.eval x (D_vec v A) * x q + v q * MvPolynomial.eval x A) =
        (MvPolynomial.eval (fun p => x p + a * v p) A - MvPolynomial.eval x A -
          a * MvPolynomial.eval x (D_vec v A)) * (x q + a * v q) +
        a ^ 2 * (MvPolynomial.eval x (D_vec v A) * v q) := by ring
    rw [hsplit]
    have hxq : ‖x q + a * v q‖ ≤ 2 * M := by
      calc ‖x q + a * v q‖ ≤ ‖x q‖ + ‖a * v q‖ := norm_add_le _ _
        _ = ‖x q‖ + ‖a‖ * ‖v q‖ := by rw [norm_mul]
        _ ≤ M + 1 * M := add_le_add (hx q) (mul_le_mul ha (hv q) (norm_nonneg _) zero_le_one)
        _ = 2 * M := by ring
    have hDv : ‖MvPolynomial.eval x (D_vec v A)‖ ≤ B_der := by
      unfold D_vec
      rw [map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [map_mul, MvPolynomial.eval_C, norm_mul]
      calc ‖v p‖ * ‖MvPolynomial.eval x (MvPolynomial.pderiv p A)‖
          ≤ M * Bp p := mul_le_mul (hv p) (hBp p x hx) (norm_nonneg _) hM
        _ = Bp p * M := mul_comm _ _
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ = ‖MvPolynomial.eval (fun p => x p + a * v p) A - MvPolynomial.eval x A -
            a * MvPolynomial.eval x (D_vec v A)‖ * ‖x q + a * v q‖ +
          ‖a‖ ^ 2 * (‖MvPolynomial.eval x (D_vec v A)‖ * ‖v q‖) := by
          rw [norm_mul, norm_mul, norm_pow, norm_mul]
      _ ≤ (CA * ‖a‖ ^ 2) * (2 * M) + ‖a‖ ^ 2 * (B_der * M) :=
          add_le_add (mul_le_mul (hAb x v a hx hv ha) hxq (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left (mul_le_mul hDv (hv q) (norm_nonneg _) hB_der) (sq_nonneg _))
      _ = (CA * (2 * M) + B_der * M) * ‖a‖ ^ 2 := by ring

/-- **Positive-Real-Ray Induction (Codex Lemma 4, real-axis core)**:
If `Qmin` is a minimal-total-degree nonzero relation for `b : Fin d → ℂ → ℂ`, then for every
positive real pole `s > 0` with `(s : ℂ) ∈ unionPoles h`, we have
`D_vec_conv (jointVec h (s : ℂ)) Qmin = 0`. -/
private theorem D_vec_conv_eq_zero_of_pos_real_pole {d r : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i))
    (Qmin : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries)
    (hQmin_pos : 0 < Qmin.totalDegree)
    (hQmin_zero : formalEvalConvJoint (fun i => formalSeries (b i)) Qmin = 0)
    (hQmin_min : ∀ P : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries,
      P ≠ 0 → P.totalDegree < Qmin.totalDegree →
      formalEvalConvJoint (fun i => formalSeries (b i)) P ≠ 0)
    {s_max : ℝ} (_hs_max : 0 < s_max) :
    ∀ x : ℝ, 0 < x → x ≤ s_max → (x : ℂ) ∈ unionPoles h →
      D_vec_conv (jointVec h (x : ℂ)) Qmin = 0 := by
  classical
  -- Enumerate the finitely many real poles in (0, s_max] in strictly increasing order
  have hfin_box := finite_on_closedBall_unionPoles h s_max
  let S_all : Finset ℝ :=
    (hfin_box.toFinset.filter (fun w => 0 < w.re ∧ w.re ≤ s_max ∧ w.im = 0)).image Complex.re
  have hS_mem : ∀ x : ℝ, x ∈ S_all ↔ 0 < x ∧ x ≤ s_max ∧ (x : ℂ) ∈ unionPoles h := fun x => by
    simp only [S_all, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨w, ⟨⟨_, hwP⟩, hre0, hres, him0⟩, rfl⟩
      have heq : (w.re : ℂ) = w := Complex.ext rfl (by simp [him0])
      exact ⟨hre0, hres, heq.symm ▸ hwP⟩
    · rintro ⟨hx0, hxs, hxP⟩
      refine ⟨(x : ℂ), ⟨⟨?_, hxP⟩, by simpa using hx0, by simpa using hxs, by simp⟩, by simp⟩
      rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]; exact hxs
  -- Induct on the number of elements of S_all strictly less than x
  suffices hstrong : ∀ N : ℕ, ∀ x ∈ S_all, (S_all.filter (· < x)).card = N →
      D_vec_conv (jointVec h (x : ℂ)) Qmin = 0 by
    intro x hx0 hxs hxP
    exact hstrong _ x ((hS_mem x).mpr ⟨hx0, hxs, hxP⟩) rfl
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro s hs_mem hcard
    have hs_spec := (hS_mem s).mp hs_mem
    have hs_pos : 0 < s := hs_spec.1
    have hprev_D : ∀ x ∈ S_all, x < s → D_vec_conv (jointVec h (x : ℂ)) Qmin = 0 := by
      intro x hx_mem hxs
      have hsub : S_all.filter (· < x) ⊂ S_all.filter (· < s) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨x, Finset.mem_filter.mpr ⟨hx_mem, hxs⟩, by simp⟩
        · intro y hy
          rw [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, lt_trans hy.2 hxs⟩
      have hlt_card : (S_all.filter (· < x)).card < N := hcard ▸ Finset.card_lt_card hsub
      exact ih _ hlt_card x hx_mem rfl
    -- Construct the finite narrow triangle geometry for target radius s
    obtain ⟨T, T', m, m', ε, S_ray, hs_lt_T, hT_lt_T', hm_pos, hm_lt_m', hε_pos, hε_lt_T',
      hS_ray_iff, htri_sub, htri_poles, hdisj_plus, hdisj_minus, hz_plus_mem, hz_minus_mem⟩ :=
      exists_finite_triangle_geometry h hs_pos
    have hT_pos : 0 < T := lt_trans hs_pos hs_lt_T
    have hT'_pos : 0 < T' := lt_trans hT_pos hT_lt_T'
    let zP : ℂ := (T : ℂ) * (1 + I * (m : ℂ))
    let zM : ℂ := (T : ℂ) * (1 - I * (m : ℂ))
    have hzP_re : zP.re = T := by simp [zP, Complex.mul_re]
    have hzM_re : zM.re = T := by simp [zM, Complex.mul_re]
    let UP : Set ℂ := finiteWedgePlus m' ε T'
    let UM : Set ℂ := finiteWedgeMinus m' ε T'
    let UTri : Set ℂ := finiteWedgeTri m' ε T'
    have hUP_dom : Domain UP := finiteWedgePlus_domain hε_pos hT'_pos
    have hUM_dom : Domain UM := finiteWedgeMinus_domain hε_pos hT'_pos
    have h0P : (0 : ℂ) ∈ UP := ⟨Or.inl (by simpa [Metric.mem_ball] using hε_pos), by simpa using hT'_pos⟩
    have h0M : (0 : ℂ) ∈ UM := ⟨Or.inl (by simpa [Metric.mem_ball] using hε_pos), by simpa using hT'_pos⟩
    have hbP : ∀ i : Fin d, AnalyticOnNhd ℂ (b i) UP := fun i =>
      (h i).analyticOn.mono fun w hw hpol =>
        Set.disjoint_left.mp hdisj_plus hw (Set.mem_iUnion.mpr ⟨i, hpol⟩)
    have hbM : ∀ i : Fin d, AnalyticOnNhd ℂ (b i) UM := fun i =>
      (h i).analyticOn.mono fun w hw hpol =>
        Set.disjoint_left.mp hdisj_minus hw (Set.mem_iUnion.mpr ⟨i, hpol⟩)
    -- Step A: Finite-contour transfer on both flanking segments zP and zM
    obtain ⟨KP, hKP_nn, hQP_bd⟩ := finite_contour_transfer_joint hUP_dom h0P hz_plus_mem
      (hzP_re.symm ▸ hT_pos) hbP Qmin hQmin_zero
    obtain ⟨KM, hKM_nn, hQM_bd⟩ := finite_contour_transfer_joint hUM_dom h0M hz_minus_mem
      (hzM_re.symm ▸ hT_pos) hbM Qmin hQmin_zero
    -- Step B: Simple-pole triangle residue jump for each (i, j)
    have hjump_each : ∀ p : Fin d × Fin (r + 1),
        ∃ C_p : ℝ, 0 ≤ C_p ∧ ∀ u : ℝ, 0 ≤ u →
          ‖truncJet b zM u p - truncJet b zP u p -
            ∑ x ∈ S_ray, (2 * (Real.pi : ℂ) * I * Complex.exp (-(x : ℂ) * (u : ℂ))) *
              jointVec h (x : ℂ) p‖ ≤ C_p * Real.exp (-T * u) := by
      intro p
      have hU_pol_i : UTri ∩ (h p.1).poles ⊆ (fun x : ℝ => (x : ℂ)) '' (S_ray : Set ℝ) := by
        rw [← htri_poles]
        exact Set.inter_subset_inter_right UTri (Set.subset_iUnion (fun i => (h i).poles) p.1)
      have hS_in : ∀ x ∈ S_ray, 0 < x ∧ x < T := fun x hx =>
        ⟨((hS_ray_iff x).mp hx).1, lt_of_le_of_lt ((hS_ray_iff x).mp hx).2.1 hs_lt_T⟩
      obtain ⟨C_p, hCp_nn, hCp_bd⟩ := finite_triangle_simple_pole_jump (h p.1) hT_pos hm_pos
        (isOpen_finiteWedgeTri m' ε T') htri_sub hS_in hU_pol_i p.2.val
      refine ⟨C_p, hCp_nn, fun u hu => ?_⟩
      have hrew := hCp_bd u hu
      rw [← truncJet_eq_truncLaplace b zM u p, ← truncJet_eq_truncLaplace b zP u p] at hrew
      refine (le_of_eq ?_).trans hrew
      congr 2
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold jointVec; ring
    choose C_jp hCjp_nn hCjp_bd using hjump_each
    let C_rem : ℝ := ∑ p : Fin d × Fin (r + 1), C_jp p
    have hCrem_nn : 0 ≤ C_rem := Finset.sum_nonneg fun p _ => hCjp_nn p
    have hCjp_le : ∀ p, C_jp p ≤ C_rem := fun p =>
      Finset.single_le_sum (fun q _ => hCjp_nn q) (Finset.mem_univ p)
    -- Step C: Uniform bounds on truncJet b zP u, truncJet b zM u, jointVec, and coefficients of Qmin
    have hs_in_Sray : s ∈ S_ray := (hS_ray_iff s).mpr ⟨hs_pos, le_rfl, hs_spec.2.2⟩
    let S_prev : Finset ℝ := S_ray.erase s
    have hSprev_sub : ∀ x ∈ S_prev, x ∈ S_all ∧ x < s := fun x hx => by
      have hne : x ≠ s := (Finset.mem_erase.mp hx).1
      have hspec := (hS_ray_iff x).mp (Finset.mem_erase.mp hx).2
      exact ⟨(hS_mem x).mpr ⟨hspec.1, hspec.2.1.trans hs_spec.2.1, hspec.2.2⟩,
        lt_of_le_of_ne hspec.2.1 hne⟩
    have hseg_bd_P : ∀ p : Fin d × Fin (r + 1),
        ∃ BP : ℝ, 0 ≤ BP ∧ ∀ u : ℝ, 0 ≤ u → ‖truncJet b zP u p‖ ≤ BP := fun p => by
      have hc := continuousOn_segment_of_analyticOn hUP_dom hz_plus_mem
        (minor_jetIter_analyticOn (hbP p.1) p.2.val)
      obtain ⟨Mp, hMp, hMp_bd⟩ := exists_segment_bound hc
      refine ⟨‖(Minor.jet^[p.2.val] ⟨0, b p.1⟩).atom‖ + ‖zP‖ * Mp, by positivity, fun u hu => ?_⟩
      exact truncVal_norm_le (hzP_re.symm ▸ hT_pos.le) hu hMp hMp_bd
    have hseg_bd_M : ∀ p : Fin d × Fin (r + 1),
        ∃ BM : ℝ, 0 ≤ BM ∧ ∀ u : ℝ, 0 ≤ u → ‖truncJet b zM u p‖ ≤ BM := fun p => by
      have hc := continuousOn_segment_of_analyticOn hUM_dom hz_minus_mem
        (minor_jetIter_analyticOn (hbM p.1) p.2.val)
      obtain ⟨Mm, hMm, hMm_bd⟩ := exists_segment_bound hc
      refine ⟨‖(Minor.jet^[p.2.val] ⟨0, b p.1⟩).atom‖ + ‖zM‖ * Mm, by positivity, fun u hu => ?_⟩
      exact truncVal_norm_le (hzM_re.symm ▸ hT_pos.le) hu hMm hMm_bd
    choose BP hBP_nn hBP_bd using hseg_bd_P
    choose BM hBM_nn hBM_bd using hseg_bd_M
    let M_vec : ℝ := ∑ x ∈ S_ray, ∑ p : Fin d × Fin (r + 1), ‖jointVec h (x : ℂ) p‖
    let M : ℝ := 1 + (∑ p, BP p) + (∑ p, BM p) + (2 * Real.pi) * M_vec + C_rem
    have hM_nn : 0 ≤ M := by
      have h1 : 0 ≤ ∑ p, BP p := Finset.sum_nonneg fun p _ => hBP_nn p
      have h2 : 0 ≤ ∑ p, BM p := Finset.sum_nonneg fun p _ => hBM_nn p
      have h3 : 0 ≤ M_vec := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have h4 : 0 ≤ 2 * Real.pi := by positivity
      dsimp only [M]; nlinarith
    -- Uniform coefficient bounds for Qmin
    choose Bc hBc_ev using fun β : (Fin d × Fin (r + 1)) →₀ ℕ => evalConv_eventually_bdd (Qmin.coeff β)
    have hBc_all : ∀ᶠ u : ℝ in atTop, ∀ β ∈ Qmin.support,
        ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹‖ ≤ max (Bc β) 0 := by
      rw [Filter.eventually_all_finset]
      intro β _
      filter_upwards [(hBc_ev β).2] with u hu
      exact hu.trans (le_max_left _ _)
    -- Monomial-wise Lipschitz and Taylor constants
    choose C_lip_β hClip_nn hClip_β using fun β : (Fin d × Fin (r + 1)) →₀ ℕ =>
      eval_lipschitz_of_bounded (MvPolynomial.monomial β (1 : ℂ)) hM_nn
    choose C_tay_β hCtay_nn hCtay_β using fun β : (Fin d × Fin (r + 1)) →₀ ℕ =>
      eval_shift_taylor_bound_gen (MvPolynomial.monomial β (1 : ℂ)) hM_nn
    let C_L : ℝ := ∑ β ∈ Qmin.support, max (Bc β) 0 * C_lip_β β
    let C_T : ℝ := ∑ β ∈ Qmin.support, max (Bc β) 0 * C_tay_β β
    have hCL_nn : 0 ≤ C_L := Finset.sum_nonneg fun β _ => mul_nonneg (le_max_right _ _) (hClip_nn β)
    have hCT_nn : 0 ≤ C_T := Finset.sum_nonneg fun β _ => mul_nonneg (le_max_right _ _) (hCtay_nn β)
    -- Eventual shift-invariance equations for all x ∈ S_prev
    have hprev_ev : ∀ᶠ u : ℝ in atTop, ∀ x ∈ S_prev,
        D_vec (jointVec h (x : ℂ)) (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) = 0 := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hD0 : D_vec_conv (jointVec h (x : ℂ)) Qmin = 0 :=
        hprev_D x (hSprev_sub x hx).1 (hSprev_sub x hx).2
      filter_upwards [evalConvMvPolyGen_D_vec_conv_eventually (jointVec h (x : ℂ)) Qmin] with u hu
      rw [← hu, hD0]
      ext α; simp [evalConvMvPolyGen_coeff, evalConv_zero]
    -- Choose exponential decay margin δ := min (T - s) s > 0
    let δ : ℝ := min (T - s) s
    have hδ_pos : 0 < δ := lt_min (sub_pos.mpr hs_lt_T) hs_pos
    have h2pi_pos : 0 < 2 * Real.pi := by positivity
    -- Bound on ‖eval (truncJet b zP u) (evalConvMvPolyGen (D_vec_conv (jointVec h s) Qmin) u⁻¹)‖
    let C_fin : ℝ := (KP + KM + C_L * C_rem) / (2 * Real.pi) + C_T * (2 * Real.pi)
    have hD_decay : ∀ᶠ u : ℝ in atTop,
        ‖MvPolynomial.eval (truncJet b zP u)
          (evalConvMvPolyGen (D_vec_conv (jointVec h (s : ℂ)) Qmin) (u : ℂ)⁻¹)‖ ≤
          C_fin * Real.exp (-δ * u) := by
      -- Choose u large enough that 2π * exp(-s * u) ≤ 1
      have ha_small : ∀ᶠ u : ℝ in atTop, 2 * Real.pi * Real.exp (-s * u) ≤ 1 := by
        have hlim : Tendsto (fun u : ℝ => 2 * Real.pi * Real.exp (-s * u)) atTop (𝓝 0) := by
          have h1 : Tendsto (fun u : ℝ => Real.exp (-s * u)) atTop (𝓝 0) :=
            Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hs_pos) tendsto_id)
          simpa using h1.const_mul (2 * Real.pi)
        exact hlim.eventually (Iic_mem_nhds one_pos)
      filter_upwards [hQP_bd, hQM_bd, hBc_all, hprev_ev,
        evalConvMvPolyGen_D_vec_conv_eventually (jointVec h (s : ℂ)) Qmin,
        ha_small, eventually_ge_atTop (0 : ℝ)] with u huP huM huBc huprev huDs hua1 hu0
      rw [hzP_re] at huP
      rw [hzM_re] at huM
      let xP : Fin d × Fin (r + 1) → ℂ := truncJet b zP u
      let xM : Fin d × Fin (r + 1) → ℂ := truncJet b zM u
      let a : ℂ := 2 * (Real.pi : ℂ) * I * Complex.exp (-(s : ℂ) * (u : ℂ))
      let vs : Fin d × Fin (r + 1) → ℂ := jointVec h (s : ℂ)
      let y_ex : Fin d × Fin (r + 1) → ℂ := fun p =>
        xP p + ∑ x ∈ S_ray, (2 * (Real.pi : ℂ) * I * Complex.exp (-(x : ℂ) * (u : ℂ))) *
          jointVec h (x : ℂ) p
      let y_s : Fin d × Fin (r + 1) → ℂ := fun p => xP p + a * vs p
      have ha_norm : ‖a‖ = 2 * Real.pi * Real.exp (-s * u) := by
        dsimp only [a]
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_exp]
        congr 2; simp
      have ha_pos : 0 < ‖a‖ := by rw [ha_norm]; positivity
      have ha_le1 : ‖a‖ ≤ 1 := by rw [ha_norm]; exact hua1
      -- Coordinate bounds ≤ M for xP, xM, y_ex, vs
      have hxP_le : ∀ p, ‖xP p‖ ≤ M := fun p => by
        have h1 := hBP_bd p u hu0
        have h2 : BP p ≤ ∑ q, BP q := Finset.single_le_sum (fun q _ => hBP_nn q) (Finset.mem_univ p)
        have h3 : 0 ≤ ∑ q, BM q := Finset.sum_nonneg fun q _ => hBM_nn q
        have h4 : 0 ≤ M_vec := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        dsimp only [M]; nlinarith [Real.pi_pos]
      have hxM_le : ∀ p, ‖xM p‖ ≤ M := fun p => by
        have h1 := hBM_bd p u hu0
        have h2 : BM p ≤ ∑ q, BM q := Finset.single_le_sum (fun q _ => hBM_nn q) (Finset.mem_univ p)
        have h3 : 0 ≤ ∑ q, BP q := Finset.sum_nonneg fun q _ => hBP_nn q
        have h4 : 0 ≤ M_vec := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        dsimp only [M]; nlinarith [Real.pi_pos]
      have hvs_le : ∀ p, ‖vs p‖ ≤ M := fun p => by
        have h1 : ‖vs p‖ ≤ ∑ q, ‖jointVec h (s : ℂ) q‖ :=
          Finset.single_le_sum (fun q _ => norm_nonneg _) (Finset.mem_univ p)
        have h2 : (∑ q : Fin d × Fin (r + 1), ‖jointVec h (s : ℂ) q‖) ≤ M_vec := by
          change (∑ q : Fin d × Fin (r + 1), ‖jointVec h (s : ℂ) q‖) ≤
            ∑ x ∈ S_ray, ∑ q : Fin d × Fin (r + 1), ‖jointVec h (x : ℂ) q‖
          exact Finset.single_le_sum (f := fun x : ℝ => ∑ q : Fin d × Fin (r + 1), ‖jointVec h (x : ℂ) q‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hs_in_Sray
        have h3 : 0 ≤ ∑ q, BP q := Finset.sum_nonneg fun q _ => hBP_nn q
        have h4 : 0 ≤ ∑ q, BM q := Finset.sum_nonneg fun q _ => hBM_nn q
        have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        dsimp only [M]; nlinarith [norm_nonneg (vs p)]
      have hyex_le : ∀ p, ‖y_ex p‖ ≤ M := fun p => by
        have hsum_bd : ‖∑ x ∈ S_ray, (2 * (Real.pi : ℂ) * I * Complex.exp (-(x : ℂ) * (u : ℂ))) *
            jointVec h (x : ℂ) p‖ ≤ 2 * Real.pi * M_vec := by
          calc ‖∑ x ∈ S_ray, _‖ ≤ ∑ x ∈ S_ray, ‖(2 * (Real.pi : ℂ) * I * Complex.exp (-(x : ℂ) * (u : ℂ))) *
                jointVec h (x : ℂ) p‖ := norm_sum_le _ _
            _ ≤ ∑ x ∈ S_ray, (2 * Real.pi) * ∑ q, ‖jointVec h (x : ℂ) q‖ := by
                refine Finset.sum_le_sum fun x hx => ?_
                have hx0 : 0 < x := ((hS_ray_iff x).mp hx).1
                rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
                  Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_exp]
                have hexp1 : Real.exp ((-(x : ℂ) * (u : ℂ)).re) ≤ 1 := by
                  have hre : (-(x : ℂ) * (u : ℂ)).re = -x * u := by simp
                  rw [hre]; exact Real.exp_le_one_iff.mpr (by nlinarith)
                have hq : ‖jointVec h (x : ℂ) p‖ ≤ ∑ q, ‖jointVec h (x : ℂ) q‖ :=
                  Finset.single_le_sum (fun q _ => norm_nonneg _) (Finset.mem_univ p)
                calc 2 * Real.pi * Real.exp ((-(x : ℂ) * (u : ℂ)).re) * ‖jointVec h (x : ℂ) p‖
                    ≤ 2 * Real.pi * 1 * ∑ q, ‖jointVec h (x : ℂ) q‖ := by
                      refine mul_le_mul (mul_le_mul_of_nonneg_left hexp1 (by positivity)) hq (norm_nonneg _) (by positivity)
                  _ = 2 * Real.pi * ∑ q, ‖jointVec h (x : ℂ) q‖ := by ring
            _ = 2 * Real.pi * M_vec := by rw [← Finset.mul_sum]
        have h1 := hBP_bd p u hu0
        have h2 : BP p ≤ ∑ q, BP q := Finset.single_le_sum (fun q _ => hBP_nn q) (Finset.mem_univ p)
        have h3 : 0 ≤ ∑ q, BM q := Finset.sum_nonneg fun q _ => hBM_nn q
        calc ‖y_ex p‖ ≤ ‖xP p‖ + ‖∑ x ∈ S_ray, _‖ := norm_add_le _ _
          _ ≤ BP p + 2 * Real.pi * M_vec := add_le_add h1 hsum_bd
          _ ≤ M := by dsimp only [M]; linarith
      -- Lipschitz comparison between xM and y_ex
      have hQ_decomp : evalConvMvPolyGen Qmin (u : ℂ)⁻¹ =
          ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ • MvPolynomial.monomial β (1 : ℂ) := by
        unfold evalConvMvPolyGen
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      have hlip_diff : ‖MvPolynomial.eval y_ex (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            MvPolynomial.eval xM (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)‖ ≤
          C_L * C_rem * Real.exp (-T * u) := by
        rw [hQ_decomp, map_sum, map_sum, ← Finset.sum_sub_distrib]
        calc ‖∑ β ∈ Qmin.support, _‖
            ≤ ∑ β ∈ Qmin.support, ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                (MvPolynomial.eval y_ex (MvPolynomial.monomial β 1) -
                  MvPolynomial.eval xM (MvPolynomial.monomial β 1))‖ := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
              simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
              rw [← mul_sub]
          _ ≤ ∑ β ∈ Qmin.support, max (Bc β) 0 * (C_lip_β β * (C_rem * Real.exp (-T * u))) := by
              refine Finset.sum_le_sum fun β hβ => ?_
              rw [norm_mul]
              have hδp : ∀ p, ‖y_ex p - xM p‖ ≤ C_rem * Real.exp (-T * u) := fun p => by
                have hb := hCjp_bd p u hu0
                rw [show y_ex p - xM p = -(xM p - xP p - ∑ x ∈ S_ray, (2 * (Real.pi : ℂ) * I *
                    Complex.exp (-(x : ℂ) * (u : ℂ))) * jointVec h (x : ℂ) p) by dsimp only [y_ex]; ring,
                  norm_neg]
                exact hb.trans (mul_le_mul_of_nonneg_right (hCjp_le p) (Real.exp_pos _).le)
              have hβl := hClip_β β y_ex xM (C_rem * Real.exp (-T * u)) (by positivity) hyex_le hxM_le hδp
              exact mul_le_mul (huBc β hβ) hβl (norm_nonneg _) (le_max_right _ _)
          _ = C_L * C_rem * Real.exp (-T * u) := by
              have hCL_eq : C_L * C_rem * Real.exp (-T * u) =
                  ∑ β ∈ Qmin.support, max (Bc β) 0 * (C_lip_β β * (C_rem * Real.exp (-T * u))) := by
                show (∑ β ∈ Qmin.support, max (Bc β) 0 * C_lip_β β) * C_rem * Real.exp (-T * u) = _
                rw [Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun β _ => by ring
              exact hCL_eq.symm
      -- Exact shift invariance eliminates all x ∈ S_prev: eval y_ex Q = eval y_s Q
      have hshift_eq : MvPolynomial.eval y_ex (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) =
          MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) := by
        have hy_split : y_ex = fun p => y_s p + ∑ x ∈ S_prev,
            (2 * (Real.pi : ℂ) * I * Complex.exp (-(x : ℂ) * (u : ℂ))) * jointVec h (x : ℂ) p := by
          funext p
          dsimp only [y_ex, y_s, a, vs, S_prev]
          rw [← Finset.add_sum_erase S_ray _ hs_in_Sray]
          ring
        rw [hy_split]
        exact shift_invariant_finset_of_D_vec_eq_zero S_prev (fun x => jointVec h (x : ℂ))
          (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) huprev _ y_s
      -- Combine with huM to get ‖eval y_s Q‖ ≤ (KM + C_L * C_rem) * exp(-T * u)
      have hys_bd : ‖MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)‖ ≤
          (KM + C_L * C_rem) * Real.exp (-T * u) := by
        rw [← hshift_eq]
        calc ‖MvPolynomial.eval y_ex (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)‖
            = ‖(MvPolynomial.eval y_ex (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
                MvPolynomial.eval xM (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)) +
                MvPolynomial.eval xM (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)‖ := by congr 1; ring
          _ ≤ ‖MvPolynomial.eval y_ex (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
                MvPolynomial.eval xM (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)‖ +
              ‖MvPolynomial.eval xM (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)‖ := norm_add_le _ _
          _ ≤ C_L * C_rem * Real.exp (-T * u) + KM * Real.exp (-T * u) := add_le_add hlip_diff huM
          _ = (KM + C_L * C_rem) * Real.exp (-T * u) := by ring
      -- Taylor expansion of evalConvMvPolyGen Qmin u⁻¹ at xP in direction a * vs
      have htay_bd : ‖MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            MvPolynomial.eval xP (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            a * MvPolynomial.eval xP (D_vec vs (evalConvMvPolyGen Qmin (u : ℂ)⁻¹))‖ ≤
          C_T * ‖a‖ ^ 2 := by
        have hD_decomp : D_vec vs (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) =
            ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ •
              D_vec vs (MvPolynomial.monomial β (1 : ℂ)) := by
          unfold D_vec
          rw [hQ_decomp]
          have hpd : ∀ p, MvPolynomial.pderiv p
              (∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ • MvPolynomial.monomial β (1 : ℂ)) =
              ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ •
                MvPolynomial.pderiv p (MvPolynomial.monomial β (1 : ℂ)) := fun p => by
            rw [map_sum]
            exact Finset.sum_congr rfl fun β _ => Derivation.map_smul_of_tower _ _ _
          simp_rw [hpd, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]; ring
        rw [hD_decomp, hQ_decomp, map_sum, map_sum, map_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        calc ‖∑ β ∈ Qmin.support, _‖
            ≤ ∑ β ∈ Qmin.support, ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                (MvPolynomial.eval y_s (MvPolynomial.monomial β 1) -
                  MvPolynomial.eval xP (MvPolynomial.monomial β 1) -
                  a * MvPolynomial.eval xP (D_vec vs (MvPolynomial.monomial β 1)))‖ := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
              simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
              exact le_of_eq (congrArg norm (by ring))
          _ ≤ ∑ β ∈ Qmin.support, max (Bc β) 0 * (C_tay_β β * ‖a‖ ^ 2) := by
              refine Finset.sum_le_sum fun β hβ => ?_
              rw [norm_mul]
              exact mul_le_mul (huBc β hβ) (hCtay_β β xP vs a hxP_le hvs_le ha_le1)
                (norm_nonneg _) (le_max_right _ _)
          _ = C_T * ‖a‖ ^ 2 := by
              dsimp only [C_T]; rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun β _ => by ring
      -- Isolate ‖a‖ * ‖eval xP (evalConvMvPolyGen (D_vec_conv vs Qmin) u⁻¹)‖ and divide by ‖a‖
      rw [huDs]
      have hprod_bd : ‖a‖ * ‖MvPolynomial.eval xP (D_vec vs (evalConvMvPolyGen Qmin (u : ℂ)⁻¹))‖ ≤
          (KP + KM + C_L * C_rem) * Real.exp (-T * u) + C_T * ‖a‖ ^ 2 := by
        rw [← norm_mul]
        have hid : a * MvPolynomial.eval xP (D_vec vs (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)) =
            MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            MvPolynomial.eval xP (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            (MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
              MvPolynomial.eval xP (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
              a * MvPolynomial.eval xP (D_vec vs (evalConvMvPolyGen Qmin (u : ℂ)⁻¹))) := by ring
        rw [hid]
        have htri1 := norm_sub_le
          (MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            MvPolynomial.eval xP (evalConvMvPolyGen Qmin (u : ℂ)⁻¹))
          (MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            MvPolynomial.eval xP (evalConvMvPolyGen Qmin (u : ℂ)⁻¹) -
            a * MvPolynomial.eval xP (D_vec vs (evalConvMvPolyGen Qmin (u : ℂ)⁻¹)))
        have htri2 := norm_sub_le
          (MvPolynomial.eval y_s (evalConvMvPolyGen Qmin (u : ℂ)⁻¹))
          (MvPolynomial.eval xP (evalConvMvPolyGen Qmin (u : ℂ)⁻¹))
        linarith [hys_bd, huP, htay_bd]
      have hdiv := (le_div_iff₀' ha_pos).mpr hprod_bd
      have hdiv_simp : ‖MvPolynomial.eval xP (D_vec vs (evalConvMvPolyGen Qmin (u : ℂ)⁻¹))‖ ≤
          ((KP + KM + C_L * C_rem) * Real.exp (-T * u)) / ‖a‖ + C_T * ‖a‖ := by
        refine hdiv.trans_eq ?_
        field_simp [ha_pos.ne']
      refine hdiv_simp.trans ?_
      rw [ha_norm]
      have hterm1 : ((KP + KM + C_L * C_rem) * Real.exp (-T * u)) / (2 * Real.pi * Real.exp (-s * u)) ≤
          ((KP + KM + C_L * C_rem) / (2 * Real.pi)) * Real.exp (-δ * u) := by
        have hrew : ((KP + KM + C_L * C_rem) * Real.exp (-T * u)) / (2 * Real.pi * Real.exp (-s * u)) =
            ((KP + KM + C_L * C_rem) / (2 * Real.pi)) * Real.exp (-(T - s) * u) := by
          have hexp : Real.exp (-T * u) / Real.exp (-s * u) = Real.exp (-(T - s) * u) := by
            rw [← Real.exp_sub]; congr 1; ring
          rw [← hexp]; ring
        rw [hrew]
        have hδ1 : δ ≤ T - s := min_le_left _ _
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
      have hterm2 : C_T * (2 * Real.pi * Real.exp (-s * u)) ≤ (C_T * (2 * Real.pi)) * Real.exp (-δ * u) := by
        have hδ2 : δ ≤ s := min_le_right _ _
        calc C_T * (2 * Real.pi * Real.exp (-s * u))
            = (C_T * (2 * Real.pi)) * Real.exp (-s * u) := by ring
          _ ≤ (C_T * (2 * Real.pi)) * Real.exp (-δ * u) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
      dsimp only [C_fin]
      linarith
    -- Step D: Exponential flatness forces formalEvalConvJoint (D_vec_conv vs Qmin) = 0, contradicting minimality!
    have hD_formal : formalEvalConvJoint (fun i => formalSeries (b i))
        (D_vec_conv (jointVec h (s : ℂ)) Qmin) = 0 :=
      formalEvalConvJoint_eq_zero_of_exp_decay hUP_dom h0P hz_plus_mem
        (hzP_re.symm ▸ hT_pos) hbP (D_vec_conv (jointVec h (s : ℂ)) Qmin) hδ_pos hD_decay
    by_contra hD_ne
    exact hQmin_min (D_vec_conv (jointVec h (s : ℂ)) Qmin) hD_ne
      (degree_D_vec_conv_lt (jointVec h (s : ℂ)) Qmin hQmin_pos) hD_formal

/-! #### 4B. Rotation Automorphism & Arbitrary Complex Pole Pullback -/

/-- Rotate a `PlaneSimplePoleData b` by nonzero `μ : ℂ`: `b_rot(z) = b(μ * z)`. -/
def PlaneSimplePoleData.rotate {b : ℂ → ℂ} (h : PlaneSimplePoleData b) {μ : ℂ} (hμ : μ ≠ 0) :
    PlaneSimplePoleData (fun z => b (μ * z)) where
  poles := {w : ℂ | μ * w ∈ h.poles}
  res := fun w => μ⁻¹ * h.res (μ * w)
  zero_not_mem := by simpa using h.zero_not_mem
  finite_on_closedBall R := by
    have hfin := h.finite_on_closedBall (‖μ‖ * R)
    have hsub : (fun w => μ * w) '' (Metric.closedBall (0 : ℂ) R ∩ {w : ℂ | μ * w ∈ h.poles}) ⊆
        Metric.closedBall (0 : ℂ) (‖μ‖ * R) ∩ h.poles := by
      rintro _ ⟨w, ⟨hwR, hwP⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hwR
      exact ⟨by rw [Metric.mem_closedBall, dist_zero_right, norm_mul]; exact mul_le_mul_of_nonneg_left hwR (norm_nonneg μ), hwP⟩
    exact (hfin.subset hsub).of_finite_image (fun a _ b _ hab => mul_left_cancel₀ hμ hab)
  analyticOn z hz := by
    have hmul : AnalyticAt ℂ (fun w : ℂ => μ * w) z := analyticAt_const.mul analyticAt_id
    exact (h.analyticOn (μ * z) hz).comp hmul
  res_ne_zero ω hω := mul_ne_zero (inv_ne_zero hμ) (h.res_ne_zero (μ * ω) hω)
  simple_pole ω hω := by
    have htend_mul : Tendsto (fun z : ℂ => μ * z) (𝓝[≠] ω) (𝓝[≠] (μ * ω)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(continuousAt_const.mul continuousAt_id).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ ω)
      exact fun heq => hz (mul_left_cancel₀ hμ heq)
    have h1 := ((h.simple_pole (μ * ω) hω).comp htend_mul).const_mul μ⁻¹
    refine h1.congr fun z => ?_
    change μ⁻¹ * ((μ * z - μ * ω) * b (μ * z)) = (z - ω) * b (μ * z)
    have hfac : μ * z - μ * ω = μ * (z - ω) := by ring
    rw [hfac, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]

/-- Degree-preserving rotation ring endomorphism on `MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries`:
`a(w) ↦ a(μ * w)` and `X (i, j) ↦ μ^{j+1} X (i, j)`. -/
@[expose] def rotConvPolyGen {d r : ℕ} (μ : ℂ) :
    MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries →+*
      MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (rescaleConv μ))
    (fun p : Fin d × Fin (r + 1) => MvPolynomial.C (convC (μ ^ (p.2.val + 1))) * MvPolynomial.X p)

private lemma rotConvPolyGen_coeff {d r : ℕ} (μ : ℂ)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries)
    (α : (Fin d × Fin (r + 1)) →₀ ℕ) :
    (rotConvPolyGen μ Q).coeff α =
      rescaleConv μ (Q.coeff α) * convC (α.prod fun p e => (μ ^ (p.2.val + 1)) ^ e) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial β a =>
    change (MvPolynomial.eval₂ (MvPolynomial.C.comp (rescaleConv μ))
        (fun p => MvPolynomial.C (convC (μ ^ (p.2.val + 1))) * MvPolynomial.X p)
        (MvPolynomial.monomial β a)).coeff α = _
    rw [MvPolynomial.eval₂_monomial, RingHom.comp_apply]
    have hprod : β.prod (fun (p : Fin d × Fin (r + 1)) (e : ℕ) =>
          (MvPolynomial.C (convC (μ ^ (p.2.val + 1))) * MvPolynomial.X p) ^ e) =
        MvPolynomial.C (convC (β.prod fun p e => (μ ^ (p.2.val + 1)) ^ e)) * MvPolynomial.monomial β 1 := by
      have h1 : ∀ (p : Fin d × Fin (r + 1)) (e : ℕ),
          (MvPolynomial.C (convC (μ ^ (p.2.val + 1))) * MvPolynomial.X p) ^ e =
          MvPolynomial.C (convC ((μ ^ (p.2.val + 1)) ^ e)) * MvPolynomial.X p ^ e := fun p e => by
        rw [mul_pow, ← map_pow]
        congr 2; apply Subtype.ext; simp [convC]
      simp_rw [Finsupp.prod, h1, Finset.prod_mul_distrib]
      congr 1
      · rw [← map_prod]; congr 1; apply toPS_injective
        rw [map_prod]
        change (∏ x ∈ β.support, PowerSeries.C ((μ ^ (x.2.val + 1)) ^ β x)) =
          PowerSeries.C (∏ x ∈ β.support, (μ ^ (x.2.val + 1)) ^ β x)
        rw [map_prod]
      · simp [MvPolynomial.monomial_eq]
    rw [hprod, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add A B hA hB =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply,
      hA, hB, map_add, add_mul]

private lemma rotConvPolyGen_injective {d r : ℕ} {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Injective (rotConvPolyGen (d := d) (r := r) μ) := by
  intro A B hAB
  apply MvPolynomial.ext
  intro α
  have hc := congrArg (fun P => P.coeff α) hAB
  rw [rotConvPolyGen_coeff, rotConvPolyGen_coeff] at hc
  have hprod_ne : (α.prod fun p e => (μ ^ (p.2.val + 1)) ^ e) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (pow_ne_zero _ hμ)
  have hconv_ne : convC (α.prod fun p e => (μ ^ (p.2.val + 1)) ^ e) ≠ 0 := fun h0 =>
    hprod_ne (by simpa [convC] using congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 0 a.val) h0)
  have hres : rescaleConv μ (A.coeff α) = rescaleConv μ (B.coeff α) :=
    mul_right_cancel₀ hconv_ne hc
  apply Subtype.ext
  ext n
  have hn := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff n a.val) hres
  simp only [rescaleConv, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    PowerSeries.coeff_rescale] at hn
  exact mul_left_cancel₀ (pow_ne_zero n hμ) hn

private lemma rotConvPolyGen_totalDegree {d r : ℕ} {μ : ℂ} (hμ : μ ≠ 0)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries) :
    (rotConvPolyGen μ Q).totalDegree = Q.totalDegree := by
  have hsupp : (rotConvPolyGen μ Q).support = Q.support := by
    ext α
    simp only [MvPolynomial.mem_support_iff, rotConvPolyGen_coeff]
    have hprod_ne : (α.prod fun p e => (μ ^ (p.2.val + 1)) ^ e) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (pow_ne_zero _ hμ)
    have hconv_ne : convC (α.prod fun p e => (μ ^ (p.2.val + 1)) ^ e) ≠ 0 := fun h0 =>
      hprod_ne (by simpa [convC] using congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 0 a.val) h0)
    have hres_zero : ∀ a : ConvergentPowerSeries, rescaleConv μ a = 0 ↔ a = 0 := fun a => by
      constructor
      · intro h0
        apply Subtype.ext; ext n
        have hn := congrArg (fun x : ConvergentPowerSeries => PowerSeries.coeff n x.val) h0
        simp only [rescaleConv, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          PowerSeries.coeff_rescale, Subring.coe_zero, map_zero] at hn
        exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero n hμ)
      · rintro rfl; exact map_zero _
    rw [ne_eq, mul_eq_zero, hres_zero, or_iff_left hconv_ne]
  simp only [MvPolynomial.totalDegree, hsupp]

private lemma rotConvPolyGen_comp_inv {d r : ℕ} {μ : ℂ} (hμ : μ ≠ 0)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries) :
    rotConvPolyGen μ (rotConvPolyGen μ⁻¹ Q) = Q := by
  ext α
  rw [rotConvPolyGen_coeff, rotConvPolyGen_coeff, map_mul]
  have hres_inv : rescaleConv μ (rescaleConv μ⁻¹ (Q.coeff α)) = Q.coeff α := by
    apply Subtype.ext; ext n
    simp only [rescaleConv, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      PowerSeries.coeff_rescale]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hμ, one_pow, one_mul]
  have hres_C : ∀ c : ℂ, rescaleConv μ (convC c) = convC c := fun c => by
    apply Subtype.ext; ext n
    cases n <;> simp [rescaleConv, convC, PowerSeries.coeff_rescale]
  rw [hres_inv, hres_C, mul_assoc]
  have hprod1 : convC (α.prod fun p e => (μ⁻¹ ^ (p.2.val + 1)) ^ e) *
      convC (α.prod fun p e => (μ ^ (p.2.val + 1)) ^ e) = 1 := by
    apply Subtype.ext
    change PowerSeries.C _ * PowerSeries.C _ = 1
    rw [← map_mul]
    have hmul1 : (α.prod fun p e => (μ⁻¹ ^ (p.2.val + 1)) ^ e) *
        (α.prod fun p e => (μ ^ (p.2.val + 1)) ^ e) = 1 := by
      simp only [Finsupp.prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun p _ => ?_
      rw [← mul_pow, ← mul_pow, inv_mul_cancel₀ hμ, one_pow, one_pow]
    rw [hmul1, map_one]
  rw [hprod1, mul_one]

private lemma iteratedDeriv_comp_const_mul_zero_FC {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (μ : ℂ) (k : ℕ) :
    iteratedDeriv k (fun z => φ (μ * z)) 0 = μ ^ k * iteratedDeriv k φ 0 := by
  have hloc : ∀ m : ℕ, ∀ᶠ z in 𝓝 (0 : ℂ),
      iteratedDeriv m (fun w => φ (μ * w)) z = μ ^ m * iteratedDeriv m φ (μ * z) := fun m => by
    induction m with
    | zero => exact Eventually.of_forall fun _ => by simp
    | succ m ih =>
      have hdm_anal : AnalyticAt ℂ (iteratedDeriv m φ) 0 := by
        clear ih
        induction m generalizing φ with
        | zero => simpa using hφ
        | succ j ihj => rw [iteratedDeriv_succ']; exact ihj hφ.deriv
      have hcont : ContinuousAt (fun z : ℂ => μ * z) 0 := continuousAt_const.mul continuousAt_id
      have hdm_diff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (iteratedDeriv m φ) (μ * z) := by
        have this' := hdm_anal.eventually_analyticAt
        rw [show (0 : ℂ) = μ * 0 by ring] at this'
        exact (hcont.tendsto.eventually this').mono fun z hz => hz.differentiableAt
      filter_upwards [ih.eventually_nhds, hdm_diff] with z hzeq hzdiff
      rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hzeq]
      have hchain : HasDerivAt (fun w => μ ^ m * iteratedDeriv m φ (μ * w))
          (μ ^ m * (deriv (iteratedDeriv m φ) (μ * z) * μ)) z :=
        (hzdiff.hasDerivAt.comp z (((hasDerivAt_id z).const_mul μ).congr_deriv (mul_one μ))).const_mul (μ ^ m)
      rw [hchain.deriv, iteratedDeriv_succ]; ring
  simpa using (hloc k).self_of_nhds

private lemma d_u_iter_formalSeries_rot_FC {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    {μ : ℂ} (hμ : μ ≠ 0) (j : ℕ) :
    d_u^[j] (formalSeries (fun z => φ (μ * z))) =
      PowerSeries.C (μ⁻¹ ^ (j + 1)) * PowerSeries.rescale μ (d_u^[j] (formalSeries φ)) := by
  have hC_du : ∀ (c : ℂ) (S : PowerSeries ℂ), d_u (PowerSeries.C c * S) = PowerSeries.C c * d_u S := by
    intro c S; ext n
    cases n with
    | zero => simp [d_u]
    | succ n =>
      cases n with
      | zero => simp [d_u, PowerSeries.coeff_X_pow_mul']
      | succ m =>
        simp only [d_u, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
        split_ifs with h
        · simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]; ring
        · simp
  have hres_du : ∀ S : PowerSeries ℂ,
      d_u (PowerSeries.rescale μ S) = PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (d_u S) := by
    intro S; ext n
    cases n with
    | zero =>
      change -(PowerSeries.coeff 0 (PowerSeries.X ^ 2 * PowerSeries.derivative (PowerSeries.rescale μ S))) =
        PowerSeries.coeff 0 (PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_neg,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']; simp
    | succ n =>
      cases n with
      | zero =>
        change -(PowerSeries.coeff 1 (PowerSeries.X ^ 2 * PowerSeries.derivative (PowerSeries.rescale μ S))) =
          PowerSeries.coeff 1 (PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_neg,
          PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']; simp
      | succ m =>
        change -(PowerSeries.coeff (m + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative (PowerSeries.rescale μ S))) =
          PowerSeries.coeff (m + 2) (PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_neg,
          PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
        split_ifs with hle2
        · simp only [Nat.add_sub_cancel, PowerSeries.coeff_derivative, PowerSeries.coeff_rescale]
          rw [show m + 2 = (m + 1) + 1 by omega, pow_succ']
          field_simp [hμ]; ring
        · omega
  have h0 : formalSeries (fun z => φ (μ * z)) =
      PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (formalSeries φ) := by
    ext n
    cases n with
    | zero => simp [formalSeries]
    | succ k =>
      simp only [formalSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
      rw [iteratedDeriv_comp_const_mul_zero_FC hφ μ k, pow_succ']
      field_simp [hμ]
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      hC_du, hres_du, ← mul_assoc, ← map_mul, ← pow_succ]

private lemma formalEvalConvJoint_rot {d r : ℕ} {b : Fin d → ℂ → ℂ}
    (hb0 : ∀ i, AnalyticAt ℂ (b i) 0) {μ : ℂ} (hμ : μ ≠ 0)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries) :
    formalEvalConvJoint (fun i => formalSeries (fun z => b i (μ * z))) (rotConvPolyGen μ Q) =
      PowerSeries.rescale μ (formalEvalConvJoint (fun i => formalSeries (b i)) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp [formalEvalConvJoint, rotConvPolyGen, rescaleConv]
  | add A B hA hB =>
    simp only [map_add, formalEvalConvJoint, MvPolynomial.eval₂_add] at hA hB ⊢
    rw [hA, hB]
  | mul_X A p hA =>
    simp only [map_mul, formalEvalConvJoint, MvPolynomial.eval₂_mul] at hA ⊢
    rw [hA]
    congr 1
    simp only [rotConvPolyGen, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    rw [d_u_iter_formalSeries_rot_FC (hb0 p.1) hμ p.2.val]
    change PowerSeries.C (μ ^ (p.2.val + 1)) * (PowerSeries.C (μ⁻¹ ^ (p.2.val + 1)) * _) = _
    rw [← mul_assoc, ← map_mul, ← mul_pow, mul_inv_cancel₀ hμ, one_pow, map_one, one_mul]

private lemma rotConvPolyGen_D_vec_conv {d r : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i)) {ω : ℂ} (hω_ne : ω ≠ 0)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries) :
    let s : ℝ := ‖ω‖
    let μ : ℂ := ω / (s : ℂ)
    have hμ : μ ≠ 0 := div_ne_zero hω_ne (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hω_ne).ne')
    D_vec_conv (jointVec (fun i => (h i).rotate hμ) (s : ℂ)) (rotConvPolyGen μ Q) =
      rotConvPolyGen μ (D_vec_conv (jointVec h ω) Q) := by
  intro s μ hμ
  have hμs : μ * (s : ℂ) = ω := div_mul_cancel₀ ω (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hω_ne).ne')
  have hvec_mul : ∀ p : Fin d × Fin (r + 1),
      jointVec (fun i => (h i).rotate hμ) (s : ℂ) p * μ ^ (p.2.val + 1) = jointVec h ω p := fun p => by
    unfold jointVec PlaneSimplePoleData.extRes PlaneSimplePoleData.rotate
    dsimp only
    have hmem_iff : (s : ℂ) ∈ {w : ℂ | μ * w ∈ (h p.1).poles} ↔ ω ∈ (h p.1).poles := by
      simp [hμs]
    rw [hμs]
    by_cases hp : ω ∈ (h p.1).poles
    · have hp' : (s : ℂ) ∈ {w : ℂ | μ * w ∈ (h p.1).poles} := hmem_iff.mpr hp
      simp only [hp, hp', ↓reduceIte]
      have hpow : (-(s : ℂ)) ^ p.2.val * μ ^ (p.2.val + 1) = μ * (-ω) ^ p.2.val := by
        rw [pow_succ', ← mul_assoc, mul_comm ((-(s : ℂ)) ^ p.2.val) μ, mul_assoc, ← mul_pow]
        have h1 : -(s : ℂ) * μ = -ω := by rw [← hμs]; ring
        rw [h1]
      calc μ⁻¹ * (h p.1).res ω * (-(s : ℂ)) ^ p.2.val * μ ^ (p.2.val + 1)
          = μ⁻¹ * (h p.1).res ω * ((-(s : ℂ)) ^ p.2.val * μ ^ (p.2.val + 1)) := by ring
        _ = μ⁻¹ * (h p.1).res ω * (μ * (-ω) ^ p.2.val) := by rw [hpow]
        _ = (μ⁻¹ * μ) * ((h p.1).res ω * (-ω) ^ p.2.val) := by ring
        _ = (h p.1).res ω * (-ω) ^ p.2.val := by rw [inv_mul_cancel₀ hμ, one_mul]
    · have hp' : (s : ℂ) ∉ {w : ℂ | μ * w ∈ (h p.1).poles} := fun h0 => hp (hmem_iff.mp h0)
      simp [hp, hp']
  apply MvPolynomial.ext
  intro α
  unfold D_vec_conv
  rw [map_sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv, rotConvPolyGen_coeff, map_mul]
  -- Evaluate LHS and RHS at α
  have hLHS : convC (jointVec (fun i => (h i).rotate hμ) (s : ℂ) p) *
        (rescaleConv μ (Q.coeff (α + Finsupp.single p 1)) *
          convC ((α + Finsupp.single p 1).prod fun q e => (μ ^ (q.2.val + 1)) ^ e) *
          ((α p : ConvergentPowerSeries) + 1)) =
      rescaleConv μ (Q.coeff (α + Finsupp.single p 1) * ((α p : ConvergentPowerSeries) + 1)) *
        convC (jointVec h ω p * (α.prod fun q e => (μ ^ (q.2.val + 1)) ^ e)) := by
    have hprod_add : ((α + Finsupp.single p 1).prod fun q e => (μ ^ (q.2.val + 1)) ^ e) =
        (α.prod fun q e => (μ ^ (q.2.val + 1)) ^ e) * μ ^ (p.2.val + 1) := by
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_single_index (h := fun (q : Fin d × Fin (r + 1)) (e : ℕ) => (μ ^ (q.2.val + 1)) ^ e)
          (pow_zero _), pow_one]
    have hres_nat : rescaleConv μ ((α p : ConvergentPowerSeries) + 1) =
        ((α p : ConvergentPowerSeries) + 1) := by
      rw [map_add, map_natCast, map_one]
    have hCmul : ∀ x y : ℂ, convC (x * y) = convC x * convC y := fun x y => by
      apply Subtype.ext; simp [convC, map_mul]
    rw [hprod_add, map_mul (rescaleConv μ), hres_nat, hCmul, hCmul, ← hvec_mul p, hCmul]
    ring
  have hRHS : (rotConvPolyGen μ (MvPolynomial.C (convC (jointVec h ω p))) *
        rotConvPolyGen μ (MvPolynomial.pderiv p Q)).coeff α =
      rescaleConv μ (Q.coeff (α + Finsupp.single p 1) * ((α p : ConvergentPowerSeries) + 1)) *
        convC (jointVec h ω p * (α.prod fun q e => (μ ^ (q.2.val + 1)) ^ e)) := by
    have hC_rot : rotConvPolyGen (d := d) (r := r) μ (MvPolynomial.C (convC (jointVec h ω p))) =
        MvPolynomial.C (convC (jointVec h ω p)) := by
      simp only [rotConvPolyGen, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      congr 1; apply Subtype.ext; ext n
      cases n <;> simp [rescaleConv, convC, PowerSeries.coeff_rescale]
    rw [hC_rot, MvPolynomial.coeff_C_mul, rotConvPolyGen_coeff, MvPolynomial.coeff_pderiv]
    have hCmul : ∀ x y : ℂ, convC (x * y) = convC x * convC y := fun x y => by
      apply Subtype.ext; simp [convC, map_mul]
    rw [hCmul]; ring
  rw [hLHS, hRHS]

/-- **Arbitrary Complex Pole Annihilation**:
For a minimal-total-degree nonzero relation `Qmin`, EVERY pole `ω ∈ unionPoles h` anywhere in
`ℂ \ {0}` satisfies `D_vec_conv (jointVec h ω) Qmin = 0`. -/
theorem D_vec_conv_eq_zero_of_pole {d r : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i))
    (Qmin : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries)
    (hQmin_pos : 0 < Qmin.totalDegree)
    (hQmin_zero : formalEvalConvJoint (fun i => formalSeries (b i)) Qmin = 0)
    (hQmin_min : ∀ P : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries,
      P ≠ 0 → P.totalDegree < Qmin.totalDegree →
      formalEvalConvJoint (fun i => formalSeries (b i)) P ≠ 0)
    {ω : ℂ} (hω : ω ∈ unionPoles h) :
    D_vec_conv (jointVec h ω) Qmin = 0 := by
  have hω_ne : ω ≠ 0 := fun h0 => zero_not_mem_unionPoles h (h0 ▸ hω)
  let s : ℝ := ‖ω‖
  have hs_pos : 0 < s := norm_pos_iff.mpr hω_ne
  let μ : ℂ := ω / (s : ℂ)
  have hμ : μ ≠ 0 := div_ne_zero hω_ne (Complex.ofReal_ne_zero.mpr hs_pos.ne')
  have hμs : μ * (s : ℂ) = ω := div_mul_cancel₀ ω (Complex.ofReal_ne_zero.mpr hs_pos.ne')
  let h_rot : ∀ i : Fin d, PlaneSimplePoleData (fun z => b i (μ * z)) :=
    fun i => (h i).rotate hμ
  let Qrot := rotConvPolyGen μ Qmin
  have hb0 : ∀ i, AnalyticAt ℂ (b i) 0 := fun i => (h i).analyticOn 0 (h i).zero_not_mem
  have hQrot_pos : 0 < Qrot.totalDegree := by
    rwa [rotConvPolyGen_totalDegree hμ]
  have hQrot_zero : formalEvalConvJoint (fun i => formalSeries (fun z => b i (μ * z))) Qrot = 0 := by
    rw [formalEvalConvJoint_rot hb0 hμ Qmin, hQmin_zero, map_zero]
  have hQrot_min : ∀ P : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries,
      P ≠ 0 → P.totalDegree < Qrot.totalDegree →
      formalEvalConvJoint (fun i => formalSeries (fun z => b i (μ * z))) P ≠ 0 := by
    intro P hP_ne hP_deg hP_zero
    let P_back := rotConvPolyGen μ⁻¹ P
    have hPb_ne : P_back ≠ 0 := fun h0 => hP_ne (by
      have := congrArg (rotConvPolyGen μ) h0
      rw [rotConvPolyGen_comp_inv hμ, map_zero] at this; exact this)
    have hPb_deg : P_back.totalDegree < Qmin.totalDegree := by
      rw [rotConvPolyGen_totalDegree (inv_ne_zero hμ)]
      rwa [rotConvPolyGen_totalDegree hμ] at hP_deg
    have hPb_zero : formalEvalConvJoint (fun i => formalSeries (b i)) P_back = 0 := by
      have hres := formalEvalConvJoint_rot hb0 hμ P_back
      rw [rotConvPolyGen_comp_inv hμ, hP_zero] at hres
      ext n
      have hn := congrArg (PowerSeries.coeff n) hres.symm
      simp only [PowerSeries.coeff_rescale, map_zero] at hn
      exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero n hμ)
    exact hQmin_min P_back hPb_ne hPb_deg hPb_zero
  have hs_mem : (s : ℂ) ∈ unionPoles h_rot := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change μ * (s : ℂ) ∈ (h i).poles
    rwa [hμs]
  have hDrot : D_vec_conv (jointVec h_rot (s : ℂ)) Qrot = 0 :=
    D_vec_conv_eq_zero_of_pos_real_pole h_rot Qrot hQrot_pos hQrot_zero hQrot_min hs_pos
      s hs_pos le_rfl hs_mem
  have hcomm := rotConvPolyGen_D_vec_conv h hω_ne Qmin
  dsimp only at hcomm
  have hrot_eq : rotConvPolyGen μ (D_vec_conv (jointVec h ω) Qmin) = 0 := by
    rw [← hcomm]; exact hDrot
  exact rotConvPolyGen_injective hμ (hrot_eq.trans (map_zero _).symm)

/-! #### 4C. Lowest-`w`-Order Coefficient Extraction & Joint Matrix Span Contradiction -/

/-- Extract the `[w^k]` coefficient polynomial in `MvPolynomial ι ℂ` from a polynomial over `ℂ{w}`. -/
@[expose] def coeffWGen {ι : Type*} (k : ℕ)
    (Q : MvPolynomial ι ConvergentPowerSeries) : MvPolynomial ι ℂ :=
  ∑ α ∈ Q.support, MvPolynomial.monomial α (PowerSeries.coeff k (Q.coeff α).val)

lemma coeffWGen_coeff {ι : Type*} (k : ℕ)
    (Q : MvPolynomial ι ConvergentPowerSeries) (α : ι →₀ ℕ) :
    (coeffWGen k Q).coeff α = PowerSeries.coeff k (Q.coeff α).val := by
  classical
  unfold coeffWGen
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ Q.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Subring.coe_zero, map_zero]
    exact Finset.sum_eq_zero fun β hβ => by simp [show β ≠ α from fun h => hα (h ▸ hβ)]

lemma coeffWGen_D_vec_conv {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (v : ι → ℂ)
    (Q : MvPolynomial ι ConvergentPowerSeries) :
    coeffWGen k (D_vec_conv v Q) = D_vec v (coeffWGen k Q) := by
  ext α
  rw [coeffWGen_coeff]
  unfold D_vec_conv D_vec
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv, coeffWGen_coeff]
  have hval : (∑ p : ι, convC (v p) * (Q.coeff (α + Finsupp.single p 1) * ((α p : ConvergentPowerSeries) + 1))).val =
      ∑ p : ι, (convC (v p) * (Q.coeff (α + Finsupp.single p 1) * ((α p : ConvergentPowerSeries) + 1))).val :=
    map_sum toPS _ _
  rw [hval, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  change PowerSeries.coeff k (PowerSeries.C (v p) * ((Q.coeff (α + Finsupp.single p 1)).val *
      ((α p : PowerSeries ℂ) + 1))) = _
  rw [PowerSeries.coeff_C_mul]
  have hnat : ((α p : PowerSeries ℂ) + 1) = PowerSeries.C (((α p : ℂ) + 1)) := by
    rw [map_add, map_natCast, map_one]
  rw [hnat, mul_comm ((Q.coeff _).val), PowerSeries.coeff_C_mul]
  ring

private lemma exists_coeffWGen_pos_deg {ι : Type*}
    (Q : MvPolynomial ι ConvergentPowerSeries) (hpos : 0 < Q.totalDegree) :
    ∃ k : ℕ, 0 < (coeffWGen k Q).totalDegree := by
  classical
  have hex_α : ∃ α ∈ Q.support, 0 < α.sum (fun _ e => e) := by
    by_contra hnone
    push Not at hnone
    have hle : Q.totalDegree ≤ 0 := by
      rw [MvPolynomial.totalDegree]
      exact Finset.sup_le fun α hα => hnone α hα
    omega
  obtain ⟨α, hα_supp, hα_pos⟩ := hex_α
  have hcoeff_ne : (Q.coeff α).val ≠ 0 := fun h0 =>
    MvPolynomial.mem_support_iff.mp hα_supp (Subtype.ext h0)
  have hex_k : ∃ k : ℕ, PowerSeries.coeff k (Q.coeff α).val ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hcoeff_ne (by ext k; simp [hall k])
  obtain ⟨k, hk⟩ := hex_k
  refine ⟨k, ?_⟩
  have hmem : α ∈ (coeffWGen k Q).support := by
    rw [MvPolynomial.mem_support_iff, coeffWGen_coeff]; exact hk
  exact lt_of_lt_of_le hα_pos (MvPolynomial.le_totalDegree hmem)

/-- **Master Finite-Contour Joint Span Engine (Codex Lemma 4)**:
For a finite family `b : Fin d → ℂ → ℂ` with `PlaneSimplePoleData (b i)`, suppose there exists a
family of poles `ω : Fin d × Fin (r + 1) → ℂ` (all in `unionPoles h`) whose joint residue-jet matrix
`M p q := jointVec h (ω p) q` is invertible (`M.det ≠ 0`). Then there is NO nonzero formal relation
`Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries` with
`formalEvalConvJoint (fun i => formalSeries (b i)) Q = 0`. -/
theorem finite_contour_joint_no_conv_ade_of_det_ne_zero {d r : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i))
    (ω : Fin d × Fin (r + 1) → ℂ)
    (hω_mem : ∀ p, ω p ∈ unionPoles h)
    (hdet : (Matrix.of (fun p q : Fin d × Fin (r + 1) => jointVec h (ω p) q)).det ≠ 0)
    (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConvJoint (fun i => formalSeries (b i)) Q = 0) : Q = 0 := by
  classical
  by_contra hQ_ne
  have hex : ∃ deg : ℕ, ∃ P : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries,
      P.totalDegree = deg ∧ P ≠ 0 ∧ formalEvalConvJoint (fun i => formalSeries (b i)) P = 0 :=
    ⟨Q.totalDegree, Q, rfl, hQ_ne, hQ⟩
  let Qmin := Classical.choose (Nat.find_spec hex)
  have hQmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hQmin_deg : Qmin.totalDegree = Nat.find hex := hQmin_spec.1
  have hQmin_ne : Qmin ≠ 0 := hQmin_spec.2.1
  have hQmin_zero : formalEvalConvJoint (fun i => formalSeries (b i)) Qmin = 0 := hQmin_spec.2.2
  have hQmin_min : ∀ P : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries,
      P ≠ 0 → P.totalDegree < Qmin.totalDegree →
      formalEvalConvJoint (fun i => formalSeries (b i)) P ≠ 0 := by
    intro P hP_ne hP_deg hP_zero
    rw [hQmin_deg] at hP_deg
    exact Nat.find_min hex hP_deg ⟨P, rfl, hP_ne, hP_zero⟩
  have hQmin_pos : 0 < Qmin.totalDegree := by
    by_contra! hle
    have h0 : Qmin.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev0 : formalEvalConvJoint (fun i => formalSeries (b i))
        (MvPolynomial.C (Qmin.coeff 0) : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries) = 0 := by
      rw [← hC]; exact hQmin_zero
    have hp0 : toPS (Qmin.coeff 0) = 0 := by simpa [formalEvalConvJoint] using hev0
    have hcoeff0 : Qmin.coeff 0 = 0 := toPS_injective (hp0.trans (map_zero toPS).symm)
    exact hQmin_ne (hC.trans (by rw [hcoeff0, map_zero]))
  obtain ⟨k₀, hk₀_pos⟩ := exists_coeffWGen_pos_deg Qmin hQmin_pos
  let P₀ : MvPolynomial (Fin d × Fin (r + 1)) ℂ := coeffWGen k₀ Qmin
  have hD_all : ∀ p : Fin d × Fin (r + 1), D_vec (jointVec h (ω p)) P₀ = 0 := fun p => by
    have hDc := D_vec_conv_eq_zero_of_pole h Qmin hQmin_pos hQmin_zero hQmin_min (hω_mem p)
    have hck := congrArg (coeffWGen k₀) hDc
    rw [coeffWGen_D_vec_conv] at hck
    refine hck.trans ?_
    ext α; simp [coeffWGen_coeff]
  let M : Matrix (Fin d × Fin (r + 1)) (Fin d × Fin (r + 1)) ℂ :=
    Matrix.of fun p q => jointVec h (ω p) q
  have hM_inv : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hall_pd : ∀ q : Fin d × Fin (r + 1), MvPolynomial.pderiv q P₀ = 0 := by
    intro q
    ext α
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    let x : Fin d × Fin (r + 1) → ℂ := fun q' => (MvPolynomial.pderiv q' P₀).coeff α
    have hMx : M.mulVec x = 0 := by
      ext p
      have hc := congrArg (fun R => R.coeff α) (hD_all p)
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
      unfold D_vec at hc
      rw [MvPolynomial.coeff_sum] at hc
      simp_rw [MvPolynomial.coeff_C_mul] at hc
      simpa [M, x, Matrix.mulVec, dotProduct] using hc
    have hx0 : x = 0 := by
      have h1 := congrArg (M⁻¹.mulVec) hMx
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM_inv, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      exact h1
    exact congrFun hx0 q
  have hC0 : P₀ = MvPolynomial.C (P₀.coeff 0) := all_partials_zero P₀ hall_pd
  have hdeg0 : P₀.totalDegree = 0 := by rw [hC0, MvPolynomial.totalDegree_C]
  exact absurd hdeg0 (Nat.ne_of_gt hk₀_pos)

/-! ### 5. Scalar Finite-Pole Count Bound, Strong `ℂ({t})` D-Transcendence & Entire Log-Derivative Bridge -/

/-- **Scalar Finite-Pole Count Theorem (Codex Main Finite-Order Theorem)**:
Let `b : ℂ → ℂ` satisfy `PlaneSimplePoleData b` (NO growth assumption at `∞`, NO wedge assumption).
If `formalEvalConv (formalSeries b) Q = 0` for a nonzero `Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries`,
then `b` CANNOT have `r + 1` distinct simple poles (equivalently, every `Finset` of poles of `b`
has cardinality `≤ r`). -/
theorem finite_contour_scalar_no_conv_ade_of_poles {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    {r : ℕ} (ω : Fin (r + 1) → ℂ) (hω_inj : Function.Injective ω)
    (hω_mem : ∀ k, ω k ∈ h.poles)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries b) Q = 0) : Q = 0 := by
  let b1 : Fin 1 → ℂ → ℂ := fun _ => b
  let h1 : ∀ i : Fin 1, PlaneSimplePoleData (b1 i) := fun _ => h
  let e : Fin (r + 1) ≃ Fin 1 × Fin (r + 1) :=
    { toFun := fun j => (0, j)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun ⟨i, j⟩ => Prod.ext (Fin.eq_zero i).symm rfl }
  let Q1 : MvPolynomial (Fin 1 × Fin (r + 1)) ConvergentPowerSeries := MvPolynomial.rename e Q
  have hQ1 : formalEvalConvJoint (fun i => formalSeries (b1 i)) Q1 = 0 := by
    unfold formalEvalConvJoint Q1
    rw [MvPolynomial.eval₂_rename]
    exact hQ
  let ω1 : Fin 1 × Fin (r + 1) → ℂ := fun p => ω p.2
  have hω1_mem : ∀ p, ω1 p ∈ unionPoles h1 := fun p =>
    Set.mem_iUnion.mpr ⟨0, hω_mem p.2⟩
  -- Determinant of the (Fin 1 × Fin (r + 1)) matrix equals (∏ res (ω k)) * det (Vandermonde (-ω)) ≠ 0
  have hdet : (Matrix.of (fun p q : Fin 1 × Fin (r + 1) => jointVec h1 (ω1 p) q)).det ≠ 0 := by
    let M1 : Matrix (Fin 1 × Fin (r + 1)) (Fin 1 × Fin (r + 1)) ℂ :=
      Matrix.of fun p q => jointVec h1 (ω1 p) q
    let M0 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
      Matrix.of fun k j => h.res (ω k) * (-ω k) ^ j.val
    have hreindex : M0 = Matrix.reindex e.symm e.symm M1 := by
      ext k j
      change h.res (ω k) * (-ω k) ^ j.val = jointVec h1 (ω1 (e k)) (e j)
      simp [jointVec, ω1, e, PlaneSimplePoleData.extRes, h1, hω_mem k]
    have hdet_eq : M0.det = M1.det := by
      rw [hreindex, Matrix.det_reindex_self]
    rw [← hdet_eq]
    have hfac : M0 = Matrix.diagonal (fun k => h.res (ω k)) * Matrix.vandermonde (fun k => -ω k) := by
      ext k j
      simp [M0, Matrix.mul_apply, Matrix.diagonal, Matrix.vandermonde]
    rw [hfac, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => h.res_ne_zero (ω k) (hω_mem k)) ?_
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i < j := (Finset.mem_Ioi.mp hj)
    intro h0
    have heq : ω j = ω i := by linear_combination -h0
    exact hij.ne' (hω_inj heq)
  have hQ1_zero : Q1 = 0 :=
    finite_contour_joint_no_conv_ade_of_det_ne_zero h1 ω1 hω1_mem hdet Q1 hQ1
  exact MvPolynomial.rename_injective e e.injective (hQ1_zero.trans (map_zero _).symm)

/-- **Sharp Finite-Pole Count Corollary**:
If `Q ≠ 0` is a vanishing order-`r` convergent-germ ADE for `formalSeries b`, then every finite
subset of `h.poles` has cardinality at most `r`. -/
theorem finite_contour_pole_count_bound {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ_ne : Q ≠ 0) (hQ : formalEvalConv (formalSeries b) Q = 0)
    (S : Finset ℂ) (hS : (S : Set ℂ) ⊆ h.poles) :
    S.card ≤ r := by
  by_contra! hgt
  have hle : r + 1 ≤ S.card := hgt
  let e := S.equivFin
  let ω : Fin (r + 1) → ℂ := fun k => (e.symm ⟨k.val, lt_of_lt_of_le k.isLt hle⟩).val
  have hω_inj : Function.Injective ω := fun a b hab => by
    have hsub : (e.symm ⟨a.val, lt_of_lt_of_le a.isLt hle⟩) = e.symm ⟨b.val, lt_of_lt_of_le b.isLt hle⟩ :=
      Subtype.ext hab
    have hfin : (⟨a.val, lt_of_lt_of_le a.isLt hle⟩ : Fin S.card) =
        ⟨b.val, lt_of_lt_of_le b.isLt hle⟩ := e.symm.injective hsub
    exact Fin.ext (show a.val = b.val from congrArg (fun x : Fin S.card => x.val) hfin)
  have hω_mem : ∀ k, ω k ∈ h.poles := fun k =>
    hS (Finset.mem_coe.mpr (e.symm ⟨k.val, lt_of_lt_of_le k.isLt hle⟩).property)
  exact hQ_ne (finite_contour_scalar_no_conv_ade_of_poles h ω hω_inj hω_mem Q hQ)

/-- **Infinite-Pole Convergent-Germ ADE Obstruction (`d_u`)**:
If `h : PlaneSimplePoleData b` has infinitely many distinct simple poles (`h.poles.Infinite`),
then `formalSeries b` satisfies NO nonzero ADE over `ConvergentPowerSeries` (`ℂ{w}`) — with ZERO
growth assumption at `∞`. -/
theorem finite_contour_no_conv_ade {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    (hinf : h.poles.Infinite)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries b) Q = 0) : Q = 0 := by
  by_contra hQ_ne
  obtain ⟨S, hS_sub, hS_card⟩ := hinf.exists_subset_card_eq (r + 1)
  have hle := finite_contour_pole_count_bound h Q hQ_ne hQ S hS_sub
  omega

/-- **Infinite-Pole Strong `ℂ({t})` D-Transcendence of `ogfOfEGF b`**:
If `h : PlaneSimplePoleData b` has infinitely many distinct simple poles, then
`ogfOfEGF b = ∑_{n ≥ 0} b^{(n)}(0) t^n` is **strongly differentially transcendental over convergent
meromorphic germs `ℂ({t})`**, with ZERO growth assumption at `∞`. -/
theorem finite_contour_ogf_stronglyDTrans {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    (hinf : h.poles.Infinite) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF b) :=
  stronglyDTransOverMeromorphicGerms_of_convergent
    (stronglyDTransOverConvergent_of_X_mul_no_conv_ade fun Q hQ => by
      rw [← formalSeries_eq_X_mul_ogfOfEGF] at hQ
      exact finite_contour_no_conv_ade h hinf Q hQ)

/-- **Infinite-Pole Strong `ℂ({t})` D-Transcendence of `formalSeries b`**:
If `h : PlaneSimplePoleData b` has infinitely many distinct simple poles, then
`formalSeries b = ∑_{n ≥ 0} b^{(n)}(0) t^{n+1}` is **strongly differentially transcendental over
convergent meromorphic germs `ℂ({t})`**. -/
theorem finite_contour_formalSeries_stronglyDTrans {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    (hinf : h.poles.Infinite) :
    StronglyDTransOverMeromorphicGerms (formalSeries b) := by
  have hconvX_ne : convX ≠ 0 := by
    intro h0
    have h1 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 1 a.val) h0
    simp [convX] at h1
  have hOGF : StronglyDTransOverConvergent (ogfOfEGF b) :=
    stronglyDTransOverConvergent_of_X_mul_no_conv_ade fun Q hQ => by
      rw [← formalSeries_eq_X_mul_ogfOfEGF] at hQ
      exact finite_contour_no_conv_ade h hinf Q hQ
  refine stronglyDTransOverMeromorphicGerms_of_convergent ?_
  rw [formalSeries_eq_X_mul_ogfOfEGF]
  change StronglyDTransOverConvergent (convX.val * ogfOfEGF b)
  exact stronglyDTransOverConvergent_mul_conv hOGF hconvX_ne

/-- **Universal Entire Logarithmic-Derivative Bridge**:
For ANY entire function `E : ℂ → ℂ` and ANY center `c : ℂ` with `E c ≠ 0`, the shifted negative
logarithmic derivative `b(w) := -deriv E (c + w) / E (c + w)` unconditionally satisfies
`PlaneSimplePoleData b`, with:
- `poles = {w : ℂ | E (c + w) = 0}`,
- `res w = -(analyticOrderNatAt E (c + w) : ℂ) ≠ 0` (arbitrary zero multiplicities allowed!). -/
@[expose] def entireLogDeriv_planeSimplePoleData {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    {c : ℂ} (hc : E c ≠ 0) :
    PlaneSimplePoleData (fun w => -deriv E (c + w) / E (c + w)) where
  poles := {w : ℂ | E (c + w) = 0}
  res := fun w => -(analyticOrderNatAt E (c + w) : ℂ)
  zero_not_mem := by simpa using hc
  finite_on_closedBall R := by
    have hE_an : AnalyticOnNhd ℂ E Set.univ := hE.differentiableOn.analyticOnNhd isOpen_univ
    have hcod := hE_an.preimage_zero_mem_codiscreteWithin (x := c) hc (Set.mem_univ c) isConnected_univ
    have hcod' : (E ⁻¹' {0})ᶜ ∈ Filter.codiscrete ℂ := by
      rw [mem_codiscreteWithin] at hcod
      rw [mem_codiscrete]
      intro x
      simpa using hcod x (Set.mem_univ x)
    have hclosed : IsClosed (E ⁻¹' {0}) := by simpa using (mem_codiscrete'.mp hcod').1
    have hdisc : IsDiscrete (E ⁻¹' {0}) := by simpa using (mem_codiscrete'.mp hcod').2
    have hcomp : IsCompact (Metric.closedBall c R) := isCompact_closedBall c R
    have hfin_c : (Metric.closedBall c R ∩ E ⁻¹' {0}).Finite :=
      (hcomp.inter_right hclosed).finite (hdisc.mono Set.inter_subset_right)
    have hsub : (fun w => c + w) '' (Metric.closedBall (0 : ℂ) R ∩ {w : ℂ | E (c + w) = 0}) ⊆
        Metric.closedBall c R ∩ E ⁻¹' {0} := by
      rintro _ ⟨w, ⟨hwR, hw0⟩, rfl⟩
      refine ⟨?_, hw0⟩
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      simpa [Metric.mem_closedBall, dist_zero_right] using hwR
    exact (hfin_c.subset hsub).of_finite_image (fun a _ b _ hab => add_left_cancel hab)
  analyticOn w hw := by
    have hE_an : AnalyticOnNhd ℂ E Set.univ := hE.differentiableOn.analyticOnNhd isOpen_univ
    have hshift : AnalyticAt ℂ (fun z : ℂ => c + z) w := analyticAt_const.add analyticAt_id
    have hnum : AnalyticAt ℂ (fun z : ℂ => -deriv E (c + z)) w :=
      ((hE_an.deriv (c + w) (Set.mem_univ _)).comp hshift).neg
    have hden : AnalyticAt ℂ (fun z : ℂ => E (c + z)) w :=
      (hE_an (c + w) (Set.mem_univ _)).comp hshift
    exact hnum.div hden hw
  res_ne_zero ω hω := by
    have hE_an : AnalyticOnNhd ℂ E Set.univ := hE.differentiableOn.analyticOnNhd isOpen_univ
    have hne_top : analyticOrderAt E (c + ω) ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      have h0 := hE_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ (c + ω)) htop
      exact hc (h0 (Set.mem_univ c))
    have hpos : 0 < analyticOrderNatAt E (c + ω) := by
      have hord_ne : analyticOrderAt E (c + ω) ≠ 0 :=
        (hE_an (c + ω) (Set.mem_univ _)).analyticOrderAt_ne_zero.mpr hω
      have hord_pos : 0 < analyticOrderAt E (c + ω) := pos_iff_ne_zero.mpr hord_ne
      have hcast : (analyticOrderNatAt E (c + ω) : ℕ∞) = analyticOrderAt E (c + ω) :=
        ENat.natCast_toNat hne_top
      exact_mod_cast (hcast.symm ▸ hord_pos : (0 : ℕ∞) < (analyticOrderNatAt E (c + ω) : ℕ∞))
    exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hpos.ne')
  simple_pole ω hω := by
    have hE_an : AnalyticOnNhd ℂ E Set.univ := hE.differentiableOn.analyticOnNhd isOpen_univ
    have hne_top : analyticOrderAt E (c + ω) ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      have h0 := hE_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ (c + ω)) htop
      exact hc (h0 (Set.mem_univ c))
    let m : ℕ := analyticOrderNatAt E (c + ω)
    obtain ⟨g, hg_an, hg_ne, hfac⟩ := (hE_an (c + ω) (Set.mem_univ _)).analyticOrderAt_ne_top.mp hne_top
    have hshift_tend : Tendsto (fun z : ℂ => c + z) (𝓝[≠] ω) (𝓝[≠] (c + ω)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(continuousAt_const.add continuousAt_id).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ ω)
      exact fun heq => hz (add_left_cancel heq)
    have hlim_ratio : Tendsto (fun z : ℂ => -(m : ℂ) - (z - ω) * (deriv g (c + z) / g (c + z)))
        (𝓝[≠] ω) (𝓝 (-(m : ℂ))) := by
      have h1 : Tendsto (fun z : ℂ => (z - ω) * (deriv g (c + z) / g (c + z))) (𝓝[≠] ω) (𝓝 0) := by
        have hsub0 : Tendsto (fun z : ℂ => z - ω) (𝓝[≠] ω) (𝓝 0) := by
          have hc_sub : ContinuousAt (fun z : ℂ => z - ω) ω := continuousAt_id.sub continuousAt_const
          simpa using hc_sub.tendsto.mono_left (nhdsWithin_le_nhds (s := {ω}ᶜ))
        have hdg : ContinuousAt (fun z : ℂ => deriv g (c + z) / g (c + z)) ω :=
          ((hg_an.deriv.continuousAt.comp (continuousAt_const.add continuousAt_id)).div
            (hg_an.continuousAt.comp (continuousAt_const.add continuousAt_id)) hg_ne)
        simpa using hsub0.mul (hdg.tendsto.mono_left nhdsWithin_le_nhds)
      simpa using tendsto_const_nhds.sub h1
    refine hlim_ratio.congr' ?_
    have hnhds_s : ∀ᶠ s in 𝓝 (c + ω),
        E s = (s - (c + ω)) ^ m * g s ∧
        deriv E s = (m : ℂ) * (s - (c + ω)) ^ (m - 1) * g s + (s - (c + ω)) ^ m * deriv g s ∧
        g s ≠ 0 := by
      filter_upwards [hfac.eventually_nhds, hg_an.eventually_analyticAt,
        hg_an.continuousAt.eventually_ne hg_ne] with s hs_fac hs_ga hs_gne
      have hEs : E s = (s - (c + ω)) ^ m * g s := by simpa [m, smul_eq_mul] using hs_fac.self_of_nhds
      refine ⟨hEs, ?_, hs_gne⟩
      have hloc_eq : E =ᶠ[𝓝 s] fun t => (t - (c + ω)) ^ m * g t := by
        filter_upwards [hs_fac] with t ht; simpa [m, smul_eq_mul] using ht
      rw [hloc_eq.deriv_eq]
      have hd1 : HasDerivAt (fun t : ℂ => (t - (c + ω)) ^ m)
          ((m : ℂ) * (s - (c + ω)) ^ (m - 1)) s := by
        have hbase : HasDerivAt (fun t : ℂ => t - (c + ω)) 1 s := (hasDerivAt_id s).sub_const (c + ω)
        have hpow : HasDerivAt (fun t : ℂ => (t - (c + ω)) ^ m)
            ((m : ℂ) * (s - (c + ω)) ^ (m - 1) * 1) s := hbase.pow m
        simpa only [mul_one] using hpow
      exact (hd1.mul hs_ga.differentiableAt.hasDerivAt).deriv
    filter_upwards [hshift_tend.eventually (nhdsWithin_le_nhds hnhds_s), self_mem_nhdsWithin] with
      z ⟨hEz, hdEz, hgz⟩ (hz_ne : z ≠ ω)
    have hsub_eq : c + z - (c + ω) = z - ω := by ring
    rw [hsub_eq] at hEz hdEz
    have hsub_ne : z - ω ≠ 0 := sub_ne_zero.mpr hz_ne
    have hpow_ne : (z - ω) ^ m ≠ 0 := pow_ne_zero m hsub_ne
    have hEz_ne : E (c + z) ≠ 0 := hEz.symm ▸ mul_ne_zero hpow_ne hgz
    have hpos : 1 ≤ m := by
      have hord_ne : analyticOrderAt E (c + ω) ≠ 0 :=
        (hE_an (c + ω) (Set.mem_univ _)).analyticOrderAt_ne_zero.mpr hω
      have hord_pos : 0 < analyticOrderAt E (c + ω) := pos_iff_ne_zero.mpr hord_ne
      have hcast : (m : ℕ∞) = analyticOrderAt E (c + ω) := ENat.natCast_toNat hne_top
      have h0m : 0 < m := by
        exact_mod_cast (hcast.symm ▸ hord_pos : (0 : ℕ∞) < (m : ℕ∞))
      omega
    have hpow_split : (z - ω) * (z - ω) ^ (m - 1) = (z - ω) ^ m := by
      conv_rhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    rw [hEz, hdEz]
    field_simp [hsub_ne, hpow_ne, hgz]
    have halg : -((m : ℂ) * (z - ω) ^ (m - 1) * g (c + z) + (z - ω) ^ m * deriv g (c + z)) * (z - ω) =
        -(m : ℂ) * ((z - ω) ^ m * g (c + z)) - (z - ω) * deriv g (c + z) * (z - ω) ^ m := by
      calc -((m : ℂ) * (z - ω) ^ (m - 1) * g (c + z) + (z - ω) ^ m * deriv g (c + z)) * (z - ω)
          = -(m : ℂ) * ((z - ω) * (z - ω) ^ (m - 1) * g (c + z)) - (z - ω) * deriv g (c + z) * (z - ω) ^ m := by
            ring
        _ = -(m : ℂ) * ((z - ω) ^ m * g (c + z)) - (z - ω) * deriv g (c + z) * (z - ω) ^ m := by
            rw [hpow_split]
    linear_combination -alg_of_eq halg
  where
    alg_of_eq {a b : ℂ} (h : a = b) : a - b = 0 := sub_eq_zero.mpr h

/-- **Universal Entire Function Logarithmic-Derivative Strong `ℂ({t})` D-Transcendence Theorem**:
For ANY entire function `E : ℂ → ℂ` with infinitely many distinct zeros and ANY center `c : ℂ`
with `E c ≠ 0`, BOTH `ogfOfEGF (fun w => -deriv E (c + w) / E (c + w))` AND
`formalSeries (fun w => -deriv E (c + w) / E (c + w))` are **strongly differentially transcendental
over convergent meromorphic germs `ℂ({t})`** — with ZERO growth condition on `E` and ZERO
zero-simplicity assumption! -/
theorem entireLogDeriv_ogf_stronglyDTrans {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    {c : ℂ} (hc : E c ≠ 0) (hinf : {ρ : ℂ | E ρ = 0}.Infinite) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF fun w => -deriv E (c + w) / E (c + w)) := by
  have hpoles_inf : (entireLogDeriv_planeSimplePoleData hE hc).poles.Infinite := by
    have him : (fun ρ => ρ - c) '' {ρ : ℂ | E ρ = 0} ⊆ (entireLogDeriv_planeSimplePoleData hE hc).poles := by
      rintro _ ⟨ρ, hρ, rfl⟩
      change E (c + (ρ - c)) = 0
      simpa [add_sub_cancel] using hρ
    exact (hinf.image fun a _ b _ hab => sub_left_inj.mp hab).mono him
  exact finite_contour_ogf_stronglyDTrans (entireLogDeriv_planeSimplePoleData hE hc) hpoles_inf

theorem entireLogDeriv_formalSeries_stronglyDTrans {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    {c : ℂ} (hc : E c ≠ 0) (hinf : {ρ : ℂ | E ρ = 0}.Infinite) :
    StronglyDTransOverMeromorphicGerms (formalSeries fun w => -deriv E (c + w) / E (c + w)) := by
  have hpoles_inf : (entireLogDeriv_planeSimplePoleData hE hc).poles.Infinite := by
    have him : (fun ρ => ρ - c) '' {ρ : ℂ | E ρ = 0} ⊆ (entireLogDeriv_planeSimplePoleData hE hc).poles := by
      rintro _ ⟨ρ, hρ, rfl⟩
      change E (c + (ρ - c)) = 0
      simpa [add_sub_cancel] using hρ
    exact (hinf.image fun a _ b _ hab => sub_left_inj.mp hab).mono him
  exact finite_contour_formalSeries_stronglyDTrans (entireLogDeriv_planeSimplePoleData hE hc) hpoles_inf

/-! ### 6. Joint Multi-Series Strong `ℂ({t})` Differential Independence & Block-Triangular Transfer -/

/-- Joint strong differential independence over convergent power series `ℂ{t}` for `d` formal
series `F : Fin d → PowerSeries ℂ`. -/
@[expose] def JointlyStronglyDTransOverConvergent {d : ℕ} (F : Fin d → PowerSeries ℂ) : Prop :=
  ∀ {r : ℕ} (P : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries),
    MvPolynomial.eval₂ toPS (fun p : Fin d × Fin (r + 1) => seriesJet (F p.1) p.2.val) P = 0 →
      P = 0

/-- Joint strong differential independence over convergent meromorphic germs `ℂ({t})` for `d` formal
series `F : Fin d → PowerSeries ℂ`: the entire doubly-indexed family `{F_i^{(j)}}_{i, j}` is
algebraically independent over `FractionRing ConvergentPowerSeries` inside
`FractionRing (PowerSeries ℂ)`. -/
@[expose] def JointlyStronglyDTransOverMeromorphicGerms {d : ℕ} (F : Fin d → PowerSeries ℂ) : Prop :=
  AlgebraicIndependent (FractionRing ConvergentPowerSeries)
    (fun p : Fin d × ℕ => fracPS_of_ps (seriesJet (F p.1) p.2))

/-- Clearing denominators for joint differential independence: `ℂ{t}` → `ℂ({t})`. -/
theorem jointlyStronglyDTransOverMeromorphicGerms_of_convergent {d : ℕ}
    {F : Fin d → PowerSeries ℂ} (hF : JointlyStronglyDTransOverConvergent F) :
    JointlyStronglyDTransOverMeromorphicGerms F := by
  classical
  rw [JointlyStronglyDTransOverMeromorphicGerms, algebraicIndependent_iff]
  intro Q hQ
  let K := FractionRing ConvergentPowerSeries
  let alg : ConvergentPowerSeries →+* K := algebraMap ConvergentPowerSeries K
  have halg_inj : Function.Injective alg := IsFractionRing.injective ConvergentPowerSeries K
  choose num den hden_nz hdiv using fun α : (Fin d × ℕ) →₀ ℕ =>
    IsFractionRing.div_surjective (A := ConvergentPowerSeries) (K := K) (Q.coeff α)
  have hden_ne : ∀ α, den α ≠ 0 := fun α => mem_nonZeroDivisors_iff_ne_zero.mp (hden_nz α)
  let D : ConvergentPowerSeries := ∏ β ∈ Q.support, den β
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun β _ => hden_ne β
  let Q_conv : MvPolynomial (Fin d × ℕ) ConvergentPowerSeries :=
    ∑ α ∈ Q.support, MvPolynomial.monomial α (num α * ∏ β ∈ Q.support.erase α, den β)
  have hclear : MvPolynomial.map alg Q_conv = MvPolynomial.C (alg D) * Q := by
    apply MvPolynomial.ext
    intro α
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
    dsimp only [Q_conv]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ Q.support
    · rw [Finset.sum_eq_single α]
      · simp only [↓reduceIte, map_mul, map_prod]
        have hD_split : alg D = alg (den α) * ∏ β ∈ Q.support.erase α, alg (den β) := by
          dsimp only [D]; rw [map_prod, ← Finset.mul_prod_erase Q.support _ hα]
        have hden_alg_ne : alg (den α) ≠ 0 := fun h0 =>
          hden_ne α (halg_inj (h0.trans (map_zero alg).symm))
        rw [hD_split, ← hdiv α]
        change alg (num α) * ∏ β ∈ Q.support.erase α, alg (den β) =
          (alg (den α) * ∏ β ∈ Q.support.erase α, alg (den β)) * (alg (num α) / alg (den α))
        field_simp [hden_alg_ne]
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · have hsum0 : (∑ x ∈ Q.support, if x = α then num x * ∏ β ∈ Q.support.erase x, den β else 0) = 0 :=
        Finset.sum_eq_zero fun β hβ => by simp [show β ≠ α from fun h => hα (h ▸ hβ)]
      rw [hsum0, map_zero, MvPolynomial.notMem_support_iff.mp hα, mul_zero]
  have hmap_eval : MvPolynomial.aeval (fun p : Fin d × ℕ => fracPS_of_ps (seriesJet (F p.1) p.2))
        (MvPolynomial.map alg Q_conv) =
      fracPS_of_ps (MvPolynomial.eval₂ toPS (fun p : Fin d × ℕ => seriesJet (F p.1) p.2) Q_conv) := by
    induction Q_conv using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.eval₂_C]
      change meromorphicGermToFracPS (alg a) = fracPS_of_ps (toPS a)
      exact IsFractionRing.lift_algebraMap convToFracPS_injective a
    | add A B hA hB =>
      simp only [map_add, MvPolynomial.eval₂_add] at hA hB ⊢; rw [hA, hB]
    | mul_X A p hA =>
      simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X] at hA ⊢; rw [hA]
  have hQ_conv_eval : MvPolynomial.eval₂ toPS (fun p : Fin d × ℕ => seriesJet (F p.1) p.2) Q_conv = 0 := by
    have h1 : fracPS_of_ps (MvPolynomial.eval₂ toPS (fun p : Fin d × ℕ => seriesJet (F p.1) p.2) Q_conv) = 0 := by
      rw [← hmap_eval, hclear, map_mul, hQ, mul_zero]
    exact IsFractionRing.injective (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))
      (h1.trans (map_zero fracPS_of_ps).symm)
  let r : ℕ := Q_conv.vars.sup Prod.snd
  let emb : Fin d × Fin (r + 1) → Fin d × ℕ := fun p => (p.1, p.2.val)
  have hemb_inj : Function.Injective emb := fun a b hab => by
    have h1 : a.1 = b.1 := congrArg (fun x : Fin d × ℕ => x.1) hab
    have h2 : a.2.val = b.2.val := congrArg (fun x : Fin d × ℕ => x.2) hab
    exact Prod.ext h1 (Fin.ext h2)
  obtain ⟨P, hP_rename⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q_conv emb hemb_inj
    (fun p hp => ⟨(p.1, ⟨p.2, Nat.lt_succ_of_le (Finset.le_sup (f := Prod.snd) hp)⟩), rfl⟩)
  have hP_eval : MvPolynomial.eval₂ toPS (fun p : Fin d × Fin (r + 1) => seriesJet (F p.1) p.2.val) P = 0 := by
    rw [← hP_rename, MvPolynomial.eval₂_rename] at hQ_conv_eval
    exact hQ_conv_eval
  have hP0 : P = 0 := hF P hP_eval
  have hQ_conv0 : Q_conv = 0 := by rw [← hP_rename, hP0, map_zero]
  rw [hQ_conv0, map_zero] at hclear
  have hCD_ne : (MvPolynomial.C (alg D) : MvPolynomial (Fin d × ℕ) K) ≠ 0 := by
    intro h0
    exact hD_ne (halg_inj ((MvPolynomial.C_eq_zero.mp h0).trans (map_zero alg).symm))
  exact (mul_eq_zero.mp hclear.symm).resolve_left hCD_ne

/-- Backward jet transformation coefficients `X^{2j+1} F^{(j)} = ∑_{k ≤ j} c_{j,k} X^{j-k} d_u^k(X F)`. -/
private def backCoeffFC : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, k =>
    if k = 0 then -((j + 1 : ℕ) : ℂ) * backCoeffFC j 0
    else -(((j + k + 1 : ℕ) : ℂ)) * backCoeffFC j k - backCoeffFC j (k - 1)

private lemma backCoeffFC_diag (j : ℕ) : backCoeffFC j j = (-1 : ℂ) ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [backCoeffFC, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hgt : backCoeffFC j (j + 1) = 0 := by
      clear ih
      induction j with
      | zero => rfl
      | succ m ihm =>
        simp only [backCoeffFC, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have hgt2 : ∀ n k, n < k → backCoeffFC n k = 0 := by
          intro n
          induction n with
          | zero => intro k hk; cases k; omega; rfl
          | succ n ihn =>
            intro k hk
            have hk0 : k ≠ 0 := by omega
            simp only [backCoeffFC, hk0, ↓reduceIte]
            rw [ihn k (by omega), ihn (k - 1) (by omega)]; ring
        rw [hgt2 m (m + 2) (by omega), hgt2 m (m + 1) (by omega)]; ring
    rw [hgt, mul_zero, zero_sub, ih, pow_succ]; ring

private lemma backCoeffFC_eq_zero_of_lt {j k : ℕ} (h : j < k) : backCoeffFC j k = 0 := by
  induction j generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => rfl
  | succ j ih =>
    have hk0 : k ≠ 0 := by omega
    simp only [backCoeffFC, hk0, ↓reduceIte]
    rw [ih (by omega : j < k), ih (by omega : j < k - 1)]
    ring

private lemma X_pow_mul_seriesJet_FC (F : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.X ^ (2 * j + 1) * seriesJet F j =
      ∑ k ∈ Finset.range (j + 1),
        PowerSeries.C (backCoeffFC j k) * PowerSeries.X ^ (j - k) * d_u^[k] (PowerSeries.X * F) := by
  have hd_C_mul : ∀ (c : ℂ) (P : PowerSeries ℂ),
      PowerSeries.derivative (PowerSeries.C c * P) = PowerSeries.C c * PowerSeries.derivative P := by
    intro c P
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
  have hd_u_C_mul : ∀ (c : ℂ) (P : PowerSeries ℂ), d_u (PowerSeries.C c * P) = PowerSeries.C c * d_u P := by
    intro c P; unfold d_u; rw [hd_C_mul]; ring
  have hd_u_mul : ∀ A B : PowerSeries ℂ, d_u (A * B) = d_u A * B + A * d_u B := fun A B => by
    unfold d_u; rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  have hd_u_X_pow : ∀ n : ℕ, d_u (PowerSeries.X ^ n : PowerSeries ℂ) =
      PowerSeries.C (-(n : ℂ)) * PowerSeries.X ^ (n + 1) := fun n => by
    cases n with
    | zero => simp [d_u]
    | succ n =>
      rw [d_u, PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one, Nat.succ_sub_one]
      have hn : ((n + 1 : ℕ) : PowerSeries ℂ) = PowerSeries.C ((n + 1 : ℕ) : ℂ) := by
        rw [← map_natCast PowerSeries.C]
      rw [hn, map_neg]
      have hpow : (PowerSeries.X : PowerSeries ℂ) ^ 2 * PowerSeries.X ^ n =
          PowerSeries.X ^ (n + 1 + 1) := by rw [← pow_add]; congr 1; omega
      calc -(PowerSeries.X ^ 2 * (PowerSeries.C ((n + 1 : ℕ) : ℂ) * PowerSeries.X ^ n))
          = -(PowerSeries.C ((n + 1 : ℕ) : ℂ) * (PowerSeries.X ^ 2 * PowerSeries.X ^ n)) := by ring
        _ = -(PowerSeries.C ((n + 1 : ℕ) : ℂ) * PowerSeries.X ^ (n + 1 + 1)) := by rw [hpow]
        _ = _ := by push_cast; ring
  let S := PowerSeries.X * F
  induction j with
  | zero =>
    simp [seriesJet, backCoeffFC]
  | succ j ih =>
    have hdu_lhs : d_u (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) =
        -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X ^ (2 * j + 2) * seriesJet F j) -
          PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1) := by
      rw [hd_u_mul, hd_u_X_pow]
      have hdu_jet : d_u (seriesJet F j) = -(PowerSeries.X ^ 2 * seriesJet F (j + 1)) := by
        rw [d_u, seriesJet, seriesJet, Function.iterate_succ_apply']
      rw [hdu_jet, map_neg, show (2 * j + 1) + 1 = 2 * j + 2 by omega,
        show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pow_add]
      ring
    have hstep_L : PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1) =
        PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ)) * PowerSeries.X * (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) -
        d_u (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) := by
      rw [hdu_lhs, map_neg]
      have hpow : (PowerSeries.X : PowerSeries ℂ) * PowerSeries.X ^ (2 * j + 1) =
          PowerSeries.X ^ (2 * j + 2) := by rw [← pow_succ']
      calc PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1)
          = -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X ^ (2 * j + 2) * seriesJet F j) -
              (-(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X ^ (2 * j + 2) * seriesJet F j) -
                PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1)) := by ring
        _ = -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * (PowerSeries.X * PowerSeries.X ^ (2 * j + 1)) * seriesJet F j) -
              (-(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X ^ (2 * j + 2) * seriesJet F j) -
                PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1)) := by rw [hpow]
        _ = _ := by ring
    rw [hstep_L, ih]
    have h_first :
        PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ)) * PowerSeries.X *
            ∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (backCoeffFC j k) * PowerSeries.X ^ (j - k) * d_u^[k] S =
          ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffFC j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show j + 1 - k = 1 + (j - k) by omega, pow_add, pow_one, map_mul, map_neg]; ring
    have h_du_sum :
        d_u (∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (backCoeffFC j k) * PowerSeries.X ^ (j - k) * d_u^[k] S) =
          ∑ k ∈ Finset.range (j + 1),
            (PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffFC j k) *
                PowerSeries.X ^ (j + 1 - k) * d_u^[k] S +
              PowerSeries.C (backCoeffFC j k) * PowerSeries.X ^ (j + 1 - (k + 1)) *
                d_u^[k + 1] S) := by
      have h_lin : ∀ (s : Finset ℕ) (f : ℕ → PowerSeries ℂ), d_u (∑ k ∈ s, f k) = ∑ k ∈ s, d_u (f k) := by
        intro s f; simp only [d_u, map_sum, Finset.mul_sum, Finset.sum_neg_distrib]
      rw [h_lin]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_assoc (PowerSeries.C (backCoeffFC j k)), hd_u_C_mul, hd_u_mul, hd_u_X_pow,
        ← Function.iterate_succ_apply' d_u k S,
        show j + 1 - k = (j - k) + 1 by omega, show j + 1 - (k + 1) = j - k by omega]
      simp only [map_mul, map_neg]; ring
    rw [h_first, h_du_sum, Finset.sum_add_distrib]
    let A (k : ℕ) : PowerSeries ℂ :=
      PowerSeries.C (-((j + k + 1 : ℕ) : ℂ) * backCoeffFC j k) * PowerSeries.X ^ (j + 1 - k) * d_u^[k] S
    let B (k : ℕ) : PowerSeries ℂ :=
      PowerSeries.C (backCoeffFC j k) * PowerSeries.X ^ (j + 1 - (k + 1)) * d_u^[k + 1] S
    have h_comb_A :
        ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffFC j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S -
          ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffFC j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S =
          ∑ k ∈ Finset.range (j + 1), A k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hcast : ((j - k : ℕ) : ℂ) = (j : ℂ) - (k : ℂ) := by rw [Nat.cast_sub hk_le]
      have hcoeff :
          (-((2 * j + 1 : ℕ) : ℂ) * backCoeffFC j k) - (-((j - k : ℕ) : ℂ) * backCoeffFC j k) =
            -((j + k + 1 : ℕ) : ℂ) * backCoeffFC j k := by rw [hcast]; push_cast; ring
      dsimp only [A]; rw [← hcoeff, map_sub, sub_mul, sub_mul]
    have h_sub_all :
        (∑ k ∈ Finset.range (j + 1), A k) - (∑ k ∈ Finset.range (j + 1), B k) =
          ∑ k ∈ Finset.range (j + 2),
            PowerSeries.C (backCoeffFC (j + 1) k) * PowerSeries.X ^ (j + 1 - k) * d_u^[k] S := by
      have hA_ext : ∑ k ∈ Finset.range (j + 1), A k = ∑ k ∈ Finset.range (j + 2), A k := by
        rw [Finset.sum_range_succ (n := j + 1) A]
        have hA_end : A (j + 1) = 0 := by simp [A, backCoeffFC_eq_zero_of_lt (Nat.lt_succ_self j)]
        rw [hA_end, add_zero]
      have hB_ext :
          ∑ k ∈ Finset.range (j + 1), B k =
            ∑ k ∈ Finset.range (j + 2), (if k = 0 then (0 : PowerSeries ℂ) else B (k - 1)) := by
        rw [Finset.sum_range_succ' (n := j + 1) (fun k => if k = 0 then 0 else B (k - 1))]; simp
      rw [hA_ext, hB_ext, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      cases k with
      | zero => simp [A, backCoeffFC]
      | succ k =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, A, B, backCoeffFC]
        have hcoeff :
            (-((j + (k + 1) + 1 : ℕ) : ℂ) * backCoeffFC j (k + 1)) - backCoeffFC j k =
              -((j + (k + 1) + 1 : ℕ) : ℂ) * backCoeffFC j (k + 1) - backCoeffFC j k := rfl
        rw [← hcoeff, map_sub, sub_mul, sub_mul]
    calc
      (∑ k ∈ Finset.range (j + 1),
          PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffFC j k) *
            PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) -
        ((∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffFC j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) +
          ∑ k ∈ Finset.range (j + 1), B k)
          = ((∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffFC j k) *
                PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) -
              (∑ k ∈ Finset.range (j + 1),
                PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffFC j k) *
                  PowerSeries.X ^ (j + 1 - k) * d_u^[k] S)) -
            ∑ k ∈ Finset.range (j + 1), B k := by ring
      _ = (∑ k ∈ Finset.range (j + 1), A k) - ∑ k ∈ Finset.range (j + 1), B k := by rw [h_comb_A]
      _ = _ := h_sub_all

/-- **Block-Triangular Joint `X * F_i → F_i` Transfer over `ℂ{t}`**:
If the `d` series `fun i => PowerSeries.X * F i` satisfy no nonzero joint `d_u`-ADE over
`ConvergentPowerSeries`, then `F` is jointly strongly differentially independent over
`ConvergentPowerSeries` (`JointlyStronglyDTransOverConvergent F`). -/
theorem jointlyStronglyDTransOverConvergent_of_X_mul_no_conv_ade {d : ℕ}
    {F : Fin d → PowerSeries ℂ}
    (hno : ∀ {r : ℕ} (Q : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries),
      formalEvalConvJoint (fun i => PowerSeries.X * F i) Q = 0 → Q = 0) :
    JointlyStronglyDTransOverConvergent F := by
  classical
  cases d with
  | zero =>
    intro r P hP
    -- Fin 0 × Fin (r + 1) is empty, so P is a constant C c with toPS c = 0
    have hdeg0 : P.totalDegree = 0 := by
      rw [MvPolynomial.totalDegree]
      refine Nat.eq_zero_of_le_zero (Finset.sup_le fun α _ => ?_)
      have hα0 : α = 0 := by ext p; exact p.1.elim0
      simp [hα0]
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
    rw [hC] at hP ⊢
    have hp0 : toPS (P.coeff 0) = 0 := by simpa using hP
    rw [toPS_injective (hp0.trans (map_zero toPS).symm), map_zero]
  | succ d' =>
    let d := d' + 1
    intro r P hP
    let S : Fin d → PowerSeries ℂ := fun i => PowerSeries.X * F i
    let M : ℕ := (2 * r + 1) * P.totalDegree
    let jetConv (p : Fin d × Fin (r + 1)) : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries :=
      ∑ k ∈ Finset.univ.filter (fun k : Fin (r + 1) => k.val ≤ p.2.val),
        MvPolynomial.C (convC (backCoeffFC p.2.val k.val) * convX ^ (p.2.val - k.val)) *
          MvPolynomial.X (p.1, k)
    have hjet_eval : ∀ p : Fin d × Fin (r + 1),
        formalEvalConvJoint S (jetConv p) = PowerSeries.X ^ (2 * p.2.val + 1) * seriesJet (F p.1) p.2.val := by
      intro p
      rw [X_pow_mul_seriesJet_FC (F p.1) p.2.val]
      dsimp only [formalEvalConvJoint, jetConv]
      rw [MvPolynomial.eval₂_sum]
      simp_rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_mul,
        map_pow, toPS_convC, toPS_convX]
      refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
      · intro k hk
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
      · intro k₁ _ k₂ _ he; exact Fin.ext he
      · intro k hk
        have hkj : k ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        refine ⟨⟨k, lt_of_le_of_lt hkj p.2.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj⟩, rfl⟩
      · intro _ _; rfl
    let wt (m : (Fin d × Fin (r + 1)) →₀ ℕ) : ℕ := m.sum fun p e => (2 * p.2.val + 1) * e
    have hwt_le : ∀ m ∈ P.support, wt m ≤ M := fun m hm => by
      have hdeg : (m.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hm
      have hterm : ∀ p ∈ m.support, (2 * p.2.val + 1) * m p ≤ (2 * r + 1) * m p := fun p _ =>
        Nat.mul_le_mul_right (m p) (by have := p.2.isLt; omega)
      calc wt m = ∑ p ∈ m.support, (2 * p.2.val + 1) * m p := rfl
        _ ≤ ∑ p ∈ m.support, (2 * r + 1) * m p := Finset.sum_le_sum hterm
        _ = (2 * r + 1) * ∑ p ∈ m.support, m p := (Finset.mul_sum _ _ _).symm
        _ ≤ (2 * r + 1) * P.totalDegree := Nat.mul_le_mul_left _ hdeg
    let P_S : MvPolynomial (Fin d × Fin (r + 1)) ConvergentPowerSeries :=
      ∑ m ∈ P.support, MvPolynomial.C (P.coeff m * convX ^ (M - wt m)) *
        m.prod fun p e => jetConv p ^ e
    have hPS_eval : formalEvalConvJoint S P_S = 0 := by
      have heq : formalEvalConvJoint S P_S =
          PowerSeries.X ^ M * MvPolynomial.eval₂ toPS (fun p : Fin d × Fin (r + 1) => seriesJet (F p.1) p.2.val) P := by
        dsimp only [P_S, formalEvalConvJoint]
        rw [MvPolynomial.eval₂_sum]
        conv_rhs => rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, map_mul, map_pow, toPS_convX]
        have hprod : MvPolynomial.eval₂ toPS (fun q : Fin d × Fin (r + 1) => d_u^[q.2.val] (S q.1))
              (m.prod fun p e => jetConv p ^ e) =
            PowerSeries.X ^ wt m * ∏ p ∈ m.support, seriesJet (F p.1) p.2.val ^ m p := by
          unfold Finsupp.prod
          rw [MvPolynomial.eval₂_prod]
          have hstep : ∀ p ∈ m.support,
              MvPolynomial.eval₂ toPS (fun q : Fin d × Fin (r + 1) => d_u^[q.2.val] (S q.1)) (jetConv p ^ m p) =
                PowerSeries.X ^ ((2 * p.2.val + 1) * m p) * seriesJet (F p.1) p.2.val ^ m p := fun p _ => by
            rw [MvPolynomial.eval₂_pow, show MvPolynomial.eval₂ toPS _ (jetConv p) =
              formalEvalConvJoint S (jetConv p) from rfl, hjet_eval p, mul_pow, ← pow_mul]
          rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; rfl
        rw [hprod]
        have hexp : (PowerSeries.X : PowerSeries ℂ) ^ (M - wt m) * PowerSeries.X ^ wt m =
            PowerSeries.X ^ M := by rw [← pow_add, Nat.sub_add_cancel (hwt_le m hm)]
        calc (toPS (P.coeff m) * PowerSeries.X ^ (M - wt m)) *
              (PowerSeries.X ^ wt m * ∏ p ∈ m.support, seriesJet (F p.1) p.2.val ^ m p)
            = toPS (P.coeff m) * (PowerSeries.X ^ (M - wt m) * PowerSeries.X ^ wt m) *
                ∏ p ∈ m.support, seriesJet (F p.1) p.2.val ^ m p := by ring
          _ = PowerSeries.X ^ M * (toPS (P.coeff m) * ∏ p ∈ m.support, seriesJet (F p.1) p.2.val ^ m p) := by
              rw [hexp]; ring
      rw [heq, hP, mul_zero]
    have hPS_zero : P_S = 0 := hno P_S hPS_eval
    -- Map to K = FractionRing ConvergentPowerSeries and rename Fin d × Fin (r + 1) ≃ Fin (N + 1)
    let K := FractionRing ConvergentPowerSeries
    let alg : ConvergentPowerSeries →+* K := algebraMap ConvergentPowerSeries K
    have halg_inj : Function.Injective alg := IsFractionRing.injective ConvergentPowerSeries K
    have hconvX_ne : convX ≠ 0 := by
      intro h0
      have h1 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 1 a.val) h0
      simp [convX] at h1
    have hxK_ne : alg convX ≠ 0 := fun h0 => hconvX_ne (halg_inj (h0.trans (map_zero alg).symm))
    let g : Fin d × Fin (r + 1) → MvPolynomial (Fin d × Fin (r + 1)) K := fun p =>
      MvPolynomial.C ((alg convX ^ (2 * p.2.val + 1))⁻¹) * MvPolynomial.map alg (jetConv p)
    have hmap_PS : MvPolynomial.map alg P_S =
        MvPolynomial.C (alg convX ^ M) * MvPolynomial.aeval g (MvPolynomial.map alg P) := by
      dsimp only [P_S]
      rw [map_sum]
      conv_rhs => rw [MvPolynomial.as_sum P, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [map_mul, MvPolynomial.map_C, map_mul, map_pow, MvPolynomial.map_monomial,
        MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
      unfold Finsupp.prod
      rw [map_prod]
      have hprod_g : (∏ p ∈ m.support, MvPolynomial.map alg (jetConv p ^ m p)) =
          MvPolynomial.C (alg convX ^ wt m) * ∏ p ∈ m.support, g p ^ m p := by
        have hstep : ∀ p ∈ m.support,
            MvPolynomial.map alg (jetConv p ^ m p) =
              MvPolynomial.C (alg convX ^ ((2 * p.2.val + 1) * m p)) * g p ^ m p := fun p _ => by
          dsimp only [g]
          rw [map_pow, mul_pow, ← mul_assoc, ← MvPolynomial.C_pow, ← map_mul, pow_mul, ← mul_pow,
            mul_inv_cancel₀ (pow_ne_zero _ hxK_ne), one_pow, map_one, one_mul]
        rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
        rfl
      rw [hprod_g]
      have hexp : alg convX ^ (M - wt m) * alg convX ^ wt m = alg convX ^ M := by
        rw [← pow_add, Nat.sub_add_cancel (hwt_le m hm)]
      calc MvPolynomial.C (alg (P.coeff m) * alg convX ^ (M - wt m)) *
            (MvPolynomial.C (alg convX ^ wt m) * ∏ p ∈ m.support, g p ^ m p)
          = MvPolynomial.C (alg (P.coeff m)) *
              MvPolynomial.C (alg convX ^ (M - wt m) * alg convX ^ wt m) *
              ∏ p ∈ m.support, g p ^ m p := by rw [map_mul, map_mul]; ring
        _ = MvPolynomial.C (alg convX ^ M) *
              (MvPolynomial.C (alg (P.coeff m)) * ∏ p ∈ m.support, g p ^ m p) := by rw [hexp]; ring
    have haeval0 : MvPolynomial.aeval g (MvPolynomial.map alg P) = 0 := by
      rw [hPS_zero, map_zero] at hmap_PS
      have hCM_ne : (MvPolynomial.C (alg convX ^ M) : MvPolynomial (Fin d × Fin (r + 1)) K) ≠ 0 := by
        intro h0; exact pow_ne_zero M hxK_ne (MvPolynomial.C_eq_zero.mp h0)
      exact (mul_eq_zero.mp hmap_PS.symm).resolve_left hCM_ne
    -- Reindex Fin d × Fin (r + 1) ≃ Fin (N + 1) preserving block-triangularity: (i, j) ↦ i * (r + 1) + j
    let N : ℕ := d * (r + 1) - 1
    have hN1 : N + 1 = d * (r + 1) := Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d') (Nat.succ_pos r))
    let e : Fin d × Fin (r + 1) ≃ Fin (N + 1) :=
      finProdFinEquiv.trans (finCongr hN1.symm)
    have he_val : ∀ p : Fin d × Fin (r + 1), (e p).val = p.1.val * (r + 1) + p.2.val := fun p => by
      simp [e, finProdFinEquiv]; ring
    let g' : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K := fun q =>
      MvPolynomial.rename e (g (e.symm q))
    let u' : Fin (N + 1) → K := fun q =>
      (alg convX ^ (2 * (e.symm q).2.val + 1))⁻¹ * alg (convC ((-1 : ℂ) ^ (e.symm q).2.val))
    have hu'_unit : ∀ q : Fin (N + 1), IsUnit (u' q) := fun q => by
      refine isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hxK_ne)) ?_)
      intro h0
      have hC0 := halg_inj (h0.trans (map_zero alg).symm)
      have hc0 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 0 a.val) hC0
      simp [convC] at hc0
    let S' : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K := fun q =>
      let p := e.symm q
      MvPolynomial.C ((alg convX ^ (2 * p.2.val + 1))⁻¹) *
        ∑ k ∈ Finset.univ.filter (fun k : Fin (r + 1) => k.val < p.2.val),
          MvPolynomial.C (alg (convC (backCoeffFC p.2.val k.val) * convX ^ (p.2.val - k.val))) *
            MvPolynomial.X (e (p.1, k))
    have hg'_split : ∀ q : Fin (N + 1), g' q = MvPolynomial.C (u' q) * MvPolynomial.X q + S' q := by
      intro q
      let p := e.symm q
      have hsplit_filt : Finset.univ.filter (fun k : Fin (r + 1) => k.val ≤ p.2.val) =
          insert p.2 (Finset.univ.filter (fun k : Fin (r + 1) => k.val < p.2.val)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Nat.le_iff_lt_or_eq, Fin.ext_iff]
        tauto
      have hnotmem : p.2 ∉ Finset.univ.filter (fun k : Fin (r + 1) => k.val < p.2.val) := by simp
      dsimp only [g', g, jetConv, u', S']
      rw [map_mul, MvPolynomial.rename_C, map_sum, map_sum, hsplit_filt, Finset.sum_insert hnotmem,
        mul_add]
      congr 1
      · dsimp only [p]
        have heq_q : e ((e.symm q).1, (e.symm q).2) = q := e.apply_symm_apply q
        simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.rename_C,
          MvPolynomial.rename_X, backCoeffFC_diag, Nat.sub_self, pow_zero, mul_one, heq_q]
        rw [← mul_assoc]
      · congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.rename_C,
          MvPolynomial.rename_X]
    have hS'_vars : ∀ q : Fin (N + 1), ∀ k ∈ (S' q).vars, k.val < q.val := by
      intro q k hk
      dsimp only [S'] at hk
      rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk) with hC | hsum
      · exact absurd hC (by rw [MvPolynomial.vars_C]; simp)
      · obtain ⟨j, hj, hk_j⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hsum)
        rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk_j) with hC2 | hX
        · exact absurd hC2 (by rw [MvPolynomial.vars_C]; simp)
        · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hX
          subst hX
          have hjlt : j.val < (e.symm q).2.val := (Finset.mem_filter.mp hj).2
          have hq_val : q.val = (e.symm q).1.val * (r + 1) + (e.symm q).2.val := by
            conv_lhs => rw [← e.apply_symm_apply q]
            exact he_val (e.symm q)
          rw [he_val, hq_val]
          dsimp only
          omega
    have hrename_aeval : MvPolynomial.aeval g' (MvPolynomial.rename e (MvPolynomial.map alg P)) =
        MvPolynomial.rename e (MvPolynomial.aeval g (MvPolynomial.map alg P)) := by
      induction (MvPolynomial.map alg P) using MvPolynomial.induction_on with
      | C c => simp [MvPolynomial.algebraMap_eq]
      | add A B hA hB => simp only [map_add] at hA hB ⊢; rw [hA, hB]
      | mul_X A p hA =>
        simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.aeval_X, g', e.symm_apply_apply] at hA ⊢
        rw [hA]
    have haeval0' : MvPolynomial.aeval g' (MvPolynomial.rename e (MvPolynomial.map alg P)) = 0 := by
      rw [hrename_aeval, haeval0, map_zero]
    have hren0 : MvPolynomial.rename e (MvPolynomial.map alg P) = 0 :=
      triangular_aeval_injective g' u' hu'_unit S' hg'_split hS'_vars (haeval0'.trans (map_zero _).symm)
    have hmap0 : MvPolynomial.map alg P = 0 :=
      MvPolynomial.rename_injective e e.injective (hren0.trans (map_zero _).symm)
    exact MvPolynomial.map_injective alg halg_inj (hmap0.trans (map_zero _).symm)

/-- **Master Joint Multi-Series Strong `ℂ({t})` Differential Independence Theorem**:
For `d` plane-meromorphic minors `b : Fin d → ℂ → ℂ` with `PlaneSimplePoleData (b i)`, if for
every jet order `r : ℕ` there exists a family of poles `ω : Fin d × Fin (r + 1) → ℂ` in
`unionPoles h` whose joint residue-jet matrix `M p q := jointVec h (ω p) q` is invertible, then
the `d` formal OGFs `fun i => ogfOfEGF (b i)` are **jointly strongly differentially independent
over convergent meromorphic germs `ℂ({t})`**. -/
theorem finite_contour_joint_ogf_stronglyDTrans {d : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i))
    (hspan : ∀ r : ℕ, ∃ ω : Fin d × Fin (r + 1) → ℂ,
      (∀ p, ω p ∈ unionPoles h) ∧
      (Matrix.of (fun p q : Fin d × Fin (r + 1) => jointVec h (ω p) q)).det ≠ 0) :
    JointlyStronglyDTransOverMeromorphicGerms (fun i => ogfOfEGF (b i)) := by
  have hconv : JointlyStronglyDTransOverConvergent (fun i => ogfOfEGF (b i)) := by
    refine jointlyStronglyDTransOverConvergent_of_X_mul_no_conv_ade
      (F := fun i => ogfOfEGF (b i)) ?_
    intro r Q hQ
    obtain ⟨ω, hω_mem, hdet⟩ := hspan r
    have hS : (fun i => PowerSeries.X * ogfOfEGF (b i)) = fun i => formalSeries (b i) :=
      funext fun i => (formalSeries_eq_X_mul_ogfOfEGF (b i)).symm
    rw [hS] at hQ
    exact finite_contour_joint_no_conv_ade_of_det_ne_zero h ω hω_mem hdet Q hQ
  exact jointlyStronglyDTransOverMeromorphicGerms_of_convergent hconv

end
end PakPrimes.FiniteContourStokes


