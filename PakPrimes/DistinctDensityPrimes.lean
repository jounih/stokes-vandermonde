module

public import PakPrimes.PakNthPrimeUnconditional
import all PakPrimes.NthPrimeAbelError

/-! # Joint Differential Independence of Distinct-Density Prime-Like Sequences

This module formalizes the simultaneous differential independence of finitely (and countably)
many distinct-density prime-like ordinary generating functions, building directly on top of
`PakPrimes.PakNthPrimeUnconditional` (`I_entire`, `I_entire_div_hasGev1Exp`, `HasGev1Exp`).

### Non-Circular Parameter Schedule
All analytic estimates in Section 1 use three nested closed sectors sharing the exact same
center `θ₀ = -5π/24` and strictly positive opening `> π`:
- **Outer sector `Σ'`**: `θ₁' = -19π/24`, `θ₂' = 3π/8` (half-width `14π/24 = 28π/48`, opening `7π/6 > π`),
  radius `R_conv ≥ 10^6`, on which `PakNthPrimeUnconditional.I_entire_div_hasGev1Exp` provides
  `HasGev1Exp Σ' (fun u => I_entire u / u) a_I`.
- **Middle sector `Σ_mid`**: `theta1_mid = -37π/48`, `theta2_mid = 17π/48` (half-width `27π/48`,
  opening `9π/8 > π`, angle margin `π/48 > 1/16` inside `Σ'`), radius `R_mid = 2 * R_conv`.
  Cauchy differentiation (`hasGev1Exp_iteratedDeriv`) transfers `HasGev1Exp` from `Σ'` to every
  jet `u ↦ iteratedDeriv j I_entire u / u` on `Σ_mid`.
- **Common shrunk sector `Σ_common(δ)`**: `theta1 = -3π/4`, `theta2 = π/3` (half-width `13π/24 = 26π/48`,
  opening `13π/12 > π`, angle margin `π/48 > 1/16` inside `Σ_mid`), common radius
  `R_common(δ) = max (4 * R_conv) (32 * ∑ i, |Real.log (δ i)| + 2)` depending only on the
  finitely many positive densities `δ : Fin d → ℝ`.
  For every `u ∈ Σ_common(δ)` and every shift `a_i = -Real.log (δ i)`, we have `|a_i| / ‖u‖ ≤ 1/32`,
  so `u + a_i ∈ Σ_mid` and `Complex.log (u + a_i) = Complex.log u + Complex.log (1 + a_i / u)`.
  Shift closure (`hasGev1Exp_shift_mul`) gives `HasGev1Exp Σ_common(δ)` simultaneously for every
  shifted jet `u ↦ iteratedDeriv j (fun v => I_entire (v + a_i)) u / u`.

### Architecture
1. **Section 1 — Shifted Gevrey-1 Closure & Mixed-Tuple Watson Uniqueness**:
   - `hasGev1Exp_shift_mul`, `I_entire_shift_div_hasGev1Exp`,
     `I_entire_shift_iteratedDeriv_div_hasGev1Exp`.
   - `mixed_flat_implies_exact_vanishing`: any polynomial `P ∈ ℂ[X_{i,j}]` flat to all inverse
     powers on the upper shifted jets `J_i^+(u) = I_plus (u - log δ_i)` vanishes identically on
     both `J^+(u)` and `J^-(u)` for all `u : ℝ`.
2. **Section 2 — Simultaneous Affine Flow `B_op` & Additive-Wave Descent `L_m`**:
   - Degree-preserving linear derivation `B_op δ`, invariance `B_op_preserves_flatIdeal`,
     entire `τ`-flow `tau_invariance_multi`.
   - Constant vector fields `Lm_op δ m`, minimal-degree strong induction
     `strong_induction_Lm_multi_eq_zero`, and pairwise-distinct density dominance
     `distinctDensity_vanish_of_Lm_zero`, yielding `distinctDensity_ideal_eq_zero` and the
     100% unconditional analytic theorem `distinctDensity_branches_algebraicIndependent`.
3. **Section 3 — Counting Transfer & Pullback to Ordinary Generating Functions**:
   - `HasDensityPNT` → `HasScaledDensityAsymp` via Abel summation (`NthPrimeAbelError`) and
     rescaled inverse-`li` Riemann-sum MVT bounds.
   - Exact unitriangular `t`-adic pullback (`distinctDensity_ogf_joint_algebraicIndependent`)
     and the dyadic-density specialization `δ_k = 2 ^ (1 - k)` (both finite and countably infinite).
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.DistinctDensityPrimes

open Complex Real Filter MeasureTheory Set MvPolynomial
open scoped Topology BigOperators

noncomputable section

open PakPrimes.PakNthPrimeStokes PakPrimes.PakNthPrimeClosure PakPrimes.PakNthPrimeUnconditional

/-! ### Section 1. Shifted Gevrey-1 Closure on a Common Sector & Mixed Watson Uniqueness -/

/-- Intermediate sector angles `θ₁_mid = -37π/48`, `θ₂_mid = 17π/48` (center `-5π/24`,
half-width `27π/48`, opening `9π/8 > π`), leaving margin `π/48 > 1/16` both inside
`[theta1', theta2']` and outside `[theta1, theta2]`. -/
@[expose] def theta1_mid : ℝ := -37 * Real.pi / 48
@[expose] def theta2_mid : ℝ := 17 * Real.pi / 48

/-- Common radius for finitely many real shifts `a : Fin d → ℝ` on `[theta1, theta2]`. -/
@[expose] def commonShiftRadius {d : ℕ} (a : Fin d → ℝ) : ℝ :=
  max (4 * R_conv) (32 * (∑ i : Fin d, |a i|) + 2)

lemma commonShiftRadius_ge_four_R_conv {d : ℕ} (a : Fin d → ℝ) :
    4 * R_conv ≤ commonShiftRadius a :=
  le_max_left _ _

lemma commonShiftRadius_ge_one {d : ℕ} (a : Fin d → ℝ) :
    1 ≤ commonShiftRadius a := by
  have h1 := R_conv_ge_1e6
  have h2 := commonShiftRadius_ge_four_R_conv a
  norm_num at h1; linarith

lemma commonShiftRadius_pos {d : ℕ} (a : Fin d → ℝ) :
    0 < commonShiftRadius a :=
  lt_of_lt_of_le zero_lt_one (commonShiftRadius_ge_one a)

lemma abs_le_commonShiftRadius_div_32 {d : ℕ} (a : Fin d → ℝ) (i : Fin d) :
    |a i| ≤ commonShiftRadius a / 32 := by
  have h1 : |a i| ≤ ∑ k : Fin d, |a k| :=
    Finset.single_le_sum (f := fun k => |a k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : 32 * (∑ k : Fin d, |a k|) + 2 ≤ commonShiftRadius a := le_max_right _ _
  linarith

/-- Monotonicity of `HasGev1Exp` under shrinking the domain set `S`. -/
lemma hasGev1Exp_mono {S₁ S₂ : Set ℂ} (hsub : S₁ ⊆ S₂) {f : ℂ → ℂ} {a : LogCoeff}
    (hf : HasGev1Exp S₂ f a) : HasGev1Exp S₁ f a := by
  rcases hf with ⟨h0, C, hC, A, hA, hcoeff, hrem⟩
  exact ⟨h0, C, hC, A, hA, hcoeff, fun N z hz => hrem N z (hsub hz)⟩

/-- General additive perturbation lemma inside concentric rotated sectors with margin `π/48`:
if `z` lies in the inner sector with `2 * R_out ≤ ‖z‖` and `‖w‖ ≤ ‖z‖ / 32`, then `z + w` lies
in the outer sector with radius `R_out` and half-width enlarged by `π/48`. -/
lemma add_mem_rotatedClosedSector_of_margin
    {θ₁_in θ₂_in θ₁_out θ₂_out R_out : ℝ}
    (hR_out : 0 < R_out)
    (hcen : (θ₁_out + θ₂_out) / 2 = (θ₁_in + θ₂_in) / 2)
    (hhw_in : (θ₂_in - θ₁_in) / 2 ≤ 27 * Real.pi / 48)
    (hmargin : (θ₂_in - θ₁_in) / 2 + Real.pi / 48 ≤ (θ₂_out - θ₁_out) / 2)
    {z w : ℂ} (hz : z ∈ rotatedClosedSector θ₁_in θ₂_in (2 * R_out))
    (hw : ‖w‖ ≤ (1 / 32 : ℝ) * ‖z‖) :
    z + w ∈ rotatedClosedSector θ₁_out θ₂_out R_out := by
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith) hz.1
  have hz_ne : z ≠ 0 := norm_pos_iff.mp hz_pos
  have hzw_norm : R_out ≤ ‖z + w‖ := by
    have htri : ‖z‖ ≤ ‖z + w‖ + ‖w‖ := by
      have := norm_add_le (z + w) (-w)
      rw [add_neg_cancel_right, norm_neg] at this
      exact this
    linarith [hz.1]
  refine ⟨hzw_norm, ?_⟩
  rw [hcen]
  let invRot : ℂ := Complex.exp (-(((θ₁_in + θ₂_in) / 2 : ℝ) : ℂ) * I)
  let δ : ℂ := w / z
  have hδ_le : ‖δ‖ ≤ 1 / 32 := by
    dsimp only [δ]; rw [norm_div, div_le_iff₀ hz_pos]; linarith
  have h1δ_arg : |Complex.arg (1 + δ)| ≤ 1 / 16 := abs_arg_one_add_le hδ_le
  have h1δ_ne : 1 + δ ≠ 0 := by
    intro h0
    have h1 : ‖δ‖ = 1 := by
      have : δ = -1 := by linear_combination h0
      simp [this]
    linarith
  have hprod : invRot * (z + w) = (invRot * z) * (1 + δ) := by
    dsimp only [δ]; field_simp [hz_ne]
  have hpi48 : (1 / 16 : ℝ) ≤ Real.pi / 48 := by linarith [Real.pi_gt_three]
  have harg_z : |Complex.arg (invRot * z)| ≤ (θ₂_in - θ₁_in) / 2 := hz.2
  have hsum_in : Complex.arg (invRot * z) + Complex.arg (1 + δ) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 := abs_le.mp (harg_z.trans hhw_in)
    have h2 := abs_le.mp (h1δ_arg.trans hpi48)
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have harg_mul : Complex.arg (invRot * (z + w)) = Complex.arg (invRot * z) + Complex.arg (1 + δ) := by
    rw [hprod]
    have hne1 : invRot * z ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hz_ne
    have h := Complex.arg_mul_coe_angle hne1 h1δ_ne
    have h' : (((Complex.arg ((invRot * z) * (1 + δ)) : ℝ) : Real.Angle)) =
        (((Complex.arg (invRot * z) + Complex.arg (1 + δ) : ℝ) : Real.Angle)) := by
      simpa [Real.Angle.coe_add] using h
    have hto := congr_arg Real.Angle.toReal h'
    rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
      Real.Angle.toReal_coe_eq_self_iff.mpr hsum_in] at hto
    exact hto
  change |Complex.arg (invRot * (z + w))| ≤ (θ₂_out - θ₁_out) / 2
  rw [harg_mul]
  calc |Complex.arg (invRot * z) + Complex.arg (1 + δ)|
      ≤ |Complex.arg (invRot * z)| + |Complex.arg (1 + δ)| := abs_add_le _ _
    _ ≤ (θ₂_in - θ₁_in) / 2 + 1 / 16 := add_le_add harg_z h1δ_arg
    _ ≤ (θ₂_in - θ₁_in) / 2 + Real.pi / 48 := by linarith
    _ ≤ (θ₂_out - θ₁_out) / 2 := hmargin

/-- Disk containment for Cauchy differentiation from `Σ_mid` into `Σ'`. -/
lemma closedBall_mid_subset_enlarged {R₀ : ℝ} (hR₀ : 0 < R₀) {z : ℂ}
    (hz : z ∈ rotatedClosedSector theta1_mid theta2_mid (2 * R₀)) :
    Metric.closedBall z ((1 / 32 : ℝ) * ‖z‖) ⊆ rotatedClosedSector theta1' theta2' R₀ := by
  intro w hw
  have hdist : ‖w - z‖ ≤ (1 / 32 : ℝ) * ‖z‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have heq : z + (w - z) = w := by ring
  rw [← heq]
  exact add_mem_rotatedClosedSector_of_margin hR₀
    (by dsimp [theta1_mid, theta2_mid, theta1', theta2']; ring)
    (by dsimp [theta1_mid, theta2_mid]; linarith [Real.pi_pos])
    (by dsimp [theta1_mid, theta2_mid, theta1', theta2']; linarith [Real.pi_pos])
    hz hdist

/-- Sector containment `rotatedClosedSector theta1 theta2 R ⊆ rotatedClosedSector theta1_mid theta2_mid R`. -/
lemma sector_subset_mid {R : ℝ} :
    rotatedClosedSector theta1 theta2 R ⊆ rotatedClosedSector theta1_mid theta2_mid R := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hcen : (theta1_mid + theta2_mid) / 2 = (theta1 + theta2) / 2 := by
    dsimp [theta1_mid, theta2_mid, theta1, theta2]; ring
  rw [hcen]
  have hhw : (theta2 - theta1) / 2 ≤ (theta2_mid - theta1_mid) / 2 := by
    dsimp [theta1_mid, theta2_mid, theta1, theta2]; linarith [Real.pi_pos]
  exact hz.2.trans hhw

/-- Sector containment `rotatedClosedSector theta1_mid theta2_mid R ⊆ rotatedClosedSector theta1' theta2' R`. -/
lemma mid_subset_enlarged {R : ℝ} :
    rotatedClosedSector theta1_mid theta2_mid R ⊆ rotatedClosedSector theta1' theta2' R := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hcen : (theta1' + theta2') / 2 = (theta1_mid + theta2_mid) / 2 := by
    dsimp [theta1_mid, theta2_mid, theta1', theta2']; ring
  rw [hcen]
  have hhw : (theta2_mid - theta1_mid) / 2 ≤ (theta2' - theta1') / 2 := by
    dsimp [theta1_mid, theta2_mid, theta1', theta2']; linarith [Real.pi_pos]
  exact hz.2.trans hhw

/-- Argument range on `rotatedClosedSector theta1' theta2' R` (`R > 0`): `arg u ∈ [-19π/24, 3π/8]`. -/
lemma rotatedClosedSector_enlarged_arg_mem_any {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu : u ∈ rotatedClosedSector theta1' theta2' R) :
    theta1' ≤ Complex.arg u ∧ Complex.arg u ≤ theta2' := by
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le hR hu.1
  have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hcen : (theta1' + theta2') / 2 = -5 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
  have hhw : (theta2' - theta1') / 2 = 14 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
  let α : ℝ := 5 * Real.pi / 24
  have hrot : Complex.exp (-(((theta1' + theta2') / 2 : ℝ) : ℂ) * I) = Complex.exp ((α : ℂ) * I) := by
    rw [hcen]; congr 1; dsimp [α]; push_cast; ring
  have harg_rot : Complex.arg (Complex.exp ((α : ℂ) * I)) = α := by
    have him : ((α : ℂ) * I).im = α := by simp
    rw [arg_cexp_eq_im (by rw [him]; dsimp [α]; linarith [Real.pi_pos])
      (by rw [him]; dsimp [α]; linarith [Real.pi_pos]), him]
  have hangle := Complex.arg_mul_coe_angle (Complex.exp_ne_zero ((α : ℂ) * I)) hu0
  rw [harg_rot] at hangle
  have h1 : |Complex.arg (Complex.exp ((α : ℂ) * I) * u)| ≤ 14 * Real.pi / 24 := by
    have h2 := hu.2
    rw [hrot, hhw] at h2
    exact h2
  -- Show `α + arg u ∈ (-π, π]` or `α + arg u - 2π ∈ (-π, π]`
  have hlo : -Real.pi < Complex.arg u := Complex.neg_pi_lt_arg u
  have hhi : Complex.arg u ≤ Real.pi := Complex.arg_le_pi u
  by_cases hsum_le : α + Complex.arg u ≤ Real.pi
  · have hsum_in : α + Complex.arg u ∈ Set.Ioc (-Real.pi) Real.pi :=
      ⟨by dsimp [α]; linarith [Real.pi_pos], hsum_le⟩
    have hto := congr_arg Real.Angle.toReal hangle
    rw [← Real.Angle.coe_add,
      Real.Angle.toReal_coe_eq_self_iff.mpr ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
      Real.Angle.toReal_coe_eq_self_iff.mpr hsum_in] at hto
    rw [hto, abs_le] at h1
    dsimp only [α] at h1
    dsimp only [theta1', theta2']
    constructor <;> linarith [h1.1, h1.2]
  · push Not at hsum_le
    have hsum_in : α + Complex.arg u - 2 * Real.pi ∈ Set.Ioc (-Real.pi) Real.pi :=
      ⟨by linarith [Real.pi_pos], by dsimp [α]; linarith [Real.pi_pos]⟩
    have hcoe : ((α : Real.Angle) + (Complex.arg u : Real.Angle)) =
        (((α + Complex.arg u - 2 * Real.pi : ℝ) : Real.Angle)) := by
      rw [← Real.Angle.coe_add, Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]
    rw [hcoe] at hangle
    have hto := congr_arg Real.Angle.toReal hangle
    rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
      Real.Angle.toReal_coe_eq_self_iff.mpr hsum_in] at hto
    rw [hto, abs_le] at h1
    dsimp only [α] at h1 hsum_le
    linarith [h1.1, Real.pi_pos]

/-- Complex logarithm splitting `log (u + a) = log u + log (1 + a / u)` on `rotatedClosedSector theta1' theta2' R`
whenever `|a| ≤ ‖u‖ / 32`. -/
lemma clog_add_ofReal_eq_general {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu : u ∈ rotatedClosedSector theta1' theta2' R) {a : ℝ} (ha : |a| ≤ ‖u‖ / 32) :
    Complex.log (u + (a : ℂ)) = Complex.log u + Complex.log (1 + (a : ℂ) / u) := by
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le hR hu.1
  have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
  let t : ℂ := (a : ℂ) / u
  have ht_norm : ‖t‖ ≤ 1 / 32 := by
    dsimp only [t]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hu_pos]; linarith
  have h1t_re : (31 / 32 : ℝ) ≤ (1 + t).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm t).trans ht_norm)).1
    simp only [Complex.add_re, Complex.one_re]; linarith
  have h1t0 : 1 + t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (h1t_re.trans (Complex.re_le_norm _)))
  have harg_1t : |Complex.arg (1 + t)| ≤ 1 / 16 := abs_arg_one_add_le ht_norm
  have hpi48 : (1 / 16 : ℝ) ≤ Real.pi / 48 := by linarith [Real.pi_gt_three]
  obtain ⟨harg_lo, harg_hi⟩ := rotatedClosedSector_enlarged_arg_mem_any hR hu
  have h1t_abs := abs_le.mp (harg_1t.trans hpi48)
  have hprod : u + (a : ℂ) = u * (1 + t) := by dsimp only [t]; field_simp [hu0]
  rw [hprod]
  exact Complex.log_mul hu0 h1t0
    ⟨by dsimp only [theta1'] at harg_lo; linarith [Real.pi_pos],
     by dsimp only [theta2'] at harg_hi; linarith [Real.pi_pos]⟩

/-- Formal Gevrey-1 log-power coefficients for `(1 + a / u) * f (u + a)` induced by shifting `b`. -/
@[expose] def shiftLogCoeff (a : ℝ) (b : LogCoeff) (d l : ℕ) : ℂ :=
  if d < l then 0 else
  ∑ n ∈ Finset.range (d + 1),
    ∑ k ∈ Finset.range (n + 1),
      if l ≤ k then
        b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) * ((a : ℂ) ^ (d - n))
      else 0

/-- Algebraic reindexing of `evalTrunc (shiftLogCoeff a b) N u` into the `(n, m, k, l)` quadruple sum. -/
lemma evalTrunc_shiftLogCoeff_eq (a : ℝ) (b : LogCoeff) (N : ℕ) (u : ℂ) :
    evalTrunc (shiftLogCoeff a b) N u =
      ∑ n ∈ Finset.range N,
        ∑ m ∈ Finset.range (N - n),
          ∑ k ∈ Finset.range (n + 1),
            ∑ l ∈ Finset.range (k + 1),
              b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                ((a : ℂ) ^ m) * (Complex.log u ^ l / u ^ (n + m)) := by
  have hterm : ∀ d : ℕ, evalTerm (shiftLogCoeff a b) d u =
      ∑ n ∈ Finset.range (d + 1),
        ∑ k ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (k + 1),
            b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
              ((a : ℂ) ^ (d - n)) * (Complex.log u ^ l / u ^ d) := by
    intro d
    dsimp only [evalTerm]
    rw [Finset.sum_div]
    have h1 : ∑ l ∈ Finset.range (d + 1), shiftLogCoeff a b d l * Complex.log u ^ l / u ^ d =
        ∑ l ∈ Finset.range (d + 1),
          ∑ n ∈ Finset.range (d + 1),
            ∑ k ∈ Finset.range (n + 1),
              (if l ≤ k then
                b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
                  ((a : ℂ) ^ (d - n)) * (Complex.log u ^ l / u ^ d)
              else 0) := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hdl : ¬ d < l := by simp only [Finset.mem_range] at hl; omega
      dsimp only [shiftLogCoeff]; simp only [hdl, ↓reduceIte]
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd : k ≤ d := by simp only [Finset.mem_range] at hn hk; omega
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range (d + 1)).filter (fun l => l ≤ k) = Finset.range (k + 1) := by
      ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt]
  dsimp only [evalTrunc]
  simp_rw [hterm]
  let F : ℕ → ℕ → ℂ := fun n m =>
    ∑ k ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (k + 1),
        b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
          ((a : ℂ) ^ m) * (Complex.log u ^ l / u ^ (n + m))
  have hL : (∑ d ∈ Finset.range N, ∑ n ∈ Finset.range (d + 1),
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
        b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
          ((a : ℂ) ^ (d - n)) * (Complex.log u ^ l / u ^ d)) =
      ∑ p ∈ (Finset.range N).sigma (fun d => Finset.range (d + 1)), F p.2 (p.1 - p.2) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    dsimp only [F]
    have hadd : p.2 + (p.1 - p.2) = p.1 := Nat.add_sub_of_le (by omega)
    rw [hadd]
  have hR : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (N - n), F n m) =
      ∑ q ∈ (Finset.range N).sigma (fun n => Finset.range (N - n)), F q.1 q.2 :=
    Finset.sum_sigma' _ _ _
  rw [hL, hR]
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 - p.2⟩) (fun q => ⟨q.1 + q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp; simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢; omega
  · intro q hq; simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢; omega
  · intro p hp; simp only [Finset.mem_sigma, Finset.mem_range] at hp
    exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
  · intro q hq; simp only [Finset.mem_sigma, Finset.mem_range] at hq
    exact Sigma.ext rfl (heq_of_eq (by dsimp; omega))
  · intro p _; rfl

/-- Elementary bound `(d + 1)^2 ≤ 4 ^ d` for all `d : ℕ`. -/
lemma nat_add_one_sq_le_four_pow_dd (d : ℕ) : ((d : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ d := by
  have h1 := nat_succ_le_two_pow d
  calc ((d : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ = ((2 : ℝ) ^ 2) ^ d := by rw [← pow_mul, mul_comm, pow_mul]
    _ = (4 : ℝ) ^ d := by norm_num

/-- **Real-Shift Closure of `HasGev1Exp`**:
If `f` satisfies `HasGev1Exp (rotatedClosedSector θ₁_out θ₂_out R_out) f b` on a sector
contained in `[theta1', theta2']`, then for any fixed real shift `a : ℝ`, on the concentric
shrunk sector `S_in = rotatedClosedSector θ₁_in θ₂_in R_in` (with margin `π/48` and
`R_in ≥ max (2 * R_out) (32 * |a| + 2)`), the shifted function `u ↦ (1 + a / u) * f (u + a)`
satisfies `HasGev1Exp S_in _ (shiftLogCoeff a b)`. -/
theorem hasGev1Exp_shift_mul
    {θ₁_in θ₂_in θ₁_out θ₂_out R_out R_in : ℝ}
    (hR_out : 1 ≤ R_out)
    (hR_in_out : 2 * R_out ≤ R_in)
    (hcen : (θ₁_out + θ₂_out) / 2 = (θ₁_in + θ₂_in) / 2)
    (hhw_in : (θ₂_in - θ₁_in) / 2 ≤ 27 * Real.pi / 48)
    (hmargin : (θ₂_in - θ₁_in) / 2 + Real.pi / 48 ≤ (θ₂_out - θ₁_out) / 2)
    (hsub_enlarged : rotatedClosedSector θ₁_in θ₂_in R_in ⊆ rotatedClosedSector theta1' theta2' R_in)
    (a : ℝ) (ha_R : 32 * |a| + 2 ≤ R_in)
    {f : ℂ → ℂ} {b : LogCoeff}
    (hf : HasGev1Exp (rotatedClosedSector θ₁_out θ₂_out R_out) f b) :
    HasGev1Exp (rotatedClosedSector θ₁_in θ₂_in R_in)
      (fun u => (1 + (a : ℂ) / u) * f (u + (a : ℂ))) (shiftLogCoeff a b) := by
  rcases hf with ⟨hb0, C, hC, A, hA, hb_coeff, hb_rem⟩
  have hR_out_pos : 0 < R_out := by linarith
  have hR_in_ge1 : 1 ≤ R_in := by linarith
  have hR_in_pos : 0 < R_in := by linarith
  let M_a : ℝ := |a| + 1
  have hMa_ge1 : 1 ≤ M_a := by dsimp [M_a]; linarith [abs_nonneg a]
  let C_fin : ℝ := (4 + 4 * Real.exp (Real.pi + 1)) * C
  let A_fin : ℝ := 8 * A * M_a
  have hC_fin : 0 < C_fin := by dsimp [C_fin]; positivity
  have hA_fin : 1 ≤ A_fin := by dsimp [A_fin]; nlinarith
  refine ⟨fun d l hdl => by simp [shiftLogCoeff, hdl], C_fin, hC_fin, A_fin, hA_fin, ?_, ?_⟩
  · -- Part 1: Gevrey-1 coefficient bound for `shiftLogCoeff a b`
    intro d l hld
    dsimp only [shiftLogCoeff]
    simp only [not_lt.mpr hld, ↓reduceIte]
    have hinner : ∀ n ∈ Finset.range (d + 1), ∀ k ∈ Finset.range (n + 1),
        ‖if l ≤ k then b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) * ((a : ℂ) ^ (d - n)) else 0‖ ≤
          (2 * C) * (2 * A * M_a) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by
      intro n hn k hk
      simp only [Finset.mem_range] at hn hk
      split_ifs with hlk
      · rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        have h1 := hb_coeff n k (by omega)
        have h2 := norm_shiftC_le n (k - l) (d - n)
        have h3 : |a| ^ (d - n) ≤ M_a ^ d :=
          (pow_le_pow_left₀ (abs_nonneg a) (by dsimp [M_a]; linarith) (d - n)).trans
            (pow_le_pow_right₀ hMa_ge1 (by omega))
        have hch_eq : ((k.choose l : ℕ) : ℝ) =
            (k.factorial : ℝ) / ((l.factorial : ℝ) * ((k - l).factorial : ℝ)) := by
          have h := Nat.choose_mul_factorial_mul_factorial hlk
          have hcast : ((k.choose l : ℕ) : ℝ) * (l.factorial : ℝ) * ((k - l).factorial : ℝ) = (k.factorial : ℝ) := by
            exact_mod_cast h
          have hlpos : (0 : ℝ) < (l.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos l)
          have hklpos : (0 : ℝ) < ((k - l).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos (k - l))
          rw [eq_div_iff (by positivity)]; linarith
        have h2pow : (2 : ℝ) ^ (n + 1 + (d - n)) = 2 * (2 : ℝ) ^ d := by
          have : n + 1 + (d - n) = d + 1 := by omega
          rw [this, pow_succ]; ring
        have hA_le : A ^ n ≤ A ^ d := pow_le_pow_right₀ hA (by omega)
        have hfac_le : (n.factorial : ℝ) ≤ (d.factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le (by omega : n ≤ d)
        have hkl_ge1 : (1 : ℝ) ≤ ((k - l).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - l)
        have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
        have hl_pos : (0 : ℝ) < (l.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos l)
        calc ‖b n k‖ * (k.choose l : ℝ) * ‖shiftC n (k - l) (d - n)‖ * |a| ^ (d - n)
            ≤ (C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) * (k.choose l : ℝ) *
                ((2 : ℝ) ^ (n + 1 + (d - n))) * M_a ^ d := by gcongr
          _ = 2 * C * A ^ n * (2 : ℝ) ^ d * M_a ^ d *
                ((n.factorial : ℝ) / ((l.factorial : ℝ) * ((k - l).factorial : ℝ))) := by
              rw [hch_eq, h2pow]; field_simp [hk_pos.ne', hl_pos.ne']
          _ ≤ 2 * C * A ^ d * (2 : ℝ) ^ d * M_a ^ d *
                ((d.factorial : ℝ) / ((l.factorial : ℝ) * 1)) := by
              have hdiv : (n.factorial : ℝ) / ((l.factorial : ℝ) * ((k - l).factorial : ℝ)) ≤
                  (d.factorial : ℝ) / ((l.factorial : ℝ) * 1) :=
                div_le_div₀ (by positivity) hfac_le (by positivity)
                  (mul_le_mul_of_nonneg_left hkl_ge1 hl_pos.le)
              gcongr
          _ = (2 * C) * (2 * A * M_a) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by
              rw [mul_one, mul_pow, mul_pow]; ring
      · rw [norm_zero]; positivity
    have hsum_le : ‖∑ n ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (n + 1),
          if l ≤ k then b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) * ((a : ℂ) ^ (d - n)) else 0‖ ≤
        ((d : ℝ) + 1) ^ 2 * ((2 * C) * (2 * A * M_a) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) := by
      calc _ ≤ ∑ n ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (n + 1),
              ‖if l ≤ k then b n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) * ((a : ℂ) ^ (d - n)) else 0‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
        _ ≤ ∑ n ∈ Finset.range (d + 1), ∑ _k ∈ Finset.range (n + 1),
              ((2 * C) * (2 * A * M_a) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) :=
            Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hinner n hn k hk
        _ ≤ ∑ _n ∈ Finset.range (d + 1), ((d : ℝ) + 1) *
              ((2 * C) * (2 * A * M_a) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hnd : ((n + 1 : ℕ) : ℝ) ≤ (d : ℝ) + 1 := by
              simp only [Finset.mem_range] at hn; exact_mod_cast (show n + 1 ≤ d + 1 by omega)
            exact mul_le_mul_of_nonneg_right hnd (by positivity)
        _ = ((d : ℝ) + 1) ^ 2 * ((2 * C) * (2 * A * M_a) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have h2C : 2 * C ≤ C_fin := by dsimp [C_fin]; nlinarith [Real.exp_pos (Real.pi + 1)]
    calc _ ≤ (4 : ℝ) ^ d * ((2 * C) * (2 * A * M_a) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) :=
          hsum_le.trans (mul_le_mul_of_nonneg_right (nat_add_one_sq_le_four_pow_dd d) (by positivity))
      _ = (2 * C) * A_fin ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by
          dsimp only [A_fin]
          have : (4 : ℝ) ^ d * (2 * A * M_a) ^ d = (8 * A * M_a) ^ d := by
            rw [← mul_pow]; congr 1; ring
          calc _ = (2 * C) * ((4 : ℝ) ^ d * (2 * A * M_a) ^ d) * (d.factorial : ℝ) / (l.factorial : ℝ) := by ring
            _ = _ := by rw [this]
      _ ≤ C_fin * A_fin ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by gcongr
  · -- Part 2: Uniform Gevrey-1 remainder bound
    intro N u hu
    have hu_R : R_in ≤ ‖u‖ := hu.1
    have hu_ge1 : 1 ≤ ‖u‖ := hR_in_ge1.trans hu_R
    have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu_ge1
    have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
    have ha_le : |a| ≤ ‖u‖ / 32 := by linarith
    have ha_norm_le : ‖(a : ℂ)‖ ≤ (1 / 32 : ℝ) * ‖u‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have ht_le : ‖(a : ℂ) / u‖ ≤ 1 / 4 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hu_pos]; linarith
    have hu_in_2R : u ∈ rotatedClosedSector θ₁_in θ₂_in (2 * R_out) :=
      ⟨hR_in_out.trans hu.1, hu.2⟩
    have hua_mem : u + (a : ℂ) ∈ rotatedClosedSector θ₁_out θ₂_out R_out :=
      add_mem_rotatedClosedSector_of_margin hR_out_pos hcen hhw_in hmargin hu_in_2R ha_norm_le
    have hua_norm_lo : (1 / 2 : ℝ) * ‖u‖ ≤ ‖u + (a : ℂ)‖ := by
      have htri : ‖u‖ ≤ ‖u + (a : ℂ)‖ + ‖(a : ℂ)‖ := by
        have := norm_add_le (u + (a : ℂ)) (-(a : ℂ))
        rw [add_neg_cancel_right, norm_neg] at this; exact this
      linarith
    have hua_norm_hi : ‖u + (a : ℂ)‖ ≤ 2 * ‖u‖ := by
      have htri := norm_add_le u (a : ℂ)
      linarith
    have h1a_le : ‖(1 : ℂ) + (a : ℂ) / u‖ ≤ 2 := by
      calc ‖(1 : ℂ) + (a : ℂ) / u‖ ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) / u‖ := norm_add_le _ _
        _ ≤ 1 + 1 / 4 := by rw [norm_one]; linarith
        _ ≤ 2 := by norm_num
    -- Split remainder into `P₁ + P₂`
    let P₁ : ℂ := (1 + (a : ℂ) / u) * (f (u + (a : ℂ)) - evalTrunc b N (u + (a : ℂ)))
    let P₂ : ℂ := (1 + (a : ℂ) / u) * evalTrunc b N (u + (a : ℂ)) - evalTrunc (shiftLogCoeff a b) N u
    have hsplit : (1 + (a : ℂ) / u) * f (u + (a : ℂ)) - evalTrunc (shiftLogCoeff a b) N u = P₁ + P₂ := by
      dsimp only [P₁, P₂]; ring
    rw [hsplit]
    -- Bound `P₁`: original truncation remainder at `u + a`
    have hP1 : ‖P₁‖ ≤ (4 * C) * ‖u‖ * A_fin ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
      dsimp only [P₁]
      rw [norm_mul]
      have hrem := hb_rem N (u + (a : ℂ)) hua_mem
      have hpow_lo : ((1 / 2 : ℝ) * ‖u‖) ^ N ≤ ‖u + (a : ℂ)‖ ^ N :=
        pow_le_pow_left₀ (by positivity) hua_norm_lo N
      have h2A : 2 * A ≤ A_fin := by dsimp [A_fin]; nlinarith
      calc ‖(1 : ℂ) + (a : ℂ) / u‖ * ‖f (u + (a : ℂ)) - evalTrunc b N (u + (a : ℂ))‖
          ≤ 2 * (C * ‖u + (a : ℂ)‖ * A ^ N * (N.factorial : ℝ) / ‖u + (a : ℂ)‖ ^ N) :=
            mul_le_mul h1a_le hrem (norm_nonneg _) (by norm_num)
        _ ≤ 2 * (C * (2 * ‖u‖) * A ^ N * (N.factorial : ℝ) / ((1 / 2 : ℝ) * ‖u‖) ^ N) := by gcongr
        _ = (4 * C) * ‖u‖ * (2 * A) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
            rw [mul_pow, mul_pow]
            have hhalf : (1 / 2 : ℝ) ^ N * (2 : ℝ) ^ N = 1 := by rw [← mul_pow]; norm_num
            have hhalf_ne : (1 / 2 : ℝ) ^ N ≠ 0 := by positivity
            field_simp [hu_pos.ne', hhalf_ne]
            calc (2 : ℝ) ^ 2 = 4 * 1 := by norm_num
              _ = 4 * ((1 / 2 : ℝ) ^ N * (2 : ℝ) ^ N) := by rw [hhalf]
              _ = (1 / 2 : ℝ) ^ N * 4 * (2 : ℝ) ^ N := by ring
        _ ≤ (4 * C) * ‖u‖ * A_fin ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by gcongr
    -- Bound `P₂`: Taylor tail of `shiftBasis`
    have hP2 : ‖P₂‖ ≤ (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * A_fin ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
      have hlog := clog_add_ofReal_eq_general hR_in_pos (hsub_enlarged hu) ha_le
      have hua : u + (a : ℂ) = u * (1 + (a : ℂ) / u) := by field_simp [hu0]
      have hP2_eq : P₂ =
          ∑ n ∈ Finset.range N,
            ∑ k ∈ Finset.range (n + 1),
              ∑ l ∈ Finset.range (k + 1),
                b n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                  (shiftBasis n (k - l) ((a : ℂ) / u) -
                    ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((a : ℂ) / u) ^ m) := by
        have h1 : (1 + (a : ℂ) / u) * evalTrunc b N (u + (a : ℂ)) =
            ∑ n ∈ Finset.range N,
              ∑ k ∈ Finset.range (n + 1),
                ∑ l ∈ Finset.range (k + 1),
                  b n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                    shiftBasis n (k - l) ((a : ℂ) / u) := by
          dsimp only [evalTrunc, evalTerm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hlog, add_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp only [shiftBasis]
          rw [hua, mul_pow, div_eq_mul_inv, mul_inv, ← inv_pow]
          ring
        have h2 : evalTrunc (shiftLogCoeff a b) N u =
            ∑ n ∈ Finset.range N,
              ∑ k ∈ Finset.range (n + 1),
                ∑ l ∈ Finset.range (k + 1),
                  b n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                    (∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((a : ℂ) / u) ^ m) := by
          rw [evalTrunc_shiftLogCoeff_eq]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [div_pow, pow_add]; ring
        dsimp only [P₂]
        rw [h1, h2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => by ring
      have hlog_pow_le : ∀ k : ℕ, (1 + ‖Complex.log u‖) ^ k / (k.factorial : ℝ) ≤
          Real.exp (Real.pi + 1) * ‖u‖ := by
        intro k
        calc (1 + ‖Complex.log u‖) ^ k / (k.factorial : ℝ)
            ≤ Real.exp (1 + ‖Complex.log u‖) := Real.pow_div_factorial_le_exp _ (by positivity) k
          _ = Real.exp 1 * Real.exp ‖Complex.log u‖ := Real.exp_add 1 _
          _ ≤ Real.exp 1 * (Real.exp Real.pi * ‖u‖) :=
              mul_le_mul_of_nonneg_left (exp_norm_log_le hu_ge1) (Real.exp_pos 1).le
          _ = Real.exp (Real.pi + 1) * ‖u‖ := by rw [Real.exp_add]; ring
      have hterm_nk : ∀ n ∈ Finset.range N, ∀ k ∈ Finset.range (n + 1),
          ‖∑ l ∈ Finset.range (k + 1),
            b n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
              (shiftBasis n (k - l) ((a : ℂ) / u) -
                ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((a : ℂ) / u) ^ m)‖ ≤
            (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * (2 * A * M_a) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
        intro n hn k hk
        simp only [Finset.mem_range] at hn hk
        have hrem_a : ∀ l : ℕ, ‖shiftBasis n (k - l) ((a : ℂ) / u) -
              ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((a : ℂ) / u) ^ m‖ ≤
            (2 : ℝ) ^ (n + 2) * (2 * (|a| / ‖u‖)) ^ (N - n) := by
          intro l
          have h := norm_shiftBasis_sub_sum_le n (k - l) (N - n) ht_le
          rwa [norm_div, Complex.norm_real, Real.norm_eq_abs] at h
        have hsum_l : ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖Complex.log u‖ ^ l =
            (1 + ‖Complex.log u‖) ^ k := by
          have h := add_pow ‖Complex.log u‖ (1 : ℝ) k
          rw [add_comm] at h; simpa [one_pow, mul_comm] using h.symm
        have hfac_n : (2 : ℝ) ^ (n + 2) * (2 * (|a| / ‖u‖)) ^ (N - n) / ‖u‖ ^ n ≤
            4 * (2 * M_a) ^ N / ‖u‖ ^ N := by
          rw [mul_pow, div_pow]
          have hadd : n + (N - n) = N := Nat.add_sub_of_le (by omega)
          have h2 : (2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (N - n) = 4 * (2 : ℝ) ^ N := by
            calc (2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (N - n)
                = 4 * ((2 : ℝ) ^ n * (2 : ℝ) ^ (N - n)) := by rw [pow_add]; ring
              _ = 4 * (2 : ℝ) ^ N := by rw [← pow_add, hadd]
          have hu_pow : ‖u‖ ^ (N - n) * ‖u‖ ^ n = ‖u‖ ^ N := by rw [← pow_add, add_comm, hadd]
          have ha_pow : |a| ^ (N - n) ≤ M_a ^ N :=
            (pow_le_pow_left₀ (abs_nonneg a) (by dsimp [M_a]; linarith) (N - n)).trans
              (pow_le_pow_right₀ hMa_ge1 (by omega))
          calc (2 : ℝ) ^ (n + 2) * ((2 : ℝ) ^ (N - n) * (|a| ^ (N - n) / ‖u‖ ^ (N - n))) / ‖u‖ ^ n
              = ((2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (N - n)) * |a| ^ (N - n) / (‖u‖ ^ (N - n) * ‖u‖ ^ n) := by
                field_simp [hu_pos.ne']
            _ = 4 * (2 : ℝ) ^ N * |a| ^ (N - n) / ‖u‖ ^ N := by rw [h2, hu_pow]
            _ ≤ 4 * (2 : ℝ) ^ N * M_a ^ N / ‖u‖ ^ N := by gcongr
            _ = 4 * (2 * M_a) ^ N / ‖u‖ ^ N := by rw [mul_pow]; ring
        have hA_le : A ^ n ≤ A ^ N := pow_le_pow_right₀ hA (by omega)
        have hfac_le : (n.factorial : ℝ) ≤ (N.factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le (by omega : n ≤ N)
        calc ‖∑ l ∈ Finset.range (k + 1), _‖
            ≤ ∑ l ∈ Finset.range (k + 1), ‖b n k‖ * (k.choose l : ℝ) *
                (‖Complex.log u‖ ^ l / ‖u‖ ^ n) *
                ((2 : ℝ) ^ (n + 2) * (2 * (|a| / ‖u‖)) ^ (N - n)) := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_div, norm_pow, norm_pow]
              exact mul_le_mul_of_nonneg_left (hrem_a l) (by positivity)
          _ = ‖b n k‖ * (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖Complex.log u‖ ^ l) *
                ((2 : ℝ) ^ (n + 2) * (2 * (|a| / ‖u‖)) ^ (N - n) / ‖u‖ ^ n) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun l _ => by ring
          _ ≤ (C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) * (1 + ‖Complex.log u‖) ^ k *
                (4 * (2 * M_a) ^ N / ‖u‖ ^ N) := by
              rw [hsum_l]
              have hbnk := hb_coeff n k (by omega)
              gcongr
          _ = (C * A ^ n * (n.factorial : ℝ)) * ((1 + ‖Complex.log u‖) ^ k / (k.factorial : ℝ)) *
                (4 * (2 * M_a) ^ N / ‖u‖ ^ N) := by ring
          _ ≤ (C * A ^ N * (N.factorial : ℝ)) * (Real.exp (Real.pi + 1) * ‖u‖) *
                (4 * (2 * M_a) ^ N / ‖u‖ ^ N) := by
              have hlp := hlog_pow_le k
              gcongr
          _ = (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * (2 * A * M_a) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
              have : A ^ N * (2 * M_a) ^ N = (2 * A * M_a) ^ N := by rw [← mul_pow]; congr 1; ring
              calc _ = (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * (A ^ N * (2 * M_a) ^ N) * (N.factorial : ℝ) / ‖u‖ ^ N := by ring
                _ = _ := by rw [this]
      rw [hP2_eq]
      let B2 : ℝ := (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * (2 * A * M_a) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N
      have hB2_nn : 0 ≤ B2 := by dsimp [B2]; positivity
      have hsum_nk : ‖∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
            b n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
              (shiftBasis n (k - l) ((a : ℂ) / u) -
                ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((a : ℂ) / u) ^ m)‖ ≤
          ((N : ℝ) + 1) ^ 2 * B2 := by
        calc _ ≤ ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1),
                ‖∑ l ∈ Finset.range (k + 1), _‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
          _ ≤ ∑ n ∈ Finset.range N, ∑ _k ∈ Finset.range (n + 1), B2 :=
              Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hterm_nk n hn k hk
          _ ≤ ∑ _n ∈ Finset.range N, ((N : ℝ) + 1) * B2 := by
              refine Finset.sum_le_sum fun n hn => ?_
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              have h1 : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
                simp only [Finset.mem_range] at hn; exact_mod_cast (show n + 1 ≤ N + 1 by omega)
              exact mul_le_mul_of_nonneg_right h1 hB2_nn
          _ = (N : ℝ) * (((N : ℝ) + 1) * B2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ ((N : ℝ) + 1) ^ 2 * B2 := by
              have hN : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
              nlinarith [hB2_nn]
      calc _ ≤ (4 : ℝ) ^ N * B2 := hsum_nk.trans (mul_le_mul_of_nonneg_right (nat_add_one_sq_le_four_pow_dd N) hB2_nn)
        _ = (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * A_fin ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
            dsimp only [B2, A_fin]
            have : (4 : ℝ) ^ N * (2 * A * M_a) ^ N = (8 * A * M_a) ^ N := by rw [← mul_pow]; congr 1; ring
            calc _ = (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * ((4 : ℝ) ^ N * (2 * A * M_a) ^ N) * (N.factorial : ℝ) / ‖u‖ ^ N := by ring
              _ = _ := by rw [this]
    calc ‖P₁ + P₂‖ ≤ ‖P₁‖ + ‖P₂‖ := norm_add_le _ _
      _ ≤ (4 * C) * ‖u‖ * A_fin ^ N * (N.factorial : ℝ) / ‖u‖ ^ N +
            (4 * Real.exp (Real.pi + 1) * C) * ‖u‖ * A_fin ^ N * (N.factorial : ℝ) / ‖u‖ ^ N :=
          add_le_add hP1 hP2
      _ = C_fin * ‖u‖ * A_fin ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by dsimp [C_fin]; ring

/-- **Shifted Gevrey-1 Closure for `I_entire (u + a) / u`** on the middle sector `Σ_mid`. -/
theorem I_entire_shift_div_hasGev1Exp (a : ℝ) :
    ∃ a_shift : LogCoeff,
      HasGev1Exp (rotatedClosedSector theta1_mid theta2_mid (max (2 * R_conv) (32 * |a| + 2)))
        (fun u => I_entire (u + (a : ℂ)) / u) a_shift := by
  obtain ⟨a_I, ha_I⟩ := I_entire_div_hasGev1Exp
  let R_a : ℝ := max (2 * R_conv) (32 * |a| + 2)
  have hR_conv_ge1 : 1 ≤ R_conv := by have h := R_conv_ge_1e6; norm_num at h; linarith
  have hshift := hasGev1Exp_shift_mul
    (θ₁_in := theta1_mid) (θ₂_in := theta2_mid) (θ₁_out := theta1') (θ₂_out := theta2')
    (R_out := R_conv) (R_in := R_a)
    hR_conv_ge1 (le_max_left _ _)
    (by dsimp [theta1_mid, theta2_mid, theta1', theta2']; ring)
    (by dsimp [theta1_mid, theta2_mid]; linarith [Real.pi_pos])
    (by dsimp [theta1_mid, theta2_mid, theta1', theta2']; linarith [Real.pi_pos])
    mid_subset_enlarged a (le_max_right _ _) ha_I
  refine ⟨shiftLogCoeff a a_I, ?_⟩
  rcases hshift with ⟨h0, C, hC, A, hA, hcoeff, hrem⟩
  refine ⟨h0, C, hC, A, hA, hcoeff, fun N u hu => ?_⟩
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le (by linarith [le_max_left (2 * R_conv) (32 * |a| + 2)]) hu.1
  have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
  have ha_le : |a| ≤ ‖u‖ / 32 := by
    have h2 : 32 * |a| + 2 ≤ ‖u‖ := (le_max_right (2 * R_conv) (32 * |a| + 2)).trans hu.1
    linarith
  have hua0 : u + (a : ℂ) ≠ 0 := by
    have htri : ‖u‖ ≤ ‖u + (a : ℂ)‖ + ‖(a : ℂ)‖ := by
      have := norm_add_le (u + (a : ℂ)) (-(a : ℂ))
      rw [add_neg_cancel_right, norm_neg] at this; exact this
    rw [Complex.norm_real, Real.norm_eq_abs] at htri
    exact norm_pos_iff.mp (by linarith)
  have heq : (1 + (a : ℂ) / u) * (I_entire (u + (a : ℂ)) / (u + (a : ℂ))) = I_entire (u + (a : ℂ)) / u := by
    have h1 : 1 + (a : ℂ) / u = (u + (a : ℂ)) / u := by field_simp [hu0]
    rw [h1]; field_simp [hu0, hua0]
  dsimp only
  rw [← heq]
  exact hrem N u hu

/-- All complex derivatives `iteratedDeriv j I_entire z / z` satisfy `HasGev1Exp` on `Σ_mid`. -/
theorem I_entire_iteratedDeriv_div_hasGev1Exp (j : ℕ) :
    ∃ a_j : LogCoeff,
      HasGev1Exp (rotatedClosedSector theta1_mid theta2_mid (2 * R_conv))
        (fun z => iteratedDeriv j I_entire z / z) a_j := by
  obtain ⟨a_I, ha_I⟩ := I_entire_div_hasGev1Exp
  have hR_conv_ge1 : 1 ≤ R_conv := by have h := R_conv_ge_1e6; norm_num at h; linarith
  let S₀ : Set ℂ := rotatedClosedSector theta1' theta2' R_conv
  let S_mid : Set ℂ := rotatedClosedSector theta1_mid theta2_mid (2 * R_conv)
  have hS₀_slit : S₀ ⊆ Complex.slitPlane := rotatedClosedSector_enlarged_subset_slitPlane R_conv_pos
  have hS_norm : ∀ z ∈ S_mid, 1 ≤ ‖z‖ := fun z hz => by linarith [hz.1]
  have hball : ∀ z ∈ S_mid, Metric.closedBall z ((1 / 32 : ℝ) * ‖z‖) ⊆ S₀ :=
    fun z hz => closedBall_mid_subset_enlarged R_conv_pos hz
  have hS_sub_S₀ : S_mid ⊆ S₀ := fun z hz => hball z hz (Metric.mem_closedBall_self (by positivity))
  let U₁ : Set ℂ := {(0 : ℂ)}ᶜ
  have hU₁ : IsOpen U₁ := isOpen_compl_singleton
  have hS₀_U₁ : S₀ ⊆ U₁ := fun z hz => norm_pos_iff.mp (lt_of_lt_of_le R_conv_pos hz.1)
  let Y : ℂ → ℂ := fun z => I_entire z / z
  have hY_diff : DifferentiableOn ℂ Y U₁ :=
    differentiable_I_entire.differentiableOn.div differentiableOn_id fun z hz => hz
  have hY_jet : ∀ k : ℕ, ∃ a : LogCoeff, HasGev1Exp S_mid (iteratedDeriv k Y) a := fun k =>
    ⟨derivCoeff^[k] a_I, hasGev1Exp_iteratedDeriv (by norm_num) (by norm_num)
      hU₁ hS₀_U₁ hS₀_slit hS_norm hball hY_diff ha_I k⟩
  have hI_div_eq : ∀ k : ℕ, ∀ z ∈ U₁,
      iteratedDeriv k I_entire z / z =
        iteratedDeriv k Y z + (k : ℂ) * z⁻¹ * (if k = 0 then 0 else iteratedDeriv (k - 1) Y z) := by
    intro k z hz
    have hev : I_entire =ᶠ[𝓝 z] fun w => w * Y w := by
      filter_upwards [hU₁.mem_nhds hz] with w hw
      dsimp only [Y]; exact (mul_div_cancel₀ (I_entire w) hw).symm
    rw [hev.iteratedDeriv_eq]
    have hY_cd : ContDiffAt ℂ k Y z := ((hY_diff.analyticOnNhd hU₁) z hz).contDiffAt.of_le le_top
    have hid_cd : ContDiffAt ℂ k (fun w : ℂ => w) z := contDiffAt_id
    have hleib := iteratedDeriv_mul hid_cd hY_cd
    have hid_k : ∀ m : ℕ, iteratedDeriv m (fun w : ℂ => w) z =
        if m = 0 then z else if m = 1 then 1 else 0 := by
      intro m
      cases m with
      | zero => simp
      | succ m =>
        cases m with
        | zero => simp [iteratedDeriv_succ]
        | succ p =>
          have hzero : ∀ q : ℕ, iteratedDeriv (q + 2) (fun w : ℂ => w) = 0 := by
            intro q
            induction q with
            | zero => ext w; simp [iteratedDeriv_succ]
            | succ q ihq => rw [iteratedDeriv_succ, ihq]; ext w; simp
          simp [hzero p]
    change iteratedDeriv k ((fun w : ℂ => w) * Y) z / z = _
    rw [hleib]
    cases k with
    | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
        Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero, Nat.cast_zero, zero_mul,
        ↓reduceIte, mul_zero, add_zero]
      exact mul_div_cancel_left₀ (Y z) hz
    | succ m =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have htail : ∑ q ∈ Finset.range m,
          ((m + 1).choose (q + 2) : ℂ) * iteratedDeriv (q + 2) (fun w : ℂ => w) z *
            iteratedDeriv (m + 1 - (q + 2)) Y z = 0 := by
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [hid_k (q + 2)]; simp
      rw [htail, zero_add, hid_k 0, hid_k 1]
      have hch1 : ((m + 1).choose 1 : ℂ) = (m + 1 : ℂ) := by
        rw [Nat.choose_one_right]; push_cast; rfl
      simp only [↓reduceIte, one_ne_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
        Nat.sub_zero, mul_one, Nat.add_sub_cancel, Nat.succ_ne_zero, hch1]
      have hz_ne : z ≠ 0 := hz
      field_simp [hz_ne]
      push_cast; ring
  rcases hY_jet j with ⟨a1, ha1⟩
  cases j with
  | zero =>
    rcases ha1 with ⟨h1, C1, hC1, A1, hA1, hc1, hr1⟩
    refine ⟨a1, h1, C1, hC1, A1, hA1, hc1, fun N z hz => ?_⟩
    simpa [hI_div_eq 0 z (hS₀_U₁ (hS_sub_S₀ hz))] using hr1 N z hz
  | succ m =>
    rcases hY_jet m with ⟨a2, ha2⟩
    have hinv := hasGev1Exp_inv hS_norm
    have hterm2 := hasGev1Exp_smul ((m + 1 : ℕ) : ℂ) (hasGev1Exp_mul hS_norm hinv ha2)
    have hsum := hasGev1Exp_add ha1 hterm2
    rcases hsum with ⟨h1, C1, hC1, A1, hA1, hc1, hr1⟩
    refine ⟨_, h1, C1, hC1, A1, hA1, hc1, fun N z hz => ?_⟩
    have heq := hI_div_eq (m + 1) z (hS₀_U₁ (hS_sub_S₀ hz))
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at heq
    dsimp only
    rw [heq]
    simpa [mul_assoc] using hr1 N z hz

/-- Every shifted jet `u ↦ iteratedDeriv j I_entire (u + a_i) / u` satisfies `HasGev1Exp` on
the common shrunk sector `rotatedClosedSector theta1 theta2 (commonShiftRadius a)`. -/
theorem I_entire_shift_iteratedDeriv_div_hasGev1Exp {d : ℕ} (a : Fin d → ℝ) (i : Fin d) (j : ℕ) :
    ∃ a_ij : LogCoeff,
      HasGev1Exp (rotatedClosedSector theta1 theta2 (commonShiftRadius a))
        (fun u => iteratedDeriv j I_entire (u + (a i : ℂ)) / u) a_ij := by
  obtain ⟨b_j, hb_j⟩ := I_entire_iteratedDeriv_div_hasGev1Exp j
  have h2R_ge1 : 1 ≤ 2 * R_conv := by have h := R_conv_ge_1e6; norm_num at h; linarith
  have ha_le : 32 * |a i| + 2 ≤ commonShiftRadius a := by
    have h1 : |a i| ≤ ∑ k : Fin d, |a k| :=
      Finset.single_le_sum (f := fun k => |a k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : 32 * (∑ k : Fin d, |a k|) + 2 ≤ commonShiftRadius a := le_max_right _ _
    linarith
  have hshift := hasGev1Exp_shift_mul
    (θ₁_in := theta1) (θ₂_in := theta2) (θ₁_out := theta1_mid) (θ₂_out := theta2_mid)
    (R_out := 2 * R_conv) (R_in := commonShiftRadius a)
    h2R_ge1 (by linarith [commonShiftRadius_ge_four_R_conv a])
    (by dsimp [theta1_mid, theta2_mid, theta1, theta2]; ring)
    (by dsimp [theta1, theta2]; linarith [Real.pi_pos])
    (by dsimp [theta1_mid, theta2_mid, theta1, theta2]; linarith [Real.pi_pos])
    (sector_subset_mid.trans mid_subset_enlarged) (a i) ha_le hb_j
  refine ⟨shiftLogCoeff (a i) b_j, ?_⟩
  rcases hshift with ⟨h0, C, hC, A, hA, hcoeff, hrem⟩
  refine ⟨h0, C, hC, A, hA, hcoeff, fun N u hu => ?_⟩
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le (commonShiftRadius_pos a) hu.1
  have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hua0 : u + (a i : ℂ) ≠ 0 := by
    have htri : ‖u‖ ≤ ‖u + (a i : ℂ)‖ + ‖(a i : ℂ)‖ := by
      have := norm_add_le (u + (a i : ℂ)) (-(a i : ℂ))
      rw [add_neg_cancel_right, norm_neg] at this; exact this
    rw [Complex.norm_real, Real.norm_eq_abs] at htri
    have h32 : |a i| ≤ ‖u‖ / 32 := by linarith [hu.1]
    exact norm_pos_iff.mp (by linarith)
  have heq : (1 + (a i : ℂ) / u) * (iteratedDeriv j I_entire (u + (a i : ℂ)) / (u + (a i : ℂ))) =
      iteratedDeriv j I_entire (u + (a i : ℂ)) / u := by
    have h1 : 1 + (a i : ℂ) / u = (u + (a i : ℂ)) / u := by field_simp [hu0]
    rw [h1]; field_simp [hu0, hua0]
  dsimp only
  rw [← heq]
  exact hrem N u hu

/-- Translation commutes with real `iteratedDeriv`. -/
lemma iteratedDeriv_comp_add_const (f : ℝ → ℂ) (c : ℝ) (j : ℕ) :
    ∀ u : ℝ, iteratedDeriv j (fun v : ℝ => f (v + c)) u = iteratedDeriv j f (u + c) := by
  induction j with
  | zero => intro u; simp
  | succ j ih =>
    intro u
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfun : iteratedDeriv j (fun v : ℝ => f (v + c)) = fun v : ℝ => iteratedDeriv j f (v + c) :=
      funext ih
    rw [hfun]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv j f) (u + c)
    · have h1 : HasDerivAt (fun v : ℝ => v + c) 1 u := by simpa using (hasDerivAt_id u).add_const c
      simpa [Function.comp_def] using (hd.hasDerivAt.scomp u h1).deriv
    · have hnd : ¬ DifferentiableAt ℝ (fun v : ℝ => iteratedDeriv j f (v + c)) u := by
        intro h
        have h1 : HasDerivAt (fun v : ℝ => v - c) 1 (u + c) := by
          simpa using (hasDerivAt_id (u + c)).sub_const c
        have h' : DifferentiableAt ℝ (fun v : ℝ => iteratedDeriv j f (v + c)) (u + c - c) := by
          simpa using h
        have hc := h'.comp (u + c) h1.differentiableAt
        have hcomp : ((fun v : ℝ => iteratedDeriv j f (v + c)) ∘ fun v : ℝ => v - c) = iteratedDeriv j f := by
          ext v; simp
        rw [hcomp] at hc
        exact hd hc
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd]

lemma iteratedDeriv_comp_sub_const (f : ℝ → ℂ) (c : ℝ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun v : ℝ => f (v - c)) u = iteratedDeriv j f (u - c) := by
  simpa [sub_eq_add_neg] using iteratedDeriv_comp_add_const f (-c) j u

/-- Shifted upper and lower physical branches `J_i^±(u) = I_±(u - log δ_i)` and their jets. -/
@[expose] def J_plus {d : ℕ} (δ : Fin d → ℝ) (i : Fin d) (u : ℝ) : ℂ :=
  I_plus (u - Real.log (δ i))

@[expose] def J_minus {d : ℕ} (δ : Fin d → ℝ) (i : Fin d) (u : ℝ) : ℂ :=
  I_minus (u - Real.log (δ i))

@[expose] def jetPlus {d : ℕ} (δ : Fin d → ℝ) (r : ℕ) (u : ℝ) : Fin d × Fin (r + 1) → ℂ :=
  fun p => iteratedDeriv p.2.val (J_plus δ p.1) u

@[expose] def jetMinus {d : ℕ} (δ : Fin d → ℝ) (r : ℕ) (u : ℝ) : Fin d × Fin (r + 1) → ℂ :=
  fun p => iteratedDeriv p.2.val (J_minus δ p.1) u

lemma jetPlus_eq {d : ℕ} (δ : Fin d → ℝ) (r : ℕ) (u : ℝ) (p : Fin d × Fin (r + 1)) :
    jetPlus δ r u p = iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1)) :=
  iteratedDeriv_comp_sub_const I_plus (Real.log (δ p.1)) p.2.val u

lemma jetMinus_eq {d : ℕ} (δ : Fin d → ℝ) (r : ℕ) (u : ℝ) (p : Fin d × Fin (r + 1)) :
    jetMinus δ r u p = iteratedDeriv p.2.val I_minus (u - Real.log (δ p.1)) :=
  iteratedDeriv_comp_sub_const I_minus (Real.log (δ p.1)) p.2.val u

/-- The flat-evaluation ideal `I` of jet polynomials `P ∈ ℂ[X_{i,j}]` whose evaluation on
`jetPlus δ r u` is `O_N(u^{-N})` for every `N : ℕ`. -/
@[expose] def InFlatIdeal {d r : ℕ} (δ : Fin d → ℝ)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) : Prop :=
  ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
    ‖MvPolynomial.eval (jetPlus δ r u) P‖ ≤ C / u ^ N

/-- Global polynomial jet growth bound for shifted `J_plus δ`. -/
lemma jetPlus_poly_bound {d : ℕ} (δ : Fin d → ℝ) (r : ℕ) :
    ∃ CH > 0, ∃ A : ℕ, ∃ U₀ : ℝ, 1 ≤ U₀ ∧
      ∀ p : Fin d × Fin (r + 1), ∀ u : ℝ, U₀ ≤ u →
        ‖jetPlus δ r u p‖ ≤ CH * u ^ A := by
  obtain ⟨CH0, hCH0, A, hbound⟩ := I_plus_poly_jet_bound r
  let L : ℝ := ∑ i : Fin d, |Real.log (δ i)|
  have hL_nn : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨CH0 * (2 : ℝ) ^ A, by positivity, A, L + 2, by linarith, fun p u hu => ?_⟩
  have hLi : |Real.log (δ p.1)| ≤ L :=
    Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
  have hui_ge1 : 1 ≤ u - Real.log (δ p.1) := by
    have := (abs_le.mp hLi).2; linarith
  have hui_le2u : u - Real.log (δ p.1) ≤ 2 * u := by
    have := (abs_le.mp hLi).1; linarith
  rw [jetPlus_eq]
  calc ‖iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1))‖
      ≤ CH0 * (u - Real.log (δ p.1)) ^ A := hbound p.2 (u - Real.log (δ p.1)) hui_ge1
    _ ≤ CH0 * (2 * u) ^ A := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hui_le2u A) hCH0.le
    _ = (CH0 * (2 : ℝ) ^ A) * u ^ A := by rw [mul_pow]; ring

/-- General multivariate polynomial jet-difference transfer over any finite index type `ι`. -/
lemma eval_jet_diff_allOrders_general {ι : Type*} [Fintype ι] {f g : ι → ℝ → ℂ}
    (hg_bound : ∃ CH > 0, ∃ A : ℕ, ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ p : ι, ∀ u ≥ U₀, ‖g p u‖ ≤ CH * u ^ A)
    (hdiff : ∀ p : ι, ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U, ‖f p u - g p u‖ ≤ C / u ^ N)
    (P : MvPolynomial ι ℂ) :
    (∃ CP > 0, ∃ AP : ℕ, ∃ UP : ℝ, 1 ≤ UP ∧ ∀ u ≥ UP, ‖MvPolynomial.eval (fun p => g p u) P‖ ≤ CP * u ^ AP) ∧
    (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖MvPolynomial.eval (fun p => f p u) P - MvPolynomial.eval (fun p => g p u) P‖ ≤ C / u ^ N) := by
  obtain ⟨CH, hCH, A, U₀, hU₀, hgB⟩ := hg_bound
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨⟨‖c‖ + 1, by positivity, 0, 1, le_rfl, fun u _ => by simp⟩,
      fun N => ⟨1, zero_lt_one, 1, fun u hu => by
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
        simp only [MvPolynomial.eval_C, sub_self, norm_zero]
        positivity⟩⟩
  | add p q ihp ihq =>
    obtain ⟨⟨Cp, hCp, Ap, Up, hUp, hpb⟩, hpd⟩ := ihp
    obtain ⟨⟨Cq, hCq, Aq, Uq, hUq, hqb⟩, hqd⟩ := ihq
    refine ⟨⟨Cp + Cq, add_pos hCp hCq, max Ap Aq, max Up Uq, le_trans hUp (le_max_left _ _), fun u hu => ?_⟩,
      fun N => ?_⟩
    · have hu1 : 1 ≤ u := (hUp.trans (le_max_left _ _)).trans hu
      rw [map_add]
      have h1 : u ^ Ap ≤ u ^ max Ap Aq := pow_le_pow_right₀ hu1 (le_max_left _ _)
      have h2 : u ^ Aq ≤ u ^ max Ap Aq := pow_le_pow_right₀ hu1 (le_max_right _ _)
      calc ‖MvPolynomial.eval _ p + MvPolynomial.eval _ q‖
          ≤ ‖MvPolynomial.eval _ p‖ + ‖MvPolynomial.eval _ q‖ := norm_add_le _ _
        _ ≤ Cp * u ^ Ap + Cq * u ^ Aq :=
            add_le_add (hpb u ((le_max_left _ _).trans hu)) (hqb u ((le_max_right _ _).trans hu))
        _ ≤ Cp * u ^ max Ap Aq + Cq * u ^ max Ap Aq := by gcongr
        _ = (Cp + Cq) * u ^ max Ap Aq := by ring
    · obtain ⟨C1, hC1, U1, h1⟩ := hpd N
      obtain ⟨C2, hC2, U2, h2⟩ := hqd N
      refine ⟨C1 + C2, add_pos hC1 hC2, max U1 U2, fun u hu => ?_⟩
      have heq : MvPolynomial.eval (fun i => f i u) (p + q) - MvPolynomial.eval (fun i => g i u) (p + q) =
          (MvPolynomial.eval (fun i => f i u) p - MvPolynomial.eval (fun i => g i u) p) +
          (MvPolynomial.eval (fun i => f i u) q - MvPolynomial.eval (fun i => g i u) q) := by
        simp only [map_add]; ring
      rw [heq, add_div]
      exact (norm_add_le _ _).trans
        (add_le_add (h1 u ((le_max_left _ _).trans hu)) (h2 u ((le_max_right _ _).trans hu)))
  | mul_X p k ihp =>
    obtain ⟨⟨Cp, hCp, Ap, Up, hUp, hpb⟩, hpd⟩ := ihp
    refine ⟨⟨Cp * CH, mul_pos hCp hCH, Ap + A, max Up U₀, le_trans hUp (le_max_left _ _), fun u hu => ?_⟩,
      fun N => ?_⟩
    · have hu0 : 0 ≤ u := by linarith [hUp.trans ((le_max_left _ _).trans hu)]
      rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_add]
      calc ‖MvPolynomial.eval _ p‖ * ‖g k u‖
          ≤ (Cp * u ^ Ap) * (CH * u ^ A) :=
            mul_le_mul (hpb u ((le_max_left _ _).trans hu)) (hgB k u ((le_max_right _ _).trans hu))
              (norm_nonneg _) (by positivity)
        _ = (Cp * CH) * (u ^ Ap * u ^ A) := by ring
    · obtain ⟨C1, hC1, U1, h1⟩ := hpd (N + A)
      obtain ⟨C2, hC2, U2, h2⟩ := hdiff k (N + Ap)
      obtain ⟨C3, hC3, U3, h3⟩ := hdiff k N
      refine ⟨C1 * CH + C1 * C3 + Cp * C2, by positivity,
        max (max Up U₀) (max (max U1 U2) U3), fun u hu => ?_⟩
      have huUp : Up ≤ u := ((le_max_left _ _).trans (le_max_left _ _)).trans hu
      have huU0 : U₀ ≤ u := ((le_max_right _ _).trans (le_max_left _ _)).trans hu
      have huU1 : U1 ≤ u := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hu
      have huU2 : U2 ≤ u := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hu
      have huU3 : U3 ≤ u := ((le_max_right _ _).trans (le_max_right _ _)).trans hu
      have hu1 : 1 ≤ u := hUp.trans huUp
      have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
      have hfk_le : ‖f k u‖ ≤ CH * u ^ A + C3 := by
        have htri : ‖f k u‖ ≤ ‖g k u‖ + ‖f k u - g k u‖ := by
          have := norm_add_le (g k u) (f k u - g k u); simpa using this
        have hdiv_le : C3 / u ^ N ≤ C3 := div_le_self hC3.le (one_le_pow₀ hu1)
        linarith [hgB k u huU0, h3 u huU3]
      have heq : MvPolynomial.eval (fun i => f i u) (p * MvPolynomial.X k) -
            MvPolynomial.eval (fun i => g i u) (p * MvPolynomial.X k) =
          (MvPolynomial.eval (fun i => f i u) p - MvPolynomial.eval (fun i => g i u) p) * f k u +
          MvPolynomial.eval (fun i => g i u) p * (f k u - g k u) := by
        simp only [map_mul, MvPolynomial.eval_X]; ring
      rw [heq]
      have ht1 : ‖(MvPolynomial.eval (fun i => f i u) p - MvPolynomial.eval (fun i => g i u) p) * f k u‖ ≤
          (C1 * CH + C1 * C3) / u ^ N := by
        rw [norm_mul]
        have hpowA : u ^ (N + A) = u ^ N * u ^ A := pow_add u N A
        have hle1 : u ^ A ≤ u ^ A := le_rfl
        have h1' : (C1 / u ^ (N + A)) * (CH * u ^ A + C3) ≤ (C1 * CH + C1 * C3) / u ^ N := by
          have hC3_le : C3 ≤ C3 * u ^ A := by
            have : (1 : ℝ) ≤ u ^ A := one_le_pow₀ hu1
            nlinarith
          have hnum : CH * u ^ A + C3 ≤ (CH + C3) * u ^ A := by linarith
          calc (C1 / u ^ (N + A)) * (CH * u ^ A + C3)
              ≤ (C1 / u ^ (N + A)) * ((CH + C3) * u ^ A) :=
                mul_le_mul_of_nonneg_left hnum (by positivity)
            _ = (C1 * CH + C1 * C3) / u ^ N := by
                rw [hpowA]; field_simp [(pow_pos hu_pos N).ne', (pow_pos hu_pos A).ne']
        exact (mul_le_mul (h1 u huU1) hfk_le (norm_nonneg _) (by positivity)).trans h1'
      have ht2 : ‖MvPolynomial.eval (fun i => g i u) p * (f k u - g k u)‖ ≤ (Cp * C2) / u ^ N := by
        rw [norm_mul]
        calc ‖MvPolynomial.eval (fun i => g i u) p‖ * ‖f k u - g k u‖
            ≤ (Cp * u ^ Ap) * (C2 / u ^ (N + Ap)) :=
              mul_le_mul (hpb u huUp) (h2 u huU2) (norm_nonneg _) (by positivity)
          _ = (Cp * C2) / u ^ N := by
              rw [pow_add]; field_simp [(pow_pos hu_pos N).ne', (pow_pos hu_pos Ap).ne']
      calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
        _ ≤ (C1 * CH + C1 * C3) / u ^ N + (Cp * C2) / u ^ N := add_le_add ht1 ht2
        _ = (C1 * CH + C1 * C3 + Cp * C2) / u ^ N := by ring

/-- **Mixed-Tuple Upper Watson Uniqueness**:
Any polynomial `P ∈ ℂ[X_{i,j}]` in `InFlatIdeal δ` evaluates to **EXACTLY ZERO** on
`jetPlus δ r u` for **ALL** `u : ℝ`! -/
theorem mixed_flat_implies_upper_vanishing {d r : ℕ} (δ : Fin d → ℝ)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (hflat : InFlatIdeal δ P) :
    ∀ u : ℝ, MvPolynomial.eval (jetPlus δ r u) P = 0 := by
  let a : Fin d → ℝ := fun i => -Real.log (δ i)
  let R : ℝ := commonShiftRadius a
  have hR_ge1 : 1 ≤ R := commonShiftRadius_ge_one a
  have hR_pos : 0 < R := commonShiftRadius_pos a
  let S : Set ℂ := rotatedClosedSector theta1 theta2 R
  have hS_norm : ∀ z ∈ S, 1 ≤ ‖z‖ := fun z hz => hR_ge1.trans hz.1
  let F : ℂ → ℂ := fun z =>
    MvPolynomial.eval (fun p : Fin d × Fin (r + 1) => iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ))) P
  let deg : ℕ := P.totalDegree
  let G : ℂ → ℂ := fun z => z⁻¹ ^ deg * F z
  -- Step 1: `G` has `HasGev1Exp S` by balancing monomials with `z⁻¹`
  have hG_gev : ∃ aG : LogCoeff, HasGev1Exp S G aG := by
    have hG_sum : ∀ z ∈ S, G z =
        ∑ s ∈ P.support, P.coeff s *
          (z⁻¹ ^ (deg - ∑ p : Fin d × Fin (r + 1), s p) *
            ∏ p : Fin d × Fin (r + 1), (iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) / z) ^ (s p)) := by
      intro z hz
      have hz_ne : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hS_norm z hz))
      dsimp only [G, F]
      rw [MvPolynomial.eval_eq', Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hdeg_le : ∑ p : Fin d × Fin (r + 1), s p ≤ deg := by
        dsimp only [deg]
        have h1 : s.sum (fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hs
        have h2 : s.sum (fun _ e => e) = ∑ p : Fin d × Fin (r + 1), s p := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        omega
      have hprod_div : (∏ p : Fin d × Fin (r + 1),
            (iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) / z) ^ (s p)) =
          (∏ p : Fin d × Fin (r + 1), iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) ^ (s p)) /
            z ^ (∑ p : Fin d × Fin (r + 1), s p) := by
        simp_rw [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hprod_div]
      have hpow_z : z⁻¹ ^ (deg - ∑ p : Fin d × Fin (r + 1), s p) *
            (z ^ (∑ p : Fin d × Fin (r + 1), s p))⁻¹ = z⁻¹ ^ deg := by
        rw [← inv_pow, ← pow_add, Nat.sub_add_cancel hdeg_le]
      rw [div_eq_mul_inv]
      calc z⁻¹ ^ deg * (P.coeff s * ∏ p : Fin d × Fin (r + 1), iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) ^ s p)
          = P.coeff s * (z⁻¹ ^ deg * ∏ p : Fin d × Fin (r + 1), iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) ^ s p) := by ring
        _ = P.coeff s * (z⁻¹ ^ (deg - ∑ p : Fin d × Fin (r + 1), s p) * (z ^ ∑ p : Fin d × Fin (r + 1), s p)⁻¹ *
              ∏ p : Fin d × Fin (r + 1), iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) ^ s p) := by rw [hpow_z]
        _ = P.coeff s * (z⁻¹ ^ (deg - ∑ p : Fin d × Fin (r + 1), s p) *
              ((∏ p : Fin d × Fin (r + 1), iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) ^ s p) *
                (z ^ ∑ p : Fin d × Fin (r + 1), s p)⁻¹)) := by ring
    have hterm_gev : ∀ s : (Fin d × Fin (r + 1)) →₀ ℕ, ∃ c : LogCoeff,
        HasGev1Exp S (fun z => P.coeff s *
          (z⁻¹ ^ (deg - ∑ p : Fin d × Fin (r + 1), s p) *
            ∏ p : Fin d × Fin (r + 1), (iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) / z) ^ (s p))) c := by
      intro s
      obtain ⟨ap1, hap1⟩ := hasGev1Exp_pow hS_norm (hasGev1Exp_inv hS_norm) (deg - ∑ p : Fin d × Fin (r + 1), s p)
      have hprod_gev : ∀ T : Finset (Fin d × Fin (r + 1)), ∃ c : LogCoeff,
          HasGev1Exp S (fun z => ∏ p ∈ T, (iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) / z) ^ (s p)) c := by
        intro T
        classical
        induction T using Finset.induction_on with
        | empty => exact ⟨constCoeff 1, by simpa using hasGev1Exp_const hS_norm 1⟩
        | insert p T hp ih =>
          rcases ih with ⟨aT, haT⟩
          rcases I_entire_shift_iteratedDeriv_div_hasGev1Exp a p.1 p.2.val with ⟨ap, hap⟩
          rcases hasGev1Exp_pow hS_norm hap (s p) with ⟨app, happ⟩
          refine ⟨mulCoeff app aT, ?_⟩
          simpa [Finset.prod_insert hp] using hasGev1Exp_mul hS_norm happ haT
      obtain ⟨ap2, hap2⟩ := hprod_gev Finset.univ
      exact ⟨smulCoeff (P.coeff s) (mulCoeff ap1 ap2),
        hasGev1Exp_smul (P.coeff s) (hasGev1Exp_mul hS_norm hap1 hap2)⟩
    have hfinset_sum : ∀ T : Finset ((Fin d × Fin (r + 1)) →₀ ℕ), ∃ c : LogCoeff,
        HasGev1Exp S (fun z => ∑ s ∈ T, P.coeff s *
          (z⁻¹ ^ (deg - ∑ p : Fin d × Fin (r + 1), s p) *
            ∏ p : Fin d × Fin (r + 1), (iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ)) / z) ^ (s p))) c := by
      intro T
      classical
      induction T using Finset.induction_on with
      | empty => exact ⟨constCoeff 0, by simpa using hasGev1Exp_const hS_norm 0⟩
      | insert s T hs ih =>
        rcases ih with ⟨aT, haT⟩
        rcases hterm_gev s with ⟨as, has⟩
        refine ⟨addCoeff as aT, ?_⟩
        simpa [Finset.sum_insert hs] using hasGev1Exp_add has haT
    obtain ⟨aG, haG⟩ := hfinset_sum P.support
    rcases haG with ⟨h1, C1, hC1, A1, hA1, hc1, hr1⟩
    exact ⟨aG, h1, C1, hC1, A1, hA1, hc1, fun N z hz => by rw [hG_sum z hz]; exact hr1 N z hz⟩
  -- Step 2: `F` agrees with `eval (jetPlus δ r u) P` on ALL `u : ℝ`!
  have hF_agree : ∀ u : ℝ, F (u : ℂ) = MvPolynomial.eval (jetPlus δ r u) P := by
    intro u
    dsimp only [F]
    refine congrArg (fun x => MvPolynomial.eval x P) (funext fun p => ?_)
    rw [jetPlus_eq]
    have hreal : (u : ℂ) + (a p.1 : ℂ) = ((u - Real.log (δ p.1) : ℝ) : ℂ) := by
      dsimp only [a]; push_cast; ring
    rw [hreal, ← PakNthPrimeUnconditional.iteratedDeriv_comp_ofReal_eq isOpen_univ
      differentiable_I_entire.differentiableOn p.2.val (u - Real.log (δ p.1)) trivial]
    have hfun : (fun x : ℝ => I_entire (x : ℂ)) = I_plus := funext I_entire_ofReal
    rw [hfun]
  -- Step 3: `G` is flat on `[R, ∞)`, so all its Gevrey-1 coefficients vanish → Watson uniqueness!
  have hG_flat : ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U, ‖G (u : ℂ)‖ ≤ C / u ^ N := by
    intro N
    obtain ⟨C, hC, U, hU⟩ := hflat N
    refine ⟨C, hC, max R U, fun u hu => ?_⟩
    have hu1 : 1 ≤ u := hR_ge1.trans ((le_max_left R U).trans hu)
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    dsimp only [G]
    rw [hF_agree u, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    have hinv_le : (u⁻¹) ^ deg ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu1)
    calc (u⁻¹) ^ deg * ‖MvPolynomial.eval (jetPlus δ r u) P‖
        ≤ 1 * (C / u ^ N) := mul_le_mul hinv_le (hU u ((le_max_right R U).trans hu)) (norm_nonneg _) zero_le_one
      _ = C / u ^ N := one_mul _
  obtain ⟨aG, haG⟩ := hG_gev
  have hray_S : ∀ u : ℝ, R ≤ u → (u : ℂ) ∈ S := fun u hu =>
    ofReal_mem_rotatedClosedSector (by dsimp [theta1]; linarith [Real.pi_pos])
      (by dsimp [theta2]; linarith [Real.pi_pos])
      (by dsimp [theta1, theta2]; linarith [Real.pi_pos]) hR_pos hu
  have haG0 : ∀ n k, aG n k = 0 := coeff_eq_zero_of_ray_flat hR_ge1 hray_S haG hG_flat
  obtain ⟨CG, hCG, AG, hAG, hG_bound⟩ := gevrey1_bound_of_hasGev1Exp_zero haG haG0
  -- Step 4: `F` is entire, `G` is holomorphic on `{(0 : ℂ)}ᶜ`, apply `watson_uniqueness_rotated_gevrey1`!
  have hF_diff : Differentiable ℂ F := by
    have hjet_diff : ∀ j : ℕ, Differentiable ℂ (iteratedDeriv j I_entire) := by
      intro j
      have han : AnalyticOnNhd ℂ (iteratedDeriv j I_entire) Set.univ := by
        induction j with
        | zero => simpa using differentiable_I_entire.differentiableOn.analyticOnNhd isOpen_univ
        | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
      exact fun z => (han z trivial).differentiableAt
    have hdiff_all : ∀ Q : MvPolynomial (Fin d × Fin (r + 1)) ℂ,
        Differentiable ℂ (fun z => MvPolynomial.eval
          (fun p : Fin d × Fin (r + 1) => iteratedDeriv p.2.val I_entire (z + (a p.1 : ℂ))) Q) := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => simp only [MvPolynomial.eval_C]; exact differentiable_const c
      | add p q hp hq =>
        intro z
        have heq : (fun w => MvPolynomial.eval (fun i => iteratedDeriv i.2.val I_entire (w + (a i.1 : ℂ))) (p + q)) =
            fun w => MvPolynomial.eval (fun i => iteratedDeriv i.2.val I_entire (w + (a i.1 : ℂ))) p +
              MvPolynomial.eval (fun i => iteratedDeriv i.2.val I_entire (w + (a i.1 : ℂ))) q := by
          ext w; simp [map_add]
        rw [heq]; exact (hp z).add (hq z)
      | mul_X p k hp =>
        intro z
        have heq : (fun w => MvPolynomial.eval (fun i => iteratedDeriv i.2.val I_entire (w + (a i.1 : ℂ))) (p * MvPolynomial.X k)) =
            fun w => MvPolynomial.eval (fun i => iteratedDeriv i.2.val I_entire (w + (a i.1 : ℂ))) p *
              iteratedDeriv k.2.val I_entire (w + (a k.1 : ℂ)) := by
          ext w; simp [map_mul]
        rw [heq]
        have hk : DifferentiableAt ℂ (fun w => iteratedDeriv k.2.val I_entire (w + (a k.1 : ℂ))) z :=
          (hjet_diff k.2.val (z + (a k.1 : ℂ))).comp z (differentiableAt_id.add (differentiableAt_const _))
        exact (hp z).mul hk
    exact hdiff_all P
  have hG_diff : DifferentiableOn ℂ G {(0 : ℂ)}ᶜ := by
    intro z hz
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
    have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹ ^ deg) z :=
      (differentiableAt_id.inv hz0).pow deg
    exact (hinv.mul (hF_diff z)).differentiableWithinAt
  have hS_sub : S ⊆ {(0 : ℂ)}ᶜ := fun z hz => norm_pos_iff.mp (lt_of_lt_of_le hR_pos hz.1)
  have hG_zero : ∀ z ∈ S, G z = 0 :=
    watson_uniqueness_rotated_gevrey1 (by dsimp [theta1, theta2]; linarith [Real.pi_pos])
      (by dsimp [theta1, theta2]; linarith [Real.pi_pos])
      hR_pos hCG hAG isOpen_compl_singleton hS_sub hG_diff hG_bound
  -- Step 5: `F` vanishes on `[R, ∞)`, hence on all of `ℂ` by identity theorem!
  have hF_ray : ∀ u : ℝ, R ≤ u → F (u : ℂ) = 0 := by
    intro u hu
    have hgz := hG_zero (u : ℂ) (hray_S u hu)
    dsimp only [G] at hgz
    have hu_ne : ((u : ℂ)⁻¹) ^ deg ≠ 0 :=
      pow_ne_zero deg (inv_ne_zero (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hR_pos hu).ne'))
    exact (mul_eq_zero.mp hgz).resolve_left hu_ne
  have hF_all : ∀ z : ℂ, F z = 0 := by
    have han : AnalyticOnNhd ℂ F Set.univ := hF_diff.differentiableOn.analyticOnNhd isOpen_univ
    have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] ((R + 1 : ℝ) : ℂ), F z = 0 := by
      rw [Filter.frequently_iff]
      intro s hs
      rw [Metric.mem_nhdsWithin_iff] at hs
      obtain ⟨ε, hε, hball⟩ := hs
      let x : ℝ := R + 1 + min (ε / 2) 1
      have hmin_pos : 0 < min (ε / 2) 1 := lt_min (half_pos hε) zero_lt_one
      have hmin_le : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
      refine ⟨(x : ℂ), hball ⟨?_, ?_⟩, hF_ray x (by dsimp [x]; linarith)⟩
      · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have : x - (R + 1) = min (ε / 2) 1 := by dsimp [x]; ring
        rw [this, abs_of_pos hmin_pos]; linarith
      · intro heq
        have hre := congr_arg Complex.re heq
        simp only [Complex.ofReal_re] at hre
        dsimp [x] at hre; linarith
    have h0 := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ trivial hfreq
    intro z; exact h0 trivial
  intro u
  rw [← hF_agree u]
  exact hF_all (u : ℂ)

/-- **Mixed-Tuple Two-Sided Watson Uniqueness (`mixed_flat_implies_exact_vanishing`)**:
Any polynomial `P : MvPolynomial (Fin d × Fin (r + 1)) ℂ` in `InFlatIdeal δ` evaluates to
**EXACTLY ZERO** on BOTH `jetPlus δ r u` AND `jetMinus δ r u` for **ALL** `u : ℝ`! -/
theorem mixed_flat_implies_exact_vanishing {d r : ℕ} (δ : Fin d → ℝ)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (hflat : InFlatIdeal δ P) :
    ∀ u : ℝ, MvPolynomial.eval (jetPlus δ r u) P = 0 ∧ MvPolynomial.eval (jetMinus δ r u) P = 0 := by
  have hall_plus : ∀ u : ℝ, MvPolynomial.eval (jetPlus δ r u) P = 0 :=
    mixed_flat_implies_upper_vanishing δ P hflat
  -- Conjugate polynomial `Pbar = P.map (starRingEnd ℂ)`
  let Pbar : MvPolynomial (Fin d × Fin (r + 1)) ℂ := MvPolynomial.map (starRingEnd ℂ) P
  let L : ℝ := ∑ i : Fin d, |Real.log (δ i)|
  have hPbar_eq : ∀ u : ℝ, L + 1 ≤ u →
      MvPolynomial.eval (jetPlus δ r u) Pbar = star (MvPolynomial.eval (jetMinus δ r u) P) := by
    intro u hu
    have hjet : jetPlus δ r u = fun p => (starRingEnd ℂ) (jetMinus δ r u p) := by
      ext p
      have hLi : |Real.log (δ p.1)| ≤ L :=
        Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
      have hui_pos : 0 < u - Real.log (δ p.1) := by have := (abs_le.mp hLi).2; linarith
      have hloc : I_minus =ᶠ[𝓝 (u - Real.log (δ p.1))] (fun v : ℝ => star (I_plus v)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hui_pos] with v hv
        exact I_minus_eq_star_I_plus hv
      rw [jetPlus_eq, jetMinus_eq, hloc.iteratedDeriv_eq, iteratedDeriv_star_comp]
      simp
    dsimp only [Pbar]
    rw [hjet, MvPolynomial.eval_map]
    change MvPolynomial.eval₂ ((starRingEnd ℂ).comp (RingHom.id ℂ))
        ((starRingEnd ℂ) ∘ jetMinus δ r u) P =
      (starRingEnd ℂ) (MvPolynomial.eval₂ (RingHom.id ℂ) (jetMinus δ r u) P)
    rw [MvPolynomial.hom_eval₂]
    rfl
  -- Shifted `jetMinus - jetPlus` is flat to all orders
  have hdiff_pm : ∀ p : Fin d × Fin (r + 1), ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖jetMinus δ r u p - jetPlus δ r u p‖ ≤ C / u ^ N := by
    intro p N
    obtain ⟨C, hC, U, hU⟩ := I_minus_sub_I_plus_jet_allOrders p.2.val N
    have hLi : |Real.log (δ p.1)| ≤ L :=
      Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
    refine ⟨C * (2 : ℝ) ^ N, by positivity, max (2 * L + 2) (U + L + 1), fun u hu => ?_⟩
    have hu1 : 2 * L + 2 ≤ u := (le_max_left _ _).trans hu
    have hu2 : U + L + 1 ≤ u := (le_max_right _ _).trans hu
    have hui_geU : U ≤ u - Real.log (δ p.1) := by have := (abs_le.mp hLi).2; linarith
    have hui_half : u / 2 ≤ u - Real.log (δ p.1) := by have := (abs_le.mp hLi).2; linarith
    have hu_pos : 0 < u := by linarith [Finset.sum_nonneg (s := Finset.univ) (f := fun i : Fin d => |Real.log (δ i)|) fun _ _ => abs_nonneg _]
    rw [jetMinus_eq, jetPlus_eq]
    calc ‖iteratedDeriv p.2.val I_minus (u - Real.log (δ p.1)) -
            iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1))‖
        ≤ C / (u - Real.log (δ p.1)) ^ N := hU (u - Real.log (δ p.1)) hui_geU
      _ ≤ C / (u / 2) ^ N :=
          div_le_div_of_nonneg_left hC.le (pow_pos (by positivity) N)
            (pow_le_pow_left₀ (by positivity) hui_half N)
      _ = (C * (2 : ℝ) ^ N) / u ^ N := by rw [div_pow]; field_simp [(pow_pos hu_pos N).ne']
  have hP_minus_flat : ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖MvPolynomial.eval (jetMinus δ r u) P‖ ≤ C / u ^ N := by
    have htr := (eval_jet_diff_allOrders_general (f := fun p u => jetMinus δ r u p)
      (g := fun p u => jetPlus δ r u p) (jetPlus_poly_bound δ r) hdiff_pm P).2
    intro N
    obtain ⟨C, hC, U, hU⟩ := htr N
    refine ⟨C, hC, U, fun u hu => ?_⟩
    have h1 := hU u hu
    rw [hall_plus u, sub_zero] at h1
    exact h1
  have hPbar_flat : InFlatIdeal δ Pbar := by
    intro N
    obtain ⟨C, hC, U, hU⟩ := hP_minus_flat N
    refine ⟨C, hC, max (L + 1) U, fun u hu => ?_⟩
    rw [hPbar_eq u ((le_max_left _ _).trans hu)]
    simpa [Complex.star_def] using hU u ((le_max_right _ _).trans hu)
  have hall_Pbar : ∀ u : ℝ, MvPolynomial.eval (jetPlus δ r u) Pbar = 0 :=
    mixed_flat_implies_upper_vanishing δ Pbar hPbar_flat
  have hray_minus : ∀ u : ℝ, L + 1 ≤ u → MvPolynomial.eval (jetMinus δ r u) P = 0 := by
    intro u hu
    have h0 := hall_Pbar u
    rw [hPbar_eq u hu] at h0
    exact star_eq_zero.mp h0
  -- Global real-analyticity of `u ↦ eval (jetMinus δ r u) P` extends `[L + 1, ∞)` to all `ℝ`!
  have hall_minus : ∀ u : ℝ, MvPolynomial.eval (jetMinus δ r u) P = 0 := by
    have hjet_an : ∀ p : Fin d × Fin (r + 1), AnalyticOnNhd ℝ (fun u => jetMinus δ r u p) Set.univ := by
      intro p
      have hk : ∀ k : ℕ, AnalyticOnNhd ℝ (iteratedDeriv k I_minus) Set.univ := by
        intro k
        induction k with
        | zero => simpa using analyticOnNhd_I_minus
        | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
      have heq : (fun u : ℝ => jetMinus δ r u p) = fun u : ℝ => iteratedDeriv p.2.val I_minus (u - Real.log (δ p.1)) :=
        funext fun u => jetMinus_eq δ r u p
      rw [heq]
      intro u _
      have hlin : AnalyticAt ℝ (fun v : ℝ => v - Real.log (δ p.1)) u :=
        analyticAt_id.sub analyticAt_const
      exact (hk p.2.val (u - Real.log (δ p.1)) trivial).comp_of_eq hlin rfl
    have hP_an : AnalyticOnNhd ℝ (fun u => MvPolynomial.eval (jetMinus δ r u) P) Set.univ := by
      have hall : ∀ Q : MvPolynomial (Fin d × Fin (r + 1)) ℂ,
          AnalyticOnNhd ℝ (fun u => MvPolynomial.eval (jetMinus δ r u) Q) Set.univ := by
        intro Q
        induction Q using MvPolynomial.induction_on with
        | C c => intro u _; simp only [MvPolynomial.eval_C]; exact analyticAt_const
        | add p q hp hq =>
          intro u _
          have heq : (fun v => MvPolynomial.eval (jetMinus δ r v) (p + q)) =
              fun v => MvPolynomial.eval (jetMinus δ r v) p + MvPolynomial.eval (jetMinus δ r v) q := by
            ext v; simp [map_add]
          rw [heq]; exact (hp u trivial).add (hq u trivial)
        | mul_X p k hp =>
          intro u _
          have heq : (fun v => MvPolynomial.eval (jetMinus δ r v) (p * MvPolynomial.X k)) =
              fun v => MvPolynomial.eval (jetMinus δ r v) p * jetMinus δ r v k := by
            ext v; simp [map_mul]
          rw [heq]; exact (hp u trivial).mul (hjet_an k u trivial)
      exact hall P
    have hfreq : ∃ᶠ u : ℝ in 𝓝[≠] (L + 2), MvPolynomial.eval (jetMinus δ r u) P = 0 := by
      rw [Filter.frequently_iff]
      intro s hs
      rw [Metric.mem_nhdsWithin_iff] at hs
      obtain ⟨ε, hε, hball⟩ := hs
      let x : ℝ := L + 2 + min (ε / 2) 1
      have hmin_pos : 0 < min (ε / 2) 1 := lt_min (half_pos hε) zero_lt_one
      have hmin_le : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
      refine ⟨x, hball ⟨?_, fun heq => by have h := Set.mem_singleton_iff.mp heq; dsimp [x] at h; linarith⟩,
        hray_minus x (by dsimp [x]; linarith)⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have : x - (L + 2) = min (ε / 2) 1 := by dsimp [x]; ring
      rw [this, abs_of_pos hmin_pos]; linarith
    have h0 := hP_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ trivial hfreq
    intro u; exact h0 trivial
  exact fun u => ⟨hall_plus u, hall_minus u⟩

/-! ### Section 2. Simultaneous Affine Flow `B_op` & Additive-Wave Descent `Lm_op` -/

/-- Generic chain rule for `MvPolynomial.eval` over any finite index type `ι`. -/
lemma hasDerivAt_mvPolynomial_eval_general {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ)
    (x x' : ℂ → ι → ℂ) (τ : ℂ)
    (hx : ∀ p : ι, HasDerivAt (fun t => x t p) (x' τ p) τ) :
    HasDerivAt (fun t => MvPolynomial.eval (x t) P)
      (∑ p : ι, MvPolynomial.eval (x τ) (MvPolynomial.pderiv p P) * x' τ p) τ := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const τ c
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext t; simp
    · simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hmul := hp.mul (hx k)
    convert hmul using 1
    · ext t; simp
    · simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul,
        MvPolynomial.eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
      have hsingle : (∑ j : ι, (if k = j then (1 : ℂ) else 0) *
          MvPolynomial.eval (x τ) p * x' τ j) = MvPolynomial.eval (x τ) p * x' τ k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hjk; simp [Ne.symm hjk]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      rw [add_comm, ← hsingle]
      congr 1
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun j _ => by by_cases hkj : k = j <;> simp [hkj]

/-- Generic growth, Lipschitz, and first-order Taylor bounds for `MvPolynomial.eval` over any `[Fintype ι]`. -/
lemma mvPolynomial_bounds_general {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) :
    ∃ (C0 C1 C2 : ℝ) (D : ℕ), 0 < C0 ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (x Δ : ι → ℂ) (Mx MΔ : ℝ),
        1 ≤ Mx → 0 ≤ MΔ → MΔ ≤ 1 →
        (∀ p, ‖x p‖ ≤ Mx) → (∀ p, ‖Δ p‖ ≤ MΔ) →
        ‖MvPolynomial.eval x P‖ ≤ C0 * Mx ^ D ∧
        ‖MvPolynomial.eval (x + Δ) P - MvPolynomial.eval x P‖ ≤ C1 * Mx ^ D * MΔ ∧
        ‖MvPolynomial.eval (x + Δ) P - MvPolynomial.eval x P -
          ∑ p : ι, MvPolynomial.eval x (MvPolynomial.pderiv p P) * Δ p‖ ≤
          C2 * Mx ^ D * MΔ ^ 2 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨‖c‖ + 1, 1, 1, 0, by positivity, by positivity, by positivity, ?_⟩
    intro x Δ Mx MΔ _ hMΔ _ _ _
    simp only [MvPolynomial.eval_C, pow_zero, mul_one, sub_self, norm_zero, pderiv_C,
      map_zero, zero_mul, Finset.sum_const_zero]
    exact ⟨by linarith, by positivity, by positivity⟩
  | add p q hp hq =>
    obtain ⟨Cp0, Cp1, Cp2, Dp, hCp0, hCp1, hCp2, hpb⟩ := hp
    obtain ⟨Cq0, Cq1, Cq2, Dq, hCq0, hCq1, hCq2, hqb⟩ := hq
    refine ⟨Cp0 + Cq0, Cp1 + Cq1, Cp2 + Cq2, max Dp Dq,
      by positivity, by positivity, by positivity, ?_⟩
    intro x Δ Mx MΔ hMx hMΔ hMΔ1 hx hΔ
    obtain ⟨hp0, hp1, hp2⟩ := hpb x Δ Mx MΔ hMx hMΔ hMΔ1 hx hΔ
    obtain ⟨hq0, hq1, hq2⟩ := hqb x Δ Mx MΔ hMx hMΔ hMΔ1 hx hΔ
    have hpow_p : Mx ^ Dp ≤ Mx ^ max Dp Dq := pow_le_pow_right₀ hMx (le_max_left _ _)
    have hpow_q : Mx ^ Dq ≤ Mx ^ max Dp Dq := pow_le_pow_right₀ hMx (le_max_right _ _)
    refine ⟨?_, ?_, ?_⟩
    · calc ‖MvPolynomial.eval x (p + q)‖
          = ‖MvPolynomial.eval x p + MvPolynomial.eval x q‖ := by simp
        _ ≤ ‖MvPolynomial.eval x p‖ + ‖MvPolynomial.eval x q‖ := norm_add_le _ _
        _ ≤ Cp0 * Mx ^ Dp + Cq0 * Mx ^ Dq := add_le_add hp0 hq0
        _ ≤ Cp0 * Mx ^ max Dp Dq + Cq0 * Mx ^ max Dp Dq := by nlinarith
        _ = (Cp0 + Cq0) * Mx ^ max Dp Dq := by ring
    · have heq : MvPolynomial.eval (x + Δ) (p + q) - MvPolynomial.eval x (p + q) =
          (MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p) +
          (MvPolynomial.eval (x + Δ) q - MvPolynomial.eval x q) := by simp; ring
      rw [heq]
      calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
        _ ≤ Cp1 * Mx ^ Dp * MΔ + Cq1 * Mx ^ Dq * MΔ := add_le_add hp1 hq1
        _ ≤ Cp1 * Mx ^ max Dp Dq * MΔ + Cq1 * Mx ^ max Dp Dq * MΔ := by
            have h1 : Cp1 * Mx ^ Dp ≤ Cp1 * Mx ^ max Dp Dq := by nlinarith
            have h2 : Cq1 * Mx ^ Dq ≤ Cq1 * Mx ^ max Dp Dq := by nlinarith
            nlinarith
        _ = (Cp1 + Cq1) * Mx ^ max Dp Dq * MΔ := by ring
    · have heq :
          MvPolynomial.eval (x + Δ) (p + q) - MvPolynomial.eval x (p + q) -
            ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j (p + q)) * Δ j =
          (MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p -
            ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j p) * Δ j) +
          (MvPolynomial.eval (x + Δ) q - MvPolynomial.eval x q -
            ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j q) * Δ j) := by
        simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
      rw [heq]
      have hMΔ2 : 0 ≤ MΔ ^ 2 := sq_nonneg MΔ
      calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
        _ ≤ Cp2 * Mx ^ Dp * MΔ ^ 2 + Cq2 * Mx ^ Dq * MΔ ^ 2 := add_le_add hp2 hq2
        _ ≤ Cp2 * Mx ^ max Dp Dq * MΔ ^ 2 + Cq2 * Mx ^ max Dp Dq * MΔ ^ 2 := by
            have h1 : Cp2 * Mx ^ Dp ≤ Cp2 * Mx ^ max Dp Dq := by nlinarith
            have h2 : Cq2 * Mx ^ Dq ≤ Cq2 * Mx ^ max Dp Dq := by nlinarith
            nlinarith
        _ = (Cp2 + Cq2) * Mx ^ max Dp Dq * MΔ ^ 2 := by ring
  | mul_X p k hp =>
    obtain ⟨Cp0, Cp1, Cp2, Dp, hCp0, hCp1, hCp2, hpb⟩ := hp
    refine ⟨Cp0, 2 * Cp1 + Cp0, 2 * Cp2 + Cp1, Dp + 1,
      by positivity, by positivity, by positivity, ?_⟩
    intro x Δ Mx MΔ hMx hMΔ hMΔ1 hx hΔ
    obtain ⟨hp0, hp1, hp2⟩ := hpb x Δ Mx MΔ hMx hMΔ hMΔ1 hx hΔ
    have hxk : ‖x k‖ ≤ Mx := hx k
    have hΔk : ‖Δ k‖ ≤ MΔ := hΔ k
    have hxd : ‖x k + Δ k‖ ≤ 2 * Mx := by
      calc ‖x k + Δ k‖ ≤ ‖x k‖ + ‖Δ k‖ := norm_add_le _ _
        _ ≤ Mx + MΔ := add_le_add hxk hΔk
        _ ≤ 2 * Mx := by linarith
    have hMx_pos : 0 < Mx := lt_of_lt_of_le zero_lt_one hMx
    have hpow_le : Mx ^ Dp ≤ Mx ^ (Dp + 1) := pow_le_pow_right₀ hMx (Nat.le_succ Dp)
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ]
      calc ‖MvPolynomial.eval x p‖ * ‖x k‖
          ≤ (Cp0 * Mx ^ Dp) * Mx := mul_le_mul hp0 hxk (norm_nonneg _) (by positivity)
        _ = Cp0 * (Mx ^ Dp * Mx) := by ring
    · have heq : MvPolynomial.eval (x + Δ) (p * MvPolynomial.X k) -
            MvPolynomial.eval x (p * MvPolynomial.X k) =
          (MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p) * (x k + Δ k) +
            MvPolynomial.eval x p * Δ k := by
        simp only [map_mul, MvPolynomial.eval_X, Pi.add_apply]; ring
      rw [heq]
      calc ‖_ + _‖
          ≤ ‖MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p‖ * ‖x k + Δ k‖ +
            ‖MvPolynomial.eval x p‖ * ‖Δ k‖ := by
              simpa only [norm_mul] using norm_add_le
                ((MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p) * (x k + Δ k))
                (MvPolynomial.eval x p * Δ k)
        _ ≤ (Cp1 * Mx ^ Dp * MΔ) * (2 * Mx) + (Cp0 * Mx ^ Dp) * MΔ :=
              add_le_add (mul_le_mul hp1 hxd (norm_nonneg _) (by positivity))
                (mul_le_mul hp0 hΔk (norm_nonneg _) (by positivity))
        _ = 2 * Cp1 * Mx ^ (Dp + 1) * MΔ + Cp0 * Mx ^ Dp * MΔ := by rw [pow_succ]; ring
        _ ≤ 2 * Cp1 * Mx ^ (Dp + 1) * MΔ + Cp0 * Mx ^ (Dp + 1) * MΔ := by
              have : Cp0 * Mx ^ Dp ≤ Cp0 * Mx ^ (Dp + 1) := by nlinarith
              nlinarith
        _ = (2 * Cp1 + Cp0) * Mx ^ (Dp + 1) * MΔ := by ring
    · have hsum_pderiv :
          ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X k)) * Δ j =
          (∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j p) * Δ j) * x k +
            MvPolynomial.eval x p * Δ k := by
        simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul,
          MvPolynomial.eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
        have h1 : (∑ j : ι, MvPolynomial.eval x p * (if k = j then (1 : ℂ) else 0) * Δ j) =
            MvPolynomial.eval x p * Δ k := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro j _ hjk; simp [Ne.symm hjk]
          · intro hk; exact absurd (Finset.mem_univ k) hk
        rw [add_comm, ← h1]
        congr 1
        · rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
        · refine Finset.sum_congr rfl fun j _ => by by_cases hkj : k = j <;> simp [hkj]
      have heq' :
          MvPolynomial.eval (x + Δ) (p * MvPolynomial.X k) -
            MvPolynomial.eval x (p * MvPolynomial.X k) -
            ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X k)) * Δ j =
          (MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p -
            ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j p) * Δ j) * x k +
          (MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p) * Δ k := by
        rw [hsum_pderiv]; simp only [map_mul, MvPolynomial.eval_X, Pi.add_apply]; ring
      rw [heq']
      have hMΔ2 : 0 ≤ MΔ ^ 2 := sq_nonneg MΔ
      calc ‖_ + _‖
          ≤ ‖MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p -
              ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j p) * Δ j‖ * ‖x k‖ +
            ‖MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p‖ * ‖Δ k‖ := by
              simpa only [norm_mul] using norm_add_le
                ((MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p -
                  ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j p) * Δ j) * x k)
                ((MvPolynomial.eval (x + Δ) p - MvPolynomial.eval x p) * Δ k)
        _ ≤ (Cp2 * Mx ^ Dp * MΔ ^ 2) * Mx + (Cp1 * Mx ^ Dp * MΔ) * MΔ :=
              add_le_add (mul_le_mul hp2 hxk (norm_nonneg _) (by positivity))
                (mul_le_mul hp1 hΔk (norm_nonneg _) (by positivity))
        _ = Cp2 * Mx ^ (Dp + 1) * MΔ ^ 2 + Cp1 * Mx ^ Dp * MΔ ^ 2 := by rw [pow_succ]; ring
        _ ≤ 2 * Cp2 * Mx ^ (Dp + 1) * MΔ ^ 2 + Cp1 * Mx ^ (Dp + 1) * MΔ ^ 2 := by
              have h1 : Cp2 * Mx ^ (Dp + 1) ≤ 2 * Cp2 * Mx ^ (Dp + 1) := by nlinarith [pow_pos hMx_pos (Dp + 1)]
              have h2 : Cp1 * Mx ^ Dp ≤ Cp1 * Mx ^ (Dp + 1) := by nlinarith
              nlinarith
        _ = (2 * Cp2 + Cp1) * Mx ^ (Dp + 1) * MΔ ^ 2 := by ring

/-- The simultaneous affine-flow linear derivation `B_op δ` on `MvPolynomial (Fin d × Fin (r + 1)) ℂ`:
`B_op δ P = ∑ i, ∑ j, δ_i (∑_{k ≤ j} C(j, k) (-1)^{j - k} X_{i, k}) ∂_{i, j} P`. -/
@[expose] def B_op {d r : ℕ} (δ : Fin d → ℝ) :
    MvPolynomial (Fin d × Fin (r + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin d × Fin (r + 1)) ℂ where
  toFun P :=
    ∑ i : Fin d, ∑ j : Fin (r + 1),
      ((δ i : ℂ) • ∑ k : Fin (r + 1),
        if k.val ≤ j.val then
          ((j.val.choose k.val : ℂ) * (-1 : ℂ) ^ (j.val - k.val)) • MvPolynomial.X (i, k)
        else 0) * MvPolynomial.pderiv (i, j) P
  map_add' P Q := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv (i, j)).map_smul, mul_smul_comm]

theorem B_op_apply {d r : ℕ} (δ : Fin d → ℝ) (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) :
    B_op δ P =
      ∑ i : Fin d, ∑ j : Fin (r + 1),
        ((δ i : ℂ) • ∑ k : Fin (r + 1),
          if k.val ≤ j.val then
            ((j.val.choose k.val : ℂ) * (-1 : ℂ) ^ (j.val - k.val)) • MvPolynomial.X (i, k)
          else 0) * MvPolynomial.pderiv (i, j) P := rfl

/-- Constant-coefficient additive-wave vector field `Lm_op δ m`:
`Lm_op δ m P = ∑ i, ∑ j, δ_i^m (-m)^j ∂_{i, j} P`. -/
@[expose] def Lm_op {d r : ℕ} (δ : Fin d → ℝ) (m : ℕ) :
    MvPolynomial (Fin d × Fin (r + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin d × Fin (r + 1)) ℂ where
  toFun P :=
    ∑ i : Fin d, ∑ j : Fin (r + 1),
      ((δ i : ℂ) ^ m * (-(m : ℂ)) ^ j.val) • MvPolynomial.pderiv (i, j) P
  map_add' P Q := by
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv (i, j)).map_smul, smul_comm]

theorem Lm_op_apply {d r : ℕ} (δ : Fin d → ℝ) (m : ℕ) (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) :
    Lm_op δ m P =
      ∑ i : Fin d, ∑ j : Fin (r + 1),
        ((δ i : ℂ) ^ m * (-(m : ℂ)) ^ j.val) • MvPolynomial.pderiv (i, j) P := rfl

/-- Helper: `Complex.exp (-(u - Real.log δ)) = δ * Complex.exp (-u)` for `δ > 0`. -/
lemma cexp_neg_sub_log {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    Complex.exp (-((u - Real.log δ : ℝ) : ℂ)) = (δ : ℂ) * Complex.exp (-(u : ℂ)) := by
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul]
  congr 1
  rw [show -(u - Real.log δ) = Real.log δ + (-u) by ring, Real.exp_add, Real.exp_log hδ]

/-- Helper: `Complex.exp (-(m * (u - Real.log δ))) = δ^m * Complex.exp (-(m * u))` for `δ > 0`. -/
lemma cexp_neg_nat_mul_sub_log {δ : ℝ} (hδ : 0 < δ) (m : ℕ) (u : ℝ) :
    Complex.exp (-((m : ℂ) * ((u - Real.log δ : ℝ) : ℂ))) =
      (δ : ℂ) ^ m * Complex.exp (-((m : ℂ) * (u : ℂ))) := by
  have h1 : -((m : ℂ) * ((u - Real.log δ : ℝ) : ℂ)) = (m : ℂ) * (-((u - Real.log δ : ℝ) : ℂ)) := by ring
  have h2 : -((m : ℂ) * (u : ℂ)) = (m : ℂ) * (-(u : ℂ)) := by ring
  rw [h1, h2, Complex.exp_nat_mul, Complex.exp_nat_mul, cexp_neg_sub_log hδ u, mul_pow]

/-- Exact Stokes jet decomposition for `jetMinus δ r u`:
for `u > L_max + Real.log 4 + 1`,
`jetMinus δ r u (i, j) = jetTilde δ r u (i, j) + ∑' m, etaCoeff (m + 2) * (-(m + 2))^j * δ_i^{m+2} * exp(-(m+2)u)`. -/
@[expose] def jetTilde {d : ℕ} (δ : Fin d → ℝ) (r : ℕ) (u : ℝ) : Fin d × Fin (r + 1) → ℂ :=
  fun p => iteratedDeriv p.2.val (PakNthPrimeEngine.Y I_plus (2 * Real.pi * I)) (u - Real.log (δ p.1))

lemma jetMinus_eq_jetTilde_add_eta {d : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i) (r : ℕ)
    (p : Fin d × Fin (r + 1)) {u : ℝ} (hu : Real.log (δ p.1) + Real.log 4 + 1 < u) :
    jetMinus δ r u p =
      jetTilde δ r u p +
        ∑' m : ℕ, etaCoeff (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ p.2.val *
          (δ p.1 : ℂ) ^ (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))) := by
  obtain ⟨Cc, hCc, hc⟩ := etaCoeff_geom_bound
  have hui_gt : Real.log (2 * 2) + 1 < u - Real.log (δ p.1) := by
    have : (2 * 2 : ℝ) = 4 := by norm_num
    rw [this]; linarith
  have hui_pos : 0 < u - Real.log (δ p.1) := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hloc : I_minus =ᶠ[𝓝 (u - Real.log (δ p.1))]
      fun y : ℝ => PakNthPrimeEngine.Y I_plus (2 * Real.pi * I) y +
        ∑' m : ℕ, etaCoeff (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (y : ℂ))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hui_pos] with y hy
    exact I_minus_stokes_series hy
  have hcd_Y : ContDiff ℝ ⊤ (PakNthPrimeEngine.Y I_plus (2 * Real.pi * I)) :=
    (PakNthPrimeEngine.contDiff_expTau (2 * Real.pi * I)).mul contDiff_I_plus
  rw [jetMinus_eq, hloc.iteratedDeriv_eq,
    PakNthPrimeEngine.iteratedDeriv_add_eta hcd_Y hCc (by norm_num : (0 : ℝ) < 2) hc p.2.val
      (u - Real.log (δ p.1)) hui_gt]
  dsimp only [jetTilde]
  congr 1
  refine tsum_congr fun m => ?_
  rw [cexp_neg_nat_mul_sub_log (hδ_pos p.1) (m + 2) u]
  ring

/-- Uniform bound on `jetTilde - jetPlus` and its linear part in `t = exp (-u)`. -/
lemma jetTilde_sub_jetPlus_bounds {d : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i) (r : ℕ) :
    ∃ (C_lin C_rem : ℝ) (A : ℕ) (U₀ : ℝ), 0 < C_lin ∧ 0 < C_rem ∧ 1 ≤ U₀ ∧
      ∀ p : Fin d × Fin (r + 1), ∀ u ≥ U₀,
        ‖jetTilde δ r u p - jetPlus δ r u p‖ ≤ C_lin * u ^ A * Real.exp (-u) ∧
        ‖jetTilde δ r u p - jetPlus δ r u p -
          (2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
            ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
              if k.val ≤ p.2.val then
                ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
              else 0)‖ ≤ C_rem * u ^ A * Real.exp (-2 * u) := by
  obtain ⟨CH, hCH, A, U1, hU1, hJP⟩ := jetPlus_poly_bound δ r
  let L : ℝ := ∑ i : Fin d, |Real.log (δ i)|
  have hL_nn : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let Mδ : ℝ := (∑ i : Fin d, δ i) + 1
  have hMδ_pos : 0 < Mδ := by
    have : 0 ≤ ∑ i : Fin d, δ i := Finset.sum_nonneg fun i _ => (hδ_pos i).le
    dsimp [Mδ]; linarith
  have hδ_le : ∀ i : Fin d, δ i ≤ Mδ := fun i => by
    have h1 : δ i ≤ ∑ k : Fin d, δ k :=
      Finset.single_le_sum (f := δ) (fun k _ => (hδ_pos k).le) (Finset.mem_univ i)
    dsimp [Mδ]; linarith
  -- Choose uniform constant `K_exp` for `norm_iteratedDeriv_expTau_sub_le` over `n ≤ r`
  have hexp_all : ∃ K_exp > 0, ∀ n : ℕ, n ≤ r → ∀ v : ℝ, 1 ≤ v →
      ‖iteratedDeriv n (PakNthPrimeEngine.expTau (2 * Real.pi * I)) v -
        (if n = 0 then (1 : ℂ) + (2 * Real.pi * I) * Complex.exp (-(v : ℂ))
         else (2 * Real.pi * I) * (-1 : ℂ) ^ n * Complex.exp (-(v : ℂ)))‖ ≤
        K_exp * Real.exp (-2 * v) := by
    choose Kf hKf_pos hKf using fun k : Fin (r + 1) =>
      PakNthPrimeEngine.norm_iteratedDeriv_expTau_sub_le k.val (2 * Real.pi * I)
    refine ⟨(∑ k : Fin (r + 1), Kf k) + 1, by
      have : 0 ≤ ∑ k : Fin (r + 1), Kf k := Finset.sum_nonneg fun k _ => (hKf_pos k).le
      linarith, fun n hn v hv => ?_⟩
    have hle : Kf ⟨n, Nat.lt_succ_of_le hn⟩ ≤ (∑ k : Fin (r + 1), Kf k) + 1 := by
      have h1 := Finset.single_le_sum (f := Kf) (fun k _ => (hKf_pos k).le)
        (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (r + 1)))
      linarith
    exact (hKf ⟨n, Nat.lt_succ_of_le hn⟩ v hv).trans
      (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)
  obtain ⟨K_exp, hK_exp, hExp⟩ := hexp_all
  let B_ch : ℝ := ∑ s ∈ Finset.range (r + 1), (r.choose s : ℝ) + (2 : ℝ) ^ r
  have hB_ch : ∀ j : Fin (r + 1), (∑ s ∈ Finset.range (j.val + 1), (j.val.choose s : ℝ)) ≤ (2 : ℝ) ^ r := by
    intro j
    have h1 : (∑ s ∈ Finset.range (j.val + 1), (j.val.choose s : ℝ)) = (2 : ℝ) ^ j.val := by
      exact_mod_cast Nat.sum_range_choose j.val
    rw [h1]
    exact pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp j.isLt)
  let C_rem : ℝ := (2 : ℝ) ^ r * K_exp * Mδ ^ 2 * CH
  let C_lin : ℝ := (2 : ℝ) ^ r * (2 * Real.pi * Mδ + K_exp * Mδ ^ 2) * CH
  refine ⟨C_lin, C_rem, A, max U1 (L + 2), by dsimp [C_lin]; positivity, by dsimp [C_rem]; positivity,
    le_trans hU1 (le_max_left _ _), fun p u hu => ?_⟩
  have huU1 : U1 ≤ u := (le_max_left _ _).trans hu
  have huL : L + 2 ≤ u := (le_max_right _ _).trans hu
  have hu1 : 1 ≤ u := hU1.trans huU1
  have hLi : |Real.log (δ p.1)| ≤ L :=
    Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
  let v : ℝ := u - Real.log (δ p.1)
  have hv1 : 1 ≤ v := by dsimp [v]; have := (abs_le.mp hLi).2; linarith
  have hδi_pos : 0 < δ p.1 := hδ_pos p.1
  have hexp_v : Real.exp (-v) = δ p.1 * Real.exp (-u) := by
    dsimp [v]; rw [show -(u - Real.log (δ p.1)) = Real.log (δ p.1) + (-u) by ring,
      Real.exp_add, Real.exp_log hδi_pos]
  have hexp_2v : Real.exp (-2 * v) = (δ p.1) ^ 2 * Real.exp (-2 * u) := by
    have h1 : -2 * v = (-v) + (-v) := by ring
    have h2 : -2 * u = (-u) + (-u) := by ring
    rw [h1, Real.exp_add, hexp_v, h2, Real.exp_add]; ring
  -- Expand `jetTilde δ r u p` using `PakNthPrimeEngine.iteratedDeriv_Y_eq`
  have hY_eq : jetTilde δ r u p =
      ∑ s ∈ Finset.range (p.2.val + 1),
        (p.2.val.choose s : ℂ) *
          iteratedDeriv (p.2.val - s) (PakNthPrimeEngine.expTau (2 * Real.pi * I)) v *
          iteratedDeriv s I_plus v :=
    PakNthPrimeEngine.iteratedDeriv_Y_eq contDiff_I_plus p.2.val (2 * Real.pi * I) v
  -- Rewrite the linear part sum over `Fin (r + 1)` as a sum over `Finset.range (p.2.val + 1)`
  have hlin_eq :
      jetPlus δ r u p +
        (2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
          ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
            else 0) =
      ∑ s ∈ Finset.range (p.2.val + 1),
        (p.2.val.choose s : ℂ) *
          (if p.2.val - s = 0 then (1 : ℂ) + (2 * Real.pi * I) * Complex.exp (-(v : ℂ))
           else (2 * Real.pi * I) * (-1 : ℂ) ^ (p.2.val - s) * Complex.exp (-(v : ℂ))) *
          iteratedDeriv s I_plus v := by
    have hbij : (∑ k : Fin (r + 1),
        if k.val ≤ p.2.val then
          ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
        else 0) =
        ∑ s ∈ Finset.range (p.2.val + 1),
          ((p.2.val.choose s : ℂ) * (-1 : ℂ) ^ (p.2.val - s)) * iteratedDeriv s I_plus v := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      · intro k₁ _ k₂ _ h; exact Fin.ext h
      · intro s hs
        have hsle : s ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        refine ⟨⟨s, lt_of_le_of_lt hsle p.2.isLt⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hsle
      · intro k _; rw [jetPlus_eq]
    rw [hbij, Finset.mul_sum, Finset.mul_sum]
    have hsplit : ∑ s ∈ Finset.range (p.2.val + 1),
        (p.2.val.choose s : ℂ) *
          (if p.2.val - s = 0 then (1 : ℂ) + (2 * Real.pi * I) * Complex.exp (-(v : ℂ))
           else (2 * Real.pi * I) * (-1 : ℂ) ^ (p.2.val - s) * Complex.exp (-(v : ℂ))) *
          iteratedDeriv s I_plus v =
        (∑ s ∈ Finset.range (p.2.val + 1),
          if p.2.val - s = 0 then (p.2.val.choose s : ℂ) * iteratedDeriv s I_plus v else 0) +
        (∑ s ∈ Finset.range (p.2.val + 1),
          (p.2.val.choose s : ℂ) * ((2 * Real.pi * I) * (-1 : ℂ) ^ (p.2.val - s) * Complex.exp (-(v : ℂ))) *
            iteratedDeriv s I_plus v) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs with h0
      · rw [h0, pow_zero]; ring
      · ring
    rw [hsplit]
    congr 1
    · rw [Finset.sum_eq_single p.2.val]
      · simp [Nat.choose_self, jetPlus_eq, v]
      · intro s hs hne
        have hsle : s ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        have hsub : p.2.val - s ≠ 0 := by omega
        simp [hsub]
      · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hnot
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [cexp_neg_sub_log hδi_pos u]; ring
  -- Bound the quadratic remainder first
  have hrem_bd : ‖jetTilde δ r u p - jetPlus δ r u p -
        (2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
          ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
            else 0)‖ ≤ C_rem * u ^ A * Real.exp (-2 * u) := by
    have hdiff_eq : jetTilde δ r u p - jetPlus δ r u p -
          (2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
            ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
              if k.val ≤ p.2.val then
                ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
              else 0) =
        ∑ s ∈ Finset.range (p.2.val + 1),
          (p.2.val.choose s : ℂ) *
            (iteratedDeriv (p.2.val - s) (PakNthPrimeEngine.expTau (2 * Real.pi * I)) v -
              (if p.2.val - s = 0 then (1 : ℂ) + (2 * Real.pi * I) * Complex.exp (-(v : ℂ))
               else (2 * Real.pi * I) * (-1 : ℂ) ^ (p.2.val - s) * Complex.exp (-(v : ℂ)))) *
            iteratedDeriv s I_plus v := by
      rw [sub_sub, hY_eq, hlin_eq, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => by ring
    rw [hdiff_eq]
    calc ‖∑ s ∈ Finset.range (p.2.val + 1), _‖
        ≤ ∑ s ∈ Finset.range (p.2.val + 1),
            (p.2.val.choose s : ℝ) * (K_exp * Real.exp (-2 * v)) * (CH * u ^ A) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
          have hsle : s ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
          rw [norm_mul, norm_mul, Complex.norm_natCast]
          have h1 := hExp (p.2.val - s) (by omega) v hv1
          have h2 : ‖iteratedDeriv s I_plus v‖ ≤ CH * u ^ A := by
            have := hJP (p.1, ⟨s, lt_of_le_of_lt hsle p.2.isLt⟩) u huU1
            simpa [jetPlus_eq, v] using this
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)
      _ = (∑ s ∈ Finset.range (p.2.val + 1), (p.2.val.choose s : ℝ)) *
            (K_exp * Real.exp (-2 * v) * (CH * u ^ A)) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun s _ => by ring
      _ ≤ (2 : ℝ) ^ r * (K_exp * (Mδ ^ 2 * Real.exp (-2 * u)) * (CH * u ^ A)) := by
          rw [hexp_2v]
          have hch := hB_ch p.2
          have hδ2 : (δ p.1) ^ 2 ≤ Mδ ^ 2 := pow_le_pow_left₀ hδi_pos.le (hδ_le p.1) 2
          gcongr
      _ = C_rem * u ^ A * Real.exp (-2 * u) := by dsimp [C_rem]; ring
  -- Deduce the linear bound by triangle inequality
  have hlin_term_bd :
      ‖(2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
          ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
            else 0)‖ ≤ ((2 : ℝ) ^ r * (2 * Real.pi * Mδ) * CH) * u ^ A * Real.exp (-u) := by
    rw [norm_mul]
    have h2pi : ‖(2 * (Real.pi : ℂ) * I * Complex.exp (-(u : ℂ)))‖ = 2 * Real.pi * Real.exp (-u) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_exp]
      simp
    have hδn : ‖(δ p.1 : ℂ)‖ = δ p.1 := by rw [Complex.norm_real, Real.norm_of_nonneg hδi_pos.le]
    have hsum_bd : ‖∑ k : Fin (r + 1),
          if k.val ≤ p.2.val then
            ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
          else 0‖ ≤ (2 : ℝ) ^ r * (CH * u ^ A) := by
      have hbij : (∑ k : Fin (r + 1),
          if k.val ≤ p.2.val then
            ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
          else 0) =
          ∑ s ∈ Finset.range (p.2.val + 1),
            ((p.2.val.choose s : ℂ) * (-1 : ℂ) ^ (p.2.val - s)) * iteratedDeriv s I_plus v := by
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
        · intro k₁ _ k₂ _ h; exact Fin.ext h
        · intro s hs
          have hsle : s ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
          refine ⟨⟨s, lt_of_le_of_lt hsle p.2.isLt⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hsle
        · intro k _; rw [jetPlus_eq]
      rw [hbij]
      calc ‖∑ s ∈ Finset.range (p.2.val + 1), _‖
          ≤ ∑ s ∈ Finset.range (p.2.val + 1), (p.2.val.choose s : ℝ) * (CH * u ^ A) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
            have hsle : s ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
            rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_neg, norm_one, one_pow, mul_one]
            have h2 : ‖iteratedDeriv s I_plus v‖ ≤ CH * u ^ A := by
              have := hJP (p.1, ⟨s, lt_of_le_of_lt hsle p.2.isLt⟩) u huU1
              simpa [jetPlus_eq, v] using this
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (∑ s ∈ Finset.range (p.2.val + 1), (p.2.val.choose s : ℝ)) * (CH * u ^ A) := (Finset.sum_mul _ _ _).symm
        _ ≤ (2 : ℝ) ^ r * (CH * u ^ A) := mul_le_mul_of_nonneg_right (hB_ch p.2) (by positivity)
    rw [h2pi, norm_mul, hδn]
    have hδle := hδ_le p.1
    calc (2 * Real.pi * Real.exp (-u)) * (δ p.1 * ‖_‖)
        ≤ (2 * Real.pi * Real.exp (-u)) * (Mδ * ((2 : ℝ) ^ r * (CH * u ^ A))) := by gcongr
      _ = ((2 : ℝ) ^ r * (2 * Real.pi * Mδ) * CH) * u ^ A * Real.exp (-u) := by ring
  refine ⟨?_, hrem_bd⟩
  have h2u_le : Real.exp (-2 * u) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have htri : ‖jetTilde δ r u p - jetPlus δ r u p‖ ≤
      ‖jetTilde δ r u p - jetPlus δ r u p -
        (2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
          ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
            else 0)‖ +
      ‖(2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
          ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
            else 0)‖ := by
    have := norm_add_le
      (jetTilde δ r u p - jetPlus δ r u p -
        (2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
          ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
            else 0))
      ((2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
          ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * jetPlus δ r u (p.1, k)
            else 0))
    simpa only [sub_add_cancel] using this
  have hrem_u : C_rem * u ^ A * Real.exp (-2 * u) ≤ C_rem * u ^ A * Real.exp (-u) :=
    mul_le_mul_of_nonneg_left h2u_le (by positivity)
  have hsum_C : C_rem * u ^ A * Real.exp (-u) + ((2 : ℝ) ^ r * (2 * Real.pi * Mδ) * CH) * u ^ A * Real.exp (-u) =
      C_lin * u ^ A * Real.exp (-u) := by dsimp [C_lin, C_rem]; ring
  linarith

/-- Uniform tail bound on the shifted `η`-series for any order `M ≥ 2`. -/
lemma norm_shifted_eta_tail_le {d : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i) (r M : ℕ) (hM : 2 ≤ M) :
    ∃ K > 0, ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ p : Fin d × Fin (r + 1), ∀ u ≥ U₀,
      ‖∑' m : ℕ, etaCoeff (m + M) * (-(((m + M : ℕ) : ℂ))) ^ p.2.val *
          (δ p.1 : ℂ) ^ (m + M) * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))‖ ≤
        K * Real.exp (-(M : ℝ) * u) := by
  obtain ⟨Cc, hCc, hc⟩ := etaCoeff_geom_bound
  choose Kf hKf_pos hKf using fun j : Fin (r + 1) =>
    PakNthPrimeEngine.norm_tsum_tail_le hCc (by norm_num : (0 : ℝ) < 2) hc j.val M hM
  let L : ℝ := ∑ i : Fin d, |Real.log (δ i)|
  have hL_nn : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let Mδ : ℝ := (∑ i : Fin d, δ i) + 1
  have hMδ_pos : 0 < Mδ := by
    have : 0 ≤ ∑ i : Fin d, δ i := Finset.sum_nonneg fun i _ => (hδ_pos i).le
    dsimp [Mδ]; linarith
  have hδ_le : ∀ i : Fin d, δ i ≤ Mδ := fun i => by
    have h1 : δ i ≤ ∑ k : Fin d, δ k :=
      Finset.single_le_sum (f := δ) (fun k _ => (hδ_pos k).le) (Finset.mem_univ i)
    dsimp [Mδ]; linarith
  let K_tot : ℝ := ((∑ j : Fin (r + 1), Kf j) + 1) * Mδ ^ M
  have hK_pos : 0 < K_tot := by
    have : 0 ≤ ∑ j : Fin (r + 1), Kf j := Finset.sum_nonneg fun j _ => (hKf_pos j).le
    dsimp [K_tot]; positivity
  refine ⟨K_tot, hK_pos, L + Real.log 4 + 2, by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith, fun p u hu => ?_⟩
  have hLi : |Real.log (δ p.1)| ≤ L :=
    Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
  let v : ℝ := u - Real.log (δ p.1)
  have hv_ge : Real.log (2 * 2) + 1 ≤ v := by
    have h4 : (2 * 2 : ℝ) = 4 := by norm_num
    rw [h4]; dsimp [v]; have := (abs_le.mp hLi).2; linarith
  have hcongr : (∑' m : ℕ, etaCoeff (m + M) * (-(((m + M : ℕ) : ℂ))) ^ p.2.val *
        (δ p.1 : ℂ) ^ (m + M) * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))) =
      ∑' m : ℕ, etaCoeff (m + M) * (-(((m + M : ℕ) : ℂ))) ^ p.2.val *
        Complex.exp (-(((m + M : ℕ) : ℂ) * (v : ℂ))) := by
    refine tsum_congr fun m => ?_
    rw [cexp_neg_nat_mul_sub_log (hδ_pos p.1) (m + M) u]; ring
  rw [hcongr]
  have h1 := hKf p.2 v hv_ge
  have hexp_Mv : Real.exp (-(M : ℝ) * v) = (δ p.1) ^ M * Real.exp (-(M : ℝ) * u) := by
    have hrew : -(M : ℝ) * v = (M : ℝ) * Real.log (δ p.1) + (-(M : ℝ) * u) := by dsimp [v]; ring
    rw [hrew, Real.exp_add, Real.exp_nat_mul, Real.exp_log (hδ_pos p.1)]
  rw [hexp_Mv] at h1
  have hKf_le : Kf p.2 ≤ (∑ j : Fin (r + 1), Kf j) + 1 := by
    have h := Finset.single_le_sum (f := Kf) (fun j _ => (hKf_pos j).le) (Finset.mem_univ p.2)
    linarith
  have hδM : (δ p.1) ^ M ≤ Mδ ^ M := pow_le_pow_left₀ (hδ_pos p.1).le (hδ_le p.1) M
  have hsum_nn : 0 ≤ ∑ j : Fin (r + 1), Kf j := Finset.sum_nonneg fun j _ => (hKf_pos j).le
  have hδi_nn : 0 ≤ δ p.1 := (hδ_pos p.1).le
  calc ‖_‖ ≤ Kf p.2 * ((δ p.1) ^ M * Real.exp (-(M : ℝ) * u)) := h1
    _ ≤ ((∑ j : Fin (r + 1), Kf j) + 1) * (Mδ ^ M * Real.exp (-(M : ℝ) * u)) := by gcongr
    _ = K_tot * Real.exp (-(M : ℝ) * u) := by dsimp [K_tot]; ring

/-- **Step 1 (`B_op_preserves_flatIdeal`)**:
The simultaneous affine derivation `B_op δ` preserves the flat-evaluation ideal `InFlatIdeal δ`. -/
theorem B_op_preserves_flatIdeal {d r : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (hP : InFlatIdeal δ P) :
    InFlatIdeal δ (B_op δ P) := by
  have hexact := mixed_flat_implies_exact_vanishing δ P hP
  obtain ⟨CH, hCH, A0, U_jp, hU_jp, hJP⟩ := jetPlus_poly_bound δ r
  obtain ⟨C_lin, C_rem, A1, U_jt, hClin, hCrem, hU_jt, hJT⟩ := jetTilde_sub_jetPlus_bounds hδ_pos r
  obtain ⟨K_eta, hKeta, U_eta, hU_eta, hEta⟩ := norm_shifted_eta_tail_le hδ_pos r 2 le_rfl
  obtain ⟨C0, C1, C2, D, hC0, hC1, hC2, hPbd⟩ := mvPolynomial_bounds_general P
  -- Uniform bound on `eval x (pderiv p P)`
  have hpderiv_bd : ∃ Cp > 0, ∃ Dp : ℕ, ∀ (x : Fin d × Fin (r + 1) → ℂ) (Mx : ℝ),
      1 ≤ Mx → (∀ p, ‖x p‖ ≤ Mx) → ∀ p, ‖MvPolynomial.eval x (MvPolynomial.pderiv p P)‖ ≤ Cp * Mx ^ Dp := by
    choose c0 _ _ dp hc0 _ _ hbd using fun p : Fin d × Fin (r + 1) =>
      mvPolynomial_bounds_general (MvPolynomial.pderiv p P)
    let Cp : ℝ := (∑ p : Fin d × Fin (r + 1), c0 p) + 1
    let Dp : ℕ := Finset.univ.sup dp
    refine ⟨Cp, by
      have : 0 ≤ ∑ p : Fin d × Fin (r + 1), c0 p := Finset.sum_nonneg fun p _ => (hc0 p).le
      dsimp [Cp]; linarith, Dp, fun x Mx hMx hx p => ?_⟩
    have h1 := (hbd p x 0 Mx 0 hMx le_rfl zero_le_one hx (fun _ => by simp)).1
    have hc_le : c0 p ≤ Cp := by
      have := Finset.single_le_sum (f := c0) (fun q _ => (hc0 q).le) (Finset.mem_univ p)
      dsimp [Cp]; linarith
    have hd_le : Mx ^ dp p ≤ Mx ^ Dp := pow_le_pow_right₀ hMx (Finset.le_sup (Finset.mem_univ p))
    exact h1.trans (mul_le_mul hc_le hd_le (by positivity) (by
      have : 0 ≤ ∑ q : Fin d × Fin (r + 1), c0 q := Finset.sum_nonneg fun q _ => (hc0 q).le
      dsimp [Cp]; linarith))
  obtain ⟨Cp, hCp, Dp, hPd⟩ := hpderiv_bd
  let A : ℕ := max A0 A1
  let L : ℝ := ∑ i : Fin d, |Real.log (δ i)|
  let C_Δ : ℝ := C_lin + K_eta
  let Mx_coeff : ℝ := max 1 CH
  -- Choose `U_small` so `C_Δ * u ^ A * exp (-u) ≤ 1` for `u ≥ U_small`
  obtain ⟨C_sm, hCsm, U_sm, hUsm1, hSm⟩ := PakNthPrimeEngine.exists_bound_pow_mul_exp_neg C_Δ (by positivity) A 1
  let U_cut : ℝ := max (max (max U_jp U_jt) (max U_eta (L + Real.log 4 + 2))) (max U_sm (C_sm + 1))
  -- Show exponential decay `‖eval (jetPlus δ r u) (B_op δ P)‖ ≤ K_tot * u ^ A_tot * exp (-u)`
  let cardN : ℝ := (Fintype.card (Fin d × Fin (r + 1)) : ℝ)
  let K_tot : ℝ := (C2 * Mx_coeff ^ D * C_Δ ^ 2 + cardN * Cp * Mx_coeff ^ Dp * (C_rem + K_eta)) / (2 * Real.pi) + 1
  let A_tot : ℕ := max (A * D + 2 * A) (A * Dp + A)
  have hKtot_pos : 0 < K_tot := by dsimp [K_tot]; positivity
  have hexp_decay : ∀ u ≥ U_cut,
      ‖MvPolynomial.eval (jetPlus δ r u) (B_op δ P)‖ ≤ K_tot * u ^ A_tot * Real.exp (-u) := by
    intro u hu
    have hu_jp : U_jp ≤ u := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hu
    have hu_jt : U_jt ≤ u := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hu
    have hu_eta : U_eta ≤ u := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hu
    have hu_L : L + Real.log 4 + 2 ≤ u := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hu
    have hu_sm : U_sm ≤ u := ((le_max_left _ _).trans (le_max_right _ _)).trans hu
    have hu_Csm : C_sm + 1 ≤ u := ((le_max_right _ _).trans (le_max_right _ _)).trans hu
    have hu1 : 1 ≤ u := hU_jp.trans hu_jp
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    let x : Fin d × Fin (r + 1) → ℂ := jetPlus δ r u
    let Δ : Fin d × Fin (r + 1) → ℂ := fun p => jetMinus δ r u p - jetPlus δ r u p
    have hxΔ : x + Δ = jetMinus δ r u := by ext p; simp [x, Δ]
    let Mx : ℝ := Mx_coeff * u ^ A
    have hMx1 : 1 ≤ Mx := by
      have h1 : 1 ≤ Mx_coeff := le_max_left 1 CH
      have h2 : 1 ≤ u ^ A := one_le_pow₀ hu1
      dsimp [Mx]; nlinarith
    have hx_bd : ∀ p, ‖x p‖ ≤ Mx := fun p => by
      have h1 := hJP p u hu_jp
      have h2 : CH ≤ Mx_coeff := le_max_right 1 CH
      have h3 : u ^ A0 ≤ u ^ A := pow_le_pow_right₀ hu1 (le_max_left A0 A1)
      dsimp [x, Mx]; exact h1.trans (mul_le_mul h2 h3 (by positivity) (by linarith))
    let MΔ : ℝ := C_Δ * u ^ A * Real.exp (-u)
    have hMΔ_nn : 0 ≤ MΔ := by dsimp [MΔ]; positivity
    have hMΔ_le1 : MΔ ≤ 1 := by
      have h1 := hSm u hu_sm
      have h2 : C_sm / u ^ 1 ≤ 1 := by rw [pow_one, div_le_one hu_pos]; linarith
      exact h1.trans h2
    have hΔ_bd : ∀ p, ‖Δ p‖ ≤ MΔ := fun p => by
      have hLi : |Real.log (δ p.1)| ≤ L :=
        Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
      have hui_gt : Real.log (δ p.1) + Real.log 4 + 1 < u := by
        have := (abs_le.mp hLi).2; linarith
      have hdec := jetMinus_eq_jetTilde_add_eta hδ_pos r p hui_gt
      have hsub : Δ p = (jetTilde δ r u p - jetPlus δ r u p) +
          ∑' m : ℕ, etaCoeff (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ p.2.val *
            (δ p.1 : ℂ) ^ (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))) := by
        dsimp only [Δ]; rw [hdec]; ring
      rw [hsub]
      have h1 := (hJT p u hu_jt).1
      have h2 := hEta p u hu_eta
      have hpowA1 : u ^ A1 ≤ u ^ A := pow_le_pow_right₀ hu1 (le_max_right A0 A1)
      have h2u : Real.exp (-2 * u) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
      have h1u : (1 : ℝ) ≤ u ^ A := one_le_pow₀ hu1
      calc ‖_ + _‖ ≤ ‖jetTilde δ r u p - jetPlus δ r u p‖ + ‖∑' m : ℕ, _‖ := norm_add_le _ _
        _ ≤ C_lin * u ^ A1 * Real.exp (-u) + K_eta * Real.exp (-((2 : ℕ) : ℝ) * u) := add_le_add h1 h2
        _ ≤ C_lin * u ^ A * Real.exp (-u) + K_eta * u ^ A * Real.exp (-u) := by
            have ha : C_lin * u ^ A1 * Real.exp (-u) ≤ C_lin * u ^ A * Real.exp (-u) := by gcongr
            have hb : K_eta * Real.exp (-((2 : ℕ) : ℝ) * u) ≤ K_eta * u ^ A * Real.exp (-u) := by
              rw [Nat.cast_ofNat]
              calc K_eta * Real.exp (-(2 : ℝ) * u)
                  ≤ K_eta * Real.exp (-u) := by
                    have : -(2 : ℝ) * u = -2 * u := by ring
                    rw [this]; exact mul_le_mul_of_nonneg_left h2u hKeta.le
                _ = K_eta * 1 * Real.exp (-u) := by ring
                _ ≤ K_eta * u ^ A * Real.exp (-u) := by gcongr
            linarith
        _ = MΔ := by dsimp [MΔ, C_Δ]; ring
    -- Apply Taylor-1 bound from `mvPolynomial_bounds_general`
    have htay := (hPbd x Δ Mx MΔ hMx1 hMΔ_nn hMΔ_le1 hx_bd hΔ_bd).2.2
    rw [hxΔ, (hexact u).2, (hexact u).1, sub_zero, zero_sub, norm_neg] at htay
    -- Define the linear part vector `v_lin p` so `∑ p, eval x (pderiv p P) * v_lin p = (2πi e^{-u}) * eval x (B_op δ P)`
    let v_lin : Fin d × Fin (r + 1) → ℂ := fun p =>
      (2 * Real.pi * I * Complex.exp (-(u : ℂ))) *
        ((δ p.1 : ℂ) * ∑ k : Fin (r + 1),
          if k.val ≤ p.2.val then
            ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) * x (p.1, k)
          else 0)
    have hB_eq : (2 * Real.pi * I * Complex.exp (-(u : ℂ))) * MvPolynomial.eval x (B_op δ P) =
        ∑ p : Fin d × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv p P) * v_lin p := by
      rw [B_op_apply, map_sum, Finset.mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, PakNthPrimeEngine.eval_smul_eq, map_sum]
      have hinner : (∑ k : Fin (r + 1), MvPolynomial.eval x
            (if k.val ≤ j.val then ((j.val.choose k.val : ℂ) * (-1 : ℂ) ^ (j.val - k.val)) • MvPolynomial.X (i, k) else 0)) =
          ∑ k : Fin (r + 1),
            if k.val ≤ j.val then ((j.val.choose k.val : ℂ) * (-1 : ℂ) ^ (j.val - k.val)) * x (i, k) else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs
        · rw [PakNthPrimeEngine.eval_smul_eq, MvPolynomial.eval_X]
        · simp
      rw [hinner]; dsimp only [v_lin]; ring
    have hdiff_lin : ∀ p : Fin d × Fin (r + 1),
        ‖Δ p - v_lin p‖ ≤ (C_rem + K_eta) * u ^ A * Real.exp (-2 * u) := by
      intro p
      have hLi : |Real.log (δ p.1)| ≤ L :=
        Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
      have hui_gt : Real.log (δ p.1) + Real.log 4 + 1 < u := by
        have := (abs_le.mp hLi).2; linarith
      have hdec := jetMinus_eq_jetTilde_add_eta hδ_pos r p hui_gt
      have hsub : Δ p - v_lin p = (jetTilde δ r u p - jetPlus δ r u p - v_lin p) +
          ∑' m : ℕ, etaCoeff (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ p.2.val *
            (δ p.1 : ℂ) ^ (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))) := by
        dsimp only [Δ]; rw [hdec]; ring
      rw [hsub]
      have h1 := (hJT p u hu_jt).2
      have h2 := hEta p u hu_eta
      have hpowA1 : u ^ A1 ≤ u ^ A := pow_le_pow_right₀ hu1 (le_max_right A0 A1)
      have h1u : (1 : ℝ) ≤ u ^ A := one_le_pow₀ hu1
      calc ‖_ + _‖ ≤ ‖jetTilde δ r u p - jetPlus δ r u p - v_lin p‖ + ‖∑' m : ℕ, _‖ := norm_add_le _ _
        _ ≤ C_rem * u ^ A1 * Real.exp (-2 * u) + K_eta * Real.exp (-((2 : ℕ) : ℝ) * u) := add_le_add h1 h2
        _ ≤ C_rem * u ^ A * Real.exp (-2 * u) + K_eta * u ^ A * Real.exp (-2 * u) := by
            have ha : C_rem * u ^ A1 * Real.exp (-2 * u) ≤ C_rem * u ^ A * Real.exp (-2 * u) := by gcongr
            have hb : K_eta * Real.exp (-((2 : ℕ) : ℝ) * u) ≤ K_eta * u ^ A * Real.exp (-2 * u) := by
              rw [Nat.cast_ofNat]
              have h2e : -(2 : ℝ) * u = -2 * u := by ring
              rw [h2e]
              calc K_eta * Real.exp (-2 * u) = K_eta * 1 * Real.exp (-2 * u) := by ring
                _ ≤ K_eta * u ^ A * Real.exp (-2 * u) := by gcongr
            linarith
        _ = (C_rem + K_eta) * u ^ A * Real.exp (-2 * u) := by ring
    have hsum_err : ‖(∑ p : Fin d × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv p P) * v_lin p) -
          (∑ p : Fin d × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv p P) * Δ p)‖ ≤
        cardN * Cp * Mx ^ Dp * ((C_rem + K_eta) * u ^ A * Real.exp (-2 * u)) := by
      rw [← Finset.sum_sub_distrib]
      calc ‖∑ p : Fin d × Fin (r + 1), _‖
          ≤ ∑ p : Fin d × Fin (r + 1),
              ‖MvPolynomial.eval x (MvPolynomial.pderiv p P) * (v_lin p - Δ p)‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
            rw [← mul_sub]
        _ ≤ ∑ _p : Fin d × Fin (r + 1),
              (Cp * Mx ^ Dp) * ((C_rem + K_eta) * u ^ A * Real.exp (-2 * u)) := by
            refine Finset.sum_le_sum fun p _ => ?_
            rw [norm_mul, norm_sub_rev]
            exact mul_le_mul (hPd x Mx hMx1 hx_bd p) (hdiff_lin p) (norm_nonneg _) (by positivity)
        _ = cardN * Cp * Mx ^ Dp * ((C_rem + K_eta) * u ^ A * Real.exp (-2 * u)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [cardN]; ring
    have hprod_bd : ‖(2 * Real.pi * I * Complex.exp (-(u : ℂ))) * MvPolynomial.eval x (B_op δ P)‖ ≤
        (C2 * Mx_coeff ^ D * C_Δ ^ 2 + cardN * Cp * Mx_coeff ^ Dp * (C_rem + K_eta)) *
          u ^ A_tot * Real.exp (-2 * u) := by
      rw [hB_eq]
      have htri := norm_add_le
        ((∑ p : Fin d × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv p P) * v_lin p) -
          (∑ p : Fin d × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv p P) * Δ p))
        (∑ p : Fin d × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv p P) * Δ p)
      rw [sub_add_cancel] at htri
      have hterm1 : C2 * Mx ^ D * MΔ ^ 2 ≤ (C2 * Mx_coeff ^ D * C_Δ ^ 2) * u ^ A_tot * Real.exp (-2 * u) := by
        dsimp only [Mx, MΔ]
        rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        have hexp2 : Real.exp (-u) ^ 2 = Real.exp (-2 * u) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        rw [hexp2]
        have hpow : u ^ (A * D) * u ^ (A * 2) ≤ u ^ A_tot := by
          rw [← pow_add]
          exact pow_le_pow_right₀ hu1 (by dsimp [A_tot]; omega)
        calc C2 * (Mx_coeff ^ D * u ^ (A * D)) * (C_Δ ^ 2 * u ^ (A * 2) * Real.exp (-2 * u))
            = (C2 * Mx_coeff ^ D * C_Δ ^ 2) * (u ^ (A * D) * u ^ (A * 2)) * Real.exp (-2 * u) := by ring
          _ ≤ (C2 * Mx_coeff ^ D * C_Δ ^ 2) * u ^ A_tot * Real.exp (-2 * u) := by gcongr
      have hterm2 : cardN * Cp * Mx ^ Dp * ((C_rem + K_eta) * u ^ A * Real.exp (-2 * u)) ≤
          (cardN * Cp * Mx_coeff ^ Dp * (C_rem + K_eta)) * u ^ A_tot * Real.exp (-2 * u) := by
        dsimp only [Mx]
        rw [mul_pow, ← pow_mul]
        have hpow : u ^ (A * Dp) * u ^ A ≤ u ^ A_tot := by
          rw [← pow_add]
          exact pow_le_pow_right₀ hu1 (by dsimp [A_tot]; omega)
        calc cardN * Cp * (Mx_coeff ^ Dp * u ^ (A * Dp)) * ((C_rem + K_eta) * u ^ A * Real.exp (-2 * u))
            = (cardN * Cp * Mx_coeff ^ Dp * (C_rem + K_eta)) * (u ^ (A * Dp) * u ^ A) * Real.exp (-2 * u) := by ring
          _ ≤ (cardN * Cp * Mx_coeff ^ Dp * (C_rem + K_eta)) * u ^ A_tot * Real.exp (-2 * u) := by gcongr
      linarith
    -- Divide by `‖2πi e^{-u}‖ = 2π e^{-u}`
    rw [norm_mul] at hprod_bd
    have h2pi : ‖(2 * (Real.pi : ℂ) * I * Complex.exp (-(u : ℂ)))‖ = 2 * Real.pi * Real.exp (-u) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_exp]
      simp
    rw [h2pi] at hprod_bd
    have hden_pos : 0 < 2 * Real.pi * Real.exp (-u) := by positivity
    have hexp_split : Real.exp (-2 * u) = Real.exp (-u) * Real.exp (-u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hdiv := (le_div_iff₀' hden_pos).mpr hprod_bd
    refine hdiv.trans ?_
    rw [hexp_split]
    have hsimp : (C2 * Mx_coeff ^ D * C_Δ ^ 2 + cardN * Cp * Mx_coeff ^ Dp * (C_rem + K_eta)) *
          u ^ A_tot * (Real.exp (-u) * Real.exp (-u)) / (2 * Real.pi * Real.exp (-u)) =
        ((C2 * Mx_coeff ^ D * C_Δ ^ 2 + cardN * Cp * Mx_coeff ^ Dp * (C_rem + K_eta)) / (2 * Real.pi)) *
          u ^ A_tot * Real.exp (-u) := by
      field_simp [Real.pi_ne_zero, (Real.exp_pos (-u)).ne']
    rw [hsimp]
    dsimp only [K_tot]
    nlinarith [pow_pos hu_pos A_tot, Real.exp_pos (-u)]
  -- Convert exponential decay to all inverse powers via `exists_bound_pow_mul_exp_neg`
  intro N
  obtain ⟨C', hC', U', _, hN⟩ := PakNthPrimeEngine.exists_bound_pow_mul_exp_neg K_tot hKtot_pos A_tot N
  refine ⟨C', hC', max U_cut U', fun u hu => ?_⟩
  exact (hexp_decay u ((le_max_left _ _).trans hu)).trans (hN u ((le_max_right _ _).trans hu))

/-- The entire `τ`-deformed evaluation `F_multi δ P u τ`. -/
@[expose] def F_multi {d r : ℕ} (δ : Fin d → ℝ) (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ)
    (u : ℝ) (τ : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun p : Fin d × Fin (r + 1) => iteratedDeriv p.2.val (PakNthPrimeEngine.Y I_plus τ) (u - Real.log (δ p.1))) P

lemma hasDerivAt_F_multi {d r : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (u : ℝ) (τ : ℂ) :
    HasDerivAt (F_multi δ P u) (Complex.exp (-(u : ℂ)) * F_multi δ (B_op δ P) u τ) τ := by
  have hx : ∀ p : Fin d × Fin (r + 1),
      HasDerivAt (fun t => iteratedDeriv p.2.val (PakNthPrimeEngine.Y I_plus t) (u - Real.log (δ p.1)))
        (Complex.exp (-(u : ℂ)) * ((δ p.1 : ℂ) *
          ∑ k : Fin (r + 1),
            if k.val ≤ p.2.val then
              ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) *
                iteratedDeriv k.val (PakNthPrimeEngine.Y I_plus τ) (u - Real.log (δ p.1))
            else 0)) τ := by
    intro p
    have h1 := PakNthPrimeEngine.hasDerivAt_tau_iteratedDeriv_Y contDiff_I_plus p.2.val (u - Real.log (δ p.1)) τ
    convert h1 using 1
    rw [cexp_neg_sub_log (hδ_pos p.1) u]
    have hbij : (∑ k : Fin (r + 1),
          if k.val ≤ p.2.val then
            ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) *
              iteratedDeriv k.val (PakNthPrimeEngine.Y I_plus τ) (u - Real.log (δ p.1))
          else 0) =
        ∑ m ∈ Finset.range (p.2.val + 1),
          ((p.2.val.choose m : ℂ) * (-1 : ℂ) ^ (p.2.val - m)) *
            iteratedDeriv m (PakNthPrimeEngine.Y I_plus τ) (u - Real.log (δ p.1)) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      · intro k₁ _ k₂ _ h; exact Fin.ext h
      · intro m hm
        have hmle : m ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        refine ⟨⟨m, lt_of_le_of_lt hmle p.2.isLt⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hmle
      · intro k _; rfl
    rw [hbij]; ring
  have hmain := hasDerivAt_mvPolynomial_eval_general P
    (fun t p => iteratedDeriv p.2.val (PakNthPrimeEngine.Y I_plus t) (u - Real.log (δ p.1)))
    (fun t p => Complex.exp (-(u : ℂ)) * ((δ p.1 : ℂ) *
      ∑ k : Fin (r + 1),
        if k.val ≤ p.2.val then
          ((p.2.val.choose k.val : ℂ) * (-1 : ℂ) ^ (p.2.val - k.val)) *
            iteratedDeriv k.val (PakNthPrimeEngine.Y I_plus t) (u - Real.log (δ p.1))
        else 0)) τ hx
  refine hmain.congr_deriv ?_
  unfold F_multi
  rw [B_op_apply, map_sum, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, PakNthPrimeEngine.eval_smul_eq, map_sum]
  have hinner : (∑ k : Fin (r + 1), MvPolynomial.eval
        (fun p : Fin d × Fin (r + 1) => iteratedDeriv p.2.val (PakNthPrimeEngine.Y I_plus τ) (u - Real.log (δ p.1)))
        (if k.val ≤ j.val then ((j.val.choose k.val : ℂ) * (-1 : ℂ) ^ (j.val - k.val)) • MvPolynomial.X (i, k) else 0)) =
      ∑ k : Fin (r + 1),
        if k.val ≤ j.val then
          ((j.val.choose k.val : ℂ) * (-1 : ℂ) ^ (j.val - k.val)) *
            iteratedDeriv k.val (PakNthPrimeEngine.Y I_plus τ) (u - Real.log (δ i))
        else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [PakNthPrimeEngine.eval_smul_eq, MvPolynomial.eval_X]
    · simp
  rw [hinner]; ring

lemma iteratedDeriv_F_multi {d r : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i)
    (k : ℕ) (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (u : ℝ) (τ : ℂ) :
    iteratedDeriv k (F_multi δ P u) τ =
      Complex.exp (-((k : ℂ) * (u : ℂ))) * F_multi δ ((B_op δ)^[k] P) u τ := by
  induction k generalizing P τ with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (F_multi δ P u) = fun t => Complex.exp (-(u : ℂ)) * F_multi δ (B_op δ P) u t :=
      funext fun t => (hasDerivAt_F_multi hδ_pos P u t).deriv
    rw [hderiv, iteratedDeriv_const_mul_field, ih (B_op δ P) τ,
      Function.iterate_succ_apply, ← mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring

/-- **Step 2 (`tau_invariance_multi`)**:
Any `P ∈ InFlatIdeal δ` vanishes identically on the multiplicatively-flowed tuple `jetTilde δ r u`
for **ALL** `u : ℝ`! -/
theorem tau_invariance_multi {d r : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (hP : InFlatIdeal δ P) :
    ∀ u : ℝ, MvPolynomial.eval (jetTilde δ r u) P = 0 := by
  have hiter : ∀ k : ℕ, InFlatIdeal δ ((B_op δ)^[k] P) := by
    intro k
    induction k with
    | zero => simpa using hP
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact B_op_preserves_flatIdeal hδ_pos _ ih
  intro u
  have hdiff : Differentiable ℂ (F_multi δ P u) :=
    fun τ => (hasDerivAt_F_multi hδ_pos P u τ).differentiableAt
  have h0 : ∀ k : ℕ, iteratedDeriv k (F_multi δ P u) 0 = 0 := by
    intro k
    rw [iteratedDeriv_F_multi hδ_pos k P u 0]
    have hY0 : PakNthPrimeEngine.Y I_plus 0 = I_plus := by ext x; simp [PakNthPrimeEngine.Y, PakNthPrimeEngine.expTau]
    have hF0 : F_multi δ ((B_op δ)^[k] P) u 0 = MvPolynomial.eval (jetPlus δ r u) ((B_op δ)^[k] P) := by
      dsimp only [F_multi]
      refine congrArg (fun x => MvPolynomial.eval x _) (funext fun p => ?_)
      rw [hY0, jetPlus_eq]
    rw [hF0, (mixed_flat_implies_exact_vanishing δ ((B_op δ)^[k] P) (hiter k) u).1, mul_zero]
  exact PakNthPrimeEngine.entire_eq_zero_of_iteratedDeriv_zero hdiff h0 (2 * Real.pi * I)

/-- `Lm_op δ m` strictly drops total degree whenever `0 < P.totalDegree`. -/
lemma Lm_op_totalDegree_lt {d r : ℕ} (δ : Fin d → ℝ) (m : ℕ)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (h : 0 < P.totalDegree) :
    (Lm_op δ m P).totalDegree < P.totalDegree := by
  have hsum_lt : ∀ {α : Type} [DecidableEq α] (s : Finset α)
      (f : α → MvPolynomial (Fin d × Fin (r + 1)) ℂ),
      (∀ a ∈ s, (f a).totalDegree < P.totalDegree) →
      (∑ a ∈ s, f a).totalDegree < P.totalDegree := by
    intro α _ s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (MvPolynomial.totalDegree_add _ _).trans_lt
        (max_lt (hf a (Finset.mem_insert_self a s)) (ih fun b hb => hf b (Finset.mem_insert_of_mem hb)))
  rw [Lm_op_apply]
  refine hsum_lt (Finset.univ : Finset (Fin d)) _ fun i _ =>
    hsum_lt (Finset.univ : Finset (Fin (r + 1))) _ fun j _ => ?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans_lt (PakNthPrimeEngine.totalDegree_pderiv_lt (i, j) P h)

/-- Exact additive-wave translation invariance when `Lm_op δ m P = 0`. -/
theorem eval_add_smul_eq_of_Lm_op_eq_zero {d r : ℕ} (δ : Fin d → ℝ) (m : ℕ)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (hLm : Lm_op δ m P = 0)
    (x : Fin d × Fin (r + 1) → ℂ) (c : ℂ) :
    MvPolynomial.eval (fun p => x p + c * (δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val) P =
      MvPolynomial.eval x P := by
  let g : ℂ → ℂ := fun t => MvPolynomial.eval (fun p => x p + t * (δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val) P
  have hg : ∀ t : ℂ, HasDerivAt g 0 t := by
    intro t
    have hx : ∀ p : Fin d × Fin (r + 1),
        HasDerivAt (fun s : ℂ => x p + s * (δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val)
          ((δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val) t := by
      intro p
      have h1 : HasDerivAt (fun s : ℂ => s * ((δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val))
          ((δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val) t := by
        simpa using (hasDerivAt_id t).mul_const ((δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val)
      have h2 := (hasDerivAt_const t (x p)).fun_add h1
      simpa [mul_assoc] using h2
    have hd := hasDerivAt_mvPolynomial_eval_general P
      (fun s p => x p + s * (δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val)
      (fun _ p => (δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val) t hx
    convert hd using 1
    have h0 : MvPolynomial.eval (fun p => x p + t * (δ p.1 : ℂ) ^ m * (-(m : ℂ)) ^ p.2.val) (Lm_op δ m P) = 0 := by
      rw [hLm, map_zero]
    rw [Lm_op_apply, map_sum] at h0
    rw [← h0, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PakNthPrimeEngine.eval_smul_eq, mul_comm]
  have hconst : g c = g 0 :=
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) c 0
  simpa [g] using hconst

/-- **Step 3 (`strong_induction_Lm_multi_eq_zero`)**:
If `P ∈ InFlatIdeal δ` is nonzero of minimal total degree, then `Lm_op δ M P = 0` for EVERY `M ≥ 2`! -/
theorem strong_induction_Lm_multi_eq_zero {d r : ℕ} {δ : Fin d → ℝ} (hδ_pos : ∀ i, 0 < δ i)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ)
    (hP_flat : InFlatIdeal δ P) (hP_deg : 0 < P.totalDegree)
    (hmin : ∀ Q : MvPolynomial (Fin d × Fin (r + 1)) ℂ,
      InFlatIdeal δ Q → Q.totalDegree < P.totalDegree → Q = 0) :
    ∀ M : ℕ, 2 ≤ M → Lm_op δ M P = 0 := by
  have hexact := mixed_flat_implies_exact_vanishing δ P hP_flat
  have htilde := tau_invariance_multi hδ_pos P hP_flat
  obtain ⟨CH, hCH, A0, U_jp, hU_jp, hJP⟩ := jetPlus_poly_bound δ r
  obtain ⟨C_lin, _, A1, U_jt, hClin, _, hU_jt, hJT⟩ := jetTilde_sub_jetPlus_bounds hδ_pos r
  obtain ⟨C0, C1, C2, D, hC0, hC1, hC2, hPbd⟩ := mvPolynomial_bounds_general P
  have hpderiv_bd : ∃ Cp > 0, ∃ Dp : ℕ, ∀ (x : Fin d × Fin (r + 1) → ℂ) (Mx : ℝ),
      1 ≤ Mx → (∀ p, ‖x p‖ ≤ Mx) → ∀ p, ‖MvPolynomial.eval x (MvPolynomial.pderiv p P)‖ ≤ Cp * Mx ^ Dp := by
    choose c0 _ _ dp hc0 _ _ hbd using fun p : Fin d × Fin (r + 1) =>
      mvPolynomial_bounds_general (MvPolynomial.pderiv p P)
    let Cp : ℝ := (∑ p : Fin d × Fin (r + 1), c0 p) + 1
    let Dp : ℕ := Finset.univ.sup dp
    refine ⟨Cp, by
      have : 0 ≤ ∑ p : Fin d × Fin (r + 1), c0 p := Finset.sum_nonneg fun p _ => (hc0 p).le
      dsimp [Cp]; linarith, Dp, fun x Mx hMx hx p => ?_⟩
    have h1 := (hbd p x 0 Mx 0 hMx le_rfl zero_le_one hx (fun _ => by simp)).1
    have hc_le : c0 p ≤ Cp := by
      have := Finset.single_le_sum (f := c0) (fun q _ => (hc0 q).le) (Finset.mem_univ p)
      dsimp [Cp]; linarith
    have hd_le : Mx ^ dp p ≤ Mx ^ Dp := pow_le_pow_right₀ hMx (Finset.le_sup (Finset.mem_univ p))
    exact h1.trans (mul_le_mul hc_le hd_le (by positivity) (by
      have : 0 ≤ ∑ q : Fin d × Fin (r + 1), c0 q := Finset.sum_nonneg fun q _ => (hc0 q).le
      dsimp [Cp]; linarith))
  obtain ⟨Cp, hCp, Dp, hPd⟩ := hpderiv_bd
  obtain ⟨Cc, hCc, hc⟩ := etaCoeff_geom_bound
  let A : ℕ := max A0 A1
  let L : ℝ := ∑ i : Fin d, |Real.log (δ i)|
  intro M
  induction M using Nat.strong_induction_on with
  | ind M ih =>
    intro hM
    -- Show `InFlatIdeal δ (Lm_op δ M P)`, then use minimality of `P.totalDegree`!
    have hLm_flat : InFlatIdeal δ (Lm_op δ M P) := by
      obtain ⟨K_M, hKM, U_M, hU_M, hEtaM⟩ := norm_shifted_eta_tail_le hδ_pos r M hM
      obtain ⟨K_M1, hKM1, U_M1, hU_M1, hEtaM1⟩ := norm_shifted_eta_tail_le hδ_pos r (M + 1) (by omega)
      obtain ⟨_, C1_L, _, D_L, _, hC1L, _, hLbd⟩ := mvPolynomial_bounds_general (Lm_op δ M P)
      -- Bound `‖jetTilde δ r u p‖ ≤ Mx_tilde * u ^ A` and `‖jetTilde - jetPlus‖ ≤ C_lin * u ^ A * exp (-u) ≤ 1`
      obtain ⟨C_sm1, hCsm1, U_sm1, _, hSm1⟩ := PakNthPrimeEngine.exists_bound_pow_mul_exp_neg C_lin hClin A 1
      let U_tail : ℝ := max 1 (Real.log (K_M + 1) + 1)
      let U_cut : ℝ := max (max (max U_jp U_jt) (max U_M U_M1))
        (max (max (L + Real.log 4 + 2) U_tail) (max U_sm1 (C_sm1 + 1)))
      let Mx_c : ℝ := max 1 (CH + C_lin)
      let cardN : ℝ := (Fintype.card (Fin d × Fin (r + 1)) : ℝ)
      have hcM_ne : etaCoeff M ≠ 0 := etaCoeff_ne_zero hM
      have hcM_pos : 0 < ‖etaCoeff M‖ := norm_pos_iff.mpr hcM_ne
      let K_tot : ℝ := (C2 * Mx_c ^ D * K_M ^ 2 + cardN * Cp * Mx_c ^ Dp * K_M1) / ‖etaCoeff M‖ +
        C1_L * Mx_c ^ D_L * C_lin + 1
      let A_tot : ℕ := max (max (A * D) (A * Dp)) (A * D_L + A)
      have hKtot_pos : 0 < K_tot := by dsimp [K_tot]; positivity
      have hexp_decay : ∀ u ≥ U_cut,
          ‖MvPolynomial.eval (jetPlus δ r u) (Lm_op δ M P)‖ ≤ K_tot * u ^ A_tot * Real.exp (-u) := by
        intro u hu
        have hu_jp : U_jp ≤ u := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hu
        have hu_jt : U_jt ≤ u := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hu
        have hu_M : U_M ≤ u := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hu
        have hu_M1 : U_M1 ≤ u := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hu
        have hu_L : L + Real.log 4 + 2 ≤ u := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hu
        have hu_tail : U_tail ≤ u := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hu
        have hu_sm1 : U_sm1 ≤ u := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hu
        have hu_Csm1 : C_sm1 + 1 ≤ u := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hu
        have hu1 : 1 ≤ u := hU_jp.trans hu_jp
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
        -- Define the tail perturbation `tailM p = ∑' m, etaCoeff (m + M) * (-(m+M))^j * δ_i^{m+M} * exp(-(m+M)u)`
        let tailM : Fin d × Fin (r + 1) → ℂ := fun p =>
          ∑' m : ℕ, etaCoeff (m + M) * (-(((m + M : ℕ) : ℂ))) ^ p.2.val *
            (δ p.1 : ℂ) ^ (m + M) * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))
        let tailM1 : Fin d × Fin (r + 1) → ℂ := fun p =>
          ∑' m : ℕ, etaCoeff (m + (M + 1)) * (-(((m + (M + 1) : ℕ) : ℂ))) ^ p.2.val *
            (δ p.1 : ℂ) ^ (m + (M + 1)) * Complex.exp (-(((m + (M + 1) : ℕ) : ℂ) * (u : ℂ)))
        -- Summability of the full `η`-tail at `u` for every `p`
        have hsum_p : ∀ p : Fin d × Fin (r + 1), Summable (fun m : ℕ =>
            etaCoeff (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ p.2.val *
              (δ p.1 : ℂ) ^ (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ)))) := by
          intro p
          have hLi : |Real.log (δ p.1)| ≤ L :=
            Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
          have hv : Real.log (2 * 2) + 1 ≤ u - Real.log (δ p.1) := by
            have h4 : (2 * 2 : ℝ) = 4 := by norm_num
            rw [h4]; have := (abs_le.mp hLi).2; linarith
          have hs := (PakNthPrimeEngine.summable_tail_exp hCc (by norm_num : (0 : ℝ) < 2) hc p.2.val
            (u - Real.log (δ p.1)) hv).of_norm
          refine hs.congr fun m => ?_
          rw [cexp_neg_nat_mul_sub_log (hδ_pos p.1) (m + 2) u]; ring
        -- Remove waves `2 ≤ k < M` from `jetMinus` by repeated translation invariance!
        have hremove : ∀ k : ℕ, k ≤ M - 2 →
            MvPolynomial.eval (fun p => jetTilde δ r u p +
              ∑' m : ℕ, etaCoeff (m + (k + 2)) * (-(((m + (k + 2) : ℕ) : ℂ))) ^ p.2.val *
                (δ p.1 : ℂ) ^ (m + (k + 2)) * Complex.exp (-(((m + (k + 2) : ℕ) : ℂ) * (u : ℂ)))) P = 0 := by
          intro k
          induction k with
          | zero =>
            intro _
            have heq : (fun p => jetTilde δ r u p +
                ∑' m : ℕ, etaCoeff (m + (0 + 2)) * (-(((m + (0 + 2) : ℕ) : ℂ))) ^ p.2.val *
                  (δ p.1 : ℂ) ^ (m + (0 + 2)) * Complex.exp (-(((m + (0 + 2) : ℕ) : ℂ) * (u : ℂ)))) =
                jetMinus δ r u := by
              ext p
              have hLi : |Real.log (δ p.1)| ≤ L :=
                Finset.single_le_sum (f := fun i => |Real.log (δ i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)
              have hui_gt : Real.log (δ p.1) + Real.log 4 + 1 < u := by
                have := (abs_le.mp hLi).2; linarith
              simpa using (jetMinus_eq_jetTilde_add_eta hδ_pos r p hui_gt).symm
            rw [heq]; exact (hexact u).2
          | succ k ihk =>
            intro hk
            have hk_lt : k + 2 < M := by omega
            have hLm_k : Lm_op δ (k + 2) P = 0 := ih (k + 2) hk_lt (by omega)
            have hprev := ihk (by omega)
            have hshift_eq : (fun p => jetTilde δ r u p +
                  ∑' m : ℕ, etaCoeff (m + (k + 2)) * (-(((m + (k + 2) : ℕ) : ℂ))) ^ p.2.val *
                    (δ p.1 : ℂ) ^ (m + (k + 2)) * Complex.exp (-(((m + (k + 2) : ℕ) : ℂ) * (u : ℂ)))) =
                fun p => (jetTilde δ r u p +
                  ∑' m : ℕ, etaCoeff (m + (k + 1 + 2)) * (-(((m + (k + 1 + 2) : ℕ) : ℂ))) ^ p.2.val *
                    (δ p.1 : ℂ) ^ (m + (k + 1 + 2)) * Complex.exp (-(((m + (k + 1 + 2) : ℕ) : ℂ) * (u : ℂ)))) +
                  (etaCoeff (k + 2) * Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ)))) *
                    (δ p.1 : ℂ) ^ (k + 2) * (-(((k + 2 : ℕ) : ℂ))) ^ p.2.val := by
              ext p
              have hsk : Summable (fun m : ℕ => etaCoeff (m + (k + 2)) * (-(((m + (k + 2) : ℕ) : ℂ))) ^ p.2.val *
                  (δ p.1 : ℂ) ^ (m + (k + 2)) * Complex.exp (-(((m + (k + 2) : ℕ) : ℂ) * (u : ℂ)))) := by
                have h1 := (hsum_p p).comp_injective (add_left_injective k)
                refine h1.congr fun m => ?_
                have : m + k + 2 = m + (k + 2) := by omega
                simp only [Function.comp_apply, this]
              rw [hsk.tsum_eq_zero_add]
              simp only [zero_add]
              have hidx : (∑' m : ℕ, etaCoeff (m + 1 + (k + 2)) * (-(((m + 1 + (k + 2) : ℕ) : ℂ))) ^ p.2.val *
                  (δ p.1 : ℂ) ^ (m + 1 + (k + 2)) * Complex.exp (-(((m + 1 + (k + 2) : ℕ) : ℂ) * (u : ℂ)))) =
                  ∑' m : ℕ, etaCoeff (m + (k + 1 + 2)) * (-(((m + (k + 1 + 2) : ℕ) : ℂ))) ^ p.2.val *
                    (δ p.1 : ℂ) ^ (m + (k + 1 + 2)) * Complex.exp (-(((m + (k + 1 + 2) : ℕ) : ℂ) * (u : ℂ))) := by
                refine tsum_congr fun m => ?_
                have : m + 1 + (k + 2) = m + (k + 1 + 2) := by omega
                simp only [this]
              rw [hidx]; ring
            rw [hshift_eq, eval_add_smul_eq_of_Lm_op_eq_zero δ (k + 2) P hLm_k] at hprev
            exact hprev
        have htail_zero : MvPolynomial.eval (jetTilde δ r u + tailM) P = 0 := by
          have h1 := hremove (M - 2) le_rfl
          have hadd : M - 2 + 2 = M := Nat.sub_add_cancel hM
          have heq : jetTilde δ r u + tailM = fun p => jetTilde δ r u p +
              ∑' m : ℕ, etaCoeff (m + (M - 2 + 2)) * (-(((m + (M - 2 + 2) : ℕ) : ℂ))) ^ p.2.val *
                (δ p.1 : ℂ) ^ (m + (M - 2 + 2)) * Complex.exp (-(((m + (M - 2 + 2) : ℕ) : ℂ) * (u : ℂ))) := by
            ext p; simp only [Pi.add_apply, tailM, hadd]
          rw [heq]; exact h1
        -- Split `tailM p = leading_M p + tailM1 p`
        have htail_split : ∀ p, tailM p =
            (etaCoeff M * Complex.exp (-((M : ℂ) * (u : ℂ)))) * (δ p.1 : ℂ) ^ M * (-(M : ℂ)) ^ p.2.val +
              tailM1 p := by
          intro p
          have hsM : Summable (fun m : ℕ => etaCoeff (m + M) * (-(((m + M : ℕ) : ℂ))) ^ p.2.val *
              (δ p.1 : ℂ) ^ (m + M) * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))) := by
            have h1 := (hsum_p p).comp_injective (add_left_injective (M - 2))
            refine h1.congr fun m => ?_
            have : m + (M - 2) + 2 = m + M := by omega
            simp only [Function.comp_apply, this]
          dsimp only [tailM, tailM1]
          rw [hsM.tsum_eq_zero_add]
          simp only [zero_add]
          have hidx : (∑' m : ℕ, etaCoeff (m + 1 + M) * (-(((m + 1 + M : ℕ) : ℂ))) ^ p.2.val *
              (δ p.1 : ℂ) ^ (m + 1 + M) * Complex.exp (-(((m + 1 + M : ℕ) : ℂ) * (u : ℂ)))) =
              ∑' m : ℕ, etaCoeff (m + (M + 1)) * (-(((m + (M + 1) : ℕ) : ℂ))) ^ p.2.val *
                (δ p.1 : ℂ) ^ (m + (M + 1)) * Complex.exp (-(((m + (M + 1) : ℕ) : ℂ) * (u : ℂ))) := by
            refine tsum_congr fun m => ?_
            have : m + 1 + M = m + (M + 1) := by omega
            simp only [this]
          rw [hidx]; ring
        -- Bounds for `mvPolynomial_bounds_general P` around `x = jetTilde δ r u`
        let Mx : ℝ := Mx_c * u ^ A
        have hMx1 : 1 ≤ Mx := by
          have h1 : 1 ≤ Mx_c := le_max_left 1 (CH + C_lin)
          have h2 : 1 ≤ u ^ A := one_le_pow₀ hu1
          dsimp [Mx]; nlinarith
        have hxt_bd : ∀ p, ‖jetTilde δ r u p‖ ≤ Mx := fun p => by
          have h1 := hJP p u hu_jp
          have h2 := (hJT p u hu_jt).1
          have htri : ‖jetTilde δ r u p‖ ≤ ‖jetPlus δ r u p‖ + ‖jetTilde δ r u p - jetPlus δ r u p‖ := by
            have := norm_add_le (jetPlus δ r u p) (jetTilde δ r u p - jetPlus δ r u p); simpa using this
          have hpow0 : u ^ A0 ≤ u ^ A := pow_le_pow_right₀ hu1 (le_max_left A0 A1)
          have hpow1 : u ^ A1 ≤ u ^ A := pow_le_pow_right₀ hu1 (le_max_right A0 A1)
          have hexp1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hMc : CH + C_lin ≤ Mx_c := le_max_right 1 (CH + C_lin)
          calc ‖jetTilde δ r u p‖ ≤ CH * u ^ A0 + C_lin * u ^ A1 * Real.exp (-u) := by linarith
            _ ≤ CH * u ^ A + C_lin * u ^ A * 1 := by gcongr
            _ = (CH + C_lin) * u ^ A := by ring
            _ ≤ Mx := mul_le_mul_of_nonneg_right hMc (by positivity)
        have hxp_bd : ∀ p, ‖jetPlus δ r u p‖ ≤ Mx := fun p => by
          have h1 := hJP p u hu_jp
          have hpow0 : u ^ A0 ≤ u ^ A := pow_le_pow_right₀ hu1 (le_max_left A0 A1)
          have hMc : CH ≤ Mx_c := (by linarith : CH ≤ CH + C_lin).trans (le_max_right 1 (CH + C_lin))
          exact h1.trans (mul_le_mul hMc hpow0 (by positivity) (by linarith [le_max_left (1 : ℝ) (CH + C_lin)]))
        let MΔ : ℝ := K_M * Real.exp (-(M : ℝ) * u)
        have hMΔ_nn : 0 ≤ MΔ := by dsimp [MΔ]; positivity
        have hMΔ_le1 : MΔ ≤ 1 := by
          have h1 : Real.log (K_M + 1) + 1 ≤ u := (le_max_right _ _).trans hu_tail
          have h2 : K_M + 1 ≤ Real.exp u := by
            calc K_M + 1 = Real.exp (Real.log (K_M + 1)) := (Real.exp_log (by positivity)).symm
              _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
          have h3 : Real.exp (-(M : ℝ) * u) ≤ Real.exp (-u) := by
            refine Real.exp_le_exp.mpr ?_
            have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
            nlinarith
          have h4 : K_M * Real.exp (-u) ≤ 1 := by
            rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos u)]; linarith
          calc MΔ = K_M * Real.exp (-(M : ℝ) * u) := rfl
            _ ≤ K_M * Real.exp (-u) := mul_le_mul_of_nonneg_left h3 hKM.le
            _ ≤ 1 := h4
        have htay := (hPbd (jetTilde δ r u) tailM Mx MΔ hMx1 hMΔ_nn hMΔ_le1 hxt_bd (fun p => hEtaM p u hu_M)).2.2
        rw [htail_zero, htilde u, sub_zero, zero_sub, norm_neg] at htay
        -- Separate leading `Lm_op δ M P` term from `tailM1`
        have hLm_sum : (etaCoeff M * Complex.exp (-((M : ℂ) * (u : ℂ)))) *
              MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P) =
            (∑ p : Fin d × Fin (r + 1), MvPolynomial.eval (jetTilde δ r u) (MvPolynomial.pderiv p P) * tailM p) -
            (∑ p : Fin d × Fin (r + 1), MvPolynomial.eval (jetTilde δ r u) (MvPolynomial.pderiv p P) * tailM1 p) := by
          rw [Lm_op_apply, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [PakNthPrimeEngine.eval_smul_eq, htail_split (i, j)]; ring
        have hrem1_bd : ‖∑ p : Fin d × Fin (r + 1), MvPolynomial.eval (jetTilde δ r u) (MvPolynomial.pderiv p P) * tailM1 p‖ ≤
            cardN * Cp * Mx ^ Dp * (K_M1 * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by
          calc ‖∑ p, _‖ ≤ ∑ p, ‖MvPolynomial.eval (jetTilde δ r u) (MvPolynomial.pderiv p P)‖ * ‖tailM1 p‖ :=
                (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => by rw [norm_mul])
            _ ≤ ∑ _p, (Cp * Mx ^ Dp) * (K_M1 * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) :=
                Finset.sum_le_sum fun p _ => mul_le_mul (hPd _ Mx hMx1 hxt_bd p) (hEtaM1 p u hu_M1)
                  (norm_nonneg _) (by positivity)
            _ = cardN * Cp * Mx ^ Dp * (K_M1 * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [cardN]; ring
        have h2M_le : Real.exp (-(M : ℝ) * u) ^ 2 ≤ Real.exp (-((M + 1 : ℕ) : ℝ) * u) := by
          rw [sq, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          push_cast
          have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
          nlinarith
        have hprod_Lm : ‖etaCoeff M‖ * Real.exp (-(M : ℝ) * u) *
              ‖MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P)‖ ≤
            (C2 * Mx_c ^ D * K_M ^ 2 + cardN * Cp * Mx_c ^ Dp * K_M1) *
              u ^ A_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u) := by
          have hnorm_lhs : ‖(etaCoeff M * Complex.exp (-((M : ℂ) * (u : ℂ)))) *
                MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P)‖ =
              ‖etaCoeff M‖ * Real.exp (-(M : ℝ) * u) *
                ‖MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_exp, PakNthPrimeEngine.re_neg_nat_mul_ofReal, neg_mul]
          rw [← hnorm_lhs, hLm_sum]
          have htri := norm_sub_le
            (∑ p, MvPolynomial.eval (jetTilde δ r u) (MvPolynomial.pderiv p P) * tailM p)
            (∑ p, MvPolynomial.eval (jetTilde δ r u) (MvPolynomial.pderiv p P) * tailM1 p)
          have h1' : C2 * Mx ^ D * MΔ ^ 2 ≤ (C2 * Mx_c ^ D * K_M ^ 2) * u ^ A_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u) := by
            dsimp only [Mx, MΔ]
            rw [mul_pow, mul_pow, ← pow_mul]
            have hpow : u ^ (A * D) ≤ u ^ A_tot := pow_le_pow_right₀ hu1 (by dsimp [A_tot]; omega)
            calc C2 * (Mx_c ^ D * u ^ (A * D)) * (K_M ^ 2 * Real.exp (-(M : ℝ) * u) ^ 2)
                = (C2 * Mx_c ^ D * K_M ^ 2) * u ^ (A * D) * Real.exp (-(M : ℝ) * u) ^ 2 := by ring
              _ ≤ (C2 * Mx_c ^ D * K_M ^ 2) * u ^ A_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u) := by gcongr
          have h2' : cardN * Cp * Mx ^ Dp * (K_M1 * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) ≤
              (cardN * Cp * Mx_c ^ Dp * K_M1) * u ^ A_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u) := by
            dsimp only [Mx]
            rw [mul_pow, ← pow_mul]
            have hpow : u ^ (A * Dp) ≤ u ^ A_tot := pow_le_pow_right₀ hu1 (by dsimp [A_tot]; omega)
            calc cardN * Cp * (Mx_c ^ Dp * u ^ (A * Dp)) * (K_M1 * Real.exp (-((M + 1 : ℕ) : ℝ) * u))
                = (cardN * Cp * Mx_c ^ Dp * K_M1) * u ^ (A * Dp) * Real.exp (-((M + 1 : ℕ) : ℝ) * u) := by ring
              _ ≤ (cardN * Cp * Mx_c ^ Dp * K_M1) * u ^ A_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u) := by gcongr
          linarith
        -- Divide by `‖etaCoeff M‖ * exp (-M * u)`
        have htilde_Lm : ‖MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P)‖ ≤
            ((C2 * Mx_c ^ D * K_M ^ 2 + cardN * Cp * Mx_c ^ Dp * K_M1) / ‖etaCoeff M‖) *
              u ^ A_tot * Real.exp (-u) := by
          have hden_pos : 0 < ‖etaCoeff M‖ * Real.exp (-(M : ℝ) * u) := by positivity
          have hexp_s : Real.exp (-((M + 1 : ℕ) : ℝ) * u) = Real.exp (-(M : ℝ) * u) * Real.exp (-u) := by
            rw [← Real.exp_add]; congr 1; push_cast; ring
          have hdiv := (le_div_iff₀' hden_pos).mpr hprod_Lm
          refine hdiv.trans_eq ?_
          rw [hexp_s]
          field_simp [hcM_pos.ne', (Real.exp_pos (-(M : ℝ) * u)).ne']
        -- Transfer from `jetTilde` to `jetPlus` using Lipschitz bound on `Lm_op δ M P`
        let δ_tp : Fin d × Fin (r + 1) → ℂ := fun p => jetTilde δ r u p - jetPlus δ r u p
        have htp_eq : jetPlus δ r u + δ_tp = jetTilde δ r u := by ext p; simp [δ_tp]
        let M_tp : ℝ := C_lin * u ^ A * Real.exp (-u)
        have hMtp_le1 : M_tp ≤ 1 := by
          have h1 := hSm1 u hu_sm1
          have h2 : C_sm1 / u ^ 1 ≤ 1 := by rw [pow_one, div_le_one hu_pos]; linarith
          exact h1.trans h2
        have htp_bd : ∀ p, ‖δ_tp p‖ ≤ M_tp := fun p => by
          have h1 := (hJT p u hu_jt).1
          have hpow1 : u ^ A1 ≤ u ^ A := pow_le_pow_right₀ hu1 (le_max_right A0 A1)
          dsimp [δ_tp, M_tp]; exact h1.trans (by gcongr)
        have hlip := (hLbd (jetPlus δ r u) δ_tp Mx M_tp hMx1 (by dsimp [M_tp]; positivity) hMtp_le1 hxp_bd htp_bd).2.1
        rw [htp_eq] at hlip
        have hlip' : ‖MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P) -
              MvPolynomial.eval (jetPlus δ r u) (Lm_op δ M P)‖ ≤
            (C1_L * Mx_c ^ D_L * C_lin) * u ^ A_tot * Real.exp (-u) := by
          refine hlip.trans ?_
          dsimp only [Mx, M_tp]
          rw [mul_pow, ← pow_mul]
          have hpow : u ^ (A * D_L) * u ^ A ≤ u ^ A_tot := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hu1 (by dsimp [A_tot]; omega)
          calc C1_L * (Mx_c ^ D_L * u ^ (A * D_L)) * (C_lin * u ^ A * Real.exp (-u))
              = (C1_L * Mx_c ^ D_L * C_lin) * (u ^ (A * D_L) * u ^ A) * Real.exp (-u) := by ring
            _ ≤ (C1_L * Mx_c ^ D_L * C_lin) * u ^ A_tot * Real.exp (-u) := by gcongr
        have htri : ‖MvPolynomial.eval (jetPlus δ r u) (Lm_op δ M P)‖ ≤
            ‖MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P)‖ +
            ‖MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P) -
              MvPolynomial.eval (jetPlus δ r u) (Lm_op δ M P)‖ := by
          have := norm_sub_le (MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P))
            (MvPolynomial.eval (jetTilde δ r u) (Lm_op δ M P) - MvPolynomial.eval (jetPlus δ r u) (Lm_op δ M P))
          simpa only [sub_sub_cancel] using this
        dsimp only [K_tot]
        nlinarith [pow_pos hu_pos A_tot, Real.exp_pos (-u)]
      intro N
      obtain ⟨C', hC', U', _, hN⟩ := PakNthPrimeEngine.exists_bound_pow_mul_exp_neg K_tot hKtot_pos A_tot N
      refine ⟨C', hC', max U_cut U', fun u hu => ?_⟩
      exact (hexp_decay u ((le_max_left _ _).trans hu)).trans (hN u ((le_max_right _ _).trans hu))
    exact hmin (Lm_op δ M P) hLm_flat (Lm_op_totalDegree_lt δ M P hP_deg)

/-- If a univariate complex polynomial satisfies `Q(M) → 0` as `M : ℕ → ∞`, then `Q = 0`. -/
lemma poly_eq_zero_of_tendsto_nat_zero (Q : Polynomial ℂ)
    (hlim : Tendsto (fun M : ℕ => Q.eval (M : ℂ)) atTop (𝓝 0)) :
    Q = 0 := by
  by_contra hQ
  rcases Nat.eq_zero_or_pos Q.natDegree with hdeg0 | hdeg_pos
  · have hC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hconst : Tendsto (fun _ : ℕ => Q.coeff 0) atTop (𝓝 0) := by
      refine hlim.congr fun M => ?_
      conv_lhs => rw [hC]; simp
    have h0 : Q.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
    exact hQ (by rw [hC, h0, map_zero])
  · have hdeg_pos' : (0 : WithBot ℕ) < Q.degree := by
      rw [Polynomial.degree_eq_natDegree hQ]; exact_mod_cast hdeg_pos
    have hnat : Tendsto (fun M : ℕ => ‖(M : ℂ)‖) atTop atTop := by
      simpa only [Complex.norm_natCast] using tendsto_natCast_atTop_atTop
    have hnorm := Polynomial.tendsto_norm_atTop Q hdeg_pos' hnat
    have hnorm0 : Tendsto (fun M : ℕ => ‖Q.eval (M : ℂ)‖) atTop (𝓝 0) := by simpa using hlim.norm
    obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hnorm.eventually (Filter.eventually_ge_atTop 1))
    obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.mp
      (hnorm0.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)))
    have ha := hM₁ (max M₁ M₂) (le_max_left _ _)
    have hb := hM₂ (max M₁ M₂) (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hb
    linarith

/-- **Step 4 — Pairwise-Distinct Density Dominance Kill Shot (`distinctDensity_vanish_of_Lm_zero`)**:
If `δ : Fin d → ℝ` has strictly positive pairwise-distinct densities and `Lm_op δ M P = 0`
for all `M ≥ 2`, then EVERY coordinate derivative `pderiv (i, j) P` vanishes identically! -/
theorem distinctDensity_vanish_of_Lm_zero {d r : ℕ} {δ : Fin d → ℝ}
    (hδ_pos : ∀ i, 0 < δ i) (hδ_inj : Function.Injective δ)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ)
    (hLm : ∀ M : ℕ, 2 ≤ M → Lm_op δ M P = 0) :
    ∀ p : Fin d × Fin (r + 1), MvPolynomial.pderiv p P = 0 := by
  -- Evaluate at an arbitrary complex jet vector `x`
  have heval_zero : ∀ x : Fin d × Fin (r + 1) → ℂ, ∀ p : Fin d × Fin (r + 1),
      MvPolynomial.eval x (MvPolynomial.pderiv p P) = 0 := by
    intro x
    let Q : Fin d → Polynomial ℂ := fun i =>
      ∑ j : Fin (r + 1), Polynomial.C (MvPolynomial.eval x (MvPolynomial.pderiv (i, j) P)) * (-Polynomial.X) ^ j.val
    have hQ_eval : ∀ i (M : ℕ), (Q i).eval (M : ℂ) =
        ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv (i, j) P) * (-(M : ℂ)) ^ j.val := by
      intro i M
      change Polynomial.aeval (M : ℂ) (Q i) = _
      dsimp only [Q]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => by simp
    have hsum_univ : ∀ M : ℕ, 2 ≤ M → ∑ i ∈ (Finset.univ : Finset (Fin d)),
        ((δ i : ℂ) ^ M) * (Q i).eval (M : ℂ) = 0 := by
      intro M hM
      have h0 := congrArg (MvPolynomial.eval x) (hLm M hM)
      rw [map_zero, Lm_op_apply, map_sum] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQ_eval i M, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [PakNthPrimeEngine.eval_smul_eq]; ring
    -- Descend through subsets `S : Finset (Fin d)` by strong induction on `S.card`
    have hdesc : ∀ n : ℕ, ∀ S : Finset (Fin d), S.card = n →
        (∀ M : ℕ, 2 ≤ M → ∑ i ∈ S, ((δ i : ℂ) ^ M) * (Q i).eval (M : ℂ) = 0) →
        ∀ i ∈ S, Q i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro S hcard hS
        by_cases hne : S.Nonempty
        · obtain ⟨i₀, hi₀S, hmax⟩ := Finset.exists_max_image S δ hne
          have hδ0_pos : 0 < δ i₀ := hδ_pos i₀
          -- Each `i ∈ S.erase i₀` has `0 < δ i / δ i₀ < 1`, so `(δ i / δ i₀)^M * (Q i)(M) → 0`
          have hterm_lim : ∀ i ∈ S.erase i₀,
              Tendsto (fun M : ℕ => ((δ i / δ i₀ : ℝ) : ℂ) ^ M * (Q i).eval (M : ℂ)) atTop (𝓝 0) := by
            intro i hi
            have hiS : i ∈ S := Finset.mem_of_mem_erase hi
            have hine : i ≠ i₀ := (Finset.mem_erase.mp hi).1
            have hlt : δ i < δ i₀ := lt_of_le_of_ne (hmax i hiS) (fun heq => hine (hδ_inj heq))
            let ratio : ℝ := δ i / δ i₀
            have hr0 : 0 < ratio := div_pos (hδ_pos i) hδ0_pos
            have hr1 : ratio < 1 := (div_lt_one hδ0_pos).mpr hlt
            -- Bound `‖(Q i).eval (M : ℂ)‖ ≤ Cq * (M + 1)^D`
            let Dq : ℕ := (Q i).natDegree
            let Cq : ℝ := (∑ k ∈ Finset.range (Dq + 1), ‖(Q i).coeff k‖) + 1
            have hQ_bd : ∀ M : ℕ, ‖(Q i).eval (M : ℂ)‖ ≤ Cq * ((M : ℝ) + 1) ^ Dq := by
              intro M
              rw [Polynomial.eval_eq_sum_range]
              calc ‖∑ k ∈ Finset.range (Dq + 1), (Q i).coeff k * (M : ℂ) ^ k‖
                  ≤ ∑ k ∈ Finset.range (Dq + 1), ‖(Q i).coeff k‖ * ((M : ℝ) + 1) ^ Dq := by
                    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
                    rw [norm_mul, norm_pow, Complex.norm_natCast]
                    have hk_le : k ≤ Dq := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
                    have h1 : (M : ℝ) ^ k ≤ ((M : ℝ) + 1) ^ k :=
                      pow_le_pow_left₀ (Nat.cast_nonneg M) (by linarith) k
                    have h2 : ((M : ℝ) + 1) ^ k ≤ ((M : ℝ) + 1) ^ Dq :=
                      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) M]) hk_le
                    exact mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
                _ = (∑ k ∈ Finset.range (Dq + 1), ‖(Q i).coeff k‖) * ((M : ℝ) + 1) ^ Dq :=
                    (Finset.sum_mul _ _ _).symm
                _ ≤ Cq * ((M : ℝ) + 1) ^ Dq := by dsimp [Cq]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity) Dq]
            have hsum_geom : Summable (fun M : ℕ => ((M : ℝ) + 1) ^ Dq * ratio ^ M) := by
              have hs := summable_pow_mul_geometric_of_norm_lt_one Dq
                (show ‖ratio‖ < 1 by simpa [abs_of_pos hr0] using hr1)
              have h := (hs.comp_injective Nat.succ_injective).mul_right ratio⁻¹
              simpa [Function.comp_def, pow_succ, mul_assoc, hr0.ne'] using h
            have hlim_real : Tendsto (fun M : ℕ => Cq * (((M : ℝ) + 1) ^ Dq * ratio ^ M)) atTop (𝓝 0) := by
              simpa using hsum_geom.tendsto_atTop_zero.const_mul Cq
            refine squeeze_zero_norm' (a := fun M : ℕ => Cq * (((M : ℝ) + 1) ^ Dq * ratio ^ M)) ?_ hlim_real
            refine Filter.Eventually.of_forall fun M => ?_
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
            calc ratio ^ M * ‖(Q i).eval (M : ℂ)‖
                ≤ ratio ^ M * (Cq * ((M : ℝ) + 1) ^ Dq) := mul_le_mul_of_nonneg_left (hQ_bd M) (by positivity)
              _ = Cq * (((M : ℝ) + 1) ^ Dq * ratio ^ M) := by ring
          have hsum_lim : Tendsto (fun M : ℕ =>
              -∑ i ∈ S.erase i₀, ((δ i / δ i₀ : ℝ) : ℂ) ^ M * (Q i).eval (M : ℂ)) atTop (𝓝 0) := by
            have haux : ∀ T : Finset (Fin d),
                (∀ i ∈ T, Tendsto (fun M : ℕ => ((δ i / δ i₀ : ℝ) : ℂ) ^ M * (Q i).eval (M : ℂ)) atTop (𝓝 0)) →
                Tendsto (fun M : ℕ => ∑ i ∈ T, ((δ i / δ i₀ : ℝ) : ℂ) ^ M * (Q i).eval (M : ℂ)) atTop (𝓝 0) := by
              intro T
              classical
              induction T using Finset.induction_on with
              | empty => intro _; simp
              | insert a T ha ihT =>
                intro h
                have h1 := h a (Finset.mem_insert_self a T)
                have h2 := ihT fun b hb => h b (Finset.mem_insert_of_mem hb)
                simpa [Finset.sum_insert ha] using h1.add h2
            simpa using (haux (S.erase i₀) hterm_lim).neg
          have hQi0_lim : Tendsto (fun M : ℕ => (Q i₀).eval (M : ℂ)) atTop (𝓝 0) := by
            refine hsum_lim.congr' ?_
            filter_upwards [Filter.eventually_ge_atTop 2] with M hM
            have hsplit := hS M hM
            rw [← Finset.add_sum_erase _ _ hi₀S] at hsplit
            have hδ0M : ((δ i₀ : ℂ) ^ M) ≠ 0 := pow_ne_zero M (Complex.ofReal_ne_zero.mpr hδ0_pos.ne')
            have hmul : ((δ i₀ : ℂ) ^ M) * (-∑ i ∈ S.erase i₀, ((δ i / δ i₀ : ℝ) : ℂ) ^ M * (Q i).eval (M : ℂ)) =
                ((δ i₀ : ℂ) ^ M) * (Q i₀).eval (M : ℂ) := by
              have hrhs : ((δ i₀ : ℂ) ^ M) * (∑ i ∈ S.erase i₀, ((δ i / δ i₀ : ℝ) : ℂ) ^ M * (Q i).eval (M : ℂ)) =
                  ∑ i ∈ S.erase i₀, ((δ i : ℂ) ^ M) * (Q i).eval (M : ℂ) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Complex.ofReal_div, div_pow]
                field_simp [hδ0M]
              linear_combination -(hrhs.trans (eq_neg_of_add_eq_zero_right hsplit))
            exact mul_left_cancel₀ hδ0M hmul
          have hQi0_zero : Q i₀ = 0 := poly_eq_zero_of_tendsto_nat_zero (Q i₀) hQi0_lim
          have hS_erase : ∀ M : ℕ, 2 ≤ M → ∑ i ∈ S.erase i₀, ((δ i : ℂ) ^ M) * (Q i).eval (M : ℂ) = 0 := by
            intro M hM
            have h1 := hS M hM
            rw [← Finset.add_sum_erase _ _ hi₀S, hQi0_zero, Polynomial.eval_zero, mul_zero, zero_add] at h1
            exact h1
          have hcard_lt : (S.erase i₀).card < n := by
            rw [← hcard]; exact Finset.card_erase_lt_of_mem hi₀S
          have herase_zero := ih (S.erase i₀).card hcard_lt (S.erase i₀) rfl hS_erase
          intro i hi
          by_cases hii0 : i = i₀
          · exact hii0 ▸ hQi0_zero
          · exact herase_zero i (Finset.mem_erase.mpr ⟨hii0, hi⟩)
        · intro i hi; exact absurd ⟨i, hi⟩ hne
    have hQ_all : ∀ i : Fin d, Q i = 0 := fun i => hdesc (Finset.univ.card) Finset.univ rfl hsum_univ i (Finset.mem_univ i)
    intro p
    have hcoeff0 : (Q p.1).coeff p.2.val = 0 := by rw [hQ_all p.1, Polynomial.coeff_zero]
    have hcoeff_eq : (Q p.1).coeff p.2.val =
        MvPolynomial.eval x (MvPolynomial.pderiv p P) * (-1 : ℂ) ^ p.2.val := by
      change Polynomial.lcoeff ℂ p.2.val (Q p.1) = _
      dsimp only [Q]
      rw [map_sum, Finset.sum_eq_single p.2]
      · have hnegX : (-Polynomial.X : Polynomial ℂ) ^ p.2.val = Polynomial.C ((-1 : ℂ) ^ p.2.val) * Polynomial.X ^ p.2.val := by
          rw [neg_eq_neg_one_mul, mul_pow, map_pow, map_neg, map_one]
        rw [hnegX, ← mul_assoc, ← map_mul, Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
        simp
      · intro j _ hjp
        have hnegX : (-Polynomial.X : Polynomial ℂ) ^ j.val = Polynomial.C ((-1 : ℂ) ^ j.val) * Polynomial.X ^ j.val := by
          rw [neg_eq_neg_one_mul, mul_pow, map_pow, map_neg, map_one]
        have hne : j.val ≠ p.2.val := fun heq => hjp (Fin.ext heq)
        rw [hnegX, ← mul_assoc, ← map_mul, Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
        simp [hne.symm]
      · intro hnot; exact absurd (Finset.mem_univ p.2) hnot
    rw [hcoeff_eq] at hcoeff0
    exact (mul_eq_zero.mp hcoeff0).resolve_right (pow_ne_zero p.2.val (by norm_num))
  intro p
  exact MvPolynomial.funext fun x => by simpa using heval_zero x p

/-- **Master Section 2 Theorem (`distinctDensity_ideal_eq_zero`)**:
For any finite family of pairwise-distinct positive densities `δ : Fin d → ℝ`, the flat-evaluation
ideal `InFlatIdeal δ` on `MvPolynomial (Fin d × Fin (r + 1)) ℂ` is **IDENTICALLY ZERO**! -/
theorem distinctDensity_ideal_eq_zero {d r : ℕ} {δ : Fin d → ℝ}
    (hδ_pos : ∀ i, 0 < δ i) (hδ_inj : Function.Injective δ)
    (P : MvPolynomial (Fin d × Fin (r + 1)) ℂ) (hP : InFlatIdeal δ P) :
    P = 0 := by
  by_contra hne
  -- Choose a nonzero element `P₀ ∈ InFlatIdeal δ` of minimal total degree
  have hex : ∃ n : ℕ, ∃ Q : MvPolynomial (Fin d × Fin (r + 1)) ℂ,
      Q.totalDegree = n ∧ Q ≠ 0 ∧ InFlatIdeal δ Q := ⟨P.totalDegree, P, rfl, hne, hP⟩
  classical
  obtain ⟨P₀, hdeg_eq, hP₀_ne, hP₀_flat⟩ := Nat.find_spec hex
  have hmin : ∀ Q : MvPolynomial (Fin d × Fin (r + 1)) ℂ,
      InFlatIdeal δ Q → Q.totalDegree < P₀.totalDegree → Q = 0 := by
    intro Q hQ hlt
    by_contra hQne
    exact Nat.find_min hex (hdeg_eq ▸ hlt) ⟨Q, rfl, hQne, hQ⟩
  -- `P₀` cannot be a nonzero constant
  have hdeg_pos : 0 < P₀.totalDegree := by
    by_contra hle
    have hdeg0 : P₀.totalDegree = 0 := Nat.eq_zero_of_le_zero (not_lt.mp hle)
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
    have h0 := (mixed_flat_implies_exact_vanishing δ P₀ hP₀_flat 0).1
    rw [hC, MvPolynomial.eval_C] at h0
    exact hP₀_ne (by rw [hC, h0, map_zero])
  -- By strong induction, `Lm_op δ M P₀ = 0` for all `M ≥ 2`, so every coordinate derivative vanishes
  have hLm := strong_induction_Lm_multi_eq_zero hδ_pos P₀ hP₀_flat hdeg_pos hmin
  have hpd := distinctDensity_vanish_of_Lm_zero hδ_pos hδ_inj P₀ hLm
  -- Yet `P₀.totalDegree > 0` forces `P₀.vars.Nonempty`, so some coordinate derivative is nonzero!
  have hvars_ne : P₀.vars.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hempty
    rw [hC, MvPolynomial.totalDegree_C] at hdeg_pos
    exact lt_irrefl 0 hdeg_pos
  obtain ⟨p, hp⟩ := hvars_ne
  obtain ⟨m, hm, hmp⟩ := (MvPolynomial.mem_vars_iff_mem_support p).mp hp
  have hm_supp := Finsupp.mem_support_iff.mp hmp
  let m' : (Fin d × Fin (r + 1)) →₀ ℕ := m - Finsupp.single p 1
  have hcoeff := congrArg (fun f : MvPolynomial (Fin d × Fin (r + 1)) ℂ => f.coeff m') (hpd p)
  rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hm_supp] at hcoeff
  change P₀.coeff m * ((m' p : ℂ) + 1) = 0 at hcoeff
  have hnz : ((m' p : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' p)
  exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hm) hnz hcoeff

lemma aeval_pi_apply {ι : Type*} (f : ι → ℝ → ℂ) (P : MvPolynomial ι ℂ) (u : ℝ) :
    MvPolynomial.aeval f P u = MvPolynomial.eval (fun i => f i u) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- **UNCONDITIONAL MASTER ANALYTIC THEOREM (`distinctDensity_branches_algebraicIndependent`)**:
For any finite family of pairwise-distinct positive densities `δ : Fin d → ℝ`, the translated
physical upper branches `{u ↦ I_plus (u - Real.log (δ i))}_{i : Fin d}` are **jointly
differentially algebraically independent over `ℂ`** (zero external hypotheses!). -/
theorem distinctDensity_branches_algebraicIndependent {d : ℕ} (δ : Fin d → ℝ)
    (hδ_pos : ∀ i, 0 < δ i) (hδ_inj : Function.Injective δ) :
    AlgebraicIndependent ℂ
      (fun p : Fin d × ℕ => fun u : ℝ => iteratedDeriv p.2 (J_plus δ p.1) u) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  let r : ℕ := P.vars.sup Prod.snd
  let emb : Fin d × Fin (r + 1) → Fin d × ℕ := fun p => (p.1, p.2.val)
  have hemb_inj : Function.Injective emb := fun p₁ p₂ h => by
    have h1 := congr_arg Prod.fst h
    have h2 := congr_arg Prod.snd h
    exact Prod.ext h1 (Fin.ext h2)
  have hsub : ↑P.vars ⊆ Set.range emb := by
    intro q hq
    have hq_le : q.2 ≤ r := Finset.le_sup (f := Prod.snd) (Finset.mem_coe.mp hq)
    exact ⟨(q.1, ⟨q.2, Nat.lt_succ_of_le hq_le⟩), rfl⟩
  obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P emb hemb_inj hsub
  have hQ_flat : InFlatIdeal δ Q := by
    have hQ_zero : ∀ u : ℝ, MvPolynomial.eval (jetPlus δ r u) Q = 0 := by
      intro u
      have h1 := congrFun hP u
      rw [aeval_pi_apply] at h1
      rw [← hQ, MvPolynomial.eval_rename] at h1
      exact h1
    intro N
    refine ⟨1, zero_lt_one, 1, fun u hu => ?_⟩
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
    rw [hQ_zero u, norm_zero]; positivity
  have hQ0 : Q = 0 := distinctDensity_ideal_eq_zero hδ_pos hδ_inj Q hQ_flat
  rw [← hQ, hQ0, map_zero]

/-! ### Section 3. Counting Transfer & Pullback to Ordinary Generating Functions -/

/-! #### 3a. Density Counting Function, `HasDensityPNT`, and `HasScaledDensityAsymp` -/

/-- Exact counting function `#{k : ℕ | a k ≤ N}` for a strictly increasing sequence `a : ℕ → ℕ`. -/
@[expose] def seqCounting (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun k => a k ≤ N)).card

lemma seqCounting_strictMono {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) :
    seqCounting a (a n) = n + 1 := by
  dsimp only [seqCounting]
  have hfilt : (Finset.range (a n + 1)).filter (fun k => a k ≤ a n) = Finset.range (n + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hk
      exact Nat.lt_succ_of_le (ha.le_iff_le.mp hk.2)
    · intro hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
      have hka : k ≤ a k := ha.id_le k
      have hak : a k ≤ a n := ha.monotone hkn
      exact ⟨by omega, hak⟩
  rw [hfilt, Finset.card_range]

/-- All-orders PNT counting hypothesis for a strictly increasing sequence `a : ℕ → ℕ`
of asymptotic density `δ > 0` relative to `li(x)`. -/
@[expose] def HasDensityPNT (a : ℕ → ℕ) (δ : ℝ) : Prop :=
  StrictMono a ∧ 0 < δ ∧
    ∀ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |(seqCounting a ⌊x⌋₊ : ℝ) - δ * Main.li x| ≤ C * x / (Real.log x) ^ M

/-- Ordinary generating function `F_a(q) = ∑_{n ≥ 0} a_n q^{n+1}` (1-indexed, matching `NthPrime.series`). -/
@[expose] def seqSeries (a : ℕ → ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    match n with
    | 0 => 0
    | k + 1 => (a k : ℂ)

lemma seqSeries_coeff_zero (a : ℕ → ℕ) : PowerSeries.coeff 0 (seqSeries a) = 0 := by
  simp [seqSeries]

lemma seqSeries_coeff_succ (a : ℕ → ℕ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (seqSeries a) = (a k : ℂ) := by
  simp [seqSeries]

/-- Smoothed Abel ray `S_a(u) = e^{-2u} F_a(e^{-e^{-u}})`. -/
@[expose] def seqSmoothRay (a : ℕ → ℕ) (u : ℝ) : ℂ :=
  PrimeNome.tRay u ^ 2 * PrimeNome.value (seqSeries a) (PrimeNome.qRay u)

/-- Rescaled asymptotic jet match hypothesis `S_a(u) ~ δ⁻¹ I_plus(u - log δ)` to all inverse powers. -/
@[expose] def HasScaledDensityAsymp (a : ℕ → ℕ) (δ : ℝ) : Prop :=
  0 < δ ∧ PrimeNome.PolyCoeffBound (seqSeries a) ∧
    ∀ j N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖iteratedDeriv j (seqSmoothRay a) u - (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ)‖ ≤
        C / u ^ N

/-- Elementary lower bound `(x / 2) / log x ≤ Main.li x` for `4 ≤ x`. -/
lemma li_ge_half_div_log {x : ℝ} (hx : 4 ≤ x) :
    (x / 2) / Real.log x ≤ Main.li x := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hint_li : IntervalIntegrable (fun v : ℝ => (Real.log v)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro v hv
    exact ((Real.continuousAt_log (by linarith [hv.1])).inv₀
      (Real.log_pos (by linarith [hv.1])).ne').continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (2 : ℝ) ≤ x)
    (intervalIntegrable_const (c := (Real.log x)⁻¹)) hint_li fun v hv =>
      inv_anti₀ (Real.log_pos (by linarith [hv.1]))
        (Real.log_le_log (by linarith [hv.1]) hv.2)
  rw [intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_inv] at hmono
  have hhalf : (x / 2) / Real.log x ≤ (x - 2) / Real.log x :=
    div_le_div_of_nonneg_right (by linarith) hlogx.le
  exact hhalf.trans hmono

/-- Elementary spacing inequality for `Main.li` on `[2, B]`. -/
lemma li_inverse_spacing_dd {a b B : ℝ} (ha : a ∈ Set.Icc (2 : ℝ) B) (hb : b ∈ Set.Icc (2 : ℝ) B) :
    |a - b| ≤ Real.log B * |Main.li a - Main.li b| := by
  have hli_int : ∀ {u v : ℝ}, 2 ≤ u → u ≤ v → IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume u v := by
    intro u v hu huv
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    intro t ht
    exact ((Real.continuousAt_log (by linarith [ht.1])).inv₀
      (Real.log_pos (by linarith [ht.1])).ne').continuousWithinAt
  have hstep : ∀ {u v : ℝ}, 2 ≤ u → u ≤ v → v ≤ B → v - u ≤ Real.log B * (Main.li v - Main.li u) := by
    intro u v hu huv hvB
    have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hli_int le_rfl hu) (hli_int hu huv)
    change Main.li u + _ = Main.li v at hadd
    have hi := intervalIntegral.integral_mono_on (μ := volume) huv
      (intervalIntegrable_const (c := (Real.log B)⁻¹)) (hli_int hu huv)
      fun t ht => inv_anti₀ (Real.log_pos (by linarith [ht.1]))
        (Real.log_le_log (by linarith [ht.1]) (ht.2.trans hvB))
    rw [intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_inv] at hi
    have := (div_le_iff₀ hlogB).mp hi
    nlinarith [hadd]
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by linarith [ha.1, ha.2])
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    have hh : Main.li b - Main.li a ≤ |Main.li a - Main.li b| := by
      simpa only [neg_sub] using neg_le_abs (Main.li a - Main.li b)
    exact (hstep ha.1 hab hb.2).trans (mul_le_mul_of_nonneg_left hh hlog)
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact (hstep hb.1 hba ha.2).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hlog)

/-- From `HasDensityPNT a δ`, derive global quadratic growth of `a n` and `IndexLogError`
relative to `n ↦ NthPrime.inverseLi ((n + 1) / δ)`. -/
lemma hasDensityPNT_bounds_and_indexLogError {a : ℕ → ℕ} {δ : ℝ} (hd : HasDensityPNT a δ) :
    (∃ A_q > 0, ∀ n : ℕ, |(a n : ℝ)| ≤ A_q * ((n : ℝ) + 2) ^ 2) ∧
    NthPrime.IndexLogError (fun n : ℕ => (a n : ℝ) - NthPrime.inverseLi (((n : ℝ) + 1) / δ)) := by
  rcases hd with ⟨ha_mono, hδ_pos, hpnt⟩
  have ha_tend : Tendsto (fun n : ℕ => (a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ha_mono.tendsto_atTop
  -- Step 1: From `M = 2`, deduce `(a n) / log (a n) ≤ (4 / δ) * (n + 1)` eventually
  obtain ⟨C₂, hC₂, hM2⟩ := hpnt 2
  have hquot_ev : ∀ᶠ n : ℕ in atTop,
      4 ≤ (a n : ℝ) ∧ (a n : ℝ) / Real.log (a n : ℝ) ≤ (4 / δ) * ((n : ℝ) + 1) := by
    have hlog_big : ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ 4 * C₂ / δ ≤ Real.log x := by
      filter_upwards [eventually_ge_atTop (4 : ℝ),
        Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 * C₂ / δ))] with x hx1 hx2
      exact ⟨hx1, hx2⟩
    filter_upwards [ha_tend.eventually (hM2.and hlog_big)] with n ⟨herr, hx4, hlog_ge⟩
    have hlog_pos : 0 < Real.log (a n : ℝ) := Real.log_pos (by linarith)
    have hcnt : (seqCounting a ⌊(a n : ℝ)⌋₊ : ℝ) = (n : ℝ) + 1 := by
      rw [Nat.floor_natCast, seqCounting_strictMono ha_mono n]; push_cast; rfl
    rw [hcnt] at herr
    have hli := li_ge_half_div_log hx4
    have hsub := (abs_le.mp herr).1
    have hC2_le : C₂ * (a n : ℝ) / (Real.log (a n : ℝ)) ^ 2 ≤ (δ / 4) * ((a n : ℝ) / Real.log (a n : ℝ)) := by
      have h1 : C₂ / Real.log (a n : ℝ) ≤ δ / 4 := by
        rw [div_le_iff₀ hlog_pos]
        have h2 := (div_le_iff₀ hδ_pos).mp hlog_ge
        linarith
      calc C₂ * (a n : ℝ) / (Real.log (a n : ℝ)) ^ 2
          = (C₂ / Real.log (a n : ℝ)) * ((a n : ℝ) / Real.log (a n : ℝ)) := by rw [sq]; ring
        _ ≤ (δ / 4) * ((a n : ℝ) / Real.log (a n : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
    have hlow : (δ / 4) * ((a n : ℝ) / Real.log (a n : ℝ)) ≤ (n : ℝ) + 1 := by
      have hli_mul : (δ / 2) * ((a n : ℝ) / Real.log (a n : ℝ)) ≤ δ * Main.li (a n : ℝ) := by
        calc (δ / 2) * ((a n : ℝ) / Real.log (a n : ℝ))
            = δ * (((a n : ℝ) / 2) / Real.log (a n : ℝ)) := by ring
          _ ≤ δ * Main.li (a n : ℝ) := mul_le_mul_of_nonneg_left hli hδ_pos.le
      linarith
    refine ⟨hx4, ?_⟩
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ_pos]
    linarith
  -- Step 2: Deduce global quadratic growth `|(a n : ℝ)| ≤ A_q * (n + 2)^2`
  have hquad_ev : ∀ᶠ n : ℕ in atTop, (a n : ℝ) ≤ (8 / δ) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    filter_upwards [hquot_ev] with n ⟨hx4, hq⟩
    have han_pos : 0 < (a n : ℝ) := by linarith
    have hlog_le : Real.log (a n : ℝ) ≤ 2 * Real.sqrt (a n : ℝ) := by
      have hsq : (a n : ℝ) = Real.sqrt (a n : ℝ) ^ 2 := (Real.sq_sqrt han_pos.le).symm
      have hsqrt_pos : 0 < Real.sqrt (a n : ℝ) := Real.sqrt_pos.mpr han_pos
      calc Real.log (a n : ℝ) = Real.log (Real.sqrt (a n : ℝ) ^ 2) := by rw [← hsq]
        _ = 2 * Real.log (Real.sqrt (a n : ℝ)) := by rw [Real.log_pow]; norm_num
        _ ≤ 2 * Real.sqrt (a n : ℝ) := by linarith [Real.log_le_sub_one_of_pos hsqrt_pos]
    have hlog_pos : 0 < Real.log (a n : ℝ) := Real.log_pos (by linarith)
    have hsqrt_le : Real.sqrt (a n : ℝ) ≤ (8 / δ) * ((n : ℝ) + 1) := by
      have h1 : (a n : ℝ) ≤ (4 / δ) * ((n : ℝ) + 1) * Real.log (a n : ℝ) := (div_le_iff₀ hlog_pos).mp hq
      have h2 : (a n : ℝ) ≤ (4 / δ) * ((n : ℝ) + 1) * (2 * Real.sqrt (a n : ℝ)) :=
        h1.trans (mul_le_mul_of_nonneg_left hlog_le (by positivity))
      have hsq : Real.sqrt (a n : ℝ) * Real.sqrt (a n : ℝ) = (a n : ℝ) := Real.mul_self_sqrt han_pos.le
      have hsqrt_pos : 0 < Real.sqrt (a n : ℝ) := Real.sqrt_pos.mpr han_pos
      have h3 : Real.sqrt (a n : ℝ) * Real.sqrt (a n : ℝ) ≤ (8 / δ * ((n : ℝ) + 1)) * Real.sqrt (a n : ℝ) := by
        calc Real.sqrt (a n : ℝ) * Real.sqrt (a n : ℝ) = (a n : ℝ) := hsq
          _ ≤ (4 / δ) * ((n : ℝ) + 1) * (2 * Real.sqrt (a n : ℝ)) := h2
          _ = (8 / δ * ((n : ℝ) + 1)) * Real.sqrt (a n : ℝ) := by ring
      exact le_of_mul_le_mul_right h3 hsqrt_pos
    calc (a n : ℝ) = Real.sqrt (a n : ℝ) ^ 2 := (Real.sq_sqrt han_pos.le).symm
      _ ≤ ((8 / δ) * ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
      _ = (8 / δ) ^ 2 * ((n : ℝ) + 1) ^ 2 := mul_pow _ _ 2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hquad_ev
  let A_q : ℝ := max ((8 / δ) ^ 2) ((∑ k ∈ Finset.range N₀, (a k : ℝ)) + 1)
  have hAq_pos : 0 < A_q := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hquad_all : ∀ n : ℕ, |(a n : ℝ)| ≤ A_q * ((n : ℝ) + 2) ^ 2 := by
    intro n
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    by_cases hn : N₀ ≤ n
    · have h1 := hN₀ n hn
      have h2 : (8 / δ) ^ 2 ≤ A_q := le_max_left _ _
      have h3 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      calc (a n : ℝ) ≤ (8 / δ) ^ 2 * ((n : ℝ) + 1) ^ 2 := h1
        _ ≤ A_q * ((n : ℝ) + 2) ^ 2 := mul_le_mul h2 h3 (by positivity) hAq_pos.le
    · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
      have h1 : (a n : ℝ) ≤ ∑ k ∈ Finset.range N₀, (a k : ℝ) :=
        Finset.single_le_sum (fun k _ => Nat.cast_nonneg (a k)) hmem
      have h2 : (∑ k ∈ Finset.range N₀, (a k : ℝ)) + 1 ≤ A_q := le_max_right _ _
      have h3 : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      nlinarith
  refine ⟨⟨A_q, hAq_pos, hquad_all⟩, ?_⟩
  -- Step 3: Prove `IndexLogError (fun n => a n - inverseLi ((n + 1) / δ))`
  intro M
  obtain ⟨C, hC, herrM⟩ := hpnt (M + 2)
  let K_B : ℝ := max ((4 * (1 / δ + 1)) ^ 2) A_q
  let C_fin : ℝ := (4 * Real.log (K_B + 2) + 8) * ((C / δ) * (4 / δ) * (2 : ℝ) ^ (M + 1))
  refine ⟨C_fin, by
    have : 0 < Real.log (K_B + 2) := Real.log_pos (by
      have : 0 ≤ K_B := le_trans (by positivity) (le_max_left _ _)
      linarith)
    dsimp [C_fin]; positivity, ?_⟩
  filter_upwards [ha_tend.eventually herrM, hquot_ev, eventually_ge_atTop 3] with n he ⟨hx4, hq⟩ hn3
  have hn1_ge4 : (4 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (show 4 ≤ n + 1 by omega)
  have hlog_n1_pos : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  have hlog_an_pos : 0 < Real.log (a n : ℝ) := Real.log_pos (by linarith)
  have hcnt : (seqCounting a ⌊(a n : ℝ)⌋₊ : ℝ) = (n : ℝ) + 1 := by
    rw [Nat.floor_natCast, seqCounting_strictMono ha_mono n]; push_cast; rfl
  rw [hcnt] at he
  -- Compare `log (n + 1)` with `2 * log (a n)` (using `n ≤ a n` and `n + 1 ≤ n^2` for `n ≥ 3`)
  have hlog_cmp : Real.log ((n : ℝ) + 1) / 2 ≤ Real.log (a n : ℝ) := by
    have hna : (n : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha_mono.id_le n
    have hsq : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
      have hn3' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      nlinarith
    have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log ((a n : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) (hsq.trans (pow_le_pow_left₀ (by positivity) hna 2))
    rw [Real.log_pow] at h1; norm_num at h1; linarith
  -- Bound `|Main.li (a n) - (n + 1) / δ|`
  have hli_err : |Main.li (a n : ℝ) - ((n : ℝ) + 1) / δ| ≤
      ((C / δ) * (4 / δ) * (2 : ℝ) ^ (M + 1)) * ((n : ℝ) + 1) / (Real.log ((n : ℝ) + 1)) ^ (M + 1) := by
    have hdiv_δ : |Main.li (a n : ℝ) - ((n : ℝ) + 1) / δ| =
        |((n : ℝ) + 1) - δ * Main.li (a n : ℝ)| / δ := by
      calc |Main.li (a n : ℝ) - ((n : ℝ) + 1) / δ|
          = |(((n : ℝ) + 1) - δ * Main.li (a n : ℝ)) / δ| := by
              rw [abs_sub_comm]; congr 1; field_simp [hδ_pos.ne']
        _ = |((n : ℝ) + 1) - δ * Main.li (a n : ℝ)| / δ := by
              rw [abs_div, abs_of_pos hδ_pos]
    rw [hdiv_δ]
    have hpow_log : (Real.log ((n : ℝ) + 1) / 2) ^ (M + 1) ≤ (Real.log (a n : ℝ)) ^ (M + 1) :=
      pow_le_pow_left₀ (by positivity) hlog_cmp (M + 1)
    calc |((n : ℝ) + 1) - δ * Main.li (a n : ℝ)| / δ
        ≤ (C * (a n : ℝ) / (Real.log (a n : ℝ)) ^ (M + 2)) / δ :=
          div_le_div_of_nonneg_right he hδ_pos.le
      _ = (C / δ) * ((a n : ℝ) / Real.log (a n : ℝ)) / (Real.log (a n : ℝ)) ^ (M + 1) := by
          rw [pow_succ]; field_simp [hδ_pos.ne', hlog_an_pos.ne']
      _ ≤ (C / δ) * ((4 / δ) * ((n : ℝ) + 1)) / (Real.log ((n : ℝ) + 1) / 2) ^ (M + 1) := by gcongr
      _ = ((C / δ) * (4 / δ) * (2 : ℝ) ^ (M + 1)) * ((n : ℝ) + 1) / (Real.log ((n : ℝ) + 1)) ^ (M + 1) := by
          rw [div_pow]; field_simp [(pow_pos hlog_n1_pos (M + 1)).ne']
  -- Common upper bound `B = (K_B + 2) * (n + 2)^2` containing both `a n` and `inverseLi ((n + 1) / δ)`
  let v : ℝ := ((n : ℝ) + 1) / δ
  have hv_nn : 0 ≤ v := by dsimp [v]; positivity
  have hspec := NthPrime.inverseLi_spec hv_nn
  let B : ℝ := (K_B + 2) * ((n : ℝ) + 2) ^ 2
  have hKB_nn : 0 ≤ K_B := le_trans (by positivity) (le_max_left _ _)
  have han_B : (a n : ℝ) ∈ Set.Icc (2 : ℝ) B := by
    refine ⟨by linarith, ?_⟩
    have h1 := hquad_all n
    rw [abs_of_nonneg (Nat.cast_nonneg _)] at h1
    have h2 : A_q ≤ K_B + 2 := by linarith [le_max_right ((4 * (1 / δ + 1)) ^ 2) A_q]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
  have hinv_B : NthPrime.inverseLi v ∈ Set.Icc (2 : ℝ) B := by
    refine ⟨hspec.1.1, hspec.1.2.trans ?_⟩
    have h1 : 4 * (v + 1) ≤ (4 * (1 / δ + 1)) * ((n : ℝ) + 2) := by
      dsimp only [v]
      have hge1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
      have hle : ((n : ℝ) + 1) / δ + 1 ≤ (1 / δ + 1) * ((n : ℝ) + 2) := by
        rw [one_div, add_mul, inv_mul_eq_div]
        have h1' : ((n : ℝ) + 1) / δ ≤ ((n : ℝ) + 2) / δ := div_le_div_of_nonneg_right (by linarith) hδ_pos.le
        linarith
      linarith
    have h2 : (4 * (v + 1)) ^ 2 ≤ (4 * (1 / δ + 1)) ^ 2 * ((n : ℝ) + 2) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (4 * (1 / δ + 1)) ^ 2 ≤ K_B + 2 := by
      linarith [le_max_left ((4 * (1 / δ + 1)) ^ 2) A_q]
    exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  have hlogK_nn : 0 ≤ Real.log (K_B + 2) := Real.log_nonneg (by linarith)
  have hlogB_le : Real.log B ≤ (4 * Real.log (K_B + 2) + 8) * Real.log ((n : ℝ) + 1) := by
    have hlog_ge1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
      have : Real.exp 1 ≤ (n : ℝ) + 1 := by linarith [Real.exp_one_lt_d9]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (Real.exp_pos 1) this
    have hn2_sq : (n : ℝ) + 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have hlog_n2 : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 1) := by
      calc Real.log ((n : ℝ) + 2) ≤ Real.log (((n : ℝ) + 1) ^ 2) := Real.log_le_log (by positivity) hn2_sq
        _ = 2 * Real.log ((n : ℝ) + 1) := by rw [Real.log_pow]; norm_num
    dsimp only [B]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
    nlinarith
  have hsp := li_inverse_spacing_dd han_B hinv_B
  rw [hspec.2] at hsp
  calc |(a n : ℝ) - NthPrime.inverseLi v|
      ≤ Real.log B * |Main.li (a n : ℝ) - v| := hsp
    _ ≤ ((4 * Real.log (K_B + 2) + 8) * Real.log ((n : ℝ) + 1)) *
          (((C / δ) * (4 / δ) * (2 : ℝ) ^ (M + 1)) * ((n : ℝ) + 1) / (Real.log ((n : ℝ) + 1)) ^ (M + 1)) :=
        mul_le_mul hlogB_le hli_err (abs_nonneg _) (by positivity)
    _ = C_fin * ((n : ℝ) + 1) / (Real.log ((n : ℝ) + 1)) ^ M := by
        dsimp only [C_fin]; rw [pow_succ]; field_simp [hlog_n1_pos.ne']; ring

/-- Scaled discrete `inverseLi` sequence `n ↦ inverseLi ((n + 1) / δ)` and its Abel sum. -/
@[expose] def scaledInvLiSeq (δ : ℝ) (n : ℕ) : ℝ :=
  NthPrime.inverseLi (((n : ℝ) + 1) / δ)

@[expose] def S_invLi_scaled (δ : ℝ) (u : ℝ) : ℝ :=
  ∑' n : ℕ, NthPrime.abelPolyTerm (scaledInvLiSeq δ) 1 n u

lemma abs_scaledInvLiSeq_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ A_s > 0, ∀ n : ℕ, |scaledInvLiSeq δ n| ≤ A_s * ((n : ℝ) + 2) ^ 2 := by
  let A_s : ℝ := (4 * (1 / δ + 1)) ^ 2
  refine ⟨A_s, by dsimp [A_s]; positivity, fun n => ?_⟩
  have hspec := (NthPrime.inverseLi_spec (show (0 : ℝ) ≤ ((n : ℝ) + 1) / δ by positivity)).1
  dsimp only [scaledInvLiSeq]
  rw [abs_of_nonneg (by linarith [hspec.1])]
  refine hspec.2.trans ?_
  have h1 : 4 * (((n : ℝ) + 1) / δ + 1) ≤ 4 * (1 / δ + 1) * ((n : ℝ) + 2) := by
    have hle : ((n : ℝ) + 1) / δ + 1 ≤ (1 / δ + 1) * ((n : ℝ) + 2) := by
      rw [one_div, add_mul, inv_mul_eq_div]
      have h1' : ((n : ℝ) + 1) / δ ≤ ((n : ℝ) + 2) / δ := div_le_div_of_nonneg_right (by linarith) hδ.le
      linarith
    linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  dsimp only [A_s]
  exact h2.trans (by rw [mul_pow])

lemma iteratedDeriv_S_invLi_scaled {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    iteratedDeriv k (S_invLi_scaled δ) =
      fun u => ∑' n, NthPrime.abelPolyTerm (scaledInvLiSeq δ) (NthPrime.abelJetStep^[k] 1) n u := by
  obtain ⟨A_s, hAs, hbd⟩ := abs_scaledInvLiSeq_le hδ
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun u => (hasDerivAt_abelPolySum_quad hAs hbd _ u).deriv

lemma contDiff_S_invLi_scaled {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ContDiff ℝ n (S_invLi_scaled δ) := by
  obtain ⟨A_s, hAs, hbd⟩ := abs_scaledInvLiSeq_le hδ
  have hgen : ∀ (m : ℕ) (P : Polynomial ℝ),
      ContDiff ℝ m (fun u => ∑' k, NthPrime.abelPolyTerm (scaledInvLiSeq δ) P k u) := by
    intro m
    induction m with
    | zero =>
      intro P
      rw [Nat.cast_zero, contDiff_zero]
      exact Differentiable.continuous fun u => (hasDerivAt_abelPolySum_quad hAs hbd P u).differentiableAt
    | succ m ih =>
      intro P
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun u => (hasDerivAt_abelPolySum_quad hAs hbd P u).differentiableAt, by simp, ?_⟩
      have hd : deriv (fun u => ∑' k, NthPrime.abelPolyTerm (scaledInvLiSeq δ) P k u) =
          fun u => ∑' k, NthPrime.abelPolyTerm (scaledInvLiSeq δ) (NthPrime.abelJetStep P) k u :=
        funext fun u => (hasDerivAt_abelPolySum_quad hAs hbd P u).deriv
      rw [hd]
      exact ih (NthPrime.abelJetStep P)
  exact hgen n 1

/-- Exact change-of-variables identity:
`δ⁻¹ * abelIntPoly P (u - log δ) = t^2 * ∫_{Ioi 0} inverseLi (v / δ) * P(t v) * exp (-t v) dv`. -/
lemma scaled_abelIntPoly_eq {δ : ℝ} (hδ : 0 < δ) (P : Polynomial ℝ) (u : ℝ) :
    δ⁻¹ * abelIntPoly P (u - Real.log δ) =
      Real.exp (-u) ^ 2 *
        ∫ v in Set.Ioi (0 : ℝ), NthPrime.inverseLi (v / δ) * P.eval (Real.exp (-u) * v) *
          Real.exp (-(Real.exp (-u) * v)) := by
  dsimp only [abelIntPoly]
  have hexp : Real.exp (-(u - Real.log δ)) = δ * Real.exp (-u) := by
    rw [show -(u - Real.log δ) = Real.log δ + (-u) by ring, Real.exp_add, Real.exp_log hδ]
  rw [hexp]
  let g : ℝ → ℝ := fun v => NthPrime.inverseLi (v / δ) * P.eval (Real.exp (-u) * v) *
    Real.exp (-(Real.exp (-u) * v))
  have hcov : ∫ w in Set.Ioi (0 : ℝ), g (δ * w) =
      δ⁻¹ * ∫ v in Set.Ioi (0 : ℝ), g v := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi g (0 : ℝ) hδ
    simpa [mul_zero, smul_eq_mul] using h
  have hfun : (fun w : ℝ => NthPrime.inverseLi w * P.eval (δ * Real.exp (-u) * w) *
        Real.exp (-(δ * Real.exp (-u) * w))) = fun w : ℝ => g (δ * w) := by
    ext w
    dsimp only [g]
    rw [mul_div_cancel_left₀ w hδ.ne',
      show δ * Real.exp (-u) * w = Real.exp (-u) * (δ * w) by ring]
  rw [hfun, hcov]
  dsimp only [g]
  field_simp [hδ.ne']

/-- Scaled Riemann-sum MVT bound: for every `δ > 0` and every `P : Polynomial ℝ`,
`|(∑' n, abelPolyTerm (scaledInvLiSeq δ) P n u) - δ⁻¹ * abelIntPoly P (u - Real.log δ)| ≤ C * u * exp (-u)`
on `[1, ∞)`. -/
theorem scaled_abelPolySum_sub_abelIntPoly_exp_decay {δ : ℝ} (hδ : 0 < δ) (P : Polynomial ℝ) :
    ∃ C > 0, ∀ u : ℝ, 1 ≤ u →
      |(∑' n : ℕ, NthPrime.abelPolyTerm (scaledInvLiSeq δ) P n u) -
        δ⁻¹ * abelIntPoly P (u - Real.log δ)| ≤ C * u * Real.exp (-u) := by
  obtain ⟨CP, hCP, hP⟩ := exists_poly_abs_le P
  obtain ⟨CP', hCP', hP'⟩ := exists_poly_abs_le P.derivative
  obtain ⟨A_s, hAs, hbd_s⟩ := abs_scaledInvLiSeq_le hδ
  let d := max P.natDegree P.derivative.natDegree
  let M_poly : ℝ := (CP + CP') * 2
  have hM_poly_pos : 0 < M_poly := by dsimp [M_poly]; positivity
  -- Global linear-log bound on `inverseLi (v / δ)` for `v > 0`
  let L_δ : ℝ := 2 * Real.log (4 * (1 / δ + 1)) + 2
  have hLδ_pos : 0 < L_δ := by
    have : 0 ≤ Real.log (4 * (1 / δ + 1)) := Real.log_nonneg (by
      have : 0 < 1 / δ := by positivity
      linarith)
    dsimp [L_δ]; linarith
  have hlog_invLi : ∀ v : ℝ, 0 < v →
      Real.log (NthPrime.inverseLi (v / δ)) ≤ L_δ + 2 * Real.log (v + 1) := by
    intro v hv
    have hspec := (NthPrime.inverseLi_spec (show (0 : ℝ) ≤ v / δ by positivity)).1
    have h1 : 4 * (v / δ + 1) ≤ (4 * (1 / δ + 1)) * (v + 1) := by
      have : v / δ + 1 ≤ (1 / δ + 1) * (v + 1) := by
        rw [one_div, add_mul, mul_add, inv_mul_eq_div, mul_one, one_mul]
        linarith [inv_pos.mpr hδ, hv]
      linarith
    calc Real.log (NthPrime.inverseLi (v / δ))
        ≤ Real.log ((4 * (v / δ + 1)) ^ 2) := Real.log_le_log (by linarith [hspec.1]) hspec.2
      _ = 2 * Real.log (4 * (v / δ + 1)) := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * Real.log ((4 * (1 / δ + 1)) * (v + 1)) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h1) (by norm_num)
      _ = 2 * (Real.log (4 * (1 / δ + 1)) + Real.log (v + 1)) := by
          rw [Real.log_mul (by positivity) (by positivity)]
      _ ≤ L_δ + 2 * Real.log (v + 1) := by dsimp [L_δ]; linarith
  have hinvLi_lin : ∀ v : ℝ, 0 < v →
      NthPrime.inverseLi (v / δ) ≤ 64 + (2 / δ) * v * (L_δ + Real.log (v + 1)) := by
    intro v hv
    by_cases h1 : 1 ≤ v / δ
    · have hlin := inverseLi_le_linear_log h1
      have harg : 4 * (v / δ + 1) ≤ (4 * (1 / δ + 1)) * (v + 1) := by
        have : v / δ + 1 ≤ (1 / δ + 1) * (v + 1) := by
          rw [one_div, add_mul, mul_add, inv_mul_eq_div, mul_one, one_mul]
          linarith [inv_pos.mpr hδ, hv]
        linarith
      have hlog : Real.log (4 * (v / δ + 1)) ≤ L_δ + Real.log (v + 1) := by
        have h2 : Real.log (4 * (v / δ + 1)) ≤ Real.log (4 * (1 / δ + 1)) + Real.log (v + 1) := by
          rw [← Real.log_mul (by positivity) (by positivity)]
          exact Real.log_le_log (by positivity) harg
        have hpos : 0 ≤ Real.log (4 * (1 / δ + 1)) := Real.log_nonneg (by
          have hinv : 0 < 1 / δ := by positivity
          linarith)
        dsimp [L_δ]; linarith
      calc NthPrime.inverseLi (v / δ)
          ≤ 64 + 2 * (v / δ) * Real.log (4 * (v / δ + 1)) := hlin
        _ ≤ 64 + (2 / δ) * v * (L_δ + Real.log (v + 1)) := by
            have heq : 2 * (v / δ) = (2 / δ) * v := by ring
            rw [heq]
            linarith [mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ (2 / δ) * v by positivity)]
    · push Not at h1
      have hspec := (NthPrime.inverseLi_spec (show (0 : ℝ) ≤ v / δ by positivity)).1
      have hle64 : NthPrime.inverseLi (v / δ) ≤ 64 := by
        have : (4 * (v / δ + 1)) ^ 2 ≤ 64 := by nlinarith [show (0 : ℝ) ≤ v / δ by positivity]
        exact hspec.2.trans this
      have hlog_nn : 0 ≤ Real.log (v + 1) := Real.log_nonneg (by linarith)
      have hnn : 0 ≤ (2 / δ) * v * (L_δ + Real.log (v + 1)) := by positivity
      linarith
  -- Absorption constant for `(1 + y^d) * (1 + y^2) * exp (-y) ≤ K_abs * exp (-y / 2)`
  let K_abs : ℝ := (2 : ℝ) ^ 0 * (0 : ℕ).factorial + (2 : ℝ) ^ 1 * (1 : ℕ).factorial +
    (2 : ℝ) ^ 2 * (2 : ℕ).factorial + (2 : ℝ) ^ d * d.factorial +
    (2 : ℝ) ^ (d + 1) * (d + 1).factorial + (2 : ℝ) ^ (d + 2) * (d + 2).factorial
  let C_n0 : ℝ := 2 * ((4 * (1 / δ + 1)) ^ 2 * (CP * 2))
  let C_step : ℝ := Real.exp 1 * M_poly * (δ⁻¹ * (L_δ + 2) + 64 + (2 / δ) * (L_δ + 2)) * 4 * K_abs
  let C_tot : ℝ := C_n0 + 2 * C_step + 1
  refine ⟨C_tot, by dsimp [C_tot, C_n0, C_step, K_abs]; positivity, fun u hu => ?_⟩
  rw [scaled_abelIntPoly_eq hδ P u]
  set t : ℝ := Real.exp (-u)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  let F : ℝ → ℝ := fun v => NthPrime.inverseLi (v / δ) * P.eval (t * v) * Real.exp (-(t * v))
  have hint_F : IntegrableOn F (Set.Ioi 0) := by
    have hcont_inv : ContinuousOn (fun v : ℝ => NthPrime.inverseLi (v / δ)) (Set.Ioi (0 : ℝ)) :=
      fun v hv => ((NthPrime.inverseLi_hasDerivAt (div_pos hv hδ)).comp v
        (by simpa [div_eq_mul_inv] using (hasDerivAt_id v).mul_const δ⁻¹)).continuousAt.continuousWithinAt
    have hmeas : AEStronglyMeasurable F (volume.restrict (Set.Ioi 0)) :=
      ((hcont_inv.mul (P.continuous.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    let K_dom : ℝ := (4 * (1 / δ + 1)) ^ 2 * 2 * CP * (1 + t ^ P.natDegree) *
      ((2 / t) ^ 0 * (0 : ℕ).factorial + (2 / t) ^ 2 * (2 : ℕ).factorial +
        (2 / t) ^ P.natDegree * P.natDegree.factorial + (2 / t) ^ (P.natDegree + 2) * (P.natDegree + 2).factorial)
    have hdom : IntegrableOn (fun v : ℝ => K_dom * Real.exp (-(t / 2) * v)) (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul K_dom
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    have hspec := (NthPrime.inverseLi_spec (show (0 : ℝ) ≤ v / δ by positivity)).1
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by linarith [hspec.1]),
      abs_of_pos (Real.exp_pos _)]
    have hinv_le : NthPrime.inverseLi (v / δ) ≤ (4 * (1 / δ + 1)) ^ 2 * 2 * (1 + v ^ 2) := by
      have harg : v / δ + 1 ≤ (1 / δ + 1) * (v + 1) := by
        rw [one_div, add_mul, mul_add, inv_mul_eq_div, mul_one, one_mul]
        linarith [inv_pos.mpr hδ, hv0]
      have hsq : (4 * (v / δ + 1)) ^ 2 ≤ (4 * (1 / δ + 1)) ^ 2 * (v + 1) ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h2 : (v + 1) ^ 2 ≤ 2 * (1 + v ^ 2) := by nlinarith [sq_nonneg (v - 1)]
      calc NthPrime.inverseLi (v / δ) ≤ (4 * (v / δ + 1)) ^ 2 := hspec.2
        _ ≤ (4 * (1 / δ + 1)) ^ 2 * (v + 1) ^ 2 := hsq
        _ ≤ (4 * (1 / δ + 1)) ^ 2 * (2 * (1 + v ^ 2)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (4 * (1 / δ + 1)) ^ 2 * 2 * (1 + v ^ 2) := by ring
    have hP_le : |P.eval (t * v)| ≤ CP * (1 + t ^ P.natDegree) * (1 + v ^ P.natDegree) := by
      have h1 := hP (t * v) (by positivity)
      rw [mul_pow] at h1
      have h2 : 1 + t ^ P.natDegree * v ^ P.natDegree ≤ (1 + t ^ P.natDegree) * (1 + v ^ P.natDegree) := by
        nlinarith [pow_nonneg ht0.le P.natDegree, pow_nonneg hv0.le P.natDegree]
      nlinarith
    have hb0 := pow_mul_exp_neg_mul_le 0 ht0 hv0.le
    have hb2 := pow_mul_exp_neg_mul_le 2 ht0 hv0.le
    have hbd := pow_mul_exp_neg_mul_le P.natDegree ht0 hv0.le
    have hbd2 := pow_mul_exp_neg_mul_le (P.natDegree + 2) ht0 hv0.le
    have hexp_eq : (1 + v ^ 2) * (1 + v ^ P.natDegree) * Real.exp (-(t * v)) =
        v ^ 0 * Real.exp (-(t * v)) + v ^ 2 * Real.exp (-(t * v)) +
        v ^ P.natDegree * Real.exp (-(t * v)) + v ^ (P.natDegree + 2) * Real.exp (-(t * v)) := by
      rw [pow_zero, pow_add]; ring
    have hneg : -t * v = -(t * v) := by ring
    rw [hneg] at hb0 hb2 hbd hbd2
    have hprod_le : (1 + v ^ 2) * (1 + v ^ P.natDegree) * Real.exp (-(t * v)) ≤
        ((2 / t) ^ 0 * (0 : ℕ).factorial + (2 / t) ^ 2 * (2 : ℕ).factorial +
          (2 / t) ^ P.natDegree * P.natDegree.factorial +
          (2 / t) ^ (P.natDegree + 2) * (P.natDegree + 2).factorial) * Real.exp (-(t / 2) * v) := by
      rw [hexp_eq]; linarith
    calc NthPrime.inverseLi (v / δ) * |P.eval (t * v)| * Real.exp (-(t * v))
        ≤ ((4 * (1 / δ + 1)) ^ 2 * 2 * (1 + v ^ 2)) *
            (CP * (1 + t ^ P.natDegree) * (1 + v ^ P.natDegree)) * Real.exp (-(t * v)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hinv_le hP_le (abs_nonneg _) (by positivity)) (Real.exp_pos _).le
      _ = (4 * (1 / δ + 1)) ^ 2 * 2 * CP * (1 + t ^ P.natDegree) *
            ((1 + v ^ 2) * (1 + v ^ P.natDegree) * Real.exp (-(t * v))) := by ring
      _ ≤ K_dom * Real.exp (-(t / 2) * v) := by
          dsimp only [K_dom]
          rw [mul_assoc ((4 * (1 / δ + 1)) ^ 2 * 2 * CP * (1 + t ^ P.natDegree))]
          exact mul_le_mul_of_nonneg_left hprod_le (by positivity)
  have hIoi_eq : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioc (n : ℝ) ((n : ℝ) + 1) := by
    ext v; simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · intro hv
      let k := ⌈v⌉₊ - 1
      have hpos : 0 < ⌈v⌉₊ := Nat.ceil_pos.mpr hv
      refine ⟨k, ?_, ?_⟩
      · by_contra h; push Not at h; have := Nat.ceil_le.mpr h; omega
      · have heq : (k : ℝ) + 1 = (⌈v⌉₊ : ℝ) := by dsimp [k]; exact_mod_cast Nat.sub_add_cancel hpos
        rw [heq]; exact Nat.le_ceil v
    · rintro ⟨n, hn1, _⟩; exact lt_of_le_of_lt (Nat.cast_nonneg n) hn1
  have hdisj : Pairwise (fun m n : ℕ => Disjoint (Set.Ioc (m : ℝ) ((m : ℝ) + 1)) (Set.Ioc (n : ℝ) ((n : ℝ) + 1))) := by
    intro m n hmn
    rw [Set.disjoint_left]; intro x hxm hxn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
      linarith [hxm.2, hxn.1]
    · have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgt
      linarith [hxm.1, hxn.2]
  have hint_split : ∫ v in Set.Ioi (0 : ℝ), F v = ∑' n : ℕ, ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v := by
    rw [hIoi_eq]
    exact MeasureTheory.integral_iUnion (fun _ => measurableSet_Ioc) hdisj (hIoi_eq ▸ hint_F)
  have hsum_F : Summable (fun n : ℕ => t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v) :=
    ((MeasureTheory.hasSum_integral_iUnion (fun _ => measurableSet_Ioc) hdisj (hIoi_eq ▸ hint_F)).summable).mul_left (t ^ 2)
  have hsum_S : Summable (fun n : ℕ => NthPrime.abelPolyTerm (scaledInvLiSeq δ) P n u) := by
    obtain ⟨B, hB, hbound⟩ := abelPoly_localBound_quad hAs hbd_s P u
    exact hB.of_norm_bounded fun n => hbound n u ⟨by linarith, by linarith⟩
  have hdiff_eq : (∑' n : ℕ, NthPrime.abelPolyTerm (scaledInvLiSeq δ) P n u) - t ^ 2 * ∫ v in Set.Ioi (0 : ℝ), F v =
      ∑' n : ℕ, (t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v) := by
    rw [hint_split, ← tsum_mul_left, ← hsum_S.tsum_sub hsum_F]
    congr 1; ext n; dsimp only [NthPrime.abelPolyTerm, scaledInvLiSeq, F]; ring
  -- Term `n = 0`
  have hterm_0 : |t ^ 2 * F ((0 : ℕ) + 1 : ℝ) - t ^ 2 * ∫ v in Set.Ioc ((0 : ℕ) : ℝ) ((0 : ℕ) + 1 : ℝ), F v| ≤
      C_n0 * u * t := by
    have hF_le : ∀ v ∈ Set.Ioc (0 : ℝ) 1, |F v| ≤ (4 * (1 / δ + 1)) ^ 2 * (CP * 2) := by
      intro v hv
      have hv0 : 0 < v := hv.1
      have hspec := (NthPrime.inverseLi_spec (show (0 : ℝ) ≤ v / δ by positivity)).1
      have hinv : NthPrime.inverseLi (v / δ) ≤ (4 * (1 / δ + 1)) ^ 2 := by
        refine hspec.2.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
        have : v / δ ≤ 1 / δ := div_le_div_of_nonneg_right hv.2 hδ.le
        linarith
      have htv_le1 : t * v ≤ 1 := by nlinarith [hv.1, hv.2]
      have hP_le : |P.eval (t * v)| ≤ CP * 2 := by
        have h1 := hP (t * v) (by positivity)
        have hpow : (t * v) ^ P.natDegree ≤ 1 := pow_le_one₀ (by positivity) htv_le1
        nlinarith
      have hexp_le : Real.exp (-(t * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hv.1])
      dsimp only [F]
      rw [abs_mul, abs_mul, abs_of_pos (by linarith [hspec.1]), abs_of_pos (Real.exp_pos _)]
      calc NthPrime.inverseLi (v / δ) * |P.eval (t * v)| * Real.exp (-(t * v))
          ≤ ((4 * (1 / δ + 1)) ^ 2 * (CP * 2)) * 1 :=
            mul_le_mul (mul_le_mul hinv hP_le (abs_nonneg _) (by positivity)) hexp_le (Real.exp_pos _).le (by positivity)
        _ = (4 * (1 / δ + 1)) ^ 2 * (CP * 2) := mul_one _
    have hF1 := hF_le 1 ⟨zero_lt_one, le_rfl⟩
    have hFint : |∫ v in Set.Ioc (0 : ℝ) 1, F v| ≤ (4 * (1 / δ + 1)) ^ 2 * (CP * 2) := by
      calc |∫ v in Set.Ioc (0 : ℝ) 1, F v| ≤ ∫ v in Set.Ioc (0 : ℝ) 1, |F v| := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm F
        _ ≤ ∫ _ in Set.Ioc (0 : ℝ) 1, ((4 * (1 / δ + 1)) ^ 2 * (CP * 2)) :=
            setIntegral_mono_on (hint_F.mono_set Set.Ioc_subset_Ioi_self).norm
              (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc hF_le
        _ = (4 * (1 / δ + 1)) ^ 2 * (CP * 2) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc]; simp
    simp only [Nat.cast_zero, zero_add]
    rw [← mul_sub, abs_mul, abs_pow, abs_of_pos ht0]
    have hsub : |F 1 - ∫ v in Set.Ioc (0 : ℝ) 1, F v| ≤ C_n0 := by
      dsimp only [C_n0]; linarith [abs_sub (F 1) (∫ v in Set.Ioc (0 : ℝ) 1, F v)]
    have ht2_le : t ^ 2 ≤ u * t := by nlinarith
    calc t ^ 2 * |F 1 - ∫ v in Set.Ioc (0 : ℝ) 1, F v|
        ≤ (u * t) * C_n0 := mul_le_mul ht2_le hsub (abs_nonneg _) (by positivity)
      _ = C_n0 * u * t := by ring
  -- Terms `n = k + 1 ≥ 1` via MVT on `[n, n + 1]`
  have hterm_succ : ∀ k : ℕ,
      |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v| ≤
        (C_step * u * t) * (t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2)) := by
    intro k
    let n : ℕ := k + 1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_pos k
    set y : ℝ := t * ((n : ℝ) + 1)
    have hF'_bd : ∀ ξ ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1),
        HasDerivAt F
          ((δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval (t * ξ) +
            NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
            Real.exp (-(t * ξ))) ξ ∧
        |(δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval (t * ξ) +
            NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
            Real.exp (-(t * ξ))| ≤
          C_step * u * Real.exp (-y / 2) := by
      intro ξ hξ
      have hξ0 : 0 < ξ := by linarith [hξ.1]
      have hdiv : HasDerivAt (fun x : ℝ => x / δ) δ⁻¹ ξ := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id ξ).mul_const δ⁻¹
      have hinv_d : HasDerivAt (fun x : ℝ => NthPrime.inverseLi (x / δ))
          (δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ))) ξ := by
        have hcomp := (NthPrime.inverseLi_hasDerivAt (div_pos hξ0 hδ)).comp ξ hdiv
        change HasDerivAt (fun x : ℝ => NthPrime.inverseLi (x / δ)) _ ξ at hcomp
        exact hcomp.congr_deriv (by ring)
      have htx : HasDerivAt (fun x : ℝ => t * x) t ξ := by
        simpa using (hasDerivAt_id ξ).const_mul t
      have hP_d : HasDerivAt (fun x : ℝ => P.eval (t * x)) (P.derivative.eval (t * ξ) * t) ξ :=
        (P.hasDerivAt (t * ξ)).comp ξ htx
      have hexp_d : HasDerivAt (fun x : ℝ => Real.exp (-(t * x))) (-t * Real.exp (-(t * ξ))) ξ := by
        simpa [mul_comm] using htx.neg.exp
      have hdF : HasDerivAt F
          ((δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval (t * ξ) +
            NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
            Real.exp (-(t * ξ))) ξ := by
        refine ((hinv_d.mul hP_d).mul hexp_d).congr_deriv ?_
        dsimp only [Pi.mul_apply]; ring
      refine ⟨hdF, ?_⟩
      set z : ℝ := t * ξ
      have hz0 : 0 < z := by positivity
      have hlog_xi : Real.log (ξ + 1) ≤ u + z := by
        have h1 : ξ + 1 ≤ Real.exp u * (z + 1) := by
          have htu : Real.exp u * t = 1 := by dsimp [t]; rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
          have h2 : Real.exp u * (z + 1) = ξ + Real.exp u := by
            dsimp [z]; rw [mul_add, ← mul_assoc, htu, one_mul, mul_one]
          rw [h2]; linarith [Real.one_le_exp (by linarith : 0 ≤ u)]
        calc Real.log (ξ + 1) ≤ Real.log (Real.exp u * (z + 1)) := Real.log_le_log (by positivity) h1
          _ = u + Real.log (z + 1) := by rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
          _ ≤ u + z := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < z + 1 by positivity)]
      have hspec := (NthPrime.inverseLi_spec (show (0 : ℝ) ≤ ξ / δ by positivity)).1
      have hlog_nn : 0 ≤ Real.log (NthPrime.inverseLi (ξ / δ)) := Real.log_nonneg (by linarith [hspec.1])
      have hP_z : |P.eval z| ≤ CP * (2 * (1 + z ^ d)) := by
        have h1 := hP z hz0.le
        have h2 : 1 + z ^ P.natDegree ≤ 2 * (1 + z ^ d) := by
          by_cases hz1 : z ≤ 1
          · have : z ^ P.natDegree ≤ 1 := pow_le_one₀ hz0.le hz1
            linarith [pow_nonneg hz0.le d]
          · push Not at hz1
            have : z ^ P.natDegree ≤ z ^ d := pow_le_pow_right₀ hz1.le (le_max_left _ _)
            linarith [pow_nonneg hz0.le d]
        nlinarith
      have hP'_z : |P.derivative.eval z| ≤ CP' * (2 * (1 + z ^ d)) := by
        have h1 := hP' z hz0.le
        have h2 : 1 + z ^ P.derivative.natDegree ≤ 2 * (1 + z ^ d) := by
          by_cases hz1 : z ≤ 1
          · have : z ^ P.derivative.natDegree ≤ 1 := pow_le_one₀ hz0.le hz1
            linarith [pow_nonneg hz0.le d]
          · push Not at hz1
            have : z ^ P.derivative.natDegree ≤ z ^ d := pow_le_pow_right₀ hz1.le (le_max_right _ _)
            linarith [pow_nonneg hz0.le d]
        nlinarith
      have hM_comb : |P.derivative.eval z - P.eval z| ≤ M_poly * (1 + z ^ d) := by
        dsimp only [M_poly]; linarith [abs_sub (P.derivative.eval z) (P.eval z)]
      have hP_comb : |P.eval z| ≤ M_poly * (1 + z ^ d) := by
        dsimp only [M_poly]; nlinarith [pow_nonneg hz0.le d]
      have hterm1 : δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) ≤ δ⁻¹ * (L_δ + 2) * u * (1 + z) := by
        have h1 := hlog_invLi ξ hξ0
        have h2 : L_δ + 2 * (u + z) ≤ (L_δ + 2) * u * (1 + z) := by
          nlinarith [mul_nonneg hLδ_pos.le hz0.le, mul_nonneg (show (0 : ℝ) ≤ u - 1 by linarith) hz0.le]
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hδ.le)
      have hterm2 : NthPrime.inverseLi (ξ / δ) * t ≤ (64 + (2 / δ) * (L_δ + 2)) * u * (1 + z + z ^ 2) := by
        have h1 := hinvLi_lin ξ hξ0
        have h2 : NthPrime.inverseLi (ξ / δ) * t ≤ 64 * t + (2 / δ) * z * (L_δ + u + z) := by
          have hmul := mul_le_mul_of_nonneg_right h1 ht0.le
          have h3 : (2 / δ) * ξ * (L_δ + Real.log (ξ + 1)) * t ≤ (2 / δ) * z * (L_δ + u + z) := by
            have heq : (2 / δ) * ξ * (L_δ + Real.log (ξ + 1)) * t = (2 / δ) * z * (L_δ + Real.log (ξ + 1)) := by
              dsimp [z]; ring
            rw [heq]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
        have h3 : 64 * t ≤ 64 * u * (1 + z + z ^ 2) := by nlinarith [sq_nonneg z]
        have h4 : (2 / δ) * z * (L_δ + u + z) ≤ (2 / δ) * (L_δ + 2) * u * (1 + z + z ^ 2) := by
          have h5 : z * (L_δ + u + z) ≤ (L_δ + 2) * u * (1 + z + z ^ 2) := by
            nlinarith [sq_nonneg z, mul_nonneg hLδ_pos.le hz0.le,
              mul_nonneg (show (0 : ℝ) ≤ u - 1 by linarith) hz0.le,
              mul_nonneg hLδ_pos.le (sq_nonneg z)]
          have := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 2 / δ by positivity)
          linarith
        linarith
      have hbrac : |δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval z +
            NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval z - P.eval z)| ≤
          M_poly * (δ⁻¹ * (L_δ + 2) + 64 + (2 / δ) * (L_δ + 2)) * u * (2 * ((1 + z ^ d) * (1 + z + z ^ 2))) := by
        have h1 : |δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval z| ≤
            (δ⁻¹ * (L_δ + 2) * u * (1 + z + z ^ 2)) * (M_poly * (1 + z ^ d)) := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le) hlog_nn)]
          refine mul_le_mul ?_ hP_comb (abs_nonneg _) (by positivity)
          exact hterm1.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z]) (by positivity))
        have h2 : |NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval z - P.eval z)| ≤
            ((64 + (2 / δ) * (L_δ + 2)) * u * (1 + z + z ^ 2)) * (M_poly * (1 + z ^ d)) := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg (by linarith [hspec.1]) ht0.le)]
          exact mul_le_mul hterm2 hM_comb (abs_nonneg _) (by positivity)
        have htri := abs_add_le (δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval z)
          (NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval z - P.eval z))
        have hnn : 0 ≤ M_poly * (δ⁻¹ * (L_δ + 2) + 64 + (2 / δ) * (L_δ + 2)) * u * ((1 + z ^ d) * (1 + z + z ^ 2)) := by positivity
        linarith
      have habs_z : (1 + z ^ d) * (1 + z + z ^ 2) * Real.exp (-z) ≤ K_abs * Real.exp (-z / 2) := by
        have hb0 := pow_mul_exp_neg_mul_le 0 zero_lt_one hz0.le
        have hb1 := pow_mul_exp_neg_mul_le 1 zero_lt_one hz0.le
        have hb2 := pow_mul_exp_neg_mul_le 2 zero_lt_one hz0.le
        have hbd := pow_mul_exp_neg_mul_le d zero_lt_one hz0.le
        have hbd1 := pow_mul_exp_neg_mul_le (d + 1) zero_lt_one hz0.le
        have hbd2 := pow_mul_exp_neg_mul_le (d + 2) zero_lt_one hz0.le
        simp only [div_one, neg_mul, one_mul, pow_zero, pow_one] at hb0 hb1 hb2 hbd hbd1 hbd2
        have hdiv2 : -(1 / 2 * z) = -z / 2 := by ring
        rw [hdiv2] at hb0 hb1 hb2 hbd hbd1 hbd2
        have hexp_eq : (1 + z ^ d) * (1 + z + z ^ 2) * Real.exp (-z) =
            Real.exp (-z) + z * Real.exp (-z) + z ^ 2 * Real.exp (-z) +
            z ^ d * Real.exp (-z) + z ^ (d + 1) * Real.exp (-z) + z ^ (d + 2) * Real.exp (-z) := by
          rw [pow_succ, pow_succ, pow_succ]; ring
        rw [hexp_eq]; dsimp only [K_abs]; linarith
      have hshift_e : Real.exp (-z / 2) ≤ Real.exp 1 * Real.exp (-y / 2) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hzy : y - z ≤ 1 := by dsimp [y, z]; nlinarith [hξ.1, hξ.2]
        linarith
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval z +
              NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval z - P.eval z)| * Real.exp (-z)
          ≤ (M_poly * (δ⁻¹ * (L_δ + 2) + 64 + (2 / δ) * (L_δ + 2)) * u *
              (2 * ((1 + z ^ d) * (1 + z + z ^ 2)))) * Real.exp (-z) :=
            mul_le_mul_of_nonneg_right hbrac (Real.exp_pos _).le
        _ = M_poly * (δ⁻¹ * (L_δ + 2) + 64 + (2 / δ) * (L_δ + 2)) * u * 2 *
              ((1 + z ^ d) * (1 + z + z ^ 2) * Real.exp (-z)) := by ring
        _ ≤ M_poly * (δ⁻¹ * (L_δ + 2) + 64 + (2 / δ) * (L_δ + 2)) * u * 2 *
              (K_abs * (Real.exp 1 * Real.exp (-y / 2))) :=
            mul_le_mul_of_nonneg_left (habs_z.trans (mul_le_mul_of_nonneg_left hshift_e (by dsimp [K_abs]; positivity)))
              (by positivity)
        _ ≤ C_step * u * Real.exp (-y / 2) := by
            dsimp only [C_step]
            have hnn : 0 ≤ Real.exp 1 * M_poly * (δ⁻¹ * (L_δ + 2) + 64 + (2 / δ) * (L_δ + 2)) * K_abs * u * Real.exp (-y / 2) := by
              dsimp [K_abs]; positivity
            linarith
    -- MVT pointwise bound `|F (n + 1) - F v| ≤ C_step * u * exp (-y / 2)` for `v ∈ Ioc n (n + 1)`
    have hpt : ∀ v ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), |F ((n : ℝ) + 1) - F v| ≤ C_step * u * Real.exp (-y / 2) := by
      intro v hv
      rcases eq_or_lt_of_le hv.2 with rfl | hv_lt
      · rw [sub_self, abs_zero]; dsimp [C_step, K_abs]; positivity
      · have hcont : ContinuousOn F (Set.Icc v ((n : ℝ) + 1)) := fun ξ hξ =>
          (hF'_bd ξ ⟨hv.1.le.trans hξ.1, hξ.2⟩).1.continuousAt.continuousWithinAt
        have hdiff : ∀ ξ ∈ Set.Ioo v ((n : ℝ) + 1), HasDerivAt F _ ξ := fun ξ hξ =>
          (hF'_bd ξ ⟨(hv.1.trans hξ.1).le, hξ.2.le⟩).1
        obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope F _ hv_lt hcont hdiff
        have hlen_pos : 0 < (n : ℝ) + 1 - v := sub_pos.mpr hv_lt
        have hlen_le1 : (n : ℝ) + 1 - v ≤ 1 := by linarith [hv.1]
        have hbd := (hF'_bd ξ ⟨(hv.1.trans hξ.1).le, hξ.2.le⟩).2
        have heq : F ((n : ℝ) + 1) - F v =
            ((δ⁻¹ * Real.log (NthPrime.inverseLi (ξ / δ)) * P.eval (t * ξ) +
              NthPrime.inverseLi (ξ / δ) * t * (P.derivative.eval (t * ξ) - P.eval (t * ξ))) *
              Real.exp (-(t * ξ))) * ((n : ℝ) + 1 - v) := by
          rw [eq_div_iff hlen_pos.ne'] at hslope; linarith
        rw [heq, abs_mul, abs_of_pos hlen_pos]
        calc _ ≤ (C_step * u * Real.exp (-y / 2)) * 1 :=
              mul_le_mul hbd hlen_le1 hlen_pos.le (by dsimp [C_step, K_abs]; positivity)
          _ = C_step * u * Real.exp (-y / 2) := mul_one _
    have hint_n : IntegrableOn F (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) :=
      hint_F.mono_set fun x hx => lt_of_le_of_lt (by linarith) hx.1
    have hconst_int : ∫ _ in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F ((n : ℝ) + 1) = F ((n : ℝ) + 1) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc]
      simp
    have hsub_int : F ((n : ℝ) + 1) - ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v =
        ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), (F ((n : ℝ) + 1) - F v) := by
      rw [MeasureTheory.integral_sub (integrableOn_const (hs := measure_Ioc_lt_top.ne)) hint_n, hconst_int]
    have hint_diff : |F ((n : ℝ) + 1) - ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v| ≤
        C_step * u * Real.exp (-y / 2) := by
      rw [hsub_int]
      calc |∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), (F ((n : ℝ) + 1) - F v)|
          ≤ ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), |F ((n : ℝ) + 1) - F v| := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v => F ((n : ℝ) + 1) - F v)
        _ ≤ ∫ _ in Set.Ioc (n : ℝ) ((n : ℝ) + 1), (C_step * u * Real.exp (-y / 2)) :=
            setIntegral_mono_on ((integrableOn_const (hs := measure_Ioc_lt_top.ne)).sub hint_n).norm
              (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc hpt
        _ = C_step * u * Real.exp (-y / 2) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc]; simp
    rw [← mul_sub, abs_mul, abs_pow, abs_of_pos ht0]
    have heq_rhs : t ^ 2 * (C_step * u * Real.exp (-y / 2)) =
        (C_step * u * t) * (t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2)) := by
      dsimp only [y, n]; ring
    rw [← heq_rhs]
    exact mul_le_mul_of_nonneg_left hint_diff (by positivity)
  -- Sum `n = 0` and `n ≥ 1`
  obtain ⟨hgeom_sum, hgeom_le⟩ := t_mul_tsum_exp_neg_half_le ht0
  have hsum_abs_succ : Summable (fun k : ℕ =>
      |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v|) := by
    have hmaj := (hgeom_sum.comp_injective Nat.succ_injective).mul_left (C_step * u * t)
    exact hmaj.of_nonneg_of_le (fun _ => abs_nonneg _) hterm_succ
  have hsum_abs : Summable (fun n : ℕ => |t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v|) :=
    (summable_nat_add_iff 1).mp (hsum_abs_succ.congr fun k => by simp [Nat.cast_add, Nat.cast_one])
  have hsucc_le : (∑' k : ℕ, |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) -
        t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v|) ≤ 2 * C_step * u * t := by
    have hmaj := (hgeom_sum.comp_injective Nat.succ_injective).mul_left (C_step * u * t)
    calc _ ≤ ∑' k : ℕ, (C_step * u * t) * (t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2)) :=
          hsum_abs_succ.tsum_le_tsum hterm_succ hmaj
      _ = (C_step * u * t) * ∑' k : ℕ, t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2) := tsum_mul_left
      _ ≤ (C_step * u * t) * ∑' n : ℕ, t * Real.exp (-(t * ((n : ℝ) + 1)) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by dsimp [C_step, K_abs]; positivity)
          rw [hgeom_sum.tsum_eq_zero_add]
          have h0_nn : 0 ≤ t * Real.exp (-(t * ((0 : ℕ) + 1 : ℝ)) / 2) := by positivity
          have hsh : (∑' k : ℕ, t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2)) =
              ∑' k : ℕ, t * Real.exp (-(t * (((k + 1 : ℕ) : ℝ) + 1)) / 2) := rfl
          linarith
      _ ≤ (C_step * u * t) * 2 := mul_le_mul_of_nonneg_left hgeom_le (by dsimp [C_step, K_abs]; positivity)
      _ = 2 * C_step * u * t := by ring
  rw [hdiff_eq]
  have hle_tsum : |∑' n : ℕ, (t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v)| ≤
      ∑' n : ℕ, |t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v| := by
    have hsum_norm : Summable (fun n : ℕ => ‖t ^ 2 * F ((n : ℝ) + 1) - t ^ 2 * ∫ v in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F v‖) := by
      simpa only [Real.norm_eq_abs] using hsum_abs
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum_norm
  rw [hsum_abs.tsum_eq_zero_add] at hle_tsum
  have hsplit : |t ^ 2 * F ((0 : ℕ) + 1 : ℝ) - t ^ 2 * ∫ v in Set.Ioc ((0 : ℕ) : ℝ) ((0 : ℕ) + 1 : ℝ), F v| +
        (∑' k : ℕ, |t ^ 2 * F (((k + 1 : ℕ) : ℝ) + 1) -
          t ^ 2 * ∫ v in Set.Ioc ((k + 1 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ) + 1), F v|) ≤ C_tot * u * t := by
    dsimp only [C_tot]; nlinarith [ht0]
  exact hle_tsum.trans (by simpa [Nat.cast_add, Nat.cast_one] using hsplit)

/-- **Counting Transfer Theorem (`hasScaledDensityAsymp_of_hasDensityPNT`)**:
Any strictly increasing sequence `a : ℕ → ℕ` satisfying all-orders density-`δ` PNT
has polynomial OGF growth and its smoothed Abel ray `seqSmoothRay a` matches
`δ⁻¹ * I_plus (u - Real.log δ)` to all inverse powers in every derivative order! -/
theorem hasScaledDensityAsymp_of_hasDensityPNT {a : ℕ → ℕ} {δ : ℝ} (hd : HasDensityPNT a δ) :
    HasScaledDensityAsymp a δ := by
  have hδ : 0 < δ := hd.2.1
  obtain ⟨⟨A_q, hAq, hquad⟩, herr⟩ := hasDensityPNT_bounds_and_indexLogError hd
  have hpoly : PrimeNome.PolyCoeffBound (seqSeries a) := by
    refine ⟨4 * A_q, 2, by positivity, fun n => ?_⟩
    cases n with
    | zero => simp [seqSeries]; positivity
    | succ k =>
      simp only [seqSeries_coeff_succ, Complex.norm_natCast]
      have h1 := hquad k
      rw [abs_of_nonneg (Nat.cast_nonneg _)] at h1
      have h2 : ((k : ℝ) + 2) ^ 2 ≤ 4 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      calc (a k : ℝ) ≤ A_q * ((k : ℝ) + 2) ^ 2 := h1
        _ ≤ A_q * (4 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left h2 hAq.le
        _ = (4 * A_q) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by ring
  refine ⟨hδ, hpoly, fun j N => ?_⟩
  -- Identify `seqSmoothRay a u` with `((∑' n, abelPolyTerm (fun k => a k) 1 n u : ℝ) : ℂ)`
  have hsmooth_eq : ∀ u : ℝ, seqSmoothRay a u =
      ((∑' n : ℕ, NthPrime.abelPolyTerm (fun k => (a k : ℝ)) 1 n u : ℝ) : ℂ) := by
    intro u
    set t : ℝ := Real.exp (-u)
    have ht : 0 < t := Real.exp_pos _
    have hsum_a : Summable (fun n : ℕ => NthPrime.abelPolyTerm (fun k => (a k : ℝ)) 1 n u) := by
      obtain ⟨B, hB, hb⟩ := abelPoly_localBound_quad hAq hquad 1 u
      exact hB.of_norm_bounded fun n => hb n u ⟨by linarith, by linarith⟩
    have hval_sum : Summable (fun k : ℕ => PrimeNome.term (seqSeries a) (PrimeNome.qRay u) k) :=
      (PrimeNome.seriesJet_abs hpoly.to_diskCoeffBound 0 (PrimeNome.qRay_disk u)).of_norm
    dsimp only [seqSmoothRay, PrimeNome.value]
    rw [hval_sum.tsum_eq_zero_add]
    have h0 : PrimeNome.term (seqSeries a) (PrimeNome.qRay u) 0 = 0 := by
      simp [PrimeNome.term, seqSeries_coeff_zero]
    rw [h0, zero_add, ← tsum_mul_left]
    have hcs := (Complex.ofRealCLM.hasSum hsum_a.hasSum).tsum_eq
    change _ = Complex.ofRealCLM _
    rw [← hcs]
    congr 1; ext n
    simp only [PrimeNome.term, PrimeNome.tRay, PrimeNome.qRay, seqSeries_coeff_succ,
      NthPrime.abelPolyTerm, Polynomial.eval_one, mul_one, Complex.ofRealCLM_apply]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [← Real.exp_nat_mul (-Real.exp (-u)) (n + 1)]
    have harg : ((n + 1 : ℕ) : ℝ) * -Real.exp (-u) = -(Real.exp (-u) * ((n : ℝ) + 1)) := by
      push_cast; ring
    rw [harg]; ring
  -- Piece A: `seqSmoothRay a - S_invLi_scaled δ`
  have hPieceA : ∃ CA > 0, ∃ UA : ℝ, ∀ u ≥ UA,
      ‖iteratedDeriv j (seqSmoothRay a) u - iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u‖ ≤
        CA / u ^ N := by
    let e : ℕ → ℝ := fun k => (a k : ℝ) - scaledInvLiSeq δ k
    have he : NthPrime.IndexLogError e := herr
    have hdiff_fun : (fun u : ℝ => seqSmoothRay a u - (S_invLi_scaled δ u : ℂ)) =
        fun u : ℝ => ((∑' n : ℕ, NthPrime.abelPolyTerm e 1 n u : ℝ) : ℂ) := by
      ext u
      rw [hsmooth_eq u]
      dsimp only [S_invLi_scaled]
      rw [← Complex.ofReal_sub]
      congr 1
      have ha_s : Summable (fun n : ℕ => NthPrime.abelPolyTerm (fun k => (a k : ℝ)) 1 n u) := by
        obtain ⟨B, hB, hb⟩ := abelPoly_localBound_quad hAq hquad 1 u
        exact hB.of_norm_bounded fun n => hb n u ⟨by linarith, by linarith⟩
      obtain ⟨A_s, hAs, hbd_s⟩ := abs_scaledInvLiSeq_le hδ
      have hi_s : Summable (fun n : ℕ => NthPrime.abelPolyTerm (scaledInvLiSeq δ) 1 n u) := by
        obtain ⟨B, hB, hb⟩ := abelPoly_localBound_quad hAs hbd_s 1 u
        exact hB.of_norm_bounded fun n => hb n u ⟨by linarith, by linarith⟩
      rw [← ha_s.tsum_sub hi_s]
      congr 1; ext n; dsimp only [NthPrime.abelPolyTerm, e]; ring
    have hjet : ∀ k : ℕ, iteratedDeriv k (fun v => ∑' n, NthPrime.abelPolyTerm e 1 n v) =
        fun u => ∑' n, NthPrime.abelPolyTerm e (NthPrime.abelJetStep^[k] 1) n u := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
        exact funext fun u => (NthPrime.hasDerivAt_abelPolySum he _ u).deriv
    obtain ⟨CA, hCA, hA_ev⟩ := NthPrime.abelPolyError_allOrders he (NthPrime.abelJetStep^[j] 1) N
    obtain ⟨UA, hUA⟩ := eventually_atTop.mp hA_ev
    refine ⟨CA, hCA, UA, fun u hu => ?_⟩
    have hcd1 : ContDiffAt ℝ j (seqSmoothRay a) u := by
      have han : AnalyticAt ℝ (seqSmoothRay a) u :=
        ((PrimeNome.tRay_analytic u).pow 2).mul (PrimeNome.ray_source_analytic hpoly.to_diskCoeffBound 1 u)
      exact han.contDiffAt.of_le le_top
    have hcd2 : ContDiffAt ℝ j (fun v : ℝ => (S_invLi_scaled δ v : ℂ)) u :=
      ((Complex.ofRealCLM.contDiff.of_le le_top).comp (contDiff_S_invLi_scaled hδ j)).contDiffAt
    have hsub := iteratedDeriv_sub hcd1 hcd2
    change iteratedDeriv j (fun v => seqSmoothRay a v - (S_invLi_scaled δ v : ℂ)) u = _ at hsub
    rw [← hsub, hdiff_fun, iteratedDeriv_ofReal_comp, Complex.norm_real, Real.norm_eq_abs, hjet j]
    have hnt : |∑' n : ℕ, NthPrime.abelPolyTerm e (NthPrime.abelJetStep^[j] 1) n u| ≤
        ∑' n : ℕ, |NthPrime.abelPolyTerm e (NthPrime.abelJetStep^[j] 1) n u| := by
      have hsn : Summable (fun n : ℕ => ‖NthPrime.abelPolyTerm e (NthPrime.abelJetStep^[j] 1) n u‖) := by
        simpa only [Real.norm_eq_abs] using (hUA u hu).1
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsn
    exact hnt.trans (hUA u hu).2
  -- Piece B: `S_invLi_scaled δ - δ⁻¹ * J_invLi (u - Real.log δ)`
  have hPieceB : ∃ CB > 0, ∃ UB : ℝ, ∀ u ≥ UB,
      ‖iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u -
        (δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ)‖ ≤ CB / u ^ N := by
    obtain ⟨CB0, hCB0, hB0⟩ := scaled_abelPolySum_sub_abelIntPoly_exp_decay hδ (NthPrime.abelJetStep^[j] 1)
    obtain ⟨CB, hCB, hB⟩ := mul_exp_neg_le_div_pow CB0 hCB0 N
    refine ⟨CB, hCB, 1, fun u hu => ?_⟩
    rw [iteratedDeriv_ofReal_comp, iteratedDeriv_ofReal_comp, iteratedDeriv_S_invLi_scaled hδ j,
      iteratedDeriv_J_invLi j, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact (hB0 u hu).trans (hB u hu)
  -- Pieces C + D: `δ⁻¹ * (J_invLi - I_plus)` at `u - Real.log δ`
  have hPieceCD : ∃ CCD > 0, ∃ UCD : ℝ, ∀ u ≥ UCD,
      ‖(δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ) -
        (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ)‖ ≤ CCD / u ^ N := by
    obtain ⟨CC0, hCC0, hC0⟩ := J_invLi_sub_T_jet_exp_decay j
    obtain ⟨CD0, hCD0, hD0⟩ := I_plus_sub_T_jet_exp_decay j
    obtain ⟨CCD0, hCCD0, hCD⟩ := mul_exp_neg_le_div_pow (CC0 + CD0) (by positivity) N
    refine ⟨δ⁻¹ * CCD0 * (2 : ℝ) ^ N, by positivity, max (2 * |Real.log δ| + 2) 2, fun u hu => ?_⟩
    have hu1 : 2 * |Real.log δ| + 2 ≤ u := (le_max_left _ _).trans hu
    have hu_pos : 0 < u := by linarith [abs_nonneg (Real.log δ)]
    let v : ℝ := u - Real.log δ
    have hv1 : 1 ≤ v := by dsimp [v]; have := (abs_le.mp (le_rfl : |Real.log δ| ≤ |Real.log δ|)).2; linarith
    have hv_half : u / 2 ≤ v := by dsimp [v]; have := (abs_le.mp (le_rfl : |Real.log δ| ≤ |Real.log δ|)).2; linarith
    have hcd_J : ContDiffAt ℝ j (fun w : ℝ => (J_invLi w : ℂ)) v :=
      ((Complex.ofRealCLM.contDiff.of_le le_top).comp (contDiff_J_invLi j)).contDiffAt
    have hcd_T : ContDiffAt ℝ j (fun w : ℝ => T_integral (Real.exp (-w))) v := by
      have han : AnalyticOnNhd ℂ (fun z : ℂ => T_integral (Complex.exp (-z))) halfStrip :=
        differentiableOn_T_exp_neg.analyticOnNhd isOpen_halfStrip
      have hcd_R : ContDiffOn ℝ ⊤ (fun z : ℂ => T_integral (Complex.exp (-z))) halfStrip :=
        (han.contDiffOn isOpen_halfStrip.uniqueDiffOn).restrict_scalars ℝ
      have hv_mem : (v : ℂ) ∈ halfStrip := by
        simp only [halfStrip, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
        exact ⟨by linarith, by norm_num⟩
      have hcomp : ContDiffAt ℝ ⊤ (fun w : ℝ => T_integral (Complex.exp (-(w : ℂ)))) v :=
        (hcd_R.contDiffAt (isOpen_halfStrip.mem_nhds hv_mem)).comp v Complex.ofRealCLM.contDiff.contDiffAt
      have heq : (fun w : ℝ => T_integral (Real.exp (-w))) = fun w : ℝ => T_integral (Complex.exp (-(w : ℂ))) := by
        ext w; rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
      rw [heq]; exact hcomp.of_le le_top
    have hcd_I : ContDiffAt ℝ j I_plus v := contDiff_I_plus.contDiffAt.of_le le_top
    have hJT : ‖iteratedDeriv j (fun w => (J_invLi w : ℂ)) v -
        iteratedDeriv j (fun w => T_integral (Real.exp (-w))) v‖ ≤ CC0 * v * Real.exp (-v) := by
      have hs := iteratedDeriv_sub hcd_J hcd_T
      change iteratedDeriv j (fun w => (J_invLi w : ℂ) - T_integral (Real.exp (-w))) v = _ at hs
      rw [← hs]; exact hC0 v hv1
    have hIT : ‖iteratedDeriv j (fun w => T_integral (Real.exp (-w))) v -
        iteratedDeriv j I_plus v‖ ≤ CD0 * v * Real.exp (-v) := by
      have hs := iteratedDeriv_sub hcd_I hcd_T
      change iteratedDeriv j (fun w => I_plus w - T_integral (Real.exp (-w))) v = _ at hs
      rw [norm_sub_rev, ← hs]; exact hD0 v hv1
    have hJI : ‖iteratedDeriv j (fun w => (J_invLi w : ℂ)) v - iteratedDeriv j I_plus v‖ ≤ CCD0 / v ^ N := by
      have htri : ‖iteratedDeriv j (fun w => (J_invLi w : ℂ)) v - iteratedDeriv j I_plus v‖ ≤
          ‖iteratedDeriv j (fun w => (J_invLi w : ℂ)) v - iteratedDeriv j (fun w => T_integral (Real.exp (-w))) v‖ +
          ‖iteratedDeriv j (fun w => T_integral (Real.exp (-w))) v - iteratedDeriv j I_plus v‖ := by
        have := norm_add_le
          (iteratedDeriv j (fun w => (J_invLi w : ℂ)) v - iteratedDeriv j (fun w => T_integral (Real.exp (-w))) v)
          (iteratedDeriv j (fun w => T_integral (Real.exp (-w))) v - iteratedDeriv j I_plus v)
        simpa using this
      have hsum : (CC0 + CD0) * v * Real.exp (-v) ≤ CCD0 / v ^ N := hCD v hv1
      linarith
    rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    calc δ⁻¹ * ‖iteratedDeriv j (fun w => (J_invLi w : ℂ)) v - iteratedDeriv j I_plus v‖
        ≤ δ⁻¹ * (CCD0 / v ^ N) := mul_le_mul_of_nonneg_left hJI (inv_nonneg.mpr hδ.le)
      _ ≤ δ⁻¹ * (CCD0 / (u / 2) ^ N) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hCCD0.le (pow_pos (by positivity) N)
              (pow_le_pow_left₀ (by positivity) hv_half N)) (inv_nonneg.mpr hδ.le)
      _ = (δ⁻¹ * CCD0 * (2 : ℝ) ^ N) / u ^ N := by
          rw [div_pow]; field_simp [(pow_pos hu_pos N).ne']
  -- Combine Pieces A, B, C+D
  obtain ⟨CA, hCA, UA, hA⟩ := hPieceA
  obtain ⟨CB, hCB, UB, hB⟩ := hPieceB
  obtain ⟨CCD, hCCD, UCD, hCD⟩ := hPieceCD
  refine ⟨CA + CB + CCD, by positivity, max UA (max UB UCD), fun u hu => ?_⟩
  have h1 := hA u ((le_max_left _ _).trans hu)
  have h2 := hB u (((le_max_left _ _).trans (le_max_right _ _)).trans hu)
  have h3 := hCD u (((le_max_right _ _).trans (le_max_right _ _)).trans hu)
  have htri : ‖iteratedDeriv j (seqSmoothRay a) u - (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ)‖ ≤
      ‖iteratedDeriv j (seqSmoothRay a) u - iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u‖ +
      ‖iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u -
        (δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ)‖ +
      ‖(δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ) -
        (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ)‖ := by
    have ha := norm_add_le
      (iteratedDeriv j (seqSmoothRay a) u - iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u)
      ((iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u -
        (δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ)) +
       ((δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ) -
        (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ)))
    have hb := norm_add_le
      (iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u -
        (δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ))
      ((δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ) -
        (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ))
    have heq : (iteratedDeriv j (seqSmoothRay a) u - iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u) +
        ((iteratedDeriv j (fun v => (S_invLi_scaled δ v : ℂ)) u -
          (δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ)) +
         ((δ : ℂ)⁻¹ * iteratedDeriv j (fun v => (J_invLi v : ℂ)) (u - Real.log δ) -
          (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ))) =
        iteratedDeriv j (seqSmoothRay a) u - (δ : ℂ)⁻¹ * iteratedDeriv j I_plus (u - Real.log δ) := by ring
    rw [heq] at ha; linarith
  have hsum_div : CA / u ^ N + CB / u ^ N + CCD / u ^ N = (CA + CB + CCD) / u ^ N := by ring
  linarith

/-! #### 3b. Exact Unitriangular `t`-Adic Pullback to Ordinary Generating Functions -/

/-- Joint differential coordinates `(q, {F_i^{(j)}})` over `ℂ` in `PowerSeries ℂ`. -/
@[expose] def jointSeriesCoordinates {d : ℕ} (F : Fin d → PowerSeries ℂ) :
    Option (Fin d × ℕ) → PowerSeries ℂ
  | none => PowerSeries.X
  | some (i, j) => PrimeNome.seriesJet (F i) j

/-- Formal power series `exp (-t) = ∑_{k ≥ 0} (-1)^k / k! * t^k`. -/
@[expose] def expNegT : PowerSeries ℂ :=
  PowerSeries.mk fun k => ((-1 : ℂ) ^ k) / (k.factorial : ℂ)

/-- Geometric coefficient growth bound on `PowerSeries ℂ` (closed under `C`, `X`, `expNegT`, `+`, `*`). -/
@[expose] def GeomCoeffBound (S : PowerSeries ℂ) : Prop :=
  ∃ C > 0, ∃ M ≥ 1, ∀ k : ℕ, ‖PowerSeries.coeff k S‖ ≤ C * M ^ k

lemma geomCoeffBound_C (c : ℂ) : GeomCoeffBound (PowerSeries.C c) := by
  refine ⟨‖c‖ + 1, by positivity, 1, le_rfl, fun k => ?_⟩
  cases k with
  | zero => simp
  | succ k => simp; positivity

lemma geomCoeffBound_X : GeomCoeffBound (PowerSeries.X : PowerSeries ℂ) := by
  refine ⟨1, zero_lt_one, 1, le_rfl, fun k => ?_⟩
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

lemma geomCoeffBound_expNegT : GeomCoeffBound expNegT := by
  refine ⟨1, zero_lt_one, 1, le_rfl, fun k => ?_⟩
  simp only [expNegT, PowerSeries.coeff_mk, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_natCast, mul_one]
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.factorial_pos k

lemma geomCoeffBound_add {S T : PowerSeries ℂ} (hS : GeomCoeffBound S) (hT : GeomCoeffBound T) :
    GeomCoeffBound (S + T) := by
  rcases hS with ⟨CS, hCS, MS, hMS, hbS⟩
  rcases hT with ⟨CT, hCT, MT, hMT, hbT⟩
  let M := max MS MT
  refine ⟨CS + CT, add_pos hCS hCT, M, hMS.trans (le_max_left _ _), fun k => ?_⟩
  rw [map_add]
  have h1 : ‖PowerSeries.coeff k S‖ ≤ CS * M ^ k :=
    (hbS k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (le_max_left _ _) k) hCS.le)
  have h2 : ‖PowerSeries.coeff k T‖ ≤ CT * M ^ k :=
    (hbT k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (le_max_right _ _) k) hCT.le)
  calc ‖PowerSeries.coeff k S + PowerSeries.coeff k T‖
      ≤ ‖PowerSeries.coeff k S‖ + ‖PowerSeries.coeff k T‖ := norm_add_le _ _
    _ ≤ CS * M ^ k + CT * M ^ k := add_le_add h1 h2
    _ = (CS + CT) * M ^ k := by ring

lemma geomCoeffBound_mul {S T : PowerSeries ℂ} (hS : GeomCoeffBound S) (hT : GeomCoeffBound T) :
    GeomCoeffBound (S * T) := by
  rcases hS with ⟨CS, hCS, MS, hMS, hbS⟩
  rcases hT with ⟨CT, hCT, MT, hMT, hbT⟩
  let M := max MS MT
  have hM1 : 1 ≤ M := hMS.trans (le_max_left _ _)
  refine ⟨CS * CT, mul_pos hCS hCT, 2 * M, by linarith, fun k => ?_⟩
  rw [PowerSeries.coeff_mul]
  calc ‖∑ p ∈ Finset.antidiagonal k, PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T‖
      ≤ ∑ p ∈ Finset.antidiagonal k, ‖PowerSeries.coeff p.1 S‖ * ‖PowerSeries.coeff p.2 T‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => by rw [norm_mul])
    _ ≤ ∑ _p ∈ Finset.antidiagonal k, (CS * CT) * M ^ k := by
        refine Finset.sum_le_sum fun p hp => ?_
        have h1 : ‖PowerSeries.coeff p.1 S‖ ≤ CS * M ^ p.1 :=
          (hbS p.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (le_max_left _ _) p.1) hCS.le)
        have h2 : ‖PowerSeries.coeff p.2 T‖ ≤ CT * M ^ p.2 :=
          (hbT p.2).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (le_max_right _ _) p.2) hCT.le)
        calc ‖PowerSeries.coeff p.1 S‖ * ‖PowerSeries.coeff p.2 T‖
            ≤ (CS * M ^ p.1) * (CT * M ^ p.2) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = (CS * CT) * (M ^ p.1 * M ^ p.2) := by ring
          _ = (CS * CT) * M ^ k := by rw [← pow_add, Finset.mem_antidiagonal.mp hp]
    _ = ((k : ℝ) + 1) * ((CS * CT) * M ^ k) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; rfl
    _ ≤ (2 : ℝ) ^ k * ((CS * CT) * M ^ k) :=
        mul_le_mul_of_nonneg_right (nat_succ_le_two_pow k) (by positivity)
    _ = (CS * CT) * (2 * M) ^ k := by rw [mul_pow]; ring

lemma geomCoeffBound_pow {S : PowerSeries ℂ} (hS : GeomCoeffBound S) (n : ℕ) :
    GeomCoeffBound (S ^ n) := by
  induction n with
  | zero => simpa using geomCoeffBound_C 1
  | succ n ih => rw [pow_succ]; exact geomCoeffBound_mul ih hS

lemma geomCoeffBound_polyToPS (p : Polynomial ℂ) :
    GeomCoeffBound (Polynomial.aeval (PowerSeries.X : PowerSeries ℂ) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact geomCoeffBound_add hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, PowerSeries.algebraMap_apply]
    exact geomCoeffBound_mul (geomCoeffBound_C a) (geomCoeffBound_pow geomCoeffBound_X n)

lemma absAt_expNegT (t : ℂ) : PrimeNome.AbsAt expNegT t ∧ PrimeNome.value expNegT t = Complex.exp (-t) := by
  have hhs := NormedSpace.expSeries_div_hasSum_exp (-t)
  rw [← Complex.exp_eq_exp_ℂ] at hhs
  have hnorm : Summable (fun k : ℕ => ‖PrimeNome.term expNegT t k‖) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp ‖t‖).summable
    refine h.congr fun k => ?_
    simp only [PrimeNome.term, expNegT, PowerSeries.coeff_mk, norm_mul, norm_div, norm_pow,
      norm_neg, norm_one, one_pow, Complex.norm_natCast]
    ring
  refine ⟨hnorm, ?_⟩
  rw [← hhs.tsum_eq]
  dsimp only [PrimeNome.value]
  refine tsum_congr fun k => ?_
  simp only [PrimeNome.term, expNegT, PowerSeries.coeff_mk]
  rw [neg_eq_neg_one_mul, mul_pow]; ring

lemma absAt_of_geomCoeffBound {S : PowerSeries ℂ} {C M : ℝ} (hC : 0 < C) (hM : 1 ≤ M)
    (hb : ∀ k : ℕ, ‖PowerSeries.coeff k S‖ ≤ C * M ^ k) {t : ℂ} (ht : ‖t‖ ≤ (2 * M)⁻¹) :
    PrimeNome.AbsAt S t := by
  have hsum : Summable (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
  dsimp only [PrimeNome.term]
  rw [norm_mul, norm_pow]
  have hMt : M * ‖t‖ ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ M by linarith)
    calc M * ‖t‖ ≤ M * (2 * M)⁻¹ := h1
      _ = 1 / 2 := by field_simp [show M ≠ 0 by linarith]
  calc ‖PowerSeries.coeff k S‖ * ‖t‖ ^ k
      ≤ (C * M ^ k) * ‖t‖ ^ k := mul_le_mul_of_nonneg_right (hb k) (by positivity)
    _ = C * (M * ‖t‖) ^ k := by rw [mul_pow]; ring
    _ ≤ C * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMt k) hC.le

lemma norm_value_sub_lead_le_of_geom {S : PowerSeries ℂ} {C M : ℝ} (hC : 0 < C) (hM : 1 ≤ M)
    (hb : ∀ k : ℕ, ‖PowerSeries.coeff k S‖ ≤ C * M ^ k) {k₀ : ℕ}
    (hlow : ∀ k < k₀, PowerSeries.coeff k S = 0) {t : ℂ} (ht : ‖t‖ ≤ (2 * M)⁻¹) :
    ‖PrimeNome.value S t - PowerSeries.coeff k₀ S * t ^ k₀‖ ≤
      (2 * C * M ^ (k₀ + 1)) * ‖t‖ ^ (k₀ + 1) := by
  have habs := absAt_of_geomCoeffBound hC hM hb ht
  have hsplit := habs.of_norm.sum_add_tsum_nat_add (k₀ + 1)
  have hfin : ∑ k ∈ Finset.range (k₀ + 1), PrimeNome.term S t k = PowerSeries.coeff k₀ S * t ^ k₀ := by
    rw [Finset.sum_range_succ]
    have hprev : ∑ k ∈ Finset.range k₀, PrimeNome.term S t k = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [PrimeNome.term, hlow k (Finset.mem_range.mp hk)]
    rw [hprev, zero_add]; rfl
  have hdiff : PrimeNome.value S t - PowerSeries.coeff k₀ S * t ^ k₀ =
      ∑' m : ℕ, PrimeNome.term S t (m + (k₀ + 1)) := by
    dsimp only [PrimeNome.value]; rw [← hsplit, hfin]; ring
  rw [hdiff]
  have hMt : M * ‖t‖ ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ M by linarith)
    calc M * ‖t‖ ≤ M * (2 * M)⁻¹ := h1
      _ = 1 / 2 := by field_simp [show M ≠ 0 by linarith]
  have hmaj_sum : Summable (fun m : ℕ => (C * M ^ (k₀ + 1) * ‖t‖ ^ (k₀ + 1)) * (1 / 2 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm : ∀ m : ℕ, ‖PrimeNome.term S t (m + (k₀ + 1))‖ ≤
      (C * M ^ (k₀ + 1) * ‖t‖ ^ (k₀ + 1)) * (1 / 2 : ℝ) ^ m := by
    intro m
    dsimp only [PrimeNome.term]
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff (m + (k₀ + 1)) S‖ * ‖t‖ ^ (m + (k₀ + 1))
        ≤ (C * M ^ (m + (k₀ + 1))) * ‖t‖ ^ (m + (k₀ + 1)) :=
          mul_le_mul_of_nonneg_right (hb _) (by positivity)
      _ = (C * M ^ (k₀ + 1) * ‖t‖ ^ (k₀ + 1)) * (M * ‖t‖) ^ m := by
          rw [pow_add, pow_add, mul_pow]; ring
      _ ≤ (C * M ^ (k₀ + 1) * ‖t‖ ^ (k₀ + 1)) * (1 / 2 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMt m) (by positivity)
  have hsum_sh : Summable (fun m : ℕ => ‖PrimeNome.term S t (m + (k₀ + 1))‖) :=
    hmaj_sum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc ‖∑' m : ℕ, PrimeNome.term S t (m + (k₀ + 1))‖
      ≤ ∑' m : ℕ, ‖PrimeNome.term S t (m + (k₀ + 1))‖ := norm_tsum_le_tsum_norm hsum_sh
    _ ≤ ∑' m : ℕ, (C * M ^ (k₀ + 1) * ‖t‖ ^ (k₀ + 1)) * (1 / 2 : ℝ) ^ m :=
        hsum_sh.tsum_le_tsum hterm hmaj_sum
    _ = (C * M ^ (k₀ + 1) * ‖t‖ ^ (k₀ + 1)) * (1 - (1 / 2 : ℝ))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (2 * C * M ^ (k₀ + 1)) * ‖t‖ ^ (k₀ + 1) := by norm_num; ring

lemma value_add_of_absAt {S T : PowerSeries ℂ} {t : ℂ} (hS : PrimeNome.AbsAt S t) (hT : PrimeNome.AbsAt T t) :
    PrimeNome.AbsAt (S + T) t ∧ PrimeNome.value (S + T) t = PrimeNome.value S t + PrimeNome.value T t := by
  have he : PrimeNome.term (S + T) t = fun n => PrimeNome.term S t n + PrimeNome.term T t n := by
    ext n; simp [PrimeNome.term, add_mul]
  exact ⟨by unfold PrimeNome.AbsAt; rw [he]; exact (hS.add hT).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _),
    by simp only [PrimeNome.value, he, hS.of_norm.tsum_add hT.of_norm]⟩

lemma value_mul_of_absAt {S T : PowerSeries ℂ} {t : ℂ} (hS : PrimeNome.AbsAt S t) (hT : PrimeNome.AbsAt T t) :
    PrimeNome.AbsAt (S * T) t ∧ PrimeNome.value (S * T) t = PrimeNome.value S t * PrimeNome.value T t := by
  have hconv (n : ℕ) : PrimeNome.term (S * T) t n =
      ∑ kl ∈ Finset.antidiagonal n, PrimeNome.term S t kl.1 * PrimeNome.term T t kl.2 := by
    rw [PrimeNome.term, PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.mem_antidiagonal.mp hkl, pow_add]; unfold PrimeNome.term; ring
  exact ⟨by simpa only [PrimeNome.AbsAt, hconv] using summable_norm_sum_mul_antidiagonal_of_summable_norm hS hT,
    by simpa only [PrimeNome.value, hconv] using (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hS hT).symm⟩

lemma value_C_absAt (c t : ℂ) : PrimeNome.AbsAt (PowerSeries.C c) t ∧ PrimeNome.value (PowerSeries.C c) t = c := by
  classical
  have he : PrimeNome.term (PowerSeries.C c) t = Pi.single 0 c := by
    ext n; by_cases hn : n = 0 <;> simp [PrimeNome.term, PowerSeries.coeff_C, hn]
  simp only [PrimeNome.AbsAt, PrimeNome.value, he, Pi.single_apply, apply_ite (fun z : ℂ => ‖z‖), norm_zero]
  refine ⟨summable_of_ne_finset_zero (s := {0}) (by simp_all), by simp⟩

lemma value_pow_of_absAt {S : PowerSeries ℂ} {t : ℂ} (hS : PrimeNome.AbsAt S t) (n : ℕ) :
    PrimeNome.AbsAt (S ^ n) t ∧ PrimeNome.value (S ^ n) t = PrimeNome.value S t ^ n := by
  induction n with
  | zero => simpa using value_C_absAt 1 t
  | succ n ih =>
    rw [pow_succ, pow_succ]
    have h := value_mul_of_absAt ih.1 hS
    exact ⟨h.1, by rw [h.2, ih.2]⟩

lemma value_polyToPS (p : Polynomial ℂ) (t : ℂ) :
    PrimeNome.AbsAt (Polynomial.aeval (PowerSeries.X : PowerSeries ℂ) p) t ∧
    PrimeNome.value (Polynomial.aeval (PowerSeries.X : PowerSeries ℂ) p) t = p.eval t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add]
    have h := value_add_of_absAt hp.1 hq.1
    exact ⟨h.1, by rw [h.2, hp.2, hq.2]⟩
  | monomial n a =>
    rw [Polynomial.aeval_monomial, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Polynomial.eval_monomial]
    have hX := value_pow_of_absAt (PrimeNome.nome_abs t).1 n
    have hmul := value_mul_of_absAt (value_C_absAt a t).1 hX.1
    exact ⟨hmul.1, by rw [hmul.2, (value_C_absAt a t).2, hX.2, (PrimeNome.nome_abs t).2]⟩

/-- Unitriangular jet-conversion coefficients `jetLCoeff j k : Polynomial ℂ` encoding
`(d/dq)^j F(q) = t^{-(j+2)} q^{-j} ∑_{k=0}^j (jetLCoeff j k)(t) * D^k (t^2 F(q))`. -/
@[expose] def jetLCoeff : ℕ → ℕ → Polynomial ℂ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, k =>
      (Polynomial.C ((j + 2 : ℕ) : ℂ) - Polynomial.C (j : ℂ) * Polynomial.X) * jetLCoeff j k -
        Polynomial.X * Polynomial.derivative (jetLCoeff j k) +
        (if k = 0 then 0 else jetLCoeff j (k - 1))

lemma jetLCoeff_eq_zero_of_lt : ∀ j k : ℕ, j < k → jetLCoeff j k = 0 := by
  intro j
  induction j with
  | zero =>
    intro k hk; simp [jetLCoeff, Nat.ne_of_gt hk]
  | succ j ih =>
    intro k hk
    have hk0 : k ≠ 0 := by omega
    simp only [jetLCoeff, hk0, ↓reduceIte, ih k (by omega), ih (k - 1) (by omega),
      mul_zero, map_zero, sub_zero, add_zero]

lemma jetLCoeff_diag : ∀ j : ℕ, jetLCoeff j j = 1 := by
  intro j
  induction j with
  | zero => simp [jetLCoeff]
  | succ j ih =>
    simp only [jetLCoeff, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      jetLCoeff_eq_zero_of_lt j (j + 1) (Nat.lt_succ_self j), mul_zero, map_zero, sub_zero, zero_add]
    exact ih

/-- Exact analytic conversion from `q`-jets `F^{(j)}(qRay u)` to `u`-jets `D^k (t^2 F(qRay u))`. -/
theorem seriesJet_eq_jetLCoeff_sum {F : PowerSeries ℂ} (hF : PrimeNome.DiskCoeffBound F) (j : ℕ) (u : ℝ) :
    let S : ℝ → ℂ := fun v => PrimeNome.tRay v ^ 2 * PrimeNome.value F (PrimeNome.qRay v)
    PrimeNome.value (PrimeNome.seriesJet F j) (PrimeNome.qRay u) =
      (PrimeNome.tRay u)⁻¹ ^ (j + 2) * (PrimeNome.qRay u)⁻¹ ^ j *
        ∑ k ∈ Finset.range (j + 1), (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv k S u := by
  intro S
  have hS_an : ∀ v : ℝ, AnalyticAt ℝ S v := fun v =>
    ((PrimeNome.tRay_analytic v).pow 2).mul (PrimeNome.ray_source_analytic hF 1 v)
  have hS_diff : ∀ k : ℕ, ∀ v : ℝ, DifferentiableAt ℝ (iteratedDeriv k S) v := by
    intro k v
    have han : ∀ m : ℕ, ∀ w : ℝ, AnalyticAt ℝ (iteratedDeriv m S) w := by
      intro m
      induction m with
      | zero => simpa using hS_an
      | succ m ih => intro w; rw [iteratedDeriv_succ]; exact (ih w).deriv
    exact (han k v).differentiableAt
  induction j generalizing u with
  | zero =>
    simp only [PrimeNome.seriesJet, Function.iterate_zero, id_eq, zero_add, pow_zero, mul_one,
      Finset.range_one, Finset.sum_singleton, jetLCoeff, ↓reduceIte, Polynomial.eval_one,
      iteratedDeriv_zero, one_mul, S]
    have ht : PrimeNome.tRay u ≠ 0 := PrimeNome.tRay_ne_zero u
    field_simp [ht]
  | succ j ih =>
    -- Differentiate the `j`-th identity wrt `u` and divide by `tRay u * qRay u ≠ 0`
    have hLHS : HasDerivAt (fun v : ℝ => PrimeNome.value (PrimeNome.seriesJet F j) (PrimeNome.qRay v))
        (PrimeNome.tRay u * PrimeNome.qRay u * PrimeNome.value (PrimeNome.seriesJet F (j + 1)) (PrimeNome.qRay u)) u :=
      PrimeNome.ray_source_deriv hF j u
    have ht_ne : PrimeNome.tRay u ≠ 0 := PrimeNome.tRay_ne_zero u
    have hq_ne : PrimeNome.qRay u ≠ 0 := PrimeNome.qRay_ne_zero u
    have ht_inv : HasDerivAt (fun v : ℝ => (PrimeNome.tRay v)⁻¹) (PrimeNome.tRay u)⁻¹ u := by
      have h := (PrimeNome.tRay_deriv u).inv ht_ne
      refine h.congr_deriv ?_; field_simp [ht_ne]
    have hq_inv : HasDerivAt (fun v : ℝ => (PrimeNome.qRay v)⁻¹)
        (-(PrimeNome.tRay u * (PrimeNome.qRay u)⁻¹)) u := by
      have h := (PrimeNome.qRay_deriv u).inv hq_ne
      refine h.congr_deriv ?_; field_simp [hq_ne]
    have ht_pow : HasDerivAt (fun v : ℝ => (PrimeNome.tRay v)⁻¹ ^ (j + 2))
        (((j + 2 : ℕ) : ℂ) * (PrimeNome.tRay u)⁻¹ ^ (j + 2)) u := by
      have h := ht_inv.pow (j + 2)
      refine h.congr_deriv ?_
      change ((j + 2 : ℕ) : ℂ) * (PrimeNome.tRay u)⁻¹ ^ (j + 1) * (PrimeNome.tRay u)⁻¹ = _
      rw [pow_succ]; ring
    have hq_pow : HasDerivAt (fun v : ℝ => (PrimeNome.qRay v)⁻¹ ^ j)
        (-((j : ℂ) * PrimeNome.tRay u * (PrimeNome.qRay u)⁻¹ ^ j)) u := by
      cases j with
      | zero => simpa using hasDerivAt_const u (1 : ℂ)
      | succ m =>
        have h := hq_inv.pow (m + 1)
        refine h.congr_deriv ?_
        rw [pow_succ]; push_cast; ring
    have hsum_d : HasDerivAt
        (fun v : ℝ => ∑ k ∈ Finset.range (j + 1), (jetLCoeff j k).eval (PrimeNome.tRay v) * iteratedDeriv k S v)
        (∑ k ∈ Finset.range (j + 1),
          ((-(PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u))) * iteratedDeriv k S u +
            (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv (k + 1) S u)) u := by
      refine HasDerivAt.fun_sum fun k _ => ?_
      have hp_d : HasDerivAt (fun v : ℝ => (jetLCoeff j k).eval (PrimeNome.tRay v))
          (-(PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u))) u := by
        have h := ((jetLCoeff j k).hasDerivAt (PrimeNome.tRay u)).comp u (PrimeNome.tRay_deriv u)
        refine h.congr_deriv ?_; ring
      have hS_d : HasDerivAt (iteratedDeriv k S) (iteratedDeriv (k + 1) S u) u := by
        rw [iteratedDeriv_succ]; exact (hS_diff k u).hasDerivAt
      exact hp_d.mul hS_d
    have hRHS := (ht_pow.mul hq_pow).mul hsum_d
    have hfun_eq : (fun v : ℝ => PrimeNome.value (PrimeNome.seriesJet F j) (PrimeNome.qRay v)) =
        fun v : ℝ => (PrimeNome.tRay v)⁻¹ ^ (j + 2) * (PrimeNome.qRay v)⁻¹ ^ j *
          ∑ k ∈ Finset.range (j + 1), (jetLCoeff j k).eval (PrimeNome.tRay v) * iteratedDeriv k S v :=
      funext ih
    rw [hfun_eq] at hLHS
    have hderiv_eq := hLHS.unique hRHS
    -- Algebraically identify RHS derivative with `tRay * qRay * (tRay⁻¹^(j+3) * qRay⁻¹^(j+1) * ∑_{k ≤ j+1} jetLCoeff (j+1) k * D^k S)`
    have hsum_step :
        ∑ k ∈ Finset.range (j + 2), (jetLCoeff (j + 1) k).eval (PrimeNome.tRay u) * iteratedDeriv k S u =
        (((j + 2 : ℕ) : ℂ) - (j : ℂ) * PrimeNome.tRay u) *
            (∑ k ∈ Finset.range (j + 1), (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv k S u) +
          ∑ k ∈ Finset.range (j + 1),
            ((-(PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u))) * iteratedDeriv k S u +
              (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv (k + 1) S u) := by
      have hsplit : ∑ k ∈ Finset.range (j + 2), (jetLCoeff (j + 1) k).eval (PrimeNome.tRay u) * iteratedDeriv k S u =
          (∑ k ∈ Finset.range (j + 2),
            ((((j + 2 : ℕ) : ℂ) - (j : ℂ) * PrimeNome.tRay u) * (jetLCoeff j k).eval (PrimeNome.tRay u) -
              PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u)) * iteratedDeriv k S u) +
          (∑ k ∈ Finset.range (j + 2),
            (if k = 0 then (0 : ℂ) else (jetLCoeff j (k - 1)).eval (PrimeNome.tRay u)) * iteratedDeriv k S u) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp only [jetLCoeff]
        simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
        split_ifs
        · simp
        · ring
      rw [hsplit]
      have hpart1 : (∑ k ∈ Finset.range (j + 2),
            ((((j + 2 : ℕ) : ℂ) - (j : ℂ) * PrimeNome.tRay u) * (jetLCoeff j k).eval (PrimeNome.tRay u) -
              PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u)) * iteratedDeriv k S u) =
          ∑ k ∈ Finset.range (j + 1),
            ((((j + 2 : ℕ) : ℂ) - (j : ℂ) * PrimeNome.tRay u) * (jetLCoeff j k).eval (PrimeNome.tRay u) -
              PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u)) * iteratedDeriv k S u := by
        rw [Finset.sum_range_succ, jetLCoeff_eq_zero_of_lt j (j + 1) (Nat.lt_succ_self j)]
        simp
      have hpart2 : (∑ k ∈ Finset.range (j + 2),
            (if k = 0 then (0 : ℂ) else (jetLCoeff j (k - 1)).eval (PrimeNome.tRay u)) * iteratedDeriv k S u) =
          ∑ k ∈ Finset.range (j + 1), (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv (k + 1) S u := by
        rw [Finset.sum_range_succ']
        simp
      rw [hpart1, hpart2, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    have htq_ne : PrimeNome.tRay u * PrimeNome.qRay u ≠ 0 := mul_ne_zero ht_ne hq_ne
    apply mul_left_cancel₀ htq_ne
    rw [hderiv_eq, hsum_step]
    have hpow_t : PrimeNome.tRay u * (PrimeNome.tRay u)⁻¹ ^ (j + 3) = (PrimeNome.tRay u)⁻¹ ^ (j + 2) := by
      rw [pow_succ']; field_simp [ht_ne]
    have hpow_q : PrimeNome.qRay u * (PrimeNome.qRay u)⁻¹ ^ (j + 1) = (PrimeNome.qRay u)⁻¹ ^ j := by
      rw [pow_succ']; field_simp [hq_ne]
    calc _ = ((PrimeNome.tRay u)⁻¹ ^ (j + 2) * (PrimeNome.qRay u)⁻¹ ^ j) *
            ((((j + 2 : ℕ) : ℂ) - (j : ℂ) * PrimeNome.tRay u) *
                (∑ k ∈ Finset.range (j + 1), (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv k S u) +
              ∑ k ∈ Finset.range (j + 1),
                (-(PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u)) * iteratedDeriv k S u +
                  (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv (k + 1) S u)) := by
            dsimp only [Pi.mul_apply]; ring
      _ = (PrimeNome.tRay u * PrimeNome.qRay u) *
            ((PrimeNome.tRay u)⁻¹ ^ (j + 3) * (PrimeNome.qRay u)⁻¹ ^ (j + 1) *
              ((((j + 2 : ℕ) : ℂ) - (j : ℂ) * PrimeNome.tRay u) *
                  (∑ k ∈ Finset.range (j + 1), (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv k S u) +
                ∑ k ∈ Finset.range (j + 1),
                  (-(PrimeNome.tRay u * (Polynomial.derivative (jetLCoeff j k)).eval (PrimeNome.tRay u)) * iteratedDeriv k S u +
                    (jetLCoeff j k).eval (PrimeNome.tRay u) * iteratedDeriv (k + 1) S u))) := by
          rw [← mul_assoc (PrimeNome.tRay u * PrimeNome.qRay u),
            show PrimeNome.tRay u * PrimeNome.qRay u * ((PrimeNome.tRay u)⁻¹ ^ (j + 3) * (PrimeNome.qRay u)⁻¹ ^ (j + 1)) =
              (PrimeNome.tRay u * (PrimeNome.tRay u)⁻¹ ^ (j + 3)) * (PrimeNome.qRay u * (PrimeNome.qRay u)⁻¹ ^ (j + 1)) by ring,
            hpow_t, hpow_q]

/-- Subring of globally absolutely convergent power series `S ∈ ℂ[[t]]` (`∀ t : ℂ, AbsAt S t`)
whose coefficients also satisfy `GeomCoeffBound`. -/
@[expose] def GeomEntirePS : Subring (PowerSeries ℂ) where
  carrier := {S : PowerSeries ℂ | (∀ t : ℂ, PrimeNome.AbsAt S t) ∧ GeomCoeffBound S}
  mul_mem' hS hT := ⟨fun t => (value_mul_of_absAt (hS.1 t) (hT.1 t)).1, geomCoeffBound_mul hS.2 hT.2⟩
  one_mem' := ⟨fun t => by simpa using (value_C_absAt 1 t).1, by simpa using geomCoeffBound_C 1⟩
  add_mem' hS hT := ⟨fun t => (value_add_of_absAt (hS.1 t) (hT.1 t)).1, geomCoeffBound_add hS.2 hT.2⟩
  zero_mem' := ⟨fun t => by simpa using (value_C_absAt 0 t).1, by simpa using geomCoeffBound_C 0⟩
  neg_mem' hS := ⟨fun t => (hS.1 t).congr fun n => by simp [PrimeNome.term], by
    rcases hS.2 with ⟨C, hC, M, hM, hb⟩
    exact ⟨C, hC, M, hM, fun k => by simpa using hb k⟩⟩

@[expose] def geomValHom (t : ℂ) : GeomEntirePS →+* ℂ where
  toFun S := PrimeNome.value S.1 t
  map_one' := by simpa using (value_C_absAt 1 t).2
  map_mul' S T := (value_mul_of_absAt (S.2.1 t) (T.2.1 t)).2
  map_zero' := by simpa using (value_C_absAt 0 t).2
  map_add' S T := (value_add_of_absAt (S.2.1 t) (T.2.1 t)).2

@[expose] def geC (c : ℂ) : GeomEntirePS :=
  ⟨PowerSeries.C c, fun t => (value_C_absAt c t).1, geomCoeffBound_C c⟩

@[expose] def geX : GeomEntirePS :=
  ⟨PowerSeries.X, fun t => (PrimeNome.nome_abs t).1, geomCoeffBound_X⟩

@[expose] def geExpNegT : GeomEntirePS :=
  ⟨expNegT, fun t => (absAt_expNegT t).1, geomCoeffBound_expNegT⟩

@[expose] def gePoly (p : Polynomial ℂ) : GeomEntirePS :=
  ⟨Polynomial.aeval (PowerSeries.X : PowerSeries ℂ) p,
    fun t => (value_polyToPS p t).1, geomCoeffBound_polyToPS p⟩

/-- Unitriangular back-substitution: for fixed `t ≠ 0` and target vector `z : Fin d × Fin (r + 1) → ℂ`,
find `x : Fin d × Fin (r + 1) → ℂ` solving `∑_{k ≤ j} (jetLCoeff j k).eval t * x (i, k) = t^(j+2) * exp(-j*t) * z (i, j)`. -/
def backSubVec {d r : ℕ} (t : ℂ) (z : Fin d × Fin (r + 1) → ℂ) (i : Fin d) : ℕ → ℂ
  | 0 => t ^ 2 * z (i, ⟨0, Nat.succ_pos r⟩)
  | j + 1 =>
      if h : j + 1 < r + 1 then
        t ^ (j + 3) * Complex.exp (-((j + 1 : ℕ) : ℂ) * t) * z (i, ⟨j + 1, h⟩) -
          ∑ k : Fin (j + 1), (jetLCoeff (j + 1) k.val).eval t * backSubVec t z i k.val
      else 0
termination_by j => j
decreasing_by exact k.isLt

lemma backSubVec_spec {d r : ℕ} (t : ℂ) (z : Fin d × Fin (r + 1) → ℂ) (i : Fin d) (j : Fin (r + 1)) :
    (∑ k ∈ Finset.range (j.val + 1), (jetLCoeff j.val k).eval t * backSubVec t z i k) =
      t ^ (j.val + 2) * Complex.exp (-(j.val : ℂ) * t) * z (i, j) := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
    simp [backSubVec, jetLCoeff]
  | succ m =>
    rw [Finset.sum_range_succ, jetLCoeff_diag (m + 1), Polynomial.eval_one, one_mul]
    have hsum_fin : (∑ k : Fin (m + 1), (jetLCoeff (m + 1) k.val).eval t * backSubVec t z i k.val) =
        ∑ k ∈ Finset.range (m + 1), (jetLCoeff (m + 1) k).eval t * backSubVec t z i k :=
      Fin.sum_univ_eq_sum_range (fun k => (jetLCoeff (m + 1) k).eval t * backSubVec t z i k) (m + 1)
    rw [backSubVec]
    simp only [hj, ↓reduceDIte, hsum_fin]
    push_cast; ring

/-- **Master Pullback Theorem (`distinctDensity_ogf_joint_algebraicIndependent_of_asymp`)**:
If finitely many sequences `a_i` satisfy `HasScaledDensityAsymp (a i) (δ i)` with pairwise
distinct positive densities `δ : Fin d → ℝ`, then their ordinary generating functions
`F_i(q) = ∑_{n ≥ 0} a_{i, n} q^{n+1}` are jointly differentially algebraically independent over `ℂ(q)`! -/
theorem distinctDensity_ogf_joint_algebraicIndependent_of_asymp
    {d : ℕ} (a : Fin d → ℕ → ℕ) (δ : Fin d → ℝ)
    (hasymp : ∀ i, HasScaledDensityAsymp (a i) (δ i))
    (hinj : Function.Injective δ) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i => seqSeries (a i))) := by
  classical
  have hδ_pos : ∀ i, 0 < δ i := fun i => (hasymp i).1
  have hdisk : ∀ i, PrimeNome.DiskCoeffBound (seqSeries (a i)) := fun i => (hasymp i).2.1.to_diskCoeffBound
  rw [algebraicIndependent_iff]
  intro Q hQ_zero
  by_contra hQ_ne
  -- Step 1: Restrict `Q` to finite jet order `r`
  let r : ℕ := Q.vars.sup fun v => match v with | none => 0 | some (_, j) => j
  let emb : Option (Fin d × Fin (r + 1)) → Option (Fin d × ℕ) :=
    fun v => match v with | none => none | some (i, j) => some (i, j.val)
  have hemb_inj : Function.Injective emb := by
    intro v₁ v₂ h
    cases v₁ with
    | none => cases v₂ with | none => rfl | some _ => simp [emb] at h
    | some p₁ => cases v₂ with
      | none => simp [emb] at h
      | some p₂ =>
        simp only [emb, Option.some.injEq, Prod.mk.injEq] at h
        exact congrArg some (Prod.ext h.1 (Fin.ext h.2))
  have hsub : ↑Q.vars ⊆ Set.range emb := by
    intro v hv
    cases v with
    | none => exact ⟨none, rfl⟩
    | some p =>
      have hp_le : p.2 ≤ r :=
        Finset.le_sup (f := fun v : Option (Fin d × ℕ) => match v with | none => 0 | some (_, j) => j)
          (Finset.mem_coe.mp hv)
      exact ⟨some (p.1, ⟨p.2, Nat.lt_succ_of_le hp_le⟩), rfl⟩
  obtain ⟨Q₁, hQ₁⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q emb hemb_inj hsub
  have hQ₁_ne : Q₁ ≠ 0 := by intro h0; apply hQ_ne; rw [← hQ₁, h0, map_zero]
  -- Evaluate `Q₁ = 0` along `q = qRay u`
  have hQ₁_ray : ∀ u : ℝ,
      MvPolynomial.eval (fun v : Option (Fin d × Fin (r + 1)) =>
        match v with
        | none => PrimeNome.qRay u
        | some (i, j) => PrimeNome.value (PrimeNome.seriesJet (seqSeries (a i)) j.val) (PrimeNome.qRay u)) Q₁ = 0 := by
    intro u
    have hq := PrimeNome.qRay_disk u
    have habs : ∀ v : Option (Fin d × ℕ), PrimeNome.AbsAt (jointSeriesCoordinates (fun i => seqSeries (a i)) v) (PrimeNome.qRay u) := by
      intro v
      cases v with
      | none => exact (PrimeNome.nome_abs _).1
      | some p => exact PrimeNome.seriesJet_abs (hdisk p.1) p.2 hq
    have hv := (PrimeNome.polynomial_value Q habs).2
    rw [hQ_zero] at hv
    have hval0 : PrimeNome.value (0 : PowerSeries ℂ) (PrimeNome.qRay u) = 0 := by simp [PrimeNome.value, PrimeNome.term]
    rw [hval0] at hv
    have h1 : MvPolynomial.eval (fun v => PrimeNome.value (jointSeriesCoordinates (fun i => seqSeries (a i)) v) (PrimeNome.qRay u)) Q = 0 := hv.symm
    rw [← hQ₁, MvPolynomial.eval_rename] at h1
    refine h1.symm.trans (congrArg (fun f => MvPolynomial.eval f Q₁) (funext fun v => ?_)) |>.symm
    cases v with
    | none => exact (PrimeNome.nome_abs _).2
    | some p => rfl
  -- Step 2: Construct denominator-cleared `R_poly ∈ MvPolynomial (Fin d × Fin (r + 1)) GeomEntirePS`
  let D : ℕ := Q₁.totalDegree
  let M : ℕ := (r + 2) * D
  let N : ℕ := r * D
  let wt_t : (Option (Fin d × Fin (r + 1)) →₀ ℕ) → ℕ :=
    fun m => ∑ p : Fin d × Fin (r + 1), (p.2.val + 2) * m (some p)
  let wt_q : (Option (Fin d × Fin (r + 1)) →₀ ℕ) → ℕ :=
    fun m => ∑ p : Fin d × Fin (r + 1), p.2.val * m (some p)
  have hwt_t_le : ∀ m ∈ Q₁.support, wt_t m ≤ M := by
    intro m hm
    have hdeg : ∑ v : Option (Fin d × Fin (r + 1)), m v ≤ D := by
      have h1 := MvPolynomial.le_totalDegree hm
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    have hsum_some : ∑ p : Fin d × Fin (r + 1), m (some p) ≤ D := by
      have h1 : (∑ v : Option (Fin d × Fin (r + 1)), m v) = m none + ∑ p : Fin d × Fin (r + 1), m (some p) :=
        Fintype.sum_option m
      omega
    calc wt_t m ≤ ∑ p : Fin d × Fin (r + 1), (r + 2) * m (some p) :=
          Finset.sum_le_sum fun p _ => Nat.mul_le_mul_right _ (by omega)
      _ = (r + 2) * ∑ p : Fin d × Fin (r + 1), m (some p) := (Finset.mul_sum _ _ _).symm
      _ ≤ (r + 2) * D := Nat.mul_le_mul_left _ hsum_some
  have hwt_q_le : ∀ m ∈ Q₁.support, wt_q m ≤ N := by
    intro m hm
    have hdeg : ∑ v : Option (Fin d × Fin (r + 1)), m v ≤ D := by
      have h1 := MvPolynomial.le_totalDegree hm
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    have hsum_some : ∑ p : Fin d × Fin (r + 1), m (some p) ≤ D := by
      have h1 : (∑ v : Option (Fin d × Fin (r + 1)), m v) = m none + ∑ p : Fin d × Fin (r + 1), m (some p) :=
        Fintype.sum_option m
      omega
    calc wt_q m ≤ ∑ p : Fin d × Fin (r + 1), r * m (some p) :=
          Finset.sum_le_sum fun p _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp p.2.isLt)
      _ = r * ∑ p : Fin d × Fin (r + 1), m (some p) := (Finset.mul_sum _ _ _).symm
      _ ≤ r * D := Nat.mul_le_mul_left _ hsum_some
  let L_poly : Fin d × Fin (r + 1) → MvPolynomial (Fin d × Fin (r + 1)) GeomEntirePS :=
    fun p => ∑ k : Fin (r + 1),
      if k.val ≤ p.2.val then
        MvPolynomial.C (gePoly (jetLCoeff p.2.val k.val)) * MvPolynomial.X (p.1, k)
      else 0
  let R_poly : MvPolynomial (Fin d × Fin (r + 1)) GeomEntirePS :=
    ∑ m ∈ Q₁.support,
      MvPolynomial.C (geC (Q₁.coeff m) * geX ^ (M - wt_t m) * geExpNegT ^ (m none + (N - wt_q m))) *
      ∏ p : Fin d × Fin (r + 1), (L_poly p) ^ (m (some p))
  -- Step 3: Exact algebraic evaluation of `R_poly` at ANY `t ≠ 0` and ANY `x`
  have hL_eval : ∀ (t : ℂ) (x : Fin d × Fin (r + 1) → ℂ) (p : Fin d × Fin (r + 1)),
      MvPolynomial.eval₂ (geomValHom t) x (L_poly p) =
        ∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0 := by
    intro t x p
    dsimp only [L_poly]
    rw [MvPolynomial.eval₂_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
      exact congrArg (· * x (p.1, k)) (value_polyToPS (jetLCoeff p.2.val k.val) t).2
    · rw [MvPolynomial.eval₂_zero]
  have hR_eval : ∀ (t : ℂ), t ≠ 0 → ∀ x : Fin d × Fin (r + 1) → ℂ,
      MvPolynomial.eval₂ (geomValHom t) x R_poly =
      t ^ M * Complex.exp (-t) ^ N *
        MvPolynomial.eval (fun v : Option (Fin d × Fin (r + 1)) =>
          match v with
          | none => Complex.exp (-t)
          | some p => t⁻¹ ^ (p.2.val + 2) * (Complex.exp (-t))⁻¹ ^ p.2.val *
              (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0)) Q₁ := by
    intro t ht0 x
    have hexp_ne : Complex.exp (-t) ≠ 0 := Complex.exp_ne_zero (-t)
    dsimp only [R_poly]
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, map_mul, map_mul, map_pow, map_pow, MvPolynomial.eval₂_prod]
    have hC_v : geomValHom t (geC (Q₁.coeff m)) = Q₁.coeff m := (value_C_absAt (Q₁.coeff m) t).2
    have hX_v : geomValHom t geX = t := (PrimeNome.nome_abs t).2
    have hE_v : geomValHom t geExpNegT = Complex.exp (-t) := (absAt_expNegT t).2
    rw [hC_v, hX_v, hE_v]
    have hprod_L : (∏ p : Fin d × Fin (r + 1), MvPolynomial.eval₂ (geomValHom t) x (L_poly p ^ m (some p))) =
        ∏ p : Fin d × Fin (r + 1),
          (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0) ^ m (some p) := by
      refine Finset.prod_congr rfl fun p _ => by rw [MvPolynomial.eval₂_pow, hL_eval]
    rw [hprod_L]
    have hprod_Q : (∏ v : Option (Fin d × Fin (r + 1)),
          (match v with
            | none => Complex.exp (-t)
            | some p => t⁻¹ ^ (p.2.val + 2) * (Complex.exp (-t))⁻¹ ^ p.2.val *
                (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0)) ^ m v) =
        Complex.exp (-t) ^ m none * (t⁻¹ ^ wt_t m * (Complex.exp (-t))⁻¹ ^ wt_q m) *
          ∏ p : Fin d × Fin (r + 1),
            (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0) ^ m (some p) := by
      rw [Fintype.prod_option]
      simp_rw [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      dsimp only [wt_t, wt_q]; ring
    rw [hprod_Q]
    have hwt_t_id : t ^ M * t⁻¹ ^ wt_t m = t ^ (M - wt_t m) := by
      have hle := hwt_t_le m hm
      rw [inv_pow, ← div_eq_mul_inv]
      conv_lhs => rw [show M = (M - wt_t m) + wt_t m from (Nat.sub_add_cancel hle).symm]
      rw [pow_add, mul_div_cancel_right₀ _ (pow_ne_zero _ ht0)]
    have hwt_q_id : Complex.exp (-t) ^ N * Complex.exp (-t) ^ m none * (Complex.exp (-t))⁻¹ ^ wt_q m =
        Complex.exp (-t) ^ (m none + (N - wt_q m)) := by
      have hle := hwt_q_le m hm
      rw [inv_pow, pow_add]
      conv_lhs => rw [show N = (N - wt_q m) + wt_q m from (Nat.sub_add_cancel hle).symm]
      rw [pow_add]
      field_simp [hexp_ne]
    calc Q₁.coeff m * t ^ (M - wt_t m) * Complex.exp (-t) ^ (m none + (N - wt_q m)) *
            ∏ p : Fin d × Fin (r + 1),
              (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0) ^ m (some p)
        = Q₁.coeff m * (t ^ M * t⁻¹ ^ wt_t m) *
            (Complex.exp (-t) ^ N * Complex.exp (-t) ^ m none * (Complex.exp (-t))⁻¹ ^ wt_q m) *
            ∏ p : Fin d × Fin (r + 1),
              (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0) ^ m (some p) := by
          rw [hwt_t_id, hwt_q_id]
      _ = _ := by ring
  -- Step 4: `R_poly ≠ 0` by triangular back-substitution + `MvPolynomial.funext_set`!
  have hR_ne : R_poly ≠ 0 := by
    intro hR0
    apply hQ₁_ne
    let S_q : Set ℂ := Set.range (fun n : ℕ => Complex.exp (-(((n + 1 : ℕ) : ℝ) : ℂ)))
    have hSq_inf : S_q.Infinite := by
      refine Set.infinite_range_of_injective fun m n h => ?_
      have hm_eq : Complex.exp (-(((m + 1 : ℕ) : ℝ) : ℂ)) = ((Real.exp (-((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
      have hn_eq : Complex.exp (-(((n + 1 : ℕ) : ℝ) : ℂ)) = ((Real.exp (-((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
      have hreal : Real.exp (-((m + 1 : ℕ) : ℝ)) = Real.exp (-((n + 1 : ℕ) : ℝ)) :=
        Complex.ofReal_injective (by rw [← hm_eq, ← hn_eq]; exact h)
      have hlin := Real.exp_injective hreal
      have hnat : (m + 1 : ℕ) = (n + 1 : ℕ) := by exact_mod_cast (by linarith : ((m + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ))
      omega
    refine MvPolynomial.funext_set
      (fun v => match v with | none => S_q | some _ => Set.univ)
      (fun v => by cases v <;> [exact hSq_inf; exact Set.infinite_univ])
      fun y hy => ?_
    obtain ⟨n, hn⟩ := hy none (Set.mem_univ none)
    let t : ℂ := (((n + 1 : ℕ) : ℝ) : ℂ)
    have ht0 : t ≠ 0 := by dsimp [t]; exact_mod_cast Nat.succ_ne_zero n
    let z : Fin d × Fin (r + 1) → ℂ := fun p => y (some p)
    let x : Fin d × Fin (r + 1) → ℂ := fun p => backSubVec t z p.1 p.2.val
    have heval0 : MvPolynomial.eval₂ (geomValHom t) x R_poly = 0 := by rw [hR0, MvPolynomial.eval₂_zero]
    rw [hR_eval t ht0 x] at heval0
    have hfac_ne : t ^ M * Complex.exp (-t) ^ N ≠ 0 :=
      mul_ne_zero (pow_ne_zero M ht0) (pow_ne_zero N (Complex.exp_ne_zero _))
    have hQ0 := (mul_eq_zero.mp heval0).resolve_left hfac_ne
    have hvec_eq : (fun v : Option (Fin d × Fin (r + 1)) =>
          match v with
          | none => Complex.exp (-t)
          | some p => t⁻¹ ^ (p.2.val + 2) * (Complex.exp (-t))⁻¹ ^ p.2.val *
              (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0)) = y := by
      ext v
      cases v with
      | none => exact hn
      | some p =>
        dsimp only
        have hbij : (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval t * x (p.1, k) else 0) =
            ∑ k ∈ Finset.range (p.2.val + 1), (jetLCoeff p.2.val k).eval t * backSubVec t z p.1 k := by
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
          · intro k₁ _ k₂ _ h; exact Fin.ext h
          · intro k hk
            have hkle : k ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            refine ⟨⟨k, lt_of_le_of_lt hkle p.2.isLt⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hkle
          · intro k _; rfl
        rw [hbij, backSubVec_spec t z p.1 p.2]
        have hexp_pow : (Complex.exp (-t))⁻¹ ^ p.2.val * Complex.exp (-(p.2.val : ℂ) * t) = 1 := by
          have h1 : Complex.exp (-(p.2.val : ℂ) * t) = Complex.exp (-t) ^ p.2.val := by
            rw [← Complex.exp_nat_mul]; congr 1; ring
          rw [h1, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]
        have ht_pow : t⁻¹ ^ (p.2.val + 2) * t ^ (p.2.val + 2) = 1 := by
          rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ ht0)]
        calc t⁻¹ ^ (p.2.val + 2) * (Complex.exp (-t))⁻¹ ^ p.2.val *
              (t ^ (p.2.val + 2) * Complex.exp (-(p.2.val : ℂ) * t) * z p)
            = (t⁻¹ ^ (p.2.val + 2) * t ^ (p.2.val + 2)) *
              ((Complex.exp (-t))⁻¹ ^ p.2.val * Complex.exp (-(p.2.val : ℂ) * t)) * z p := by ring
          _ = z p := by rw [ht_pow, hexp_pow, one_mul, one_mul]
    rwa [hvec_eq] at hQ0
  -- Step 5: Extract minimum `t`-adic order `k₀` among nonzero coefficients of `R_poly`, producing `P₀ ≠ 0`!
  have hsupp_ne : R_poly.support.Nonempty := MvPolynomial.support_nonempty.mpr hR_ne
  have hex_ord : ∀ s ∈ R_poly.support, ∃ k : ℕ, PowerSeries.coeff k (R_poly.coeff s).1 ≠ 0 := by
    intro s hs
    by_contra hall
    push Not at hall
    have h0 : (R_poly.coeff s).1 = 0 := by ext k; simpa using hall k
    exact MvPolynomial.mem_support_iff.mp hs (Subtype.ext h0)
  let ordS : ((Fin d × Fin (r + 1)) →₀ ℕ) → ℕ :=
    fun s => if hs : s ∈ R_poly.support then Nat.find (hex_ord s hs) else 0
  let k₀ : ℕ := R_poly.support.inf' hsupp_ne ordS
  have hk₀_le : ∀ s ∈ R_poly.support, k₀ ≤ ordS s := fun s hs => Finset.inf'_le ordS hs
  obtain ⟨s₀, hs₀_mem, hs₀_eq⟩ := Finset.exists_mem_eq_inf' hsupp_ne ordS
  let P₀ : MvPolynomial (Fin d × Fin (r + 1)) ℂ :=
    ∑ s ∈ R_poly.support, MvPolynomial.monomial s (PowerSeries.coeff k₀ (R_poly.coeff s).1)
  have hP₀_ne : P₀ ≠ 0 := by
    intro h0
    have hc0 : P₀.coeff s₀ = 0 := by rw [h0]; simp
    have hcs0 : P₀.coeff s₀ = PowerSeries.coeff k₀ (R_poly.coeff s₀).1 := by
      dsimp only [P₀]
      rw [MvPolynomial.coeff_sum, Finset.sum_eq_single s₀]
      · simp [MvPolynomial.coeff_monomial]
      · intro s _ hs; simp [MvPolynomial.coeff_monomial, hs]
      · intro hnot; exact absurd hs₀_mem hnot
    rw [hcs0] at hc0
    dsimp only [k₀] at hc0
    rw [hs₀_eq] at hc0
    have hspec : PowerSeries.coeff (ordS s₀) (R_poly.coeff s₀).1 ≠ 0 := by
      dsimp only [ordS]; simp only [hs₀_mem, ↓reduceDIte]; exact Nat.find_spec (hex_ord s₀ hs₀_mem)
    exact hspec hc0
  have hlow_zero : ∀ s ∈ R_poly.support, ∀ k < k₀, PowerSeries.coeff k (R_poly.coeff s).1 = 0 := by
    intro s hs k hk
    have hlt : k < Nat.find (hex_ord s hs) := by
      have h1 := hk₀_le s hs
      dsimp only [ordS] at h1
      simp only [hs, ↓reduceDIte] at h1
      omega
    exact not_not.mp (Nat.find_min (hex_ord s hs) hlt)
  -- Step 6: Show `eval (jetS u) P₀ = O_N(u^{-N})` using `R_poly` vanishing on `jetS u`!
  let jetS : ℝ → Fin d × Fin (r + 1) → ℂ := fun u p => iteratedDeriv p.2.val (seqSmoothRay (a p.1)) u
  have hR_zero_S : ∀ u : ℝ, MvPolynomial.eval₂ (geomValHom (PrimeNome.tRay u)) (jetS u) R_poly = 0 := by
    intro u
    rw [hR_eval (PrimeNome.tRay u) (PrimeNome.tRay_ne_zero u) (jetS u)]
    have hq_eq : Complex.exp (-PrimeNome.tRay u) = PrimeNome.qRay u := by
      dsimp only [PrimeNome.tRay, PrimeNome.qRay]
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    have hvec : (fun v : Option (Fin d × Fin (r + 1)) =>
          match v with
          | none => Complex.exp (-PrimeNome.tRay u)
          | some p => (PrimeNome.tRay u)⁻¹ ^ (p.2.val + 2) * (Complex.exp (-PrimeNome.tRay u))⁻¹ ^ p.2.val *
              (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval (PrimeNome.tRay u) * jetS u (p.1, k) else 0)) =
        fun v : Option (Fin d × Fin (r + 1)) =>
          match v with
          | none => PrimeNome.qRay u
          | some (i, j) => PrimeNome.value (PrimeNome.seriesJet (seqSeries (a i)) j.val) (PrimeNome.qRay u) := by
      ext v
      cases v with
      | none => exact hq_eq
      | some p =>
        dsimp only
        rw [hq_eq]
        have hbij : (∑ k : Fin (r + 1), if k.val ≤ p.2.val then (jetLCoeff p.2.val k.val).eval (PrimeNome.tRay u) * jetS u (p.1, k) else 0) =
            ∑ k ∈ Finset.range (p.2.val + 1), (jetLCoeff p.2.val k).eval (PrimeNome.tRay u) * iteratedDeriv k (seqSmoothRay (a p.1)) u := by
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
          · intro k₁ _ k₂ _ h; exact Fin.ext h
          · intro k hk
            have hkle : k ≤ p.2.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            refine ⟨⟨k, lt_of_le_of_lt hkle p.2.isLt⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hkle
          · intro k _; rfl
        rw [hbij]
        exact (seriesJet_eq_jetLCoeff_sum (hdisk p.1) p.2.val u).symm
    rw [hvec, hQ₁_ray u, mul_zero]
  -- Uniform geometric bound on all coefficients of `R_poly`
  have hR_unif : ∃ C_R > 0, ∃ M_R ≥ 1, ∀ s ∈ R_poly.support, ∀ k : ℕ,
      ‖PowerSeries.coeff k (R_poly.coeff s).1‖ ≤ C_R * M_R ^ k := by
    choose Cs hCs Ms hMs hbs using fun s : (Fin d × Fin (r + 1)) →₀ ℕ => (R_poly.coeff s).2.2
    let C_R : ℝ := (∑ s ∈ R_poly.support, Cs s) + 1
    let M_R : ℝ := (∑ s ∈ R_poly.support, Ms s) + 1
    refine ⟨C_R, by
      have : 0 ≤ ∑ s ∈ R_poly.support, Cs s := Finset.sum_nonneg fun s _ => (hCs s).le
      dsimp [C_R]; linarith, M_R, by
      have : 0 ≤ ∑ s ∈ R_poly.support, Ms s := Finset.sum_nonneg fun s _ => by linarith [hMs s]
      dsimp [M_R]; linarith, fun s hs k => ?_⟩
    have h1 : Cs s ≤ C_R := by
      have := Finset.single_le_sum (f := Cs) (fun q _ => (hCs q).le) hs; dsimp [C_R]; linarith
    have h2 : Ms s ≤ M_R := by
      have := Finset.single_le_sum (f := Ms) (fun q _ => by linarith [hMs q]) hs; dsimp [M_R]; linarith
    have hM_nn : 0 ≤ Ms s := by linarith [hMs s]
    exact (hbs s k).trans (mul_le_mul h1 (pow_le_pow_left₀ hM_nn h2 k) (by positivity) (by
      have : 0 ≤ ∑ q ∈ R_poly.support, Cs q := Finset.sum_nonneg fun q _ => (hCs q).le
      dsimp [C_R]; linarith))
  obtain ⟨C_R, hCR, M_R, hMR, hR_bd⟩ := hR_unif
  -- Polynomial growth bound for `jetS u p` (from `hasymp` + `jetPlus_poly_bound`)
  have hjetS_poly : ∃ CS > 0, ∃ AS : ℕ, ∃ US : ℝ, 1 ≤ US ∧ ∀ p : Fin d × Fin (r + 1), ∀ u ≥ US,
      ‖jetS u p‖ ≤ CS * u ^ AS := by
    obtain ⟨CH, hCH, A0, U0, hU0, hJP⟩ := jetPlus_poly_bound δ r
    choose Cd hCd Ud hUd using fun p : Fin d × Fin (r + 1) => (hasymp p.1).2.2 p.2.val 0
    let M_inv : ℝ := (∑ i : Fin d, (δ i)⁻¹) + 1
    let C_d : ℝ := (∑ p : Fin d × Fin (r + 1), Cd p) + 1
    let U_d : ℝ := (∑ p : Fin d × Fin (r + 1), |Ud p|) + 1
    have hM_inv : 0 < M_inv := by
      have : 0 ≤ ∑ i : Fin d, (δ i)⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hδ_pos i).le
      dsimp [M_inv]; linarith
    have hC_d : 0 < C_d := by
      have : 0 ≤ ∑ p : Fin d × Fin (r + 1), Cd p := Finset.sum_nonneg fun p _ => (hCd p).le
      dsimp [C_d]; linarith
    refine ⟨M_inv * CH + C_d, by positivity, A0, max U0 U_d, le_trans hU0 (le_max_left _ _), fun p u hu => ?_⟩
    have hu0 : U0 ≤ u := (le_max_left _ _).trans hu
    have hu1 : 1 ≤ u := hU0.trans hu0
    have hUp : Ud p ≤ u := by
      have h1 : Ud p ≤ |Ud p| := le_abs_self _
      have h2 : |Ud p| ≤ ∑ q : Fin d × Fin (r + 1), |Ud q| :=
        Finset.single_le_sum (f := fun q => |Ud q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p)
      have h3 : U_d ≤ u := (le_max_right _ _).trans hu
      dsimp [U_d] at h3; linarith
    have h1 := hUd p u hUp
    simp only [pow_zero, div_one] at h1
    have h2 := hJP p u hu0
    rw [jetPlus_eq] at h2
    have htri : ‖jetS u p‖ ≤ ‖jetS u p - (δ p.1 : ℂ)⁻¹ * iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1))‖ +
        ‖(δ p.1 : ℂ)⁻¹ * iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1))‖ := by
      have := norm_add_le (jetS u p - (δ p.1 : ℂ)⁻¹ * iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1)))
        ((δ p.1 : ℂ)⁻¹ * iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1)))
      simpa only [sub_add_cancel] using this
    have hδ_le : (δ p.1)⁻¹ ≤ M_inv := by
      have := Finset.single_le_sum (f := fun i => (δ i)⁻¹) (fun i _ => inv_nonneg.mpr (hδ_pos i).le) (Finset.mem_univ p.1)
      dsimp [M_inv]; linarith
    have hCd_le : Cd p ≤ C_d := by
      have := Finset.single_le_sum (f := Cd) (fun q _ => (hCd q).le) (Finset.mem_univ p)
      dsimp [C_d]; linarith
    have hterm2 : ‖(δ p.1 : ℂ)⁻¹ * iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1))‖ ≤ M_inv * CH * u ^ A0 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hδ_pos p.1).le]
      calc (δ p.1)⁻¹ * ‖iteratedDeriv p.2.val I_plus (u - Real.log (δ p.1))‖
          ≤ M_inv * (CH * u ^ A0) := mul_le_mul hδ_le h2 (norm_nonneg _) hM_inv.le
        _ = M_inv * CH * u ^ A0 := by ring
    have h1u : (1 : ℝ) ≤ u ^ A0 := one_le_pow₀ hu1
    have hterm1 : Cd p ≤ C_d * u ^ A0 := by nlinarith
    calc ‖jetS u p‖ ≤ Cd p + M_inv * CH * u ^ A0 := by linarith
      _ ≤ C_d * u ^ A0 + M_inv * CH * u ^ A0 := by linarith
      _ = (M_inv * CH + C_d) * u ^ A0 := by ring
  obtain ⟨CS, hCS, AS, US, hUS1, hJS⟩ := hjetS_poly
  -- Show `eval (jetS u) P₀` decays exponentially, hence is `O_N(u^{-N})` for every `N`!
  let D_R : ℕ := R_poly.totalDegree
  let CS' : ℝ := max 1 CS
  let K_P0 : ℝ := (R_poly.support.card : ℝ) * (2 * C_R * M_R ^ (k₀ + 1)) * CS' ^ D_R + 1
  have hKP0_pos : 0 < K_P0 := by dsimp [K_P0]; positivity
  let U_P0 : ℝ := max US (Real.log (2 * M_R) + 1)
  have hP0_exp : ∀ u ≥ U_P0,
      ‖MvPolynomial.eval (jetS u) P₀‖ ≤ K_P0 * u ^ (AS * D_R) * Real.exp (-u) := by
    intro u hu
    have huS : US ≤ u := (le_max_left _ _).trans hu
    have hu1 : 1 ≤ u := hUS1.trans huS
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hu_M : Real.log (2 * M_R) + 1 ≤ u := (le_max_right _ _).trans hu
    have ht_le : ‖PrimeNome.tRay u‖ ≤ (2 * M_R)⁻¹ := by
      dsimp only [PrimeNome.tRay]
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_neg]
      refine inv_anti₀ (by positivity) ?_
      calc 2 * M_R = Real.exp (Real.log (2 * M_R)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    have ht_norm : ‖PrimeNome.tRay u‖ = Real.exp (-u) := by
      dsimp only [PrimeNome.tRay]
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    -- Compare `(tRay u)^k₀ * eval (jetS u) P₀` with `eval₂ (geomValHom (tRay u)) (jetS u) R_poly = 0`!
    have hdiff_eq : (PrimeNome.tRay u) ^ k₀ * MvPolynomial.eval (jetS u) P₀ =
        ∑ s ∈ R_poly.support,
          (PowerSeries.coeff k₀ (R_poly.coeff s).1 * (PrimeNome.tRay u) ^ k₀ -
            PrimeNome.value (R_poly.coeff s).1 (PrimeNome.tRay u)) *
          ∏ p : Fin d × Fin (r + 1), (jetS u p) ^ (s p) := by
      have h0 := hR_zero_S u
      rw [MvPolynomial.eval₂_eq'] at h0
      have hP0_ev : (PrimeNome.tRay u) ^ k₀ * MvPolynomial.eval (jetS u) P₀ =
          ∑ s ∈ R_poly.support, (PowerSeries.coeff k₀ (R_poly.coeff s).1 * (PrimeNome.tRay u) ^ k₀) *
            ∏ p : Fin d × Fin (r + 1), (jetS u p) ^ (s p) := by
        dsimp only [P₀]
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        ring
      have h0' : ∑ s ∈ R_poly.support, PrimeNome.value (R_poly.coeff s).1 (PrimeNome.tRay u) *
            ∏ p : Fin d × Fin (r + 1), (jetS u p) ^ (s p) = 0 := by
        rw [← h0]
        refine Finset.sum_congr rfl fun s _ => rfl
      rw [hP0_ev, ← sub_zero (∑ s ∈ R_poly.support, _), ← h0', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => by ring
    have hprod_bd : ∀ s ∈ R_poly.support,
        ‖∏ p : Fin d × Fin (r + 1), (jetS u p) ^ (s p)‖ ≤ CS' ^ D_R * u ^ (AS * D_R) := by
      intro s hs
      have hdeg_s : ∑ p : Fin d × Fin (r + 1), s p ≤ D_R := by
        have h1 := MvPolynomial.le_totalDegree hs
        rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
      have hCS'1 : 1 ≤ CS' := le_max_left 1 CS
      have hprod_le : ‖∏ p : Fin d × Fin (r + 1), (jetS u p) ^ (s p)‖ ≤
          (CS' * u ^ AS) ^ (∑ p : Fin d × Fin (r + 1), s p) := by
        rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
        have haux : ∀ T : Finset (Fin d × Fin (r + 1)),
            ∏ p ∈ T, ‖(jetS u p) ^ (s p)‖ ≤ ∏ p ∈ T, (CS' * u ^ AS) ^ (s p) := by
          intro T
          induction T using Finset.induction_on with
          | empty => simp
          | insert p T hp ih =>
            rw [Finset.prod_insert hp, Finset.prod_insert hp]
            have h1 : ‖(jetS u p) ^ (s p)‖ ≤ (CS' * u ^ AS) ^ (s p) := by
              rw [norm_pow]
              exact pow_le_pow_left₀ (norm_nonneg _)
                ((hJS p u huS).trans (mul_le_mul_of_nonneg_right (le_max_right 1 CS) (by positivity))) (s p)
            exact mul_le_mul h1 ih (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
        exact haux Finset.univ
      have hbase1 : 1 ≤ CS' * u ^ AS := by
        have h1 : (1 : ℝ) ≤ u ^ AS := one_le_pow₀ hu1
        nlinarith
      calc _ ≤ (CS' * u ^ AS) ^ (∑ p : Fin d × Fin (r + 1), s p) := hprod_le
        _ ≤ (CS' * u ^ AS) ^ D_R := pow_le_pow_right₀ hbase1 hdeg_s
        _ = CS' ^ D_R * u ^ (AS * D_R) := by rw [mul_pow, ← pow_mul]
    have hlead_bd : ‖(PrimeNome.tRay u) ^ k₀ * MvPolynomial.eval (jetS u) P₀‖ ≤
        ((R_poly.support.card : ℝ) * (2 * C_R * M_R ^ (k₀ + 1)) * CS' ^ D_R) *
          u ^ (AS * D_R) * Real.exp (-u) ^ (k₀ + 1) := by
      rw [hdiff_eq]
      calc ‖∑ s ∈ R_poly.support, _‖
          ≤ ∑ s ∈ R_poly.support,
              ‖PowerSeries.coeff k₀ (R_poly.coeff s).1 * (PrimeNome.tRay u) ^ k₀ -
                PrimeNome.value (R_poly.coeff s).1 (PrimeNome.tRay u)‖ *
              ‖∏ p : Fin d × Fin (r + 1), (jetS u p) ^ (s p)‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => by rw [norm_mul])
        _ ≤ ∑ _s ∈ R_poly.support,
              ((2 * C_R * M_R ^ (k₀ + 1)) * Real.exp (-u) ^ (k₀ + 1)) * (CS' ^ D_R * u ^ (AS * D_R)) := by
            refine Finset.sum_le_sum fun s hs => ?_
            rw [norm_sub_rev]
            have hrem := norm_value_sub_lead_le_of_geom hCR hMR (hR_bd s hs) (hlow_zero s hs) ht_le
            rw [ht_norm] at hrem
            exact mul_le_mul hrem (hprod_bd s hs) (norm_nonneg _) (by positivity)
        _ = ((R_poly.support.card : ℝ) * (2 * C_R * M_R ^ (k₀ + 1)) * CS' ^ D_R) *
              u ^ (AS * D_R) * Real.exp (-u) ^ (k₀ + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    rw [norm_mul, norm_pow, ht_norm, pow_succ] at hlead_bd
    have hpos_k0 : 0 < Real.exp (-u) ^ k₀ := pow_pos (Real.exp_pos _) k₀
    have hmul_le : Real.exp (-u) ^ k₀ * ‖MvPolynomial.eval (jetS u) P₀‖ ≤
        Real.exp (-u) ^ k₀ * (K_P0 * u ^ (AS * D_R) * Real.exp (-u)) := by
      have hK_le : ((R_poly.support.card : ℝ) * (2 * C_R * M_R ^ (k₀ + 1)) * CS' ^ D_R) ≤ K_P0 := by
        dsimp only [K_P0]; linarith
      have hrhs : ((R_poly.support.card : ℝ) * (2 * C_R * M_R ^ (k₀ + 1)) * CS' ^ D_R) *
            u ^ (AS * D_R) * (Real.exp (-u) ^ k₀ * Real.exp (-u)) ≤
          Real.exp (-u) ^ k₀ * (K_P0 * u ^ (AS * D_R) * Real.exp (-u)) := by
        have hstep := mul_le_mul_of_nonneg_right hK_le
          (mul_nonneg (pow_nonneg hu_pos.le (AS * D_R)) (mul_nonneg hpos_k0.le (Real.exp_pos (-u)).le))
        calc ((R_poly.support.card : ℝ) * (2 * C_R * M_R ^ (k₀ + 1)) * CS' ^ D_R) *
              u ^ (AS * D_R) * (Real.exp (-u) ^ k₀ * Real.exp (-u))
            = ((R_poly.support.card : ℝ) * (2 * C_R * M_R ^ (k₀ + 1)) * CS' ^ D_R) *
              (u ^ (AS * D_R) * (Real.exp (-u) ^ k₀ * Real.exp (-u))) := by ring
          _ ≤ K_P0 * (u ^ (AS * D_R) * (Real.exp (-u) ^ k₀ * Real.exp (-u))) := hstep
          _ = Real.exp (-u) ^ k₀ * (K_P0 * u ^ (AS * D_R) * Real.exp (-u)) := by ring
      exact hlead_bd.trans hrhs
    exact le_of_mul_le_mul_left hmul_le hpos_k0
  have hP0_flat_S : ∀ K : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖MvPolynomial.eval (jetS u) P₀‖ ≤ C / u ^ K := by
    intro K
    obtain ⟨C', hC', U', _, hK⟩ := PakNthPrimeEngine.exists_bound_pow_mul_exp_neg K_P0 hKP0_pos (AS * D_R) K
    refine ⟨C', hC', max U_P0 U', fun u hu => ?_⟩
    exact (hP0_exp u ((le_max_left _ _).trans hu)).trans (hK u ((le_max_right _ _).trans hu))
  -- Step 7: Transfer `jetS u → fun p => (δ p.1)⁻¹ * jetPlus δ r u p` and rescale into `InFlatIdeal δ`!
  let scaledJetPlus : Fin d × Fin (r + 1) → ℝ → ℂ :=
    fun p u => (δ p.1 : ℂ)⁻¹ * jetPlus δ r u p
  have hscaled_poly : ∃ CH > 0, ∃ A : ℕ, ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ p, ∀ u ≥ U₀, ‖scaledJetPlus p u‖ ≤ CH * u ^ A := by
    obtain ⟨CH, hCH, A0, U0, hU0, hJP⟩ := jetPlus_poly_bound δ r
    let M_inv : ℝ := (∑ i : Fin d, (δ i)⁻¹) + 1
    have hM_inv : 0 < M_inv := by
      have : 0 ≤ ∑ i : Fin d, (δ i)⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hδ_pos i).le
      dsimp [M_inv]; linarith
    refine ⟨M_inv * CH, by positivity, A0, U0, hU0, fun p u hu => ?_⟩
    dsimp only [scaledJetPlus]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hδ_pos p.1).le]
    have hδ_le : (δ p.1)⁻¹ ≤ M_inv := by
      have := Finset.single_le_sum (f := fun i => (δ i)⁻¹) (fun i _ => inv_nonneg.mpr (hδ_pos i).le) (Finset.mem_univ p.1)
      dsimp [M_inv]; linarith
    calc (δ p.1)⁻¹ * ‖jetPlus δ r u p‖ ≤ M_inv * (CH * u ^ A0) :=
          mul_le_mul hδ_le (hJP p u hu) (norm_nonneg _) hM_inv.le
      _ = (M_inv * CH) * u ^ A0 := by ring
  have hdiff_S : ∀ p : Fin d × Fin (r + 1), ∀ K : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
      ‖jetS u p - scaledJetPlus p u‖ ≤ C / u ^ K := by
    intro p K
    obtain ⟨C, hC, U, hU⟩ := (hasymp p.1).2.2 p.2.val K
    refine ⟨C, hC, U, fun u hu => ?_⟩
    dsimp only [jetS, scaledJetPlus]
    rw [jetPlus_eq]
    exact hU u hu
  have htr := (eval_jet_diff_allOrders_general (f := fun p u => jetS u p) (g := scaledJetPlus)
    hscaled_poly hdiff_S P₀).2
  -- Rescale `X (i, j) ↦ (δ i)⁻¹ • X (i, j)` to obtain nonzero `P₁ ∈ InFlatIdeal δ`!
  let P₁ : MvPolynomial (Fin d × Fin (r + 1)) ℂ :=
    MvPolynomial.aeval (fun p : Fin d × Fin (r + 1) => ((δ p.1 : ℂ)⁻¹) • MvPolynomial.X p) P₀
  have hP₁_ne : P₁ ≠ 0 := by
    intro h0
    apply hP₀_ne
    have hback : MvPolynomial.aeval (fun p : Fin d × Fin (r + 1) => (δ p.1 : ℂ) • MvPolynomial.X p) P₁ = P₀ := by
      dsimp only [P₁]
      induction P₀ using MvPolynomial.induction_on with
      | C c => simp
      | add p q hp hq => rw [map_add, map_add, hp, hq]
      | mul_X p k hp =>
        rw [map_mul, map_mul, MvPolynomial.aeval_X, map_smul, MvPolynomial.aeval_X, hp,
          smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hδ_pos k.1).ne'), one_smul]
    rw [h0, map_zero] at hback
    exact hback.symm
  have hP₁_eval : ∀ u : ℝ, MvPolynomial.eval (jetPlus δ r u) P₁ =
      MvPolynomial.eval (fun p => scaledJetPlus p u) P₀ := by
    intro u
    dsimp only [P₁]
    induction P₀ using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp =>
      rw [map_mul, map_mul, map_mul, MvPolynomial.aeval_X, hp, PakNthPrimeEngine.eval_smul_eq,
        MvPolynomial.eval_X, MvPolynomial.eval_X]
  have hP₁_flat : InFlatIdeal δ P₁ := by
    intro K
    obtain ⟨C1, hC1, U1, h1⟩ := hP0_flat_S K
    obtain ⟨C2, hC2, U2, h2⟩ := htr K
    refine ⟨C1 + C2, add_pos hC1 hC2, max U1 U2, fun u hu => ?_⟩
    rw [hP₁_eval u]
    have htri : ‖MvPolynomial.eval (fun p => scaledJetPlus p u) P₀‖ ≤
        ‖MvPolynomial.eval (jetS u) P₀‖ +
        ‖MvPolynomial.eval (jetS u) P₀ - MvPolynomial.eval (fun p => scaledJetPlus p u) P₀‖ := by
      have := norm_sub_le (MvPolynomial.eval (jetS u) P₀)
        (MvPolynomial.eval (jetS u) P₀ - MvPolynomial.eval (fun p => scaledJetPlus p u) P₀)
      simpa only [sub_sub_cancel] using this
    have hsum_div : C1 / u ^ K + C2 / u ^ K = (C1 + C2) / u ^ K := by ring
    linarith [h1 u ((le_max_left _ _).trans hu), h2 u ((le_max_right _ _).trans hu)]
  -- Contradiction from `distinctDensity_ideal_eq_zero`!
  exact hP₁_ne (distinctDensity_ideal_eq_zero hδ_pos hinj P₁ hP₁_flat)

/-- **MASTER OGF THEOREM (`distinctDensity_ogf_joint_algebraicIndependent`)**:
For any finite family of strictly increasing sequences `a : Fin d → ℕ → ℕ` with pairwise
distinct positive densities `δ : Fin d → ℝ` satisfying all-orders PNT counting asymptotics
`HasDensityPNT (a i) (δ i)`, their ordinary generating functions `F_i(q) = ∑_{n ≥ 0} a_{i, n} q^{n+1}`
are **jointly differentially algebraically independent over `ℂ(q)`**! -/
theorem distinctDensity_ogf_joint_algebraicIndependent
    {d : ℕ} (a : Fin d → ℕ → ℕ) (δ : Fin d → ℝ)
    (hd : ∀ i, HasDensityPNT (a i) (δ i))
    (hinj : Function.Injective δ) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i => seqSeries (a i))) :=
  distinctDensity_ogf_joint_algebraicIndependent_of_asymp a δ
    (fun i => hasScaledDensityAsymp_of_hasDensityPNT (hd i)) hinj

/-! #### 3c. Dyadic-Density Specialization Corollaries (`δ_k = 2 ^ (1 - k)`) -/

/-- Dyadic density `δ_k = 2 ^ (1 - k)` for `k : ℕ` (e.g., primes `p ≡ 1 mod 2^k` for `k ≥ 1`). -/
@[expose] def dyadicDensity (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (1 - (k : ℤ))

lemma dyadicDensity_pos (k : ℕ) : 0 < dyadicDensity k :=
  zpow_pos (by norm_num : (0 : ℝ) < 2) _

lemma dyadicDensity_injective : Function.Injective dyadicDensity := by
  intro k₁ k₂ h
  have h1 : (1 - (k₁ : ℤ)) = (1 - (k₂ : ℤ)) :=
    StrictMono.injective (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)) h
  omega

/-- **Finite Dyadic-Density Specialization (`distinctDensity_dyadic_finite`)**:
For any finite injective selection `k : Fin d → ℕ` of dyadic levels `δ_i = 2 ^ (1 - k_i)`
(e.g., any finite selection of nested prime progressions `p ≡ 1 mod 2^k`), the corresponding
ordinary generating functions are jointly differentially algebraically independent over `ℂ(q)`. -/
theorem distinctDensity_dyadic_finite
    {d : ℕ} (a : Fin d → ℕ → ℕ) (k : Fin d → ℕ)
    (hkinj : Function.Injective k)
    (hd : ∀ i, HasDensityPNT (a i) (dyadicDensity (k i))) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i => seqSeries (a i))) :=
  distinctDensity_ogf_joint_algebraicIndependent a (fun i => dyadicDensity (k i)) hd
    (dyadicDensity_injective.comp hkinj)

/-- Countable joint differential coordinates `(q, {F_k^{(j)} : k, j ∈ ℕ})` in `PowerSeries ℂ`. -/
@[expose] def countableSeriesCoordinates (F : ℕ → PowerSeries ℂ) :
    Option (ℕ × ℕ) → PowerSeries ℂ
  | none => PowerSeries.X
  | some (k, j) => PrimeNome.seriesJet (F k) j

/-- **Countably Infinite Dyadic-Density Corollary (`distinctDensity_dyadic_countable`)**:
Given a countably infinite family of sequences `a : ℕ → ℕ → ℕ` with densities `2 ^ (1 - (k + 1))`
(such as the nested prime progressions `p ≡ 1 mod 2^{k+1}` for `k = 0, 1, 2, ...`), ALL of their
ordinary generating functions and ALL of their derivatives taken together are algebraically
independent over `ℂ(q)`! -/
theorem distinctDensity_dyadic_countable
    (a : ℕ → ℕ → ℕ)
    (hd : ∀ k : ℕ, HasDensityPNT (a k) (dyadicDensity (k + 1))) :
    AlgebraicIndependent ℂ (countableSeriesCoordinates (fun k => seqSeries (a k))) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  let d : ℕ := (P.vars.sup fun v => match v with | none => 0 | some (k, _) => k) + 1
  let emb : Option (Fin d × ℕ) → Option (ℕ × ℕ) :=
    fun v => match v with | none => none | some (i, j) => some (i.val, j)
  have hemb_inj : Function.Injective emb := by
    intro v₁ v₂ h
    cases v₁ with
    | none => cases v₂ with | none => rfl | some _ => simp [emb] at h
    | some p₁ => cases v₂ with
      | none => simp [emb] at h
      | some p₂ =>
        simp only [emb, Option.some.injEq, Prod.mk.injEq] at h
        exact congrArg some (Prod.ext (Fin.ext h.1) h.2)
  have hsub : ↑P.vars ⊆ Set.range emb := by
    intro v hv
    cases v with
    | none => exact ⟨none, rfl⟩
    | some p =>
      have hk_lt : p.1 < d := by
        have h := Finset.le_sup (f := fun v : Option (ℕ × ℕ) => match v with | none => 0 | some (k, _) => k)
          (Finset.mem_coe.mp hv)
        dsimp only at h
        dsimp only [d]; omega
      exact ⟨some (⟨p.1, hk_lt⟩, p.2), rfl⟩
  obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P emb hemb_inj hsub
  have hind := distinctDensity_dyadic_finite (fun i : Fin d => a i.val) (fun i : Fin d => i.val + 1)
    (fun i₁ i₂ h => Fin.ext (by dsimp only at h; omega)) (fun i => hd i.val)
  have hQ_zero : MvPolynomial.aeval (jointSeriesCoordinates (fun i : Fin d => seqSeries (a i.val))) Q = 0 := by
    rw [← hQ, MvPolynomial.aeval_rename] at hP
    have heq : (countableSeriesCoordinates (fun k => seqSeries (a k)) ∘ emb) =
        jointSeriesCoordinates (fun i : Fin d => seqSeries (a i.val)) := by
      ext v; cases v <;> rfl
    rwa [heq] at hP
  have hQ0 : Q = 0 := (algebraicIndependent_iff.mp hind) Q hQ_zero
  rw [← hQ, hQ0, map_zero]

end
end PakPrimes.DistinctDensityPrimes
