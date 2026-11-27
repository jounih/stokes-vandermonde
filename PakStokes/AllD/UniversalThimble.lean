module

public import PakStokes.AllD.BesicovitchCore
public import PakStokes.LaplaceWaveJets
public import PakStokes.RayAlgebra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Calculus.Deriv.Pow
import all PakStokes.AllD.BesicovitchCore
import all PakStokes.RayAlgebra
import all PakStokes.LaplaceWaveJets
import all PakStokes.WaveProducts

/-! Exact all-`d` Lefschetz thimble geometry (`d ≥ 3`):
1. The exact rotated phase identity `φ_d(c_ℓ w) = A_ℓ + c_ℓ^d (w^d - d w + (d - 1))`.
2. The 8-line critical-value-free left half-plane theorem: every critical value
   of `P_d(w) = w^d - d w + (d - 1)` other than `0` has strictly positive real part.
3. Exact UHP active saddle counts (`d/2` for even `d`, `2 * ⌊(d+1)/4⌋` for odd `d`).
4. Universal Beta-averaged kernel bounds and the universal `PowerClass (1/2)`
   wave scaling & jet expansion for every `d ≥ 3`. -/
public section
namespace CubicTheta.AllD
open Complex Filter Set MeasureTheory LaplaceWave
open scoped Topology
noncomputable section

/-! ### 1. Saddle Phase, Critical Points, and Exact Rotated Phase Identity -/

/-- The rescaled Fourier-Laplace phase `φ_d(v) = v^d - d i v`. -/
def thimblePhase (d : ℕ) (v : ℂ) : ℂ := v ^ d - (d : ℂ) * I * v

/-- Critical angle `α_ℓ = π (4ℓ + 1) / (2 (d - 1))`. -/
def saddleAngle (d ℓ : ℕ) : ℝ := Real.pi * (4 * (ℓ : ℝ) + 1) / (2 * ((d - 1 : ℕ) : ℝ))

/-- Critical point `c_ℓ = exp(i α_ℓ)` of `φ_d`. -/
def saddlePoint (d ℓ : ℕ) : ℂ := Complex.exp (I * (saddleAngle d ℓ : ℂ))

/-- Critical value / Stokes action `A_ℓ = φ_d(c_ℓ)`. -/
def saddleAction (d ℓ : ℕ) : ℂ := thimblePhase d (saddlePoint d ℓ)

/-- The `ℓ`-independent universal thimble polynomial `P_d(w) = w^d - d w + (d - 1)`. -/
def universalPoly (d : ℕ) (w : ℂ) : ℂ := w ^ d - (d : ℂ) * w + ((d - 1 : ℕ) : ℂ)

theorem saddlePoint_pow_pred {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    saddlePoint d ℓ ^ (d - 1) = I := by
  unfold saddlePoint saddleAngle
  rw [← Complex.exp_nat_mul]
  have hr0 : ((d - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
  have hexp : ((d - 1 : ℕ) : ℂ) * (I * (((Real.pi * (4 * (ℓ : ℝ) + 1) /
      (2 * ((d - 1 : ℕ) : ℝ)) : ℝ) : ℂ))) =
      ((ℓ : ℂ) * (2 * (Real.pi : ℂ) * I)) + (Real.pi : ℂ) / 2 * I := by
    push_cast
    field_simp [hr0]
    ring
  rw [hexp, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul, Complex.exp_pi_div_two_mul_I]

theorem saddlePoint_pow {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    saddlePoint d ℓ ^ d = I * saddlePoint d ℓ := by
  have hd_eq : d = (d - 1) + 1 := by omega
  conv_lhs => rw [show saddlePoint d ℓ ^ d = saddlePoint d ℓ ^ ((d - 1) + 1) by rw [← hd_eq]]
  rw [pow_succ, saddlePoint_pow_pred hd ℓ]

theorem saddleAction_eq {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    saddleAction d ℓ = -((d - 1 : ℕ) : ℂ) * I * saddlePoint d ℓ := by
  unfold saddleAction thimblePhase
  rw [saddlePoint_pow hd ℓ]
  have hd_eq : (d : ℂ) = ((d - 1 : ℕ) : ℂ) + 1 := by
    exact_mod_cast (show d = d - 1 + 1 by omega)
  rw [hd_eq]
  ring

theorem saddleAction_polar {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    saddleAction d ℓ =
      ((d - 1 : ℕ) : ℂ) * Complex.exp (I * ((saddleAngle d ℓ - Real.pi / 2 : ℝ) : ℂ)) := by
  rw [saddleAction_eq hd ℓ, saddlePoint]
  have hnegI : -I = Complex.exp (I * (-(Real.pi / 2 : ℝ) : ℂ)) := by
    rw [show I * (-(Real.pi / 2 : ℝ) : ℂ) = -((Real.pi : ℂ) / 2 * I) by push_cast; ring,
        Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]
  calc -((d - 1 : ℕ) : ℂ) * I * Complex.exp (I * (saddleAngle d ℓ : ℂ))
      = ((d - 1 : ℕ) : ℂ) * ((-I) * Complex.exp (I * (saddleAngle d ℓ : ℂ))) := by ring
    _ = ((d - 1 : ℕ) : ℂ) *
          (Complex.exp (I * (-(Real.pi / 2 : ℝ) : ℂ)) * Complex.exp (I * (saddleAngle d ℓ : ℂ))) := by
          rw [hnegI]
    _ = ((d - 1 : ℕ) : ℂ) * Complex.exp (I * ((saddleAngle d ℓ - Real.pi / 2 : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]
          congr 2
          push_cast; ring

theorem saddleAction_re {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    (saddleAction d ℓ).re = ((d - 1 : ℕ) : ℝ) * Real.sin (saddleAngle d ℓ) := by
  rw [saddleAction_polar hd ℓ]
  have hre : (Complex.exp (I * ((saddleAngle d ℓ - Real.pi / 2 : ℝ) : ℂ))).re =
      Real.cos (saddleAngle d ℓ - Real.pi / 2) := by
    rw [mul_comm I _, Complex.exp_ofReal_mul_I_re]
  rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, hre,
      Real.cos_sub_pi_div_two]

theorem saddleAction_im {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    (saddleAction d ℓ).im = -((d - 1 : ℕ) : ℝ) * Real.cos (saddleAngle d ℓ) := by
  rw [saddleAction_polar hd ℓ]
  have him : (Complex.exp (I * ((saddleAngle d ℓ - Real.pi / 2 : ℝ) : ℂ))).im =
      Real.sin (saddleAngle d ℓ - Real.pi / 2) := by
    rw [mul_comm I _, Complex.exp_ofReal_mul_I_im]
  rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero, him,
      Real.sin_sub_pi_div_two]
  ring

theorem saddleAction_norm {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    ‖saddleAction d ℓ‖ = ((d - 1 : ℕ) : ℝ) := by
  rw [saddleAction_polar hd ℓ, norm_mul, Complex.norm_natCast]
  have h1 : ‖Complex.exp (I * ((saddleAngle d ℓ - Real.pi / 2 : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

/-- **Exact Rotated Phase Identity**: substituting `v = c_ℓ w` turns `φ_d(v)` into
`A_ℓ + c_ℓ^d P_d(w)` identically for EVERY `d ≥ 3`, `ℓ`, and `w ∈ ℂ`. -/
theorem rotated_phase_identity {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) (w : ℂ) :
    thimblePhase d (saddlePoint d ℓ * w) =
      saddleAction d ℓ + saddlePoint d ℓ ^ d * universalPoly d w := by
  unfold thimblePhase universalPoly
  rw [mul_pow, saddleAction_eq hd ℓ, saddlePoint_pow hd ℓ]
  ring

/-! ### 2. Exact 8-Line Critical-Value-Free Left Half-Plane Theorem -/

theorem hasDerivAt_universalPoly {d : ℕ} (_hd : 1 ≤ d) (w : ℂ) :
    HasDerivAt (universalPoly d) ((d : ℂ) * (w ^ (d - 1) - 1)) w := by
  unfold universalPoly
  have h1 := ((hasDerivAt_pow d w).sub ((hasDerivAt_id w).const_mul (d : ℂ))).add
    (hasDerivAt_const w ((d - 1 : ℕ) : ℂ))
  have hfun : (fun w : ℂ ↦ w ^ d - (d : ℂ) * w + ((d - 1 : ℕ) : ℂ)) =
      ((fun x : ℂ ↦ x ^ d) - fun y : ℂ ↦ (d : ℂ) * id y) + fun _ ↦ ((d - 1 : ℕ) : ℂ) := by
    funext z; simp
  rw [hfun]
  convert h1 using 1
  ring

theorem universalPoly_crit_iff {d : ℕ} (hd : 3 ≤ d) (w : ℂ) :
    deriv (universalPoly d) w = 0 ↔ w ^ (d - 1) = 1 := by
  rw [(hasDerivAt_universalPoly (by omega) w).deriv]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp [hd0, sub_eq_zero]

theorem universalPoly_at_crit {d : ℕ} (hd : 3 ≤ d) {w : ℂ} (hw : w ^ (d - 1) = 1) :
    universalPoly d w = ((d - 1 : ℕ) : ℂ) * (1 - w) := by
  unfold universalPoly
  have hwd : w ^ d = w := by
    have hd_eq : d = (d - 1) + 1 := by omega
    rw [hd_eq, pow_succ, hw, one_mul]
  have hd_cast : (d : ℂ) = ((d - 1 : ℕ) : ℂ) + 1 := by
    exact_mod_cast (show d = d - 1 + 1 by omega)
  rw [hwd, hd_cast]
  ring

/-- Every critical point `w ≠ 1` of `P_d(w) = w^d - d w + (d - 1)` has critical value
strictly in the open right half-plane `Re(P_d(w)) = (d - 1)(1 - Re w) > 0`. -/
theorem universalPoly_crit_re_pos {d : ℕ} (hd : 3 ≤ d) {w : ℂ}
    (hcrit : deriv (universalPoly d) w = 0) (hne : w ≠ 1) :
    0 < (universalPoly d w).re := by
  have hw : w ^ (d - 1) = 1 := (universalPoly_crit_iff hd w).mp hcrit
  have hnorm : ‖w‖ = 1 := by
    have hp : ‖w‖ ^ (d - 1) = 1 := by rw [← norm_pow, hw, norm_one]
    have hpow := (pow_left_inj₀ (norm_nonneg w) zero_le_one (by omega : d - 1 ≠ 0)).mp (by simpa using hp)
    exact hpow
  have hre_le : w.re ≤ 1 := hnorm ▸ Complex.re_le_norm w
  have hre_lt : w.re < 1 := by
    rcases hre_le.eq_or_lt with heq | hlt
    · exfalso
      have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
        have hns : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
        simpa [Complex.normSq_apply, sq] using hns
      rw [heq, one_pow] at hsq
      have him0 : w.im = 0 := by nlinarith
      exact hne (Complex.ext heq him0)
    · exact hlt
  rw [universalPoly_at_crit hd hw]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.one_re]
  have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  exact mul_pos hr_pos (sub_pos.mpr hre_lt)

/-- **Exact All-`d` Critical-Value-Free Left Half-Plane Theorem**:
For every `d ≥ 3`, ZERO nonzero critical values of `P_d(w) = w^d - d w + (d - 1)`
lie in the closed left half-plane `{Re ζ ≤ 0}`. -/
theorem universalPoly_no_nonzero_critValue_in_LHP {d : ℕ} (hd : 3 ≤ d) {ζ : ℂ}
    (hre : ζ.re ≤ 0) (hne : ζ ≠ 0) :
    ¬ ∃ w : ℂ, deriv (universalPoly d) w = 0 ∧ universalPoly d w = ζ := by
  rintro ⟨w, hcrit, hval⟩
  by_cases hw1 : w = 1
  · subst hw1
    have h0 : universalPoly d 1 = 0 := by
      unfold universalPoly
      have hd_cast : (d : ℂ) = ((d - 1 : ℕ) : ℂ) + 1 := by
        exact_mod_cast (show d = d - 1 + 1 by omega)
      rw [one_pow, mul_one, hd_cast]
      ring
    exact hne (hval.symm.trans h0)
  · have hpos := universalPoly_crit_re_pos hd hcrit hw1
    rw [hval] at hpos
    linarith

/-- Real-axis barrier (Theorem 1 Step 4): `x^d - d x + (d - 1) ≥ 0` for all `x ≥ 0`. -/
theorem universalPoly_real_nonneg {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x ^ d - (d : ℝ) * x + ((d - 1 : ℕ) : ℝ) := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hstep : x ^ (k + 1) - ((k + 1 : ℕ) : ℝ) * x + ((k + 1 - 1 : ℕ) : ℝ) =
        (x ^ k - (k : ℝ) * x + ((k - 1 : ℕ) : ℝ)) + (x ^ k - 1) * (x - 1) := by
      have hk1 : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel hk
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      linarith
    rw [hstep]
    have hprod : 0 ≤ (x ^ k - 1) * (x - 1) := by
      rcases le_or_gt 1 x with hge | hlt
      · exact mul_nonneg (sub_nonneg.mpr (one_le_pow₀ hge)) (sub_nonneg.mpr hge)
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (pow_le_one₀ hx hlt.le))
          (sub_nonpos.mpr hlt.le)
    linarith

/-- Upper sector-ray barrier (Theorem 1 Step 4): on `w = ρ exp(i π / d)`,
`Im P_d(w) = -d ρ sin(π/d) < 0` for every `ρ > 0`. -/
theorem universalPoly_ray_im_neg {d : ℕ} (hd : 3 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    (universalPoly d ((ρ : ℂ) * Complex.exp (I * ((Real.pi / (d : ℝ) : ℝ) : ℂ)))).im < 0 := by
  unfold universalPoly
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hpow : ((ρ : ℂ) * Complex.exp (I * ((Real.pi / (d : ℝ) : ℝ) : ℂ))) ^ d = -((ρ ^ d : ℝ) : ℂ) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    have hexp : (d : ℂ) * (I * ((Real.pi / (d : ℝ) : ℝ) : ℂ)) = (Real.pi : ℂ) * I := by
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      push_cast; field_simp [hd0]
    rw [hexp, Complex.exp_pi_mul_I]
    push_cast; ring
  rw [hpow]
  have him_exp : (Complex.exp (I * ((Real.pi / (d : ℝ) : ℝ) : ℂ))).im = Real.sin (Real.pi / d) := by
    rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  have hsin_pos : 0 < Real.sin (Real.pi / d) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hd_pos)
      ((div_lt_iff₀ hd_pos).mpr (by nlinarith [Real.pi_pos, show (3 : ℝ) ≤ d by exact_mod_cast hd]))
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.natCast_im,
    neg_zero, add_zero, zero_sub]
  rw [show ((d : ℂ) * ((ρ : ℂ) * Complex.exp (I * ((Real.pi / (d : ℝ) : ℝ) : ℂ)))).im =
      (d : ℝ) * ρ * Real.sin (Real.pi / d) by
    rw [← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him_exp]]
  nlinarith [mul_pos (mul_pos hd_pos hρ) hsin_pos]

/-! ### 3. Exact UHP Saddle Count, Distinct Imaginary Parts, and Active Saddle Set -/

theorem saddleAngle_pos_lt_pi {d ℓ : ℕ} (hd : 3 ≤ d) (hℓ : ℓ < d / 2) :
    0 < saddleAngle d ℓ ∧ saddleAngle d ℓ < Real.pi := by
  unfold saddleAngle
  have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hnum_lt : 4 * (ℓ : ℝ) + 1 < 2 * ((d - 1 : ℕ) : ℝ) := by
    have : 4 * ℓ + 1 < 2 * (d - 1) := by omega
    exact_mod_cast this
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]

theorem uhp_saddle_re_pos {d ℓ : ℕ} (hd : 3 ≤ d) (hℓ : ℓ < d / 2) :
    0 < (saddleAction d ℓ).re := by
  rw [saddleAction_re hd ℓ]
  have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  obtain ⟨h0, hpi⟩ := saddleAngle_pos_lt_pi hd hℓ
  exact mul_pos hr_pos (Real.sin_pos_of_pos_of_lt_pi h0 hpi)

theorem rotated_ray_in_LHP {d ℓ : ℕ} (hd : 3 ≤ d) (hℓ : ℓ < d / 2) {u : ℝ} (hu : 0 < u) :
    (Complex.exp (I * ((-Real.pi / 2 - saddleAngle d ℓ : ℝ) : ℂ)) * (u : ℂ)).re < 0 := by
  have hre : (Complex.exp (I * ((-Real.pi / 2 - saddleAngle d ℓ : ℝ) : ℂ))).re =
      -Real.sin (saddleAngle d ℓ) := by
    rw [mul_comm I _, Complex.exp_mul_I]
    simp only [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re, Complex.sin_ofReal_re,
      Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    rw [show -Real.pi / 2 - saddleAngle d ℓ = -(saddleAngle d ℓ + Real.pi / 2) by ring,
        Real.cos_neg, Real.cos_add_pi_div_two]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hre]
  obtain ⟨h0, hpi⟩ := saddleAngle_pos_lt_pi hd hℓ
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  nlinarith

/-- Exact characterization of the open right-half-plane saddles among `0 ≤ ℓ < d - 1`. -/
theorem uhp_saddle_iff {d ℓ : ℕ} (hd : 3 ≤ d) (hℓ : ℓ < d - 1) :
    0 < (saddleAction d ℓ).re ↔ ℓ < d / 2 := by
  constructor
  · intro hpos
    by_contra hge
    have hpi_le : Real.pi ≤ saddleAngle d ℓ := by
      unfold saddleAngle
      have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
      rw [le_div_iff₀ (by positivity)]
      have hnat : 2 * (d - 1) ≤ 4 * ℓ + 1 := by omega
      have hreal : (2 * ((d - 1 : ℕ) : ℝ)) ≤ 4 * (ℓ : ℝ) + 1 := by exact_mod_cast hnat
      nlinarith [Real.pi_pos]
    have hlt_2pi : saddleAngle d ℓ < 2 * Real.pi := by
      unfold saddleAngle
      have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
      rw [div_lt_iff₀ (by positivity)]
      have hnat : 4 * ℓ + 1 < 4 * (d - 1) := by omega
      have hreal : 4 * (ℓ : ℝ) + 1 < 4 * ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      nlinarith [Real.pi_pos]
    have hsin_le : Real.sin (saddleAngle d ℓ) ≤ 0 := by
      have hsub : Real.sin (saddleAngle d ℓ) = -Real.sin (saddleAngle d ℓ - Real.pi) := by
        rw [Real.sin_sub_pi]; ring
      rw [hsub]
      have hnn : 0 ≤ Real.sin (saddleAngle d ℓ - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      linarith
    rw [saddleAction_re hd ℓ] at hpos
    have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    nlinarith
  · exact uhp_saddle_re_pos hd

/-- No two distinct critical points `0 ≤ ℓ₁, ℓ₂ < d - 1` have the same imaginary part
of `A_ℓ` (since `4(ℓ₁ + ℓ₂) + 2 ≠ 4(d - 1)` mod 4). -/
theorem saddleAction_im_inj {d : ℕ} (hd : 3 ≤ d) {ℓ₁ ℓ₂ : ℕ}
    (h₁ : ℓ₁ < d - 1) (h₂ : ℓ₂ < d - 1)
    (him : (saddleAction d ℓ₁).im = (saddleAction d ℓ₂).im) : ℓ₁ = ℓ₂ := by
  rw [saddleAction_im hd ℓ₁, saddleAction_im hd ℓ₂] at him
  have hr_ne : -((d - 1 : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    linarith
  have hcos : Real.cos (saddleAngle d ℓ₁) = Real.cos (saddleAngle d ℓ₂) :=
    mul_left_cancel₀ hr_ne him
  have hrange (ℓ : ℕ) (hℓ : ℓ < d - 1) : 0 < saddleAngle d ℓ ∧ saddleAngle d ℓ < 2 * Real.pi := by
    unfold saddleAngle
    have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    refine ⟨by positivity, (div_lt_iff₀ (by positivity)).mpr ?_⟩
    have hnat : 4 * ℓ + 1 < 4 * (d - 1) := by omega
    have hreal : 4 * (ℓ : ℝ) + 1 < 4 * ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    nlinarith [Real.pi_pos]
  obtain ⟨h10, h12⟩ := hrange ℓ₁ h₁
  obtain ⟨h20, h22⟩ := hrange ℓ₂ h₂
  -- Compare on `[0, π]` vs `[π, 2π]` via `Real.strictAntiOn_cos`.
  have hpi_cases : saddleAngle d ℓ₁ = saddleAngle d ℓ₂ ∨
      saddleAngle d ℓ₁ + saddleAngle d ℓ₂ = 2 * Real.pi := by
    rcases le_or_gt (saddleAngle d ℓ₁) Real.pi with ha1 | ha1 <;>
    rcases le_or_gt (saddleAngle d ℓ₂) Real.pi with ha2 | ha2
    · left
      exact Real.injOn_cos ⟨h10.le, ha1⟩ ⟨h20.le, ha2⟩ hcos
    · right
      have hcos2 : Real.cos (saddleAngle d ℓ₁) = Real.cos (2 * Real.pi - saddleAngle d ℓ₂) := by
        rw [Real.cos_two_pi_sub, hcos]
      have heq := Real.injOn_cos ⟨h10.le, ha1⟩ ⟨by linarith, by linarith⟩ hcos2
      linarith
    · right
      have hcos1 : Real.cos (2 * Real.pi - saddleAngle d ℓ₁) = Real.cos (saddleAngle d ℓ₂) := by
        rw [Real.cos_two_pi_sub, hcos]
      have heq := Real.injOn_cos ⟨by linarith, by linarith⟩ ⟨h20.le, ha2⟩ hcos1
      linarith
    · left
      have hcos' : Real.cos (2 * Real.pi - saddleAngle d ℓ₁) =
          Real.cos (2 * Real.pi - saddleAngle d ℓ₂) := by
        rw [Real.cos_two_pi_sub, Real.cos_two_pi_sub, hcos]
      have heq := Real.injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hcos'
      linarith
  have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  rcases hpi_cases with heq | hsum
  · unfold saddleAngle at heq
    have hmul : Real.pi * (4 * (ℓ₁ : ℝ) + 1) = Real.pi * (4 * (ℓ₂ : ℝ) + 1) :=
      (div_left_inj₀ (by positivity)).mp heq
    have hlin : 4 * (ℓ₁ : ℝ) + 1 = 4 * (ℓ₂ : ℝ) + 1 := mul_left_cancel₀ Real.pi_ne_zero hmul
    have hnat : (ℓ₁ : ℝ) = (ℓ₂ : ℝ) := by linarith
    exact_mod_cast hnat
  · exfalso
    unfold saddleAngle at hsum
    have hsum' : Real.pi * (4 * (ℓ₁ : ℝ) + 1 + (4 * (ℓ₂ : ℝ) + 1)) /
        (2 * ((d - 1 : ℕ) : ℝ)) = 2 * Real.pi := by
      rw [mul_add, add_div]
      exact hsum
    rw [div_eq_iff (by positivity)] at hsum'
    have hcancel : 4 * (ℓ₁ : ℝ) + 1 + (4 * (ℓ₂ : ℝ) + 1) = 4 * ((d - 1 : ℕ) : ℝ) := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      linarith
    have hnat : 4 * ℓ₁ + 1 + (4 * ℓ₂ + 1) = 4 * (d - 1) := by exact_mod_cast hcancel
    omega

theorem odd_active_angle_lt_pi_div_two {d ℓ : ℕ} (hd : 3 ≤ d) (ho : Odd d) (hℓ : ℓ < (d + 1) / 4) :
    0 < saddleAngle d ℓ ∧ saddleAngle d ℓ < Real.pi / 2 := by
  unfold saddleAngle
  have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  obtain ⟨m, rfl⟩ := ho
  have hnat : 4 * ℓ + 1 < 2 * m := by omega
  have hreal : 4 * (ℓ : ℝ) + 1 < ((2 * m + 1 - 1 : ℕ) : ℝ) := by
    have : 2 * m + 1 - 1 = 2 * m := by omega
    rw [this]; exact_mod_cast hnat
  refine ⟨by positivity, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) two_pos]
  nlinarith [Real.pi_pos]

/-- The exact finite set of active Stokes saddle actions in Theorem 1:
`{A_0, ..., A_{d/2 - 1}}` for even `d`, and `{A_ℓ, conj(A_ℓ) : 0 ≤ ℓ < ⌊(d+1)/4⌋}`
for odd `d`. -/
def activeSaddles (d : ℕ) : Finset ℂ := by
  classical
  exact if Even d then
    (Finset.range (d / 2)).image (saddleAction d)
  else
    ((Finset.range ((d + 1) / 4)).image (saddleAction d)) ∪
    ((Finset.range ((d + 1) / 4)).image (fun ℓ ↦ star (saddleAction d ℓ)))

theorem activeSaddles_card_even {d : ℕ} (hd : 3 ≤ d) (he : Even d) :
    (activeSaddles d).card = d / 2 := by
  classical
  simp only [activeSaddles, he, ↓reduceIte]
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro ℓ₁ h₁ ℓ₂ h₂ hEq
  rw [Finset.mem_coe, Finset.mem_range] at h₁ h₂
  exact saddleAction_im_inj hd (by omega) (by omega) (congrArg Complex.im hEq)

theorem activeSaddles_card_odd {d : ℕ} (hd : 3 ≤ d) (ho : Odd d) :
    (activeSaddles d).card = 2 * ((d + 1) / 4) := by
  classical
  have hne : ¬ Even d := Nat.not_even_iff_odd.mpr ho
  simp only [activeSaddles, hne, ↓reduceIte]
  have hdisj : Disjoint ((Finset.range ((d + 1) / 4)).image (saddleAction d))
      ((Finset.range ((d + 1) / 4)).image (fun ℓ ↦ star (saddleAction d ℓ))) := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨ℓ₁, h₁, rfl⟩ := Finset.mem_image.mp hz₁
    obtain ⟨ℓ₂, h₂, hEq⟩ := Finset.mem_image.mp hz₂
    rw [Finset.mem_range] at h₁ h₂
    obtain ⟨h10, h1h⟩ := odd_active_angle_lt_pi_div_two hd ho h₁
    obtain ⟨h20, h2h⟩ := odd_active_angle_lt_pi_div_two hd ho h₂
    have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    have him1 : (saddleAction d ℓ₁).im < 0 := by
      rw [saddleAction_im hd ℓ₁]
      nlinarith [Real.cos_pos_of_mem_Ioo ⟨by linarith, h1h⟩]
    have him2 : 0 < (star (saddleAction d ℓ₂)).im := by
      simp only [Complex.star_def, Complex.conj_im, saddleAction_im hd ℓ₂]
      nlinarith [Real.cos_pos_of_mem_Ioo ⟨by linarith, h2h⟩]
    have := congrArg Complex.im hEq
    linarith
  rw [Finset.card_union_of_disjoint hdisj]
  have hinj1 : Set.InjOn (saddleAction d) (Finset.range ((d + 1) / 4) : Set ℕ) := by
    intro ℓ₁ h₁ ℓ₂ h₂ hEq
    rw [Finset.mem_coe, Finset.mem_range] at h₁ h₂
    exact saddleAction_im_inj hd (by omega) (by omega) (congrArg Complex.im hEq)
  have hinj2 : Set.InjOn (fun ℓ ↦ star (saddleAction d ℓ)) (Finset.range ((d + 1) / 4) : Set ℕ) := by
    intro ℓ₁ h₁ ℓ₂ h₂ hEq
    exact hinj1 h₁ h₂ (star_injective hEq)
  rw [Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2, Finset.card_range]
  ring

theorem activeSaddles_re_pos {d : ℕ} (hd : 3 ≤ d) {z : ℂ} (hz : z ∈ activeSaddles d) :
    0 < z.re := by
  classical
  unfold activeSaddles at hz
  by_cases he : Even d
  · simp only [he, ↓reduceIte, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨ℓ, hℓ, rfl⟩ := hz
    exact uhp_saddle_re_pos hd hℓ
  · simp only [he, ↓reduceIte, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩
    · exact uhp_saddle_re_pos hd (by omega)
    · simp only [Complex.star_def, Complex.conj_re]
      exact uhp_saddle_re_pos hd (by omega)

theorem activeSaddles_principal_mem {d : ℕ} (hd : 3 ≤ d) :
    saddleAction d 0 ∈ activeSaddles d := by
  classical
  unfold activeSaddles
  by_cases he : Even d
  · simp only [he, ↓reduceIte, Finset.mem_image, Finset.mem_range]
    exact ⟨0, by omega, rfl⟩
  · simp only [he, ↓reduceIte, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl ⟨0, by omega, rfl⟩

theorem saddleAction_three_zero :
    saddleAction 3 0 = ⟨Real.sqrt 2, -Real.sqrt 2⟩ := by
  apply Complex.ext
  · rw [saddleAction_re (by decide : 3 ≤ 3) 0]
    have hα : saddleAngle 3 0 = Real.pi / 4 := by unfold saddleAngle; norm_num
    rw [hα, Real.sin_pi_div_four]
    norm_num
    ring
  · rw [saddleAction_im (by decide : 3 ≤ 3) 0]
    have hα : saddleAngle 3 0 = Real.pi / 4 := by unfold saddleAngle; norm_num
    rw [hα, Real.cos_pi_div_four]
    norm_num
    ring

/-! ### 4. Universal Beta-Averaged Kernel Bounds -/

/-- The universal Beta-averaged steepest-descent kernel
`H(w) = (2 / √π) ∫_0^(π/2) G(w sin² θ) dθ` (Lemma 1.1). -/
def betaAverage (G : ℝ → ℂ) (w : ℝ) : ℂ :=
  ((2 / Real.sqrt Real.pi : ℝ) : ℂ) *
    ∫ θ in Ioc (0 : ℝ) (Real.pi / 2), G (w * (Real.sin θ) ^ 2)

theorem betaAverage_zero (G : ℝ → ℂ) :
    betaAverage G 0 = ((Real.sqrt Real.pi : ℝ) : ℂ) * G 0 := by
  unfold betaAverage
  simp only [zero_mul, setIntegral_const, Real.volume_Ioc,
    sub_zero, Measure.real_def, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  exact_mod_cast (show (2 / Real.sqrt Real.pi) * (Real.pi / 2) = Real.sqrt Real.pi by
    field_simp [hpi]; linarith)

theorem betaAverage_bound {G : ℝ → ℂ} {M : ℝ} (_hM : 0 ≤ M) (hG : ∀ u ≥ 0, ‖G u‖ ≤ M)
    {w : ℝ} (hw : 0 ≤ w) :
    ‖betaAverage G w‖ ≤ Real.sqrt Real.pi * M := by
  unfold betaAverage
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hint : ‖∫ θ in Ioc (0 : ℝ) (Real.pi / 2), G (w * (Real.sin θ) ^ 2)‖ ≤
      M * (Real.pi / 2) := by
    have hle := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) (Real.pi / 2))
      (f := fun θ : ℝ ↦ G (w * (Real.sin θ) ^ 2)) (C := M)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun θ _ ↦ hG (w * (Real.sin θ) ^ 2) (mul_nonneg hw (sq_nonneg (Real.sin θ))))
    simpa [Measure.real_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi / 2), mul_comm] using hle
  calc (2 / Real.sqrt Real.pi) * ‖∫ θ in Ioc (0 : ℝ) (Real.pi / 2), G (w * (Real.sin θ) ^ 2)‖
      ≤ (2 / Real.sqrt Real.pi) * (M * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = Real.sqrt Real.pi * M := by
        have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
        have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
        field_simp [hpi]; nlinarith

/-! ### 5. Universal `PowerClass (1/2)` Wave Scaling & Expansion for ALL `d ≥ 3` -/

/-- Universal mode scale `κ_1(d) = (2π / d)^(d / (d - 1))`. -/
def modeScale (d : ℕ) : ℝ :=
  (2 * Real.pi / (d : ℝ)) ^ ((d : ℝ) / ((d - 1 : ℕ) : ℝ))

theorem modeScale_pos {d : ℕ} (hd : 3 ≤ d) : 0 < modeScale d := by
  unfold modeScale
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  exact Real.rpow_pos_of_pos (div_pos (mul_pos two_pos Real.pi_pos) hd_pos) _

/-- Mode rate `n^(d/(d-1)) * a` for any `d ≥ 3` and complex direction `a`. -/
def allDRate (d : ℕ) (a : ℂ) (n : ℕ+) : ℂ := ((rAction d n.val : ℝ) : ℂ) * a

theorem allDRate_re_pos {d : ℕ} {a : ℂ} (ha : 0 < a.re) (n : ℕ+) :
    0 < (allDRate d a n).re := by
  simp only [allDRate, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hn : (0 : ℝ) < (n.val : ℝ) := by exact_mod_cast n.property
  exact mul_pos (Real.rpow_pos_of_pos hn _) ha

/-- For every `d ≥ 3`, the exponent `d/(d-1)` sits strictly in `(1, 3/2] ⊂ [1, 2]`,
so the uniform `loss = 2` summability budget carries over identically for ALL `d ≥ 3`! -/
theorem exponent_bounds {d : ℕ} (hd : 3 ≤ d) :
    (1 : ℝ) ≤ (d : ℝ) / ((d - 1 : ℕ) : ℝ) ∧ (d : ℝ) / ((d - 1 : ℕ) : ℝ) ≤ 2 := by
  have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have h1 : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show d - 1 ≤ d by omega)
  have h2 : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show d ≤ 2 * (d - 1) by omega)
  exact ⟨(one_le_div hr_pos).mpr h1, (div_le_iff₀ hr_pos).mpr h2⟩

theorem allDRate_finite_window {d : ℕ} (hd : 3 ≤ d) {a : ℂ} (ha : 0 < a.re) (R : ℝ) :
    {n : ℕ+ | (allDRate d a n).re ≤ R}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R / a.re)
  refine ((Set.finite_le_nat N).preimage PNat.coe_injective.injOn).subset ?_
  intro n hn
  change (n : ℕ) ≤ N
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast n.property
  have hexp := (exponent_bounds hd).1
  have powle : (n : ℝ) ≤ rAction d n.val := by
    simpa [rAction] using Real.rpow_le_rpow_of_exponent_le hn1 hexp
  change (allDRate d a n).re ≤ R at hn
  simp only [allDRate, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hn
  exact_mod_cast ((le_div_iff₀ ha).mpr ((mul_le_mul_of_nonneg_right powle ha.le).trans hn)).trans hN.le

/-- Universal all-`d` Laplace wave expansion at derivative order `j` (`d ≥ 3`).
Every wave has universal outside power `p^(1/2)` (`amplitude ... (3/2) 0`),
uniform polynomial loss `2`, and exponential-decay summable budget. -/
def allDWaveJet (d : ℕ) (hd : 3 ≤ d) (a : ℂ) (ha : 0 < a.re) (F : ℕ+ → ℝ → ℂ)
    (hb : ∀ n u, 0 < u → ‖F n u‖ ≤ 1) (pref : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hpre : ∀ n, ‖pref n‖ ≤ C) (j : ℕ) : WaveExpansion ℕ+ where
  rate := allDRate d a
  amplitude := fun n x ↦ pref n * amplitude (F n) (allDRate d a n) j (3 / 2) 0 x
  loss := 2
  budget := fun n ↦ (C * boundConst j (3 / 2) 0 * (1 + ‖a‖) ^ j) *
    ((n : ℝ) ^ (2 * j) * Real.exp (-a.re * n))
  re_nonneg := fun n ↦ (allDRate_re_pos ha n).le
  budget_nonneg := fun n ↦ by
    have hbc : 0 ≤ boundConst j (3 / 2) 0 := bound_nonneg j (3 / 2) 0
    positivity
  summable_budget := by
    have h := (Real.summable_pow_mul_exp_neg_nat_mul (2 * j) ha).subtype (fun n ↦ 0 < n)
    exact h.mul_left _
  bound := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx n
    have hn : 1 ≤ (n : ℝ) := by exact_mod_cast n.property
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    obtain ⟨hexp1, hexp2⟩ := exponent_bounds hd
    have nlo : (n : ℝ) ≤ rAction d n.val := by
      simpa [rAction] using Real.rpow_le_rpow_of_exponent_le hn hexp1
    have nhi : rAction d n.val ≤ (n : ℝ) ^ 2 := by
      simpa [rAction] using Real.rpow_le_rpow_of_exponent_le hn hexp2
    have xhi : x ^ (3 / 2 : ℝ) ≤ x ^ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (3 / 2 : ℝ) ≤ 2)
    have normc : 1 + ‖allDRate d a n‖ ≤ (1 + ‖a‖) * (n : ℝ) ^ 2 := by
      have hra : 0 ≤ rAction d n.val := Real.rpow_nonneg hn0 _
      rw [allDRate, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hra]
      nlinarith [mul_le_mul_of_nonneg_right nhi (norm_nonneg a), sq_nonneg ((n : ℝ) - 1)]
    have damp : 1 ≤ Real.exp (-a.re * n) * Real.exp (allDRate d a n).re := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      simp only [allDRate, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith [mul_le_mul_of_nonneg_right nlo ha.le]
    let B := boundConst j (3 / 2) 0
    have hB : 0 ≤ B := bound_nonneg ..
    rw [norm_mul]
    calc ‖pref n‖ * ‖amplitude (F n) (allDRate d a n) j (3 / 2) 0 x‖
        ≤ C * (B * (1 + ‖allDRate d a n‖) ^ j * x ^ (3 / 2 : ℝ)) :=
          mul_le_mul (hpre n) (amplitude_bound (hb n) _ _ _ _ hx) (norm_nonneg _) hC
      _ ≤ C * (B * ((1 + ‖a‖) * (n : ℝ) ^ 2) ^ j * x ^ 2) := by
          gcongr
      _ ≤ (C * (B * ((1 + ‖a‖) * (n : ℝ) ^ 2) ^ j * x ^ 2)) *
            (Real.exp (-a.re * n) * Real.exp (allDRate d a n).re) :=
          le_mul_of_one_le_right (by positivity) damp
      _ = _ := by simp only [mul_pow, ← pow_mul]; dsimp [B]; ring

theorem allDWaveJet_derivatives (d : ℕ) (hd : 3 ≤ d) (a : ℂ) (ha : 0 < a.re)
    (F : ℕ+ → ℝ → ℂ) (hc : ∀ n, ContinuousOn (F n) (Ioi 0))
    (hb : ∀ n u, 0 < u → ‖F n u‖ ≤ 1) (pref : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hpre : ∀ n, ‖pref n‖ ≤ C) (j : ℕ) :
    iteratedDeriv j (allDWaveJet d hd a ha F hb pref C hC hpre 0).value =ᶠ[atTop]
      (allDWaveJet d hd a ha F hb pref C hC hpre j).value := by
  apply WaveExpansion.iteratedDeriv_value
  intro l
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx n
  have h := (deriv_wave (hc n) (hb n) (allDRate d a n) l (3 / 2) 0 hx).const_mul (pref n)
  simpa only [WaveExpansion.term, allDWaveJet, wave, mul_left_comm] using h

private theorem moment_density_allD {F : ℝ → ℂ} (hF : RayDensity F) (m : ℕ) :
    RayDensity (fun u : ℝ ↦ u ^ m • F u) := by
  refine ⟨fun x hx ↦ (analyticAt_id.pow m).smul (hF.1 x hx), ?_⟩
  induction m with
  | zero => simpa using hF.2
  | succ m ih => simpa only [pow_succ', mul_smul, Complex.real_smul] using ih.times_u

private theorem class_scale_allD {s f} (c : ℂ) (h : PowerClass s f) :
    PowerClass s (fun x ↦ c * f x) := by
  simpa using (PowerClass.const c).mul h

/-- Universal `PowerClass` closure for arbitrary Laplace wave jet amplitudes. -/
theorem amplitude_powerClass {F : ℝ → ℂ} (hF : RayDensity F) (c : ℂ) (j : ℕ) (s : ℝ) (m : ℕ) :
    PowerClass s (amplitude F c j s m) := by
  induction j generalizing s m with
  | zero =>
    refine ⟨-1, _, moment_density_allD hF m, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [raySum_eq_weighted _ hx, smul_smul]
    have scale : x ^ (s + ((-1 : ℤ) : ℝ)) * x = x ^ s := by
      calc x ^ (s + ((-1 : ℤ) : ℝ)) * x
          = x ^ (s - 1) * x ^ (1 : ℝ) := by simp [sub_eq_add_neg]
        _ = x ^ s := by rw [← Real.rpow_add hx]; norm_num
    rw [scale]; rfl
  | succ j ih =>
    have a := class_scale_allD (-c) (ih s m)
    have b := class_scale_allD (s : ℂ)
      ((ih (s - 1) m).reindex (t := s) (-1) (by norm_num [sub_eq_add_neg]))
    have e := class_scale_allD (-1) (ih s (m + 1))
    simpa [amplitude, sub_eq_add_neg] using (a.add b).add e

/-- **Universal `PowerClass (1/2)` Wave Scaling Lemma**: for EVERY `d ≥ 3`, every
derivative order `j ≥ 0`, and every mode `n ∈ ℕ+`, the wave jet amplitude sits
universally in `PowerClass (1/2)`. -/
theorem allDWaveJet_powerClass_half (d : ℕ) (hd : 3 ≤ d) (a : ℂ) (ha : 0 < a.re)
    (F : ℕ+ → ℝ → ℂ) (hF : ∀ n, RayDensity (F n))
    (hb : ∀ n u, 0 < u → ‖F n u‖ ≤ 1) (pref : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hpre : ∀ n, ‖pref n‖ ≤ C) (j : ℕ) (n : ℕ+) :
    PowerClass (1 / 2) ((allDWaveJet d hd a ha F hb pref C hC hpre j).amplitude n) := by
  exact class_scale_allD (pref n)
    ((amplitude_powerClass (hF n) (allDRate d a n) j (3 / 2) 0).reindex 1
      (show (3 / 2 : ℝ) = 1 / 2 + (1 : ℤ) by norm_num))

/-- Exact leading Vandermonde asymptotic for every `d ≥ 3` wave jet:
`p^(-1/2) * amplitude_j(n, p) → pref(n) * F_n(0) * (-allDRate d a n)^j`. -/
theorem allDWaveJet_limit (d : ℕ) (hd : 3 ≤ d) (a : ℂ) (ha : 0 < a.re)
    (F : ℕ+ → ℝ → ℂ) (hc : ∀ n, ContinuousOn (F n) (Ioi 0))
    (hz : ∀ n, ContinuousAt (F n) 0) (hb : ∀ n u, 0 < u → ‖F n u‖ ≤ 1)
    (pref : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hpre : ∀ n, ‖pref n‖ ≤ C) (j : ℕ) (n : ℕ+) :
    Tendsto (fun p : ℝ ↦ ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (allDWaveJet d hd a ha F hb pref C hC hpre j).amplitude n p)
      atTop (𝓝 ((pref n * F n 0) * (-allDRate d a n) ^ j)) := by
  have lim := amplitude_limit (hc n) (hz n) (hb n) (allDRate d a n) j (3 / 2) 0
  have normed : Tendsto (fun x : ℝ ↦
      ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * amplitude (F n) (allDRate d a n) j (3 / 2) 0 x)
      atTop (𝓝 ((-allDRate d a n) ^ j * F n 0)) := by
    norm_num [Complex.real_smul] at lim ⊢
    exact lim
  simpa only [allDWaveJet, mul_assoc, mul_left_comm, mul_comm] using normed.const_mul (pref n)

end
end CubicTheta.AllD
