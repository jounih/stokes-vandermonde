module

public import PakStokes.AllD.AllDFormalTransfer
public import PakStokes.PhysicalPhases
public import PakStokes.PhysicalSeries
public import PakStokes.RegularCube
public import PakStokes.PhysicalParity
public import PakStokes.PhysicalJacobian
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Data.Set.Card
import all PakStokes.AllD.AllDFormalTransfer
import all PakStokes.AllD.ExtremeRayProjection
import all PakStokes.AllD.UniversalThimble
import all PakStokes.AllD.BesicovitchCore
import all PakStokes.PhysicalPhases
import all PakStokes.WaveProducts
import all PakStokes.PhysicalSeries
import all PakStokes.PhysicalKummer
import all PakStokes.CubicKummerJets
import all PakStokes.CubicEulerKernel
import all PakStokes.RegularCube
import all PakStokes.BackgroundJets
import all PakStokes.PhysicalParity
import all PakStokes.PhysicalJacobian
import all PakStokes.RayAlgebra
import all PakStokes.LaplaceWaveJets

/-! 1. `AllDStokesProfile d`: minimal analytic interface packaging the
steepest-descent + Beta-averaged `RayDensity` decomposition of `regularThetaD d`.
2. `TrackedExpansion`: unified extreme-ray marked-wave engine powering both
single `Θ_d(q)` and arbitrary same-degree dilations `{Θ_d(q^{a_1}), ..., Θ_d(q^{a_s})}`.
3. Concrete unconditional `d = 3` non-vacuity witness `stokesProfileThree`
constructed directly from the existing kernel-checked `PakStokes` library. -/
public section
namespace CubicTheta.AllD
open Complex Filter Set MeasureTheory LaplaceWave
open scoped Topology
noncomputable section

/-! ### 1. The Minimal All-`d` Analytic Input Profile (`AllDStokesProfile d`) -/

/-- Minimal analytic input for the all-`d` marked-wave Stokes theorem (`d ≥ 3`):
the steepest-descent decomposition of `regularThetaD d` on `p > 0` into a
`PowerClass 0` background `bg` (identically `0` for even `d`) and finitely many
active saddle branches in `activeSaddles d` with bounded real-analytic
Beta-averaged `RayDensity` kernels `kernel s n`. -/
structure AllDStokesProfile (d : ℕ) (hd : 3 ≤ d) where
  Saddle : Type
  [fintypeSaddle : Fintype Saddle]
  [decEqSaddle : DecidableEq Saddle]
  principal : Saddle
  saddleDir : Saddle → ℂ
  saddleDir_mem : ∀ s, saddleDir s ∈ activeSaddles d
  saddleDir_principal : saddleDir principal = principalSaddle d
  saddleDir_ne_principal : ∀ s, s ≠ principal → saddleDir s ≠ principalSaddle d
  kernel : Saddle → ℕ+ → ℝ → ℂ
  kernel_analytic : ∀ s n, AnalyticOnNhd ℝ (kernel s n) (Ici 0)
  kernel_bound : ∀ s n u, 0 ≤ u → ‖kernel s n u‖ ≤ 1
  kernel_principal_zero : ∀ n, kernel principal n 0 ≠ 0
  pref : Saddle → ℕ+ → ℂ
  prefBound : ℝ
  prefBound_nonneg : 0 ≤ prefBound
  pref_bound : ∀ s n, ‖pref s n‖ ≤ prefBound
  pref_principal_ne_zero : ∀ n, pref principal n ≠ 0
  bg : ℝ → ℂ
  bg_diff : ∀ j, ∀ᶠ p : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j bg) p
  bg_bound : ∀ j, ∃ (B : ℝ) (L : ℕ), 0 ≤ B ∧ ∀ᶠ p : ℝ in atTop, ‖iteratedDeriv j bg p‖ ≤ B * p ^ L
  bg_powerClass : ∀ j, PowerClass 0 (iteratedDeriv j bg)
  regular_eq : regularThetaD d =ᶠ[atTop] fun p ↦
    bg p + ∑ s : Saddle,
      (allDWaveJet d hd (((modeScale d : ℝ) : ℂ) * saddleDir s)
        (by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          exact mul_pos (modeScale_pos hd) (activeSaddles_re_pos hd (saddleDir_mem s)))
        (kernel s) (fun n u hu ↦ kernel_bound s n u hu.le)
        (pref s) prefBound prefBound_nonneg (pref_bound s) 0).value p

attribute [instance] AllDStokesProfile.fintypeSaddle AllDStokesProfile.decEqSaddle

namespace AllDStokesProfile

variable {d : ℕ} {hd : 3 ≤ d} (P : AllDStokesProfile d hd)

def branchAction (s : P.Saddle) : ℂ := ((modeScale d : ℝ) : ℂ) * P.saddleDir s

theorem branchAction_re_pos (s : P.Saddle) : 0 < (P.branchAction s).re := by
  simp only [branchAction, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (modeScale_pos hd) (activeSaddles_re_pos hd (P.saddleDir_mem s))

def branchWave (s : P.Saddle) (j : ℕ) : WaveExpansion ℕ+ :=
  allDWaveJet d hd (P.branchAction s) (P.branchAction_re_pos s)
    (P.kernel s) (fun n u hu ↦ P.kernel_bound s n u hu.le)
    (P.pref s) P.prefBound P.prefBound_nonneg (P.pref_bound s) j

theorem branchWave_rayDensity (s : P.Saddle) (n : ℕ+) : RayDensity (P.kernel s n) :=
  ⟨P.kernel_analytic s n, 1, 0, zero_le_one, le_rfl, fun u hu ↦ by simpa using P.kernel_bound s n u hu⟩

/-- Combined wave expansion over `P.Saddle × ℕ+` at derivative order `j`, optionally
rescaled by `p ↦ σ * p` (`σ > 0`) for same-degree dilations! -/
def scaledWaves (σ : ℝ) (hσ : 0 < σ) (j : ℕ) : WaveExpansion (P.Saddle × ℕ+) where
  rate := fun sn ↦ ((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2
  amplitude := fun sn x ↦ ((σ ^ j : ℝ) : ℂ) * (P.branchWave sn.1 j).amplitude sn.2 (σ * x)
  loss := 2
  budget := fun sn ↦ (σ ^ j * (max 1 σ) ^ 2 * Real.exp (0)) *
    (P.prefBound * boundConst j (3 / 2) 0 * (1 + ‖P.branchAction sn.1‖) ^ j) *
    ((sn.2 : ℝ) ^ (2 * j) * Real.exp (-(σ * (P.branchAction sn.1).re) * sn.2))
  re_nonneg := fun sn ↦ by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hσ.le (allDRate_re_pos (P.branchAction_re_pos sn.1) sn.2).le
  budget_nonneg := fun sn ↦ by
    have hP := P.prefBound_nonneg
    have hB := bound_nonneg j (3 / 2) 0
    positivity
  summable_budget := by
    rw [← (Equiv.sigmaEquivProd P.Saddle ℕ+).summable_iff]
    refine (summable_sigma_of_nonneg (fun sn ↦ by
      dsimp only [Function.comp_def, Equiv.sigmaEquivProd_apply]
      have hP := P.prefBound_nonneg; have hB := bound_nonneg j (3 / 2) 0; positivity)).mpr ⟨?_, ?_⟩
    · intro s
      have hpos : 0 < σ * (P.branchAction s).re := mul_pos hσ (P.branchAction_re_pos s)
      have h : Summable (fun n : ℕ+ ↦ (n : ℝ) ^ (2 * j) * Real.exp (-(σ * (P.branchAction s).re) * (n : ℝ))) :=
        (Real.summable_pow_mul_exp_neg_nat_mul (2 * j) hpos).subtype (fun n ↦ 0 < n)
      exact h.mul_left
        (σ ^ j * max 1 σ ^ 2 * Real.exp 0 *
          (P.prefBound * boundConst j (3 / 2) 0 * (1 + ‖P.branchAction s‖) ^ j))
    · exact hasSum_fintype _ |>.summable
  bound := by
    filter_upwards [eventually_ge_atTop (max 1 σ⁻¹)] with x hx sn
    have hx1 : 1 ≤ x := (le_max_left 1 σ⁻¹).trans hx
    have hσx1 : 1 ≤ σ * x := by
      have hle : σ⁻¹ ≤ x := (le_max_right 1 σ⁻¹).trans hx
      have := mul_le_mul_of_nonneg_left hle hσ.le
      rwa [mul_inv_cancel₀ hσ.ne'] at this
    have hn : 1 ≤ (sn.2 : ℝ) := by exact_mod_cast sn.2.property
    have hn0 : 0 ≤ (sn.2 : ℝ) := by positivity
    obtain ⟨hexp1, hexp2⟩ := exponent_bounds hd
    have nlo : (sn.2 : ℝ) ≤ rAction d sn.2.val := by
      simpa [rAction] using Real.rpow_le_rpow_of_exponent_le hn hexp1
    have nhi : rAction d sn.2.val ≤ (sn.2 : ℝ) ^ 2 := by
      simpa [rAction] using Real.rpow_le_rpow_of_exponent_le hn hexp2
    have hσx_hi : (σ * x) ^ (3 / 2 : ℝ) ≤ (max 1 σ) ^ 2 * x ^ 2 := by
      have h1 : (σ * x) ^ (3 / 2 : ℝ) ≤ (σ * x) ^ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le hσx1 (by norm_num : (3 / 2 : ℝ) ≤ 2)
      calc (σ * x) ^ (3 / 2 : ℝ) ≤ (σ * x) ^ 2 := h1
        _ = σ ^ 2 * x ^ 2 := mul_pow σ x 2
        _ ≤ (max 1 σ) ^ 2 * x ^ 2 := by gcongr; exact le_max_right 1 σ
    have normc : 1 + ‖allDRate d (P.branchAction sn.1) sn.2‖ ≤
        (1 + ‖P.branchAction sn.1‖) * (sn.2 : ℝ) ^ 2 := by
      have hra : 0 ≤ rAction d sn.2.val := Real.rpow_nonneg hn0 _
      rw [allDRate, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hra]
      nlinarith [mul_le_mul_of_nonneg_right nhi (norm_nonneg (P.branchAction sn.1)),
        sq_nonneg ((sn.2 : ℝ) - 1)]
    have hre_eq : (((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2).re =
        σ * (rAction d sn.2.val * (P.branchAction sn.1).re) := by
      simp [allDRate, Complex.mul_re]
    have damp : 1 ≤ Real.exp (-(σ * (P.branchAction sn.1).re) * sn.2) *
        Real.exp (((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2).re := by
      rw [← Real.exp_add, Real.one_le_exp_iff, hre_eq]
      have hpos : 0 ≤ σ * (P.branchAction sn.1).re := (mul_pos hσ (P.branchAction_re_pos sn.1)).le
      nlinarith [mul_le_mul_of_nonneg_left nlo hpos]
    let B := boundConst j (3 / 2) 0
    have hB : 0 ≤ B := bound_nonneg ..
    have hP := P.prefBound_nonneg
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hσ j)]
    change σ ^ j * ‖P.pref sn.1 sn.2 *
      amplitude (P.kernel sn.1 sn.2) (allDRate d (P.branchAction sn.1) sn.2) j (3 / 2) 0 (σ * x)‖ ≤ _
    rw [norm_mul]
    calc σ ^ j * (‖P.pref sn.1 sn.2‖ *
          ‖amplitude (P.kernel sn.1 sn.2) (allDRate d (P.branchAction sn.1) sn.2) j (3 / 2) 0 (σ * x)‖)
        ≤ σ ^ j * (P.prefBound * (B * (1 + ‖allDRate d (P.branchAction sn.1) sn.2‖) ^ j * (σ * x) ^ (3 / 2 : ℝ))) := by
          gcongr
          · exact P.pref_bound sn.1 sn.2
          · exact amplitude_bound (fun u hu ↦ P.kernel_bound sn.1 sn.2 u hu.le) _ _ _ _ hσx1
      _ ≤ σ ^ j * (P.prefBound * (B * ((1 + ‖P.branchAction sn.1‖) * (sn.2 : ℝ) ^ 2) ^ j *
            ((max 1 σ) ^ 2 * x ^ 2))) := by
          gcongr
      _ ≤ (σ ^ j * (P.prefBound * (B * ((1 + ‖P.branchAction sn.1‖) * (sn.2 : ℝ) ^ 2) ^ j *
            ((max 1 σ) ^ 2 * x ^ 2)))) *
          (Real.exp (-(σ * (P.branchAction sn.1).re) * sn.2) *
            Real.exp (((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2).re) :=
          le_mul_of_one_le_right (by positivity) damp
      _ = _ := by
          simp only [Real.exp_zero, mul_one, mul_pow, ← pow_mul]
          dsimp [B]; ring

theorem scaledWaves_value_zero (σ : ℝ) (hσ : 0 < σ) :
    ∀ᶠ p : ℝ in atTop,
      (P.scaledWaves σ hσ 0).value p = ∑ s : P.Saddle, (P.branchWave s 0).value (σ * p) := by
  filter_upwards [(P.scaledWaves σ hσ 0).norm_summable] with p hs
  unfold WaveExpansion.value
  have hs' : Summable (fun sn : P.Saddle × ℕ+ ↦ (P.scaledWaves σ hσ 0).term p sn) := hs.of_norm
  rw [hs'.tsum_prod]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl; intro s _
  apply tsum_congr; intro n
  simp only [WaveExpansion.term, scaledWaves, branchWave, pow_zero, Complex.ofReal_one, one_mul,
    allDWaveJet]
  congr 2; push_cast; ring

theorem scaledWaves_derivatives (σ : ℝ) (hσ : 0 < σ) (j : ℕ) :
    iteratedDeriv j (P.scaledWaves σ hσ 0).value =ᶠ[atTop] (P.scaledWaves σ hσ j).value := by
  apply WaveExpansion.iteratedDeriv_value
  intro l
  filter_upwards [eventually_gt_atTop (2 * σ⁻¹)] with x hx sn
  have hσx : 2 < σ * x := by
    have := mul_lt_mul_of_pos_left hx hσ
    rwa [← mul_assoc, mul_comm σ 2, mul_assoc, mul_inv_cancel₀ hσ.ne', mul_one] at this
  have hd_w := deriv_wave ((P.kernel_analytic sn.1 sn.2).continuousOn.mono Ioi_subset_Ici_self)
    (fun u hu ↦ P.kernel_bound sn.1 sn.2 u hu.le)
    (allDRate d (P.branchAction sn.1) sn.2) l (3 / 2) 0 hσx
  have hcomp := hd_w.scomp x ((hasDerivAt_id' x).const_mul σ)
  have hmul := hcomp.const_mul (((σ ^ l : ℝ) : ℂ) * P.pref sn.1 sn.2)
  convert hmul using 1
  · funext y
    simp only [WaveExpansion.term, scaledWaves, branchWave, allDWaveJet, wave, Function.comp_def]
    have hexp : -(((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2) * (y : ℂ) =
        -allDRate d (P.branchAction sn.1) sn.2 * ((σ * y : ℝ) : ℂ) := by push_cast; ring
    rw [hexp]; ring
  · simp only [WaveExpansion.term, scaledWaves, branchWave, allDWaveJet, wave, mul_one,
      Complex.real_smul, pow_succ, Complex.ofReal_mul]
    have hexp : -(((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2) * (x : ℂ) =
        -allDRate d (P.branchAction sn.1) sn.2 * ((σ : ℂ) * (x : ℂ)) := by ring
    rw [hexp]; ring

theorem scaledWaves_diff (σ : ℝ) (hσ : 0 < σ) (j : ℕ) :
    ∀ᶠ p : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j (P.scaledWaves σ hσ 0).value) p := by
  have hd_val := (P.scaledWaves σ hσ j).hasDerivAt_value (P.scaledWaves σ hσ (j + 1)) (by
    filter_upwards [eventually_gt_atTop (2 * σ⁻¹)] with x hx sn
    have hσx : 2 < σ * x := by
      have := mul_lt_mul_of_pos_left hx hσ
      rwa [← mul_assoc, mul_comm σ 2, mul_assoc, mul_inv_cancel₀ hσ.ne', mul_one] at this
    have hd_w := deriv_wave ((P.kernel_analytic sn.1 sn.2).continuousOn.mono Ioi_subset_Ici_self)
      (fun u hu ↦ P.kernel_bound sn.1 sn.2 u hu.le)
      (allDRate d (P.branchAction sn.1) sn.2) j (3 / 2) 0 hσx
    have hcomp := hd_w.scomp x ((hasDerivAt_id' x).const_mul σ)
    have hmul := hcomp.const_mul (((σ ^ j : ℝ) : ℂ) * P.pref sn.1 sn.2)
    convert hmul using 1
    · funext y
      simp only [WaveExpansion.term, scaledWaves, branchWave, allDWaveJet, wave, Function.comp_def]
      have hexp : -(((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2) * (y : ℂ) =
          -allDRate d (P.branchAction sn.1) sn.2 * ((σ * y : ℝ) : ℂ) := by push_cast; ring
      rw [hexp]; ring
    · simp only [WaveExpansion.term, scaledWaves, branchWave, allDWaveJet, wave, mul_one,
        Complex.real_smul, pow_succ, Complex.ofReal_mul]
      have hexp : -(((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2) * (x : ℂ) =
          -allDRate d (P.branchAction sn.1) sn.2 * ((σ : ℂ) * (x : ℂ)) := by ring
      rw [hexp]; ring)
  obtain ⟨L, hL⟩ := eventually_atTop.1 (P.scaledWaves_derivatives σ hσ j)
  filter_upwards [hd_val, eventually_gt_atTop L] with p hp hLp
  exact hp.differentiableAt.congr_of_eventuallyEq ((lt_mem_nhds hLp).mono fun y hy ↦ hL y hy.le)

theorem scaled_regular_derivatives (σ : ℝ) (hσ : 0 < σ) (j : ℕ) :
    iteratedDeriv j (fun p ↦ regularThetaD d (σ * p)) =ᶠ[atTop]
      fun p ↦ ((σ ^ j : ℝ) : ℂ) * iteratedDeriv j P.bg (σ * p) + (P.scaledWaves σ hσ j).value p := by
  have hcomp_bg (k : ℕ) :
      iteratedDeriv k (fun p ↦ P.bg (σ * p)) =ᶠ[atTop]
        fun p ↦ ((σ ^ k : ℝ) : ℂ) * iteratedDeriv k P.bg (σ * p) := by
    induction k with
    | zero => filter_upwards with p; simp
    | succ k ih =>
      obtain ⟨L, hL⟩ := eventually_atTop.1 ih
      have hdiff_s : ∀ᶠ p : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv k P.bg) (σ * p) :=
        (tendsto_id.const_mul_atTop hσ).eventually (P.bg_diff k)
      filter_upwards [eventually_gt_atTop L, hdiff_s] with p hLp hdk
      rw [iteratedDeriv_succ]
      have hnear : iteratedDeriv k (fun y ↦ P.bg (σ * y)) =ᶠ[𝓝 p]
          fun y ↦ ((σ ^ k : ℝ) : ℂ) * iteratedDeriv k P.bg (σ * y) :=
        (lt_mem_nhds hLp).mono fun y hy ↦ hL y hy.le
      rw [hnear.deriv_eq]
      have hd1 : HasDerivAt (fun y ↦ iteratedDeriv k P.bg (σ * y))
          (σ • iteratedDeriv (k + 1) P.bg (σ * p)) p := by
        rw [iteratedDeriv_succ]
        simpa only [Function.comp_def, mul_one] using
          (hdk.hasDerivAt.scomp p ((hasDerivAt_id' p).const_mul σ))
      have hd2 := hd1.const_mul ((σ ^ k : ℝ) : ℂ)
      rw [hd2.deriv, Complex.real_smul, pow_succ, Complex.ofReal_mul]
      ring
  have hbg_diff_scaled (k : ℕ) :
      ∀ᶠ p : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv k (fun y ↦ P.bg (σ * y))) p := by
    obtain ⟨L, hL⟩ := eventually_atTop.1 (hcomp_bg k)
    have hdiff_s : ∀ᶠ p : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv k P.bg) (σ * p) :=
      (tendsto_id.const_mul_atTop hσ).eventually (P.bg_diff k)
    filter_upwards [eventually_gt_atTop L, hdiff_s] with p hLp hdk
    have hnear : iteratedDeriv k (fun y ↦ P.bg (σ * y)) =ᶠ[𝓝 p]
        fun y ↦ ((σ ^ k : ℝ) : ℂ) * iteratedDeriv k P.bg (σ * y) :=
      (lt_mem_nhds hLp).mono fun y hy ↦ hL y hy.le
    have hd1 := (hdk.hasDerivAt.scomp p ((hasDerivAt_id' p).const_mul σ)).const_mul ((σ ^ k : ℝ) : ℂ)
    exact hd1.differentiableAt.congr_of_eventuallyEq hnear
  have h0 : (fun p ↦ regularThetaD d (σ * p)) =ᶠ[atTop]
      fun p ↦ P.bg (σ * p) + (P.scaledWaves σ hσ 0).value p := by
    have hreg := (tendsto_id.const_mul_atTop hσ).eventually P.regular_eq
    filter_upwards [hreg, P.scaledWaves_value_zero σ hσ] with p hr hw
    simp only [id_eq] at hr
    rw [hr, hw]
    rfl
  have hsplit : ∀ k, iteratedDeriv k (fun p ↦ regularThetaD d (σ * p)) =ᶠ[atTop]
      fun p ↦ iteratedDeriv k (fun y ↦ P.bg (σ * y)) p +
        iteratedDeriv k (P.scaledWaves σ hσ 0).value p := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      obtain ⟨L, hL⟩ := eventually_atTop.1 ih
      filter_upwards [eventually_gt_atTop L, hbg_diff_scaled k, P.scaledWaves_diff σ hσ k]
        with p hLp hdb hdw
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ]
      have hnear : iteratedDeriv k (fun y ↦ regularThetaD d (σ * y)) =ᶠ[𝓝 p]
          fun y ↦ iteratedDeriv k (fun z ↦ P.bg (σ * z)) y +
            iteratedDeriv k (P.scaledWaves σ hσ 0).value y :=
        (lt_mem_nhds hLp).mono fun y hy ↦ hL y hy.le
      have hadd : HasDerivAt
          (fun y ↦ iteratedDeriv k (fun z ↦ P.bg (σ * z)) y +
            iteratedDeriv k (P.scaledWaves σ hσ 0).value y)
          (deriv (iteratedDeriv k (fun y ↦ P.bg (σ * y))) p +
            deriv (iteratedDeriv k (P.scaledWaves σ hσ 0).value) p) p :=
        hdb.hasDerivAt.add hdw.hasDerivAt
      rw [hnear.deriv_eq, hadd.deriv]
  filter_upwards [hsplit j, hcomp_bg j, P.scaledWaves_derivatives σ hσ j] with p hs hb hw
  rw [hs, hb, hw]

theorem scaledWaves_powerClass_half (σ : ℝ) (hσ : 0 < σ) (j : ℕ) (sn : P.Saddle × ℕ+) :
    PowerClass (1 / 2) ((P.scaledWaves σ hσ j).amplitude sn) := by
  have hbase := allDWaveJet_powerClass_half d hd (P.branchAction sn.1)
    (P.branchAction_re_pos sn.1) (P.kernel sn.1) (P.branchWave_rayDensity sn.1)
    (fun n u hu ↦ P.kernel_bound sn.1 n u hu.le) (P.pref sn.1) P.prefBound
    P.prefBound_nonneg (P.pref_bound sn.1) j sn.2
  have hsc := powerClass_scale_arg hbase hσ
  simpa [scaledWaves, branchWave] using (PowerClass.const ((σ ^ j : ℝ) : ℂ)).mul hsc

theorem scaledWaves_limit (σ : ℝ) (hσ : 0 < σ) (j : ℕ) (sn : P.Saddle × ℕ+) :
    Tendsto (fun p : ℝ ↦ ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (P.scaledWaves σ hσ j).amplitude sn p)
      atTop (𝓝 ((((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * P.pref sn.1 sn.2 * P.kernel sn.1 sn.2 0) *
        (-(((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2)) ^ j)) := by
  have hbase := allDWaveJet_limit d hd (P.branchAction sn.1) (P.branchAction_re_pos sn.1)
    (P.kernel sn.1) (fun n ↦ (P.kernel_analytic sn.1 n).continuousOn.mono Ioi_subset_Ici_self)
    (fun n ↦ (P.kernel_analytic sn.1 n 0 le_rfl).continuousAt)
    (fun n u hu ↦ P.kernel_bound sn.1 n u hu.le) (P.pref sn.1) P.prefBound
    P.prefBound_nonneg (P.pref_bound sn.1) j sn.2
  have hcomp := hbase.comp (tendsto_id.const_mul_atTop hσ)
  have hmul := hcomp.const_mul (((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((σ ^ j : ℝ) : ℂ))
  have hlim_eq : (((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((σ ^ j : ℝ) : ℂ)) *
      (P.pref sn.1 sn.2 * P.kernel sn.1 sn.2 0 * (-allDRate d (P.branchAction sn.1) sn.2) ^ j) =
      (((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * P.pref sn.1 sn.2 * P.kernel sn.1 sn.2 0) *
        (-(((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2)) ^ j := by
    rw [show -(((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2) =
        ((σ : ℝ) : ℂ) * (-allDRate d (P.branchAction sn.1) sn.2) by ring, mul_pow,
        ← Complex.ofReal_pow]
    ring
  rw [hlim_eq] at hmul
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
  simp only [Function.comp_def, scaledWaves, branchWave]
  have hrp : σ ^ (1 / 2 : ℝ) * (σ * p) ^ (-(1 / 2 : ℝ)) = p ^ (-(1 / 2 : ℝ)) := by
    rw [Real.mul_rpow hσ.le hp.le, ← mul_assoc, ← Real.rpow_add hσ, add_neg_cancel,
        Real.rpow_zero, one_mul]
  have hrpC : ((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((σ * p) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hrp
  calc ((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((σ ^ j : ℝ) : ℂ) *
        ((((σ * p) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (allDWaveJet d hd (P.branchAction sn.1) (P.branchAction_re_pos sn.1)
            (P.kernel sn.1) (fun n u hu ↦ P.kernel_bound sn.1 n u hu.le)
            (P.pref sn.1) P.prefBound P.prefBound_nonneg (P.pref_bound sn.1) j).amplitude sn.2 (σ * p))
      = (((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((σ * p) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
          (((σ ^ j : ℝ) : ℂ) *
            (allDWaveJet d hd (P.branchAction sn.1) (P.branchAction_re_pos sn.1)
              (P.kernel sn.1) (fun n u hu ↦ P.kernel_bound sn.1 n u hu.le)
              (P.pref sn.1) P.prefBound P.prefBound_nonneg (P.pref_bound sn.1) j).amplitude sn.2 (σ * p)) := by ring
    _ = _ := by rw [hrpC]

theorem scaledWaves_finite_window (σ : ℝ) (hσ : 0 < σ) (j : ℕ) (R : ℝ) :
    {sn : P.Saddle × ℕ+ | ((P.scaledWaves σ hσ j).rate sn).re ≤ R}.Finite := by
  have hsub : {sn : P.Saddle × ℕ+ | ((P.scaledWaves σ hσ j).rate sn).re ≤ R} ⊆
      ⋃ s : P.Saddle, (fun n ↦ (s, n)) ''
        {n : ℕ+ | (allDRate d (P.branchAction s) n).re ≤ R / σ} := by
    rintro ⟨s, n⟩ hsn
    simp only [mem_iUnion, mem_image, mem_ofPred_eq]
    refine ⟨s, n, ?_, rfl⟩
    change (((σ : ℝ) : ℂ) * allDRate d (P.branchAction s) n).re ≤ R at hsn
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hsn
    exact (le_div_iff₀' hσ).mpr hsn
  refine (Set.finite_iUnion fun s ↦
    (allDRate_finite_window hd (P.branchAction_re_pos s) (R / σ)).image _).subset hsub

theorem scaledWaves_halfSpace (σ : ℝ) (hσ : 0 < σ) (j : ℕ) (sn : P.Saddle × ℕ+) :
    0 ≤ rotIm d ((P.scaledWaves σ hσ j).rate sn) := by
  change 0 ≤ rotIm d (((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2)
  rw [allDRate, branchAction, ← mul_assoc, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      rotIm_smul_real]
  have hpos : 0 ≤ σ * rAction d sn.2.val * modeScale d := by
    have hn : 0 ≤ (sn.2.val : ℝ) := Nat.cast_nonneg _
    have hra : 0 ≤ rAction d sn.2.val := Real.rpow_nonneg hn _
    have hms := (modeScale_pos hd).le
    positivity
  exact mul_nonneg hpos (rotIm_active_nonneg hd (P.saddleDir_mem sn.1))

theorem scaledWaves_rotIm_eq_zero_iff (σ : ℝ) (hσ : 0 < σ) (j : ℕ) (sn : P.Saddle × ℕ+) :
    rotIm d ((P.scaledWaves σ hσ j).rate sn) = 0 ↔ sn.1 = P.principal := by
  change rotIm d (((σ : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2) = 0 ↔ _
  rw [allDRate, branchAction, ← mul_assoc, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      rotIm_smul_real]
  have hpos : 0 < σ * rAction d sn.2.val * modeScale d := by
    have hn : (0 : ℝ) < (sn.2.val : ℝ) := by exact_mod_cast sn.2.property
    have hra : 0 < rAction d sn.2.val := Real.rpow_pos_of_pos hn _
    exact mul_pos (mul_pos hσ hra) (modeScale_pos hd)
  rw [mul_eq_zero, or_iff_right hpos.ne']
  constructor
  · intro h0
    by_contra hne
    have hgt := rotIm_other_active_pos hd (P.saddleDir_mem sn.1) (P.saddleDir_ne_principal sn.1 hne)
    linarith
  · intro heq
    rw [heq, P.saddleDir_principal, rotIm_principal hd]

end AllDStokesProfile

/-! ### 2. `TrackedExpansion`: Unified Extreme-Ray Marked-Wave Engine -/

abbrev RayGerm := Germ (atTop : Filter ℝ) ℂ

instance rayGermComplexAlgebra : Algebra ℂ RayGerm :=
  ((Germ.coeRingHom (atTop : Filter ℝ)).comp (Pi.constRingHom ℝ ℂ)).toAlgebra

/-- A `WaveExpansion` equipped with:
- finite bounded real-decay windows,
- `FiniteParities M` amplitudes,
- rates inside the closed half-space `{rotIm d ≥ 0}`,
- extreme-face rates lying in the range of an additive frequency map `keyRate`. -/
structure TrackedExpansion (d M : ℕ) {σ : Type*} (keyRate : (σ →₀ ℕ) →+ ℂ) where
  Index : Type
  exp : WaveExpansion Index
  finite_window : ∀ R : ℝ, {i : Index | (exp.rate i).re ≤ R}.Finite
  parities : ∀ i : Index, FiniteParities M (exp.amplitude i)
  halfSpace : ∀ i : Index, 0 ≤ rotIm d (exp.rate i)
  extreme_range : ∀ i : Index, rotIm d (exp.rate i) = 0 → ∃ k : σ →₀ ℕ, exp.rate i = keyRate k

namespace TrackedExpansion

variable {d M : ℕ} {σ : Type*} {keyRate : (σ →₀ ℕ) →+ ℂ}

def ofCoeff (a : Physical.RayCoefficient) (ha : FiniteParities M a.value) :
    TrackedExpansion d M keyRate where
  Index := Unit
  exp := a.expansion
  finite_window _ := Set.toFinite _
  parities _ := ha
  halfSpace _ := by change 0 ≤ rotIm d 0; simp
  extreme_range _ _ := ⟨0, by simp [Physical.RayCoefficient.expansion]⟩

def add (a b : TrackedExpansion d M keyRate) : TrackedExpansion d M keyRate where
  Index := a.Index ⊕ b.Index
  exp := a.exp.add b.exp
  finite_window R := by
    refine (((a.finite_window R).image Sum.inl).union ((b.finite_window R).image Sum.inr)).subset ?_
    rintro (i | j) h
    · exact Or.inl ⟨i, h, rfl⟩
    · exact Or.inr ⟨j, h, rfl⟩
  parities := by rintro (i | j); exacts [a.parities i, b.parities j]
  halfSpace := by rintro (i | j); exacts [a.halfSpace i, b.halfSpace j]
  extreme_range := by rintro (i | j) h; exacts [a.extreme_range i h, b.extreme_range j h]

def mul (hM : 0 < M) (a b : TrackedExpansion d M keyRate) : TrackedExpansion d M keyRate where
  Index := a.Index × b.Index
  exp := a.exp.mul b.exp
  finite_window R := by
    refine ((a.finite_window R).prod (b.finite_window R)).subset ?_
    rintro ⟨i, j⟩ h
    change (a.exp.rate i).re + (b.exp.rate j).re ≤ R at h
    exact ⟨(le_add_of_nonneg_right (b.exp.re_nonneg j)).trans h,
      (le_add_of_nonneg_left (a.exp.re_nonneg i)).trans h⟩
  parities := fun ⟨i, j⟩ ↦ (a.parities i).mul hM (b.parities j)
  halfSpace := fun ⟨i, j⟩ ↦ by
    change 0 ≤ rotIm d (a.exp.rate i + b.exp.rate j)
    rw [rotIm_add]; exact add_nonneg (a.halfSpace i) (b.halfSpace j)
  extreme_range := fun ⟨i, j⟩ h0 ↦ by
    change rotIm d (a.exp.rate i + b.exp.rate j) = 0 at h0
    obtain ⟨h1, h2⟩ := (extremeRay_face_iff (a.halfSpace i) (b.halfSpace j)).mp h0
    obtain ⟨k₁, hk₁⟩ := a.extreme_range i h1
    obtain ⟨k₂, hk₂⟩ := b.extreme_range j h2
    exact ⟨k₁ + k₂, by change a.exp.rate i + b.exp.rate j = _; rw [hk₁, hk₂, map_add]⟩

def finsetSum (hM : 0 < M) {ι : Type*} (S : Finset ι) (f : ι → TrackedExpansion d M keyRate) :
    TrackedExpansion d M keyRate :=
  let a0 : Physical.RayCoefficient := ⟨fun _ ↦ 0, 0, 0, le_rfl, by simp⟩
  let z : TrackedExpansion d M keyRate := ofCoeff a0 (FiniteParities.of_zero hM (PowerClass.const 0))
  S.toList.foldr (fun i acc ↦ (f i).add acc) z

/-- Exact complex-rate separation on the physical ray `p > 0` for any `TrackedExpansion`
with `FiniteParities M` amplitudes! -/
theorem separate_zero (hM : 0 < M) (e : TrackedExpansion d M keyRate)
    (hzero : ∀ᶠ x : ℝ in atTop, e.exp.value x = 0) :
    ∀ r : ℂ, ∀ᶠ x : ℝ in atTop,
      (∑' i : {i : e.Index // e.exp.rate i = r}, e.exp.amplitude i x) = 0 := by
  classical
  let padded : Set ℝ := range (fun i ↦ (e.exp.rate i).re) ∪ range (Nat.cast : ℕ → ℝ)
  have padded_fin (R : ℝ) : (padded ∩ Iic R).Finite := by
    obtain ⟨N, hN⟩ := exists_nat_gt R
    refine (((e.finite_window R).image (fun i ↦ (e.exp.rate i).re)).union
      ((Set.finite_le_nat N).image (Nat.cast : ℕ → ℝ))).subset ?_
    rintro x ⟨(⟨i, rfl⟩ | ⟨n, rfl⟩), hx⟩
    · exact Or.inl ⟨i, hx, rfl⟩
    · exact Or.inr ⟨n, by exact_mod_cast (show (n : ℝ) ≤ N from hx.trans hN.le), rfl⟩
  let rank (x : padded) := (padded ∩ Iic (x : ℝ)).ncard
  have hinc : StrictMono rank := by
    intro x y h
    apply Set.ncard_lt_ncard _ (padded_fin _)
    exact Set.ssubset_iff_subset_ne.mpr ⟨inter_subset_inter_right _ (Iic_subset_Iic.mpr h.le),
      fun eqn ↦ (not_le.mpr h)
        ((eqn ▸ (show (y : ℝ) ∈ padded ∩ Iic (y : ℝ) from ⟨y.property, le_rfl⟩) :
          (y : ℝ) ∈ padded ∩ Iic (x : ℝ))).2⟩
  let iso : padded ≃o range rank := hinc.orderIso rank
  have : Infinite padded := Infinite.of_injective
    (fun n : ℕ ↦ (⟨n, Or.inr ⟨n, rfl⟩⟩ : padded))
    (fun _ _ h ↦ Nat.cast_injective (congrArg Subtype.val h))
  let _ : Infinite (range rank) := Infinite.of_injective _ iso.injective
  let enum : ℕ ≃o padded := (Nat.Subtype.orderIsoOfNat _).trans iso.symm
  let w (n : ℕ) : ℝ := enum n
  have hw : StrictMono w := fun _ _ h ↦ enum.strictMono h
  let clusterIdx (i : e.Index) : ℕ := enum.symm ⟨(e.exp.rate i).re, Or.inl ⟨i, rfl⟩⟩
  have hw_idx (i : e.Index) : w (clusterIdx i) = (e.exp.rate i).re := by simp [w, clusterIdx]
  let Freq (n : ℕ) := {y : ℝ // ∃ i : e.Index, (e.exp.rate i).re = w n ∧ -(e.exp.rate i).im = y}
  have (n : ℕ) : Fintype (Freq n) := by
    apply Set.Finite.fintype (s := {y : ℝ | ∃ i : e.Index, (e.exp.rate i).re = w n ∧ -(e.exp.rate i).im = y})
    refine ((e.finite_window (w n)).image (fun i ↦ -(e.exp.rate i).im)).subset ?_
    rintro y ⟨i, hi, rfl⟩; exact ⟨i, hi.le, rfl⟩
  let g (i : e.Index) : Σ n, Freq n := ⟨clusterIdx i, ⟨-(e.exp.rate i).im, i, (hw_idx i).symm, rfl⟩⟩
  have hrate (i : e.Index) : e.exp.rate i = ⟨w (g i).1, -((g i).2 : ℝ)⟩ := by
    apply Complex.ext
    · exact (hw_idx i).symm
    · simp [g]
  have hasymp (k : Σ n, Freq n) :
      (∀ᶠ x : ℝ in atTop, e.exp.groupAmplitude g k x = 0) ∨
        ∃ v : ℝ, ∃ z : ℂ, z ≠ 0 ∧
          Tendsto (fun x : ℝ ↦ x ^ v • e.exp.groupAmplitude g k x) atTop (𝓝 z) := by
    have hfin : (g ⁻¹' {k}).Finite := (e.finite_window (w k.1)).subset fun i hi ↦ by
      have he : g i = k := hi
      change (e.exp.rate i).re ≤ _; rw [hrate i, he]
    let _ := hfin.fintype
    have hpar : FiniteParities M (e.exp.groupAmplitude g k) := by
      unfold WaveExpansion.groupAmplitude
      simpa [tsum_fintype] using FiniteParities.finsetSum hM Finset.univ
        (fun i : g ⁻¹' {k} ↦ e.exp.amplitude i) (fun i _ ↦ e.parities i)
    exact hpar.leading_dichotomy hM
  have hsep := separate_physical_products e.exp g w (fun _ j ↦ j.val) hrate hw
    (fun _ ↦ Subtype.val_injective) hzero hasymp
  intro r
  by_cases hex : ∃ i : e.Index, e.exp.rate i = r
  · obtain ⟨i₀, hi₀⟩ := hex
    have hset : {i : e.Index | e.exp.rate i = r} = g ⁻¹' {g i₀} := by
      ext i
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      constructor
      · intro hir
        have hre : (e.exp.rate i).re = (e.exp.rate i₀).re := by rw [hir, hi₀]
        have him : -(e.exp.rate i).im = -(e.exp.rate i₀).im := by rw [hir, hi₀]
        have hidx : clusterIdx i = clusterIdx i₀ := hw.injective (by rw [hw_idx, hw_idx, hre])
        refine Sigma.ext hidx ?_
        exact (Subtype.heq_iff_coe_eq (fun y ↦ by simp only [g, hidx])).mpr him
      · intro hg
        rw [hrate i, hg, ← hrate i₀, hi₀]
    have hz := hsep (g i₀).1 (g i₀).2
    change ∀ᶠ x : ℝ in atTop, (∑' j : g ⁻¹' {g i₀}, e.exp.amplitude j x) = 0 at hz
    filter_upwards [hz] with x hx
    rw [← hx]
    exact tsum_congr_set_coe (fun i ↦ e.exp.amplitude i x) hset
  · have : IsEmpty {i : e.Index // e.exp.rate i = r} := ⟨fun i ↦ hex ⟨i.val, i.property⟩⟩
    filter_upwards with x
    simp

abbrev Fiber (e : TrackedExpansion d M keyRate) (k : σ →₀ ℕ) :=
  {i : e.Index // e.exp.rate i = keyRate k}

noncomputable instance fiberFintype (e : TrackedExpansion d M keyRate) (k : σ →₀ ℕ) :
    Fintype (Fiber e k) := by
  apply Set.Finite.fintype (s := {i : e.Index | e.exp.rate i = keyRate k})
  apply (e.finite_window (keyRate k).re).subset
  intro i hi
  change (e.exp.rate i).re ≤ _
  rw [show e.exp.rate i = keyRate k from hi]

/-- Extreme-ray marked power series projection `TrackedExpansion → MvPowerSeries σ RayGerm`.
All off-extreme-ray saddles are discarded automatically. -/
def marked (e : TrackedExpansion d M keyRate) : MvPowerSeries σ RayGerm :=
  fun k ↦ ∑ i : Fiber e k, Germ.ofFun (e.exp.amplitude i.val)

theorem marked_zero (hM : 0 < M) (e : TrackedExpansion d M keyRate)
    (hzero : ∀ᶠ x : ℝ in atTop, e.exp.value x = 0) : e.marked = 0 := by
  classical
  apply MvPowerSeries.ext
  intro k
  change (∑ i : Fiber e k, Germ.ofFun (e.exp.amplitude i.val)) = 0
  have hz := e.separate_zero hM hzero (keyRate k)
  simp only [tsum_fintype] at hz
  let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
  change (∑ i : Fiber e k, H (e.exp.amplitude i.val)) = 0
  rw [← map_sum]
  apply Germ.coe_eq.mpr
  filter_upwards [hz] with x hx
  simpa only [Finset.sum_apply] using hx

theorem marked_coeff (a : Physical.RayCoefficient) (ha : FiniteParities M a.value)
    (hinj : Function.Injective keyRate) :
    (ofCoeff (d := d) (M := M) (keyRate := keyRate) a ha).marked =
      MvPowerSeries.C (Germ.ofFun a.value) := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst k
    let E : Fiber (ofCoeff (d := d) (M := M) (keyRate := keyRate) a ha) 0 ≃ Unit :=
      ⟨fun i ↦ i.val, fun u ↦ ⟨u, by simp [ofCoeff, Physical.RayCoefficient.expansion]⟩,
        fun _ ↦ rfl, fun _ ↦ rfl⟩
    change (∑ i : Fiber _ 0, (Germ.ofFun ((ofCoeff a ha).exp.amplitude i.val) : RayGerm)) = _
    refine (Fintype.sum_equiv E _ (fun _ ↦ (Germ.ofFun a.value : RayGerm)) (fun _ ↦ rfl)).trans ?_
    simp
  · have : IsEmpty (Fiber (ofCoeff (d := d) (M := M) (keyRate := keyRate) a ha) k) :=
      ⟨fun i ↦ hk (hinj ((map_zero keyRate).trans i.property)).symm⟩
    simp [marked, MvPowerSeries.coeff_apply, hk]

theorem marked_add (a b : TrackedExpansion d M keyRate) :
    (a.add b).marked = a.marked + b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [map_add]
  change (∑ i : Fiber (a.add b) k, _) = MvPowerSeries.coeff k a.marked + MvPowerSeries.coeff k b.marked
  let E : Fiber (a.add b) k ≃ Fiber a k ⊕ Fiber b k :=
    { toFun := fun i ↦ match i with
        | ⟨.inl j, h⟩ => .inl ⟨j, h⟩
        | ⟨.inr j, h⟩ => .inr ⟨j, h⟩
      invFun := fun i ↦ match i with
        | .inl j => ⟨.inl j.val, j.property⟩
        | .inr j => ⟨.inr j.val, j.property⟩
      left_inv := by rintro ⟨(j | j), h⟩ <;> rfl
      right_inv := by rintro (j | j) <;> rfl }
  let f : Fiber a k ⊕ Fiber b k → RayGerm :=
    Sum.elim (fun i : Fiber a k ↦ Germ.ofFun (a.exp.amplitude i.val))
      (fun i : Fiber b k ↦ Germ.ofFun (b.exp.amplitude i.val))
  rw [Fintype.sum_equiv E _ f (by rintro ⟨(j | j), h⟩ <;> rfl), Fintype.sum_sum_type]
  rfl

/-- **Extreme-Ray Multiplicativity (`marked_mul`)**: By `extremeRay_face_iff` and
injectivity of `keyRate`, NO off-extreme-ray saddle can ever contribute to an
extreme-ray fiber of a product! -/
theorem marked_mul (hM : 0 < M) (a b : TrackedExpansion d M keyRate)
    (hinj : Function.Injective keyRate) (hface : ∀ k, rotIm d (keyRate k) = 0) :
    (a.mul hM b).marked = a.marked * b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_mul, ← Finset.sum_coe_sort]
  have hsplit : ∀ i : Fiber (a.mul hM b) k,
      ∃ d₁ d₂ : σ →₀ ℕ, d₁ + d₂ = k ∧ a.exp.rate i.val.1 = keyRate d₁ ∧ b.exp.rate i.val.2 = keyRate d₂ := by
    intro i
    have hrate : a.exp.rate i.val.1 + b.exp.rate i.val.2 = keyRate k := i.property
    have hrot : rotIm d (a.exp.rate i.val.1 + b.exp.rate i.val.2) = 0 := by rw [hrate]; exact hface k
    obtain ⟨h1, h2⟩ := (extremeRay_face_iff (a.halfSpace i.val.1) (b.halfSpace i.val.2)).mp hrot
    obtain ⟨d₁, hd₁⟩ := a.extreme_range i.val.1 h1
    obtain ⟨d₂, hd₂⟩ := b.extreme_range i.val.2 h2
    have hsum : d₁ + d₂ = k := hinj (by rw [map_add, ← hd₁, ← hd₂, hrate])
    exact ⟨d₁, d₂, hsum, hd₁, hd₂⟩
  choose d₁ d₂ hsum hd₁ hd₂ using hsplit
  let E : Fiber (a.mul hM b) k ≃
      (Σ p : ↥(Finset.antidiagonal k), Fiber a p.val.1 × Fiber b p.val.2) :=
    { toFun := fun i ↦ ⟨⟨(d₁ i, d₂ i), Finset.mem_antidiagonal.mpr (hsum i)⟩,
        ⟨i.val.1, hd₁ i⟩, ⟨i.val.2, hd₂ i⟩⟩
      invFun := fun ⟨p, i, j⟩ ↦ ⟨(i.val, j.val), by
        change a.exp.rate i.val + b.exp.rate j.val = keyRate k
        rw [i.property, j.property, ← map_add, Finset.mem_antidiagonal.mp p.property]⟩
      left_inv := fun _ ↦ rfl
      right_inv := by
        rintro ⟨⟨⟨s₁, s₂⟩, hp⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩
        let u : Fiber (a.mul hM b) k := ⟨(i, j), by
          change a.exp.rate i + b.exp.rate j = keyRate k
          rw [hi, hj, ← map_add, Finset.mem_antidiagonal.mp hp]⟩
        have hs₁ : d₁ u = s₁ := hinj ((hd₁ u).symm.trans hi)
        have hs₂ : d₂ u = s₂ := hinj ((hd₂ u).symm.trans hj)
        have hp_eq : (⟨(d₁ u, d₂ u), Finset.mem_antidiagonal.mpr (hsum u)⟩ : ↥(Finset.antidiagonal k)) =
            ⟨(s₁, s₂), hp⟩ := Subtype.ext (Prod.ext hs₁ hs₂)
        have hpair : HEq
            ((⟨i, hd₁ u⟩, ⟨j, hd₂ u⟩) : Fiber a (d₁ u) × Fiber b (d₂ u))
            ((⟨i, hi⟩, ⟨j, hj⟩) : Fiber a s₁ × Fiber b s₂) := by
          have aux : ∀ (t₁ t₂ : σ →₀ ℕ) (ht₁ : a.exp.rate i = keyRate t₁) (ht₂ : b.exp.rate j = keyRate t₂),
              t₁ = s₁ → t₂ = s₂ →
              HEq ((⟨i, ht₁⟩, ⟨j, ht₂⟩) : Fiber a t₁ × Fiber b t₂)
                ((⟨i, hi⟩, ⟨j, hj⟩) : Fiber a s₁ × Fiber b s₂) := by
            rintro _ _ _ _ rfl rfl; rfl
          exact aux (d₁ u) (d₂ u) (hd₁ u) (hd₂ u) hs₁ hs₂
        exact Sigma.ext hp_eq hpair }
  let f (x : Σ p : ↥(Finset.antidiagonal k), Fiber a p.val.1 × Fiber b p.val.2) : RayGerm :=
    Germ.ofFun (a.exp.amplitude x.2.1.val) * Germ.ofFun (b.exp.amplitude x.2.2.val)
  change (∑ i : Fiber (a.mul hM b) k, (Germ.ofFun ((a.mul hM b).exp.amplitude i.val) : RayGerm)) = _
  refine (Fintype.sum_equiv E _ f (fun _ ↦ rfl)).trans ?_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro p _
  rw [Fintype.sum_prod_type]
  simp [f, marked, MvPowerSeries.coeff_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end TrackedExpansion

/-! ### 3. Variable Restriction Homomorphism on `MvPowerSeries` -/

/-- Project `MvPowerSeries σ R` onto a finite injective subset of variables `marks : ι → σ`
by setting all variables outside `range marks` to `0`. -/
def restrictVars {R σ ι : Type*} [CommRing R] [DecidableEq σ]
    (marks : ι → σ) (hinj : Function.Injective marks) :
    MvPowerSeries σ R →+* MvPowerSeries ι R where
  toFun f := fun m ↦ MvPowerSeries.coeff (m.mapDomain marks) f
  map_one' := by
    classical
    apply MvPowerSeries.ext; intro m
    change MvPowerSeries.coeff (m.mapDomain marks) (1 : MvPowerSeries σ R) =
      MvPowerSeries.coeff m (1 : MvPowerSeries ι R)
    rw [MvPowerSeries.coeff_one, MvPowerSeries.coeff_one]
    have hiff : m.mapDomain marks = 0 ↔ m = 0 := by
      constructor
      · intro h
        ext i
        have := DFunLike.congr_fun h (marks i)
        rwa [Finsupp.mapDomain_apply_of_injective hinj] at this
      · rintro rfl; simp
    simp [hiff]
  map_mul' f g := by
    classical
    apply MvPowerSeries.ext; intro m
    let rf : MvPowerSeries ι R := fun n ↦ MvPowerSeries.coeff (n.mapDomain marks) f
    let rg : MvPowerSeries ι R := fun n ↦ MvPowerSeries.coeff (n.mapDomain marks) g
    change MvPowerSeries.coeff (m.mapDomain marks) (f * g) = MvPowerSeries.coeff m (rf * rg)
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    symm
    refine Finset.sum_bij (fun p _ ↦ (p.1.mapDomain marks, p.2.mapDomain marks)) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp ⊢
      rw [← Finsupp.mapDomain_add, hp]
    · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ heq
      have h1 : a₁.mapDomain marks = a₂.mapDomain marks := congrArg Prod.fst heq
      have h2 : b₁.mapDomain marks = b₂.mapDomain marks := congrArg Prod.snd heq
      exact Prod.ext (Finsupp.mapDomain_injective hinj h1) (Finsupp.mapDomain_injective hinj h2)
    · rintro ⟨u, v⟩ huv
      rw [Finset.mem_antidiagonal] at huv
      let u' : ι →₀ ℕ := u.comapDomain marks hinj.injOn
      let v' : ι →₀ ℕ := v.comapDomain marks hinj.injOn
      have hsupp_u : ∀ x, u x ≠ 0 → ∃ i, marks i = x := by
        intro x hux
        have hsum_nz : (m.mapDomain marks) x ≠ 0 := by
          rw [← huv, Finsupp.add_apply]
          exact Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero hux) _)
        by_contra hnot
        have hm0 : (m.mapDomain marks) x = 0 := by
          by_contra hne
          have hmem := Finsupp.mapDomain_support (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
          exact hnot ⟨i, rfl⟩
        exact hsum_nz hm0
      have hsupp_v : ∀ x, v x ≠ 0 → ∃ i, marks i = x := by
        intro x hvx
        have hsum_nz : (m.mapDomain marks) x ≠ 0 := by
          rw [← huv, Finsupp.add_apply]
          exact Nat.ne_of_gt (Nat.add_pos_right _ (Nat.pos_of_ne_zero hvx))
        by_contra hnot
        have hm0 : (m.mapDomain marks) x = 0 := by
          by_contra hne
          have hmem := Finsupp.mapDomain_support (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
          exact hnot ⟨i, rfl⟩
        exact hsum_nz hm0
      have hu_eq : u'.mapDomain marks = u := by
        ext x
        by_cases hx : ∃ i, marks i = x
        · obtain ⟨i, rfl⟩ := hx
          rw [Finsupp.mapDomain_apply_of_injective hinj]
          exact Finsupp.comapDomain_apply ..
        · have hu0 : u x = 0 := by by_contra hne; exact hx (hsupp_u x hne)
          rw [hu0]
          by_contra hne
          have hmem := Finsupp.mapDomain_support (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
          exact hx ⟨i, rfl⟩
      have hv_eq : v'.mapDomain marks = v := by
        ext x
        by_cases hx : ∃ i, marks i = x
        · obtain ⟨i, rfl⟩ := hx
          rw [Finsupp.mapDomain_apply_of_injective hinj]
          exact Finsupp.comapDomain_apply ..
        · have hv0 : v x = 0 := by by_contra hne; exact hx (hsupp_v x hne)
          rw [hv0]
          by_contra hne
          have hmem := Finsupp.mapDomain_support (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
          exact hx ⟨i, rfl⟩
      refine ⟨(u', v'), ?_, Prod.ext hu_eq hv_eq⟩
      rw [Finset.mem_antidiagonal]
      apply Finsupp.mapDomain_injective hinj
      rw [Finsupp.mapDomain_add, hu_eq, hv_eq, huv]
  map_zero' := by
    apply MvPowerSeries.ext; intro m
    change MvPowerSeries.coeff (m.mapDomain marks) (0 : MvPowerSeries σ R) =
      MvPowerSeries.coeff m (0 : MvPowerSeries ι R)
    simp
  map_add' f g := by
    apply MvPowerSeries.ext; intro m
    let rf : MvPowerSeries ι R := fun n ↦ MvPowerSeries.coeff (n.mapDomain marks) f
    let rg : MvPowerSeries ι R := fun n ↦ MvPowerSeries.coeff (n.mapDomain marks) g
    change MvPowerSeries.coeff (m.mapDomain marks) (f + g) = MvPowerSeries.coeff m (rf + rg)
    rw [map_add, map_add]
    rfl

theorem restrictVars_C {R σ ι : Type*} [CommRing R] [DecidableEq σ]
    (marks : ι → σ) (hinj : Function.Injective marks) (r : R) :
    restrictVars marks hinj (MvPowerSeries.C r) = MvPowerSeries.C r := by
  classical
  apply MvPowerSeries.ext; intro m
  change MvPowerSeries.coeff (m.mapDomain marks) (MvPowerSeries.C r) =
    MvPowerSeries.coeff m (MvPowerSeries.C r)
  rw [MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  have hiff : m.mapDomain marks = 0 ↔ m = 0 := by
    constructor
    · intro h; ext i
      have := DFunLike.congr_fun h (marks i)
      rwa [Finsupp.mapDomain_apply_of_injective hinj] at this
    · rintro rfl; simp
  simp [hiff]

/-! ### 4. Concrete Unconditional Non-Vacuity Witness at `d = 3` -/

private theorem modeScale_three_mul_principal :
    ((modeScale 3 : ℝ) : ℂ) * principalSaddle 3 = Physical.action := by
  have hms : modeScale 3 = Physical.lengthScale ^ (3 / 2 : ℝ) / 3 := by
    unfold modeScale Physical.lengthScale Physical.alphaConst
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have h3 : (0 : ℝ) < (3 : ℝ) := by norm_num
    have h3p : (0 : ℝ) ≤ (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
    rw [show ((3 : ℕ) : ℝ) / ((3 - 1 : ℕ) : ℝ) = (3 / 2 : ℝ) by norm_num, Nat.cast_ofNat]
    rw [Real.div_rpow h2pi h3.le, Real.div_rpow h2pi h3p, ← Real.rpow_mul h3.le]
    rw [div_div]
    congr 1
    have h1 : (3 : ℝ) ^ (3 / 2 : ℝ) = (3 : ℝ) ^ ((1 / 3 : ℝ) * (3 / 2 : ℝ)) * 3 := by
      calc (3 : ℝ) ^ (3 / 2 : ℝ)
          = (3 : ℝ) ^ ((1 / 2 : ℝ) + 1) := by norm_num
        _ = (3 : ℝ) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ (1 : ℝ) := Real.rpow_add h3 _ _
        _ = (3 : ℝ) ^ ((1 / 3 : ℝ) * (3 / 2 : ℝ)) * 3 := by norm_num
    exact h1
  unfold Physical.action Physical.radialAction principalSaddle
  rw [saddleAction_three_zero, hms]
  apply Complex.ext <;> simp <;> ring

private theorem regularThetaD_three : regularThetaD 3 = Physical.regularCube := by
  funext p
  unfold regularThetaD Physical.regularCube
  norm_num

private theorem amplitude_star_zero (F : ℝ → ℂ) (c : ℂ) (p : ℝ) :
    amplitude (fun u ↦ star (F u)) (star c) 0 (3 / 2) 0 p = star (amplitude F c 0 (3 / 2) 0 p) := by
  simp only [amplitude, star_smul, star_trivial]
  congr 1
  rw [LaplaceWave.moment, LaplaceWave.moment]
  change (∫ u in Ioi (0 : ℝ), weighted p (fun v ↦ v ^ 0 • (starRingEnd ℂ) (F v)) u) =
    (starRingEnd ℂ) (∫ u in Ioi (0 : ℝ), weighted p (fun v ↦ v ^ 0 • F v) u)
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [weighted, pow_zero, one_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]

/-- **Unconditional Non-Vacuity Witness (`d = 3`)**: constructs `AllDStokesProfile 3`
directly from the existing kernel-checked `PakStokes` `d = 3` theorems with ZERO
additional assumptions! -/
def stokesProfileThree : AllDStokesProfile 3 (by decide) where
  Saddle := Bool
  principal := false
  saddleDir := fun b ↦ if b then star (principalSaddle 3) else principalSaddle 3
  saddleDir_mem := fun b ↦ by
    cases b
    · exact activeSaddles_principal_mem (by decide)
    · classical
      unfold activeSaddles
      have hne : ¬ Even (3 : ℕ) := by decide
      simp only [hne, ↓reduceIte, Finset.mem_union, Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨0, by decide, rfl⟩
  saddleDir_principal := rfl
  saddleDir_ne_principal := fun b hb ↦ by
    cases b
    · exact absurd rfl hb
    · intro h
      have him := congrArg Complex.im h
      simp only [↓reduceIte, principalSaddle, saddleAction_three_zero, Complex.star_def,
        Complex.conj_im] at him
      have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      linarith
  kernel := fun b n u ↦
    let K := cubicBetaKernel (cubicRate Physical.action n) u
    if b then star K else K
  kernel_analytic := fun b n ↦ by
    have hc : 0 < (cubicRate Physical.action n).re := by
      simp [cubicRate]
      have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.property
      exact mul_pos (Real.rpow_pos_of_pos hn _) Physical.action_pos
    have ha := cubicBeta_analytic hc
    cases b
    · exact ha
    · intro u hu
      exact (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (ha u hu)
  kernel_bound := fun b n u hu ↦ by
    have hc : 0 < (cubicRate Physical.action n).re := by
      simp [cubicRate]
      have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.property
      exact mul_pos (Real.rpow_pos_of_pos hn _) Physical.action_pos
    cases b
    · exact cubicBeta_bound hc hu
    · simpa using cubicBeta_bound hc hu
  kernel_principal_zero := fun n ↦ by
    change cubicBetaKernel (cubicRate Physical.action n) 0 ≠ 0
    rw [cubicBeta_zero]
    exact one_ne_zero
  pref := fun b n ↦
    let C := Physical.coefficient * modeFactor n
    if b then star C else C
  prefBound := ‖Physical.coefficient‖
  prefBound_nonneg := norm_nonneg _
  pref_bound := fun b n ↦ by
    have hm : ‖modeFactor n‖ ≤ 1 := by
      have hn : 1 ≤ (n : ℝ) := by exact_mod_cast n.property
      simp only [modeFactor, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
    have hb : ‖Physical.coefficient * modeFactor n‖ ≤ ‖Physical.coefficient‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hm
    cases b
    · exact hb
    · simpa using hb
  pref_principal_ne_zero := fun n ↦ by
    change Physical.coefficient * modeFactor n ≠ 0
    exact Physical.pref_ne n
  bg := Physical.BackgroundInverse.background
  bg_diff := fun j ↦ Physical.bg_diff j
  bg_bound := fun j ↦ ⟨(Physical.backgroundCoefficient j).budget,
    (Physical.backgroundCoefficient j).loss,
    (Physical.backgroundCoefficient j).nonneg,
    (Physical.backgroundCoefficient j).bound⟩
  bg_powerClass := fun j ↦ Physical.background_integer j
  regular_eq := by
    have hsplit : regularThetaD 3 =ᶠ[atTop] fun p ↦
        Physical.BackgroundInverse.background p + (Physical.physicalJet 0).value p := by
      filter_upwards [Physical.cubeResidual_derivatives 0] with p hp
      rw [regularThetaD_three, Physical.regularCube_split, add_comm]
      simpa using hp
    have hrate_eq (n : ℕ+) :
        allDRate 3 (((modeScale 3 : ℝ) : ℂ) * principalSaddle 3) n = cubicRate Physical.action n := by
      rw [modeScale_three_mul_principal, allDRate, cubicRate, rAction]
      norm_num
    have hrate_star (n : ℕ+) :
        allDRate 3 (((modeScale 3 : ℝ) : ℂ) * star (principalSaddle 3)) n =
          star (cubicRate Physical.action n) := by
      have hact : ((modeScale 3 : ℝ) : ℂ) * star (principalSaddle 3) = star Physical.action := by
        rw [← modeScale_three_mul_principal, star_mul', Complex.star_def, Complex.conj_ofReal,
            mul_comm]
      rw [hact, allDRate, cubicRate, rAction, star_mul', Complex.star_def, Complex.conj_ofReal]
      norm_num
    filter_upwards [hsplit,
      ((kummerJet Physical.action Physical.action_pos 0).scale Physical.coefficient).value_add
        ((kummerJet Physical.action Physical.action_pos 0).scale Physical.coefficient).conjugate]
      with p hp hadd
    rw [hp]
    congr 1
    unfold Physical.physicalJet
    rw [hadd, Fintype.sum_bool]
    rw [add_comm]
    congr 1
    · apply tsum_congr; intro n
      simp only [WaveExpansion.term, WaveExpansion.conjugate, WaveExpansion.scale, kummerJet,
        cubicJet, allDWaveJet, ↓reduceIte, hrate_star n]
      rw [amplitude_star_zero]
      simp only [star_mul']
      rw [show -(star (cubicRate Physical.action n)) * (p : ℂ) =
          (starRingEnd ℂ) (-(cubicRate Physical.action n) * (p : ℂ)) by simp, Complex.exp_conj]
      ring
    · apply tsum_congr; intro n
      simp only [WaveExpansion.term, WaveExpansion.scale, kummerJet, cubicJet, allDWaveJet,
        Bool.false_eq_true, ↓reduceIte, hrate_eq n]
      ring

end
end CubicTheta.AllD
