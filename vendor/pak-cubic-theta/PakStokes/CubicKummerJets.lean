module

public import PakStokes.CubicEulerKernel
public import PakStokes.LaplaceWaveJets
import all PakStokes.WaveProducts
import all PakStokes.LaplaceWaveJets

/-! The positive-ray cubic Kummer waves form differentiable, absolutely
summable expansions at every order, for either complex action direction. -/
public section
namespace CubicTheta.LaplaceWave
open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section

def kummerFactor (c : ℂ) (p : ℝ) :=
  (Gamma (5/6))⁻¹ * ∫ y in Ioi (0:ℝ), (Real.exp (-y):ℂ)*(y:ℂ)^((5/6:ℂ)-1)*
    (1+(y:ℂ)/(2*c*p))^(-(1/6:ℂ))

private theorem rate_pos {a : ℂ} (ha : 0 < a.re) (n : ℕ+) : 0 < (cubicRate a n).re := by
  simp [cubicRate]
  have hp : 0 < (n:ℝ) := by exact_mod_cast n.property
  positivity

def modeFactor (n : ℕ+) : ℂ := ((n:ℝ)^(-(1/4:ℝ)) : ℝ)

private theorem modeFactor_bound (n : ℕ+) : ‖modeFactor n‖ ≤ 1 := by
  have hn : 1 ≤ (n:ℝ) := by exact_mod_cast n.property
  simp only [modeFactor,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)

def kummerJet (a : ℂ) (ha : 0 < a.re) (j : ℕ) :=
  cubicJet a ha (fun n ↦ cubicBetaKernel (cubicRate a n))
    (fun n _ hu ↦ cubicBeta_bound (rate_pos ha n) hu.le) modeFactor modeFactor_bound j

def kummerTerm (a : ℂ) (x : ℝ) (n : ℕ+) : ℂ :=
  Complex.exp (-cubicRate a n*x) * (modeFactor n *
    ((x^(1/2:ℝ) : ℝ) * kummerFactor (cubicRate a n) x))

def kummerSum (a : ℂ) (x : ℝ) := ∑' n : ℕ+, kummerTerm a x n

theorem kummerJet_term {a : ℂ} (ha : 0<a.re) {x : ℝ} (hx : 0<x) (n : ℕ+) :
    (kummerJet a ha 0).term x n = kummerTerm a x n := by
  unfold kummerTerm
  have eqn := (cubicBeta_raySum (rate_pos ha n) hx).symm
  change kummerFactor (cubicRate a n) x = _ at eqn
  rw [eqn,raySum_eq_weighted _ hx]
  simp only [WaveExpansion.term,kummerJet,cubicJet,amplitude,moment,Complex.real_smul,
    pow_zero,one_smul]
  rw [show (3/2:ℝ)=1/2+1 by norm_num,Real.rpow_add hx,Real.rpow_one,Complex.ofReal_mul]
  ring

theorem kummerJet_value {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    (kummerJet a ha 0).value x = kummerSum a x := tsum_congr (kummerJet_term ha hx)

theorem kummerJet_term_deriv {a : ℂ} (ha : 0<a.re) (j : ℕ) {x : ℝ} (hx : 2<x) (n : ℕ+) :
    HasDerivAt (fun y ↦ (kummerJet a ha j).term y n) ((kummerJet a ha (j+1)).term x n) x := by
  have hc := rate_pos ha n
  have h := (deriv_wave ((cubicBeta_analytic hc).continuousOn.mono Ioi_subset_Ici_self)
    (fun _ hu ↦ cubicBeta_bound hc hu.le) (cubicRate a n) j (3/2) 0 hx).const_mul (modeFactor n)
  simpa only [WaveExpansion.term,kummerJet,cubicJet,wave,mul_left_comm] using! h

/-- All real derivatives of the actual Kummer-integral series are computed
by termwise differentiation. Only positivity of the real action is required. -/
theorem kummerSum_derivatives {a : ℂ} (ha : 0 < a.re) (j : ℕ) :
    iteratedDeriv j (kummerSum a) =ᶠ[atTop] (kummerJet a ha j).value := by
  have jets := cubicJet_derivatives a ha _ (fun n ↦
    (cubicBeta_analytic (rate_pos ha n)).continuousOn.mono Ioi_subset_Ici_self)
    (fun n _ hu ↦ cubicBeta_bound (rate_pos ha n) hu.le) modeFactor modeFactor_bound j
  filter_upwards [jets,eventually_gt_atTop (0:ℝ)] with x hj hx
  refine Eq.trans ?_ hj
  have near : kummerSum a =ᶠ[𝓝 x] (kummerJet a ha 0).value :=
    (lt_mem_nhds hx).mono fun _ hy ↦ (kummerJet_value ha hy).symm
  exact near.iteratedDeriv_eq j

/-- The D_p = -d/dp convention in the manuscript cancels the sign (-1)^j. -/
theorem kummer_mode_jet_ratio {c : ℂ} (hc : 0 < c.re) (j : ℕ) :
    Tendsto (fun x : ℝ ↦ amplitude (cubicBetaKernel c) c j (3/2) 0 x /
      amplitude (cubicBetaKernel c) c 0 (3/2) 0 x) atTop (𝓝 ((-c)^j)) := by
  have anal := cubicBeta_analytic hc
  have h (l : ℕ) := amplitude_limit (anal.continuousOn.mono Ioi_subset_Ici_self)
    ((anal 0 (le_refl _)).continuousAt) (fun u hu ↦ cubicBeta_bound hc hu.le) c l (3/2) 0
  simp only [Nat.cast_zero,zero_add,Nat.factorial_zero,Nat.cast_one,one_smul,cubicBeta_zero,mul_one] at h
  have q := (h j).div (h 0) (by simp)
  simp only [pow_zero,div_one] at q
  apply q.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  simp only [Complex.real_smul,Pi.div_apply]
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne')]

end
end CubicTheta.LaplaceWave
