module

public import PakStokes.AiryContourODE
public import PakStokes.KummerEquation
public import PakStokes.CubicKummerJets
import all PakStokes.AiryContourODE
import all PakStokes.KummerEquation
import all PakStokes.PhysicalAiry
import all PakStokes.CubicKummerJets

/-! Compare the positive-temperature Airy contour with the exact Kummer and
Euler integrals on X=hr. The normalization is fixed by the value at zero. -/
public section
namespace CubicTheta.Physical
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

def radialAction : ℂ := ⟨Real.sqrt 2/3,-Real.sqrt 2/3⟩
private abbrev d := radialAction
private theorem dpos : 0 < d.re := by unfold d radialAction; simp
private theorem action_sq : 9*d^2=4*h^3 := by
  have s := Real.sq_sqrt (show 0 ≤ (3:ℝ) by norm_num)
  have t := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  apply Complex.ext <;> norm_num [d,radialAction,h,pow_succ,Complex.mul_re,Complex.mul_im] <;>
    nlinarith [congrArg (fun y : ℝ ↦ y*Real.sqrt 3) s]

def radialFrequency (x : ℝ) := d*((x^(3/2:ℝ):ℝ):ℂ)
private abbrev Z := radialFrequency
private def D (x : ℝ) := (3/2:ℂ)*d*((x^(1/2:ℝ):ℝ):ℂ)
private def DD (x : ℝ) := (3/4:ℂ)*d*((x^(-(1/2:ℝ)):ℝ):ℂ)
private theorem dz {x : ℝ} (hx : 0<x) : HasDerivAt Z (D x) x := by
  have h := ((Real.hasDerivAt_rpow_const (p := 3/2) (Or.inl hx.ne')).ofReal_comp).const_mul d
  convert! h using 1; norm_num [D]; ring
private theorem ddz {x : ℝ} (hx : 0<x) : HasDerivAt D (DD x) x := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1/2) (Or.inl hx.ne')).ofReal_comp).const_mul ((3/2:ℂ)*d)
  convert! h using 1; norm_num [DD]; ring
private theorem zpos {x : ℝ} (hx : 0<x) : 0 < (Z x).re := by
  simp only [Z,radialFrequency,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; exact mul_pos dpos (Real.rpow_pos_of_pos hx _)

private theorem scales {x : ℝ} (hx : 0<x) :
    D x ^ 2 = h^3*x ∧ 3*Z x*DD x = D x ^ 2 := by
  have half : (x^(1/2:ℝ))^2 = x := by rw [sq,← Real.rpow_add hx]; norm_num
  have full : x^(3/2:ℝ)*x^(-(1/2:ℝ)) = x := by rw [← Real.rpow_add hx]; norm_num
  have h1 : ((x^(1/2:ℝ):ℝ):ℂ)^2 = x := by exact_mod_cast half
  have h2 : ((x^(3/2:ℝ):ℝ):ℂ)*((x^(-(1/2:ℝ)):ℝ):ℂ) = x := by exact_mod_cast full
  constructor
  · unfold D; rw [mul_pow,h1]; linear_combination (x:ℂ)/4 * action_sq
  · unfold D DD Z radialFrequency; rw [mul_pow,h1]; linear_combination (9/4:ℂ)*d^2 * h2

private def U (z : ℂ) := Complex.exp (-z)*kummerMoment 0 z
private def V (z : ℂ) := Complex.exp (-z)*(-kummerMoment 0 z-kummerMoment 1 z/3)
private def W (z : ℂ) := Complex.exp (-z)*(kummerMoment 0 z+2*kummerMoment 1 z/3+7*kummerMoment 2 z/9)

private theorem dU {z : ℂ} (hz : 0<z.re) : HasDerivAt U (V z) z := by
  have h := ((hasDerivAt_id z).neg.cexp).mul (kummerMoment_deriv hz 0)
  convert! h using 1; norm_num [V,exponent]; ring
private theorem dV {z : ℂ} (hz : 0<z.re) : HasDerivAt V (W z) z := by
  have h := ((hasDerivAt_id z).neg.cexp).mul
    ((kummerMoment_deriv hz 0).neg.sub ((kummerMoment_deriv hz 1).div_const 3))
  convert! h using 1; norm_num [W,exponent]; ring
private theorem zODE {z : ℂ} (hz : 0<z.re) : 3*z*(W z-U z)+V z=0 := by
  unfold U V W
  linear_combination Complex.exp (-z) * kummerMoment_equation hz

private def Y (x : ℝ) := U (Z x)
private def Y' (x : ℝ) := V (Z x)*D x

private theorem dY {x : ℝ} (hx : 0<x) : HasDerivAt Y (Y' x) x := by
  simpa only [Y,Y',Function.comp_def,mul_comm] using! (dU (zpos hx)).scomp x (dz hx)
private theorem ddY {x : ℝ} (hx : 0<x) : HasDerivAt Y' (h^3*x*Y x) x := by
  have h := ((dV (zpos hx)).scomp x (dz hx)).mul (ddz hx)
  convert! h using 1
  have e := zODE (zpos hx)
  have sc := scales hx
  simp only [Function.comp_apply,smul_eq_mul]
  unfold Y
  rw [← sc.1]
  linear_combination -DD x * e + (U (Z x)-W (Z x)) * (-sc.2)

private theorem decayExp (s : ℝ) :
    Tendsto (fun x : ℝ ↦ Complex.exp (-Z x)*((x^s:ℝ):ℂ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ ↦ x^s*Real.exp (-d.re*x))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hxp := zero_lt_one.trans_le hx
    have hpow : x ≤ x^(3/2:ℝ) := by simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1:ℝ)≤3/2)
    simp only [norm_mul,norm_exp,neg_re,Z,radialFrequency,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,norm_real,
      Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hxp _)]
    rw [mul_comm]; gcongr; nlinarith [mul_le_mul_of_nonneg_left hpow dpos.le]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ dpos

private theorem boundedM (j : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ ↦ ‖kummerMoment j (Z x)‖) := by
  refine ⟨(∫ v in Ioi (0:ℝ), ‖base v‖)*d.re^exponent j,eventually_map.2 ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  apply moment_bound_on_halfplane dpos
  change d.re ≤ (d*↑(x^(3/2:ℝ))).re
  simp; exact le_mul_of_one_le_right dpos.le (Real.one_le_rpow hx (by norm_num))

private theorem decY : Tendsto Y atTop (𝓝 0) := by
  have q := (decayExp 0).zero_mul_isBoundedUnder_le (boundedM 0)
  change Tendsto (fun x ↦ Complex.exp (-Z x)*kummerMoment 0 (Z x)) _ _
  simpa using q

private theorem decY' : Tendsto Y' atTop (𝓝 0) := by
  have h0 := (decayExp (1/2)).zero_mul_isBoundedUnder_le (boundedM 0)
  have h1 := (decayExp (1/2)).zero_mul_isBoundedUnder_le (boundedM 1)
  have lim := (h0.neg.sub (h1.div_const 3)).const_mul ((3/2:ℂ)*d)
  simp only [neg_zero,zero_div,sub_zero,mul_zero] at lim
  apply lim.congr; intro x
  dsimp [Y',V,D]; ring

private theorem atOrigin : Tendsto Y (𝓝[>] 0) (𝓝 (Gamma (2/3))) := by
  have hz : Tendsto Z (𝓝[>] 0) (𝓝 0) := by
    have cp : Continuous Z := by unfold Z radialFrequency; fun_prop (disch := norm_num)
    have l := (cp.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    rwa [show Z 0 = 0 by simp [Z,radialFrequency,Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0)]] at l
  have h := (Complex.continuous_exp.tendsto (0:ℂ)).comp (by simpa using hz.neg : Tendsto (fun x ↦ -Z x) _ (𝓝 0))
  change Tendsto (fun x ↦ Complex.exp (-Z x)*kummerMoment 0 (Z x)) _ _
  simpa using h.mul (kummerMoment_origin hz (eventually_of_mem self_mem_nhdsWithin fun _ hx ↦ zpos hx))

/-- Equality of the actual Poisson Airy contour with a recessive Kummer
integral. The constant is expressed through their values at the origin. -/
theorem physical_contour_kummer {x : ℝ} (hx : 0<x) :
    airyContour (h*x) = airyContour 0 / Gamma (2/3) *
      (Complex.exp (-radialFrequency x)*kummerMoment 0 (radialFrequency x)) := by
  let C := airyContour 0 / Gamma (2/3)
  have gn : Gamma (2/3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have cn : C ≠ 0 := div_ne_zero origin_nonzero gn
  apply identify_physical_contour (fun y ↦ C*Y y) (fun y ↦ C*Y' y)
    (fun y hy ↦ (dY hy).const_mul C) _ _ _ _ _ x hx
  · intro y hy; convert! (ddY hy).const_mul C using 1; ring
  · simpa using decY.const_mul C
  · simpa using decY'.const_mul C
  · intro y hy; exact mul_ne_zero cn (mul_ne_zero (Complex.exp_ne_zero _) (kummerMoment_ne_zero (zpos hy)))
  · simpa [C,gn] using atOrigin.const_mul C

/-- The branch check needed to pass from the recessive integral to the same
Kummer factor that occurs in the differentiated series. Both factors in the
product have positive real part. -/
theorem kummerMoment_factor {c : ℂ} (hc : 0<c.re) {p : ℝ} (hp : 0<p) :
    kummerMoment 0 (c*p) = (2*c*p)^(-(1/6:ℂ))*Gamma (5/6)*LaplaceWave.kummerFactor c p := by
  have den : 0 < (2*c*p).re := by simp; positivity
  have dn : 2*c*p ≠ 0 := fun hh ↦ by simp [hh] at den
  have gn : Gamma (5/6) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  unfold LaplaceWave.kummerFactor
  rw [mul_assoc _ (Gamma _),← mul_assoc (Gamma _),mul_inv_cancel₀ gn,one_mul,← integral_const_mul]
  unfold kummerMoment
  apply setIntegral_congr_fun measurableSet_Ioi; intro v hv
  let f := 1+(v:ℂ)/(2*c*p)
  have fp : 0 < f.re := by
    dsimp [f]; rw [div_eq_mul_inv,Complex.mul_re,Complex.inv_re]
    simp only [ofReal_re,ofReal_im,zero_mul,sub_zero]
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (le_of_lt hv) (div_nonneg den.le (normSq_nonneg _)))
  have branch := mul_cpow (a := 2*c*p) (b := f) (r := -(1/6:ℂ)) (by
    have h1 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (.inl den))
    have h2 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (.inl fp))
    constructor <;> linarith)
  have eqn : (2*c*p)*f = (v:ℂ)+2*(c*p) := by unfold f; rw [mul_add,mul_one,mul_div_cancel₀ _ dn]; ring
  rw [eqn] at branch
  change base v * ((v:ℂ)+2*(c*p))^((exponent 0:ℝ):ℂ) = _
  rw [show ((exponent 0:ℝ):ℂ) = -(1/6:ℂ) by norm_num [exponent],branch]
  dsimp [base,f]; norm_num; ring

def airyWaveConstant :=
  airyContour 0 / Gamma (2/3) * (2*radialAction)^(-(1/6:ℂ)) * Gamma (5/6)

/-- Normalize a single physical contour mode as x^(-1/4) times the exact
cubic Kummer wave. The constant is independent of x. -/
theorem physical_contour_factor {x : ℝ} (hx : 0<x) :
    airyContour (h*x) = airyWaveConstant * ((x^(-(1/4:ℝ)):ℝ):ℂ) *
      Complex.exp (-radialFrequency x) * LaplaceWave.kummerFactor radialAction (x^(3/2:ℝ)) := by
  rw [physical_contour_kummer hx]
  set p := x^(3/2:ℝ)
  have hp : 0<p := Real.rpow_pos_of_pos hx _
  rw [show radialFrequency x = radialAction*p from rfl,kummerMoment_factor dpos hp]
  have split : (2*radialAction*(p:ℂ))^(-(1/6:ℂ)) =
      (2*radialAction)^(-(1/6:ℂ))*((x^(-(1/4:ℝ)):ℝ):ℂ) := by
    rw [mul_cpow (by simp [arg_ofReal_of_nonneg hp.le,neg_pi_lt_arg,arg_le_pi])]
    have realpow := Complex.ofReal_cpow hp.le (-(1/6:ℝ))
    push_cast at realpow
    rw [← realpow,show p^(-(1/6:ℝ))=x^(-(1/4:ℝ)) by unfold p; rw [← Real.rpow_mul hx.le]; norm_num]
  rw [split,airyWaveConstant]; ring

theorem airyWaveConstant_ne_zero : airyWaveConstant ≠ 0 :=
  mul_ne_zero (mul_ne_zero (div_ne_zero origin_nonzero (Gamma_ne_zero_of_re_pos (by norm_num)))
    (by apply Complex.cpow_ne_zero_iff.mpr; left; exact mul_ne_zero (by norm_num) (fun hh ↦ by have hp := dpos; change 0 < radialAction.re at hp; simp [hh] at hp)))
    (Gamma_ne_zero_of_re_pos (by norm_num))

end
end CubicTheta.Physical
