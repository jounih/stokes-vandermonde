module

public import LaplaceDerivative
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import PakStokes.WaveProducts
import all PakStokes.WaveProducts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Real-axis derivatives of a bounded-kernel Laplace wave. Each derivative
differentiates either the exponential, the real power, or the Laplace moment. -/
public section
namespace CubicTheta
namespace LaplaceWave
open Set Complex MeasureTheory Filter
open scoped Topology
noncomputable section

def moment (F : ℝ → ℂ) (m : ℕ) (x : ℝ) :=
  ∫ u in Ioi (0:ℝ), weighted x (fun v ↦ v^m • F v) u

private theorem kernel_growth (F : ℝ → ℂ) (hb : ∀ u > 0, ‖F u‖ ≤ 1) (m : ℕ) :
    ∀ u > 0, ‖u^m • F u‖ ≤ m.factorial*Real.exp (1*u) := by
  intro u hu
  rw [one_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hu.le _)]
  apply (mul_le_of_le_one_right (pow_nonneg hu.le _) (hb u hu)).trans
  simpa only [mul_comm] using
    (div_le_iff₀ (by positivity : (0:ℝ)<m.factorial)).mp (Real.pow_div_factorial_le_exp u hu.le m)

theorem deriv_moment {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0)) (hb : ∀ u > 0, ‖F u‖ ≤ 1)
    (m : ℕ) {x : ℝ} (hx : 2<x) : HasDerivAt (moment F m) (-moment F (m+1) x) x := by
  have h := rawLaplace_deriv ((continuous_pow m).continuousOn.smul hc) (kernel_growth F hb m) (x := x) (by linarith)
  convert! h using 1
  unfold moment
  rw [← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi; intro u _
  simp [weighted,pow_succ,mul_comm,mul_left_comm]

/-- A budget uniform in the mode only needs a common polynomial loss in x.
All x ≥ 1 share the same moment bounds. -/
theorem norm_moment {F : ℝ → ℂ} (hb : ∀ u > 0, ‖F u‖ ≤ 1) (m : ℕ) {x : ℝ} (hx : 1≤x) :
    ‖moment F m x‖ ≤ m.factorial := by
  have ev : (∫ u in Ioi (0:ℝ), u^m * Real.exp (-u)) = m.factorial := by
    simpa [Real.Gamma_nat_eq_factorial] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m:ℝ)+1) (by positivity) (by norm_num : (0:ℝ)<1)
  have hint : IntegrableOn (fun u : ℝ ↦ u^m * Real.exp (-u)) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [ev]; positivity)
  rw [← ev]
  apply norm_integral_le_of_norm_le hint
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  change 0 < u at hu
  simp only [weighted,smul_smul,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (pow_nonneg (le_of_lt hu) m)]
  have hr := Real.exp_le_exp.mpr (show -(x*u) ≤ -u by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (le_of_lt hu)])
  calc _ ≤ Real.exp (-(x*u))*u^m := mul_le_of_le_one_right (by positivity) (hb u hu)
       _ ≤ _ := by rw [mul_comm]; gcongr

/-- The amplitude after removing exp(-cx) from the jth ordinary derivative
of x^d exp(-cx) times the mth Laplace moment. -/
def amplitude (F : ℝ → ℂ) (c : ℂ) : ℕ → ℝ → ℕ → ℝ → ℂ
  | 0,d,m,x => x^d • moment F m x
  | j+1,d,m,x => (-c)*amplitude F c j d m x +
      (d:ℂ)*amplitude F c j (d-1) m x - amplitude F c j d (m+1) x

def wave (F : ℝ → ℂ) (c : ℂ) (j : ℕ) (d : ℝ) (m : ℕ) (x : ℝ) :=
  Complex.exp (-c*x)*amplitude F c j d m x

theorem deriv_wave {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0)) (hb : ∀ u > 0, ‖F u‖ ≤ 1)
    (c : ℂ) (j : ℕ) (d : ℝ) (m : ℕ) {x : ℝ} (hx : 2<x) :
    HasDerivAt (wave F c j d m) (wave F c (j+1) d m x) x := by
  induction j generalizing d m with
  | zero =>
    have he := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-c)).cexp
    have hd := (Real.hasDerivAt_rpow_const (p := d) (Or.inl (by linarith : x ≠ 0))).ofReal_comp
    have h := he.mul (hd.mul (deriv_moment hc hb m hx))
    convert! h using 1; simp [wave,amplitude,Complex.real_smul]; ring
  | succ j ih =>
    have next (l : ℕ) (y : ℝ) : wave F c (l+1) d m y =
        (-c)*wave F c l d m y + (d:ℂ)*wave F c l (d-1) m y - wave F c l d (m+1) y := by
      simp [wave,amplitude]; ring
    have h := (((ih d m).const_mul (-c)).add ((ih (d-1) m).const_mul (d:ℂ))).sub (ih d (m+1))
    simpa only [Pi.sub_apply,Pi.add_apply,show wave F c (j+1) d m = _ from funext (next j),next (j+1)] using! h

def boundConst : ℕ → ℝ → ℕ → ℝ
  | 0,_,m => m.factorial
  | j+1,d,m => boundConst j d m + |d| *boundConst j (d-1) m + boundConst j d (m+1)

private theorem bound_nonneg (j : ℕ) (d : ℝ) (m : ℕ) : 0 ≤ boundConst j d m := by
  induction j generalizing d m with
  | zero => simp [boundConst]
  | succ j ih => exact add_nonneg (add_nonneg (ih ..) (mul_nonneg (abs_nonneg _) (ih ..))) (ih ..)

theorem amplitude_bound {F : ℝ → ℂ} (hb : ∀ u > 0, ‖F u‖ ≤ 1)
    (c : ℂ) (j : ℕ) (d : ℝ) (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖amplitude F c j d m x‖ ≤ boundConst j d m * (1+‖c‖)^j * x^d := by
  have xp := zero_lt_one.trans_le hx
  induction j generalizing d m with
  | zero =>
    simp only [amplitude,boundConst,pow_zero,mul_one,norm_smul,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos xp d)]
    rw [mul_comm]; gcongr; exact norm_moment hb m hx
  | succ j ih =>
    let L := 1+‖c‖
    have le : 1 ≤ L := by dsimp [L]; linarith [norm_nonneg c]
    have pow : L^j ≤ L^(j+1) := pow_le_pow_right₀ le (Nat.le_succ j)
    have cp : ‖c‖*L^j ≤ L^(j+1) := by rw [pow_succ']; gcongr; dsimp [L]; linarith
    have xp' : x^(d-1) ≤ x^d := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    unfold amplitude
    apply (norm_sub_le ..).trans
    apply (add_le_add (norm_add_le ..) (le_refl _)).trans
    rw [norm_mul,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (ih d m) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (ih (d-1) m) (abs_nonneg _))) (ih d (m+1))).trans
    change ‖c‖*(boundConst j d m*L^j*x^d)+|d| *(boundConst j (d-1) m*L^j*x^(d-1))+
      boundConst j d (m+1)*L^j*x^d ≤ _ * L^(j+1)*x^d
    rw [show ‖c‖*(boundConst j d m*L^j*x^d) = boundConst j d m*(‖c‖*L^j)*x^d by ring]
    rw [show boundConst (j+1) d m = boundConst j d m + |d| * boundConst j (d-1) m + boundConst j d (m+1) by rfl,
      show |d| *(boundConst j (d-1) m*L^j*x^(d-1)) = (|d| *boundConst j (d-1) m)*L^j*x^(d-1) by ring]
    simp only [add_mul]
    have h0 := bound_nonneg j d m
    have h1 := bound_nonneg j (d-1) m
    have h2 := bound_nonneg j d (m+1)
    have hL : 0 ≤ L := zero_le_one.trans le
    gcongr

/-- The leading term of every jet follows from the same real moment
representation. Both terms where the derivative misses the exponential
gain a factor 1/x. -/
theorem amplitude_limit {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0))
    (hz : ContinuousAt F 0) (hb : ∀ u > 0, ‖F u‖ ≤ 1)
    (c : ℂ) (j : ℕ) (d : ℝ) (m : ℕ) :
    Tendsto (fun x : ℝ ↦ x^((m:ℝ)+1-d) • amplitude F c j d m x) atTop
      (𝓝 ((-c)^j * ((m.factorial:ℝ) • F 0))) := by
  induction j generalizing d m with
  | zero =>
    have h := raySum_leading ((continuous_pow m).continuousOn.smul hc) (by norm_num : (0:ℝ)≤1)
      (kernel_growth F hb m) hz (Eventually.of_forall fun _ ↦ rfl)
    simp only [pow_zero,one_mul]
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [raySum_eq_weighted _ hx,amplitude,moment,smul_smul,smul_smul,← Real.rpow_add hx]
    congr 1; rw [sub_add_cancel,Real.rpow_add hx,Real.rpow_natCast,Real.rpow_one]
  | succ j ih =>
    let v := (m:ℝ)+1-d
    have down {f : ℝ → ℂ} {z : ℂ} (h : Tendsto (fun x : ℝ ↦ x^(v+1) • f x) atTop (𝓝 z)) :
        Tendsto (fun x : ℝ ↦ x^v • f x) atTop (𝓝 0) := by
      have inv := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)
      have q := inv.smul h
      rw [zero_smul] at q
      apply q.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [smul_smul,← Real.rpow_add hx,show -(1:ℝ)+(v+1)=v by ring]
    have h1 := down (f := amplitude F c j (d-1) m)
      (by simpa only [v,show (m:ℝ)+1-(d-1)=(m:ℝ)+1-d+1 by ring] using ih (d-1) m)
    have h2 := down (f := amplitude F c j d (m+1))
      (by simpa only [v,Nat.cast_add,Nat.cast_one,show (m:ℝ)+1+1-d=(m:ℝ)+1-d+1 by ring] using ih d (m+1))
    have h := (((ih d m).const_mul (-c)).add (h1.const_mul (d:ℂ))).sub h2
    rw [mul_zero,add_zero,sub_zero,← mul_assoc,← pow_succ'] at h
    apply h.congr
    intro x
    simp only [amplitude,smul_sub,smul_add,mul_smul_comm,v]
def cubicRate (a : ℂ) (n : ℕ+) : ℂ := ((n:ℝ)^(3/2:ℝ) : ℝ)*a

/-- Every fixed order of cubic-wave derivatives is an absolutely summable
expansion, with a single x² loss independent of the derivative order. A bounded
mode prefactor can absorb n^(-1/4) and its constant can be taken outside. -/
def cubicJet (a : ℂ) (ha : 0 < a.re) (F : ℕ+ → ℝ → ℂ)
    (hb : ∀ n u, 0<u → ‖F n u‖ ≤ 1) (pref : ℕ+ → ℂ) (hpre : ∀ n, ‖pref n‖ ≤ 1)
    (j : ℕ) : WaveExpansion ℕ+ where
  rate := cubicRate a
  amplitude := fun n x ↦ pref n * amplitude (F n) (cubicRate a n) j (3/2) 0 x
  loss := 2
  budget := fun n ↦ (boundConst j (3/2) 0*(1+‖a‖)^j)*
    ((n:ℝ)^(2*j)*Real.exp (-a.re*n))
  re_nonneg := fun n ↦ by simp [cubicRate]; positivity
  budget_nonneg := fun n ↦ by have := bound_nonneg j (3/2) 0; positivity
  summable_budget := by
    have h := (Real.summable_pow_mul_exp_neg_nat_mul (2*j) ha).subtype (fun n ↦ 0<n)
    exact h.mul_left _
  bound := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx n
    have hn : 1 ≤ (n:ℝ) := by exact_mod_cast n.property
    have hn0 : 0 ≤ (n:ℝ) := by positivity
    have nlo : (n:ℝ) ≤ (n:ℝ)^(3/2:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)≤3/2)
    have nhi : (n:ℝ)^(3/2:ℝ) ≤ (n:ℝ)^2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (3/2:ℝ)≤2)
    have xhi : x^(3/2:ℝ) ≤ x^2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (3/2:ℝ)≤2)
    have normc : 1+‖cubicRate a n‖ ≤ (1+‖a‖)*(n:ℝ)^2 := by
      rw [cubicRate,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right nhi (norm_nonneg a),sq_nonneg ((n:ℝ)-1)]
    have damp : 1 ≤ Real.exp (-a.re*n)*Real.exp (cubicRate a n).re := by
      rw [← Real.exp_add,Real.one_le_exp_iff]; simp [cubicRate]
      nlinarith [mul_le_mul_of_nonneg_right nlo ha.le]
    let C := boundConst j (3/2) 0
    have hC : 0 ≤ C := bound_nonneg ..
    rw [norm_mul]
    calc _ ≤ ‖amplitude (F n) (cubicRate a n) j (3/2) 0 x‖ :=
           mul_le_of_le_one_left (norm_nonneg _) (hpre n)
         _ ≤ _ := amplitude_bound (hb n) _ _ _ _ hx
         _ ≤ C*((1+‖a‖)*(n:ℝ)^2)^j*x^2 := by
           dsimp [C]; gcongr
         _ ≤ (C*((1+‖a‖)*(n:ℝ)^2)^j*x^2) *
               (Real.exp (-a.re*n)*Real.exp (cubicRate a n).re) :=
           le_mul_of_one_le_right (by positivity) damp
         _ = _ := by simp only [mul_pow,← pow_mul]; dsimp [C]; ring

theorem cubicJet_derivatives (a : ℂ) (ha : 0 < a.re) (F : ℕ+ → ℝ → ℂ)
    (hc : ∀ n, ContinuousOn (F n) (Ioi 0)) (hb : ∀ n u, 0<u → ‖F n u‖ ≤ 1)
    (pref : ℕ+ → ℂ) (hpre : ∀ n, ‖pref n‖ ≤ 1) (j : ℕ) :
    iteratedDeriv j (cubicJet a ha F hb pref hpre 0).value =ᶠ[atTop]
      (cubicJet a ha F hb pref hpre j).value := by
  apply WaveExpansion.iteratedDeriv_value
  intro l
  filter_upwards [eventually_gt_atTop (2:ℝ)] with x hx n
  have h := (deriv_wave (hc n) (hb n) (cubicRate a n) l (3/2) 0 hx).const_mul (pref n)
  simpa only [WaveExpansion.term,cubicJet,wave,mul_left_comm] using h

end
end LaplaceWave
end CubicTheta
