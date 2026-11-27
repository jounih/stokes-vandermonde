module

public import PakStokes.BackgroundContour
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import all PakStokes.BackgroundContour
import all PakStokes.BackgroundInverse
import all PakStokes.PhysicalAiry

/-! Complex normal convergence of the physical background kernel. The inverse
at unit frequency supplies one analytic germ at zero for the whole tail. -/
public section
namespace CubicTheta.Physical.BackgroundInverse
open Complex Set Filter
open scoped Topology
noncomputable section

private theorem odd_inverse {b : ℝ} (hb : 0<b) (v : ℝ) :
    inverse hb (-v) = -inverse hb v := by simp [inverse]

private theorem root_scale {b : ℝ} (hb : 0<b) (v : ℝ) :
    inverse hb v = (Real.sqrt b:ℂ)*inverse (b := 1) (by norm_num) (v/(Real.sqrt b*b)) := by
  let s := Real.sqrt b
  have sp : 0<s := Real.sqrt_pos.mpr hb
  have sq : (s:ℂ)^2=(b:ℂ) := by exact_mod_cast Real.sq_sqrt hb.le
  have positive (u : ℝ) (hu : 0≤u) := inverse_wedge (b := 1) (by norm_num) (div_nonneg hu (mul_nonneg sp.le hb.le))
  have eqpos (u : ℝ) (hu : 0≤u) : inverse hb u = (s:ℂ)*inverse (b := 1) (by norm_num) (u/(s*b)) := by
    let y := inverse (b := 1) (by norm_num) (u/(s*b))
    have hy : Wedge y := positive u hu
    have hw : Wedge ((s:ℂ)*y) := by
      simp only [Wedge,mul_re,mul_im,ofReal_im,ofReal_re,zero_mul,sub_zero,add_zero]
      refine ⟨mul_nonneg sp.le hy.1,mul_nonpos_of_nonneg_of_nonpos sp.le hy.2.1,?_⟩
      simpa [neg_mul,div_eq_mul_inv,mul_assoc] using mul_le_mul_of_nonneg_left hy.2.2 sp.le
    apply phase_injective hb (inverse_wedge hb hu) hw
    have he := inverse_spec (b := 1) (by norm_num) (u/(s*b))
    change phase 1 y = _ at he
    rw [inverse_spec]
    unfold phase at he ⊢; push_cast at he
    have sc : (s:ℂ)*(b:ℂ)*((u:ℂ)/((s:ℂ)*(b:ℂ)))=u := mul_div_cancel₀ _ (mul_ne_zero (ofReal_ne_zero.mpr sp.ne') (ofReal_ne_zero.mpr hb.ne'))
    linear_combination -((s:ℂ)*(b:ℂ))*he - (s:ℂ)*y^3*sq - sc
  by_cases hv : 0≤v
  · exact eqpos v hv
  · have he := eqpos (-v) (neg_nonneg.mpr (le_of_not_ge hv))
    rw [neg_div,odd_inverse,odd_inverse,mul_neg,neg_inj] at he
    exact he

private def unitRoot (v : ℝ) := inverse (b := 1) (by norm_num) v
private def rationalFactor (y : ℂ) := -3*I/((y^2+k)^2*(3*y^2+k))

private theorem unit_germ : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
    ∀ᶠ v : ℝ in 𝓝 0, A v = rationalFactor (unitRoot v) := by
  have poly : AnalyticAt ℂ (phase 1) 0 := by unfold phase; fun_prop
  have d : HasDerivAt (phase 1) k 0 := by
    unfold phase; push_cast
    simpa [Pi.add_def] using! ((hasDerivAt_pow 3 (0:ℂ)).add ((hasDerivAt_id (0:ℂ)).const_mul k))
  have kn : k ≠ 0 := by intro h; have hp := linear_pos (b := 1) (by norm_num); simp [h] at hp
  have hn : deriv (phase 1) 0 ≠ 0 := by rwa [d.deriv]
  let g := poly.hasStrictDerivAt.localInverse (phase 1) _ 0 hn
  have hg : AnalyticAt ℂ g 0 := by simpa [phase] using poly.analyticAt_localInverse hn
  have eqn := poly.hasStrictDerivAt.eventually_left_inverse hn
  have cont : Continuous unitRoot := (posRoot_continuous _).sub ((posRoot_continuous _).comp continuous_neg)
  have z : unitRoot 0 = 0 := inverse_zero _
  have eqn' : ∀ᶠ x in 𝓝 (unitRoot 0), g (phase 1 x) = x := by rw [z]; exact eqn
  have near := (show ContinuousAt unitRoot 0 from cont.continuousAt).preimage_mem_nhds eqn'
  have eg : ∀ᶠ v : ℝ in 𝓝 0, g v = unitRoot v := by
    filter_upwards [near] with v hv
    change g (phase 1 (unitRoot v)) = unitRoot v at hv
    rwa [show phase 1 (unitRoot v) = v from inverse_spec _ v] at hv
  have g0 : g 0 = 0 := by simpa [z] using eg.self_of_nhds
  have factor : AnalyticAt ℂ rationalFactor 0 := by unfold rationalFactor; fun_prop (disch := simp [kn])
  exact ⟨rationalFactor ∘ g,(g0.symm ▸ factor).comp hg,eg.mono (fun v he ↦ congrArg rationalFactor he)⟩

private def realProjection : ℂ →L[ℝ] ℂ := (2:ℝ) • Complex.ofRealCLM.comp Complex.reCLM

private theorem realProjection_apply (z : ℂ) : realProjection z = ((2*z.re:ℝ):ℂ) := by
  simp [realProjection,Complex.real_smul]

private theorem kernel_factor {b : ℝ} (hb : 0<b) (v : ℝ) :
    kernel hb v = realProjection ((v:ℂ)^2/(b:ℂ)^4 * rationalFactor (unitRoot (v/(Real.sqrt b*b)))) := by
  let s := Real.sqrt b
  let y := unitRoot (v/(s*b))
  have sp : 0<s := Real.sqrt_pos.mpr hb
  have sq : (s:ℂ)^2=b := by exact_mod_cast Real.sq_sqrt hb.le
  have he := inverse_spec (b := 1) (by norm_num) (v/(s*b))
  change phase 1 y = _ at he
  unfold phase at he; push_cast at he
  have den (u : ℝ) (hu : 0≤u) :
      0 < ((unitRoot u)^2+k).re ∧ 0 < (3*(unitRoot u)^2+k).re := by
    have hw := inverse_wedge (b := 1) (by norm_num) hu
    have hp := linear_pos (b := 1) (by norm_num)
    have d := phase_regular (b := 1) (by norm_num) hw
    simp only [ofReal_one,mul_one] at hp d
    exact ⟨by rw [pow_two,add_re]; exact add_pos_of_nonneg_of_pos (wedge_prod hw hw) hp, d⟩
  have dpos (u : ℝ) : 0 < ((unitRoot u)^2+k).re ∧ 0 < (3*(unitRoot u)^2+k).re := by
    by_cases h : 0≤u
    · exact den u h
    · simpa [unitRoot,odd_inverse] using den (-u) (neg_nonneg.mpr (le_of_not_ge h))
  obtain ⟨h₁,h₂⟩ := dpos (v/(s*b))
  have n₁ : y^2+k ≠ 0 := fun h ↦ by change 0 < (y^2+k).re at h₁; simp [h] at h₁
  have n₂ : 3*y^2+k ≠ 0 := fun h ↦ by change 0 < (3*y^2+k).re at h₂; simp [h] at h₂
  have bn := ofReal_ne_zero.mpr hb.ne'
  have sn := ofReal_ne_zero.mpr sp.ne'
  have vEq : (v:ℂ) = (s:ℂ)*(b:ℂ)*y*(y^2+k) := by
    field_simp [sn,bn] at he; linear_combination -he
  rw [realProjection_apply,kernel,root_scale hb]
  congr 3
  change I*k/(3*((s:ℂ)*y)^2+k*b)-I/b = (v:ℂ)^2/(b:ℂ)^4*rationalFactor y
  rw [mul_pow,sq,show 3*((b:ℂ)*y^2)+k*b = b*(3*y^2+k) by ring,vEq]
  unfold rationalFactor
  field_simp [n₁,n₂,bn]; ring_nf; rw [sq]; ring

/-- The locally uniform complex tail proves analyticity of the full kernel,
including a two-sided neighborhood of the origin. -/
theorem fullKernel_analytic : AnalyticOnNhd ℝ fullKernel (Ici 0) := by
  classical
  intro x hx
  obtain ⟨A,hA,hagree⟩ := unit_germ
  let M := ‖A 0‖+1
  have mpos : 0<M := by dsimp [M]; positivity
  have hsmall := hA.eventually_analyticAt.and (hA.continuousAt.norm.eventually
    (gt_mem_nhds (show ‖A 0‖ < M by simp [M])))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hsmall
  obtain ⟨d,hd,hdisk⟩ := Metric.mem_nhds_iff.mp hagree
  let δ := min r d
  have hδ : 0<δ := lt_min hr hd
  let R := |x|+1
  have hrx : |x|<R := by simp [R]
  have hR := (abs_nonneg x).trans_lt hrx
  obtain ⟨N,hN⟩ := exists_nat_gt (R/δ)
  let S : Set ℕ+ := {n | (n:ℕ) ≤ N}
  have finiteS : S.Finite := (Set.finite_le_nat N).preimage PNat.coe_injective.injOn
  let : Fintype S := finiteS.fintype
  let b (n : ℕ+) : ℝ := 2*Real.pi*n
  have bn (n : ℕ+) : (n:ℝ) ≤ b n := by
    have h : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
    simpa [b] using mul_le_mul_of_nonneg_right h (by positivity : 0≤(n:ℝ))
  have npos (n : ℕ+) : 0 < (n:ℝ) := by exact_mod_cast n.property
  let scale (n : ℕ+) := Real.sqrt (b n)*b n
  have sc (n : ℕ+) : (n:ℝ) ≤ scale n := by
    have hb1 : 1 ≤ b n := (show 1≤(n:ℝ) by exact_mod_cast n.property).trans (bn n)
    exact (bn n).trans (le_mul_of_one_le_left (zero_le_one.trans hb1) (Real.one_le_sqrt.mpr hb1))
  have scpos (n : ℕ+) : 0 < scale n := (npos n).trans_le (sc n)
  have small (n : ↑Sᶜ) {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
      ‖z/(scale n:ℂ)‖ < δ := by
    have hnat : N < (n.val:ℕ) := lt_of_not_ge n.property
    have hn : R/δ < scale n := hN.trans_le ((show (N:ℝ) ≤ (n.val:ℝ) by exact_mod_cast hnat.le).trans (sc n))
    rw [norm_div,norm_real,Real.norm_eq_abs,abs_of_pos (scpos _),div_lt_iff₀ (scpos _)]
    rw [Metric.mem_ball,dist_zero_right] at hz
    exact hz.trans (by simpa [mul_comm] using (div_lt_iff₀ hδ).mp hn)
  let f (n : ↑Sᶜ) (z : ℂ) := z^2/(b n:ℂ)^4*A (z/(scale n:ℂ))
  have terms (n : ↑Sᶜ) : DifferentiableOn ℂ (f n) (Metric.ball 0 R) := by
    intro z hz
    have hr' := (small n hz).trans_le (min_le_left r d)
    have h := (hball (show z/(scale n:ℂ) ∈ Metric.ball 0 r by simpa using hr')).1
    exact ((differentiableAt_id.pow 2).div_const _ |>.mul (h.differentiableAt.comp z
      (differentiableAt_id.div_const _))).differentiableWithinAt
  have bound (n : ↑Sᶜ) (z : ℂ) (hz : z ∈ Metric.ball 0 R) :
      ‖f n z‖ ≤ modeBudget n*(R^2*M) := by
    have hr' := (small n hz).trans_le (min_le_left r d)
    have hh := (hball (show z/(scale n:ℂ) ∈ Metric.ball 0 r by simpa using hr')).2
    have hb : 0 < b n := mode_pos n
    have nr : ‖z‖ ≤ R := by simpa using le_of_lt (Metric.mem_ball.mp hz)
    have hb4 : (n.val:ℝ)^4 ≤ (b n)^4 := pow_le_pow_left₀ (npos _).le (bn _) _
    simp only [f,norm_mul,norm_div,norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos hb]
    apply (mul_le_mul (div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) nr 2)
      (pow_pos (npos _) 4) hb4) hh.le (norm_nonneg _) (by positivity)).trans_eq
    unfold modeBudget; ring
  have budgets := (budget_summable.subtype (· ∈ Sᶜ)).mul_right (R^2*M)
  have holo := Complex.differentiableOn_tsum_of_summable_norm budgets terms Metric.isOpen_ball bound
  have xball : (x:ℂ) ∈ Metric.ball 0 R := by simpa [Real.norm_eq_abs] using hrx
  have tail := (holo.analyticOnNhd Metric.isOpen_ball _ xball).restrictScalars.comp (Complex.ofRealCLM.analyticAt x)
  have finitePart : AnalyticAt ℝ (fun u ↦ ∑ n : S, kernel (mode_pos n) u) x :=
    Finset.analyticAt_fun_sum _ (fun n _ ↦ kernel_analytic _ _ hx)
  apply (finitePart.add ((realProjection.analyticAt _).comp tail)).congr
  have neigh : ∀ᶠ u : ℝ in 𝓝 x, (u:ℂ) ∈ Metric.ball 0 R :=
    Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds xball)
  filter_upwards [neigh] with u hu
  have normsum := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ bound n u hu) budgets
  have eqmode (n : ↑Sᶜ) : realProjection (f n u) = kernel (mode_pos n) u := by
    rw [kernel_factor]
    have sm := (small n hu).trans_le (min_le_right r d)
    have dist : (u/scale n) ∈ Metric.ball (0:ℝ) d := by
      simpa [← Complex.ofReal_div,Real.norm_eq_abs] using sm
    simpa only [f,scale,b,Complex.ofReal_div] using
      congrArg (fun z ↦ realProjection ((u:ℂ)^2/(b n:ℂ)^4*z)) (hdisk dist)
  change (∑ n : S, kernel (mode_pos n) u) + realProjection (∑' n : ↑Sᶜ, f n u) = fullKernel u
  rw [realProjection.map_tsum normsum.of_norm,tsum_congr eqmode]
  have sumtail := (realProjection.summable normsum.of_norm).congr eqmode
  have front : Summable (fun n : S ↦ kernel (mode_pos n) u) := (hasSum_fintype _).summable
  simpa only [tsum_fintype,fullKernel] using (Summable.tsum_add_tsum_compl (s := S)
    (f := fun n ↦ kernel (mode_pos n) u) front sumtail)


end
end CubicTheta.Physical.BackgroundInverse
