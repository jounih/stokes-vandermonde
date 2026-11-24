module

public import PakPrimes.MainTheorem
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

public section

/-!
# From the quantitative prime number theorem for ψ to the prime-counting ADE obstruction

The Chebyshev estimate in `PrimeNumberTheoremAnd.MediumPNT` bounds the error for ψ.
Prime-power contributions are O(√x), and Abel summation with a split at √x transfers
the logarithmic savings to the error for π. The independent project
`Erdos768.pnt_li_error` proves a stronger form of this transfer on an older toolchain.
-/

open Filter Asymptotics Real Set MeasureTheory
open scoped Topology

namespace PakPrimes.Main

private lemma log_pos_interval {x t : ℝ} (hx : 2 ≤ x) (ht : t ∈ uIcc 2 x) :
    0 < Real.log t := by
  rw [uIcc_of_le hx] at ht
  exact Real.log_pos (by linarith [ht.1])

private lemma li_eq_sub_add_log_integral {x : ℝ} (hx : 2 ≤ x) :
    li x = x / Real.log x - 2 / Real.log 2
      + ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (uIcc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    exact ((Real.continuousAt_log ht0).inv₀ (log_pos_interval hx ht).ne').continuousWithinAt
  have hcont2 : ContinuousOn (fun t : ℝ => (Real.log t ^ 2)⁻¹) (uIcc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    exact (((Real.continuousAt_log ht0).pow 2).inv₀
      (pow_ne_zero _ (log_pos_interval hx ht).ne')).continuousWithinAt
  have hderiv (t : ℝ) (ht : t ∈ uIcc 2 x) :
      HasDerivAt (fun u ↦ u / Real.log u) ((Real.log t)⁻¹ - (Real.log t ^ 2)⁻¹) t := by
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    have h := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) (log_pos_interval hx ht).ne'
    change HasDerivAt (fun u : ℝ ↦ u / Real.log u)
      ((1 * Real.log t - t * t⁻¹) / Real.log t ^ 2) t at h
    convert h using 1
    field_simp [ht0, (log_pos_interval hx ht).ne']
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable.sub hcont2.intervalIntegrable)
  rw [intervalIntegral.integral_sub hcont.intervalIntegrable hcont2.intervalIntegrable] at h
  unfold li
  linarith

/-- Abel summation expresses the prime-counting error in terms of the Chebyshev error. -/
theorem primeCounting_sub_li_eq {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - li x =
      (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  have hθ : IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x :=
    (by simpa [uIcc_of_le hx] using Chebyshev.integrableOn_theta_div_id_mul_log_sq x :
      IntegrableOn _ (uIcc 2 x) volume).intervalIntegrable
  have hlog : IntervalIntegrable (fun t ↦ (Real.log t ^ 2)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    exact (((Real.continuousAt_log ht0).pow 2).inv₀
      (pow_ne_zero _ (log_pos_interval hx ht).ne')).continuousWithinAt
  have hsub : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
        ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_sub hθ hlog]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    field_simp [ht0, (log_pos_interval hx ht).ne']
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, li_eq_sub_add_log_integral hx, hsub]
  ring

private noncomputable def thetaIntegrand (t : ℝ) := (Chebyshev.theta t - t) / (t * (log t)^2)

private lemma integrable_thetaIntegrand {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable thetaIntegrand volume a b := by
  have h1 := (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set
    (show Icc a b ⊆ Icc 2 b from Icc_subset_Icc_left ha)
  have h2 : ContinuousOn (fun t : ℝ => t / (t * (log t)^2)) (Icc a b) := by
    intro t ht
    have hpos : 0 < t := by linarith [ht.1]
    have hl : 0 < log t := log_pos (by linarith [ht.1])
    fun_prop (disch := positivity)
  have hh := h1.sub h2.integrableOn_Icc
  unfold thetaIntegrand
  simp_rw [sub_div]
  exact
    (show IntegrableOn (fun t : ℝ => Chebyshev.theta t / (t * (log t)^2) - t / (t * (log t)^2))
      (uIcc a b) from (uIcc_of_le hab).symm ▸ hh).intervalIntegrable

private lemma thetaIntegrand_bound {t : ℝ} (ht : 2 ≤ t) :
    |thetaIntegrand t| ≤ (log 4 + 1) / (log 2)^2 := by
  have htpos : 0 < t := by linarith
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hlog := log_le_log (by norm_num : 0 < (2:ℝ)) ht
  have hθ : |Chebyshev.theta t - t| ≤ (log 4 + 1) * t := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (Chebyshev.theta_nonneg t), abs_of_nonneg htpos.le]
    linarith [Chebyshev.theta_le_log4_mul_x htpos.le]
  rw [thetaIntegrand, abs_div, abs_of_nonneg (mul_nonneg htpos.le (sq_nonneg _))]
  apply (div_le_div_of_nonneg_right hθ (by positivity)).trans
  calc
    _ = (log 4 + 1) / (log t)^2 := by field_simp
    _ ≤ _ := by gcongr

/-- Splitting the integral at √x preserves each logarithmic error estimate. -/
private theorem theta_integral_allOrders (M : ℕ)
    (h : (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x : ℝ => x / (log x)^M)) :
    (fun x : ℝ => ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t)/(t*(log t)^2))
      =O[atTop] (fun x : ℝ => x/(log x)^M) := by
  obtain ⟨C,hC,hbound⟩ := h.exists_pos
  obtain ⟨A,hA⟩ := eventually_atTop.mp (isBigOWith_iff.mp hbound)
  let B : ℝ := (log 4 + 1) / (log 2)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine IsBigO.of_bound (B + C * (2:ℝ)^M) ?_
  have hg := (isLittleO_log_rpow_rpow_atTop (M : ℝ) (by norm_num : (0:ℝ) < 1/2)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [hg, tendsto_sqrt_atTop.eventually_ge_atTop (max (max A 2) (exp 1))] with x hx hxlarge
  have hsA : A ≤ sqrt x := le_trans (le_trans (le_max_left ..) (le_max_left ..)) hxlarge
  have hs2 : 2 ≤ sqrt x := le_trans (le_trans (le_max_right ..) (le_max_left ..)) hxlarge
  have hsExp : exp 1 ≤ sqrt x := le_trans (le_max_right ..) hxlarge
  have hs : 0 < sqrt x := by linarith
  have hx0 := sqrt_pos.mp hs
  have hsx := sq_sqrt hx0.le
  have hsle : sqrt x ≤ x := by nlinarith
  have hl : 0 < log x := log_pos (by linarith)
  have hls : 0 < log (sqrt x) := log_pos (by linarith)
  have hlogexp : 1 ≤ log (sqrt x) := (le_log_iff_exp_le hs).mpr hsExp
  have hsmall : (log x)^M ≤ sqrt x := by
    rw [← sqrt_eq_rpow, rpow_natCast, one_mul, Real.norm_of_nonneg (sqrt_nonneg x),
      Real.norm_of_nonneg (pow_nonneg hl.le M)] at hx
    exact hx
  have hsrate : sqrt x ≤ x / (log x)^M := (le_div_iff₀ (pow_pos hl M)).2 (by nlinarith [mul_le_mul_of_nonneg_left hsmall hs.le])
  have head : ‖∫ t in (2 : ℝ)..sqrt x, thetaIntegrand t‖ ≤ B * (x/(log x)^M) := by
    calc
      _ ≤ ∫ t in (2:ℝ)..sqrt x, ‖thetaIntegrand t‖ := intervalIntegral.norm_integral_le_integral_norm hs2
      _ ≤ ∫ _ in (2:ℝ)..sqrt x, B := intervalIntegral.integral_mono_on hs2
        (integrable_thetaIntegrand le_rfl hs2).norm intervalIntegrable_const
        (fun t ht => (Real.norm_eq_abs _).trans_le (thetaIntegrand_bound ht.1))
      _ = (sqrt x - 2) * B := by simp
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsrate hB]
  have tailBound (t : ℝ) (ht : t ∈ Icc (sqrt x) x) :
      ‖thetaIntegrand t‖ ≤ C / (log (sqrt x))^M := by
    have ht0 := hs.trans_le ht.1
    have htlog : 0 < log t := hls.trans_le (log_le_log hs ht.1)
    have hlogs : 1 ≤ log t := hlogexp.trans (log_le_log hs ht.1)
    have hb := hA t (hsA.trans ht.1)
    change ‖Chebyshev.theta t - t‖ ≤ C * ‖t/(log t)^M‖ at hb
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (div_nonneg ht0.le (pow_nonneg htlog.le M))] at hb
    rw [Real.norm_eq_abs, thetaIntegrand, abs_div, abs_of_nonneg (by positivity : 0 ≤ t*(log t)^2)]
    refine (div_le_div_of_nonneg_right hb (by positivity)).trans ?_
    calc
      _ = C / (log t)^M / (log t)^2 := by field_simp
      _ ≤ C / (log t)^M := div_le_self (by positivity) (one_le_pow₀ hlogs)
      _ ≤ C / (log (sqrt x))^M := by gcongr; exact ht.1
  have tail : ‖∫ t in sqrt x..x, thetaIntegrand t‖ ≤ C * (2:ℝ)^M * (x/(log x)^M) := by
    calc
      _ ≤ ∫ t in sqrt x..x, ‖thetaIntegrand t‖ := intervalIntegral.norm_integral_le_integral_norm hsle
      _ ≤ ∫ _ in sqrt x..x, C / (log (sqrt x))^M := intervalIntegral.integral_mono_on hsle
        (integrable_thetaIntegrand hs2 hsle).norm intervalIntegrable_const tailBound
      _ = (x-sqrt x) * (C / (log (sqrt x))^M) := by simp [mul_div_assoc]
      _ ≤ x * (C / (log (sqrt x))^M) := by gcongr; linarith
      _ = _ := by rw [log_sqrt hx0.le, div_pow, div_div_eq_mul_div]; ring
  change ‖∫ t in (2:ℝ)..x, thetaIntegrand t‖ ≤ _ * ‖x/(log x)^M‖
  rw [←intervalIntegral.integral_add_adjacent_intervals (integrable_thetaIntegrand le_rfl hs2) (integrable_thetaIntegrand hs2 hsle),
      Real.norm_of_nonneg (div_nonneg hx0.le (pow_nonneg hl.le M))]
  exact (norm_add_le ..).trans (by linarith [head,tail])

/-- A stretched exponential in the logarithm saves every fixed power of the logarithm. -/
private theorem medium_rate_isBigO (M : ℕ) {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10))) =O[atTop]
      (fun x : ℝ => x / log x ^ M) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (M : ℝ)) c hc).comp
    ((tendsto_rpow_atTop (show 0 < (1 : ℝ) / 10 by norm_num)).comp tendsto_log_atTop)
  apply IsBigO.of_bound 1
  filter_upwards [ht.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x hs hx
  have hxl := log_pos hx
  change (log x ^ ((1 : ℝ) / 10)) ^ (10 * (M : ℝ)) *
      exp (-c * log x ^ ((1 : ℝ) / 10)) < 1 at hs
  rw [← Real.rpow_mul hxl.le, show ((1 : ℝ) / 10) * (10 * (M : ℝ)) = (M : ℝ) by ring,
    Real.rpow_natCast] at hs
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  simp only [Real.norm_eq_abs, abs_of_pos (mul_pos hx0 (exp_pos _)),
    abs_of_pos (div_pos hx0 (pow_pos hxl M)), one_mul]
  apply (le_div_iff₀ (pow_pos hxl M)).mpr
  calc
    _ = x * (log x ^ M * exp (-c * log x ^ ((1 : ℝ) / 10))) := by ring
    _ ≤ x * 1 := mul_le_mul_of_nonneg_left hs.le hx0.le
    _ = _ := mul_one _

/-- The prime powers removed when passing from ψ to θ contribute only O(√x). -/
private theorem sqrt_isLittleO_logScale (M : ℕ) :
    Real.sqrt =o[atTop] (fun x : ℝ => x / log x ^ M) := by
  apply (isLittleO_mul_iff_isLittleO_div _).mp
  · conv => arg 2; ext; rw [mul_comm]
    apply (isLittleO_mul_iff_isLittleO_div _).mpr
    · simp_rw [div_sqrt, sqrt_eq_rpow, ← Real.rpow_natCast]
      exact isLittleO_log_rpow_rpow_atTop _ (by norm_num)
    filter_upwards [eventually_gt_atTop 0] with x hx using sqrt_ne_zero'.mpr hx
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact pow_ne_zero _ (log_pos hx).ne'

private theorem theta_allOrders_of_mediumPsi (M : ℕ) (h : ∃ c : ℝ, 0 < c ∧
    (Chebyshev.psi - id) =O[atTop] (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)))) :
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x : ℝ => x / log x ^ M) := by
  obtain ⟨c, hc, hψ⟩ := h
  have hθ := Chebyshev.isBigO_psi_sub_theta_sqrt.trans (sqrt_isLittleO_logScale M).isBigO
  have herr := (hψ.trans (medium_rate_isBigO M hc)).sub hθ
  simpa [Pi.sub_def] using herr

/-- The precise analytic conclusion of `MediumPNT` gives the error estimate used by
the formal prime-counting theorem. -/
theorem pntAllOrders_of_mediumPsi (hpsi : ∃ c : ℝ, 0 < c ∧
    (Chebyshev.psi - id) =O[atTop] (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)))) :
    PNTAllOrders := by
  intro M
  have htheta := theta_allOrders_of_mediumPsi M hpsi
  have hintegral := theta_integral_allOrders M htheta
  have hdiv : (fun x : ℝ => (Chebyshev.theta x - x) / log x) =O[atTop]
      (fun x : ℝ => Chebyshev.theta x - x) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    have hx0 : 0 < x := (exp_pos 1).trans_le hx
    have hxlog : 1 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
    simpa [Real.norm_eq_abs, abs_div, abs_of_pos (zero_lt_one.trans_le hxlog)]
      using (div_le_self (abs_nonneg (Chebyshev.theta x - x)) hxlog)
  have hone : (fun _ : ℝ => (1 : ℝ)) =O[atTop] Real.sqrt := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    simp only [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg x)]
    simpa using Real.sqrt_le_sqrt hx
  have hconst := (hone.trans (sqrt_isLittleO_logScale M).isBigO).const_mul_left (2 / log 2)
  have herr := ((hdiv.trans htheta).add hconst).add hintegral
  obtain ⟨C, hC, hbound⟩ := herr.exists_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [isBigOWith_iff.mp hbound, eventually_ge_atTop (2 : ℝ)] with x hb hx
  rw [primeCounting_sub_li_eq hx]
  have hx0 : 0 ≤ x := by linarith
  have hxlog : 0 < log x := log_pos (by linarith)
  simpa [Pi.add_apply, Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg hx0, abs_of_pos hxlog, abs_of_nonneg (div_nonneg hx0 (pow_nonneg hxlog.le M)), mul_div_assoc] using hb

end PakPrimes.Main
