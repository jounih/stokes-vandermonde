module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.AutonomousTransfer
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.ZetaValues

/-! # Hölder's Theorem (1887): Differential Transcendence of `Γ` over `ℂ(z)`

This module proves **Hölder's Theorem (1887)** unconditionally via `PakPrimes.HigherOrderStokes`:
neither `Complex.Gamma` (restricted to `ℝ`) nor `Real.Gamma` satisfies any nonzero algebraic
differential equation over `ℂ[u]` or `ℂ(u)`.

## Mathematical Route
1. **Bernoulli Borel Witness (`phiBern`, `phiBern_borelData`)**:
   Define `φ_Bern(ξ) := (dslope Complex.exp 0 ξ)⁻¹ - 1 + ξ / 2` (so `φ_Bern(0) = 0` and
   `φ_Bern(ξ) = ξ / (e^ξ - 1) - 1 + ξ / 2` for `ξ ≠ 0`). Its formal Laplace series
   `formalSeries phiBern` has coefficients `B_{2k}` at `u^{-(2k+1)}` (`k ≥ 1`), and along the
   positive imaginary ray `θ₀ = π/2` it satisfies `HigherOrderBorelData` with simple poles at
   `2π i (m + 1)` (`m : ℕ`) of residue `2π i (m + 1) ≠ 0` and flanking rays `θ₀ ± π/4`.
2. **Exact Trigamma Series & Euler–Maclaurin All-Orders Asymptotics**:
   From `Complex.digamma_apply_add_one` and `Complex.digamma_two_mul`, the duplication trick
   proves `trigamma (u : ℂ) = ∑' n : ℕ, 1 / ((u : ℂ) + n) ^ 2` for `u > 0`. Elementary
   1-D Euler–Maclaurin integration by parts with `bernoulliFun` establishes that
   `trigamma (u : ℂ) - u⁻¹ - 2⁻¹ * u⁻²` matches `formalSeries phiBern` and all its `u`-derivatives
   to all orders `1 / u^M`.
3. **Differential Transcendence of Trigamma (`trigamma_no_rat_ade`)**:
   `PakPrimes.HigherOrderStokes.no_rat_ade_of_higher_order_borel` rules out any nonzero `ℂ(u)`-ODE
   for `trigamma (u : ℂ) - u⁻¹ - 2⁻¹ * u⁻²`, and affine translation in `RatFunc ℂ` transfers this
   to `trigamma (u : ℂ)`.
4. **Algebraic Reduction `Γ → ψ → ψ'` (`holder_gamma_no_ade`, `holder_gamma_no_rat_ade`, `holder_realGamma_no_ade`)**:
   Any nonzero `ℂ[u]`-ODE for `Complex.Gamma` restricts via `ordinary_relation` and
   `autonomous_readout` to a nonzero autonomous ODE for `trigamma` on a neighborhood of an ordinary
   point, which extends to `(0, ∞)` by real analyticity, contradicting `trigamma_no_rat_ade`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.HolderGamma

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.HigherOrderStokes
open PakPrimes.PrimeNome
open scoped Topology Interval

noncomputable section

/-! ### 1. Bernoulli Borel Transform `phiBern` and its `HigherOrderBorelData` Witness -/

/-- The Bernoulli Borel kernel `φ_Bern(ξ) = ξ / (e^ξ - 1) - 1 + ξ / 2` (with removable
singularity `φ_Bern(0) = 0`), defined via `dslope Complex.exp 0`. -/
@[expose] def phiBern (ξ : ℂ) : ℂ :=
  (dslope Complex.exp 0 ξ)⁻¹ - 1 + ξ / 2

lemma phiBern_zero : phiBern 0 = 0 := by
  simp [phiBern, dslope_same, Complex.deriv_exp]

lemma phiBern_eq_of_ne_zero {ξ : ℂ} (hξ : ξ ≠ 0) :
    phiBern ξ = ξ / (Complex.exp ξ - 1) - 1 + ξ / 2 := by
  rw [phiBern, dslope_of_ne _ hξ, slope_def_field, Complex.exp_zero, sub_zero, inv_div]

private lemma dslope_exp_zero_analyticOn :
    AnalyticOnNhd ℂ (dslope Complex.exp 0) Set.univ := by
  intro z _
  by_cases hz : z = 0
  · subst hz
    have hps := (analyticAt_cexp (z := (0 : ℂ))).hasFPowerSeriesAt.dslope_fslope
    exact hps.analyticAt
  · have heq : dslope Complex.exp 0 =ᶠ[𝓝 z] fun w : ℂ => (Complex.exp w - 1) / w := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      rw [dslope_of_ne _ hw, slope_def_field, Complex.exp_zero, sub_zero]
    exact (((analyticAt_cexp.sub analyticAt_const).div analyticAt_id hz)).congr
      heq.symm

private lemma dslope_exp_zero_ne_zero {ξ : ℂ}
    (h : ξ = 0 ∨ ∀ k : ℤ, k ≠ 0 → ξ ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ)) :
    dslope Complex.exp 0 ξ ≠ 0 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [dslope_same, Complex.deriv_exp]
  · rw [dslope_of_ne _ hξ, slope_def_field, sub_zero, Complex.exp_zero]
    refine div_ne_zero (sub_ne_zero.mpr fun hexp => ?_) hξ
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
    rcases eq_or_ne k 0 with rfl | hk0
    · simp at hk
      exact hξ hk
    · rcases h with rfl | hfor
      · exact hξ rfl
      · exact hfor k hk0 (by rw [hk]; ring)

lemma phiBern_analyticAt {ξ : ℂ}
    (h : ξ = 0 ∨ ∀ k : ℤ, k ≠ 0 → ξ ≠ 2 * (Real.pi : ℂ) * I * (k : ℂ)) :
    AnalyticAt ℂ phiBern ξ := by
  have hd : AnalyticAt ℂ (dslope Complex.exp 0) ξ := dslope_exp_zero_analyticOn ξ (Set.mem_univ _)
  have hne : dslope Complex.exp 0 ξ ≠ 0 := dslope_exp_zero_ne_zero h
  exact ((hd.inv hne).sub analyticAt_const).add (analyticAt_id.mul analyticAt_const)

private lemma iteratedDeriv_bernCore_zero (n : ℕ) :
    iteratedDeriv n (fun ξ : ℂ => (dslope Complex.exp 0 ξ)⁻¹) 0 = (bernoulli n : ℂ) := by
  let B : ℂ → ℂ := fun ξ => (dslope Complex.exp 0 ξ)⁻¹
  have hB_ana : AnalyticAt ℂ B 0 :=
    (dslope_exp_zero_analyticOn 0 (Set.mem_univ _)).inv
      (dslope_exp_zero_ne_zero (Or.inl rfl))
  have hB_mul : (fun ξ : ℂ => B ξ * (Complex.exp ξ - 1)) =ᶠ[𝓝 (0 : ℂ)] id := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1)] with ξ hξ
    rcases eq_or_ne ξ 0 with rfl | hξ0
    · simp [B]
    · have hexp_ne : Complex.exp ξ - 1 ≠ 0 := by
        intro h0
        obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h0)
        rcases eq_or_ne k 0 with rfl | hk0
        · simp at hk; exact hξ0 hk
        · have hnorm : ‖ξ‖ = |(k : ℝ)| * (2 * Real.pi) := by
            rw [hk, norm_mul, norm_intCast, Complex.norm_mul, Complex.norm_mul,
              Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
              Complex.norm_I, mul_one]
          have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
          have hlt1 : ‖ξ‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hξ
          nlinarith [Real.pi_gt_three]
      have hBξ : B ξ = ξ / (Complex.exp ξ - 1) := by
        dsimp only [B]
        rw [dslope_of_ne _ hξ0, slope_def_field, Complex.exp_zero, sub_zero, inv_div]
      rw [hBξ]
      exact div_mul_cancel₀ ξ hexp_ne
  have hsum_rec : ∀ m : ℕ,
      ∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℂ) * iteratedDeriv k B 0 =
        if m + 1 = 1 then (1 : ℂ) else 0 := by
    intro m
    have hL : iteratedDeriv (m + 1) (fun ξ : ℂ => B ξ * (Complex.exp ξ - 1)) 0 =
        iteratedDeriv (m + 1) id 0 := Filter.EventuallyEq.iteratedDeriv_eq (m + 1) hB_mul
    have hid : iteratedDeriv (m + 1) id (0 : ℂ) = if m + 1 = 1 then 1 else 0 := by
      cases m with
      | zero => simp
      | succ m =>
        have hder : deriv (id : ℂ → ℂ) = fun _ => 1 := by ext; simp
        rw [iteratedDeriv_succ', hder, iteratedDeriv_const]
        simp
    have hmul : iteratedDeriv (m + 1) (fun ξ : ℂ => B ξ * (Complex.exp ξ - 1)) 0 =
        ∑ k ∈ Finset.range (m + 2),
          ((m + 1).choose k : ℂ) * iteratedDeriv k B 0 *
            iteratedDeriv (m + 1 - k) (fun ξ : ℂ => Complex.exp ξ - 1) 0 := by
      have hcdB : ContDiffAt ℂ (m + 1) B 0 := hB_ana.contDiffAt.of_le le_top
      have hcdE : ContDiffAt ℂ (m + 1) (fun ξ : ℂ => Complex.exp ξ - 1) 0 :=
        (analyticAt_cexp.sub analyticAt_const).contDiffAt.of_le le_top
      have hfn : (fun ξ : ℂ => B ξ * (Complex.exp ξ - 1)) = B * (fun ξ => Complex.exp ξ - 1) := rfl
      rw [hfn]
      simpa [nsmul_eq_mul, mul_assoc] using iteratedDeriv_mul hcdB hcdE
    have hExpDeriv : ∀ j : ℕ,
        iteratedDeriv j (fun ξ : ℂ => Complex.exp ξ - 1) 0 = if j = 0 then 0 else 1 := by
      intro j
      cases j with
      | zero => simp
      | succ j =>
        have hdexp : deriv (fun ξ : ℂ => Complex.exp ξ - 1) = Complex.exp := by ext ξ; simp
        have hiter : ∀ k : ℕ, iteratedDeriv k Complex.exp 0 = 1 := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk =>
            rw [iteratedDeriv_succ', show deriv Complex.exp = Complex.exp by ext; simp, ihk]
        rw [iteratedDeriv_succ', hdexp, hiter j]
        simp
    rw [hmul, Finset.sum_range_succ, Nat.sub_self, hExpDeriv 0] at hL
    simp only [↓reduceIte, mul_zero, add_zero] at hL
    have hterms : ∑ k ∈ Finset.range (m + 1),
        ((m + 1).choose k : ℂ) * iteratedDeriv k B 0 *
          iteratedDeriv (m + 1 - k) (fun ξ : ℂ => Complex.exp ξ - 1) 0 =
        ∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℂ) * iteratedDeriv k B 0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k < m + 1 := Finset.mem_range.mp hk
      have hne0 : m + 1 - k ≠ 0 := by omega
      rw [hExpDeriv (m + 1 - k), ite_eq_right_iff.mpr (fun h => absurd h hne0), mul_one]
    rw [hterms, hid] at hL
    exact hL
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have h1 := hsum_rec n
    have h2 : ∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℂ) * (bernoulli k : ℂ) =
        if n + 1 = 1 then 1 else 0 := by
      have hq := _root_.sum_bernoulli (n + 1)
      have hc := congrArg (algebraMap ℚ ℂ) hq
      simp only [map_sum, map_mul, map_natCast] at hc
      split_ifs at hc ⊢ <;> simpa using hc
    rw [Finset.sum_range_succ] at h1 h2
    have hsum_eq : ∑ k ∈ Finset.range n, ((n + 1).choose k : ℂ) * iteratedDeriv k B 0 =
        ∑ k ∈ Finset.range n, ((n + 1).choose k : ℂ) * (bernoulli k : ℂ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ih k (Finset.mem_range.mp hk)]
    rw [hsum_eq] at h1
    have hcomb := h1.trans h2.symm
    have hadd := add_left_cancel hcomb
    have hch : ((n + 1).choose n : ℂ) = (n + 1 : ℂ) := by
      rw [Nat.choose_succ_self_right n]
      push_cast; rfl
    rw [hch] at hadd
    have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact mul_left_cancel₀ hn1 hadd

lemma iteratedDeriv_phiBern_zero (n : ℕ) :
    iteratedDeriv n phiBern 0 = if n ≤ 1 then 0 else (bernoulli n : ℂ) := by
  have hB : AnalyticAt ℂ (fun ξ : ℂ => (dslope Complex.exp 0 ξ)⁻¹) 0 :=
    (dslope_exp_zero_analyticOn 0 (Set.mem_univ _)).inv
      (dslope_exp_zero_ne_zero (Or.inl rfl))
  have hL : AnalyticAt ℂ (fun ξ : ℂ => -1 + ξ / 2) 0 :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hsplit : phiBern = (fun ξ : ℂ => (dslope Complex.exp 0 ξ)⁻¹) + (fun ξ : ℂ => -1 + ξ / 2) := by
    ext ξ; simp [phiBern, sub_eq_add_neg, add_assoc]
  rw [hsplit, iteratedDeriv_add (hB.contDiffAt.of_le le_top) (hL.contDiffAt.of_le le_top),
    iteratedDeriv_bernCore_zero n]
  rcases n with _ | _ | n
  · simp [bernoulli_zero]
  · simp only [Nat.zero_add, iteratedDeriv_one, bernoulli_one, Rat.cast_div, Rat.cast_neg,
      Rat.cast_one, Nat.le_refl, ↓reduceIte]
    have hder : deriv (fun ξ : ℂ => (-1 : ℂ) + ξ / 2) 0 = 2⁻¹ := by simp
    rw [hder]
    norm_num
  · have hdL : deriv (fun ξ : ℂ => (-1 : ℂ) + ξ / 2) = fun _ => (2⁻¹ : ℂ) := by
      ext ξ; simp
    have hlin : iteratedDeriv (n + 2) (fun ξ : ℂ => (-1 : ℂ) + ξ / 2) 0 = 0 := by
      rw [iteratedDeriv_succ', hdL, iteratedDeriv_succ', deriv_const', iteratedDeriv_const]
      simp
    rw [hlin, add_zero, ite_eq_right_iff.mpr (by omega)]

lemma coeff_formalSeries_phiBern (n : ℕ) :
    PowerSeries.coeff n (formalSeries phiBern) =
      if n ≤ 2 then 0 else (bernoulli (n - 1) : ℂ) := by
  cases n with
  | zero => simp [formalSeries]
  | succ m =>
    rw [formalSeries, PowerSeries.coeff_mk]
    dsimp only
    rw [iteratedDeriv_phiBern_zero m]
    rcases m with _ | _ | m
    · simp
    · simp
    · simp

private lemma phiBern_expType_ray (σ : ℝ) (hcos : Real.cos σ ≠ 0) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) phiBern) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I σ
  have hμ_re : μ.re = Real.cos σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re σ
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ phiBern v) (Icc 0 1) := by
    intro v _
    have hana : AnalyticAt ℂ phiBern (μ * (v : ℂ)) := by
      refine phiBern_analyticAt (Or.inr fun k hk0 heq => ?_)
      have hmul : (μ * (v : ℂ)).re = Real.cos σ * v := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have hpole : (2 * (Real.pi : ℂ) * I * (k : ℂ)).re = 0 := by simp
      rw [heq, hpole] at hmul
      have hv0 : v = 0 := (mul_eq_zero.mp hmul.symm).resolve_left hcos
      subst hv0
      simp only [Complex.ofReal_zero, mul_zero] at heq
      have hk_ne : (2 * (Real.pi : ℂ) * I * (k : ℂ)) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
        · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        · exact Int.cast_ne_zero.mpr hk0
      exact hk_ne heq.symm
    change ContinuousWithinAt (fun x : ℝ => μ * phiBern (μ * (x : ℂ))) (Icc 0 1) v
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiBern (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiBern) (f := fun x : ℝ => μ * (x : ℂ)) hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let δ : ℝ := 1 - Real.exp (-|Real.cos σ|)
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    linarith [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (abs_pos.mpr hcos))]
  let C : ℝ := max (max M₀ 0) (1 / δ + 3 / 2)
  have hC : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 1, hC, zero_le_one, fun v hv => ?_⟩
  rw [one_mul]
  by_cases hv1 : v ≤ 1
  · calc ‖Minor.pull μ phiBern v‖ ≤ M₀ := hM₀ v ⟨hv, hv1⟩
      _ ≤ max M₀ 0 := le_max_left _ _
      _ ≤ C := le_max_left _ _
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_left (Real.one_le_exp hv) hC
  · push Not at hv1
    have hv_pos : 0 < v := by linarith
    have hz_ne : μ * (v : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr hv_pos.ne')
    have hz_norm : ‖μ * (v : ℂ)‖ = v := by
      rw [norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
    have hexp_ge : δ ≤ ‖Complex.exp (μ * (v : ℂ)) - 1‖ := by
      have hre : (μ * (v : ℂ)).re = Real.cos σ * v := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      rcases lt_or_gt_of_ne hcos with hneg | hpos
      · have hle : Real.cos σ * v ≤ -|Real.cos σ| := by
          rw [abs_of_neg hneg]
          nlinarith
        have hnorm_le : ‖Complex.exp (μ * (v : ℂ))‖ ≤ Real.exp (-|Real.cos σ|) := by
          rw [Complex.norm_exp, hre]
          exact Real.exp_le_exp.mpr hle
        have htri : ‖(1 : ℂ)‖ - ‖Complex.exp (μ * (v : ℂ))‖ ≤ ‖(1 : ℂ) - Complex.exp (μ * (v : ℂ))‖ :=
          norm_sub_norm_le _ _
        rw [norm_one, norm_sub_rev] at htri
        linarith
      · have hge : |Real.cos σ| ≤ Real.cos σ * v := by
          rw [abs_of_pos hpos]
          nlinarith
        have hnorm_ge : Real.exp |Real.cos σ| ≤ ‖Complex.exp (μ * (v : ℂ))‖ := by
          rw [Complex.norm_exp, hre]
          exact Real.exp_le_exp.mpr hge
        have hsub1 : Real.exp |Real.cos σ| - 1 ≥ 1 - Real.exp (-|Real.cos σ|) := by
          have hexp_pos : 0 < Real.exp |Real.cos σ| := Real.exp_pos _
          have h1 : Real.exp (-|Real.cos σ|) = (Real.exp |Real.cos σ|)⁻¹ := Real.exp_neg _
          rw [h1]
          have hsq : (Real.exp |Real.cos σ| - 1) - (1 - (Real.exp |Real.cos σ|)⁻¹) =
              (Real.exp |Real.cos σ| - 1) ^ 2 / Real.exp |Real.cos σ| := by
            field_simp [hexp_pos.ne']
          have hnonneg : 0 ≤ (Real.exp |Real.cos σ| - 1) ^ 2 / Real.exp |Real.cos σ| :=
            div_nonneg (sq_nonneg _) hexp_pos.le
          linarith
        have hrev : ‖Complex.exp (μ * (v : ℂ))‖ - 1 ≤ ‖Complex.exp (μ * (v : ℂ)) - 1‖ := by
          simpa only [norm_one] using norm_sub_norm_le (Complex.exp (μ * (v : ℂ))) (1 : ℂ)
        linarith
    have hpull : Minor.pull μ phiBern v = μ * ((μ * (v : ℂ)) / (Complex.exp (μ * (v : ℂ)) - 1) - 1 + (μ * (v : ℂ)) / 2) := by
      rw [Minor.pull, phiBern_eq_of_ne_zero hz_ne]
    rw [hpull, norm_mul, hμ_norm, one_mul]
    have h1 : ‖(μ * (v : ℂ)) / (Complex.exp (μ * (v : ℂ)) - 1)‖ ≤ v / δ := by
      rw [norm_div, hz_norm]
      exact div_le_div_of_nonneg_left hv_pos.le hδ_pos hexp_ge
    have h2 : ‖(μ * (v : ℂ)) / 2‖ = v / 2 := by
      rw [norm_div, hz_norm, Complex.norm_ofNat]
    have htri : ‖(μ * (v : ℂ)) / (Complex.exp (μ * (v : ℂ)) - 1) - 1 + (μ * (v : ℂ)) / 2‖ ≤
        v / δ + 1 + v / 2 := by
      calc ‖(μ * (v : ℂ)) / (Complex.exp (μ * (v : ℂ)) - 1) - 1 + (μ * (v : ℂ)) / 2‖
          ≤ ‖(μ * (v : ℂ)) / (Complex.exp (μ * (v : ℂ)) - 1) - 1‖ + ‖(μ * (v : ℂ)) / 2‖ :=
            norm_add_le _ _
        _ ≤ (‖(μ * (v : ℂ)) / (Complex.exp (μ * (v : ℂ)) - 1)‖ + ‖(1 : ℂ)‖) + v / 2 := by
            gcongr
            · exact norm_sub_le _ _
            · exact h2.le
        _ ≤ v / δ + 1 + v / 2 := by rw [norm_one]; linarith
    have hv_exp : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
    have h1_exp : (1 : ℝ) ≤ Real.exp v := Real.one_le_exp hv
    have hcoeff_nonneg : 0 ≤ 1 / δ + 1 / 2 := by positivity
    have hmul_bd : (1 / δ + 1 / 2) * v ≤ (1 / δ + 1 / 2) * Real.exp v :=
      mul_le_mul_of_nonneg_left hv_exp hcoeff_nonneg
    calc ‖(μ * (v : ℂ)) / (Complex.exp (μ * (v : ℂ)) - 1) - 1 + (μ * (v : ℂ)) / 2‖
        ≤ v / δ + 1 + v / 2 := htri
      _ = (1 / δ + 1 / 2) * v + 1 := by ring
      _ ≤ (1 / δ + 3 / 2) * Real.exp v := by linarith
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos v).le

/-- Genuine `HigherOrderBorelData` witness on `phiBern` along the positive imaginary axis
`θ₀ = π/2` with simple poles at `2π i (m + 1)` (`m : ℕ`) of residue `2π i (m + 1) ≠ 0`. -/
def phiBern_borelData :
    HigherOrderBorelData phiBern (Real.pi / 2)
      (fun m : ℕ => 2 * Real.pi * (m + 1 : ℝ)) (fun _ : ℕ => 1)
      (fun m s => if s = 1 then 2 * (Real.pi : ℂ) * I * ((m + 1 : ℕ) : ℂ) else 0) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := Real.pi
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := Real.pi_pos
  ω_pos := by positivity
  ω_mono := fun a b hab => by
    dsimp only
    have : (a + 1 : ℝ) < (b + 1 : ℝ) := by exact_mod_cast Nat.succ_lt_succ hab
    nlinarith [Real.pi_pos]
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by
    simp only [↓reduceIte]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  analyticOn := fun z hz => by
    refine phiBern_analyticAt (Or.inr fun k hk0 heq => ?_)
    have hexp_negI : Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ)) = -I := by
      rw [show -I * ((Real.pi / 2 : ℝ) : ℂ) = ((-(Real.pi / 2) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I]
      simp
    let w : ℂ := Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ)) * z
    have hw_eq : w = ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) := by
      dsimp only [w]
      rw [hexp_negI, heq]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rcases lt_trichotomy k 0 with hk_neg | rfl | hk_pos
    · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
      have hw_re : w.re ≤ -(2 * Real.pi) := by
        rw [hw_eq, Complex.ofReal_re]
        nlinarith [Real.pi_pos]
      have hw_norm : 2 * Real.pi ≤ ‖w‖ := by
        rw [hw_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by nlinarith [Real.pi_pos])]
        nlinarith [Real.pi_pos]
      rcases hz.1 with hball | hcone
      · rw [Metric.mem_ball, dist_zero_right] at hball
        linarith [Real.pi_pos]
      · linarith [hcone.1, Real.pi_pos]
    · exact hk0 rfl
    · apply hz.2
      refine ⟨(k - 1).toNat, ?_⟩
      change (((2 * Real.pi * (((k - 1).toNat : ℝ) + 1) : ℝ)) : ℂ) = w
      rw [hw_eq]
      congr 1
      have hk_nat : ((k - 1).toNat : ℤ) + 1 = k := by omega
      have hcast : (((k - 1).toNat : ℝ) + 1) = (k : ℝ) := by exact_mod_cast hk_nat
      rw [hcast]
  pole_principalPart := fun m => by
    have hexp_posI : Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ)) = I := by
      rw [show I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I by ring,
        Complex.exp_mul_I]
      simp
    let z_m : ℂ := Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ)) * ((2 * Real.pi * (m + 1 : ℝ) : ℝ) : ℂ)
    have hz_m_eq : z_m = 2 * (Real.pi : ℂ) * I * ((m + 1 : ℕ) : ℂ) := by
      dsimp only [z_m]
      rw [hexp_posI]
      push_cast; ring
    have hexp_zm : Complex.exp z_m = 1 := by
      rw [hz_m_eq, Complex.exp_eq_one_iff]
      refine ⟨m + 1, ?_⟩
      push_cast; ring
    let h : ℂ → ℂ := dslope (fun w => Complex.exp w - 1) z_m
    have h_ana : AnalyticAt ℂ h z_m :=
      (analyticAt_cexp.sub analyticAt_const).hasFPowerSeriesAt.dslope_fslope.analyticAt
    have hz_m_ne : z_m ≠ 0 := by
      rw [hz_m_eq]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hh_zm : h z_m = 1 := by
      have hderiv : deriv (fun w : ℂ => Complex.exp w - 1) z_m = 1 := by
        have hd := ((Complex.hasDerivAt_exp z_m).sub_const 1).deriv
        simp [hexp_zm, hd]
      simp [h, dslope_same, hderiv]
    let g : ℂ → ℂ := dslope h z_m
    have hg_ana : AnalyticAt ℂ g z_m := h_ana.hasFPowerSeriesAt.dslope_fslope.analyticAt
    let rhs : ℂ → ℂ := fun z => (1 - z_m * g z) / h z - 1 + z / 2
    have hrhs_cont : ContinuousAt rhs z_m := by
      refine ((ContinuousAt.div (continuousAt_const.sub (continuousAt_const.mul hg_ana.continuousAt))
        h_ana.continuousAt (by rw [hh_zm]; exact one_ne_zero)).sub continuousAt_const).add
        (continuousAt_id.div_const 2)
    have hball : Metric.ball z_m (min 1 (‖z_m‖ / 2)) \ {z_m} ∈ 𝓝[≠] z_m := by
      rw [Set.sdiff_eq, Set.inter_comm]
      exact inter_mem_nhdsWithin _
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (lt_min one_pos (half_pos (norm_pos_iff.mpr hz_m_ne)))))
    have heq_within :
        (fun z : ℂ => phiBern z - ∑ s ∈ Finset.Icc 1 1,
          (if s = 1 then 2 * (Real.pi : ℂ) * I * ((m + 1 : ℕ) : ℂ) else 0) / (z - z_m) ^ s) =ᶠ[𝓝[≠] z_m]
          rhs := by
      have hh_ne : ∀ᶠ z in 𝓝 z_m, h z ≠ 0 := h_ana.continuousAt.eventually_ne (by rw [hh_zm]; exact one_ne_zero)
      filter_upwards [hball, hh_ne.filter_mono nhdsWithin_le_nhds] with z ⟨hz_ball, hz_ne⟩ hhz_ne
      have hz_ne0 : z ≠ 0 := by
        intro hz0
        rw [Metric.mem_ball, dist_eq_norm, hz0, zero_sub, norm_neg] at hz_ball
        have := lt_of_lt_of_le hz_ball (min_le_right 1 (‖z_m‖ / 2))
        linarith [norm_pos_iff.mpr hz_m_ne]
      have hsub_ne : z - z_m ≠ 0 := sub_ne_zero.mpr hz_ne
      have hh_val : h z = (Complex.exp z - 1) / (z - z_m) := by
        rw [show h = dslope (fun w => Complex.exp w - 1) z_m from rfl, dslope_of_ne _ hz_ne,
          slope_def_field, hexp_zm, sub_self, sub_zero]
      have hg_val : g z = (h z - 1) / (z - z_m) := by
        rw [show g = dslope h z_m from rfl, dslope_of_ne _ hz_ne, slope_def_field, hh_zm]
      have hexp_ne : Complex.exp z - 1 ≠ 0 := by
        intro h0
        rw [hh_val, h0, zero_div] at hhz_ne
        exact hhz_ne rfl
      rw [phiBern_eq_of_ne_zero hz_ne0]
      simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one, ← hz_m_eq]
      dsimp only [rhs]
      rw [hg_val, hh_val]
      field_simp [hsub_ne, hexp_ne]
      ring
    refine ⟨rhs z_m, ?_⟩
    exact hrhs_cont.continuousWithinAt.tendsto.congr' heq_within.symm
  expType_plus := by
    have hcos : Real.cos (Real.pi / 2 + Real.pi / 4) ≠ 0 := by
      rw [add_comm (Real.pi / 2) (Real.pi / 4), Real.cos_add_pi_div_two, Real.sin_pi_div_four]
      exact neg_ne_zero.mpr (by positivity)
    exact phiBern_expType_ray (Real.pi / 2 + Real.pi / 4) hcos
  expType_minus := by
    have hcos : Real.cos (Real.pi / 2 - Real.pi / 4) ≠ 0 := by
      rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, Real.cos_pi_div_four]
      positivity
    exact phiBern_expType_ray (Real.pi / 2 - Real.pi / 4) hcos

/-! ### 2. Trigamma Series, Duplication Identity, and Euler–Maclaurin Asymptotics -/

/-- The trigamma function `ψ'(z) = d/dz (Γ'(z)/Γ(z))`. -/
@[expose] def trigamma (z : ℂ) : ℂ := deriv Complex.digamma z

private lemma re_pos_avoids_neg_nat {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private lemma gamma_analyticOnNhd_re_pos :
    AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
  exact (Complex.differentiableAt_Gamma z (re_pos_avoids_neg_nat hz)).differentiableWithinAt

private lemma digamma_analyticOnNhd_re_pos :
    AnalyticOnNhd ℂ Complex.digamma {z : ℂ | 0 < z.re} := by
  intro z hz
  have hgam : AnalyticAt ℂ Complex.Gamma z := gamma_analyticOnNhd_re_pos z hz
  have hderiv : AnalyticAt ℂ (deriv Complex.Gamma) z :=
    gamma_analyticOnNhd_re_pos.deriv z hz
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (re_pos_avoids_neg_nat hz)
  have heq : Complex.digamma = fun w : ℂ => deriv Complex.Gamma w / Complex.Gamma w := by
    ext w; simp [Complex.digamma_def, logDeriv_apply]
  rw [heq]
  exact hderiv.div hgam hne

lemma trigamma_analyticOnNhd_re_pos :
    AnalyticOnNhd ℂ trigamma {z : ℂ | 0 < z.re} :=
  digamma_analyticOnNhd_re_pos.deriv

lemma trigamma_add_one {z : ℂ} (hz : 0 < z.re) :
    trigamma (z + 1) = trigamma z - z⁻¹ ^ 2 := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun w : ℂ => Complex.digamma (w + 1)) =ᶠ[𝓝 z]
      fun w : ℂ => Complex.digamma w + w⁻¹ := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact Complex.digamma_apply_add_one w (re_pos_avoids_neg_nat hw)
  have hz1 : 0 < (z + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hz_ne : z ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have hdL : HasDerivAt (fun w : ℂ => Complex.digamma (w + 1)) (trigamma (z + 1)) z := by
    have h1 := (digamma_analyticOnNhd_re_pos (z + 1) hz1).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => w + 1) 1 z := (hasDerivAt_id z).add_const 1
    simpa only [Function.comp_def, mul_one, trigamma] using h1.comp z h2
  have hdR : HasDerivAt (fun w : ℂ => Complex.digamma w + w⁻¹) (trigamma z - z⁻¹ ^ 2) z := by
    have h1 := (digamma_analyticOnNhd_re_pos z hz).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz_ne
    refine (h1.add h2).congr_deriv ?_
    simp [trigamma, sub_eq_add_neg, inv_pow]
  exact hdL.deriv.symm.trans (hev.deriv_eq.trans hdR.deriv)

lemma trigamma_two_mul {z : ℂ} (hz : 0 < z.re) :
    trigamma (2 * z) = (1 / 4 : ℂ) * (trigamma z + trigamma (z + 1 / 2)) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun w : ℂ => Complex.digamma (2 * w)) =ᶠ[𝓝 z]
      fun w : ℂ => (1 / 2 : ℂ) * (Complex.digamma w + Complex.digamma (w + 1 / 2)) + Complex.log 2 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    have h2w : 0 < (2 * w).re := by simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; linarith
    exact Complex.digamma_two_mul (re_pos_avoids_neg_nat h2w)
  have hz2 : 0 < (2 * z).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; linarith
  have hzh : 0 < (z + 1 / 2).re := by
    simp only [Complex.add_re, one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat]; linarith
  have hdL : HasDerivAt (fun w : ℂ => Complex.digamma (2 * w)) (2 * trigamma (2 * z)) z := by
    have h1 := (digamma_analyticOnNhd_re_pos (2 * z) hz2).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => 2 * w) 2 z :=
      ((hasDerivAt_id z).const_mul (2 : ℂ)).congr_deriv (mul_one _)
    have hcomp := h1.comp z h2
    exact hcomp.congr_deriv (by dsimp only [trigamma]; ring)
  have hdR : HasDerivAt
      (fun w : ℂ => (1 / 2 : ℂ) * (Complex.digamma w + Complex.digamma (w + 1 / 2)) + Complex.log 2)
      ((1 / 2 : ℂ) * (trigamma z + trigamma (z + 1 / 2))) z := by
    have h1 := (digamma_analyticOnNhd_re_pos z hz).differentiableAt.hasDerivAt
    have h2_0 := (digamma_analyticOnNhd_re_pos (z + 1 / 2) hzh).differentiableAt.hasDerivAt
    have h2_in : HasDerivAt (fun w : ℂ => w + 1 / 2) 1 z := (hasDerivAt_id z).add_const (1 / 2 : ℂ)
    have h2 : HasDerivAt (fun w : ℂ => Complex.digamma (w + 1 / 2)) (trigamma (z + 1 / 2)) z :=
      (h2_0.comp z h2_in).congr_deriv (mul_one _)
    exact (((h1.add h2).const_mul (1 / 2 : ℂ)).add_const (Complex.log 2)).congr_deriv
      (by simp [trigamma])
  have heq : 2 * trigamma (2 * z) = (1 / 2 : ℂ) * (trigamma z + trigamma (z + 1 / 2)) :=
    hdL.deriv.symm.trans (hev.deriv_eq.trans hdR.deriv)
  linear_combination (1 / 2 : ℂ) * heq

@[expose] def trigammaSum (z : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / (z + (n : ℂ)) ^ 2

private lemma min_one_mul_succ_le {r : ℝ} (_hr : 0 < r) (n : ℕ) :
    min r 1 * ((n + 1 : ℕ) : ℝ) ≤ r + (n : ℝ) := by
  have hc1 : min r 1 ≤ 1 := min_le_right _ _
  have hcr : min r 1 ≤ r := min_le_left _ _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul : min r 1 * (n : ℝ) ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hc1 hn
  push_cast
  linarith

private lemma norm_add_nat_ge_re {z : ℂ} (_hz : 0 < z.re) (n : ℕ) :
    z.re + (n : ℝ) ≤ ‖z + (n : ℂ)‖ := by
  have hre : (z + (n : ℂ)).re = z.re + (n : ℝ) := by simp
  rw [← hre]
  exact Complex.re_le_norm _

private lemma inv_add_nat_pow_summable {p : ℕ} (hp : 2 ≤ p) {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => 1 / (r + (n : ℝ)) ^ p) := by
  let c : ℝ := min r 1
  have hc_pos : 0 < c := lt_min hr zero_lt_one
  have hlt : -(p : ℝ) < -1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hbase : Summable (fun n : ℕ => (c⁻¹ ^ p) * (1 / ((n + 1 : ℕ) : ℝ) ^ p)) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (-(p : ℝ)))) := Real.summable_nat_rpow.mpr hlt
    have h2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ p) := by
      refine ((summable_nat_add_iff 1).2 h1).congr fun n => ?_
      rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg _)]
    exact h2.mul_left (c⁻¹ ^ p)
  refine hbase.of_norm_bounded fun n => ?_
  have hle : c * ((n + 1 : ℕ) : ℝ) ≤ r + (n : ℝ) := min_one_mul_succ_le hr n
  have hpos : 0 < c * ((n + 1 : ℕ) : ℝ) := mul_pos hc_pos (by positivity)
  have hrn_pos : 0 < r + (n : ℝ) := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  calc 1 / (r + (n : ℝ)) ^ p
      ≤ 1 / (c * ((n + 1 : ℕ) : ℝ)) ^ p := by gcongr
    _ = c⁻¹ ^ p * (1 / ((n + 1 : ℕ) : ℝ) ^ p) := by
        rw [mul_pow, inv_pow]; ring

private lemma trigammaSum_summable {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => 1 / (z + (n : ℂ)) ^ 2) := by
  refine (inv_add_nat_pow_summable le_rfl hz).of_norm_bounded fun n => ?_
  rw [norm_div, norm_one, norm_pow]
  have hge := norm_add_nat_ge_re hz n
  have hpos : 0 < z.re + (n : ℝ) := by positivity
  gcongr

private lemma trigammaSum_add_one {z : ℂ} (hz : 0 < z.re) :
    trigammaSum (z + 1) = trigammaSum z - z⁻¹ ^ 2 := by
  have hs := trigammaSum_summable hz
  have hsplit := hs.tsum_eq_zero_add
  have htail : (∑' n : ℕ, 1 / (z + ((n + 1 : ℕ) : ℂ)) ^ 2) = trigammaSum (z + 1) := by
    refine tsum_congr fun n => ?_
    congr 2; push_cast; ring
  have htsum : trigammaSum z = 1 / (z + (0 : ℕ)) ^ 2 + trigammaSum (z + 1) := by
    rw [trigammaSum, hsplit, htail]
  rw [htsum]
  simp only [Nat.cast_zero, add_zero, one_div, inv_pow]
  ring

private lemma trigammaSum_two_mul {z : ℂ} (hz : 0 < z.re) :
    trigammaSum (2 * z) = (1 / 4 : ℂ) * (trigammaSum z + trigammaSum (z + 1 / 2)) := by
  have hzh : 0 < (z + 1 / 2).re := by
    simp only [Complex.add_re, one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat]; linarith
  let f : ℕ → ℂ := fun n => 1 / (2 * z + (n : ℂ)) ^ 2
  have heven : HasSum (fun k : ℕ => f (2 * k)) ((1 / 4 : ℂ) * trigammaSum z) := by
    have hs := (trigammaSum_summable hz).hasSum.mul_left (1 / 4 : ℂ)
    refine hs.congr_fun fun k => ?_
    dsimp only [f]
    have h4 : (2 * z + ((2 * k : ℕ) : ℂ)) = 2 * (z + (k : ℂ)) := by push_cast; ring
    have hsq : (2 * (z + (k : ℂ))) ^ 2 = 4 * (z + (k : ℂ)) ^ 2 := by ring
    rw [h4, hsq, one_div, one_div, one_div, mul_inv]
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) ((1 / 4 : ℂ) * trigammaSum (z + 1 / 2)) := by
    have hs := (trigammaSum_summable hzh).hasSum.mul_left (1 / 4 : ℂ)
    refine hs.congr_fun fun k => ?_
    dsimp only [f]
    have h4 : (2 * z + ((2 * k + 1 : ℕ) : ℂ)) = 2 * (z + 1 / 2 + (k : ℂ)) := by push_cast; ring
    have hsq : (2 * (z + 1 / 2 + (k : ℂ))) ^ 2 = 4 * (z + 1 / 2 + (k : ℂ)) ^ 2 := by ring
    rw [h4, hsq, one_div, one_div, one_div, mul_inv]
    ring
  have hcomb := heven.even_add_odd hodd
  change ∑' n : ℕ, f n = _
  rw [hcomb.tsum_eq]
  ring

private lemma trigammaSum_analyticOnNhd_re_pos :
    AnalyticOnNhd ℂ trigammaSum {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun z₀ hz₀ => ?_) hopen
  let r : ℝ := z₀.re / 2
  have hr_pos : 0 < r := half_pos hz₀
  have hre_gt : ∀ z ∈ Metric.ball z₀ r, r < z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre_diff : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have h1 := (abs_lt.mp (hre_diff.trans_lt hz)).1
    dsimp only [r] at *
    linarith
  have hdiff : DifferentiableOn ℂ trigammaSum (Metric.ball z₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (inv_add_nat_pow_summable le_rfl hr_pos) (fun n => ?_) Metric.isOpen_ball (fun n z hz => ?_)
    · refine DifferentiableOn.div (differentiableOn_const _)
        ((differentiableOn_id.add (differentiableOn_const _)).pow 2) fun z hz => ?_
      have hre := hre_gt z hz
      have hne := re_pos_avoids_neg_nat (lt_trans hr_pos hre) n
      have hsub : z + (n : ℂ) ≠ 0 := by intro h0; exact hne (eq_neg_of_add_eq_zero_left h0)
      exact pow_ne_zero 2 hsub
    · have hre := hre_gt z hz
      have hge := norm_add_nat_ge_re (lt_trans hr_pos hre) n
      have hrn : r + (n : ℝ) ≤ ‖z + (n : ℂ)‖ := by linarith
      have hrn_pos : 0 < r + (n : ℝ) := by positivity
      rw [norm_div, norm_one, norm_pow]
      gcongr
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))).differentiableWithinAt

/-- **Exact Trigamma Series** for `u > 0`: `ψ'(u) = ∑_{n ≥ 0} 1 / (u + n)^2`. -/
theorem trigamma_eq_trigammaSum {u : ℝ} (hu : 0 < u) :
    trigamma (u : ℂ) = trigammaSum (u : ℂ) := by
  let h : ℝ → ℂ := fun x => trigamma (x : ℂ) - trigammaSum (x : ℂ)
  have hh_add : ∀ x : ℝ, 0 < x → h (x + 1) = h x := by
    intro x hx
    have hxc : 0 < (x : ℂ).re := by simpa using hx
    dsimp only [h]
    push_cast
    rw [trigamma_add_one hxc, trigammaSum_add_one hxc]
    ring
  have hh_dup : ∀ x : ℝ, 0 < x → h (2 * x) = (1 / 4 : ℂ) * (h x + h (x + 1 / 2)) := by
    intro x hx
    have hxc : 0 < (x : ℂ).re := by simpa using hx
    dsimp only [h]
    push_cast
    rw [trigamma_two_mul hxc, trigammaSum_two_mul hxc]
    ring
  have hh_cont : ContinuousOn (fun x : ℝ => ‖h x‖) (Icc 1 2) := by
    refine ContinuousOn.norm ?_
    intro x hx
    have hx_pos : 0 < (x : ℂ).re := by simp; linarith [hx.1]
    have ht := (trigamma_analyticOnNhd_re_pos (x : ℂ) hx_pos).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
    have hs := (trigammaSum_analyticOnNhd_re_pos (x : ℂ) hx_pos).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
    exact (ht.sub hs).continuousWithinAt
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := isCompact_Icc.exists_isMaxOn ⟨1, by norm_num⟩ hh_cont
  have hx₀_pos : 0 < x₀ := by linarith [hx₀_mem.1]
  have hx₀_half_pos : 0 < x₀ / 2 := half_pos hx₀_pos
  have hx₀_1 : x₀ / 2 + 1 ∈ Icc (1 : ℝ) 2 := ⟨by linarith [hx₀_mem.1], by linarith [hx₀_mem.2]⟩
  have hx₀_2 : x₀ / 2 + 1 / 2 ∈ Icc (1 : ℝ) 2 := ⟨by linarith [hx₀_mem.1], by linarith [hx₀_mem.2]⟩
  have h_le1 : ‖h (x₀ / 2)‖ ≤ ‖h x₀‖ := by
    rw [← hh_add (x₀ / 2) hx₀_half_pos]
    exact hx₀_max hx₀_1
  have h_le2 : ‖h (x₀ / 2 + 1 / 2)‖ ≤ ‖h x₀‖ := hx₀_max hx₀_2
  have h_eq0 : ‖h x₀‖ ≤ (1 / 2 : ℝ) * ‖h x₀‖ := by
    calc ‖h x₀‖ = ‖h (2 * (x₀ / 2))‖ := by ring_nf
      _ = ‖(1 / 4 : ℂ) * (h (x₀ / 2) + h (x₀ / 2 + 1 / 2))‖ := by rw [hh_dup (x₀ / 2) hx₀_half_pos]
      _ = (1 / 4 : ℝ) * ‖h (x₀ / 2) + h (x₀ / 2 + 1 / 2)‖ := by
          rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
      _ ≤ (1 / 4 : ℝ) * (‖h (x₀ / 2)‖ + ‖h (x₀ / 2 + 1 / 2)‖) := by gcongr; exact norm_add_le _ _
      _ ≤ (1 / 4 : ℝ) * (‖h x₀‖ + ‖h x₀‖) := by gcongr
      _ = (1 / 2 : ℝ) * ‖h x₀‖ := by ring
  have h_norm_zero : ‖h x₀‖ = 0 := by linarith [norm_nonneg (h x₀)]
  have h_icc_zero : ∀ x ∈ Icc (1 : ℝ) 2, h x = 0 := fun x hx =>
    norm_eq_zero.mp (le_antisymm ((hx₀_max hx).trans_eq h_norm_zero) (norm_nonneg _))
  have h_ge_one : ∀ x : ℝ, 1 ≤ x → h x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x ≤ 2 + (n : ℝ) := ⟨Nat.ceil x, by linarith [Nat.le_ceil x]⟩
    induction n generalizing x with
    | zero => exact h_icc_zero x ⟨hx, by simpa using hn⟩
    | succ n ih =>
      by_cases hx2 : x ≤ 2
      · exact h_icc_zero x ⟨hx, hx2⟩
      · push Not at hx2
        have hx1 : 1 ≤ x - 1 := by linarith
        have hx1_pos : 0 < x - 1 := by linarith
        have hsub : x - 1 ≤ 2 + (n : ℝ) := by push_cast at hn; linarith
        have heq : h x = h ((x - 1) + 1) := by ring_nf
        rw [heq, hh_add (x - 1) hx1_pos]
        exact ih (x - 1) hx1 hsub
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 ≤ u + (k : ℝ) := ⟨1, by push_cast; linarith⟩
  have h_all : ∀ k : ℕ, h (u + (k : ℝ)) = 0 → h u = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      intro hsucc
      have huk : 0 < u + (k : ℝ) := by positivity
      have heq : h (u + ((k + 1 : ℕ) : ℝ)) = h (u + (k : ℝ)) := by
        rw [show u + ((k + 1 : ℕ) : ℝ) = (u + (k : ℝ)) + 1 by push_cast; ring]
        exact hh_add _ huk
      exact ihk (heq.symm.trans hsucc)
  exact sub_eq_zero.mp (h_all k (h_ge_one _ hk))

private lemma hasDerivAt_inv_add_nat_pow (p : ℕ) (hp : 2 ≤ p) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, 1 / ((x : ℂ) + (n : ℂ)) ^ p)
      (-(p : ℂ) * ∑' n : ℕ, 1 / ((u₀ : ℂ) + (n : ℂ)) ^ (p + 1)) u₀ := by
  let r : ℝ := u₀ / 2
  have hr_pos : 0 < r := half_pos hu₀
  let t : Set ℂ := Metric.ball (u₀ : ℂ) r
  have ht_open : IsOpen t := Metric.isOpen_ball
  have ht_pre : IsPreconnected t := (convex_ball (u₀ : ℂ) r).isPreconnected
  let g : ℕ → ℂ → ℂ := fun n z => 1 / (z + (n : ℂ)) ^ p
  let g' : ℕ → ℂ → ℂ := fun n z => -(p : ℂ) / (z + (n : ℂ)) ^ (p + 1)
  have hre_gt : ∀ z ∈ t, r < z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre_diff : |z.re - u₀| ≤ ‖z - (u₀ : ℂ)‖ := by
      have : z.re - u₀ = (z - (u₀ : ℂ)).re := by simp
      rw [this]
      exact Complex.abs_re_le_norm _
    have h1 := (abs_lt.mp (hre_diff.trans_lt hz)).1
    dsimp only [r] at *
    linarith
  have hg : ∀ (n : ℕ) (z : ℂ), z ∈ t → HasDerivAt (g n) (g' n z) z := by
    intro n z hz
    have hz_pos : 0 < z.re := lt_trans hr_pos (hre_gt z hz)
    have hne : z + (n : ℂ) ≠ 0 := by
      intro h0
      exact re_pos_avoids_neg_nat hz_pos n (eq_neg_of_add_eq_zero_left h0)
    have hd1 : HasDerivAt (fun w : ℂ => (w + (n : ℂ)) ^ p) ((p : ℂ) * (z + (n : ℂ)) ^ (p - 1)) z :=
      (((hasDerivAt_id z).add_const (n : ℂ)).pow p).congr_deriv (mul_one _)
    have hd2 : HasDerivAt (g n) (-(p : ℂ) * (z + (n : ℂ)) ^ (p - 1) / ((z + (n : ℂ)) ^ p) ^ 2) z := by
      have h0 := hd1.inv (pow_ne_zero p hne)
      refine h0.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp [g]) |>.congr_deriv ?_
      ring
    refine hd2.congr_deriv ?_
    dsimp only [g']
    rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero p hne)) (pow_ne_zero (p + 1) hne)]
    calc -(p : ℂ) * (z + (n : ℂ)) ^ (p - 1) * (z + (n : ℂ)) ^ (p + 1)
        = -(p : ℂ) * ((z + (n : ℂ)) ^ (p - 1) * (z + (n : ℂ)) ^ (p + 1)) := by ring
      _ = -(p : ℂ) * (z + (n : ℂ)) ^ (2 * p) := by
          rw [← pow_add, show p - 1 + (p + 1) = 2 * p by omega]
      _ = -(p : ℂ) * ((z + (n : ℂ)) ^ p) ^ 2 := by
          rw [mul_comm 2 p, pow_mul]
  let uBound : ℕ → ℝ := fun n => (p : ℝ) * (1 / (r + (n : ℝ)) ^ (p + 1))
  have hu_summ : Summable uBound :=
    (inv_add_nat_pow_summable (by omega : 2 ≤ p + 1) hr_pos).mul_left (p : ℝ)
  have hg' : ∀ (n : ℕ) (z : ℂ), z ∈ t → ‖g' n z‖ ≤ uBound n := by
    intro n z hz
    have hz_pos : 0 < z.re := lt_trans hr_pos (hre_gt z hz)
    have hre := hre_gt z hz
    have hge : r + (n : ℝ) ≤ ‖z + (n : ℂ)‖ := by linarith [norm_add_nat_ge_re hz_pos n]
    have hrn_pos : 0 < r + (n : ℝ) := by positivity
    dsimp only [g', uBound]
    rw [norm_div, norm_neg, Complex.norm_natCast, norm_pow, mul_one_div]
    gcongr
  have hu₀_mem : (u₀ : ℂ) ∈ t := Metric.mem_ball_self hr_pos
  have hu₀_re : 0 < ((u₀ : ℂ)).re := by simpa only [Complex.ofReal_re] using hu₀
  have hg0 : Summable fun n => g n (u₀ : ℂ) := by
    refine (inv_add_nat_pow_summable hp hu₀).of_norm_bounded fun n => ?_
    dsimp only [g]
    rw [norm_div, norm_one, norm_pow]
    have hge := norm_add_nat_ge_re hu₀_re n
    have hpos : 0 < (u₀ : ℝ) + (n : ℝ) := by positivity
    simp only [Complex.ofReal_re] at hge
    gcongr
  have hcomplex := hasDerivAt_tsum_of_isPreconnected hu_summ ht_open ht_pre hg hg' hu₀_mem hg0 hu₀_mem
  have hreal := hcomplex.comp_ofReal
  refine hreal.congr_deriv ?_
  have hs_g' : Summable (fun n : ℕ => 1 / ((u₀ : ℂ) + (n : ℂ)) ^ (p + 1)) := by
    refine (inv_add_nat_pow_summable (by omega : 2 ≤ p + 1) hu₀).of_norm_bounded fun n => ?_
    rw [norm_div, norm_one, norm_pow]
    have hge := norm_add_nat_ge_re hu₀_re n
    have hpos : 0 < (u₀ : ℝ) + (n : ℝ) := by positivity
    simp only [Complex.ofReal_re] at hge
    gcongr
  have htsum_mul : (∑' n : ℕ, g' n (u₀ : ℂ)) = -(p : ℂ) * ∑' n : ℕ, 1 / ((u₀ : ℂ) + (n : ℂ)) ^ (p + 1) := by
    rw [← hs_g'.tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp [g', div_eq_mul_inv]
  exact htsum_mul

lemma iteratedDeriv_trigamma_of_pos (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) u =
      (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * ∑' n : ℕ, 1 / ((u : ℂ) + (n : ℂ)) ^ (j + 2) := by
  induction j generalizing u with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul, Nat.factorial_one,
      Nat.cast_one, zero_add]
    exact trigamma_eq_trigammaSum hu
  | succ j ih =>
    have hev : iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) =ᶠ[𝓝 u]
        fun x : ℝ => (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
          ∑' n : ℕ, 1 / ((x : ℂ) + (n : ℂ)) ^ (j + 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
      exact ih hx
    have hd_sum := (hasDerivAt_inv_add_nat_pow (j + 2) (by omega) hu).const_mul
      ((-1 : ℂ) ^ j * ((j + 1).factorial : ℂ))
    rw [iteratedDeriv_succ, hev.deriv_eq, hd_sum.deriv]
    rw [pow_succ, Nat.factorial_succ (j + 1)]
    push_cast
    ring

private def invPowDeriv (u : ℝ) (p m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * (((p + m - 1).factorial : ℝ) / ((p - 1).factorial : ℝ)) * (u + x)⁻¹ ^ (p + m)

private lemma hasDerivAt_invPowDeriv {u : ℝ} (hu : 0 < u) {p : ℕ} (hp : 1 ≤ p) (m : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (invPowDeriv u p m) (invPowDeriv u p (m + 1) x) x := by
  have hux : u + x ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t : ℝ => (u + t)⁻¹ ^ (p + m))
      (-((p + m : ℕ) : ℝ) * (u + x)⁻¹ ^ (p + m + 1)) x := by
    have ha : HasDerivAt (fun t : ℝ => u + t) 1 x := (hasDerivAt_id x).const_add u
    have hinv : HasDerivAt (fun t : ℝ => (u + t)⁻¹) (-1 / (u + x) ^ 2) x :=
      (ha.inv hux).congr_deriv (by rw [neg_div, one_div])
    have hpow := hinv.pow (p + m)
    refine hpow.congr_deriv ?_
    have hpow_eq : (u + x)⁻¹ ^ (p + m - 1) * (-1 / (u + x) ^ 2) = -((u + x)⁻¹ ^ (p + m + 1)) := by
      have hsub : p + m - 1 + 2 = p + m + 1 := by omega
      rw [neg_div, one_div, mul_neg, ← inv_pow, ← pow_add, hsub]
    calc ((p + m : ℕ) : ℝ) * (u + x)⁻¹ ^ (p + m - 1) * (-1 / (u + x) ^ 2)
        = ((p + m : ℕ) : ℝ) * ((u + x)⁻¹ ^ (p + m - 1) * (-1 / (u + x) ^ 2)) := by ring
      _ = -((p + m : ℕ) : ℝ) * (u + x)⁻¹ ^ (p + m + 1) := by rw [hpow_eq]; ring
  have h2 := h1.const_mul ((-1 : ℝ) ^ m * (((p + m - 1).factorial : ℝ) / ((p - 1).factorial : ℝ)))
  refine h2.congr_deriv ?_
  dsimp only [invPowDeriv]
  have hpm : p + m = (p + m - 1) + 1 := by omega
  have hfac : ((p + (m + 1) - 1).factorial : ℝ) = ((p + m : ℕ) : ℝ) * ((p + m - 1).factorial : ℝ) := by
    rw [show p + (m + 1) - 1 = (p + m - 1) + 1 by omega, Nat.factorial_succ, ← hpm]
    push_cast; rfl
  rw [hfac, pow_succ]
  ring

private lemma continuousOn_invPowDeriv {u : ℝ} (hu : 0 < u) (p m : ℕ) {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (invPowDeriv u p m) (Icc a b) := by
  intro x hx
  have hux : u + x ≠ 0 := by linarith [hx.1]
  exact (((continuousAt_const.add continuousAt_id).inv₀ hux).pow (p + m)).const_mul _ |>.continuousWithinAt

private lemma eulerMaclaurin_finite {u : ℝ} (hu : 0 < u) {p : ℕ} (hp : 2 ≤ p) (N K : ℕ) :
    ∑ n ∈ Finset.range N, (u + (n : ℝ))⁻¹ ^ p =
      (∫ x in (0 : ℝ)..(N : ℝ), (u + x)⁻¹ ^ p) +
        (1 / 2 : ℝ) * (invPowDeriv u p 0 0 - invPowDeriv u p 0 (N : ℝ)) +
        ∑ k ∈ Finset.Ico 1 (K + 1),
          (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
            (invPowDeriv u p k 0 - invPowDeriv u p k (N : ℝ)) +
        (-1 : ℝ) ^ K * ∑ n ∈ Finset.range N,
          ∫ t in (0 : ℝ)..1, (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
            invPowDeriv u p (K + 1) ((n : ℝ) + t) := by
  have hp1 : 1 ≤ p := by omega
  have h_one_step : ∀ (n : ℕ),
      (u + (n : ℝ))⁻¹ ^ p =
        (∫ t in (0 : ℝ)..1, (u + ((n : ℝ) + t))⁻¹ ^ p) +
          (1 / 2 : ℝ) * (invPowDeriv u p 0 (n : ℝ) - invPowDeriv u p 0 ((n + 1 : ℕ) : ℝ)) +
          ∫ t in (0 : ℝ)..1, (bernoulliFun 1 t / ((1 : ℕ).factorial : ℝ)) *
            invPowDeriv u p 1 ((n : ℝ) + t) := by
    intro n
    let F : ℝ → ℝ := fun t => bernoulliFun 1 t * invPowDeriv u p 0 ((n : ℝ) + t)
    let F' : ℝ → ℝ := fun t =>
      invPowDeriv u p 0 ((n : ℝ) + t) + bernoulliFun 1 t * invPowDeriv u p 1 ((n : ℝ) + t)
    have hderiv : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt F (F' t) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hb : HasDerivAt (bernoulliFun 1) 1 t := by
        simpa using hasDerivAt_bernoulliFun 1 t
      have hg : HasDerivAt (fun s : ℝ => invPowDeriv u p 0 ((n : ℝ) + s))
          (invPowDeriv u p 1 ((n : ℝ) + t)) t := by
        have hcomp := (hasDerivAt_invPowDeriv hu hp1 0 (by linarith [ht.1] : 0 ≤ (n : ℝ) + t)).comp t
          ((hasDerivAt_id t).const_add (n : ℝ))
        simpa only [Function.comp_def, mul_one] using hcomp
      have hmul := hb.mul hg
      refine hmul.congr_deriv ?_
      dsimp only [F']
      ring
    have hcont_inv : ∀ (m : ℕ), ContinuousOn (fun t : ℝ => invPowDeriv u p m ((n : ℝ) + t)) (Icc 0 1) := by
      intro m t ht
      have hux : u + ((n : ℝ) + t) ≠ 0 := by linarith [ht.1]
      have hc1 : ContinuousAt (fun s : ℝ => u + ((n : ℝ) + s)) t :=
        continuousAt_const.add (continuousAt_const.add continuousAt_id)
      exact (((hc1.inv₀ hux).pow (p + m)).const_mul _).continuousWithinAt
    have hcont1 : ContinuousOn (fun t : ℝ => invPowDeriv u p 0 ((n : ℝ) + t)) (Icc 0 1) := hcont_inv 0
    have hcont2 : ContinuousOn (fun t : ℝ => bernoulliFun 1 t * invPowDeriv u p 1 ((n : ℝ) + t)) (Icc 0 1) :=
      (continuous_bernoulliFun 1).continuousOn.mul (hcont_inv 1)
    have hi1 : IntervalIntegrable (fun t : ℝ => invPowDeriv u p 0 ((n : ℝ) + t)) volume 0 1 :=
      hcont1.intervalIntegrable_of_Icc zero_le_one
    have hi2 : IntervalIntegrable (fun t : ℝ => bernoulliFun 1 t * invPowDeriv u p 1 ((n : ℝ) + t)) volume 0 1 :=
      hcont2.intervalIntegrable_of_Icc zero_le_one
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
    rw [intervalIntegral.integral_add hi1 hi2] at hftc
    have hF1 : F 1 = (1 / 2 : ℝ) * invPowDeriv u p 0 ((n + 1 : ℕ) : ℝ) := by
      dsimp only [F]
      rw [bernoulliFun_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; rfl]
    have hF0 : F 0 = -(1 / 2 : ℝ) * invPowDeriv u p 0 (n : ℝ) := by
      dsimp only [F]
      rw [bernoulliFun_one, add_zero, show (0 : ℝ) - 1 / 2 = -(1 / 2) by norm_num]
    have hg0 : invPowDeriv u p 0 (n : ℝ) = (u + (n : ℝ))⁻¹ ^ p := by
      rw [invPowDeriv, pow_zero, one_mul, add_zero,
        div_self (by positivity : ((p - 1).factorial : ℝ) ≠ 0), one_mul]
    have hg_eq : (fun t : ℝ => invPowDeriv u p 0 ((n : ℝ) + t)) =
        fun t : ℝ => (u + ((n : ℝ) + t))⁻¹ ^ p := by
      ext t
      rw [invPowDeriv, pow_zero, one_mul, add_zero,
        div_self (by positivity : ((p - 1).factorial : ℝ) ≠ 0), one_mul]
    rw [hF1, hF0, hg_eq] at hftc
    simp only [Nat.factorial_one, Nat.cast_one, div_one]
    linarith [hg0]
  induction K with
  | zero =>
    simp only [Nat.zero_add, Finset.Ico_self, Finset.sum_empty, add_zero, pow_zero, one_mul]
    have hsum : ∑ n ∈ Finset.range N, (u + (n : ℝ))⁻¹ ^ p =
        (∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..1, (u + ((n : ℝ) + t))⁻¹ ^ p) +
        (∑ n ∈ Finset.range N, (1 / 2 : ℝ) * (invPowDeriv u p 0 (n : ℝ) - invPowDeriv u p 0 ((n + 1 : ℕ) : ℝ))) +
        (∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..1, (bernoulliFun 1 t / ((1 : ℕ).factorial : ℝ)) *
          invPowDeriv u p 1 ((n : ℝ) + t)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => h_one_step n
    have hint_sum : (∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..1, (u + ((n : ℝ) + t))⁻¹ ^ p) =
        ∫ x in (0 : ℝ)..(N : ℝ), (u + x)⁻¹ ^ p := by
      have heach : ∀ n ∈ Finset.range N,
          (∫ t in (0 : ℝ)..1, (u + ((n : ℝ) + t))⁻¹ ^ p) =
            ∫ x in ((n : ℕ) : ℝ)..((n + 1 : ℕ) : ℝ), (u + x)⁻¹ ^ p := by
        intro n _
        have := intervalIntegral.integral_comp_add_left (fun x => (u + x)⁻¹ ^ p) (n : ℝ) (a := (0 : ℝ)) (b := 1)
        simpa [add_zero, Nat.cast_add, Nat.cast_one] using this
      rw [Finset.sum_congr rfl heach]
      have hadj := intervalIntegral.sum_integral_adjacent_intervals
        (μ := volume) (f := fun x : ℝ => (u + x)⁻¹ ^ p) (a := fun k : ℕ => (k : ℝ)) (n := N) fun k _ => by
        refine ContinuousOn.intervalIntegrable_of_Icc (by push_cast; linarith) ?_
        intro x hx
        have hux : u + x ≠ 0 := by linarith [hx.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        exact (((continuousAt_const.add continuousAt_id).inv₀ hux).pow p).continuousWithinAt
      simpa using hadj
    have htele : (∑ n ∈ Finset.range N,
        (1 / 2 : ℝ) * (invPowDeriv u p 0 (n : ℝ) - invPowDeriv u p 0 ((n + 1 : ℕ) : ℝ))) =
        (1 / 2 : ℝ) * (invPowDeriv u p 0 0 - invPowDeriv u p 0 (N : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub' (fun n => invPowDeriv u p 0 (n : ℝ)) N, Nat.cast_zero]
    rw [hsum, hint_sum, htele]
  | succ K ih =>
    have h_step_ibp : ∀ n : ℕ,
        (∫ t in (0 : ℝ)..1, (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
          invPowDeriv u p (K + 1) ((n : ℝ) + t)) =
          -((bernoulli (K + 2) : ℝ) / ((K + 2).factorial : ℝ)) *
            (invPowDeriv u p (K + 1) (n : ℝ) - invPowDeriv u p (K + 1) ((n + 1 : ℕ) : ℝ)) -
          ∫ t in (0 : ℝ)..1, (bernoulliFun (K + 2) t / ((K + 2).factorial : ℝ)) *
            invPowDeriv u p (K + 2) ((n : ℝ) + t) := by
      intro n
      let G : ℝ → ℝ := fun t =>
        (bernoulliFun (K + 2) t / ((K + 2).factorial : ℝ)) * invPowDeriv u p (K + 1) ((n : ℝ) + t)
      let G' : ℝ → ℝ := fun t =>
        (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) * invPowDeriv u p (K + 1) ((n : ℝ) + t) +
        (bernoulliFun (K + 2) t / ((K + 2).factorial : ℝ)) * invPowDeriv u p (K + 2) ((n : ℝ) + t)
      have hderiv : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt G (G' t) t := by
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        have hb : HasDerivAt (fun s => bernoulliFun (K + 2) s / ((K + 2).factorial : ℝ))
            (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) t := by
          have h1 := (hasDerivAt_bernoulliFun (K + 2) t).div_const ((K + 2).factorial : ℝ)
          refine h1.congr_deriv ?_
          rw [show K + 2 - 1 = K + 1 by omega, show (K + 2 : ℕ) = K + 1 + 1 by omega,
            Nat.factorial_succ (K + 1)]
          push_cast
          exact mul_div_mul_left (bernoulliFun (K + 1) t) ((K + 1).factorial : ℝ)
            (by positivity : ((K : ℝ) + 1 + 1) ≠ 0)
        have hg : HasDerivAt (fun s : ℝ => invPowDeriv u p (K + 1) ((n : ℝ) + s))
            (invPowDeriv u p (K + 2) ((n : ℝ) + t)) t := by
          have hcomp := (hasDerivAt_invPowDeriv hu hp1 (K + 1) (by linarith [ht.1] : 0 ≤ (n : ℝ) + t)).comp t
            ((hasDerivAt_id t).const_add (n : ℝ))
          exact hcomp.congr_deriv (mul_one _)
        exact hb.mul hg
      have hcont_inv : ∀ (m : ℕ), ContinuousOn (fun t : ℝ => invPowDeriv u p m ((n : ℝ) + t)) (Icc 0 1) := by
        intro m t ht
        have hux : u + ((n : ℝ) + t) ≠ 0 := by linarith [ht.1]
        have hc1 : ContinuousAt (fun s : ℝ => u + ((n : ℝ) + s)) t :=
          continuousAt_const.add (continuousAt_const.add continuousAt_id)
        exact (((hc1.inv₀ hux).pow (p + m)).const_mul _).continuousWithinAt
      have hcont1 : ContinuousOn
          (fun t : ℝ => (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
            invPowDeriv u p (K + 1) ((n : ℝ) + t)) (Icc 0 1) :=
        ((continuous_bernoulliFun (K + 1)).div_const _).continuousOn.mul (hcont_inv (K + 1))
      have hcont2 : ContinuousOn
          (fun t : ℝ => (bernoulliFun (K + 2) t / ((K + 2).factorial : ℝ)) *
            invPowDeriv u p (K + 2) ((n : ℝ) + t)) (Icc 0 1) :=
        ((continuous_bernoulliFun (K + 2)).div_const _).continuousOn.mul (hcont_inv (K + 2))
      have hi1 : IntervalIntegrable _ volume (0 : ℝ) 1 := hcont1.intervalIntegrable_of_Icc zero_le_one
      have hi2 : IntervalIntegrable _ volume (0 : ℝ) 1 := hcont2.intervalIntegrable_of_Icc zero_le_one
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
      rw [intervalIntegral.integral_add hi1 hi2] at hftc
      have hG1 : G 1 = ((bernoulli (K + 2) : ℝ) / ((K + 2).factorial : ℝ)) *
          invPowDeriv u p (K + 1) ((n + 1 : ℕ) : ℝ) := by
        dsimp only [G]
        rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero]
        push_cast; rfl
      have hG0 : G 0 = ((bernoulli (K + 2) : ℝ) / ((K + 2).factorial : ℝ)) *
          invPowDeriv u p (K + 1) (n : ℝ) := by
        dsimp only [G]
        rw [bernoulliFun_eval_zero]
        simp
      rw [hG1, hG0] at hftc
      linarith
    rw [ih]
    have hsum_step : (∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..1,
          (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) * invPowDeriv u p (K + 1) ((n : ℝ) + t)) =
        -((bernoulli (K + 2) : ℝ) / ((K + 2).factorial : ℝ)) *
          (invPowDeriv u p (K + 1) 0 - invPowDeriv u p (K + 1) (N : ℝ)) -
        ∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..1,
          (bernoulliFun (K + 2) t / ((K + 2).factorial : ℝ)) * invPowDeriv u p (K + 2) ((n : ℝ) + t) := by
      rw [Finset.sum_congr rfl (fun n _ => h_step_ibp n), Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub' (fun n => invPowDeriv u p (K + 1) (n : ℝ)) N, Nat.cast_zero]
    rw [hsum_step, Finset.sum_Ico_succ_top (by omega : 1 ≤ K + 1)]
    rw [pow_succ]
    ring

private lemma tendsto_inv_add_nat_pow_atTop {u : ℝ} (_hu : 0 < u) {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => (u + (N : ℝ))⁻¹ ^ q) atTop (𝓝 0) := by
  have hadd : Tendsto (fun N : ℕ => u + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop u tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => (u + (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hadd
  have hpow : Tendsto (fun N : ℕ => ((u + (N : ℝ))⁻¹) ^ q) atTop (𝓝 ((0 : ℝ) ^ q)) :=
    ht.pow q
  simpa [zero_pow (by omega : q ≠ 0)] using hpow

private lemma tendsto_invPowDeriv_atTop {u : ℝ} (hu : 0 < u) {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    Tendsto (fun N : ℕ => invPowDeriv u p k (N : ℝ)) atTop (𝓝 0) := by
  have ht := tendsto_inv_add_nat_pow_atTop hu (by omega : 1 ≤ p + k)
  simpa [invPowDeriv] using ht.const_mul _

private lemma eulerMaclaurin_remainder_bound {u : ℝ} (hu : 1 ≤ u) {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun n : ℕ => ∫ t in (0 : ℝ)..1,
        (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
          invPowDeriv u p (K + 1) ((n : ℝ) + t)) ∧
      |∑' n : ℕ, ∫ t in (0 : ℝ)..1,
        (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
          invPowDeriv u p (K + 1) ((n : ℝ) + t)| ≤ C / u ^ K := by
  have hcont_B : ContinuousOn (fun t : ℝ => |bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)|) (Icc 0 1) :=
    ((continuous_bernoulliFun (K + 1)).div_const _).abs.continuousOn
  obtain ⟨MB, hMB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_B
  let MB' : ℝ := max MB 0
  have hMB' : 0 ≤ MB' := le_max_right _ _
  let coeffP : ℝ := ((p + K).factorial : ℝ) / ((p - 1).factorial : ℝ)
  have hcoeffP : 0 ≤ coeffP := by positivity
  let C : ℝ := MB' * coeffP * ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2
  have hzeta2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := Real.summable_nat_rpow.mpr (by norm_num)
    refine ((summable_nat_add_iff 1).2 h1).congr fun n => ?_
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg _)]; norm_num
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hMB' hcoeffP) (tsum_nonneg fun _ => by positivity)
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  let gRem : ℕ → ℝ := fun n =>
    ∫ t in (0 : ℝ)..1, (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
      invPowDeriv u p (K + 1) ((n : ℝ) + t)
  have hbound_n : ∀ n : ℕ, ‖gRem n‖ ≤ (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hle_t : ∀ t ∈ uIoc (0 : ℝ) 1,
        ‖(bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
          invPowDeriv u p (K + 1) ((n : ℝ) + t)‖ ≤
          (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have hpos_unt : 0 < u + ((n : ℝ) + t) := by linarith [ht.1]
      have hbt : |bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)| ≤ MB' := by
        have hb0 := hMB t ⟨ht.1.le, ht.2⟩
        rw [Real.norm_of_nonneg (abs_nonneg _)] at hb0
        exact hb0.trans (le_max_left _ _)
      have hnt_ge : (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)) ≤
          (1 / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        have hpow_ge : u ^ K * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (u + ((n : ℝ) + t)) ^ (p + (K + 1)) := by
          have h1 : u ^ K ≤ (u + ((n : ℝ) + t)) ^ K := pow_le_pow_left₀ hu_pos.le (by linarith [ht.1]) K
          have h2 : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (u + ((n : ℝ) + t)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by push_cast; linarith [ht.1]) 2
          have h3 : (u + ((n : ℝ) + t)) ^ (K + 2) ≤ (u + ((n : ℝ) + t)) ^ (p + (K + 1)) :=
            pow_le_pow_right₀ (by linarith [ht.1]) (by omega)
          calc u ^ K * ((n + 1 : ℕ) : ℝ) ^ 2
              ≤ (u + ((n : ℝ) + t)) ^ K * (u + ((n : ℝ) + t)) ^ 2 :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = (u + ((n : ℝ) + t)) ^ (K + 2) := by rw [pow_add]
            _ ≤ (u + ((n : ℝ) + t)) ^ (p + (K + 1)) := h3
        rw [inv_pow, ← one_div, one_div_mul_one_div]
        exact one_div_le_one_div_of_le (by positivity) hpow_ge
      rw [Real.norm_eq_abs, abs_mul]
      have hinv_abs : |invPowDeriv u p (K + 1) ((n : ℝ) + t)| =
          coeffP * (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)) := by
        dsimp only [invPowDeriv, coeffP]
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hpos_unt.le) _),
          show p + (K + 1) - 1 = p + K by omega]
      rw [hinv_abs]
      have hnonneg_c : 0 ≤ coeffP * (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)) :=
        mul_nonneg hcoeffP (pow_nonneg (inv_nonneg.mpr hpos_unt.le) _)
      calc |bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)| *
            (coeffP * (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)))
          ≤ MB' * (coeffP * ((1 / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2))) :=
            mul_le_mul hbt (mul_le_mul_of_nonneg_left hnt_ge hcoeffP) hnonneg_c hMB'
        _ = (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hle_t
    simpa [gRem] using hnorm
  have hdom : Summable (fun n : ℕ => (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    hzeta2.mul_left _
  have hsumm : Summable gRem := hdom.of_norm_bounded hbound_n
  refine ⟨C, hC, hsumm, ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖∑' n : ℕ, gRem n‖ ≤ ∑' n : ℕ, ‖gRem n‖ := norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' n : ℕ, (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
        hsumm.norm.tsum_le_tsum hbound_n hdom
    _ = (MB' * coeffP / u ^ K) * ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := tsum_mul_left
    _ = C / u ^ K := by dsimp only [C]; ring

private lemma eulerMaclaurin_asymp_real (p K : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, ∀ {u : ℝ}, 1 ≤ u →
      |∑' n : ℕ, (u + (n : ℝ))⁻¹ ^ p -
        ((p - 1 : ℝ)⁻¹ * u⁻¹ ^ (p - 1) +
          (1 / 2 : ℝ) * u⁻¹ ^ p +
          ∑ k ∈ Finset.Ico 1 (K + 1),
            (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
              ((-1 : ℝ) ^ k * (((p + k - 1).factorial : ℝ) / ((p - 1).factorial : ℝ)) *
                u⁻¹ ^ (p + k)))| ≤ C / u ^ K := by
  have hcont_B : ContinuousOn (fun t : ℝ => |bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)|) (Icc 0 1) :=
    ((continuous_bernoulliFun (K + 1)).div_const _).abs.continuousOn
  obtain ⟨MB, hMB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_B
  let MB' : ℝ := max MB 0
  have hMB' : 0 ≤ MB' := le_max_right _ _
  let coeffP : ℝ := ((p + K).factorial : ℝ) / ((p - 1).factorial : ℝ)
  have hcoeffP : 0 ≤ coeffP := by positivity
  have hzeta2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := Real.summable_nat_rpow.mpr (by norm_num)
    refine ((summable_nat_add_iff 1).2 h1).congr fun n => ?_
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg _)]; norm_num
  refine ⟨MB' * coeffP * ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2, fun {u} hu => ?_⟩
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hp1 : 1 ≤ p := by omega
  have h_summ : Summable (fun n : ℕ => (u + (n : ℝ))⁻¹ ^ p) := by
    simpa only [one_div, inv_pow] using inv_add_nat_pow_summable hp hu_pos
  have h_lim_L : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (u + (n : ℝ))⁻¹ ^ p)
      atTop (𝓝 (∑' n : ℕ, (u + (n : ℝ))⁻¹ ^ p)) := h_summ.hasSum.tendsto_sum_nat
  have h_int_eq : ∀ N : ℕ, (∫ x in (0 : ℝ)..(N : ℝ), (u + x)⁻¹ ^ p) =
      (p - 1 : ℝ)⁻¹ * (u⁻¹ ^ (p - 1) - (u + (N : ℝ))⁻¹ ^ (p - 1)) := by
    intro N
    let F : ℝ → ℝ := fun x => -((p - 1 : ℝ)⁻¹ * (u + x)⁻¹ ^ (p - 1))
    have hderiv : ∀ x ∈ [[(0 : ℝ), (N : ℝ)]], HasDerivAt F ((u + x)⁻¹ ^ p) x := by
      intro x hx
      rw [Set.uIcc_of_le (Nat.cast_nonneg N)] at hx
      have hux : u + x ≠ 0 := by linarith [hx.1]
      have ha : HasDerivAt (fun t : ℝ => u + t) 1 x := (hasDerivAt_id x).const_add u
      have hinv : HasDerivAt (fun t : ℝ => (u + t)⁻¹) (-1 / (u + x) ^ 2) x :=
        (ha.inv hux).congr_deriv (by rw [neg_div, one_div])
      have hpow : HasDerivAt F
          (-((p - 1 : ℝ)⁻¹) * (((p - 1 : ℕ) : ℝ) * (u + x)⁻¹ ^ (p - 1 - 1) * (-1 / (u + x) ^ 2))) x :=
        ((hinv.pow (p - 1)).const_mul (-((p - 1 : ℝ)⁻¹))).congr_of_eventuallyEq
          (Eventually.of_forall fun t => by simp [F, neg_mul])
      refine hpow.congr_deriv ?_
      have hp_ne : (p - 1 : ℝ) ≠ 0 := by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
        linarith
      have hsub : p - 1 - 1 + 2 = p := by omega
      simp only [neg_div, one_div, ← inv_pow, neg_mul, mul_neg, neg_neg]
      calc (p - 1 : ℝ)⁻¹ * (((p - 1 : ℕ) : ℝ) * (u + x)⁻¹ ^ (p - 1 - 1) * (u + x)⁻¹ ^ 2)
          = (p - 1 : ℝ)⁻¹ * (p - 1 : ℝ) * ((u + x)⁻¹ ^ (p - 1 - 1) * (u + x)⁻¹ ^ 2) := by
            push_cast [hp1]; ring
        _ = 1 * (u + x)⁻¹ ^ (p - 1 - 1 + 2) := by rw [inv_mul_cancel₀ hp_ne, ← pow_add]
        _ = (u + x)⁻¹ ^ p := by rw [one_mul, hsub]
    have hcont : ContinuousOn (fun x : ℝ => (u + x)⁻¹ ^ p) (Icc 0 (N : ℝ)) := by
      intro x hx
      have hux : u + x ≠ 0 := by linarith [hx.1]
      exact (((continuousAt_const.add continuousAt_id).inv₀ hux).pow p).continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable_of_Icc (Nat.cast_nonneg N))
    dsimp only [F] at hftc
    rw [hftc, add_zero]
    ring
  have h_lim_int : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), (u + x)⁻¹ ^ p)
      atTop (𝓝 ((p - 1 : ℝ)⁻¹ * u⁻¹ ^ (p - 1))) := by
    simp_rw [h_int_eq]
    have ht := tendsto_inv_add_nat_pow_atTop hu_pos (by omega : 1 ≤ p - 1)
    simpa using (tendsto_const_nhds.sub ht).const_mul ((p - 1 : ℝ)⁻¹)
  have h_lim_0 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) * (invPowDeriv u p 0 0 - invPowDeriv u p 0 (N : ℝ)))
      atTop (𝓝 ((1 / 2 : ℝ) * invPowDeriv u p 0 0)) := by
    have ht := tendsto_invPowDeriv_atTop hu_pos hp1 0
    simpa using (tendsto_const_nhds.sub ht).const_mul (1 / 2 : ℝ)
  have h_lim_sum : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Ico 1 (K + 1),
        (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
          (invPowDeriv u p k 0 - invPowDeriv u p k (N : ℝ)))
      atTop
      (𝓝 (∑ k ∈ Finset.Ico 1 (K + 1),
        (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) * invPowDeriv u p k 0)) := by
    induction (Finset.Ico 1 (K + 1)) using Finset.induction with
    | empty => simp
    | @insert k s hks ihs =>
      simp only [Finset.sum_insert hks]
      have hk_lim : Tendsto (fun N : ℕ =>
          (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
            (invPowDeriv u p k 0 - invPowDeriv u p k (N : ℝ)))
          atTop
          (𝓝 ((-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) * invPowDeriv u p k 0)) := by
        simpa using (tendsto_const_nhds.sub (tendsto_invPowDeriv_atTop hu_pos hp1 k)).const_mul _
      exact hk_lim.add ihs
  obtain ⟨_, _, hrem_summ, _⟩ := eulerMaclaurin_remainder_bound hu hp K
  let gRem : ℕ → ℝ := fun n =>
    ∫ t in (0 : ℝ)..1, (bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
      invPowDeriv u p (K + 1) ((n : ℝ) + t)
  have h_lim_rem : Tendsto (fun N : ℕ => (-1 : ℝ) ^ K * ∑ n ∈ Finset.range N, gRem n)
      atTop (𝓝 ((-1 : ℝ) ^ K * ∑' n : ℕ, gRem n)) :=
    (hrem_summ.hasSum.tendsto_sum_nat).const_mul _
  have h_lim_R := ((h_lim_int.add h_lim_0).add h_lim_sum).add h_lim_rem
  have h_fin : ∀ N : ℕ, (∑ n ∈ Finset.range N, (u + (n : ℝ))⁻¹ ^ p) =
      (∫ x in (0 : ℝ)..(N : ℝ), (u + x)⁻¹ ^ p) +
        (1 / 2 : ℝ) * (invPowDeriv u p 0 0 - invPowDeriv u p 0 (N : ℝ)) +
        ∑ k ∈ Finset.Ico 1 (K + 1),
          (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
            (invPowDeriv u p k 0 - invPowDeriv u p k (N : ℝ)) +
        (-1 : ℝ) ^ K * ∑ n ∈ Finset.range N, gRem n :=
    fun N => eulerMaclaurin_finite hu_pos hp N K
  have h_eq : ∑' n : ℕ, (u + (n : ℝ))⁻¹ ^ p =
      (p - 1 : ℝ)⁻¹ * u⁻¹ ^ (p - 1) +
        (1 / 2 : ℝ) * invPowDeriv u p 0 0 +
        ∑ k ∈ Finset.Ico 1 (K + 1),
          (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) * invPowDeriv u p k 0 +
        (-1 : ℝ) ^ K * ∑' n : ℕ, gRem n :=
    tendsto_nhds_unique (h_lim_L.congr fun N => h_fin N) h_lim_R
  have h0_eq : invPowDeriv u p 0 0 = u⁻¹ ^ p := by
    simp [invPowDeriv, div_self (by positivity : ((p - 1).factorial : ℝ) ≠ 0)]
  have hk_eq : ∀ k : ℕ, invPowDeriv u p k 0 =
      (-1 : ℝ) ^ k * (((p + k - 1).factorial : ℝ) / ((p - 1).factorial : ℝ)) * u⁻¹ ^ (p + k) := by
    intro k; simp [invPowDeriv]
  rw [h_eq, h0_eq]
  simp_rw [hk_eq]
  have hsub_eq : ((p - 1 : ℝ)⁻¹ * u⁻¹ ^ (p - 1) + (1 / 2 : ℝ) * u⁻¹ ^ p +
        ∑ k ∈ Finset.Ico 1 (K + 1),
          (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
            ((-1 : ℝ) ^ k * (((p + k - 1).factorial : ℝ) / ((p - 1).factorial : ℝ)) * u⁻¹ ^ (p + k)) +
        (-1 : ℝ) ^ K * ∑' n : ℕ, gRem n) -
      ((p - 1 : ℝ)⁻¹ * u⁻¹ ^ (p - 1) + (1 / 2 : ℝ) * u⁻¹ ^ p +
        ∑ k ∈ Finset.Ico 1 (K + 1),
          (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
            ((-1 : ℝ) ^ k * (((p + k - 1).factorial : ℝ) / ((p - 1).factorial : ℝ)) * u⁻¹ ^ (p + k))) =
      (-1 : ℝ) ^ K * ∑' n : ℕ, gRem n := by ring
  rw [hsub_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hbound_n : ∀ n : ℕ, ‖gRem n‖ ≤ (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hle_t : ∀ t ∈ uIoc (0 : ℝ) 1,
        ‖(bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)) *
          invPowDeriv u p (K + 1) ((n : ℝ) + t)‖ ≤
          (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have hpos_unt : 0 < u + ((n : ℝ) + t) := by linarith [ht.1]
      have hbt : |bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)| ≤ MB' := by
        have hb0 := hMB t ⟨ht.1.le, ht.2⟩
        rw [Real.norm_of_nonneg (abs_nonneg _)] at hb0
        exact hb0.trans (le_max_left _ _)
      have hnt_ge : (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)) ≤
          (1 / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        have hpow_ge : u ^ K * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (u + ((n : ℝ) + t)) ^ (p + (K + 1)) := by
          have h1 : u ^ K ≤ (u + ((n : ℝ) + t)) ^ K := pow_le_pow_left₀ hu_pos.le (by linarith [ht.1]) K
          have h2 : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (u + ((n : ℝ) + t)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by push_cast; linarith [ht.1]) 2
          have h3 : (u + ((n : ℝ) + t)) ^ (K + 2) ≤ (u + ((n : ℝ) + t)) ^ (p + (K + 1)) :=
            pow_le_pow_right₀ (by linarith [ht.1]) (by omega)
          calc u ^ K * ((n + 1 : ℕ) : ℝ) ^ 2
              ≤ (u + ((n : ℝ) + t)) ^ K * (u + ((n : ℝ) + t)) ^ 2 :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = (u + ((n : ℝ) + t)) ^ (K + 2) := by rw [pow_add]
            _ ≤ (u + ((n : ℝ) + t)) ^ (p + (K + 1)) := h3
        rw [inv_pow, ← one_div, one_div_mul_one_div]
        exact one_div_le_one_div_of_le (by positivity) hpow_ge
      rw [Real.norm_eq_abs, abs_mul]
      have hinv_abs : |invPowDeriv u p (K + 1) ((n : ℝ) + t)| =
          coeffP * (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)) := by
        dsimp only [invPowDeriv, coeffP]
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hpos_unt.le) _),
          show p + (K + 1) - 1 = p + K by omega]
      rw [hinv_abs]
      have hnonneg_c : 0 ≤ coeffP * (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)) :=
        mul_nonneg hcoeffP (pow_nonneg (inv_nonneg.mpr hpos_unt.le) _)
      calc |bernoulliFun (K + 1) t / ((K + 1).factorial : ℝ)| *
            (coeffP * (u + ((n : ℝ) + t))⁻¹ ^ (p + (K + 1)))
          ≤ MB' * (coeffP * ((1 / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2))) :=
            mul_le_mul hbt (mul_le_mul_of_nonneg_left hnt_ge hcoeffP) hnonneg_c hMB'
        _ = (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
    simpa [gRem] using intervalIntegral.norm_integral_le_of_norm_le_const hle_t
  have hdom : Summable (fun n : ℕ => (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    hzeta2.mul_left _
  rw [← Real.norm_eq_abs]
  calc ‖∑' n : ℕ, gRem n‖ ≤ ∑' n : ℕ, ‖gRem n‖ := norm_tsum_le_tsum_norm hrem_summ.norm
    _ ≤ ∑' n : ℕ, (MB' * coeffP / u ^ K) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
        hrem_summ.norm.tsum_le_tsum hbound_n hdom
    _ = (MB' * coeffP * ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2) / u ^ K := by
        rw [tsum_mul_left]; ring

private lemma coeff_d_u_iter (S : PowerSeries ℂ) (hS0 : PowerSeries.coeff 0 S = 0) :
    ∀ (j m : ℕ), PowerSeries.coeff m (d_u^[j] S) =
      if m ≤ j then 0 else
        (-1 : ℂ) ^ j * (((m - 1).factorial : ℂ) / ((m - j - 1).factorial : ℂ)) *
          PowerSeries.coeff (m - j) S := by
  intro j
  induction j with
  | zero =>
    intro m
    simp only [Function.iterate_zero, id_eq, Nat.le_zero, pow_zero, one_mul, tsub_zero]
    cases m with
    | zero => simp [hS0]
    | succ m =>
      have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      simp [div_self hfac]
  | succ j ih =>
    intro m
    rw [Function.iterate_succ_apply', d_u, map_neg]
    rcases m with _ | _ | m
    · simp [PowerSeries.coeff_X_pow_mul']
    · have h0 : PowerSeries.coeff 1 (PowerSeries.X ^ 2 * PowerSeries.derivative (d_u^[j] S)) = 0 := by
        rw [PowerSeries.coeff_X_pow_mul']
        simp
      rw [h0, neg_zero]
      simp only [show 1 ≤ j + 1 by omega, ↓reduceIte]
    · have hX2 : PowerSeries.coeff (m + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative (d_u^[j] S)) =
          PowerSeries.coeff m (PowerSeries.derivative (d_u^[j] S)) := by
        rw [PowerSeries.coeff_X_pow_mul']
        simp
      rw [hX2, PowerSeries.coeff_derivative, ih (m + 1)]
      by_cases hm : m + 1 ≤ j
      · simp [hm, show m + 2 ≤ j + 1 by omega]
      · simp only [hm, ↓reduceIte, show ¬ (m + 2 ≤ j + 1) by omega]
        push Not at hm
        rw [show m + 1 - 1 = m by omega, show m + 1 + 1 - 1 = m + 1 by omega,
          pow_succ, Nat.factorial_succ m]
        push_cast
        ring

private lemma d_u_add (A B : PowerSeries ℂ) : d_u (A + B) = d_u A + d_u B := by
  ext n; simp [d_u, map_add, mul_add]; ring

private lemma d_u_iter_add (j : ℕ) (A B : PowerSeries ℂ) :
    d_u^[j] (A + B) = d_u^[j] A + d_u^[j] B := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, d_u_add]

private lemma d_u_sub (A B : PowerSeries ℂ) : d_u (A - B) = d_u A - d_u B := by
  ext n; simp [d_u, map_sub, mul_sub]; ring

private lemma d_u_iter_sub (j : ℕ) (A B : PowerSeries ℂ) :
    d_u^[j] (A - B) = d_u^[j] A - d_u^[j] B := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, d_u_sub]

/-- Formal asymptotic power series of `ψ'(u)` in `w = 1/u`:
`1/u + 1/(2u²) + ∑_{k ≥ 1} B_{2k} / u^{2k+1}`. -/
@[expose] def trigammaSeriesAsymp : PowerSeries ℂ :=
  PowerSeries.X + (2⁻¹ : ℂ) • PowerSeries.X ^ 2 + formalSeries phiBern

/-- Remainder of trigamma after subtracting the first two asymptotic terms:
`ψ'(u) - 1/u - 1/(2u²)`. -/
@[expose] def trigammaRem (u : ℝ) : ℂ :=
  trigamma (u : ℂ) - (u : ℂ)⁻¹ - (2 : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ 2

private lemma coeff_trigammaSeriesAsymp (m : ℕ) :
    PowerSeries.coeff m trigammaSeriesAsymp =
      if m = 0 then 0 else if m = 1 then 1 else if m = 2 then (2⁻¹ : ℂ) else
        (bernoulli (m - 1) : ℂ) := by
  have hX2 : (PowerSeries.X ^ 2 : PowerSeries ℂ).coeff m = if m = 2 then 1 else 0 := by
    rw [PowerSeries.coeff_X_pow]
  rw [trigammaSeriesAsymp, map_add, map_add, PowerSeries.coeff_X, PowerSeries.coeff_smul, hX2,
    coeff_formalSeries_phiBern]
  rcases m with _ | _ | _ | m
  · simp
  · simp
  · simp
  · simp [show ¬(m + 3 ≤ 2) by omega]

private lemma coeff_trigammaSeriesAsymp_zero : PowerSeries.coeff 0 trigammaSeriesAsymp = 0 := by
  simp [coeff_trigammaSeriesAsymp]

private lemma hasAsympExp_sub {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hg : HasAsympExp g T) :
    HasAsympExp (fun u => f u - g u) (S - T) := by
  intro M
  obtain ⟨Cf, hCf⟩ := hf M
  obtain ⟨Cg, hCg⟩ := hg M
  refine ⟨Cf + Cg, ?_⟩
  filter_upwards [hCf, hCg] with u hfu hgu
  have hsum : ∑ k ∈ Finset.range M, PowerSeries.coeff k (S - T) * ((u : ℂ)⁻¹ ^ k) =
      (∑ k ∈ Finset.range M, PowerSeries.coeff k S * ((u : ℂ)⁻¹ ^ k)) -
        ∑ k ∈ Finset.range M, PowerSeries.coeff k T * ((u : ℂ)⁻¹ ^ k) := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  calc ‖f u - g u - (_ - _)‖
      = ‖(f u - _) - (g u - _)‖ := by congr 1; ring
    _ ≤ ‖f u - _‖ + ‖g u - _‖ := norm_sub_le _ _
    _ ≤ Cf / u ^ M + Cg / u ^ M := add_le_add hfu hgu
    _ = (Cf + Cg) / u ^ M := by ring

private lemma hasAsympExp_of_eventuallyEq_monomial {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (k : ℕ) (c : ℂ)
    (hS : ∀ m : ℕ, PowerSeries.coeff m S = if m = k then c else 0)
    (hf : ∀ᶠ u : ℝ in atTop, f u = c * (u : ℂ)⁻¹ ^ k) :
    HasAsympExp f S := by
  intro M
  by_cases hk : k < M
  · refine ⟨0, ?_⟩
    filter_upwards [hf] with u hfu
    have hsum : ∑ m ∈ Finset.range M, PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m = c * (u : ℂ)⁻¹ ^ k := by
      simp_rw [hS, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_range.mpr hk]
    rw [hfu, hsum, sub_self, norm_zero, zero_div]
  · push Not at hk
    refine ⟨‖c‖, ?_⟩
    filter_upwards [hf, eventually_ge_atTop (1 : ℝ)] with u hfu hu
    have hsum : ∑ m ∈ Finset.range M, PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [hS m, ite_eq_right_iff.mpr (by have := Finset.mem_range.mp hm; omega), zero_mul]
    rw [hfu, hsum, sub_zero, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    have hle : (u⁻¹) ^ k ≤ (u⁻¹) ^ M := by
      have huinv0 : 0 ≤ u⁻¹ := by positivity
      have huinv1 : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu
      rw [show k = M + (k - M) by omega, pow_add]
      exact mul_le_of_le_one_right (pow_nonneg huinv0 M) (pow_le_one₀ huinv0 huinv1)
    calc ‖c‖ * (u⁻¹) ^ k ≤ ‖c‖ * (u⁻¹) ^ M := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ‖c‖ / u ^ M := by rw [inv_pow, div_eq_mul_inv]

private lemma iteratedDeriv_inv_of_pos (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹) u =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 1) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    have hev : iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹) =ᶠ[𝓝 u]
        fun x : ℝ => (-1 : ℂ) ^ j * (j.factorial : ℂ) * (x : ℂ)⁻¹ ^ (j + 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
      exact ih hx
    have hne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hinv : HasDerivAt (fun x : ℝ => (x : ℂ)⁻¹) (-((u : ℂ) ^ 2)⁻¹) u := by
      simpa using (hasDerivAt_inv hne).comp_ofReal
    have hpow := (hinv.pow (j + 1)).const_mul ((-1 : ℂ) ^ j * (j.factorial : ℂ))
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hderiv_eq : deriv (fun x : ℝ => (-1 : ℂ) ^ j * (j.factorial : ℂ) * (x : ℂ)⁻¹ ^ (j + 1)) u =
        (-1 : ℂ) ^ j * (j.factorial : ℂ) * (↑(j + 1) * (u : ℂ)⁻¹ ^ (j + 1 - 1) * -((u : ℂ) ^ 2)⁻¹) :=
      hpow.deriv
    rw [hderiv_eq]
    have hpow_eq : ((u : ℂ)⁻¹ ^ (j + 1 - 1) * -((u : ℂ) ^ 2)⁻¹) = -((u : ℂ)⁻¹ ^ (j + 1 + 1)) := by
      rw [mul_neg, Nat.add_sub_cancel, ← inv_pow, ← pow_add]
    calc (-1 : ℂ) ^ j * (j.factorial : ℂ) * (↑(j + 1) * (u : ℂ)⁻¹ ^ (j + 1 - 1) * -((u : ℂ) ^ 2)⁻¹)
        = (-1 : ℂ) ^ j * (j.factorial : ℂ) * ↑(j + 1) * ((u : ℂ)⁻¹ ^ (j + 1 - 1) * -((u : ℂ) ^ 2)⁻¹) := by ring
      _ = (-1 : ℂ) ^ (j + 1) * ((j + 1).factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 1 + 1) := by
          rw [hpow_eq, pow_succ, Nat.factorial_succ]; push_cast; ring

private lemma iteratedDeriv_inv_sq_of_pos (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹ ^ 2) u =
      (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 2) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    have hev : iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹ ^ 2) =ᶠ[𝓝 u]
        fun x : ℝ => (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (x : ℂ)⁻¹ ^ (j + 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
      exact ih hx
    have hne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hinv : HasDerivAt (fun x : ℝ => (x : ℂ)⁻¹) (-((u : ℂ) ^ 2)⁻¹) u := by
      simpa using (hasDerivAt_inv hne).comp_ofReal
    have hpow := (hinv.pow (j + 2)).const_mul ((-1 : ℂ) ^ j * ((j + 1).factorial : ℂ))
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hderiv_eq : deriv (fun x : ℝ => (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (x : ℂ)⁻¹ ^ (j + 2)) u =
        (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (↑(j + 2) * (u : ℂ)⁻¹ ^ (j + 2 - 1) * -((u : ℂ) ^ 2)⁻¹) :=
      hpow.deriv
    rw [hderiv_eq]
    have hpow_eq : ((u : ℂ)⁻¹ ^ (j + 2 - 1) * -((u : ℂ) ^ 2)⁻¹) = -((u : ℂ)⁻¹ ^ (j + 2 + 1)) := by
      have hsub : j + 2 - 1 + 2 = j + 2 + 1 := by omega
      rw [mul_neg, ← inv_pow, ← pow_add, hsub]
    calc (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (↑(j + 2) * (u : ℂ)⁻¹ ^ (j + 2 - 1) * -((u : ℂ) ^ 2)⁻¹)
        = (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * ↑(j + 2) * ((u : ℂ)⁻¹ ^ (j + 2 - 1) * -((u : ℂ) ^ 2)⁻¹) := by ring
      _ = (-1 : ℂ) ^ (j + 1) * ((j + 1 + 1).factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 1 + 2) := by
          rw [hpow_eq, pow_succ, Nat.factorial_succ (j + 1)]; push_cast; ring

private lemma trigammaSeriesAsymp_hasAsympExp (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)))
      (d_u^[j] trigammaSeriesAsymp) := by
  intro M
  obtain ⟨C₀, hEM⟩ := eulerMaclaurin_asymp_real (j + 2) M (by omega)
  let S := d_u^[j] trigammaSeriesAsymp
  let B_extra : ℝ := ∑ m ∈ Finset.Ico M (j + M + 3), ‖PowerSeries.coeff m S‖
  let K_fac : ℝ := ((j + 1).factorial : ℝ)
  refine ⟨K_fac * max C₀ 0 + B_extra, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hderiv_eq : iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) u =
      (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
        ((∑' n : ℕ, (u + (n : ℝ))⁻¹ ^ (j + 2) : ℝ) : ℂ) := by
    rw [iteratedDeriv_trigamma_of_pos j hu_pos]
    congr 1
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast; simp [one_div]
  have hpoly_match :
      (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
        ((((((j + 2 : ℕ) : ℝ) - 1)⁻¹ * u⁻¹ ^ (j + 2 - 1) +
          (1 / 2 : ℝ) * u⁻¹ ^ (j + 2) +
          ∑ k ∈ Finset.Ico 1 (M + 1),
            (-1 : ℝ) ^ k * ((bernoulli (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) *
              ((-1 : ℝ) ^ k * (((j + 2 + k - 1).factorial : ℝ) / ((j + 2 - 1).factorial : ℝ)) *
                u⁻¹ ^ (j + 2 + k))) : ℝ) : ℂ) =
      ∑ m ∈ Finset.range (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m := by
    have hS_coeff : ∀ m : ℕ, PowerSeries.coeff m S =
        if m ≤ j then 0 else
          (-1 : ℂ) ^ j * (((m - 1).factorial : ℂ) / ((m - j - 1).factorial : ℂ)) *
            PowerSeries.coeff (m - j) trigammaSeriesAsymp :=
      coeff_d_u_iter trigammaSeriesAsymp coeff_trigammaSeriesAsymp_zero j
    have h_range_split :
        (∑ m ∈ Finset.range (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m) =
        ∑ m ∈ Finset.Ico (j + 1) (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m := by
      have hsub_range : Finset.range (j + M + 3) = Finset.range (j + 1) ∪ Finset.Ico (j + 1) (j + M + 3) := by
        ext m; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      rw [hsub_range, Finset.sum_union (Finset.disjoint_iff_ne.mpr fun a ha b hb _ => by
        simp only [Finset.mem_range, Finset.mem_Ico] at ha hb; omega)]
      have hzero : ∑ m ∈ Finset.range (j + 1), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [hS_coeff m]
        simp only [show m ≤ j from Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), ↓reduceIte, zero_mul]
      rw [hzero, zero_add]
    rw [h_range_split]
    have h_shift : ∑ m ∈ Finset.Ico (j + 1) (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m =
        ∑ t ∈ Finset.range (M + 2), PowerSeries.coeff (j + 1 + t) S * (u : ℂ)⁻¹ ^ (j + 1 + t) := by
      refine Finset.sum_bij (fun m _ => m - (j + 1)) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
      · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
      · intro t ht; simp only [Finset.mem_range] at ht
        exact ⟨j + 1 + t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro m hm; simp only [Finset.mem_Ico] at hm
        rw [show j + 1 + (m - (j + 1)) = m by omega]
    rw [h_shift, Finset.sum_range_succ', Finset.sum_range_succ']
    have ht0 : PowerSeries.coeff (j + 1 + 0) S = (-1 : ℂ) ^ j * (j.factorial : ℂ) := by
      rw [hS_coeff]
      simp only [show ¬ (j + 1 + 0 ≤ j) by omega, ↓reduceIte, Nat.add_zero, Nat.add_sub_cancel,
        Nat.add_sub_cancel_left, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one,
        coeff_trigammaSeriesAsymp, one_ne_zero, mul_one]
    have ht1 : PowerSeries.coeff (j + 1 + (0 + 1)) S =
        (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (2⁻¹ : ℂ) := by
      rw [hS_coeff]
      simp only [show ¬ (j + 1 + (0 + 1) ≤ j) by omega, ↓reduceIte]
      rw [show j + 1 + (0 + 1) - 1 = j + 1 by omega,
        show j + 1 + (0 + 1) - j = 2 by omega,
        show 2 - 1 = 1 by omega,
        coeff_trigammaSeriesAsymp]
      simp
    have htail : (∑ k ∈ Finset.range M,
          PowerSeries.coeff (j + 1 + (k + 1 + 1)) S * (u : ℂ)⁻¹ ^ (j + 1 + (k + 1 + 1))) =
        ∑ k ∈ Finset.Ico 1 (M + 1),
          (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
            ((-1 : ℂ) ^ k * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
              ((-1 : ℂ) ^ k * (((j + 2 + k - 1).factorial : ℂ) / ((j + 2 - 1).factorial : ℂ)) *
                (u : ℂ)⁻¹ ^ (j + 2 + k))) := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_range, Finset.mem_Ico] at hk ⊢; omega
      · intro a _ b _ hab; omega
      · intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
        exact ⟨k - 1, by omega, by omega⟩
      · intro k _
        rw [hS_coeff]
        simp only [show ¬ (j + 1 + (k + 1 + 1) ≤ j) by omega, ↓reduceIte]
        rw [show j + 1 + (k + 1 + 1) - 1 = j + k + 2 by omega,
          show j + 1 + (k + 1 + 1) - j = k + 3 by omega,
          show k + 3 - 1 = k + 2 by omega,
          coeff_trigammaSeriesAsymp]
        simp only [show k + 3 ≠ 0 by omega, ↓reduceIte, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega]
        rw [show k + 3 - 1 = k + 2 by omega, show j + 1 + (k + 1 + 1) = j + 2 + (k + 1) by omega,
          show j + 2 + (k + 1) - 1 = j + k + 2 by omega, show j + 2 - 1 = j + 1 by omega,
          show k + 1 + 1 = k + 2 by omega]
        have hsign : (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ (k + 1) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        have hfac1 : ((j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        have hfac2 : ((k + 2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        have hsign' : ((-1 : ℂ) ^ (k + 1)) ^ 2 = 1 := by linear_combination hsign
        field_simp [hfac1, hfac2]
        rw [hsign']
        ring
    rw [ht0, ht1, htail]
    have hj1_ne : ((j : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    have hfac_succ : ((j + 1).factorial : ℂ) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hpow_1 : j + 1 + 0 = j + 1 := by ring
    have hpow_2 : j + 1 + (0 + 1) = j + 2 := by ring
    have hsub_1 : j + 2 - 1 = j + 1 := by omega
    rw [hpow_1, hpow_2, hsub_1]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_div,
      Complex.ofReal_neg, Complex.ofReal_ratCast, Complex.ofReal_natCast, Complex.ofReal_sub,
      one_div]
    have hterm1 : (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
        ((((j + 2 : ℕ) : ℂ) - 1)⁻¹ * (u : ℂ)⁻¹ ^ (j + 1)) =
        (-1 : ℂ) ^ j * (j.factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 1) := by
      rw [show ((j + 2 : ℕ) : ℂ) - 1 = (j : ℂ) + 1 by push_cast; ring, hfac_succ]
      field_simp [hj1_ne]
    calc (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
          ((((j + 2 : ℕ) : ℂ) - 1)⁻¹ * (u : ℂ)⁻¹ ^ (j + 1) + 2⁻¹ * (u : ℂ)⁻¹ ^ (j + 2) +
            ∑ x ∈ Finset.Ico 1 (M + 1),
              (-1 : ℂ) ^ x * (↑(bernoulli (x + 1)) / ((x + 1).factorial : ℂ)) *
                ((-1 : ℂ) ^ x * (((j + 2 + x - 1).factorial : ℂ) / ((j + 1).factorial : ℂ)) *
                  (u : ℂ)⁻¹ ^ (j + 2 + x)))
        = (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * ((((j + 2 : ℕ) : ℂ) - 1)⁻¹ * (u : ℂ)⁻¹ ^ (j + 1)) +
          (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (2⁻¹ * (u : ℂ)⁻¹ ^ (j + 2)) +
          (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
            ∑ x ∈ Finset.Ico 1 (M + 1),
              (-1 : ℂ) ^ x * (↑(bernoulli (x + 1)) / ((x + 1).factorial : ℂ)) *
                ((-1 : ℂ) ^ x * (((j + 2 + x - 1).factorial : ℂ) / ((j + 1).factorial : ℂ)) *
                  (u : ℂ)⁻¹ ^ (j + 2 + x)) := by ring
      _ = (-1 : ℂ) ^ j * (j.factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 1) +
          (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (2⁻¹ * (u : ℂ)⁻¹ ^ (j + 2)) +
          ∑ x ∈ Finset.Ico 1 (M + 1),
            (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
              ((-1 : ℂ) ^ x * (↑(bernoulli (x + 1)) / ((x + 1).factorial : ℂ)) *
                ((-1 : ℂ) ^ x * (((j + 2 + x - 1).factorial : ℂ) / ((j + 1).factorial : ℂ)) *
                  (u : ℂ)⁻¹ ^ (j + 2 + x))) := by
            rw [hterm1, Finset.mul_sum]
      _ = _ := by ring
  have hEM_bound : ‖iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) u -
      ∑ m ∈ Finset.range (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m‖ ≤
      K_fac * max C₀ 0 / u ^ M := by
    rw [hderiv_eq, ← hpoly_match, ← mul_sub, ← Complex.ofReal_sub, norm_mul, norm_mul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs]
    have hEMu := (hEM hu).trans (div_le_div_of_nonneg_right (le_max_left C₀ 0) (by positivity))
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.add_sub_cancel] using
      calc K_fac * |_| ≤ K_fac * (max C₀ 0 / u ^ M) := mul_le_mul_of_nonneg_left hEMu (by positivity)
        _ = K_fac * max C₀ 0 / u ^ M := by ring
  have h_split_M :
      (∑ m ∈ Finset.range (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m) -
      (∑ m ∈ Finset.range M, PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m) =
      ∑ m ∈ Finset.Ico M (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m := by
    have huni : Finset.range (j + M + 3) = Finset.range M ∪ Finset.Ico M (j + M + 3) := by
      ext m; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    rw [huni, Finset.sum_union (Finset.disjoint_iff_ne.mpr fun a ha b hb _ => by
      simp only [Finset.mem_range, Finset.mem_Ico] at ha hb; omega)]
    ring
  have h_extra_bound :
      ‖∑ m ∈ Finset.Ico M (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m‖ ≤ B_extra / u ^ M := by
    refine (norm_sum_le _ _).trans ?_
    dsimp only [B_extra]
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm_ge : M ≤ m := (Finset.mem_Ico.mp hm).1
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
    have hpow : (u⁻¹) ^ m ≤ (u⁻¹) ^ M := by
      have huinv0 : 0 ≤ u⁻¹ := by positivity
      have huinv1 : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu
      rw [show m = M + (m - M) by omega, pow_add]
      exact mul_le_of_le_one_right (pow_nonneg huinv0 M) (pow_le_one₀ huinv0 huinv1)
    calc ‖PowerSeries.coeff m S‖ * (u⁻¹) ^ m ≤ ‖PowerSeries.coeff m S‖ * (u⁻¹) ^ M :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = ‖PowerSeries.coeff m S‖ / u ^ M := by rw [inv_pow, div_eq_mul_inv]
  calc ‖iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) u -
        ∑ m ∈ Finset.range M, PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m‖
      = ‖(iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) u -
          ∑ m ∈ Finset.range (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m) +
          ((∑ m ∈ Finset.range (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m) -
          ∑ m ∈ Finset.range M, PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m)‖ := by congr 1; ring
    _ ≤ ‖iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) u -
          ∑ m ∈ Finset.range (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m‖ +
        ‖∑ m ∈ Finset.Ico M (j + M + 3), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m‖ := by
        rw [← h_split_M]; exact norm_add_le _ _
    _ ≤ K_fac * max C₀ 0 / u ^ M + B_extra / u ^ M := add_le_add hEM_bound h_extra_bound
    _ = (K_fac * max C₀ 0 + B_extra) / u ^ M := by ring

private lemma iteratedDeriv_trigammaRem_of_pos (j : ℕ) {u : ℝ} (hu_pos : 0 < u) :
    iteratedDeriv j trigammaRem u =
      iteratedDeriv j (fun x : ℝ => trigamma (x : ℂ)) u -
        (iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹) u +
          iteratedDeriv j (fun x : ℝ => (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) u) := by
  have hev_rem : trigammaRem =ᶠ[𝓝 u]
      ((fun x : ℝ => trigamma (x : ℂ)) -
        fun x : ℝ => (x : ℂ)⁻¹ + (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) := by
    refine Eventually.of_forall fun x => ?_
    change trigamma (x : ℂ) - (x : ℂ)⁻¹ - (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2 =
      trigamma (x : ℂ) - ((x : ℂ)⁻¹ + (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2)
    ring
  have hcd_tri : ContDiffAt ℝ j (fun x : ℝ => trigamma (x : ℂ)) u := by
    have hana : AnalyticAt ℝ (fun x : ℝ => trigamma (x : ℂ)) u :=
      ((trigamma_analyticOnNhd_re_pos (u : ℂ) (by simpa using hu_pos)).restrictScalars (𝕜 := ℝ)).comp
        (Complex.ofRealCLM.analyticAt u)
    exact hana.contDiffAt.of_le le_top
  have hcd_1 : ContDiffAt ℝ j (fun x : ℝ => (x : ℂ)⁻¹) u :=
    ((Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr hu_pos.ne')).contDiffAt.of_le le_top
  have hcd_2 : ContDiffAt ℝ j (fun x : ℝ => (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) u :=
    (analyticAt_const.mul (((Complex.ofRealCLM.analyticAt u).inv
      (Complex.ofReal_ne_zero.mpr hu_pos.ne')).pow 2)).contDiffAt.of_le le_top
  have hadd_eq : iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹ + (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) u =
      iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹) u +
        iteratedDeriv j (fun x : ℝ => (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) u :=
    iteratedDeriv_add hcd_1 hcd_2
  rw [hev_rem.iteratedDeriv_eq j, iteratedDeriv_sub hcd_tri (hcd_1.add hcd_2), hadd_eq]

private lemma trigammaRem_hasAsympExp (j : ℕ) :
    HasAsympExp (iteratedDeriv j trigammaRem) (d_u^[j] (formalSeries phiBern)) := by
  have h1 : HasAsympExp (iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹)) (d_u^[j] (PowerSeries.X : PowerSeries ℂ)) := by
    refine hasAsympExp_of_eventuallyEq_monomial (j + 1) ((-1 : ℂ) ^ j * (j.factorial : ℂ)) ?_ ?_
    · intro m
      rw [coeff_d_u_iter _ (by simp) j m]
      by_cases hm : m = j + 1
      · subst hm
        simp only [show ¬ (j + 1 ≤ j) by omega, ↓reduceIte,
          show j + 1 - 1 = j by omega, show j + 1 - j = 1 by omega,
          show 1 - 1 = 0 by omega]
        simp
      · by_cases hle : m ≤ j
        · simp only [hle, ↓reduceIte, hm]
        · simp only [hle, ↓reduceIte, hm]
          have hne1 : m - j ≠ 1 := by omega
          simp [PowerSeries.coeff_X, hne1]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      exact iteratedDeriv_inv_of_pos j hu
  have h2 : HasAsympExp (iteratedDeriv j (fun x : ℝ => (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2))
      (d_u^[j] ((2⁻¹ : ℂ) • (PowerSeries.X ^ 2 : PowerSeries ℂ))) := by
    refine hasAsympExp_of_eventuallyEq_monomial (j + 2)
        ((2 : ℂ)⁻¹ * (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ)) ?_ ?_
    · intro m
      rw [coeff_d_u_iter _ (by simp) j m]
      by_cases hm : m = j + 2
      · subst hm
        simp only [show ¬ (j + 2 ≤ j) by omega, ↓reduceIte,
          show j + 2 - 1 = j + 1 by omega, show j + 2 - j = 2 by omega,
          show 2 - 1 = 1 by omega, Nat.factorial_one, Nat.cast_one, div_one,
          PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
        simp [smul_eq_mul]; ring
      · by_cases hle : m ≤ j
        · simp only [hle, ↓reduceIte, hm]
        · simp only [hle, ↓reduceIte, hm]
          have hne2 : m - j ≠ 2 := by omega
          simp [PowerSeries.coeff_X_pow, hne2]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hcd : ContDiffAt ℝ j (fun x : ℝ => (x : ℂ)⁻¹ ^ 2) u := by
        have hana : AnalyticAt ℝ (fun x : ℝ => (x : ℂ)⁻¹ ^ 2) u :=
          ((Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr hu.ne')).pow 2
        exact hana.contDiffAt.of_le le_top
      have hcmul : iteratedDeriv j (fun x : ℝ => (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) u =
          (2 : ℂ)⁻¹ * iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹ ^ 2) u :=
        iteratedDeriv_const_mul (2 : ℂ)⁻¹ hcd
      rw [hcmul, iteratedDeriv_inv_sq_of_pos j hu]
      ring
  have h12 : HasAsympExp
      (fun u : ℝ => iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹) u +
        iteratedDeriv j (fun x : ℝ => (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) u)
      (d_u^[j] (PowerSeries.X + (2⁻¹ : ℂ) • PowerSeries.X ^ 2)) := by
    rw [d_u_iter_add]
    exact h1.add h2
  have hsub := hasAsympExp_sub (trigammaSeriesAsymp_hasAsympExp j) h12
  have hS_eq : d_u^[j] trigammaSeriesAsymp - d_u^[j] (PowerSeries.X + (2⁻¹ : ℂ) • PowerSeries.X ^ 2) =
      d_u^[j] (formalSeries phiBern) := by
    rw [← d_u_iter_sub, trigammaSeriesAsymp]
    congr 1; ring
  rw [hS_eq] at hsub
  refine fun M => ?_
  obtain ⟨C, hC⟩ := hsub M
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hCu hu_pos
  rw [← iteratedDeriv_trigammaRem_of_pos j hu_pos] at hCu
  exact hCu

/-- **Differential Transcendence of `trigammaRem` over `ℂ(u)`**. -/
theorem trigammaRem_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val trigammaRem u)
        (evalRatU P (u : ℂ)) = 0) :
    P = 0 :=
  no_rat_ade_of_higher_order_borel phiBern_borelData trigammaRem_hasAsympExp P hP

private noncomputable def shiftRatFunc (j : ℕ) : RatFunc ℂ :=
  RatFunc.C ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (RatFunc.X : RatFunc ℂ)⁻¹ ^ (j + 1) +
  RatFunc.C ((2 : ℂ)⁻¹ * (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ)) * (RatFunc.X : RatFunc ℂ)⁻¹ ^ (j + 2)

private lemma ratEval_eq_ratFunc_eval (q : RatFunc ℂ) (u : ℂ) :
    ratEval q u = RatFunc.eval (RingHom.id ℂ) u q := by
  simp [ratEval, RatFunc.eval, Polynomial.eval₂_id]

private lemma ratEval_add (p q : RatFunc ℂ) (u : ℂ)
    (hp : p.denom.eval u ≠ 0) (hq : q.denom.eval u ≠ 0) :
    ratEval (p + q) u = ratEval p u + ratEval q u := by
  simp only [ratEval_eq_ratFunc_eval]
  exact RatFunc.eval_add (RingHom.id ℂ) u
    (by simpa only [Polynomial.eval₂_id] using hp)
    (by simpa only [Polynomial.eval₂_id] using hq)

private lemma ratEval_mul (p q : RatFunc ℂ) (u : ℂ)
    (hp : p.denom.eval u ≠ 0) (hq : q.denom.eval u ≠ 0) :
    ratEval (p * q) u = ratEval p u * ratEval q u := by
  simp only [ratEval_eq_ratFunc_eval]
  exact RatFunc.eval_mul (RingHom.id ℂ) u
    (by simpa only [Polynomial.eval₂_id] using hp)
    (by simpa only [Polynomial.eval₂_id] using hq)

private def regularAt (u : ℂ) : Subring (RatFunc ℂ) where
  carrier := {q : RatFunc ℂ | q.denom.eval u ≠ 0}
  mul_mem' {p q} hp hq := by
    change (p * q).denom.eval u ≠ 0
    intro h0
    obtain ⟨r, hr⟩ := RatFunc.denom_mul_dvd p q
    have hmul : (p.denom * q.denom).eval u = 0 := by
      rw [hr, Polynomial.eval_mul, h0, zero_mul]
    rw [Polynomial.eval_mul] at hmul
    exact mul_ne_zero hp hq hmul
  one_mem' := by simp
  add_mem' {p q} hp hq := by
    change (p + q).denom.eval u ≠ 0
    intro h0
    obtain ⟨r, hr⟩ := RatFunc.denom_add_dvd p q
    have hmul : (p.denom * q.denom).eval u = 0 := by
      rw [hr, Polynomial.eval_mul, h0, zero_mul]
    rw [Polynomial.eval_mul] at hmul
    exact mul_ne_zero hp hq hmul
  zero_mem' := by simp
  neg_mem' {p} hp := by
    change (-p).denom.eval u ≠ 0
    have hneg : -p = RatFunc.C (-1) * p := by simp
    rw [hneg]
    intro h0
    obtain ⟨r, hr⟩ := RatFunc.denom_mul_dvd (RatFunc.C (-1)) p
    have hmul : ((RatFunc.C (-1 : ℂ)).denom * p.denom).eval u = 0 := by
      rw [hr, Polynomial.eval_mul, h0, zero_mul]
    rw [Polynomial.eval_mul, RatFunc.denom_C, Polynomial.eval_one, one_mul] at hmul
    exact hp hmul

private noncomputable def ratEvalHom (u : ℂ) : regularAt u →+* ℂ where
  toFun q := ratEval q.1 u
  map_one' := by simp [ratEval]
  map_mul' p q := ratEval_mul p.1 q.1 u p.2 q.2
  map_zero' := by simp [ratEval]
  map_add' p q := ratEval_add p.1 q.1 u p.2 q.2

private lemma X_inv_mem_regularAt {u : ℝ} (hu : 0 < u) :
    (RatFunc.X : RatFunc ℂ)⁻¹ ∈ regularAt (u : ℂ) := by
  have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  change ((RatFunc.X : RatFunc ℂ)⁻¹).denom.eval (u : ℂ) ≠ 0
  have hdiv : (RatFunc.X : RatFunc ℂ)⁻¹ =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) 1 / algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X := by
    simp [RatFunc.algebraMap_X]
  have hdvd : ((RatFunc.X : RatFunc ℂ)⁻¹).denom ∣ Polynomial.X := by
    rw [hdiv]; exact RatFunc.denom_div_dvd 1 Polynomial.X
  intro h0
  obtain ⟨r, hr⟩ := hdvd
  have hev := congrArg (Polynomial.eval (u : ℂ)) hr
  rw [Polynomial.eval_mul, h0, zero_mul, Polynomial.eval_X] at hev
  exact hu_ne hev

private lemma ratEval_shiftRatFunc (j : ℕ) {u : ℝ} (hu : 0 < u) :
    ratEval (shiftRatFunc j) (u : ℂ) =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 1) +
      (2 : ℂ)⁻¹ * (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (u : ℂ)⁻¹ ^ (j + 2) := by
  have hXinv_mem := X_inv_mem_regularAt hu
  have hXinv_eval : ratEvalHom (u : ℂ) ⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ = (u : ℂ)⁻¹ := by
    have hX_mem : (RatFunc.X : RatFunc ℂ) ∈ regularAt (u : ℂ) := by
      change (RatFunc.X : RatFunc ℂ).denom.eval (u : ℂ) ≠ 0; simp [RatFunc.denom_X]
    have hmul1 : (⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ : regularAt (u : ℂ)) *
        ⟨RatFunc.X, hX_mem⟩ = 1 := by
      ext; exact inv_mul_cancel₀ RatFunc.X_ne_zero
    have hmul2 := congrArg (ratEvalHom (u : ℂ)) hmul1
    rw [map_mul, map_one] at hmul2
    have hX_eval : ratEvalHom (u : ℂ) ⟨RatFunc.X, hX_mem⟩ = (u : ℂ) := by
      simp [ratEvalHom, ratEval]
    rw [hX_eval] at hmul2
    exact eq_inv_of_mul_eq_one_left hmul2
  have hC_mem : ∀ c : ℂ, RatFunc.C c ∈ regularAt (u : ℂ) := fun c => by
    change (RatFunc.C c).denom.eval (u : ℂ) ≠ 0
    rw [RatFunc.denom_C, Polynomial.eval_one]
    exact one_ne_zero
  have hC_eval : ∀ c : ℂ, ratEvalHom (u : ℂ) ⟨RatFunc.C c, hC_mem c⟩ = c := fun c => by
    simp [ratEvalHom, ratEval]
  let c1 : ℂ := (-1 : ℂ) ^ j * (j.factorial : ℂ)
  let c2 : ℂ := (2 : ℂ)⁻¹ * (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ)
  calc ratEval (shiftRatFunc j) (u : ℂ)
      = ratEvalHom (u : ℂ)
          (⟨RatFunc.C c1, hC_mem c1⟩ * ⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ ^ (j + 1) +
           ⟨RatFunc.C c2, hC_mem c2⟩ * ⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ ^ (j + 2)) := rfl
    _ = ratEvalHom (u : ℂ) (⟨RatFunc.C c1, hC_mem c1⟩ * ⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ ^ (j + 1)) +
        ratEvalHom (u : ℂ) (⟨RatFunc.C c2, hC_mem c2⟩ * ⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ ^ (j + 2)) :=
          map_add (ratEvalHom (u : ℂ)) _ _
    _ = ratEvalHom (u : ℂ) ⟨RatFunc.C c1, hC_mem c1⟩ *
          ratEvalHom (u : ℂ) (⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ ^ (j + 1)) +
        ratEvalHom (u : ℂ) ⟨RatFunc.C c2, hC_mem c2⟩ *
          ratEvalHom (u : ℂ) (⟨(RatFunc.X : RatFunc ℂ)⁻¹, hXinv_mem⟩ ^ (j + 2)) :=
          congrArg₂ (· + ·) (map_mul (ratEvalHom (u : ℂ)) _ _) (map_mul (ratEvalHom (u : ℂ)) _ _)
    _ = c1 * (u : ℂ)⁻¹ ^ (j + 1) + c2 * (u : ℂ)⁻¹ ^ (j + 2) :=
          congrArg₂ (· + ·)
            (congrArg₂ (· * ·) (hC_eval c1)
              ((map_pow (ratEvalHom (u : ℂ)) _ _).trans (congrArg (· ^ (j + 1)) hXinv_eval)))
            (congrArg₂ (· * ·) (hC_eval c2)
              ((map_pow (ratEvalHom (u : ℂ)) _ _).trans (congrArg (· ^ (j + 2)) hXinv_eval)))

private lemma evalRatU_map_subtype {r : ℕ} (u : ℂ)
    (Q : MvPolynomial (Fin (r + 1)) (regularAt u)) :
    evalRatU (MvPolynomial.map (regularAt u).subtype Q) u =
      MvPolynomial.map (ratEvalHom u) Q := by
  classical
  ext α
  simp only [evalRatU, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_map]
  by_cases hα : α ∈ (MvPolynomial.map (regularAt u).subtype Q).support
  · rw [Finset.sum_eq_single α]
    · simp [ratEvalHom]
    · intro β _ hβα; simp [hβα]
    · intro hn; exact absurd hα hn
  · have hq0 : (MvPolynomial.map (regularAt u).subtype Q).coeff α = 0 :=
      MvPolynomial.notMem_support_iff.mp hα
    rw [MvPolynomial.coeff_map] at hq0
    have hq0' : Q.coeff α = 0 := Subtype.ext hq0
    rw [hq0', map_zero, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

/-- **Differential Transcendence of `trigamma` over `ℂ(u)`**:
`ψ'(u) = d/du (Γ'(u)/Γ(u))` satisfies NO nonzero algebraic differential equation over `ℂ(u)`. -/
theorem trigamma_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => trigamma (x : ℂ)) u)
        (evalRatU P (u : ℂ)) = 0) :
    P = 0 := by
  classical
  let g : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) :=
    fun j => MvPolynomial.X j + MvPolynomial.C (shiftRatFunc j.val)
  let Q : MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := MvPolynomial.eval₂ MvPolynomial.C g P
  have hQ_zero : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val trigammaRem u)
        (evalRatU Q (u : ℂ)) = 0 := by
    have hden : ∀ᶠ u : ℝ in Filter.atTop, ∀ β ∈ P.support, (P.coeff β).denom.eval (u : ℂ) ≠ 0 :=
      (Filter.eventually_all_finset P.support).mpr fun β _ => by
        let q := (P.coeff β).denom
        have hq : q ≠ 0 := RatFunc.denom_ne_zero _
        let B : ℝ := Finset.sum q.roots.toFinset fun z : ℂ => ‖z‖
        have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
        filter_upwards [eventually_gt_atTop B] with u hu h0
        have hmem : (u : ℂ) ∈ q.roots := (Polynomial.mem_roots hq).mpr h0
        have hle : ‖(u : ℂ)‖ ≤ B := Finset.single_le_sum (f := fun z : ℂ => ‖z‖)
          (fun _ _ => norm_nonneg _) (Multiset.mem_toFinset.mpr hmem)
        have hpos : 0 < u := lt_of_le_of_lt hB hu
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hle
        linarith
    filter_upwards [hP, hden, eventually_gt_atTop (0 : ℝ)] with u hu hdu hu_pos
    let P_reg : MvPolynomial (Fin (r + 1)) (regularAt (u : ℂ)) :=
      ∑ β ∈ P.support.attach, MvPolynomial.monomial β.1 ⟨P.coeff β.1, hdu β.1 β.2⟩
    have hP_reg_map : MvPolynomial.map (regularAt (u : ℂ)).subtype P_reg = P := by
      ext α
      simp only [P_reg, MvPolynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      by_cases hα : α ∈ P.support
      · rw [Finset.sum_eq_single ⟨α, hα⟩]
        · simp
        · intro β _ hβα; simp [show β.1 ≠ α from fun h => hβα (Subtype.ext h)]
        · intro hn; exact absurd (Finset.mem_attach _ ⟨α, hα⟩) hn
      · rw [MvPolynomial.notMem_support_iff.mp hα, Finset.sum_eq_zero]
        · simp
        · intro β _; simp [show β.1 ≠ α from fun h => hα (h ▸ β.2)]
    have hC_mem : ∀ c : ℂ, RatFunc.C c ∈ regularAt (u : ℂ) := fun c => by
      change (RatFunc.C c).denom.eval (u : ℂ) ≠ 0
      rw [RatFunc.denom_C, Polynomial.eval_one]
      exact one_ne_zero
    have h_shift_mem : ∀ j : ℕ, shiftRatFunc j ∈ regularAt (u : ℂ) := by
      intro j
      have hXinv := X_inv_mem_regularAt hu_pos
      exact (regularAt (u : ℂ)).add_mem
        ((regularAt (u : ℂ)).mul_mem (hC_mem _) ((regularAt (u : ℂ)).pow_mem hXinv (j + 1)))
        ((regularAt (u : ℂ)).mul_mem (hC_mem _) ((regularAt (u : ℂ)).pow_mem hXinv (j + 2)))
    let g_reg : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (regularAt (u : ℂ)) :=
      fun j => MvPolynomial.X j + MvPolynomial.C ⟨shiftRatFunc j.val, h_shift_mem j.val⟩
    let Q_reg : MvPolynomial (Fin (r + 1)) (regularAt (u : ℂ)) := MvPolynomial.eval₂ MvPolynomial.C g_reg P_reg
    have hQ_reg_map : MvPolynomial.map (regularAt (u : ℂ)).subtype Q_reg = Q := by
      dsimp only [Q_reg, Q]
      rw [MvPolynomial.map_eval₂, hP_reg_map]
      congr 1
      funext j
      simp [g_reg, g]
    have h_eval_shift : ∀ j : Fin (r + 1),
        iteratedDeriv j.val trigammaRem u + ratEval (shiftRatFunc j.val) (u : ℂ) =
          iteratedDeriv j.val (fun x : ℝ => trigamma (x : ℂ)) u := by
      intro j
      have h_cmul : iteratedDeriv j.val (fun x : ℝ => (2 : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ 2) u =
          (2 : ℂ)⁻¹ * iteratedDeriv j.val (fun x : ℝ => (x : ℂ)⁻¹ ^ 2) u :=
        iteratedDeriv_const_mul (2 : ℂ)⁻¹
          (((Complex.ofRealCLM.analyticAt u).inv (Complex.ofReal_ne_zero.mpr hu_pos.ne')).pow 2 |>.contDiffAt.of_le le_top)
      rw [iteratedDeriv_trigammaRem_of_pos j.val hu_pos, h_cmul,
        iteratedDeriv_inv_of_pos j.val hu_pos, iteratedDeriv_inv_sq_of_pos j.val hu_pos,
        ratEval_shiftRatFunc j.val hu_pos]
      ring
    rw [← hQ_reg_map, evalRatU_map_subtype]
    dsimp only [Q_reg]
    rw [MvPolynomial.map_eval₂, MvPolynomial.eval_eval₂, MvPolynomial.eval₂_map]
    have hC_id :
        ((MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val trigammaRem u)).comp
            (MvPolynomial.C : ℂ →+* MvPolynomial (Fin (r + 1)) ℂ)).comp (ratEvalHom (u : ℂ)) =
          ratEvalHom (u : ℂ) := by
      ext c; simp
    have h_fn_eq :
        (fun j : Fin (r + 1) =>
          MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.val trigammaRem u)
            ((MvPolynomial.map (ratEvalHom (u : ℂ)) ∘ g_reg) j)) =
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => trigamma (x : ℂ)) u) := by
      funext j
      simp [g_reg, ratEvalHom, h_eval_shift j]
    have hLHS :
        MvPolynomial.eval₂
          (((MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val trigammaRem u)).comp
              (MvPolynomial.C : ℂ →+* MvPolynomial (Fin (r + 1)) ℂ)).comp (ratEvalHom (u : ℂ)))
          (fun j => MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.val trigammaRem u)
            ((MvPolynomial.map (ratEvalHom (u : ℂ)) ∘ g_reg) j)) P_reg =
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => trigamma (x : ℂ)) u)
            (evalRatU P (u : ℂ)) := by
      rw [hC_id, h_fn_eq, ← hP_reg_map, evalRatU_map_subtype, MvPolynomial.eval_map]
    rw [hLHS, hu]
  have hQ0 : Q = 0 := trigammaRem_no_rat_ade Q hQ_zero
  let g_inv : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) :=
    fun j => MvPolynomial.X j - MvPolynomial.C (shiftRatFunc j.val)
  have h_roundtrip : MvPolynomial.eval₂ MvPolynomial.C g_inv Q = P := by
    have key : ∀ R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ),
        MvPolynomial.eval₂ MvPolynomial.C g_inv (MvPolynomial.eval₂ MvPolynomial.C g R) = R := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C c => simp
      | add p q hp hq => simp only [MvPolynomial.eval₂_add, hp, hq]
      | mul_X p j hp =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul, hp]
        dsimp only [g, g_inv]
        rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
        simp
    exact key P
  rw [← h_roundtrip, hQ0, MvPolynomial.eval₂_zero]

/-! ### 3. Hölder's Theorem (1887): Differential Transcendence of `Complex.Gamma` and `Real.Gamma` -/

private noncomputable def polyToMvNat : Polynomial ℂ →+* MvPolynomial ℕ ℂ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

private lemma eval_polyToMvNat (p : Polynomial ℂ) (y : ℕ → ℂ) :
    MvPolynomial.eval y (polyToMvNat p) = p.eval (y 0) := by
  have h : (MvPolynomial.eval y).comp polyToMvNat = Polynomial.evalRingHom (y 0) := by
    apply Polynomial.ringHom_ext
    · intro c; simp [polyToMvNat]
    · simp [polyToMvNat]
  exact RingHom.congr_fun h p

private noncomputable def mvPolyToMvNat {r : ℕ} :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) →+* MvPolynomial ℕ ℂ :=
  MvPolynomial.eval₂Hom polyToMvNat (fun j : Fin (r + 1) => MvPolynomial.X (j.val + 1))

private lemma eval_mvPolyToMvNat {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (y : ℕ → ℂ) :
    MvPolynomial.eval y (mvPolyToMvNat P) =
      MvPolynomial.eval (fun j : Fin (r + 1) => y (j.val + 1)) (evalU P (y 0)) := by
  have h : (MvPolynomial.eval y).comp (mvPolyToMvNat (r := r)) =
      (MvPolynomial.eval (fun j : Fin (r + 1) => y (j.val + 1))).comp
        (MvPolynomial.map (Polynomial.evalRingHom (y 0))) := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [mvPolyToMvNat, eval_polyToMvNat]
    · intro j
      simp [mvPolyToMvNat]
  exact RingHom.congr_fun h P

private lemma mvPolyToMvNat_eq_zero_imp {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : mvPolyToMvNat P = 0) : P = 0 := by
  rw [MvPolynomial.ext_iff]
  intro α
  rw [show (0 : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)).coeff α = 0 from rfl]
  apply Polynomial.funext
  intro u
  rw [Polynomial.eval_zero]
  have heval_zero : ∀ x : Fin (r + 1) → ℂ, MvPolynomial.eval x (evalU P u) = 0 := by
    intro x
    let y : ℕ → ℂ := fun n =>
      if n = 0 then u else x ⟨(n - 1) % (r + 1), Nat.mod_lt _ (Nat.succ_pos r)⟩
    have hy0 : y 0 = u := by simp [y]
    have hyj : ∀ j : Fin (r + 1), y (j.val + 1) = x j := by
      intro j
      simp [y, Nat.mod_eq_of_lt j.isLt]
    have h1 := eval_mvPolyToMvNat P y
    rw [hP, map_zero, hy0] at h1
    simpa [hyj] using h1.symm
  have hU0 : evalU P u = 0 := MvPolynomial.funext heval_zero
  have hc := congrArg (fun Q : MvPolynomial (Fin (r + 1)) ℂ => Q.coeff α) hU0
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom] at hc
  exact hc

private lemma poly_eval_eventually_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∀ᶠ u : ℝ in Filter.atTop, q.eval (u : ℂ) ≠ 0 := by
  let B : ℝ := Finset.sum q.roots.toFinset fun z : ℂ => ‖z‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  filter_upwards [eventually_gt_atTop B] with u hu h0
  have hmem : (u : ℂ) ∈ q.roots := (Polynomial.mem_roots hq).mpr h0
  have hle : ‖(u : ℂ)‖ ≤ B :=
    Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _)
      (Multiset.mem_toFinset.mpr hmem)
  have hpos : 0 < u := lt_of_le_of_lt hB hu
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hle
  linarith

private noncomputable def clearDenomPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    Polynomial ℂ :=
  ∏ α ∈ P.support, (P.coeff α).denom

private noncomputable def clearDenomMvPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α
    ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)

private lemma clearDenomMvPoly_coeff {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (α : Fin (r + 1) →₀ ℕ) :
    (clearDenomMvPoly P).coeff α =
      (P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom := by
  classical
  unfold clearDenomMvPoly
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hP0, RatFunc.num_zero, zero_mul, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

private lemma clearDenomMvPoly_eq_zero_iff {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    clearDenomMvPoly P = 0 ↔ P = 0 := by
  constructor
  · intro h0
    ext α
    have hc := congrArg (fun Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) => Q.coeff α) h0
    change (clearDenomMvPoly P).coeff α = 0 at hc
    rw [clearDenomMvPoly_coeff] at hc
    have hden_ne : (∏ β ∈ P.support.erase α, (P.coeff β).denom) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ => RatFunc.denom_ne_zero _
    have hnum0 : (P.coeff α).num = 0 := (mul_eq_zero.mp hc).resolve_right hden_ne
    exact RatFunc.num_eq_zero_iff.mp hnum0
  · rintro rfl
    simp [clearDenomMvPoly]

private lemma evalU_clearDenomMvPoly {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) {u : ℂ}
    (hu : ∀ β ∈ P.support, (P.coeff β).denom.eval u ≠ 0) :
    evalU (clearDenomMvPoly P) u = (clearDenomPoly P).eval u • evalRatU P u := by
  classical
  ext α
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, clearDenomMvPoly_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul, evalRatU, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp only [↓reduceIte, ratEval, clearDenomPoly, Polynomial.eval_prod]
      rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval u) hα,
        Polynomial.eval_mul, Polynomial.eval_prod]
      field_simp [hu α hα]
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hP0, RatFunc.num_zero, zero_mul, Polynomial.eval_zero, Finset.sum_eq_zero]
    · simp
    · intro β hβ
      rw [ite_eq_right_iff]
      intro hβα
      subst hβα
      exact absurd hβ hα

/-- **Hölder's Theorem (1887) over `ℂ[u]`**:
`Complex.Gamma` restricted to `ℝ` satisfies NO nonzero algebraic differential equation over `ℂ[u]`. -/
theorem holder_gamma_no_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => Complex.Gamma (x : ℂ)) u)
        (evalU P (u : ℂ)) = 0) :
    P = 0 := by
  classical
  by_contra hP_ne
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hP
  let U : Set ℝ := Set.Ioi (max R₀ 0)
  have hU_ne : U.Nonempty := ⟨max R₀ 0 + 1, by simp [U]⟩
  have hU_pos : ∀ z ∈ U, 0 < z := fun z hz => lt_of_le_of_lt (le_max_right _ _) hz
  let y : ℕ → ℝ → ℂ := fun i x =>
    if i = 0 then (x : ℂ) else iteratedDeriv (i - 1) (fun t : ℝ => Complex.Gamma (t : ℂ)) x
  have hmv_ne : mvPolyToMvNat P ≠ 0 := fun h0 => hP_ne (mvPolyToMvNat_eq_zero_imp h0)
  have hmv_vanish : ∀ x ∈ U, MvPolynomial.eval (fun i => y i x) (mvPolyToMvNat P) = 0 := by
    intro x hx
    rw [eval_mvPolyToMvNat]
    have hy0 : y 0 x = (x : ℂ) := by simp [y]
    have hyj : ∀ j : Fin (r + 1),
        y (j.val + 1) x = iteratedDeriv j.val (fun t : ℝ => Complex.Gamma (t : ℂ)) x := by
      intro j; simp [y]
    rw [hy0]
    simp_rw [hyj]
    exact hR₀ x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx))
  obtain ⟨n, Q, x₀, hx₀, hS_ne, hQ_vanish⟩ :=
    ordinary_relation U hU_ne y ⟨mvPolyToMvNat P, hmv_ne, hmv_vanish⟩
  have hn_ne : n ≠ 0 := by
    rintro rfl
    let q : Polynomial ℂ := MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) Q
    have hq_eval : ∀ (T : MvPolynomial (Fin 1) ℂ) (c : ℂ),
        (MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) T).eval c =
          MvPolynomial.eval (fun _ : Fin 1 => c) T := by
      intro T c
      induction T using MvPolynomial.induction_on with
      | C a => simp
      | add a b ha hb => simp [MvPolynomial.eval₂_add, ha, hb]
      | mul_X a i ha => simp [MvPolynomial.eval₂_mul, ha]
    have hq0 : q = 0 := by
      by_contra hq_ne
      obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (poly_eval_eventually_ne_zero hq_ne)
      let z : ℝ := max (max R₀ 0) R₁ + 1
      have hzU : z ∈ U := by simp only [U, Set.mem_Ioi, z]; linarith [le_max_left (max R₀ 0) R₁]
      have hzR₁ : R₁ < z := by simp only [z]; linarith [le_max_right (max R₀ 0) R₁]
      have hvan := hQ_vanish z hzU
      have hy_fin : (fun i : Fin 1 => y i.val z) = fun _ : Fin 1 => (z : ℂ) := by
        funext i; fin_cases i; simp [y]
      rw [hy_fin, ← hq_eval Q (z : ℂ)] at hvan
      exact hR₁ z hzR₁.le hvan
    have hQ0 : Q = 0 := by
      apply MvPolynomial.funext
      intro w
      have hw : w = fun _ : Fin 1 => w 0 := funext fun i => by fin_cases i; rfl
      rw [hw, ← hq_eval Q (w 0), show eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) Q = q from rfl,
        hq0, Polynomial.eval_zero, map_zero]
    have hp0 : MvPolynomial.pderiv (Fin.last 0) Q = 0 := by rw [hQ0, map_zero]
    rw [hp0, map_zero] at hS_ne
    exact hS_ne rfl
  have hn_pos : 1 < n + 1 := by omega
  let idx1 : Fin (n + 1) := ⟨1, hn_pos⟩
  let v : Fin (n + 1) → ℝ → ℂ := fun i z => y i.val z
  let top : Fin (n + 1) := Fin.last n
  let g : Fin (n + 1) → ℝ → ℂ := fun i z =>
    MvPolynomial.eval (fun j => v j z) (MvPolynomial.pderiv i Q)
  let S : ℝ → ℂ := g top
  have gamma_analytic : ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      AnalyticAt ℝ (iteratedDeriv k (fun t : ℝ => Complex.Gamma (t : ℂ))) z := by
    intro k z hz
    induction k generalizing z with
    | zero =>
      have hzc : 0 < (z : ℂ).re := by simpa only [Complex.ofReal_re] using hz
      have h0 : AnalyticAt ℝ (fun t : ℝ => Complex.Gamma (t : ℂ)) z :=
        ((gamma_analyticOnNhd_re_pos (z : ℂ) hzc).restrictScalars (𝕜 := ℝ)).comp
          (Complex.ofRealCLM.analyticAt z)
      simpa using h0
    | succ k ih =>
      have hzc : 0 < z := hz
      have hk := ih z hzc
      rw [iteratedDeriv_succ]
      exact hk.deriv
  have hd : ∀ z : ℝ, 0 < z → ∀ i : Fin (n + 1), DifferentiableAt ℝ (v i) z := by
    intro z hz i
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero =>
      have hv0 : v ⟨0, hk⟩ = fun t : ℝ => (t : ℂ) := by ext t; simp [v, y]
      rw [hv0]
      exact Complex.ofRealCLM.differentiableAt
    | succ k =>
      have hvk : v ⟨k + 1, hk⟩ = iteratedDeriv k (fun t : ℝ => Complex.Gamma (t : ℂ)) := by
        ext t; simp [v, y]
      rw [hvk]
      exact (gamma_analytic k z hz).differentiableAt
  have chain : ∀ (A : MvPolynomial (Fin (n + 1)) ℂ) (z : ℝ), 0 < z →
      HasDerivAt (fun p => MvPolynomial.eval (fun i => v i p) A)
        (∑ i, MvPolynomial.eval (fun j => v j z) (MvPolynomial.pderiv i A) * _root_.deriv (v i) z) z :=
    fun A z hz => polynomial_chain A v (fun i => _root_.deriv (v i)) z fun i => (hd z hz i).hasDerivAt
  have hU_open : IsOpen U := isOpen_Ioi
  have vanish : ∀ z ∈ U, ∑ i : Fin (n + 1), g i z * _root_.deriv (v i) z = 0 := by
    intro z hz
    have near : (fun w => MvPolynomial.eval (fun i => v i w) Q) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hU_open.mem_nhds hz] with w hw
      exact hQ_vanish w hw
    exact (chain Q z (hU_pos z hz)).deriv.symm.trans (near.deriv_eq.trans (deriv_const _ _))
  have Snz : ∀ᶠ z in 𝓝 x₀, S z ≠ 0 :=
    (chain (MvPolynomial.pderiv top Q) x₀ (hU_pos x₀ hx₀)).continuousAt.eventually_ne hS_ne
  let invS (z : ℝ) : ℂ := (S z)⁻¹
  let invG (z : ℝ) : ℂ := (v idx1 z)⁻¹
  let uState : Fin (n + 1) ⊕ Fin 2 → ℝ → ℂ := Sum.elim v ![invS, invG]
  have h_inr0 : uState (.inr 0) = invS := rfl
  have h_inr1 : uState (.inr 1) = invG := rfl
  let G := Generated uState x₀
  have gv (i : Fin (n + 1)) : G (v i) := Generated.coord (u := uState) (.inl i)
  have gw : G invS := Generated.coord (u := uState) (.inr 0)
  have hgG : G invG := Generated.coord (u := uState) (.inr 1)
  have gc (c : ℂ) : G (fun _ => c) := Generated.const _
  have gg (i : Fin (n + 1)) : G (g i) := Generated.evalPoly v gv _
  have low (i : Fin (n + 1)) (hi : i ≠ top) : G (_root_.deriv (v i)) := by
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero =>
      have hv0 : v ⟨0, hk⟩ = fun t : ℝ => (t : ℂ) := by ext t; simp [v, y]
      have hd0 : ∀ z : ℝ, _root_.deriv (v ⟨0, hk⟩) z = 1 := by
        intro z
        rw [hv0]
        simpa using (hasDerivAt_id z).ofReal_comp.deriv
      exact (gc 1).congr (Eventually.of_forall fun z => (hd0 z).symm)
    | succ k =>
      have hlt : k + 2 < n + 1 := by
        have h : k + 1 ≠ n := fun eqn => hi (Fin.ext eqn); omega
      refine (gv ⟨k + 2, hlt⟩).congr (Eventually.of_forall fun z => ?_)
      have hvk : v ⟨k + 1, hk⟩ = iteratedDeriv k (fun t : ℝ => Complex.Gamma (t : ℂ)) := by
        ext t; simp [v, y]
      have hv2 : v ⟨k + 2, hlt⟩ z = iteratedDeriv (k + 1) (fun t : ℝ => Complex.Gamma (t : ℂ)) z := by
        simp [v, y]
      rw [hv2, hvk, iteratedDeriv_succ]
  let lowSum := ∑ i ∈ Finset.univ.erase top, g i * _root_.deriv (v i)
  have gl : G lowSum :=
    Generated.finsetSum _ _ fun i hi => (gg i).mul (low i (Finset.mem_erase.mp hi).1)
  have dv (i : Fin (n + 1)) : G (_root_.deriv (v i)) := by
    by_cases hi : i = top
    · subst i
      apply (((gc (-1)).mul gl).mul gw).congr
      filter_upwards [hU_open.mem_nhds hx₀, Snz] with z hz nz
      have he := vanish z hz
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at he
      change (-1) * lowSum z * (S z)⁻¹ = _root_.deriv (v top) z
      have hh : S z * _root_.deriv (v top) z + lowSum z = 0 := by
        simpa [S, lowSum, Finset.sum_apply] using he
      field_simp [nz]
      linear_combination -hh
    · exact low i hi
  have dS : G (_root_.deriv S) := by
    let D (i : Fin (n + 1)) (z : ℝ) :=
      MvPolynomial.eval (fun k => v k z) (MvPolynomial.pderiv i (MvPolynomial.pderiv top Q))
    have gen (i) : G (D i) := Generated.evalPoly v gv _
    apply (Generated.finsetSum Finset.univ _ fun i _ => (gen i).mul (dv i)).congr
    filter_upwards [hU_open.mem_nhds hx₀] with z hz
    simpa [D, Finset.sum_apply] using
      (chain (MvPolynomial.pderiv top Q) z (hU_pos z hz)).deriv.symm
  have smooth : ∀ᶠ z in 𝓝 x₀, ∀ i, DifferentiableAt ℝ (uState i) z := by
    filter_upwards [hU_open.mem_nhds hx₀, Snz] with z hz nz i
    rcases i with i | i
    · exact hd z (hU_pos z hz) i
    · fin_cases i
      · exact (chain (MvPolynomial.pderiv top Q) z (hU_pos z hz)).differentiableAt.inv nz
      · have hGnz : v idx1 z ≠ 0 := by
          have hv1 : v idx1 z = Complex.Gamma (z : ℂ) := by simp [v, y, idx1]
          have hzc : 0 < (z : ℂ).re := by simpa only [Complex.ofReal_re] using hU_pos z hz
          rw [hv1]
          exact Complex.Gamma_ne_zero (re_pos_avoids_neg_nat hzc)
        exact (hd z (hU_pos z hz) idx1).inv hGnz
  have closed (i) : G (_root_.deriv (uState i)) := by
    rcases i with i | i
    · exact dv i
    · fin_cases i
      · change G (_root_.deriv (uState (.inr 0)))
        rw [h_inr0]
        apply (((gc (-1)).mul dS).mul (gw.pow 2)).congr
        filter_upwards [hU_open.mem_nhds hx₀, Snz] with z hz nz
        have hi := ((chain (MvPolynomial.pderiv top Q) z (hU_pos z hz)).differentiableAt.hasDerivAt.inv nz).deriv
        change (-1) * _root_.deriv S z * ((S z)⁻¹) ^ 2 = _root_.deriv invS z
        change _root_.deriv invS z = -_root_.deriv S z / (S z) ^ 2 at hi
        rw [hi]; simp [inv_pow, div_eq_mul_inv]
      · change G (_root_.deriv (uState (.inr 1)))
        rw [h_inr1]
        apply (((gc (-1)).mul (dv idx1)).mul (hgG.pow 2)).congr
        filter_upwards [hU_open.mem_nhds hx₀] with z hz
        have hGnz : v idx1 z ≠ 0 := by
          have hv1 : v idx1 z = Complex.Gamma (z : ℂ) := by simp [v, y, idx1]
          have hzc : 0 < (z : ℂ).re := by simpa only [Complex.ofReal_re] using hU_pos z hz
          rw [hv1]
          exact Complex.Gamma_ne_zero (re_pos_avoids_neg_nat hzc)
        have hi := ((hd z (hU_pos z hz) idx1).hasDerivAt.inv hGnz).deriv
        change (-1) * _root_.deriv (v idx1) z * ((v idx1 z)⁻¹) ^ 2 = _root_.deriv invG z
        change _root_.deriv invG z = -_root_.deriv (v idx1) z / (v idx1 z) ^ 2 at hi
        rw [hi]; simp [inv_pow, div_eq_mul_inv]
  have readout_digamma : G (fun z : ℝ => Complex.digamma (z : ℂ)) := by
    refine ((dv idx1).mul hgG).congr ?_
    filter_upwards [hU_open.mem_nhds hx₀] with z hz
    have hzc : 0 < (z : ℂ).re := by simpa only [Complex.ofReal_re] using hU_pos z hz
    have hd_gam : HasDerivAt Complex.Gamma (deriv Complex.Gamma (z : ℂ)) (z : ℂ) :=
      (Complex.differentiableAt_Gamma (z : ℂ) (re_pos_avoids_neg_nat hzc)).hasDerivAt
    have hd_real : HasDerivAt (fun t : ℝ => Complex.Gamma (t : ℂ)) (deriv Complex.Gamma (z : ℂ)) z :=
      hd_gam.comp_ofReal
    have hv1 : v idx1 = fun t : ℝ => Complex.Gamma (t : ℂ) := by ext t; simp [v, y, idx1]
    change (_root_.deriv (v idx1) * invG) z = Complex.digamma (z : ℂ)
    dsimp only [Pi.mul_apply]
    rw [Complex.digamma_def, logDeriv_apply, hv1, hd_real.deriv]
    simp [invG, hv1, div_eq_mul_inv]
  have readout_trigamma : G (fun z : ℝ => trigamma (z : ℂ)) := by
    refine (readout_digamma.deriv smooth closed).congr ?_
    filter_upwards [hU_open.mem_nhds hx₀] with z hz
    have hzc : 0 < (z : ℂ).re := by simpa only [Complex.ofReal_re] using hU_pos z hz
    have hd_dig := (digamma_analyticOnNhd_re_pos (z : ℂ) hzc).differentiableAt.hasDerivAt.comp_ofReal
    exact hd_dig.deriv
  obtain ⟨R, hR_ne, hR_nhds⟩ :=
    autonomous_readout uState x₀ (fun z : ℝ => trigamma (z : ℂ)) readout_trigamma smooth closed
  have tri_analytic : ∀ k : ℕ, AnalyticOnNhd ℝ (iteratedDeriv k (fun t : ℝ => trigamma (t : ℂ))) (Set.Ioi 0) := by
    intro k
    induction k with
    | zero =>
      intro z hz
      have hzc : 0 < (z : ℂ).re := by simpa only [Complex.ofReal_re] using Set.mem_Ioi.mp hz
      have h0 : AnalyticAt ℝ (fun t : ℝ => trigamma (t : ℂ)) z :=
        ((trigamma_analyticOnNhd_re_pos (z : ℂ) hzc).restrictScalars (𝕜 := ℝ)).comp
          (Complex.ofRealCLM.analyticAt z)
      simpa using h0
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      exact (ih z hz).deriv
  have R_analytic : AnalyticOnNhd ℝ
      (fun u : ℝ => MvPolynomial.eval
        (fun j : Fin (Fintype.card (Fin (n + 1) ⊕ Fin 2) + 1) =>
          iteratedDeriv j.val (fun t : ℝ => trigamma (t : ℂ)) u) R) (Set.Ioi 0) := by
    intro u hu
    clear hR_ne hR_nhds
    induction R using MvPolynomial.induction_on with
    | C c => simpa using analyticAt_const
    | add A B hA hB => simpa only [map_add] using! hA.add hB
    | mul_X A j hA => simpa only [map_mul, MvPolynomial.eval_X] using! hA.mul (tri_analytic j.val u hu)
  have hR_tail : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval
        (fun j : Fin (Fintype.card (Fin (n + 1) ⊕ Fin 2) + 1) =>
          iteratedDeriv j.val (fun t : ℝ => trigamma (t : ℂ)) u) R = 0 := by
    refine eventually_atTop.mpr ⟨1, fun u hu => ?_⟩
    exact R_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected (hU_pos x₀ hx₀) hR_nhds (Set.mem_Ioi.mpr (by linarith))
  let R_rat : MvPolynomial (Fin (Fintype.card (Fin (n + 1) ⊕ Fin 2) + 1)) (RatFunc ℂ) :=
    MvPolynomial.map (RatFunc.C : ℂ →+* RatFunc ℂ) R
  have hR_rat_eval : ∀ u : ℂ, evalRatU R_rat u = R := by
    intro u
    ext α
    simp only [evalRatU, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      R_rat, MvPolynomial.coeff_map]
    by_cases hα : α ∈ R_rat.support
    · rw [Finset.sum_eq_single α]
      · simp [ratEval]
      · intro β _ hβα; simp [hβα]
      · intro hn; exact absurd hα hn
    · have hr0 : R_rat.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
      dsimp only [R_rat] at hr0
      rw [MvPolynomial.coeff_map] at hr0
      have hr0' : R.coeff α = 0 := RatFunc.C_injective (hr0.trans (map_zero _).symm)
      rw [hr0', Finset.sum_eq_zero]
      intro β hβ
      have hne : β ≠ α := fun h => hα (h ▸ hβ)
      simp [hne]
  have hR_rat_zero : R_rat = 0 := by
    refine trigamma_no_rat_ade R_rat ?_
    filter_upwards [hR_tail] with u hu
    rw [hR_rat_eval, hu]
  exact hR_ne (MvPolynomial.map_injective RatFunc.C RatFunc.C_injective (hR_rat_zero.trans (map_zero _).symm))

/-- **Hölder's Theorem (1887) over `ℂ(u)`**:
`Complex.Gamma` restricted to `ℝ` satisfies NO nonzero algebraic differential equation over `ℂ(u)`. -/
theorem holder_gamma_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => Complex.Gamma (x : ℂ)) u)
        (evalRatU P (u : ℂ)) = 0) :
    P = 0 := by
  have hden : ∀ᶠ u : ℝ in Filter.atTop, ∀ β ∈ P.support, (P.coeff β).denom.eval (u : ℂ) ≠ 0 :=
    (Filter.eventually_all_finset P.support).mpr fun β _ =>
      poly_eval_eventually_ne_zero (RatFunc.denom_ne_zero _)
  have hP_clear : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => Complex.Gamma (x : ℂ)) u)
        (evalU (clearDenomMvPoly P) (u : ℂ)) = 0 := by
    filter_upwards [hP, hden] with u hu hdu
    rw [evalU_clearDenomMvPoly P hdu, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hu,
      mul_zero]
  exact (clearDenomMvPoly_eq_zero_iff P).mp (holder_gamma_no_ade (clearDenomMvPoly P) hP_clear)

private lemma deriv_ofReal_comp (f : ℝ → ℝ) (x : ℝ) :
    _root_.deriv (fun t : ℝ => (f t : ℂ)) x = ((_root_.deriv f x : ℝ) : ℂ) := by
  by_cases hd : DifferentiableAt ℝ f x
  · exact hd.hasDerivAt.ofReal_comp.deriv
  · have hnd : ¬ DifferentiableAt ℝ (fun t : ℝ => (f t : ℂ)) x := by
      intro hdc
      have hre : (fun t : ℝ => Complex.reCLM ((f t : ℂ))) = f := by ext t; simp
      have hd' : DifferentiableAt ℝ f x := by
        rw [← hre]
        exact Complex.reCLM.differentiableAt.comp x hdc
      exact hd hd'
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd,
      Complex.ofReal_zero]

private lemma iteratedDeriv_ofReal_comp (f : ℝ → ℝ) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => (f t : ℂ)) = fun x : ℝ => ((iteratedDeriv j f x : ℝ) : ℂ) := by
  induction j with
  | zero => ext x; simp
  | succ j ih =>
    ext x
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_ofReal_comp]

/-- **Hölder's Theorem (1887) for `Real.Gamma` over `ℝ[u]`**:
`Real.Gamma` satisfies NO nonzero algebraic differential equation over `ℝ[u]`. -/
theorem holder_realGamma_no_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℝ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val Real.Gamma u)
        (MvPolynomial.map (Polynomial.evalRingHom u) P) = 0) :
    P = 0 := by
  let φ : Polynomial ℝ →+* Polynomial ℂ := Polynomial.mapRingHom Complex.ofRealHom
  let PC : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := MvPolynomial.map φ P
  have hGam : (fun t : ℝ => Complex.Gamma (t : ℂ)) = fun t : ℝ => (Real.Gamma t : ℂ) := by
    ext t; exact Complex.Gamma_ofReal t
  have hPC : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun x : ℝ => Complex.Gamma (x : ℂ)) u)
        (evalU PC (u : ℂ)) = 0 := by
    filter_upwards [hP] with u hu
    have hmap_eq : evalU PC (u : ℂ) =
        MvPolynomial.map Complex.ofRealHom (MvPolynomial.map (Polynomial.evalRingHom u) P) := by
      simp only [evalU, PC, MvPolynomial.map_map]
      refine congrArg (fun fn => MvPolynomial.map fn P) ?_
      apply Polynomial.ringHom_ext
      · intro c; simp [φ]
      · simp [φ]
    have h_iter : (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun x : ℝ => Complex.Gamma (x : ℂ)) u) =
        Complex.ofRealHom ∘ (fun j : Fin (r + 1) => iteratedDeriv j.val Real.Gamma u) := by
      funext j
      rw [hGam, iteratedDeriv_ofReal_comp]
      rfl
    rw [hmap_eq, h_iter, ← MvPolynomial.map_eval, hu, map_zero]
  have hPC0 : PC = 0 := holder_gamma_no_ade PC hPC
  have hφ_inj : Function.Injective φ := Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  exact MvPolynomial.map_injective φ hφ_inj (hPC0.trans (map_zero _).symm)

end
end PakPrimes.HolderGamma
