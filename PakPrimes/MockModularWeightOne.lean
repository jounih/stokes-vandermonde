module

public import PakPrimes.HigherOrderStokes
public import Mathlib.Data.Nat.Nth
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Weight-1 Mock Modular / Eichler-Integral Differential Transcendence

End-to-end Tier-1 Lean 4.36.0 formalization of Regime III (weight `k = 1`) of the
Modular–Mock Differential Dichotomy directly on top of `PakPrimes.HigherOrderStokes`
(zero extra hypotheses, axioms strictly `[propext, Classical.choice, Quot.sound]`):

1. **Exact Split Weight-1 Borel Transform (`eichlerBorel`, `eichlerWeightOne_borelData`)**:
   For any Fourier coefficient sequence `c : ℕ → ℂ` with `∑ ‖c n‖ e^{-2π(n+1)} < ∞`
   (in particular any sub-exponential bound `‖c n‖ ≤ C e^{α n}`, `α < 2π`) and infinitely
   many nonzero entries, the split Borel transform
   `φ_g(ξ) = ∑_{n ≥ 0} c_n e^{-(2π(n+1) + ξ)} / (2π(n+1) + ξ)`
   instantiates `HigherOrderBorelData` along the rotated ray `θ₀ = π` with **pure simple poles**
   at `ξ_k = -2π(n_k + 1)` and exact residues `c(n_k) ≠ 0`.
2. **Exact Stieltjes–Laplace Identity & All-Orders Watson's Lemma (`eichlerNormalized_eq_laplace`,
   `eichlerNormalized_hasAsympExp`)**:
   For every `u > 0`, `u⁻¹ I_g(u) = ∫_0^∞ e^{-u ξ} φ_g(ξ) dξ` where
   `I_g(u) = ∫_1^∞ (∑_{n ≥ 0} c_n e^{-2π(n+1) s}) (1 + s/u)⁻¹ ds`,
   and every derivative `iteratedDeriv j (u⁻¹ I_g(u))` satisfies `HasAsympExp` against
   `d_u^[j] (formalSeries φ_g)`.
3. **General Weight-1 Eichler-Integral D-Transcendence (`eichlerWeightOne_no_rat_ade`,
   `eichlerWeightOne_integral_no_rat_ade`, `eichlerWeightOne_no_poly_ade`,
   `eichlerWeightOne_no_autonomous_ade`)**:
   Transfers differential transcendence from `u⁻¹ I_g(u)` directly to `I_g(u)` itself via the
   invertible differential substitution `Y_0 ↦ u Z_0`, `Y_{k+1} ↦ u Z_{k+1} + (k+1) Z_k`.
4. **Zero-Hypothesis Tier-1 Arithmetic Witnesses**:
   - **KRY / Duke–Li Weight-1 Eisenstein Shadow** (`kryDivisorCoeff`, `kryEisenstein_no_rat_ade`):
     `c_n = ∑_{d ∣ n+1} χ_{-3}(d)`, proved nonvanishing (`= 1`) on all `3^k - 1`.
   - **Weight-1 Cusp-Form Shadow `g₂₃(τ) = η(τ) η(23τ)`** (`cuspG23Coeff`, `cuspG23_no_rat_ade`):
     `c_n = (r_{x²+xy+6y²}(n+1) - r_{2x²+xy+3y²}(n+1)) / 2`, proved nonvanishing on all `23^{2k} - 1`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.MockModularWeightOne

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Frequencies `ω_n = 2π (n + 1)` -/

/-- Frequencies `ω_n = 2π (n + 1)` of the `q`-expansion `q^{n+1} = e^{-2π (n+1) s}` at `τ = i s`. -/
@[expose] def freq (n : ℕ) : ℝ := 2 * Real.pi * ((n : ℝ) + 1)

lemma two_pi_le_freq (n : ℕ) : 2 * Real.pi ≤ freq n := by
  unfold freq
  have h : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith [Real.pi_pos]

lemma freq_pos (n : ℕ) : 0 < freq n :=
  lt_of_lt_of_le (by positivity) (two_pi_le_freq n)

lemma one_le_freq (n : ℕ) : 1 ≤ freq n := by
  linarith [two_pi_le_freq n, Real.two_le_pi]

lemma freq_strictMono : StrictMono freq := fun a b hab => by
  unfold freq
  have : (a : ℝ) < b := by exact_mod_cast hab
  nlinarith [Real.pi_pos]

lemma freq_injective : Function.Injective freq := freq_strictMono.injective

lemma nat_le_freq (n : ℕ) : (n : ℝ) + 1 ≤ freq n := by
  unfold freq
  have h : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith [Real.two_le_pi]

/-! ### 2. The simple-pole series `ψ_a(z) = ∑ a_n / (ω_n + z)` -/

/-- Simple-pole series `ψ_a(z) = ∑_{n ≥ 0} a_n / (ω_n + z)` with poles at `-ω_n`. -/
@[expose] def poleSeries (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n / ((freq n : ℂ) + z)

private lemma term_norm_le {a : ℕ → ℂ} {n : ℕ} {z : ℂ} (h : 1 ≤ ‖(freq n : ℂ) + z‖) :
    ‖a n / ((freq n : ℂ) + z)‖ ≤ ‖a n‖ := by
  rw [norm_div]
  have hpos : 0 < ‖(freq n : ℂ) + z‖ := lt_of_lt_of_le one_pos h
  rw [div_le_iff₀ hpos]
  nlinarith [norm_nonneg (a n)]

private lemma exists_tail (w : ℂ) (R : ℝ) :
    ∃ N : ℕ, ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w R → 1 ≤ ‖(freq (k + N) : ℂ) + z‖ := by
  refine ⟨Nat.ceil (‖w‖ + R), fun k z hz => ?_⟩
  have hN : ‖w‖ + R ≤ (Nat.ceil (‖w‖ + R) : ℝ) := Nat.le_ceil _
  have hz' : ‖z‖ < ‖w‖ + R := by
    have hball : ‖z - w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ < R + ‖w‖ := by linarith
      _ = ‖w‖ + R := by ring
  have hf := nat_le_freq (k + Nat.ceil (‖w‖ + R))
  push_cast at hf
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htri := norm_sub_le ((freq (k + Nat.ceil (‖w‖ + R)) : ℂ) + z) z
  rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg
    (freq_pos _).le] at htri
  linarith

lemma poleSeries_summable {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (z : ℂ) :
    Summable (fun n => a n / ((freq n : ℂ) + z)) := by
  obtain ⟨N, hN⟩ := exists_tail z 1
  refine (summable_nat_add_iff N).1 ?_
  refine ((summable_nat_add_iff N).2 ha).of_norm_bounded fun k => ?_
  exact term_norm_le (hN k z (Metric.mem_ball_self one_pos))

lemma poleSeries_analyticAt {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {w : ℂ}
    (hw : ∀ n, a n ≠ 0 → (freq n : ℂ) + w ≠ 0) : AnalyticAt ℂ (poleSeries a) w := by
  obtain ⟨N, hN⟩ := exists_tail w 1
  let head : ℂ → ℂ := fun z => ∑ n ∈ Finset.range N, a n / ((freq n : ℂ) + z)
  let tail : ℂ → ℂ := fun z => ∑' k : ℕ, a (k + N) / ((freq (k + N) : ℂ) + z)
  have htail_diff : DifferentiableOn ℂ tail (Metric.ball w 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun k : ℕ => ‖a (k + N)‖) ((summable_nat_add_iff N).2 ha) (fun k => ?_)
      Metric.isOpen_ball (fun k z hz => term_norm_le (hN k z hz))
    refine DifferentiableOn.div (differentiableOn_const _)
      ((differentiableOn_const _).add differentiableOn_id) fun z hz => ?_
    intro h0
    have h1 := hN k z hz
    rw [h0, norm_zero] at h1
    linarith
  have htail_ana : AnalyticAt ℂ tail w :=
    (htail_diff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self one_pos)
  have hhead_ana : AnalyticAt ℂ head w := by
    refine Finset.analyticAt_fun_sum (Finset.range N) fun n _ => ?_
    by_cases han : a n = 0
    · simp only [han, zero_div]
      exact analyticAt_const
    · exact AnalyticAt.div analyticAt_const (analyticAt_const.add analyticAt_id) (hw n han)
  have heq : ∀ z ∈ Metric.ball w 1, poleSeries a z = head z + tail z := by
    intro z _
    exact ((poleSeries_summable ha z).sum_add_tsum_nat_add N).symm
  have hev : poleSeries a =ᶠ[𝓝 w] fun z => head z + tail z :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)) heq
  exact (hhead_ana.add htail_ana).congr hev.symm

lemma poleSeries_split {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (m : ℕ) (z : ℂ) :
    poleSeries a z = a m / ((freq m : ℂ) + z) + poleSeries (Function.update a m 0) z := by
  classical
  unfold poleSeries
  rw [(poleSeries_summable ha z).tsum_eq_add_tsum_ite m]
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hnm : n = m
  · subst hnm; simp
  · simp [hnm]

lemma summable_update {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (m : ℕ) :
    Summable (fun n => ‖Function.update a m 0 n‖) := by
  refine ha.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  by_cases hnm : n = m
  · subst hnm; simp
  · rw [Function.update_of_ne hnm]

/-! ### 3. The weight-1 split Eichler Borel transform `φ_g` -/

/-- **Exact Borel transform of the split weight-1 Eichler/Stieltjes integral**:
`φ_g(ξ) = ∑_{n ≥ 0} c_n e^{-(ω_n + ξ)} / (ω_n + ξ)`, `ω_n = 2π(n+1)`. -/
@[expose] def eichlerBorel (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, c n * Complex.exp (-((freq n : ℂ) + z)) / ((freq n : ℂ) + z)

/-- Exponentially damped coefficients `a_n = c_n e^{-ω_n}`. -/
@[expose] def dampedCoeff (c : ℕ → ℂ) (n : ℕ) : ℂ := c n * Complex.exp (-(freq n : ℂ))

lemma norm_dampedCoeff (c : ℕ → ℂ) (n : ℕ) :
    ‖dampedCoeff c n‖ = ‖c n‖ * Real.exp (-freq n) := by
  rw [dampedCoeff, norm_mul, Complex.norm_exp]
  simp

lemma summable_dampedCoeff {c : ℕ → ℂ} (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) :
    Summable (fun n => ‖dampedCoeff c n‖) := by
  simpa only [norm_dampedCoeff] using hc

lemma dampedCoeff_ne_zero_iff {c : ℕ → ℂ} {n : ℕ} : dampedCoeff c n ≠ 0 ↔ c n ≠ 0 := by
  simp [dampedCoeff, Complex.exp_ne_zero]

lemma eichlerBorel_eq (c : ℕ → ℂ) (z : ℂ) :
    eichlerBorel c z = Complex.exp (-z) * poleSeries (dampedCoeff c) z := by
  unfold eichlerBorel poleSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [dampedCoeff, neg_add, Complex.exp_add]
  ring

/-- Enumeration `k ↦ n_k` (strictly increasing) of the indices of the nonzero coefficients. -/
@[expose] def suppIdx (c : ℕ → ℂ) : ℕ → ℕ := Nat.nth (fun n => c n ≠ 0)

/-- Pole frequencies `ω_{n_k} = 2π (n_k + 1)` (poles of `φ_g` at `-ω_{n_k}`). -/
@[expose] def poleFreq (c : ℕ → ℂ) (k : ℕ) : ℝ := freq (suppIdx c k)

private lemma exp_I_pi : Complex.exp (I * (Real.pi : ℂ)) = -1 := by
  rw [mul_comm]; exact Complex.exp_pi_mul_I

private lemma exp_neg_I_pi : Complex.exp (-I * (Real.pi : ℂ)) = -1 := by
  rw [neg_mul, Complex.exp_neg, exp_I_pi]; norm_num

private lemma norm_exp_I_real (t : ℝ) : ‖Complex.exp (I * (t : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I t

private lemma exp_I_real_im (t : ℝ) : (Complex.exp (I * (t : ℂ))).im = Real.sin t := by
  rw [mul_comm]; exact Complex.exp_ofReal_mul_I_im t

private lemma norm_freq_add_ge (n : ℕ) {d : ℂ} (hd : ‖d‖ = 1) (v : ℝ) :
    freq n * |d.im| ≤ ‖(freq n : ℂ) + d * v‖ := by
  have hns : d.re * d.re + d.im * d.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hd]; norm_num
  rw [Complex.norm_def]
  refine Real.le_sqrt_of_sq_le ?_
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.add_im, Complex.mul_im, zero_add]
  have key : (freq n + d.re * v) * (freq n + d.re * v) + d.im * v * (d.im * v) =
      (v + freq n * d.re) ^ 2 + (freq n * d.im) ^ 2 := by
    linear_combination (v ^ 2 - freq n ^ 2) * hns
  rw [key, mul_pow, sq_abs]
  nlinarith [sq_nonneg (v + freq n * d.re)]

private lemma eichlerBorel_pull_bound (c : ℕ → ℂ)
    (ha : Summable (fun n => ‖dampedCoeff c n‖)) {d : ℂ} (hd : ‖d‖ = 1)
    (hdim : 1 / 2 ≤ |d.im|) (v : ℝ) (hv : 0 ≤ v) :
    ‖Minor.pull d (eichlerBorel c) v‖ ≤ (∑' n, ‖dampedCoeff c n‖) * Real.exp (1 * v) := by
  rw [Minor.pull, norm_mul, hd, one_mul, eichlerBorel_eq, norm_mul]
  have hexp : ‖Complex.exp (-(d * (v : ℂ)))‖ ≤ Real.exp (1 * v) := by
    rw [Complex.norm_exp, one_mul]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    rw [norm_neg, norm_mul, hd, one_mul, Complex.norm_real, Real.norm_of_nonneg hv]
  have hterm : ∀ n, ‖dampedCoeff c n / ((freq n : ℂ) + d * v)‖ ≤ ‖dampedCoeff c n‖ := by
    intro n
    refine term_norm_le ?_
    have h1 := norm_freq_add_ge n hd v
    have h2 : freq n / 2 ≤ freq n * |d.im| := by
      nlinarith [freq_pos n]
    linarith [two_pi_le_freq n, Real.two_le_pi]
  have hsumm : Summable (fun n => ‖dampedCoeff c n / ((freq n : ℂ) + d * v)‖) :=
    ha.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hψ : ‖poleSeries (dampedCoeff c) (d * v)‖ ≤ ∑' n, ‖dampedCoeff c n‖ :=
    (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_le_tsum hterm ha)
  calc ‖Complex.exp (-(d * (v : ℂ)))‖ * ‖poleSeries (dampedCoeff c) (d * v)‖
      ≤ Real.exp (1 * v) * ∑' n, ‖dampedCoeff c n‖ :=
        mul_le_mul hexp hψ (norm_nonneg _) (Real.exp_pos _).le
    _ = (∑' n, ‖dampedCoeff c n‖) * Real.exp (1 * v) := by ring

/-- **`eichlerWeightOne_borelData`**: for ANY coefficient sequence `c` with
`∑ ‖c n‖ e^{-2π(n+1)} < ∞` and infinitely many nonzero entries, the exact weight-1 split Eichler
Borel transform `φ_g` satisfies `HigherOrderBorelData` along the rotated ray `θ₀ = π`, with
PURE SIMPLE POLES at `-2π (n_k + 1)` and residues `c (n_k) ≠ 0`. -/
def eichlerWeightOne_borelData (c : ℕ → ℂ)
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (hinf : {n : ℕ | c n ≠ 0}.Infinite) :
    HigherOrderBorelData (eichlerBorel c) Real.pi (poleFreq c) (fun _ => 1)
      (fun k s => if s = 1 then c (suppIdx c k) else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := freq_pos _
  ω_mono := freq_strictMono.comp (Nat.nth_strictMono hinf)
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun k => by
    simpa [suppIdx] using Nat.nth_mem_of_infinite hinf k
  analyticOn := by
    have ha := summable_dampedCoeff hc
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hz' := hz.2
    rw [exp_neg_I_pi] at hz'
    have hψ : AnalyticAt ℂ (poleSeries (dampedCoeff c)) z := by
      refine poleSeries_analyticAt ha fun n hn h0 => hz' ?_
      have hcn : c n ≠ 0 := dampedCoeff_ne_zero_iff.1 hn
      have hmem : n ∈ Set.range (suppIdx c) := by
        rw [suppIdx, Nat.range_nth_of_infinite hinf]; exact hcn
      obtain ⟨k, hk⟩ := hmem
      refine ⟨k, ?_⟩
      simp only [poleFreq, hk]
      linear_combination h0
    have hfun : eichlerBorel c = fun z => Complex.exp (-z) * poleSeries (dampedCoeff c) z :=
      funext (eichlerBorel_eq c)
    rw [hfun]
    exact AnalyticAt.mul (by fun_prop) hψ
  pole_principalPart := fun k => by
    have ha := summable_dampedCoeff hc
    have hcm : c (suppIdx c k) ≠ 0 := Nat.nth_mem_of_infinite hinf k
    set m := suppIdx c k with hm
    set a := dampedCoeff c with ha_def
    set ω : ℂ := (freq m : ℂ) with hω
    have hpole : Complex.exp (I * (Real.pi : ℂ)) * ((poleFreq c k : ℝ) : ℂ) = -ω := by
      rw [exp_I_pi, hω, poleFreq, ← hm]; ring
    rw [hpole]
    have hψ'_an : AnalyticAt ℂ (poleSeries (Function.update a m 0)) (-ω) := by
      refine poleSeries_analyticAt (summable_update ha m) fun n hn => ?_
      by_cases hnm : n = m
      · subst hnm; simp at hn
      · intro h0
        apply hnm
        apply freq_injective
        have : (freq n : ℂ) = (freq m : ℂ) := by linear_combination h0
        exact_mod_cast this
    have hd : HasDerivAt (fun z : ℂ => Complex.exp (-z)) (-Complex.exp ω) (-ω) := by
      have := ((hasDerivAt_id (-ω)).neg).cexp
      simpa using this
    have hslope := hasDerivAt_iff_tendsto_slope.mp hd
    refine ⟨Complex.exp ω * poleSeries (Function.update a m 0) (-ω) + a m * (-Complex.exp ω), ?_⟩
    have hcont : ContinuousAt (fun z => Complex.exp (-z) * poleSeries (Function.update a m 0) z)
        (-ω) := ContinuousAt.mul (by fun_prop) hψ'_an.continuousAt
    have h1 := hcont.continuousWithinAt (s := {-ω}ᶜ) |>.tendsto
    have h1' : Tendsto (fun z => Complex.exp (-z) * poleSeries (Function.update a m 0) z)
        (𝓝[≠] (-ω)) (𝓝 (Complex.exp ω * poleSeries (Function.update a m 0) (-ω))) := by
      simpa using h1
    have hlim := h1'.add (hslope.const_mul (a m))
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    have hz' : z + ω ≠ 0 := by
      intro h0; apply hz; simp only [Set.mem_singleton_iff]; linear_combination h0
    have hz'' : (freq m : ℂ) + z ≠ 0 := by rw [← hω, add_comm]; exact hz'
    have hcm' : c m = a m * Complex.exp ω := by
      rw [ha_def, dampedCoeff, mul_assoc, ← Complex.exp_add, hω, neg_add_cancel,
        Complex.exp_zero, mul_one]
    simp only [eichlerBorel_eq, slope_def_field, Finset.Icc_self, Finset.sum_singleton,
      ↓reduceIte, pow_one]
    rw [poleSeries_split ha m z, hcm', sub_neg_eq_add, ← hω]
    rw [← hω] at hz''
    field_simp
    ring
  expType_plus := by
    have ha := summable_dampedCoeff hc
    refine ⟨∑' n, ‖dampedCoeff c n‖, 1, tsum_nonneg (fun _ => norm_nonneg _), zero_le_one,
      fun v hv => eichlerBorel_pull_bound c ha (norm_exp_I_real _) ?_ v hv⟩
    rw [exp_I_real_im, add_comm, Real.sin_add_pi, Real.sin_pi_div_six, abs_neg,
      abs_of_pos (by norm_num)]
  expType_minus := by
    have ha := summable_dampedCoeff hc
    refine ⟨∑' n, ‖dampedCoeff c n‖, 1, tsum_nonneg (fun _ => norm_nonneg _), zero_le_one,
      fun v hv => eichlerBorel_pull_bound c ha (norm_exp_I_real _) ?_ v hv⟩
    rw [exp_I_real_im, Real.sin_pi_sub, Real.sin_pi_div_six, abs_of_pos (by norm_num)]

/-- **Formal Borel-level weight-1 theorem**: the formal Laplace series of `φ_g` satisfies NO
nonzero non-autonomous rational differential equation over `ℂ(u)`. -/
theorem eichlerWeightOne_formal_no_rat_ade (c : ℕ → ℂ)
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (hinf : {n : ℕ | c n ≠ 0}.Infinite)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (eichlerBorel c)) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade (eichlerWeightOne_borelData c hc hinf) P hP

/-! ### 4. Growth & Subsequence Convenience Lemmas -/

/-- Any strictly increasing subsequence of nonzero coefficients witnesses `{n | c n ≠ 0}.Infinite`. -/
lemma infinite_support_of_subseq {c : ℕ → ℂ} (idx : ℕ → ℕ) (hmono : StrictMono idx)
    (hne : ∀ k, c (idx k) ≠ 0) : {n : ℕ | c n ≠ 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem hmono.injective fun k => hne k

/-- Sub-exponential growth `‖c n‖ ≤ C e^{α n}` with `α < 2π` implies `∑ ‖c n‖ e^{-2π(n+1)} < ∞`. -/
lemma summable_of_exp_bound {c : ℕ → ℂ} {C α : ℝ} (hα : α < 2 * Real.pi)
    (hC : ∀ n : ℕ, ‖c n‖ ≤ C * Real.exp (α * (n : ℝ))) :
    Summable (fun n : ℕ => ‖c n‖ * Real.exp (-freq n)) := by
  have hr_pos : 0 < Real.exp (α - 2 * Real.pi) := Real.exp_pos _
  have hr_lt : Real.exp (α - 2 * Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => (max C 0 * Real.exp (-2 * Real.pi)) *
      (Real.exp (α - 2 * Real.pi)) ^ n) :=
    (summable_geometric_of_lt_one hr_pos.le hr_lt).mul_left _
  refine hgeom.of_nonneg_of_le (fun _ => by positivity) fun n => ?_
  have hC' : ‖c n‖ ≤ max C 0 * Real.exp (α * (n : ℝ)) :=
    (hC n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hexp_eq : Real.exp (α * (n : ℝ)) * Real.exp (-freq n) =
      Real.exp (-2 * Real.pi) * (Real.exp (α - 2 * Real.pi)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold freq
    ring
  calc ‖c n‖ * Real.exp (-freq n)
      ≤ (max C 0 * Real.exp (α * (n : ℝ))) * Real.exp (-freq n) :=
        mul_le_mul_of_nonneg_right hC' (Real.exp_pos _).le
    _ = max C 0 * (Real.exp (α * (n : ℝ)) * Real.exp (-freq n)) := by ring
    _ = (max C 0 * Real.exp (-2 * Real.pi)) * (Real.exp (α - 2 * Real.pi)) ^ n := by
        rw [hexp_eq]; ring

/-- Polynomial growth `‖c n‖ ≤ C (n + 1)^d` implies `∑ ‖c n‖ e^{-2π(n+1)} < ∞`. -/
lemma summable_of_poly_bound {c : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (hC : ∀ n : ℕ, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ d) :
    Summable (fun n : ℕ => ‖c n‖ * Real.exp (-freq n)) := by
  refine summable_of_exp_bound (C := max C 0 * (d.factorial : ℝ) * Real.exp 1) (α := 1)
    (by linarith [Real.two_le_pi]) fun n => ?_
  have h1 : ((n : ℝ) + 1) ^ d ≤ (d.factorial : ℝ) * Real.exp ((n : ℝ) + 1) := by
    have hle := Real.pow_div_factorial_le_exp (x := (n : ℝ) + 1) (by positivity) d
    have hfac : (0 : ℝ) < (d.factorial : ℝ) := by positivity
    rw [div_le_iff₀ hfac] at hle
    linarith
  have h2 : Real.exp ((n : ℝ) + 1) = Real.exp 1 * Real.exp (1 * (n : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ d := hC n
    _ ≤ max C 0 * ((n : ℝ) + 1) ^ d :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ((d.factorial : ℝ) * Real.exp ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    _ = max C 0 * (d.factorial : ℝ) * Real.exp 1 * Real.exp (1 * (n : ℝ)) := by
        rw [h2]; ring

/-! ### 5. Exact Split Stieltjes / Eichler Integral & Laplace Transform Identity -/

/-- The weight-1 shadow `q`-series evaluated along the positive imaginary axis `τ = i s`:
`g(i s) = ∑_{n ≥ 0} c_n e^{-2π(n+1) s}`. -/
@[expose] def shadowSeries (c : ℕ → ℂ) (s : ℝ) : ℂ :=
  ∑' n : ℕ, c n * Complex.exp (-(freq n : ℂ) * (s : ℂ))

/-- The split weight-1 Stieltjes / Eichler integral:
`I_g(u) = ∫_1^∞ g(i s) / (1 + s / u) ds`. -/
@[expose] def eichlerIntegral (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∫ s in Ioi (1 : ℝ), shadowSeries c s / (1 + (s : ℂ) / (u : ℂ))

/-- Normalized Eichler integral `u⁻¹ I_g(u)`, equal to the exact Laplace transform of `φ_g`
for `u > 0`. -/
@[expose] def eichlerNormalized (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  (u : ℂ)⁻¹ * eichlerIntegral c u

/-- Exact Laplace transform `L_g(u) = ∫_0^∞ e^{-u ξ} φ_g(ξ) dξ`. -/
@[expose] def eichlerLaplace (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (ξ : ℂ)) * eichlerBorel c (ξ : ℂ)

private lemma integral_comp_add_right_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (a d : ℝ) :
    ∫ x in Ioi a, g (x + d) = ∫ x in Ioi (a + d), g x := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun x => (Ioi (a + d)).indicator g x) d]
  congr 1; funext x
  by_cases hx : a < x
  · have hx' : a + d < x + d := by linarith
    simp [Set.indicator_of_mem, hx, hx']
  · have hx' : ¬ a + d < x + d := by linarith
    simp [Set.indicator_of_notMem, hx, hx']

/-- Elementary 1D scalar Stieltjes–Laplace identity: for `a > 0` and `u > 0`,
`∫_1^∞ e^{-a s} / (u + s) ds = ∫_0^∞ e^{-u ξ} e^{-(a + ξ)} / (a + ξ) dξ`. -/
private lemma scalar_stieltjes_eq_laplace {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    ∫ s in Ioi (1 : ℝ), Complex.exp (-(a : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ)) =
      ∫ ξ in Ioi (0 : ℝ),
        Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
          (Complex.exp (-((a : ℂ) + (ξ : ℂ))) / ((a : ℂ) + (ξ : ℂ))) := by
  have hL :
      ∫ s in Ioi (1 : ℝ), Complex.exp (-(a : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ)) =
        Complex.exp ((a : ℂ) * (u : ℂ)) *
          ∫ w in Ioi (a * (1 + u)), Complex.exp (-(w : ℂ)) / (w : ℂ) := by
    have h1 :
        ∫ s in Ioi (1 : ℝ), Complex.exp (-(a : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ)) =
          ∫ t in Ioi (1 + u),
            Complex.exp ((a : ℂ) * (u : ℂ)) * (Complex.exp (-(a : ℂ) * (t : ℂ)) / (t : ℂ)) := by
      rw [← integral_comp_add_right_Ioi
        (fun t : ℝ => Complex.exp ((a : ℂ) * (u : ℂ)) * (Complex.exp (-(a : ℂ) * (t : ℂ)) / (t : ℂ)))
        1 u]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [← mul_div_assoc, ← Complex.exp_add]
      congr 1
      · congr 1; push_cast; ring
      · push_cast; ring
    rw [h1, integral_const_mul]
    congr 1
    have h2 := integral_comp_mul_left_Ioi
      (fun w : ℝ => Complex.exp (-(w : ℂ)) / (w : ℂ)) (1 + u) ha
    have h3 : ∫ t in Ioi (1 + u), Complex.exp (-(a : ℂ) * (t : ℂ)) / (t : ℂ) =
        a • ∫ t in Ioi (1 + u), Complex.exp (-((a * t : ℝ) : ℂ)) / ((a * t : ℝ) : ℂ) := by
      rw [← integral_smul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [Complex.real_smul]
      have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
      push_cast
      field_simp [ha']
    rw [h3, h2, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hR :
      ∫ ξ in Ioi (0 : ℝ),
          Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (Complex.exp (-((a : ℂ) + (ξ : ℂ))) / ((a : ℂ) + (ξ : ℂ))) =
        Complex.exp ((a : ℂ) * (u : ℂ)) *
          ∫ w in Ioi ((u + 1) * a), Complex.exp (-(w : ℂ)) / (w : ℂ) := by
    have h1 :
        ∫ ξ in Ioi (0 : ℝ),
            Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
              (Complex.exp (-((a : ℂ) + (ξ : ℂ))) / ((a : ℂ) + (ξ : ℂ))) =
          ∫ t in Ioi a,
            Complex.exp ((a : ℂ) * (u : ℂ)) *
              (Complex.exp (-((u + 1 : ℝ) : ℂ) * (t : ℂ)) / (t : ℂ)) := by
      have hshift := integral_comp_add_right_Ioi
        (fun t : ℝ => Complex.exp ((a : ℂ) * (u : ℂ)) *
          (Complex.exp (-((u + 1 : ℝ) : ℂ) * (t : ℂ)) / (t : ℂ))) 0 a
      rw [zero_add] at hshift
      rw [← hshift]
      refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
      rw [← mul_div_assoc, ← mul_div_assoc, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      · congr 1; push_cast; ring
      · push_cast; ring
    rw [h1, integral_const_mul]
    congr 1
    have hu1 : (0 : ℝ) < u + 1 := by linarith
    have h2 := integral_comp_mul_left_Ioi
      (fun w : ℝ => Complex.exp (-(w : ℂ)) / (w : ℂ)) a hu1
    have h3 : ∫ t in Ioi a, Complex.exp (-((u + 1 : ℝ) : ℂ) * (t : ℂ)) / (t : ℂ) =
        (u + 1) • ∫ t in Ioi a,
          Complex.exp (-(((u + 1) * t : ℝ) : ℂ)) / (((u + 1) * t : ℝ) : ℂ) := by
      rw [← integral_smul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [Complex.real_smul]
      have hu1' : (u : ℂ) + 1 ≠ 0 := by exact_mod_cast hu1.ne'
      push_cast
      field_simp [hu1']
    rw [h3, h2, smul_smul, mul_inv_cancel₀ hu1.ne', one_smul]
  rw [hL, hR]
  congr 2
  rw [show a * (1 + u) = (u + 1) * a by ring]

/-- **Exact Split Stieltjes–Laplace Identity**: for any `c` with `∑ ‖c n‖ e^{-2π(n+1)} < ∞`
and every `u > 0`, `u⁻¹ I_g(u) = ∫_0^∞ e^{-u ξ} φ_g(ξ) dξ`. -/
theorem eichlerNormalized_eq_laplace {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) {u : ℝ} (hu : 0 < u) :
    eichlerNormalized c u = eichlerLaplace c u := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  -- Left-hand side: bring `u⁻¹` inside the integral and swap `∫` with `∑'`
  have hL_rew : eichlerNormalized c u =
      ∫ s in Ioi (1 : ℝ),
        ∑' n : ℕ, c n * (Complex.exp (-(freq n : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ))) := by
    rw [eichlerNormalized, eichlerIntegral, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hus : (u : ℂ) + (s : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < u + s := by linarith [Set.mem_Ioi.mp hs]
      exact_mod_cast hpos.ne'
    have hdiv : (u : ℂ)⁻¹ * (shadowSeries c s / (1 + (s : ℂ) / (u : ℂ))) =
        ((u : ℂ) + (s : ℂ))⁻¹ * shadowSeries c s := by
      field_simp [huC, hus]
    rw [hdiv, shadowSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_; ring
  have hL_int : ∀ n : ℕ, IntegrableOn
      (fun s : ℝ => c n * (Complex.exp (-(freq n : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ))))
      (Ioi (1 : ℝ)) := by
    intro n
    have hdom : IntegrableOn (fun s : ℝ => ‖c n‖ * Real.exp (-freq n * s)) (Ioi (1 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (a := -freq n) (by linarith [freq_pos n]) 1).const_mul ‖c n‖
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => ?_)
      have hpos : (0 : ℝ) < u + s := by linarith [Set.mem_Ioi.mp hs]
      exact_mod_cast hpos.ne'
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
      have hs1 : (1 : ℝ) < s := Set.mem_Ioi.mp hs
      have hus1 : (1 : ℝ) ≤ ‖(u : ℂ) + (s : ℂ)‖ := by
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
      rw [norm_mul, norm_div, Complex.norm_exp]
      have hre : (-(freq n : ℂ) * (s : ℂ)).re = -freq n * s := by simp
      rw [hre]
      calc ‖c n‖ * (Real.exp (-freq n * s) / ‖(u : ℂ) + (s : ℂ)‖)
          ≤ ‖c n‖ * (Real.exp (-freq n * s) / 1) := by
            gcongr
        _ = ‖c n‖ * Real.exp (-freq n * s) := by ring
  have hL_sum : Summable (fun n : ℕ => ∫ s in Ioi (1 : ℝ),
      ‖c n * (Complex.exp (-(freq n : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ)))‖) := by
    refine hc.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) fun n => ?_
    have hdom : IntegrableOn (fun s : ℝ => ‖c n‖ * Real.exp (-freq n * s)) (Ioi (1 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (a := -freq n) (by linarith [freq_pos n]) 1).const_mul ‖c n‖
    have hle : ∫ s in Ioi (1 : ℝ),
          ‖c n * (Complex.exp (-(freq n : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ)))‖ ≤
        ∫ s in Ioi (1 : ℝ), ‖c n‖ * Real.exp (-freq n * s) := by
      refine setIntegral_mono_on (hL_int n).norm hdom measurableSet_Ioi fun s hs => ?_
      have hs1 : (1 : ℝ) < s := Set.mem_Ioi.mp hs
      have hus1 : (1 : ℝ) ≤ ‖(u : ℂ) + (s : ℂ)‖ := by
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
      rw [norm_mul, norm_div, Complex.norm_exp]
      have hre : (-(freq n : ℂ) * (s : ℂ)).re = -freq n * s := by simp
      rw [hre]
      calc ‖c n‖ * (Real.exp (-freq n * s) / ‖(u : ℂ) + (s : ℂ)‖)
          ≤ ‖c n‖ * (Real.exp (-freq n * s) / 1) := by gcongr
        _ = ‖c n‖ * Real.exp (-freq n * s) := by ring
    have heval : ∫ s in Ioi (1 : ℝ), ‖c n‖ * Real.exp (-freq n * s) =
        ‖c n‖ * (Real.exp (-freq n) / freq n) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (a := -freq n) (by linarith [freq_pos n]) 1,
        mul_one]
      ring
    refine hle.trans (heval.trans_le ?_)
    have h1 := one_le_freq n
    have hdiv : Real.exp (-freq n) / freq n ≤ Real.exp (-freq n) :=
      div_le_self (Real.exp_pos _).le h1
    exact mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)
  have hL_swap : eichlerNormalized c u =
      ∑' n : ℕ, c n * ∫ s in Ioi (1 : ℝ),
        Complex.exp (-(freq n : ℂ) * (s : ℂ)) / ((u : ℂ) + (s : ℂ)) := by
    rw [hL_rew, ← integral_tsum_of_summable_integral_norm hL_int hL_sum]
    refine tsum_congr fun n => ?_
    rw [integral_const_mul]
  -- Right-hand side: swap `∫` with `∑'`
  have hR_rew : eichlerLaplace c u =
      ∫ ξ in Ioi (0 : ℝ), ∑' n : ℕ,
        c n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
          (Complex.exp (-((freq n : ℂ) + (ξ : ℂ))) / ((freq n : ℂ) + (ξ : ℂ)))) := by
    rw [eichlerLaplace]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    rw [eichlerBorel, ← tsum_mul_left]
    refine tsum_congr fun n => ?_; ring
  have hR_int : ∀ n : ℕ, IntegrableOn
      (fun ξ : ℝ => c n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
        (Complex.exp (-((freq n : ℂ) + (ξ : ℂ))) / ((freq n : ℂ) + (ξ : ℂ)))))
      (Ioi (0 : ℝ)) := by
    intro n
    have hdom : IntegrableOn (fun ξ : ℝ => (‖c n‖ * Real.exp (-freq n)) * Real.exp (-u * ξ))
        (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (a := -u) (by linarith) 0).const_mul _
    refine hdom.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine continuousOn_const.mul (ContinuousOn.mul (by fun_prop)
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun ξ hξ => ?_))
      have hpos : (0 : ℝ) < freq n + ξ := by linarith [freq_pos n, Set.mem_Ioi.mp hξ]
      exact_mod_cast hpos.ne'
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ξ hξ => ?_)
      have hξ0 : (0 : ℝ) < ξ := Set.mem_Ioi.mp hξ
      have hden : (1 : ℝ) ≤ ‖(freq n : ℂ) + (ξ : ℂ)‖ := by
        rw [← Complex.ofReal_add, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [freq_pos n])]
        linarith [one_le_freq n]
      rw [norm_mul, norm_mul, norm_div, Complex.norm_exp, Complex.norm_exp]
      have hr1 : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
      have hr2 : (-((freq n : ℂ) + (ξ : ℂ))).re = -freq n + -ξ := by simp; ring
      rw [hr1, hr2, Real.exp_add]
      have heξ : Real.exp (-ξ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc ‖c n‖ * (Real.exp (-u * ξ) * (Real.exp (-freq n) * Real.exp (-ξ) /
              ‖(freq n : ℂ) + (ξ : ℂ)‖))
          ≤ ‖c n‖ * (Real.exp (-u * ξ) * (Real.exp (-freq n) * 1 / 1)) := by
            gcongr
        _ = (‖c n‖ * Real.exp (-freq n)) * Real.exp (-u * ξ) := by ring
  have hR_sum : Summable (fun n : ℕ => ∫ ξ in Ioi (0 : ℝ),
      ‖c n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
        (Complex.exp (-((freq n : ℂ) + (ξ : ℂ))) / ((freq n : ℂ) + (ξ : ℂ))))‖) := by
    refine (hc.mul_right (1 / u)).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) fun n => ?_
    have hdom : IntegrableOn (fun ξ : ℝ => (‖c n‖ * Real.exp (-freq n)) * Real.exp (-u * ξ))
        (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (a := -u) (by linarith) 0).const_mul _
    have hle : ∫ ξ in Ioi (0 : ℝ),
          ‖c n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (Complex.exp (-((freq n : ℂ) + (ξ : ℂ))) / ((freq n : ℂ) + (ξ : ℂ))))‖ ≤
        ∫ ξ in Ioi (0 : ℝ), (‖c n‖ * Real.exp (-freq n)) * Real.exp (-u * ξ) := by
      refine setIntegral_mono_on (hR_int n).norm hdom measurableSet_Ioi fun ξ hξ => ?_
      have hξ0 : (0 : ℝ) < ξ := Set.mem_Ioi.mp hξ
      have hden : (1 : ℝ) ≤ ‖(freq n : ℂ) + (ξ : ℂ)‖ := by
        rw [← Complex.ofReal_add, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [freq_pos n])]
        linarith [one_le_freq n]
      rw [norm_mul, norm_mul, norm_div, Complex.norm_exp, Complex.norm_exp]
      have hr1 : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
      have hr2 : (-((freq n : ℂ) + (ξ : ℂ))).re = -freq n + -ξ := by simp; ring
      rw [hr1, hr2, Real.exp_add]
      have heξ : Real.exp (-ξ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc ‖c n‖ * (Real.exp (-u * ξ) * (Real.exp (-freq n) * Real.exp (-ξ) /
              ‖(freq n : ℂ) + (ξ : ℂ)‖))
          ≤ ‖c n‖ * (Real.exp (-u * ξ) * (Real.exp (-freq n) * 1 / 1)) := by gcongr
        _ = (‖c n‖ * Real.exp (-freq n)) * Real.exp (-u * ξ) := by ring
    refine hle.trans_eq ?_
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -u) (by linarith) 0]
    simp [div_eq_mul_inv]
  have hR_swap : eichlerLaplace c u =
      ∑' n : ℕ, c n * ∫ ξ in Ioi (0 : ℝ),
        Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
          (Complex.exp (-((freq n : ℂ) + (ξ : ℂ))) / ((freq n : ℂ) + (ξ : ℂ))) := by
    rw [hR_rew, ← integral_tsum_of_summable_integral_norm hR_int hR_sum]
    refine tsum_congr fun n => ?_
    rw [integral_const_mul]
  rw [hL_swap, hR_swap]
  refine tsum_congr fun n => ?_
  rw [scalar_stieltjes_eq_laplace (freq_pos n) hu]

/-! ### 6. Uniform Bound on `[0, ∞)`, Derivatives Under the Integral, and Watson's Lemma -/

/-- `φ_g(ξ)` is uniformly bounded on `[0, ∞)` by `∑' n, ‖c n‖ e^{-2π(n+1)}`. -/
lemma norm_eichlerBorel_real_le {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ‖eichlerBorel c (ξ : ℂ)‖ ≤ ∑' n, ‖c n‖ * Real.exp (-freq n) := by
  have hterm : ∀ n : ℕ,
      ‖c n * Complex.exp (-((freq n : ℂ) + (ξ : ℂ))) / ((freq n : ℂ) + (ξ : ℂ))‖ ≤
        ‖c n‖ * Real.exp (-freq n) := by
    intro n
    have hden : (1 : ℝ) ≤ ‖(freq n : ℂ) + (ξ : ℂ)‖ := by
      rw [← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by linarith [freq_pos n])]
      linarith [one_le_freq n]
    rw [norm_div, norm_mul, Complex.norm_exp]
    have hre : (-((freq n : ℂ) + (ξ : ℂ))).re = -freq n + -ξ := by simp; ring
    rw [hre, Real.exp_add]
    have heξ : Real.exp (-ξ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc ‖c n‖ * (Real.exp (-freq n) * Real.exp (-ξ)) / ‖(freq n : ℂ) + (ξ : ℂ)‖
        ≤ ‖c n‖ * (Real.exp (-freq n) * 1) / 1 := by gcongr
      _ = ‖c n‖ * Real.exp (-freq n) := by ring
  have hsumm : Summable (fun n : ℕ =>
      ‖c n * Complex.exp (-((freq n : ℂ) + (ξ : ℂ))) / ((freq n : ℂ) + (ξ : ℂ))‖) :=
    hc.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  exact (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_le_tsum hterm hc)

lemma eichlerBorel_analyticAt_nonneg {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    AnalyticAt ℂ (eichlerBorel c) (ξ : ℂ) := by
  have hfun : eichlerBorel c = fun z => Complex.exp (-z) * poleSeries (dampedCoeff c) z :=
    funext (eichlerBorel_eq c)
  rw [hfun]
  refine AnalyticAt.mul (by fun_prop) (poleSeries_analyticAt (summable_dampedCoeff hc) fun n _ => ?_)
  have hpos : (0 : ℝ) < freq n + ξ := by linarith [freq_pos n]
  exact_mod_cast hpos.ne'

lemma eichlerBorel_continuousOn_Ici {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) :
    ContinuousOn (fun ξ : ℝ => eichlerBorel c (ξ : ℂ)) (Ici (0 : ℝ)) := by
  intro ξ hξ
  exact ((eichlerBorel_analyticAt_nonneg hc (Set.mem_Ici.mp hξ)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

private lemma pow_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (m : ℕ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ξ ^ m * Real.exp (-a * ξ) ≤
      (m.factorial : ℝ) / (a / 2) ^ m * Real.exp (-(a / 2) * ξ) := by
  have ha2 : 0 < a / 2 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (x := (a / 2) * ξ) (by positivity) m
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  rw [div_le_iff₀ hfac, mul_pow] at h1
  have h2 : ξ ^ m ≤ (m.factorial : ℝ) / (a / 2) ^ m * Real.exp ((a / 2) * ξ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha2 m)]
    linarith
  calc ξ ^ m * Real.exp (-a * ξ)
      ≤ ((m.factorial : ℝ) / (a / 2) ^ m * Real.exp ((a / 2) * ξ)) * Real.exp (-a * ξ) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (m.factorial : ℝ) / (a / 2) ^ m * (Real.exp ((a / 2) * ξ) * Real.exp (-a * ξ)) := by ring
    _ = (m.factorial : ℝ) / (a / 2) ^ m * Real.exp (-(a / 2) * ξ) := by
        rw [← Real.exp_add]; congr 2; ring

private lemma integrableOn_pow_mul_exp_neg_Ioi (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun ξ : ℝ => ξ ^ m * Real.exp (-a * ξ)) (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn
      (fun ξ : ℝ => (m.factorial : ℝ) / (a / 2) ^ m * Real.exp (-(a / 2) * ξ)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (a := -(a / 2)) (by linarith) 0).const_mul _
  refine hdom.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ξ hξ => ?_)
  have hξ0 : 0 ≤ ξ := (Set.mem_Ioi.mp hξ).le
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_mul_exp_neg_le ha m hξ0

private lemma tendsto_pow_mul_exp_neg_atTop (m : ℕ) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun ξ : ℝ => ξ ^ m * Real.exp (-u * ξ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun ξ : ℝ => (m.factorial : ℝ) / (u / 2) ^ m * Real.exp (-(u / 2) * ξ))
      atTop (𝓝 0) := by
    have he : Tendsto (fun ξ : ℝ => Real.exp (-(u / 2) * ξ)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using he.const_mul ((m.factorial : ℝ) / (u / 2) ^ m)
  refine squeeze_zero' ?_ ?_ h0
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ξ hξ; positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ξ hξ
    exact pow_mul_exp_neg_le hu m hξ

/-- Gamma factorial integral: `∫_0^∞ ξ^m e^{-u ξ} dξ = m! / u^{m+1}` for `u > 0`. -/
private lemma integral_pow_mul_exp_neg_Ioi (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ ξ in Ioi (0 : ℝ), ξ ^ m * Real.exp (-u * ξ) = (m.factorial : ℝ) / u ^ (m + 1) := by
  induction m with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one]
    rw [integral_exp_mul_Ioi (a := -u) (by linarith) 0]
    simp [div_eq_mul_inv]
  | succ m ih =>
    let F : ℝ → ℝ := fun ξ => -(ξ ^ (m + 1) / u) * Real.exp (-u * ξ)
    let F' : ℝ → ℝ := fun ξ =>
      ξ ^ (m + 1) * Real.exp (-u * ξ) - (((m + 1 : ℕ) : ℝ) / u) * (ξ ^ m * Real.exp (-u * ξ))
    have hderiv : ∀ ξ ∈ Ici (0 : ℝ), HasDerivAt F (F' ξ) ξ := fun ξ _ => by
      have h1 : HasDerivAt (fun t : ℝ => -(t ^ (m + 1) / u))
          (-(((m + 1 : ℕ) : ℝ) * ξ ^ m / u)) ξ :=
        ((hasDerivAt_pow (m + 1) ξ).div_const u).neg
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-u * t))
          (Real.exp (-u * ξ) * (-u)) ξ := by
        simpa using ((hasDerivAt_id ξ).const_mul (-u)).exp
      have hmul := h1.mul h2
      convert hmul using 1
      dsimp only [F']
      field_simp [hu.ne']
      ring
    have hF_lim : Tendsto F atTop (𝓝 0) := by
      have h := (tendsto_pow_mul_exp_neg_atTop (m + 1) hu).const_mul (-(1 / u))
      simpa only [mul_zero] using h.congr fun ξ => by dsimp only [F]; ring
    have hF'_int : IntegrableOn F' (Ioi (0 : ℝ)) :=
      (integrableOn_pow_mul_exp_neg_Ioi (m + 1) hu).sub
        ((integrableOn_pow_mul_exp_neg_Ioi m hu).const_mul _)
    have h0 := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hF'_int hF_lim
    have hF0 : F 0 = 0 := by simp [F]
    rw [hF0, sub_zero] at h0
    have hsub : ∫ ξ in Ioi (0 : ℝ), F' ξ =
        (∫ ξ in Ioi (0 : ℝ), ξ ^ (m + 1) * Real.exp (-u * ξ)) -
          (((m + 1 : ℕ) : ℝ) / u) * ∫ ξ in Ioi (0 : ℝ), ξ ^ m * Real.exp (-u * ξ) := by
      dsimp only [F']
      rw [integral_sub (integrableOn_pow_mul_exp_neg_Ioi (m + 1) hu)
        ((integrableOn_pow_mul_exp_neg_Ioi m hu).const_mul _), integral_const_mul]
    rw [hsub] at h0
    have heq : ∫ ξ in Ioi (0 : ℝ), ξ ^ (m + 1) * Real.exp (-u * ξ) =
        (((m + 1 : ℕ) : ℝ) / u) * ∫ ξ in Ioi (0 : ℝ), ξ ^ m * Real.exp (-u * ξ) :=
      sub_eq_zero.mp h0
    rw [heq, ih, Nat.factorial_succ]
    push_cast
    rw [pow_succ, pow_succ]
    field_simp [hu.ne']
    ring

private lemma integral_pow_mul_cexp_neg_Ioi (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ ξ in Ioi (0 : ℝ), (ξ : ℂ) ^ m * Complex.exp (-(u : ℂ) * (ξ : ℂ)) =
      (m.factorial : ℂ) / (u : ℂ) ^ (m + 1) := by
  have hcast : (fun ξ : ℝ => (ξ : ℂ) ^ m * Complex.exp (-(u : ℂ) * (ξ : ℂ))) =
      fun ξ : ℝ => ((ξ ^ m * Real.exp (-u * ξ) : ℝ) : ℂ) := by
    funext ξ
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
    congr 2; push_cast; ring
  rw [hcast, integral_complex_ofReal, integral_pow_mul_exp_neg_Ioi m hu]
  push_cast; rfl

/-- The `j`-th differentiated Laplace integral `L_j(u) = ∫_0^∞ (-ξ)^j e^{-u ξ} φ_g(ξ) dξ`. -/
private def laplaceDeriv (c : ℕ → ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * eichlerBorel c (ξ : ℂ)

private lemma laplaceDeriv_integrable {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn
      (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * eichlerBorel c (ξ : ℂ))
      (Ioi (0 : ℝ)) := by
  set M := ∑' n, ‖c n‖ * Real.exp (-freq n)
  have hdom : IntegrableOn (fun ξ : ℝ => M * (ξ ^ j * Real.exp (-u * ξ))) (Ioi (0 : ℝ)) :=
    (integrableOn_pow_mul_exp_neg_Ioi j hu).const_mul M
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((by fun_prop : ContinuousOn (fun ξ : ℝ => (-(ξ : ℂ)) ^ j *
        Complex.exp (-(u : ℂ) * (ξ : ℂ))) (Ioi 0)).mul
      ((eichlerBorel_continuousOn_Ici hc).mono Ioi_subset_Ici_self))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ξ hξ => ?_)
    have hξ0 : 0 ≤ ξ := (Set.mem_Ioi.mp hξ).le
    rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hξ0,
      Complex.norm_exp]
    have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
    rw [hre]
    have hφ := norm_eichlerBorel_real_le hc hξ0
    calc ξ ^ j * Real.exp (-u * ξ) * ‖eichlerBorel c (ξ : ℂ)‖
        ≤ ξ ^ j * Real.exp (-u * ξ) * M := mul_le_mul_of_nonneg_left hφ (by positivity)
      _ = M * (ξ ^ j * Real.exp (-u * ξ)) := by ring

private lemma laplaceDeriv_hasDerivAt {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) (j : ℕ) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    HasDerivAt (laplaceDeriv c j) (laplaceDeriv c (j + 1) u₀) u₀ := by
  set M := ∑' n, ‖c n‖ * Real.exp (-freq n)
  let F : ℝ → ℝ → ℂ := fun u ξ =>
    (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * eichlerBorel c (ξ : ℂ)
  let F' : ℝ → ℝ → ℂ := fun u ξ =>
    (-(ξ : ℂ)) ^ (j + 1) * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * eichlerBorel c (ξ : ℂ)
  let bound : ℝ → ℝ := fun ξ => M * (ξ ^ (j + 1) * Real.exp (-(u₀ / 2) * ξ))
  have hs : Ioi (u₀ / 2) ∈ 𝓝 u₀ := Ioi_mem_nhds (by linarith)
  have hF_meas : ∀ᶠ u in 𝓝 u₀, AEStronglyMeasurable (F u) (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun u =>
      (((by fun_prop : ContinuousOn (fun ξ : ℝ => (-(ξ : ℂ)) ^ j *
          Complex.exp (-(u : ℂ) * (ξ : ℂ))) (Ioi 0)).mul
        ((eichlerBorel_continuousOn_Ici hc).mono Ioi_subset_Ici_self))).aestronglyMeasurable
        measurableSet_Ioi
  have hF_int : Integrable (F u₀) (volume.restrict (Ioi (0 : ℝ))) :=
    laplaceDeriv_integrable hc j hu₀
  have hF'_meas : AEStronglyMeasurable (F' u₀) (volume.restrict (Ioi (0 : ℝ))) :=
    (laplaceDeriv_integrable hc (j + 1) hu₀).aestronglyMeasurable
  have h_bound : ∀ᵐ ξ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ u ∈ Ioi (u₀ / 2), ‖F' u ξ‖ ≤ bound ξ := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ξ hξ u hu => ?_)
    have hξ0 : 0 ≤ ξ := (Set.mem_Ioi.mp hξ).le
    have hu_gt : u₀ / 2 < u := Set.mem_Ioi.mp hu
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hξ0,
      Complex.norm_exp]
    have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
    rw [hre]
    have hexp : Real.exp (-u * ξ) ≤ Real.exp (-(u₀ / 2) * ξ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hφ := norm_eichlerBorel_real_le hc hξ0
    calc ξ ^ (j + 1) * Real.exp (-u * ξ) * ‖eichlerBorel c (ξ : ℂ)‖
        ≤ ξ ^ (j + 1) * Real.exp (-(u₀ / 2) * ξ) * M := by
          gcongr
      _ = M * (ξ ^ (j + 1) * Real.exp (-(u₀ / 2) * ξ)) := by ring
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_pow_mul_exp_neg_Ioi (j + 1) (by positivity)).const_mul M
  have h_diff : ∀ᵐ ξ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ u ∈ Ioi (u₀ / 2), HasDerivAt (F · ξ) (F' u ξ) u := by
    refine Eventually.of_forall fun ξ u _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * (ξ : ℂ)))
        (Complex.exp (-(u : ℂ) * (ξ : ℂ)) * (-(ξ : ℂ))) u := by
      have ha : HasDerivAt (fun t : ℝ => -(t : ℂ) * (ξ : ℂ)) (-(ξ : ℂ)) u := by
        simpa using (((hasDerivAt_id u).ofReal_comp).neg).mul_const (ξ : ℂ)
      exact ha.cexp
    have h2 := (h1.const_mul ((-(ξ : ℂ)) ^ j)).mul_const (eichlerBorel c (ξ : ℂ))
    convert h2 using 1
    dsimp only [F']
    rw [pow_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound hbound_int h_diff).2

/-- For every `j : ℕ` and `u > 0`, `iteratedDeriv j (eichlerNormalized c) u = laplaceDeriv c j u`. -/
private lemma iteratedDeriv_eichlerNormalized_eq {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (eichlerNormalized c) u = laplaceDeriv c j u := by
  have heq_lap : ∀ k : ℕ, ∀ t : ℝ, 0 < t →
      iteratedDeriv k (eichlerLaplace c) t = laplaceDeriv c k t := by
    intro k
    induction k with
    | zero =>
      intro t _
      simp [laplaceDeriv, eichlerLaplace]
    | succ k ih =>
      intro t ht
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (eichlerLaplace c) =ᶠ[𝓝 t] laplaceDeriv c k :=
        Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => ih s hs
      rw [hev.deriv_eq, (laplaceDeriv_hasDerivAt hc k ht).deriv]
  have hev0 : eichlerNormalized c =ᶠ[𝓝 u] eichlerLaplace c :=
    Filter.eventually_of_mem (Ioi_mem_nhds hu) fun t ht => eichlerNormalized_eq_laplace hc ht
  rw [hev0.iteratedDeriv_eq j, heq_lap j u hu]

/-- Exact formula for coefficients of `d_u^[j] (formalSeries φ)`. -/
private lemma coeff_iter_d_u_formalSeries (φ : ℂ → ℂ) (j n : ℕ) :
    PowerSeries.coeff n (d_u^[j] (formalSeries φ)) =
      if n < j + 1 then 0
      else (-1 : ℂ) ^ j * (((n - 1).factorial : ℂ) / ((n - j - 1).factorial : ℂ)) *
        iteratedDeriv (n - j - 1) φ 0 := by
  induction j generalizing n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, zero_add, pow_zero, one_mul, Nat.sub_zero]
    rcases n with _ | k
    · simp [formalSeries]
    · have hk : ¬ (k + 1 < 1) := by omega
      have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      simp [hk, formalSeries, div_self hfac]
  | succ j ih =>
    rw [Function.iterate_succ_apply', d_u, map_neg]
    rcases n with _ | _ | k
    · simp [PowerSeries.coeff_mul, PowerSeries.coeff_X_pow]
    · simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, PowerSeries.coeff_X_pow]
    · have hcoeff : PowerSeries.coeff (k + 2) (PowerSeries.X ^ 2 *
          PowerSeries.derivative (d_u^[j] (formalSeries φ))) =
          ((k + 1 : ℕ) : ℂ) * PowerSeries.coeff (k + 1) (d_u^[j] (formalSeries φ)) := by
        rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_derivative]
        push_cast; ring
      rw [hcoeff, ih (k + 1)]
      by_cases hk : k + 2 < j + 1 + 1
      · have hk' : k + 1 < j + 1 := by omega
        simp [hk, hk']
      · have hk' : ¬ (k + 1 < j + 1) := by omega
        simp only [hk, hk', ↓reduceIte]
        have hsub1 : k + 2 - 1 = k + 1 := by omega
        have hsub2 : k + 1 - 1 = k := by omega
        have hsub3 : k + 2 - (j + 1) - 1 = k + 1 - j - 1 := by omega
        rw [hsub1, hsub2, hsub3, Nat.factorial_succ k, pow_succ]
        push_cast; ring

/-- Global Taylor remainder bound on `[0, ∞)` for `φ_g`: for any `K : ℕ`, there exists `C ≥ 0`
such that `‖φ_g(ξ) - ∑_{k < K} (ξ^k / k!) φ_g^{(k)}(0)‖ ≤ C ξ^K` for all `ξ ≥ 0`. -/
private lemma eichlerBorel_taylor_global_bound {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 ≤ ξ →
      ‖eichlerBorel c (ξ : ℂ) -
        ∑ k ∈ Finset.range K,
          ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0‖ ≤
        C * ξ ^ K := by
  have han := eichlerBorel_analyticAt_nonneg hc (le_refl (0 : ℝ))
  obtain ⟨Q, hQa, hQeq⟩ := han.exists_eventuallyEq_sum_add_pow_mul K
  have hQbd : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Q z‖ ≤ ‖Q 0‖ + 1 := by
    have hcont : Tendsto (fun z => ‖Q z‖) (𝓝 0) (𝓝 ‖Q 0‖) :=
      (hQa.continuousAt.norm).tendsto
    exact hcont.eventually (Iic_mem_nhds (by linarith))
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (hQeq.and hQbd)
  set M := ∑' n, ‖c n‖ * Real.exp (-freq n)
  have hM : 0 ≤ M := tsum_nonneg fun _ => by positivity
  set S_tail : ℝ := M / δ ^ K +
    ∑ k ∈ Finset.range K,
      ‖iteratedDeriv k (eichlerBorel c) 0‖ / ((k.factorial : ℝ) * δ ^ (K - k))
  have hS_tail : 0 ≤ S_tail := add_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => by positivity)
  refine ⟨max (‖Q 0‖ + 1) S_tail, le_trans (by positivity) (le_max_left _ _), fun ξ hξ => ?_⟩
  by_cases hlt : ξ < δ
  · have hmem : dist (ξ : ℂ) 0 < δ := by
      simpa [dist_eq_norm, Complex.norm_real, Real.norm_of_nonneg hξ] using hlt
    obtain ⟨heq, hq⟩ := hδ hmem
    have hsub : eichlerBorel c (ξ : ℂ) -
        ∑ k ∈ Finset.range K,
          ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0 =
        (ξ : ℂ) ^ K * Q (ξ : ℂ) := by
      rw [heq]
      simp only [smul_eq_mul, add_sub_cancel_left]
    rw [hsub, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hξ]
    calc ξ ^ K * ‖Q (ξ : ℂ)‖
        ≤ ξ ^ K * (‖Q 0‖ + 1) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (‖Q 0‖ + 1) * ξ ^ K := by ring
      _ ≤ max (‖Q 0‖ + 1) S_tail * ξ ^ K :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push Not at hlt
    have h1 : ‖eichlerBorel c (ξ : ℂ)‖ ≤ (M / δ ^ K) * ξ ^ K := by
      have hratio : (1 : ℝ) ≤ ξ ^ K / δ ^ K := by
        rw [one_le_div (pow_pos hδ_pos K)]
        exact pow_le_pow_left₀ hδ_pos.le hlt K
      calc ‖eichlerBorel c (ξ : ℂ)‖ ≤ M := norm_eichlerBorel_real_le hc hξ
        _ = M * 1 := by ring
        _ ≤ M * (ξ ^ K / δ ^ K) := mul_le_mul_of_nonneg_left hratio hM
        _ = (M / δ ^ K) * ξ ^ K := by ring
    have h2 : ‖∑ k ∈ Finset.range K,
          ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0‖ ≤
        (∑ k ∈ Finset.range K,
          ‖iteratedDeriv k (eichlerBorel c) 0‖ / ((k.factorial : ℝ) * δ ^ (K - k))) * ξ ^ K := by
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      have hk_lt : k < K := Finset.mem_range.mp hk
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hξ,
        Complex.norm_natCast]
      have hpow : ξ ^ k ≤ ξ ^ K / δ ^ (K - k) := by
        rw [le_div_iff₀ (pow_pos hδ_pos _)]
        calc ξ ^ k * δ ^ (K - k) ≤ ξ ^ k * ξ ^ (K - k) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ_pos.le hlt _) (by positivity)
          _ = ξ ^ (k + (K - k)) := (pow_add _ _ _).symm
          _ = ξ ^ K := by rw [Nat.add_sub_of_le hk_lt.le]
      calc ξ ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k (eichlerBorel c) 0‖
          ≤ (ξ ^ K / δ ^ (K - k)) / (k.factorial : ℝ) * ‖iteratedDeriv k (eichlerBorel c) 0‖ := by
            gcongr
        _ = ‖iteratedDeriv k (eichlerBorel c) 0‖ / ((k.factorial : ℝ) * δ ^ (K - k)) * ξ ^ K := by
            ring
    calc ‖eichlerBorel c (ξ : ℂ) -
            ∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0‖
        ≤ ‖eichlerBorel c (ξ : ℂ)‖ +
            ‖∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0‖ :=
          norm_sub_le _ _
      _ ≤ (M / δ ^ K) * ξ ^ K +
            (∑ k ∈ Finset.range K,
              ‖iteratedDeriv k (eichlerBorel c) 0‖ / ((k.factorial : ℝ) * δ ^ (K - k))) * ξ ^ K :=
          add_le_add h1 h2
      _ = S_tail * ξ ^ K := by dsimp only [S_tail]; ring
      _ ≤ max (‖Q 0‖ + 1) S_tail * ξ ^ K :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **Watson's Lemma (All Orders & All Derivatives)**: for every `j : ℕ`, the `j`-th derivative
of `u⁻¹ I_g(u)` has the exact all-orders `1/u` asymptotic expansion `d_u^[j] (formalSeries φ_g)`. -/
theorem eichlerNormalized_hasAsympExp {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (eichlerNormalized c))
      (d_u^[j] (formalSeries (eichlerBorel c))) := by
  intro M
  by_cases hMj : M ≤ j + 1
  · set B := ∑' n, ‖c n‖ * Real.exp (-freq n)
    refine ⟨B * (j.factorial : ℝ), ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu_pos : 0 < u := by linarith
    have hsum0 : ∑ k ∈ Finset.range M,
        PowerSeries.coeff k (d_u^[j] (formalSeries (eichlerBorel c))) * ((u : ℂ)⁻¹ ^ k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkj : k < j + 1 := lt_of_lt_of_le (Finset.mem_range.mp hk) hMj
      rw [coeff_iter_d_u_formalSeries, ite_eq_left_iff.mpr (fun h => absurd hkj h), zero_mul]
    rw [hsum0, sub_zero, iteratedDeriv_eichlerNormalized_eq hc j hu_pos, laplaceDeriv]
    have hdom : IntegrableOn (fun ξ : ℝ => B * (ξ ^ j * Real.exp (-u * ξ))) (Ioi (0 : ℝ)) :=
      (integrableOn_pow_mul_exp_neg_Ioi j hu_pos).const_mul B
    have hbd : ‖∫ ξ in Ioi (0 : ℝ),
          (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * eichlerBorel c (ξ : ℂ)‖ ≤
        ∫ ξ in Ioi (0 : ℝ), B * (ξ ^ j * Real.exp (-u * ξ)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on (laplaceDeriv_integrable hc j hu_pos).norm hdom
        measurableSet_Ioi fun ξ hξ => ?_
      have hξ0 : 0 ≤ ξ := (Set.mem_Ioi.mp hξ).le
      rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hξ0,
        Complex.norm_exp]
      have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
      rw [hre]
      have hφ := norm_eichlerBorel_real_le hc hξ0
      calc ξ ^ j * Real.exp (-u * ξ) * ‖eichlerBorel c (ξ : ℂ)‖
          ≤ ξ ^ j * Real.exp (-u * ξ) * B := mul_le_mul_of_nonneg_left hφ (by positivity)
        _ = B * (ξ ^ j * Real.exp (-u * ξ)) := by ring
    refine hbd.trans ?_
    rw [integral_const_mul, integral_pow_mul_exp_neg_Ioi j hu_pos, ← mul_div_assoc]
    have hB : 0 ≤ B := tsum_nonneg fun _ => by positivity
    have hpow : u ^ M ≤ u ^ (j + 1) := pow_le_pow_right₀ hu hMj
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hu_pos M) hpow
  · push Not at hMj
    set K := M - (j + 1) with hK_def
    have hMK : K + j + 1 = M := by omega
    obtain ⟨C, hC_nn, hC⟩ := eichlerBorel_taylor_global_bound hc K
    refine ⟨C * ((j + K).factorial : ℝ), ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [iteratedDeriv_eichlerNormalized_eq hc j hu, laplaceDeriv]
    -- Rewrite the `Finset.range M` asymptotic sum as the integral of the degree `< K` Taylor poly
    have hpoly_int :
        ∑ n ∈ Finset.range M,
          PowerSeries.coeff n (d_u^[j] (formalSeries (eichlerBorel c))) * ((u : ℂ)⁻¹ ^ n) =
        ∫ ξ in Ioi (0 : ℝ),
          (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0) := by
      have hsum_k :
          ∑ n ∈ Finset.range M,
            PowerSeries.coeff n (d_u^[j] (formalSeries (eichlerBorel c))) * ((u : ℂ)⁻¹ ^ n) =
          ∑ k ∈ Finset.range K,
            (-1 : ℂ) ^ j * (((k + j).factorial : ℂ) / (k.factorial : ℂ)) *
              iteratedDeriv k (eichlerBorel c) 0 * ((u : ℂ)⁻¹ ^ (k + j + 1)) := by
        rw [← hMK, show K + j + 1 = (j + 1) + K by omega, Finset.sum_range_add]
        have hhead : ∑ n ∈ Finset.range (j + 1),
            PowerSeries.coeff n (d_u^[j] (formalSeries (eichlerBorel c))) * ((u : ℂ)⁻¹ ^ n) = 0 := by
          refine Finset.sum_eq_zero fun n hn => ?_
          rw [coeff_iter_d_u_formalSeries, ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_range.mp hn) h), zero_mul]
        rw [hhead, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hnot : ¬ (j + 1 + k < j + 1) := by omega
        rw [coeff_iter_d_u_formalSeries, ite_eq_right_iff.mpr (fun h => absurd h hnot)]
        have hs1 : j + 1 + k - 1 = k + j := by omega
        have hs2 : j + 1 + k - j - 1 = k := by omega
        have hs3 : j + 1 + k = k + j + 1 := by omega
        rw [hs1, hs2, hs3]
      rw [hsum_k]
      have hterm_int : ∀ k ∈ Finset.range K, IntegrableOn
          (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0))
          (Ioi (0 : ℝ)) := by
        intro k _
        have hrew : (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0)) =
            fun ξ : ℝ =>
              ((-1 : ℂ) ^ j * (iteratedDeriv k (eichlerBorel c) 0 / (k.factorial : ℂ))) *
                (((ξ ^ (k + j) * Real.exp (-u * ξ) : ℝ) : ℂ)) := by
          funext ξ
          rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp,
            neg_eq_neg_one_mul, mul_pow, pow_add]
          have hexp : Complex.exp (-(u : ℂ) * (ξ : ℂ)) = Complex.exp ((-u * ξ : ℝ) : ℂ) := by
            congr 1; push_cast; ring
          rw [hexp]; ring
        rw [hrew]
        exact ((integrableOn_pow_mul_exp_neg_Ioi (k + j) hu).ofReal).const_mul _
      have hswap : ∫ ξ in Ioi (0 : ℝ),
          (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (∑ k ∈ Finset.range K,
              ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0) =
          ∑ k ∈ Finset.range K, ∫ ξ in Ioi (0 : ℝ),
            (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
              (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0) := by
        simp_rw [Finset.mul_sum]
        have hgen : ∀ (s : Finset ℕ), (∀ k ∈ s, IntegrableOn
            (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
              (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0))
            (Ioi (0 : ℝ))) →
            (∫ ξ in Ioi (0 : ℝ), ∑ k ∈ s,
              (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
                (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0)) =
            ∑ k ∈ s, ∫ ξ in Ioi (0 : ℝ),
              (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
                (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0) := by
          intro s
          induction s using Finset.cons_induction with
          | empty => intro _; simp
          | cons a s ha ih =>
            intro hs
            simp_rw [Finset.sum_cons]
            have h1 := hs a (Finset.mem_cons_self a s)
            have h2 : IntegrableOn (fun ξ : ℝ => ∑ k ∈ s,
                (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
                  (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0))
                (Ioi (0 : ℝ)) := by
              have hsub : ∀ k ∈ s, IntegrableOn
                  (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
                    (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0))
                  (Ioi (0 : ℝ)) := fun k hk => hs k (Finset.mem_cons_of_mem hk)
              clear ih hs ha
              induction s using Finset.cons_induction with
              | empty => simp
              | cons b t _ iht =>
                simp_rw [Finset.sum_cons]
                exact (hsub b (Finset.mem_cons_self b t)).add
                  (iht fun k hk => hsub k (Finset.mem_cons_of_mem hk))
            rw [integral_add h1 h2, ih fun k hk => hs k (Finset.mem_cons_of_mem hk)]
        exact hgen (Finset.range K) hterm_int
      rw [hswap]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hrew : (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
          (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0)) =
          fun ξ : ℝ =>
            ((-1 : ℂ) ^ j * (iteratedDeriv k (eichlerBorel c) 0 / (k.factorial : ℂ))) *
              ((ξ : ℂ) ^ (k + j) * Complex.exp (-(u : ℂ) * (ξ : ℂ))) := by
        funext ξ
        rw [neg_eq_neg_one_mul, mul_pow, pow_add]; ring
      rw [hrew, integral_const_mul, integral_pow_mul_cexp_neg_Ioi (k + j) hu]
      rw [inv_pow]
      ring
    rw [hpoly_int]
    have hT_int : IntegrableOn
        (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
          (∑ k ∈ Finset.range K,
            ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0))
        (Ioi (0 : ℝ)) := by
      simp_rw [Finset.mul_sum]
      have hterm : ∀ k : ℕ, IntegrableOn
          (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0))
          (Ioi (0 : ℝ)) := fun k => by
        have hrew : (fun ξ : ℝ => (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
            (((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0)) =
            fun ξ : ℝ =>
              ((-1 : ℂ) ^ j * (iteratedDeriv k (eichlerBorel c) 0 / (k.factorial : ℂ))) *
                (((ξ ^ (k + j) * Real.exp (-u * ξ) : ℝ) : ℂ)) := by
          funext ξ
          rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp,
            neg_eq_neg_one_mul, mul_pow, pow_add]
          have hexp : Complex.exp (-(u : ℂ) * (ξ : ℂ)) = Complex.exp ((-u * ξ : ℝ) : ℂ) := by
            congr 1; push_cast; ring
          rw [hexp]; ring
        rw [hrew]
        exact ((integrableOn_pow_mul_exp_neg_Ioi (k + j) hu).ofReal).const_mul _
      induction (Finset.range K) using Finset.cons_induction with
      | empty => simp
      | cons a s _ ih =>
        simp_rw [Finset.sum_cons]
        exact (hterm a).add ih
    rw [← integral_sub (laplaceDeriv_integrable hc j hu) hT_int]
    have hdom : IntegrableOn (fun ξ : ℝ => C * (ξ ^ (j + K) * Real.exp (-u * ξ))) (Ioi (0 : ℝ)) :=
      (integrableOn_pow_mul_exp_neg_Ioi (j + K) hu).const_mul C
    have hbd : ‖∫ ξ in Ioi (0 : ℝ),
          (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) * eichlerBorel c (ξ : ℂ) -
            (-(ξ : ℂ)) ^ j * Complex.exp (-(u : ℂ) * (ξ : ℂ)) *
              (∑ k ∈ Finset.range K,
                ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0)‖ ≤
        ∫ ξ in Ioi (0 : ℝ), C * (ξ ^ (j + K) * Real.exp (-u * ξ)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on ((laplaceDeriv_integrable hc j hu).sub hT_int).norm hdom
        measurableSet_Ioi fun ξ hξ => ?_
      have hξ0 : 0 ≤ ξ := (Set.mem_Ioi.mp hξ).le
      rw [← mul_sub, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg hξ0, Complex.norm_exp]
      have hre : (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ := by simp
      rw [hre]
      calc ξ ^ j * Real.exp (-u * ξ) *
            ‖eichlerBorel c (ξ : ℂ) -
              ∑ k ∈ Finset.range K,
                ((ξ : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (eichlerBorel c) 0‖
          ≤ ξ ^ j * Real.exp (-u * ξ) * (C * ξ ^ K) :=
            mul_le_mul_of_nonneg_left (hC ξ hξ0) (by positivity)
        _ = C * (ξ ^ (j + K) * Real.exp (-u * ξ)) := by rw [pow_add]; ring
    refine hbd.trans_eq ?_
    rw [integral_const_mul, integral_pow_mul_exp_neg_Ioi (j + K) hu, ← mul_div_assoc]
    congr 2
    have : j + K + 1 = M := by omega
    rw [this]

/-! ### 7. General Weight-1 Eichler-Integral Differential Transcendence Theorems -/

/-- Normalized weight-1 Eichler integral `u⁻¹ I_g(u)` satisfies NO nonzero polynomial ADE
over `ℂ[u]`. -/
theorem eichlerWeightOne_normalized_no_poly_ade (c : ℕ → ℂ)
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (hinf : {n : ℕ | c n ≠ 0}.Infinite)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerNormalized c) u)
        (evalU P (u : ℂ)) = 0) : P = 0 :=
  no_nonautonomous_ade_of_higher_order_borel
    (eichlerWeightOne_borelData c hc hinf) (eichlerNormalized_hasAsympExp hc) P hP

/-- Normalized weight-1 Eichler integral `u⁻¹ I_g(u)` satisfies NO nonzero rational ADE
over `ℂ(u)`. -/
theorem eichlerWeightOne_normalized_no_rat_ade (c : ℕ → ℂ)
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (hinf : {n : ℕ | c n ≠ 0}.Infinite)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerNormalized c) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  no_rat_ade_of_higher_order_borel
    (eichlerWeightOne_borelData c hc hinf) (eichlerNormalized_hasAsympExp hc) P hP

/-- For `u > 0`, `I_g(u) = u · (u⁻¹ I_g(u))`. -/
private lemma eichlerIntegral_eq_mul (c : ℕ → ℂ) {u : ℝ} (hu : 0 < u) :
    eichlerIntegral c u = (u : ℂ) * eichlerNormalized c u := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [eichlerNormalized, ← mul_assoc, mul_inv_cancel₀ huC, one_mul]

/-- Leibniz derivatives of `I_g(u) = u · L_g(u)` on `(0, ∞)`. -/
private lemma iteratedDeriv_eichlerIntegral_eq {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n))) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (eichlerIntegral c) u =
      match j with
      | 0 => (u : ℂ) * laplaceDeriv c 0 u
      | k + 1 => (u : ℂ) * laplaceDeriv c (k + 1) u + ((k + 1 : ℕ) : ℂ) * laplaceDeriv c k u := by
  induction j generalizing u with
  | zero =>
    simp only [iteratedDeriv_zero]
    rw [eichlerIntegral_eq_mul c hu, eichlerNormalized_eq_laplace hc hu]
    simp [laplaceDeriv, eichlerLaplace]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    cases k with
    | zero =>
      have hev : iteratedDeriv 0 (eichlerIntegral c) =ᶠ[𝓝 u]
          fun t : ℝ => (t : ℂ) * laplaceDeriv c 0 t :=
        Filter.eventually_of_mem (Ioi_mem_nhds hu) fun t ht => ih ht
      rw [hev.deriv_eq]
      have hd : HasDerivAt (fun t : ℝ => (t : ℂ) * laplaceDeriv c 0 t)
          (1 * laplaceDeriv c 0 u + (u : ℂ) * laplaceDeriv c 1 u) u :=
        ((hasDerivAt_id u).ofReal_comp).mul (laplaceDeriv_hasDerivAt hc 0 hu)
      rw [hd.deriv]
      push_cast; ring
    | succ m =>
      have hev : iteratedDeriv (m + 1) (eichlerIntegral c) =ᶠ[𝓝 u]
          fun t : ℝ => (t : ℂ) * laplaceDeriv c (m + 1) t +
            ((m + 1 : ℕ) : ℂ) * laplaceDeriv c m t :=
        Filter.eventually_of_mem (Ioi_mem_nhds hu) fun t ht => ih ht
      rw [hev.deriv_eq]
      have hd1 : HasDerivAt (fun t : ℝ => (t : ℂ) * laplaceDeriv c (m + 1) t)
          (1 * laplaceDeriv c (m + 1) u + (u : ℂ) * laplaceDeriv c (m + 2) u) u :=
        ((hasDerivAt_id u).ofReal_comp).mul (laplaceDeriv_hasDerivAt hc (m + 1) hu)
      have hd2 : HasDerivAt (fun t : ℝ => ((m + 1 : ℕ) : ℂ) * laplaceDeriv c m t)
          (((m + 1 : ℕ) : ℂ) * laplaceDeriv c (m + 1) u) u :=
        (laplaceDeriv_hasDerivAt hc m hu).const_mul _
      have hd := hd1.add hd2
      change HasDerivAt
        (fun t : ℝ => (t : ℂ) * laplaceDeriv c (m + 1) t +
          ((m + 1 : ℕ) : ℂ) * laplaceDeriv c m t) _ u at hd
      rw [hd.deriv]
      push_cast; ring

/-- Differential substitution `Y_0 ↦ u Z_0`, `Y_{k+1} ↦ u Z_{k+1} + (k+1) Z_k` over `ℂ[u]`. -/
private def mulUSubst {r : ℕ} :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) →ₐ[Polynomial ℂ]
      MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  MvPolynomial.aeval fun j : Fin (r + 1) =>
    match h : j.val with
    | 0 => MvPolynomial.C Polynomial.X * MvPolynomial.X j
    | k + 1 => MvPolynomial.C Polynomial.X * MvPolynomial.X j +
        MvPolynomial.C (Polynomial.C ((k + 1 : ℕ) : ℂ)) * MvPolynomial.X ⟨k, by omega⟩

/-- Pointwise evaluation `u ∈ ℂ` of `mulUSubst` as an endomorphism of `ℂ[Z_0, ..., Z_r]`. -/
private def mulUSubstC {r : ℕ} (u : ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (r + 1)) ℂ :=
  MvPolynomial.aeval fun j : Fin (r + 1) =>
    match h : j.val with
    | 0 => MvPolynomial.C u * MvPolynomial.X j
    | k + 1 => MvPolynomial.C u * MvPolynomial.X j +
        MvPolynomial.C ((k + 1 : ℕ) : ℂ) * MvPolynomial.X ⟨k, by omega⟩

private def mulUInvImg {r : ℕ} (u : ℂ) : (j : ℕ) → j < r + 1 → MvPolynomial (Fin (r + 1)) ℂ
  | 0, h => MvPolynomial.C u⁻¹ * MvPolynomial.X ⟨0, h⟩
  | k + 1, h => MvPolynomial.C u⁻¹ *
      (MvPolynomial.X ⟨k + 1, h⟩ - MvPolynomial.C ((k + 1 : ℕ) : ℂ) * mulUInvImg u k (by omega))

private def mulUInvC {r : ℕ} (u : ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (r + 1)) ℂ :=
  MvPolynomial.aeval fun j : Fin (r + 1) => mulUInvImg u j.val j.isLt

private lemma mulUInvC_comp_mulUSubstC {r : ℕ} {u : ℂ} (hu : u ≠ 0)
    (Q : MvPolynomial (Fin (r + 1)) ℂ) :
    mulUInvC u (mulUSubstC u Q) = Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [mulUSubstC, mulUInvC]
  | add A B hA hB => simp [map_add, hA, hB]
  | mul_X A j hA =>
    rw [map_mul, map_mul, hA]
    congr 1
    rcases j with ⟨jv, hjv⟩
    cases jv with
    | zero =>
      simp only [mulUSubstC, mulUInvC, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, mulUInvImg]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul]
    | succ k =>
      simp only [mulUSubstC, mulUInvC, MvPolynomial.aeval_X, map_add, map_mul, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, mulUInvImg]
      rw [← mul_assoc (MvPolynomial.C u), ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul,
        sub_add_cancel]

private lemma evalU_mulUSubst {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    evalU (mulUSubst P) u = mulUSubstC u (evalU P u) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
    simp [evalU, mulUSubst, mulUSubstC, MvPolynomial.algebraMap_eq]
  | add A B hA hB =>
    simp only [map_add, evalU] at hA hB ⊢
    rw [hA, hB]
  | mul_X A j hA =>
    have hmap : evalU (mulUSubst (A * MvPolynomial.X j)) u =
        evalU (mulUSubst A) u * evalU (mulUSubst (MvPolynomial.X j)) u := by
      simp [evalU, map_mul]
    rw [hmap, hA]
    have hrhs : mulUSubstC u (evalU (A * MvPolynomial.X j) u) =
        mulUSubstC u (evalU A u) * mulUSubstC u (MvPolynomial.X j) := by
      simp [evalU, map_mul]
    rw [hrhs]
    congr 1
    rcases j with ⟨jv, hjv⟩
    cases jv with
    | zero =>
      simp [evalU, mulUSubst, mulUSubstC]
    | succ k =>
      simp [evalU, mulUSubst, mulUSubstC]

private lemma mulUSubst_injective {r : ℕ} {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)}
    (hP : mulUSubst P = 0) : P = 0 := by
  have heval_zero : ∀ u : ℂ, u ≠ 0 → evalU P u = 0 := by
    intro u hu
    have h1 : mulUSubstC u (evalU P u) = 0 := by
      rw [← evalU_mulUSubst, hP, evalU, map_zero]
    rw [← mulUInvC_comp_mulUSubstC hu (evalU P u), h1, map_zero]
  refine MvPolynomial.ext P 0 fun α => ?_
  change P.coeff α = 0
  by_contra hne
  let B : ℝ := Finset.sum (P.coeff α).roots.toFinset fun z : ℂ => ‖z‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let u₀ : ℝ := B + 1
  have hu₀_pos : 0 < u₀ := by linarith
  have hu₀_ne : (u₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu₀_pos.ne'
  have hroot : (P.coeff α).eval (u₀ : ℂ) = 0 := by
    have h0 := congrArg (fun Q => Q.coeff α) (heval_zero (u₀ : ℂ) hu₀_ne)
    simpa [evalU, MvPolynomial.coeff_map] using h0
  have hmem : (u₀ : ℂ) ∈ (P.coeff α).roots := (Polynomial.mem_roots hne).mpr hroot
  have hle : ‖(u₀ : ℂ)‖ ≤ B :=
    Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _)
      (Multiset.mem_toFinset.mpr hmem)
  rw [Complex.norm_real, Real.norm_of_nonneg hu₀_pos.le] at hle
  linarith

private lemma eval_mulUSubst_eq {r : ℕ} {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) {u : ℝ} (hu : 0 < u) :
    MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerNormalized c) u)
        (evalU (mulUSubst P) (u : ℂ)) =
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral c) u)
        (evalU P (u : ℂ)) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
    simp [evalU, mulUSubst, MvPolynomial.algebraMap_eq]
  | add A B hA hB =>
    simp only [map_add, evalU] at hA hB ⊢
    rw [hA, hB]
  | mul_X A j hA =>
    have hL : MvPolynomial.eval (fun i : Fin (r + 1) => iteratedDeriv i.val (eichlerNormalized c) u)
          (evalU (mulUSubst (A * MvPolynomial.X j)) (u : ℂ)) =
        MvPolynomial.eval (fun i : Fin (r + 1) => iteratedDeriv i.val (eichlerNormalized c) u)
            (evalU (mulUSubst A) (u : ℂ)) *
          MvPolynomial.eval (fun i : Fin (r + 1) => iteratedDeriv i.val (eichlerNormalized c) u)
            (evalU (mulUSubst (MvPolynomial.X j)) (u : ℂ)) := by
      simp [evalU, map_mul]
    have hR : MvPolynomial.eval (fun i : Fin (r + 1) => iteratedDeriv i.val (eichlerIntegral c) u)
          (evalU (A * MvPolynomial.X j) (u : ℂ)) =
        MvPolynomial.eval (fun i : Fin (r + 1) => iteratedDeriv i.val (eichlerIntegral c) u)
            (evalU A (u : ℂ)) *
          iteratedDeriv j.val (eichlerIntegral c) u := by
      simp [evalU, map_mul]
    rw [hL, hR, hA]
    congr 1
    rcases j with ⟨jv, hjv⟩
    cases jv with
    | zero =>
      simp only [mulUSubst, MvPolynomial.aeval_X, evalU, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, Polynomial.coe_evalRingHom, Polynomial.eval_X, MvPolynomial.eval_C,
        MvPolynomial.eval_X]
      rw [iteratedDeriv_eichlerNormalized_eq hc 0 hu, iteratedDeriv_eichlerIntegral_eq hc 0 hu]
    | succ k =>
      simp only [mulUSubst, MvPolynomial.aeval_X, evalU, map_add, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [iteratedDeriv_eichlerNormalized_eq hc (k + 1) hu,
        iteratedDeriv_eichlerNormalized_eq hc k hu,
        iteratedDeriv_eichlerIntegral_eq hc (k + 1) hu]

/-- **General Weight-1 Eichler-Integral Polynomial ADE Theorem (`ℂ[u]`)**:
For ANY coefficient sequence `c` with `∑ ‖c n‖ e^{-2π(n+1)} < ∞` and infinitely many nonzero
entries, the split Stieltjes / Eichler integral `I_g(u) = ∫_1^∞ g(i s) / (1 + s/u) ds` satisfies
NO nonzero polynomial differential equation over `ℂ[u]`. -/
theorem eichlerWeightOne_no_poly_ade (c : ℕ → ℂ)
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (hinf : {n : ℕ | c n ≠ 0}.Infinite)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral c) u)
        (evalU P (u : ℂ)) = 0) : P = 0 := by
  have hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerNormalized c) u)
        (evalU (mulUSubst P) (u : ℂ)) = 0 := by
    filter_upwards [hP, eventually_gt_atTop (0 : ℝ)] with u hu hu_pos
    rw [eval_mulUSubst_eq hc P hu_pos, hu]
  exact mulUSubst_injective (eichlerWeightOne_normalized_no_poly_ade c hc hinf (mulUSubst P) hQ)

private def clearRatDenomPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    Polynomial ℂ :=
  ∏ α ∈ P.support, (P.coeff α).denom

private def clearRatDenomMvPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ α ∈ P.support,
    MvPolynomial.monomial α ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)

private lemma clearRatDenomMvPoly_eq_zero_iff {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    clearRatDenomMvPoly P = 0 ↔ P = 0 := by
  classical
  constructor
  · intro h0
    refine MvPolynomial.ext P 0 fun α => ?_
    change P.coeff α = 0
    by_cases hα : α ∈ P.support
    · have hc0 : (clearRatDenomMvPoly P).coeff α = 0 := by
        simpa using congrArg (fun Q => Q.coeff α) h0
      rw [clearRatDenomMvPoly, MvPolynomial.coeff_sum] at hc0
      simp_rw [MvPolynomial.coeff_monomial] at hc0
      rw [Finset.sum_eq_single α (fun β _ hβα => by simp [hβα]) (fun h => absurd hα h),
        ite_eq_left_iff.mpr (fun h => absurd rfl h)] at hc0
      have hprod_ne : ∏ β ∈ P.support.erase α, (P.coeff β).denom ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun β _ => RatFunc.denom_ne_zero _
      have hnum0 : (P.coeff α).num = 0 := (mul_eq_zero.mp hc0).resolve_right hprod_ne
      rw [← RatFunc.num_div_denom (P.coeff α), hnum0, map_zero, zero_div]
    · exact MvPolynomial.notMem_support_iff.mp hα
  · intro h0; subst h0; simp [clearRatDenomMvPoly]

private lemma evalU_clearRatDenomMvPoly {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) {u : ℂ}
    (hu : ∀ β ∈ P.support, (P.coeff β).denom.eval u ≠ 0) :
    evalU (clearRatDenomMvPoly P) u = (clearRatDenomPoly P).eval u • evalRatU P u := by
  classical
  ext α
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, clearRatDenomMvPoly,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, evalRatU, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α (fun β _ hβα => by simp [hβα]) (fun h => absurd hα h),
      Finset.sum_eq_single α (fun β _ hβα => by simp [hβα]) (fun h => absurd hα h)]
    simp only [↓reduceIte, ratEval, clearRatDenomPoly, Polynomial.eval_mul, Polynomial.eval_prod]
    rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval u) hα]
    field_simp [hu α hα]
  · rw [Finset.sum_eq_zero (fun β hβ => ite_eq_right_iff.mpr fun h => by subst h; exact absurd hβ hα),
      Finset.sum_eq_zero (fun β hβ => ite_eq_right_iff.mpr fun h => by subst h; exact absurd hβ hα)]
    simp

private lemma poly_eventually_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∀ᶠ u : ℝ in Filter.atTop, q.eval (u : ℂ) ≠ 0 := by
  let B : ℝ := Finset.sum q.roots.toFinset fun z : ℂ => ‖z‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  filter_upwards [eventually_gt_atTop B] with u hu h0
  have hmem : (u : ℂ) ∈ q.roots := (Polynomial.mem_roots hq).mpr h0
  have hle : ‖(u : ℂ)‖ ≤ B :=
    Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _)
      (Multiset.mem_toFinset.mpr hmem)
  have hpos : 0 < u := lt_of_le_of_lt hB hu
  rw [Complex.norm_real, Real.norm_of_nonneg hpos.le] at hle
  linarith

/-- **General Weight-1 Eichler-Integral Rational ADE Theorem (`ℂ(u)`)**:
For ANY coefficient sequence `c` with `∑ ‖c n‖ e^{-2π(n+1)} < ∞` and infinitely many nonzero
entries, the split Stieltjes / Eichler integral `I_g(u) = ∫_1^∞ g(i s) / (1 + s/u) ds` satisfies
NO nonzero non-autonomous rational-coefficient differential equation over `ℂ(u)`. -/
theorem eichlerWeightOne_no_rat_ade (c : ℕ → ℂ)
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (hinf : {n : ℕ | c n ≠ 0}.Infinite)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral c) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hden : ∀ᶠ u : ℝ in Filter.atTop, ∀ β ∈ P.support, (P.coeff β).denom.eval (u : ℂ) ≠ 0 :=
    (Filter.eventually_all_finset P.support).mpr fun β _ =>
      poly_eventually_ne_zero (RatFunc.denom_ne_zero _)
  have hclear : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral c) u)
        (evalU (clearRatDenomMvPoly P) (u : ℂ)) = 0 := by
    filter_upwards [hP, hden] with u hu hdu
    rw [evalU_clearRatDenomMvPoly P hdu, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      hu, mul_zero]
  exact (clearRatDenomMvPoly_eq_zero_iff P).mp
    (eichlerWeightOne_no_poly_ade c hc hinf (clearRatDenomMvPoly P) hclear)

/-- **Sub-Exponential / Subsequence Packaging (`eichlerWeightOne_integral_no_rat_ade`)**:
Direct packaging with sub-exponential growth `‖c n‖ ≤ C e^{α n}` (`α < 2π`) and a strictly
increasing subsequence `idx` of nonzero Fourier coefficients. -/
theorem eichlerWeightOne_integral_no_rat_ade (c : ℕ → ℂ)
    (idx : ℕ → ℕ) (hmono : StrictMono idx) (hne : ∀ k, c (idx k) ≠ 0)
    (hgrowth : ∃ C α : ℝ, α < 2 * Real.pi ∧ ∀ n : ℕ, ‖c n‖ ≤ C * Real.exp (α * (n : ℝ)))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral c) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  obtain ⟨C, α, hα, hC⟩ := hgrowth
  exact eichlerWeightOne_no_rat_ade c (summable_of_exp_bound hα hC)
    (infinite_support_of_subseq idx hmono hne) P hP

/-- **Autonomous Corollary**: `I_g(u)` satisfies NO nonzero autonomous ADE over `ℂ`. -/
theorem eichlerWeightOne_no_autonomous_ade (c : ℕ → ℂ)
    (hc : Summable (fun n => ‖c n‖ * Real.exp (-freq n)))
    (hinf : {n : ℕ | c n ≠ 0}.Infinite)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral c) u) P = 0) :
    P = 0 := by
  have hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral c) u)
        (evalU (MvPolynomial.map Polynomial.C P) (u : ℂ)) = 0 := by
    filter_upwards [hP] with u hu
    have hev : evalU (MvPolynomial.map Polynomial.C P) (u : ℂ) = P := by
      unfold evalU
      rw [MvPolynomial.map_map]
      have hid : (Polynomial.evalRingHom (u : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
        ext c; simp
      rw [hid, MvPolynomial.map_id]
    rw [hev, hu]
  have h0 := eichlerWeightOne_no_poly_ade c hc hinf (MvPolynomial.map Polynomial.C P) hQ
  exact MvPolynomial.map_injective Polynomial.C Polynomial.C_injective (h0.trans (map_zero _).symm)

/-! ### 8. Tier-1 Witness 1: Kudla–Rapoport–Yang / Duke–Li Weight-1 Eisenstein Shadow (`χ_{-3}`) -/

/-- Quadratic Dirichlet character `χ_{-3}(d) = ( -3 / d )`. -/
@[expose] def chiNeg3 (d : ℕ) : ℤ :=
  if d % 3 = 1 then 1 else if d % 3 = 2 then -1 else 0

/-- Exact `n`-th Fourier coefficient (`q^{n+1}`) of the weight-1 Eisenstein series
`E_1(τ; χ_{-3})`: `r_3(n + 1) = ∑_{d ∣ n + 1} χ_{-3}(d)`. -/
@[expose] def kryDivisorCoeff (n : ℕ) : ℂ :=
  ((∑ d ∈ Nat.divisors (n + 1), chiNeg3 d : ℤ) : ℂ)

private lemma chiNeg3_abs_le_one (d : ℕ) : |(chiNeg3 d : ℝ)| ≤ 1 := by
  unfold chiNeg3
  split_ifs <;> norm_num

private lemma kryDivisorCoeff_three_pow (k : ℕ) : kryDivisorCoeff (3 ^ k - 1) = 1 := by
  have hpow : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
  have hadd : 3 ^ k - 1 + 1 = 3 ^ k := Nat.sub_add_cancel hpow
  unfold kryDivisorCoeff
  rw [hadd, Nat.divisors_prime_pow Nat.prime_three k, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ']
  have htail : ∑ j ∈ Finset.range k, chiNeg3 (3 ^ (j + 1)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hmod : 3 ^ (j + 1) % 3 = 0 := by
      rw [pow_succ, Nat.mul_mod_left]
    simp [chiNeg3, hmod]
  rw [htail, zero_add]
  norm_num [chiNeg3]

private lemma kryDivisorCoeff_summable :
    Summable (fun n : ℕ => ‖kryDivisorCoeff n‖ * Real.exp (-freq n)) := by
  refine summable_of_poly_bound (C := 1) (d := 1) fun n => ?_
  rw [one_mul, pow_one, kryDivisorCoeff, Complex.norm_intCast]
  have hsum : |(∑ d ∈ Nat.divisors (n + 1), chiNeg3 d : ℤ)| ≤
      ((Nat.divisors (n + 1)).card : ℤ) := by
    have h1 : |(∑ d ∈ Nat.divisors (n + 1), (chiNeg3 d : ℝ))| ≤
        ∑ d ∈ Nat.divisors (n + 1), |(chiNeg3 d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ d ∈ Nat.divisors (n + 1), |(chiNeg3 d : ℝ)| ≤ ((Nat.divisors (n + 1)).card : ℝ) := by
      calc ∑ d ∈ Nat.divisors (n + 1), |(chiNeg3 d : ℝ)|
          ≤ ∑ _d ∈ Nat.divisors (n + 1), (1 : ℝ) := Finset.sum_le_sum fun d _ => chiNeg3_abs_le_one d
        _ = ((Nat.divisors (n + 1)).card : ℝ) := by simp
    have hreal : ((|(∑ d ∈ Nat.divisors (n + 1), chiNeg3 d : ℤ)| : ℤ) : ℝ) ≤
        ((Nat.divisors (n + 1)).card : ℝ) := by
      push_cast
      exact h1.trans h2
    exact_mod_cast hreal
  have hcard : (Nat.divisors (n + 1)).card ≤ n + 1 := by
    have hsub : Nat.divisors (n + 1) ⊆ Finset.Icc 1 (n + 1) := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        Nat.le_of_dvd (Nat.succ_pos n) (Nat.dvd_of_mem_divisors hd)⟩
    exact (Finset.card_le_card hsub).trans_eq (by rw [Nat.card_Icc]; omega)
  have h1 : (|(∑ d ∈ Nat.divisors (n + 1), chiNeg3 d : ℤ)| : ℝ) ≤ ((Nat.divisors (n + 1)).card : ℝ) := by
    exact_mod_cast hsum
  have h2 : ((Nat.divisors (n + 1)).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
  exact h1.trans h2

private lemma kryDivisorCoeff_infinite : {n : ℕ | kryDivisorCoeff n ≠ 0}.Infinite := by
  refine infinite_support_of_subseq (fun k => 3 ^ k - 1) ?_ fun k => ?_
  · intro a b hab
    have h1 : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by norm_num)
    have hlt : 3 ^ a < 3 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
    exact Nat.sub_lt_sub_right h1 hlt
  · rw [kryDivisorCoeff_three_pow]; exact one_ne_zero

/-- Concrete `HigherOrderBorelData` witness for the KRY / Duke–Li weight-1 Eisenstein shadow
`E_1(τ; χ_{-3})`. -/
def kryEisenstein_borelData :
    HigherOrderBorelData (eichlerBorel kryDivisorCoeff) Real.pi (poleFreq kryDivisorCoeff)
      (fun _ => 1) (fun k s => if s = 1 then kryDivisorCoeff (suppIdx kryDivisorCoeff k) else 0) :=
  eichlerWeightOne_borelData kryDivisorCoeff kryDivisorCoeff_summable kryDivisorCoeff_infinite

/-- **Tier-1 Witness 1 (KRY / Duke–Li Weight-1 Eisenstein Shadow `χ_{-3}`)**:
The split weight-1 Eichler integral of `E_1(τ; χ_{-3})` (`c_n = ∑_{d ∣ n} χ_{-3}(d)`) satisfies
NO nonzero rational-coefficient differential equation over `ℂ(u)` (zero extra hypotheses). -/
theorem kryEisenstein_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral kryDivisorCoeff) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  eichlerWeightOne_no_rat_ade kryDivisorCoeff kryDivisorCoeff_summable kryDivisorCoeff_infinite P hP

/-- Formal Borel-level D-transcendence for the KRY / Duke–Li weight-1 Eisenstein shadow. -/
theorem kryEisenstein_formal_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (eichlerBorel kryDivisorCoeff)) P = 0) : P = 0 :=
  eichlerWeightOne_formal_no_rat_ade kryDivisorCoeff kryDivisorCoeff_summable
    kryDivisorCoeff_infinite P hP

/-! ### 9. Tier-1 Witness 2: Weight-1 Cusp-Form Shadow `g₂₃(τ) = η(τ) η(23τ) = (θ_{Q₁} - θ_{Q₂}) / 2` -/

/-- Exact lattice representation count `r_{Q₁}(m) = #{(x, y) ∈ ℤ² : x² + xy + 6y² = m}`.
Every integer solution satisfies `|x|, |y| ≤ 3m` (certified by `mem_box_of_Q1_eq`). -/
@[expose] def repQ1 (m : ℕ) : ℕ :=
  ((Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ)) ×ˢ Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ))).filter
    fun p : ℤ × ℤ => p.1 ^ 2 + p.1 * p.2 + 6 * p.2 ^ 2 = (m : ℤ)).card

/-- Exact lattice representation count `r_{Q₂}(m) = #{(x, y) ∈ ℤ² : 2x² + xy + 3y² = m}`.
Every integer solution satisfies `|x|, |y| ≤ 3m` (certified by `mem_box_of_Q2_eq`). -/
@[expose] def repQ2 (m : ℕ) : ℕ :=
  ((Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ)) ×ˢ Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ))).filter
    fun p : ℤ × ℤ => 2 * p.1 ^ 2 + p.1 * p.2 + 3 * p.2 ^ 2 = (m : ℤ)).card

/-- Certification that `repQ1` captures ALL integer solutions `(x, y) ∈ ℤ²`. -/
lemma mem_box_of_Q1_eq {m : ℕ} (hm : 1 ≤ m) {x y : ℤ}
    (h : x ^ 2 + x * y + 6 * y ^ 2 = (m : ℤ)) :
    (x, y) ∈ Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ)) ×ˢ
      Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ)) := by
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hid : (2 * x + y) ^ 2 + 23 * y ^ 2 = 4 * (m : ℤ) := by linear_combination 4 * h
  have hy2 : y ^ 2 ≤ (3 * (m : ℤ)) ^ 2 := by nlinarith [sq_nonneg (2 * x + y)]
  have hxy2 : (2 * x + y) ^ 2 ≤ (3 * (m : ℤ)) ^ 2 := by nlinarith [sq_nonneg y]
  have hy_lo : -(3 * (m : ℤ)) ≤ y := by nlinarith
  have hy_hi : y ≤ 3 * (m : ℤ) := by nlinarith
  have hxy_lo : -(3 * (m : ℤ)) ≤ 2 * x + y := by nlinarith
  have hxy_hi : 2 * x + y ≤ 3 * (m : ℤ) := by nlinarith
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨hy_lo, hy_hi⟩⟩

/-- Certification that `repQ2` captures ALL integer solutions `(x, y) ∈ ℤ²`. -/
lemma mem_box_of_Q2_eq {m : ℕ} (hm : 1 ≤ m) {x y : ℤ}
    (h : 2 * x ^ 2 + x * y + 3 * y ^ 2 = (m : ℤ)) :
    (x, y) ∈ Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ)) ×ˢ
      Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ)) := by
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hid : (4 * x + y) ^ 2 + 23 * y ^ 2 = 8 * (m : ℤ) := by linear_combination 8 * h
  have hy2 : y ^ 2 ≤ (3 * (m : ℤ)) ^ 2 := by nlinarith [sq_nonneg (4 * x + y)]
  have hxy2 : (4 * x + y) ^ 2 ≤ (3 * (m : ℤ)) ^ 2 := by nlinarith [sq_nonneg y]
  have hy_lo : -(3 * (m : ℤ)) ≤ y := by nlinarith
  have hy_hi : y ≤ 3 * (m : ℤ) := by nlinarith
  have hxy_lo : -(3 * (m : ℤ)) ≤ 4 * x + y := by nlinarith
  have hxy_hi : 4 * x + y ≤ 3 * (m : ℤ) := by nlinarith
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨hy_lo, hy_hi⟩⟩

/-- Exact `n`-th Fourier coefficient (`q^{n+1}`) of the weight-1 cusp form
`g₂₃(τ) = η(τ) η(23τ) = (θ_{x²+xy+6y²}(τ) - θ_{2x²+xy+3y²}(τ)) / 2 ∈ S₁(Γ₀(23), (-23/·))`. -/
@[expose] def cuspG23Coeff (n : ℕ) : ℂ :=
  (((repQ1 (n + 1) : ℤ) - (repQ2 (n + 1) : ℤ)) : ℂ) / 2

private lemma prime_23_int : Prime (23 : ℤ) :=
  Int.prime_iff_natAbs_prime.mpr (by decide : Nat.Prime 23)

/-- `Q₂(x, y) = 2x² + xy + 3y²` NEVER represents `23^{2k}` for any `k : ℕ`. -/
private lemma no_sol_Q2_pow23 (k : ℕ) :
    ∀ x y : ℤ, 2 * x ^ 2 + x * y + 3 * y ^ 2 ≠ (23 : ℤ) ^ (2 * k) := by
  induction k with
  | zero =>
    intro x y h
    simp only [mul_zero, pow_zero] at h
    have hid : (4 * x + y) ^ 2 + 23 * y ^ 2 = 8 := by linear_combination 8 * h
    have hy0 : y = 0 := by nlinarith [sq_nonneg (4 * x + y)]
    subst hy0
    have hx : 2 * x ^ 2 = 1 := by linarith
    have : (2 : ℤ) ∣ 1 := ⟨x ^ 2, hx.symm⟩
    omega
  | succ k ih =>
    intro x y h
    have hid : (4 * x + y) ^ 2 + 23 * y ^ 2 = 8 * (23 : ℤ) ^ (2 * (k + 1)) := by
      linear_combination 8 * h
    have hpow : (23 : ℤ) ^ (2 * (k + 1)) = 23 * (23 * (23 : ℤ) ^ (2 * k)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, pow_succ, pow_succ]; ring
    have hdvd_sq1 : (23 : ℤ) ∣ (4 * x + y) ^ 2 :=
      ⟨8 * (23 * (23 : ℤ) ^ (2 * k)) - y ^ 2, by linarith [hid, hpow]⟩
    have hdvd1 : (23 : ℤ) ∣ (4 * x + y) := prime_23_int.dvd_of_dvd_pow hdvd_sq1
    obtain ⟨u, hu⟩ := hdvd1
    have hred1 : 23 * u ^ 2 + y ^ 2 = 8 * (23 * (23 : ℤ) ^ (2 * k)) := by
      have hmul : 23 * (23 * u ^ 2 + y ^ 2) = 23 * (8 * (23 * (23 : ℤ) ^ (2 * k))) := by
        linear_combination hid - (4 * x + y + 23 * u) * hu - 8 * hpow
      linarith
    have hdvd_sq2 : (23 : ℤ) ∣ y ^ 2 :=
      ⟨8 * (23 : ℤ) ^ (2 * k) - u ^ 2, by linarith [hred1]⟩
    have hdvd2 : (23 : ℤ) ∣ y := prime_23_int.dvd_of_dvd_pow hdvd_sq2
    obtain ⟨v, hv⟩ := hdvd2
    have hdvd_4x : (23 : ℤ) ∣ 4 * x := ⟨u - v, by linarith [hu, hv]⟩
    have hdvd_x : (23 : ℤ) ∣ x := (prime_23_int.dvd_or_dvd hdvd_4x).resolve_left (by omega)
    obtain ⟨x', hx'⟩ := hdvd_x
    apply ih x' v
    have hmul : 23 * 23 * (2 * x' ^ 2 + x' * v + 3 * v ^ 2) =
        23 * 23 * (23 : ℤ) ^ (2 * k) := by
      rw [hpow] at h
      linear_combination h - (2 * (x + 23 * x') + y) * hx' - (23 * x' + 3 * (y + 23 * v)) * hv
    linarith

private lemma repQ2_pow23_eq_zero (k : ℕ) : repQ2 (23 ^ (2 * k)) = 0 := by
  unfold repQ2
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hp
  exact no_sol_Q2_pow23 k p.1 p.2 (by exact_mod_cast hp)

private lemma repQ1_pow23_pos (k : ℕ) : 0 < repQ1 (23 ^ (2 * k)) := by
  unfold repQ1
  refine Finset.card_pos.mpr ⟨((23 : ℤ) ^ k, 0), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · have hpow : (23 : ℤ) ^ k * (23 : ℤ) ^ k = (23 : ℤ) ^ (2 * k) := by
      rw [← pow_add, two_mul]
    have hge1 : (1 : ℤ) ≤ (23 : ℤ) ^ k := one_le_pow₀ (by norm_num)
    have hle : (23 : ℤ) ^ k ≤ ((23 ^ (2 * k) : ℕ) : ℤ) := by
      push_cast; nlinarith
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩,
        Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩
  · push_cast
    rw [show 2 * k = k + k by omega, pow_add]
    ring

private lemma cuspG23Coeff_pow23_ne_zero (k : ℕ) :
    cuspG23Coeff (23 ^ (2 * k) - 1) ≠ 0 := by
  have h1 : 1 ≤ 23 ^ (2 * k) := Nat.one_le_pow (2 * k) 23 (by norm_num)
  have hadd : 23 ^ (2 * k) - 1 + 1 = 23 ^ (2 * k) := Nat.sub_add_cancel h1
  unfold cuspG23Coeff
  rw [hadd, repQ2_pow23_eq_zero k]
  simp only [Nat.cast_zero, Int.cast_zero, sub_zero, Int.cast_natCast]
  exact div_ne_zero (Nat.cast_ne_zero.mpr (repQ1_pow23_pos k).ne') (by norm_num)

private lemma box_card_le (m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ)) ×ˢ
      Finset.Icc (-(3 * (m : ℤ))) (3 * (m : ℤ))).card : ℝ) ≤ 49 * (m : ℝ) ^ 2 := by
  rw [Finset.card_product, Int.card_Icc]
  have hcard : (3 * (m : ℤ) + 1 - -(3 * (m : ℤ))).toNat = 6 * m + 1 := by omega
  rw [hcard]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  push_cast
  nlinarith

private lemma cuspG23Coeff_summable :
    Summable (fun n : ℕ => ‖cuspG23Coeff n‖ * Real.exp (-freq n)) := by
  refine summable_of_poly_bound (C := 49) (d := 2) fun n => ?_
  unfold cuspG23Coeff
  rw [norm_div, Complex.norm_ofNat]
  have hQ1 : (repQ1 (n + 1) : ℝ) ≤ 49 * ((n : ℝ) + 1) ^ 2 := by
    have h1 : (repQ1 (n + 1) : ℝ) ≤
        ((Finset.Icc (-(3 * ((n + 1 : ℕ) : ℤ))) (3 * ((n + 1 : ℕ) : ℤ)) ×ˢ
          Finset.Icc (-(3 * ((n + 1 : ℕ) : ℤ))) (3 * ((n + 1 : ℕ) : ℤ))).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    exact h1.trans (by simpa [Nat.cast_add, Nat.cast_one] using box_card_le (n + 1) (by omega))
  have hQ2 : (repQ2 (n + 1) : ℝ) ≤ 49 * ((n : ℝ) + 1) ^ 2 := by
    have h1 : (repQ2 (n + 1) : ℝ) ≤
        ((Finset.Icc (-(3 * ((n + 1 : ℕ) : ℤ))) (3 * ((n + 1 : ℕ) : ℤ)) ×ˢ
          Finset.Icc (-(3 * ((n + 1 : ℕ) : ℤ))) (3 * ((n + 1 : ℕ) : ℤ))).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    exact h1.trans (by simpa [Nat.cast_add, Nat.cast_one] using box_card_le (n + 1) (by omega))
  have hnorm : ‖(((repQ1 (n + 1) : ℤ) - (repQ2 (n + 1) : ℤ)) : ℂ)‖ ≤
      (repQ1 (n + 1) : ℝ) + (repQ2 (n + 1) : ℝ) := by
    push_cast
    calc ‖(repQ1 (n + 1) : ℂ) - (repQ2 (n + 1) : ℂ)‖
        ≤ ‖(repQ1 (n + 1) : ℂ)‖ + ‖(repQ2 (n + 1) : ℂ)‖ := norm_sub_le _ _
      _ = (repQ1 (n + 1) : ℝ) + (repQ2 (n + 1) : ℝ) := by
          rw [Complex.norm_natCast, Complex.norm_natCast]
  linarith

private lemma cuspG23Coeff_infinite : {n : ℕ | cuspG23Coeff n ≠ 0}.Infinite := by
  refine infinite_support_of_subseq (fun k => 23 ^ (2 * k) - 1) ?_ cuspG23Coeff_pow23_ne_zero
  intro a b hab
  have h1 : 1 ≤ 23 ^ (2 * a) := Nat.one_le_pow (2 * a) 23 (by norm_num)
  have hlt : 23 ^ (2 * a) < 23 ^ (2 * b) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact Nat.sub_lt_sub_right h1 hlt

/-- Concrete `HigherOrderBorelData` witness for the weight-1 cusp form shadow
`g₂₃(τ) = η(τ) η(23τ) ∈ S₁(Γ₀(23), (-23/·))`. -/
def cuspG23_borelData :
    HigherOrderBorelData (eichlerBorel cuspG23Coeff) Real.pi (poleFreq cuspG23Coeff)
      (fun _ => 1) (fun k s => if s = 1 then cuspG23Coeff (suppIdx cuspG23Coeff k) else 0) :=
  eichlerWeightOne_borelData cuspG23Coeff cuspG23Coeff_summable cuspG23Coeff_infinite

/-- **Tier-1 Witness 2 (Weight-1 Cusp-Form Shadow `g₂₃(τ) = η(τ) η(23τ)`)**:
The split weight-1 Eichler integral of `g₂₃(τ) = η(τ) η(23τ)` satisfies NO nonzero
rational-coefficient differential equation over `ℂ(u)` (zero extra hypotheses). -/
theorem cuspG23_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral cuspG23Coeff) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  eichlerWeightOne_no_rat_ade cuspG23Coeff cuspG23Coeff_summable cuspG23Coeff_infinite P hP

/-- Formal Borel-level D-transcendence for the weight-1 cusp-form shadow `g₂₃(τ) = η(τ) η(23τ)`. -/
theorem cuspG23_formal_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (eichlerBorel cuspG23Coeff)) P = 0) : P = 0 :=
  eichlerWeightOne_formal_no_rat_ade cuspG23Coeff cuspG23Coeff_summable
    cuspG23Coeff_infinite P hP

end

end PakPrimes.MockModularWeightOne
