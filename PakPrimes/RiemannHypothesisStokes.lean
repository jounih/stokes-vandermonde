module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.HolderGamma
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Riemann Hypothesis → Von Mangoldt Borel–Stokes Differential Transcendence Bridge

This module formalizes the **Critical-Line Von Mangoldt Borel–Stokes Bridge** directly on
Mathlib's literal `RiemannHypothesis` predicate, stacking on `PakPrimes.HigherOrderStokes`
along the rotated critical-line ray `θ₀ = π / 2` (`e^{i π / 2} = i`).

## Mathematical Architecture
1. **Pole-Subtracted Critical-Line Borel Kernel (`phiLambdaRaw`, `phiLambda`, `G_Lambda`)**:
   - Raw pole-subtracted logarithmic derivative:
     `phiLambdaRaw ξ := -(deriv riemannZeta (1 / 2 + ξ)) / riemannZeta (1 / 2 + ξ) - 1 / (ξ - 1 / 2)`.
   - Analytic continuation across the removable singularity at `ξ = 1 / 2` (`s = 1`) via Mathlib's
     entire completion `riemannZeta₁ s = 1 + (s - 1) * riemannZeta₀ s`:
     `phiLambda ξ := -(deriv riemannZeta₁ (1 / 2 + ξ)) / riemannZeta₁ (1 / 2 + ξ)`.
   - Unconditionally:
     * `phiLambda ξ = phiLambdaRaw ξ` whenever `ξ ≠ 1 / 2` and `riemannZeta (1 / 2 + ξ) ≠ 0`,
     * `phiLambda (1 / 2) = -γ_E` (`-(Real.eulerMascheroniConstant : ℂ)`),
     * `AnalyticAt ℂ phiLambda (1 / 2)` and `Tendsto phiLambdaRaw (𝓝[≠] (1 / 2)) (𝓝 (-γ_E))`,
     * `riemannZeta (1 / 2) ≠ 0` (proved unconditionally from scratch via the paired alternating
       Dirichlet eta series on `{s : ℂ | 0 < s.re}`), hence `AnalyticAt ℂ phiLambda 0`,
     * `G_Lambda := formalSeries phiLambda = formalSeries phiLambdaRaw`.
2. **Simple Poles with Arbitrary Multiplicity (No Simplicity Assumption)**:
   - At any zero `ρ = 1 / 2 + i γ` of `riemannZeta`, `phiLambda` has a simple pole at `ξ = i γ`
     with exact principal part `-(zeroMultiplicity γ : ℂ) / (ξ - i γ)`, where
     `zeroMultiplicity γ = analyticOrderNatAt riemannZeta (1 / 2 + i γ) ≥ 1`, hence nonzero
     residue `-m_ρ ∈ ℤ_{<0}` unconditionally without assuming simple zeros.
3. **Exact Role of Mathlib's `RiemannHypothesis`**:
   - Unconditionally, `phiLambda` is holomorphic on `{ξ | 1 / 2 ≤ ξ.re}` and on
     `{ξ | ξ.re ≤ -1 / 2 ∧ ξ.im ≠ 0}`.
   - Under Mathlib's literal `RiemannHypothesis`, EVERY nontrivial zero lies on `ξ.re = 0`,
     rendering `phiLambda` holomorphic on `{ξ | 0 < ξ.re}`, on `{ξ | -1 / 2 < ξ.re ∧ ξ.re < 0}`,
     on `{ξ | ξ.re < 0 ∧ ξ.im ≠ 0}`, and on the entire rotated punctured wedge
     `rotatedPuncturedWedge (π / 2) α₀ ε (criticalLineZeroSeq hInf)`.
4. **Flanking-Ray & Real-Axis Exponential-Type Bounds (Discharged Unconditionally from RH)**:
   - On the right flanking ray `e^{i (π/2 - θ)} ℝ_{≥0}` and the real ray `ℝ_{≥0}`: bounded `O(1)`
     for large `r` via `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.
   - On the left flanking ray `e^{i (π/2 + θ)} ℝ_{≥0}`: linear growth `O(r)` (hence exponential
     type) via `logDeriv_riemannZeta_one_sub`, boundedness of `tan` for `Im z ≤ -1`, and the
     linear digamma bound `‖digamma s‖ ≤ C₀ + C₁ ‖s - 1‖` on `Re s ≥ 1` (via `HolderGamma.trigamma`).
5. **External Theorems Box (Explicit & Minimal)**:
   - `RiemannHypothesis` (Mathlib's literal `Prop`, composing directly with any Lean-certified
     proof of RH without external imports).
   - `InfinitelyManyCriticalLineZeros` (`{γ : ℝ | 0 < γ ∧ riemannZeta (1 / 2 + I * γ) = 0}.Infinite`,
     Hardy 1914 / Riemann–von Mangoldt, not yet in Mathlib).
   - Both `riemannZeta (1 / 2) ≠ 0` and the flanking-ray exponential-type bounds are **proved
     in full inside this file** and do NOT appear as external assumptions.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.RiemannHypothesisStokes

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.HigherOrderStokes
open PakPrimes.HolderGamma
open scoped Topology Interval

noncomputable section

/-! ### 1. Public Definitions and External Theorems Box -/

/-- Raw pole-subtracted critical-line logarithmic derivative of `riemannZeta`:
`Φ_Λ^{raw}(ξ) = -ζ'(1/2 + ξ)/ζ(1/2 + ξ) - 1/(ξ - 1/2)`. -/
@[expose] def phiLambdaRaw (ξ : ℂ) : ℂ :=
  -(deriv riemannZeta (1 / 2 + ξ)) / riemannZeta (1 / 2 + ξ) - 1 / (ξ - 1 / 2)

/-- Analytic continuation of `phiLambdaRaw` across the removable singularity at `ξ = 1 / 2` (`s = 1`),
defined via Mathlib's entire completion `riemannZeta₁ s = 1 + (s - 1) * riemannZeta₀ s`:
`Φ_Λ(ξ) = -ζ₁'(1/2 + ξ) / ζ₁(1/2 + ξ)`. -/
@[expose] def phiLambda (ξ : ℂ) : ℂ :=
  -(deriv riemannZeta₁ (1 / 2 + ξ)) / riemannZeta₁ (1 / 2 + ξ)

/-- Formal Von Mangoldt critical-line Borel–Laplace series
`G_Λ(u) = ∑_{k ≥ 0} Φ_Λ^{(k)}(0) u^{-(k+1)} ∈ ℂ[[1/u]]`. -/
@[expose] def G_Lambda : PowerSeries ℂ :=
  formalSeries phiLambda

/-- Pole-subtracted regularized real-axis Laplace integral
`G_Λ^{reg}(u) = ∫_0^∞ e^{-u ξ} Φ_Λ(ξ) dξ` (`u > 0`). -/
@[expose] def G_Lambda_laplace (u : ℝ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (ξ : ℂ)) * phiLambda (ξ : ℂ)

/-- Positive ordinates of critical-line zeros of `riemannZeta`. -/
@[expose] def criticalLinePosZeros : Set ℝ :=
  {γ : ℝ | 0 < γ ∧ riemannZeta (1 / 2 + I * (γ : ℂ)) = 0}

/-- Vanishing multiplicity `m_ρ ≥ 1` of `riemannZeta` at `1 / 2 + i γ`. -/
@[expose] def zeroMultiplicity (γ : ℝ) : ℕ :=
  analyticOrderNatAt riemannZeta (1 / 2 + I * (γ : ℂ))

/-- **External Theorem Input (Hardy 1914 / Riemann–von Mangoldt)**:
`riemannZeta` has infinitely many zeros `1 / 2 + i γ` with `γ > 0` on the critical line.
This is the ONLY external theorem hypothesis beyond Mathlib's literal `RiemannHypothesis`. -/
@[expose] def InfinitelyManyCriticalLineZeros : Prop :=
  criticalLinePosZeros.Infinite

/-- Convenience constructor for `InfinitelyManyCriticalLineZeros` from any strictly increasing
sequence of positive critical-line zero ordinates. -/
lemma infinitelyManyCriticalLineZeros_of_seq (γ : ℕ → ℝ) (h0 : 0 < γ 0)
    (hmono : StrictMono γ) (hzero : ∀ k : ℕ, riemannZeta (1 / 2 + I * (γ k : ℂ)) = 0) :
    InfinitelyManyCriticalLineZeros := by
  have hsub : Set.range γ ⊆ criticalLinePosZeros := by
    rintro _ ⟨k, rfl⟩
    exact ⟨lt_of_lt_of_le h0 (hmono.monotone (Nat.zero_le k)), hzero k⟩
  exact (Set.infinite_range_of_injective hmono.injective).mono hsub

/-! ### 2. Unconditional Nonvanishing of `riemannZeta` on `(0, 1)` via Paired Dirichlet Eta -/

/-- Paired alternating Dirichlet eta series `η(s) = ∑_{k ≥ 0} ((2k+1)^{-s} - (2k+2)^{-s})`,
which converges locally uniformly on `{s : ℂ | 0 < s.re}`. -/
private def dirichletEtaTerm (k : ℕ) (s : ℂ) : ℂ :=
  ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)

private def dirichletEta (s : ℂ) : ℂ :=
  ∑' k : ℕ, dirichletEtaTerm k s

private lemma dirichletEtaTerm_eq_integral (k : ℕ) (s : ℂ) :
    dirichletEtaTerm k s =
      s * ∫ t in ((2 * k + 1 : ℕ) : ℝ)..((2 * k + 2 : ℕ) : ℝ), (t : ℂ) ^ (-s - 1) := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * k + 2 : ℕ) : ℝ)
  have ha_pos : 0 < a := by positivity
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact_mod_cast (show 2 * k + 1 ≤ 2 * k + 2 by omega)
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => -((x : ℂ) ^ (-s))) (s * (t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht.1
    have hslit : (t : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using ht_pos)
    have hc : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) (t : ℂ) :=
      (Complex.hasStrictDerivAt_cpow_const (c := -s) hslit).hasDerivAt
    have hcomp : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
      simpa using hc.comp_ofReal
    have hneg : HasDerivAt (fun x : ℝ => -((x : ℂ) ^ (-s))) (-((-s) * (t : ℂ) ^ (-s - 1))) t :=
      hcomp.fun_neg
    simpa [neg_mul] using hneg
  have hcont : ContinuousOn (fun t : ℝ => s * (t : ℂ) ^ (-s - 1)) (Set.uIcc a b) := by
    refine continuousOn_const.mul ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht.1
    have hslit : (t : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using ht_pos)
    have hc : ContinuousAt (fun z : ℂ => z ^ (-s - 1)) (t : ℂ) :=
      (Complex.hasStrictDerivAt_cpow_const (c := -s - 1) hslit).hasDerivAt.continuousAt
    exact (ContinuousAt.comp (g := fun z : ℂ => z ^ (-s - 1)) (f := fun x : ℝ => (x : ℂ))
      hc Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hint
  have hL : -((b : ℂ) ^ (-s)) - -((a : ℂ) ^ (-s)) = dirichletEtaTerm k s := by
    dsimp only [dirichletEtaTerm, a, b]
    push_cast
    ring
  rw [← hL, ← hint]

private lemma norm_dirichletEtaTerm_le (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖dirichletEtaTerm k s‖ ≤ ‖s‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1))) := by
  rw [dirichletEtaTerm_eq_integral, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * k + 2 : ℕ) : ℝ)
  have ha_pos : 0 < a := by positivity
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact_mod_cast (show 2 * k + 1 ≤ 2 * k + 2 by omega)
  have hba : b - a = 1 := by
    dsimp only [a, b]; push_cast; ring
  have hbd : ∀ t ∈ Set.Ioc a b, ‖(t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-(s.re + 1)) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht.1.le
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hre : (-s - 1).re = -(s.re + 1) := by simp; ring
    rw [hre]
    have hexp_neg : -(s.re + 1) ≤ 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos ha_pos ht.1.le hexp_neg
  have hnorm_int := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := a ^ (-(s.re + 1))) (f := fun t : ℝ => (t : ℂ) ^ (-s - 1)) fun t ht => by
      rw [Set.uIoc_of_le hab] at ht
      exact hbd t ht
  rw [hba, abs_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), mul_one] at hnorm_int
  exact hnorm_int

private lemma summable_odd_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ => (((2 * k + 1 : ℕ) : ℝ) ^ (-p))) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hp
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    dsimp at h
    omega
  exact hnat.comp_injective hinj

private lemma dirichletEta_differentiableOn :
    DifferentiableOn ℂ dirichletEta {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  let r : ℝ := min (s₀.re / 2) 1
  have hr_pos : 0 < r := lt_min (half_pos hs₀) one_pos
  have hr_le : r ≤ s₀.re / 2 := min_le_left _ _
  have hball_re : ∀ s ∈ Metric.ball s₀ r, s₀.re / 2 < s.re := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h1 := (abs_lt.mp (hre.trans_lt hs)).1
    linarith
  have hball_norm : ∀ s ∈ Metric.ball s₀ r, ‖s‖ ≤ ‖s₀‖ + r := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have htri : ‖s‖ ≤ ‖s - s₀‖ + ‖s₀‖ := by simpa [sub_add_cancel] using norm_add_le (s - s₀) s₀
    linarith
  let M : ℝ := ‖s₀‖ + r
  let p : ℝ := 1 + s₀.re / 2
  have hp : 1 < p := by dsimp only [p]; linarith
  have hu : Summable (fun k : ℕ => M * (((2 * k + 1 : ℕ) : ℝ) ^ (-p))) :=
    (summable_odd_rpow_neg hp).mul_left M
  have hdiff_ball : DifferentiableOn ℂ dirichletEta (Metric.ball s₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu (fun k => ?_) Metric.isOpen_ball
      (fun k s hs => ?_)
    · have h1 : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * k + 1 ≠ 0 by omega)
      have h2 : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * k + 2 ≠ 0 by omega)
      refine DifferentiableOn.sub ?_ ?_
      · exact (differentiableOn_id.neg.const_cpow (Or.inl h1))
      · exact (differentiableOn_id.neg.const_cpow (Or.inl h2))
    · have hre_s : s₀.re / 2 < s.re := hball_re s hs
      have hre_pos : 0 < s.re := lt_trans (half_pos hs₀) hre_s
      have hle1 := norm_dirichletEtaTerm_le k hre_pos
      have hbase_ge1 : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
      have hrpow_le : (((2 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1))) ≤
          (((2 * k + 1 : ℕ) : ℝ) ^ (-p)) :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge1 (by dsimp only [p]; linarith)
      exact hle1.trans (mul_le_mul (hball_norm s hs) hrpow_le (by positivity) (by positivity))
  exact (hdiff_ball.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))).differentiableWithinAt

private lemma dirichletEta_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = dirichletEta s := by
  let f : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) ^ (-s)
  have hsum : Summable f := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs
    have hshift : Summable (fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) :=
      h0.comp_injective Nat.succ_injective
    refine hshift.congr fun n => ?_
    dsimp only [f]
    rw [one_div, Complex.cpow_neg]
  have hzeta : riemannZeta s = ∑' n : ℕ, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun n => ?_
    dsimp only [f]
    rw [one_div, Complex.cpow_neg]
    push_cast; rfl
  have heven_sub : Summable (fun k : ℕ => f (2 * k)) :=
    hsum.comp_injective (fun a b h => by omega)
  have hodd_sub : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hsum.comp_injective (fun a b h => by omega)
  have hsplit : riemannZeta s = (∑' k : ℕ, f (2 * k)) + (∑' k : ℕ, f (2 * k + 1)) := by
    rw [hzeta]
    exact (heven_sub.hasSum.even_add_odd hodd_sub.hasSum).tsum_eq
  have h2_term : ∀ k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * f k := by
    intro k
    dsimp only [f]
    have hmul : ((2 * k + 1 + 1 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hmul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    push_cast; rfl
  have hodd_eq : ∑' k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [hzeta, ← tsum_mul_left]
    exact tsum_congr h2_term
  have hpow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  have heta_eq : dirichletEta s = (∑' k : ℕ, f (2 * k)) - (∑' k : ℕ, f (2 * k + 1)) := by
    unfold dirichletEta dirichletEtaTerm
    rw [← heven_sub.tsum_sub hodd_sub]
  rw [heta_eq, hpow]
  linear_combination hsplit + 2 * hodd_eq

private lemma isPreconnected_re_pos_sdiff_one :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
  let U₁ : Set ℂ := {s : ℂ | 0 < s.re ∧ 0 < s.im}
  let U₂ : Set ℂ := {s : ℂ | 0 < s.re ∧ s.im < 0}
  let U₃ : Set ℂ := {s : ℂ | 1 < s.re}
  let U₄ : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}
  have hconv_pos : ∀ (a b x y : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 → 0 < x → 0 < y → 0 < a * x + b * y := by
    intro a b x y ha hb hab hx hy
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; linarith
    · nlinarith
  have hU₁ : IsPreconnected U₁ := by
    refine Convex.isPreconnected fun x hx y hy a b ha hb hab => ?_
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact hconv_pos a b x.re y.re ha hb hab hx.1 hy.1
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      exact hconv_pos a b x.im y.im ha hb hab hx.2 hy.2
  have hU₂ : IsPreconnected U₂ := by
    refine Convex.isPreconnected fun x hx y hy a b ha hb hab => ?_
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact hconv_pos a b x.re y.re ha hb hab hx.1 hy.1
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      have hneg := hconv_pos a b (-x.im) (-y.im) ha hb hab (neg_pos.mpr hx.2) (neg_pos.mpr hy.2)
      linarith
  have hU₃ : IsPreconnected U₃ := by
    refine Convex.isPreconnected fun x hx y hy a b ha hb hab => ?_
    change 1 < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have h1 := hconv_pos a b (x.re - 1) (y.re - 1) ha hb hab (sub_pos.mpr hx) (sub_pos.mpr hy)
    nlinarith
  have hU₄ : IsPreconnected U₄ := by
    refine Convex.isPreconnected fun x hx y hy a b ha hb hab => ?_
    change 0 < (a • x + b • y).re ∧ (a • x + b • y).re < 1
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    refine ⟨hconv_pos a b x.re y.re ha hb hab hx.1 hy.1, ?_⟩
    have h1 := hconv_pos a b (1 - x.re) (1 - y.re) ha hb hab (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)
    nlinarith
  have h13 : IsPreconnected (U₁ ∪ U₃) := hU₁.union (2 + I) (by simp [U₁]) (by simp [U₃]) hU₃
  have h132 : IsPreconnected ((U₁ ∪ U₃) ∪ U₂) :=
    h13.union (2 - I) (Or.inr (by simp [U₃])) (by simp [U₂]) hU₂
  have h1324 : IsPreconnected (((U₁ ∪ U₃) ∪ U₂) ∪ U₄) :=
    h132.union (1 / 2 + I) (Or.inl (Or.inl (by simp [U₁]))) (by simp [U₄]; norm_num) hU₄
  have heq : (((U₁ ∪ U₃) ∪ U₂) ∪ U₄) = {s : ℂ | 0 < s.re} \ {(1 : ℂ)} := by
    ext s
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      U₁, U₂, U₃, U₄]
    constructor
    · rintro (((⟨hre, him⟩ | hre) | ⟨hre, him⟩) | ⟨hre, hlt⟩)
      · exact ⟨hre, fun h => by rw [h] at him; simp at him⟩
      · exact ⟨by linarith, fun h => by rw [h] at hre; simp at hre⟩
      · exact ⟨hre, fun h => by rw [h] at him; simp at him⟩
      · exact ⟨hre, fun h => by rw [h] at hlt; simp at hlt⟩
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy s.re 1 with hlt | hreq | hgt
      · exact Or.inr ⟨hre, hlt⟩
      · rcases lt_trichotomy s.im 0 with him | himeq | him
        · exact Or.inl (Or.inr ⟨hre, him⟩)
        · exfalso; apply hne; exact Complex.ext hreq himeq
        · exact Or.inl (Or.inl (Or.inl ⟨hre, him⟩))
      · exact Or.inl (Or.inl (Or.inr hgt))
  rwa [← heq]

private lemma dirichletEta_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = dirichletEta s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {(1 : ℂ)}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hLHS : AnalyticOnNhd ℂ (fun z : ℂ => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - w)) z :=
      (differentiableAt_const (1 : ℂ)).sub differentiableAt_id |>.const_cpow (Or.inl (by norm_num))
    exact (((differentiableAt_const (1 : ℂ)).sub hpow).mul
      (differentiableAt_riemannZeta hz.2)).differentiableWithinAt
  have hRHS : AnalyticOnNhd ℂ dirichletEta U :=
    (dirichletEta_differentiableOn.mono Set.sdiff_subset).analyticOnNhd hU_open
  have h2_mem : (2 : ℂ) ∈ U := ⟨by simp, by norm_num⟩
  have hev : (fun z : ℂ => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) =ᶠ[𝓝 (2 : ℂ)] dirichletEta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    exact dirichletEta_eq_of_one_lt_re hz
  exact hLHS.eqOn_of_preconnected_of_eventuallyEq hRHS isPreconnected_re_pos_sdiff_one h2_mem hev
    ⟨hs, hs1⟩

/-- **Unconditional Nonvanishing of `riemannZeta` on `(0, 1)`**:
For every real `x ∈ (0, 1)`, `riemannZeta (x : ℂ) ≠ 0` (in fact `riemannZeta x < 0`). -/
theorem riemannZeta_ne_zero_of_real_pos_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  have hx_re : 0 < (x : ℂ).re := by simpa using hx0
  have hx_ne1 : (x : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have heq := dirichletEta_eq_of_re_pos hx_re hx_ne1
  have hterm_real : ∀ k : ℕ,
      dirichletEtaTerm k (x : ℂ) =
        ((((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) := by
    intro k
    unfold dirichletEtaTerm
    rw [Complex.ofReal_sub,
      Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
    simp
  have hsummable_real :
      Summable (fun k : ℕ => (((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x))) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      ((summable_odd_rpow_neg (show 1 < x + 1 by linarith)).mul_left ‖(x : ℂ)‖)
    · have hle : ((2 * k + 2 : ℕ) : ℝ) ^ (-x) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-x) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (show 2 * k + 1 ≤ 2 * k + 2 by omega))
          (by linarith)
      linarith
    · have hnorm := norm_dirichletEtaTerm_le k hx_re
      rw [hterm_real k, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg] at hnorm
      · simpa using hnorm
      · have hle : ((2 * k + 2 : ℕ) : ℝ) ^ (-x) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-x) :=
          Real.rpow_le_rpow_of_nonpos (by positivity)
            (by exact_mod_cast (show 2 * k + 1 ≤ 2 * k + 2 by omega)) (by linarith)
        linarith
  have heta_eq : dirichletEta (x : ℂ) =
      ((∑' k : ℕ, (((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x)) : ℝ) : ℂ) := by
    unfold dirichletEta
    simp_rw [hterm_real]
    exact (Complex.ofReal_tsum _).symm
  have hsum_pos :
      0 < ∑' k : ℕ, (((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x)) := by
    refine hsummable_real.tsum_pos (fun k => ?_) 0 ?_
    · have hle : ((2 * k + 2 : ℕ) : ℝ) ^ (-x) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-x) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (by exact_mod_cast (show 2 * k + 1 ≤ 2 * k + 2 by omega)) (by linarith)
      linarith
    · simp only [mul_zero, zero_add, Nat.cast_one, Real.one_rpow, Nat.cast_ofNat, sub_pos]
      exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr hx0)
  have heta_ne : dirichletEta (x : ℂ) ≠ 0 := by
    rw [heta_eq]
    exact Complex.ofReal_ne_zero.mpr hsum_pos.ne'
  intro hzeta0
  rw [hzeta0, mul_zero] at heq
  exact heta_ne heq.symm

/-- **Unconditional Nonvanishing at `s = 1 / 2`**: `riemannZeta (1 / 2) ≠ 0`. -/
theorem riemannZeta_half_ne_zero : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  simpa using riemannZeta_ne_zero_of_real_pos_lt_one (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

/-! ### 3. Unconditional Removable Singularity at `ξ = 1 / 2` and Holomorphicity at `ξ = 0` -/

/-- Exact characterization of zeros of Mathlib's entire completion `riemannZeta₁`. -/
lemma riemannZeta₁_eq_zero_iff {s : ℂ} :
    riemannZeta₁ s = 0 ↔ s ≠ 1 ∧ riemannZeta s = 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [riemannZeta₁_one]
  · constructor
    · intro h0
      refine ⟨hs, ?_⟩
      rw [riemannZeta_eq_inv_sub_mul hs, h0, mul_zero]
    · rintro ⟨_, h0⟩
      rw [riemannZeta_eq_inv_sub_mul hs] at h0
      exact (mul_eq_zero.mp h0).resolve_left (inv_ne_zero (sub_ne_zero.mpr hs))

lemma riemannZeta₁_ne_zero_of_ne {s : ℂ} (h : s = 1 ∨ riemannZeta s ≠ 0) :
    riemannZeta₁ s ≠ 0 := by
  intro h0
  obtain ⟨hs1, hζ0⟩ := riemannZeta₁_eq_zero_iff.mp h0
  exact h.elim hs1 (fun hne => hne hζ0)

/-- Exact identity between `phiLambda` and `phiLambdaRaw` at every point away from `ξ = 1 / 2`
where `riemannZeta (1 / 2 + ξ) ≠ 0`. -/
theorem phiLambda_eq_raw {ξ : ℂ} (hξ : ξ ≠ 1 / 2) (hζ : riemannZeta (1 / 2 + ξ) ≠ 0) :
    phiLambda ξ = phiLambdaRaw ξ := by
  have hs1 : (1 / 2 : ℂ) + ξ ≠ 1 := by
    intro h
    apply hξ
    linear_combination h
  have hsub : (1 / 2 : ℂ) + ξ - 1 = ξ - 1 / 2 := by ring
  have hsub_ne : ξ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hξ
  have hz1_ne : riemannZeta₁ (1 / 2 + ξ) ≠ 0 := riemannZeta₁_ne_zero_of_ne (Or.inr hζ)
  unfold phiLambda phiLambdaRaw
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1, riemannZeta_eq_inv_sub_mul hs1, hsub]
  set u : ℂ := ξ - 1 / 2
  set a : ℂ := riemannZeta₁ (1 / 2 + ξ)
  set b : ℂ := deriv riemannZeta₁ (1 / 2 + ξ)
  field_simp [hsub_ne, hz1_ne]
  ring

/-- Exact value at the removable singularity `ξ = 1 / 2` (`s = 1`): `Φ_Λ(1 / 2) = -γ_E`. -/
theorem phiLambda_half : phiLambda (1 / 2) = -(Real.eulerMascheroniConstant : ℂ) := by
  have h1 : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  rw [phiLambda, h1, riemannZeta₁_one, deriv_riemannZeta₁_one, div_one]

/-- `phiLambda` is analytic at every `ξ` where `riemannZeta₁ (1 / 2 + ξ) ≠ 0`. -/
lemma phiLambda_analyticAt_of_zeta1_ne_zero {ξ : ℂ} (h : riemannZeta₁ (1 / 2 + ξ) ≠ 0) :
    AnalyticAt ℂ phiLambda ξ := by
  have h1_entire : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ
  have hshift : AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) ξ :=
    analyticAt_const.add analyticAt_id
  have hnum : AnalyticAt ℂ (fun w : ℂ => -(deriv riemannZeta₁ (1 / 2 + w))) ξ :=
    ((h1_entire.deriv (1 / 2 + ξ) (Set.mem_univ _)).comp hshift).neg
  have hden : AnalyticAt ℂ (fun w : ℂ => riemannZeta₁ (1 / 2 + w)) ξ :=
    (h1_entire (1 / 2 + ξ) (Set.mem_univ _)).comp hshift
  exact hnum.div hden h

/-- **Unconditional Removable Singularity Theorem at `ξ = 1 / 2` (`s = 1`)**:
`phiLambda` is analytic at `ξ = 1 / 2` (the simple pole of `-ζ'/ζ` at `s = 1` is cancelled
by `-1 / (ξ - 1 / 2)`). -/
theorem phiLambda_analyticAt_half : AnalyticAt ℂ phiLambda (1 / 2) := by
  refine phiLambda_analyticAt_of_zeta1_ne_zero ?_
  have h1 : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  rw [h1, riemannZeta₁_one]
  exact one_ne_zero

/-- The raw pole-subtracted logarithmic derivative `phiLambdaRaw ξ` tends to `-γ_E` as `ξ → 1 / 2`. -/
theorem phiLambdaRaw_tendsto_half :
    Tendsto phiLambdaRaw (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hcont : Tendsto phiLambda (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    rw [← phiLambda_half]
    exact phiLambda_analyticAt_half.continuousAt.continuousWithinAt
  have hshift_cont : ContinuousAt (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (1 / 2 : ℂ) :=
    continuousAt_const.add continuousAt_id
  have hshift : Tendsto (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (1 : ℂ)) := by
    have h := hshift_cont.continuousWithinAt (s := {(1 / 2 : ℂ)}ᶜ)
    have h1 : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
    change Tendsto (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 ((1 / 2 : ℂ) + 1 / 2)) at h
    rwa [h1] at h
  have hne : ∀ᶠ ξ in 𝓝[≠] (1 / 2 : ℂ), riemannZeta₁ (1 / 2 + ξ) ≠ 0 :=
    hshift.eventually riemannZeta₁_ne_zero_of_near_one
  refine hcont.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin, hne] with ξ hξ hζ1
  have hξ_ne : ξ ≠ 1 / 2 := hξ
  have hζ : riemannZeta (1 / 2 + ξ) ≠ 0 := by
    intro h0
    apply hζ1
    refine riemannZeta₁_eq_zero_iff.mpr ⟨?_, h0⟩
    intro h1
    apply hξ_ne
    linear_combination h1
  exact phiLambda_eq_raw hξ_ne hζ

/-- **Unconditional Holomorphicity at `ξ = 0`**: `phiLambda` is analytic at `ξ = 0`. -/
theorem phiLambda_analyticAt_zero : AnalyticAt ℂ phiLambda 0 := by
  refine phiLambda_analyticAt_of_zeta1_ne_zero ?_
  rw [add_zero]
  exact riemannZeta₁_ne_zero_of_ne (Or.inr riemannZeta_half_ne_zero)

/-- `phiLambda` and `phiLambdaRaw` agree identically on an open neighborhood of `ξ = 0`. -/
lemma phiLambda_eventuallyEq_raw_zero : phiLambda =ᶠ[𝓝 (0 : ℂ)] phiLambdaRaw := by
  have hne_half : ∀ᶠ ξ : ℂ in 𝓝 (0 : ℂ), ξ ≠ 1 / 2 :=
    isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1 / 2)
  have hshift : ContinuousAt (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) 0 :=
    continuousAt_const.add continuousAt_id
  have hdiff : ContinuousAt riemannZeta ((1 / 2 : ℂ) + 0) := by
    rw [add_zero]
    exact (differentiableAt_riemannZeta (by norm_num : (1 / 2 : ℂ) ≠ 1)).continuousAt
  have hzeta_cont : ContinuousAt (fun ξ : ℂ => riemannZeta (1 / 2 + ξ)) 0 :=
    ContinuousAt.comp (g := riemannZeta) (f := fun ξ : ℂ => (1 / 2 : ℂ) + ξ) hdiff hshift
  have hzeta_ne : ∀ᶠ ξ : ℂ in 𝓝 (0 : ℂ), riemannZeta (1 / 2 + ξ) ≠ 0 :=
    hzeta_cont.eventually_ne (by simpa using riemannZeta_half_ne_zero)
  filter_upwards [hne_half, hzeta_ne] with ξ hξ hζ
  exact phiLambda_eq_raw hξ hζ

/-- **Unconditional Formal Series Identity**: `G_Lambda = formalSeries phiLambda = formalSeries phiLambdaRaw`. -/
theorem G_Lambda_eq_formalSeries_raw : G_Lambda = formalSeries phiLambdaRaw := by
  ext n
  cases n with
  | zero => simp [G_Lambda, formalSeries]
  | succ k =>
    simp only [G_Lambda, formalSeries, PowerSeries.coeff_mk]
    exact phiLambda_eventuallyEq_raw_zero.iteratedDeriv_eq k

/-! ### 4. Unconditional Simple Pole & Negative-Integer Residue `-m_ρ` at Every Critical-Line Zero -/

private lemma half_add_I_mul_ne_one (γ : ℝ) : (1 / 2 : ℂ) + I * (γ : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

private lemma riemannZeta_analyticOrderAt_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have hzero := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconn hs htop
  have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by norm_num
  exact riemannZeta_ne_zero_of_one_le_re (s := (2 : ℂ)) (by simp) (hzero h2)

/-- Every critical-line zero `1 / 2 + i γ` has positive finite vanishing multiplicity `m_ρ ≥ 1`
(no simplicity assumption). -/
theorem zeroMultiplicity_pos {γ : ℝ} (hγ : riemannZeta (1 / 2 + I * (γ : ℂ)) = 0) :
    1 ≤ zeroMultiplicity γ := by
  have hs1 : (1 / 2 : ℂ) + I * (γ : ℂ) ≠ 1 := half_add_I_mul_ne_one γ
  have hana : AnalyticAt ℂ riemannZeta (1 / 2 + I * (γ : ℂ)) :=
    analyticOn_riemannZeta _ hs1
  have hne_top : analyticOrderAt riemannZeta (1 / 2 + I * (γ : ℂ)) ≠ ⊤ :=
    riemannZeta_analyticOrderAt_ne_top hs1
  have hne_zero : analyticOrderAt riemannZeta (1 / 2 + I * (γ : ℂ)) ≠ 0 :=
    hana.analyticOrderAt_ne_zero.mpr hγ
  have hnat_ne : zeroMultiplicity γ ≠ 0 := by
    intro h0
    apply hne_zero
    rw [← Nat.cast_analyticOrderNatAt hne_top]
    exact_mod_cast h0
  omega

/-- **Unconditional Simple Pole Principal Part at Any Critical-Line Zero (Arbitrary Multiplicity)**:
For any zero `1 / 2 + i γ` of `riemannZeta`, `phiLambda ξ - (-m_ρ) / (ξ - i γ)` extends
continuously to `ξ = i γ`, where `m_ρ = zeroMultiplicity γ ≥ 1`. -/
theorem phiLambda_simple_pole_principalPart {γ : ℝ}
    (hγ : riemannZeta (1 / 2 + I * (γ : ℂ)) = 0) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun ξ : ℂ => phiLambda ξ - (-((zeroMultiplicity γ : ℕ) : ℂ)) / (ξ - I * (γ : ℂ)))
        (𝓝[≠] (I * (γ : ℂ))) (𝓝 L) := by
  let s₀ : ℂ := 1 / 2 + I * (γ : ℂ)
  let m : ℕ := zeroMultiplicity γ
  have hm_pos : 1 ≤ m := zeroMultiplicity_pos hγ
  have hs1 : s₀ ≠ 1 := half_add_I_mul_ne_one γ
  have hana : AnalyticAt ℂ riemannZeta s₀ := analyticOn_riemannZeta s₀ hs1
  have hne_top : analyticOrderAt riemannZeta s₀ ≠ ⊤ := riemannZeta_analyticOrderAt_ne_top hs1
  obtain ⟨g, hg_ana, hg0, hfg⟩ := hana.analyticOrderAt_ne_top.mp hne_top
  let h : ℂ → ℂ := fun ξ => g (1 / 2 + ξ)
  have hshift : AnalyticAt ℂ (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (I * (γ : ℂ)) :=
    analyticAt_const.add analyticAt_id
  have hh_ana : AnalyticAt ℂ h (I * (γ : ℂ)) :=
    AnalyticAt.comp (g := g) (f := fun ξ : ℂ => (1 / 2 : ℂ) + ξ) hg_ana hshift
  have hh0 : h (I * (γ : ℂ)) ≠ 0 := hg0
  have hshift_tend : Tendsto (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) (𝓝 (I * (γ : ℂ))) (𝓝 s₀) :=
    hshift.continuousAt
  have hzeta_ev : (fun ξ : ℂ => riemannZeta (1 / 2 + ξ)) =ᶠ[𝓝 (I * (γ : ℂ))]
      fun ξ : ℂ => (ξ - I * (γ : ℂ)) ^ m * h ξ := by
    filter_upwards [hshift_tend.eventually hfg] with ξ hξ
    have hsub : (1 / 2 : ℂ) + ξ - s₀ = ξ - I * (γ : ℂ) := by dsimp only [s₀]; ring
    change riemannZeta (1 / 2 + ξ) = (ξ - I * (γ : ℂ)) ^ m * g (1 / 2 + ξ)
    have hξ' : riemannZeta (1 / 2 + ξ) = (1 / 2 + ξ - s₀) ^ m * g (1 / 2 + ξ) := by
      simpa [m, zeroMultiplicity, s₀, smul_eq_mul] using hξ
    rw [hξ', hsub]
  have hderiv_zeta : ∀ᶠ ξ in 𝓝 (I * (γ : ℂ)),
      deriv riemannZeta (1 / 2 + ξ) =
        (m : ℂ) * (ξ - I * (γ : ℂ)) ^ (m - 1) * h ξ + (ξ - I * (γ : ℂ)) ^ m * deriv h ξ := by
    have hcomp_deriv : ∀ᶠ ξ in 𝓝 (I * (γ : ℂ)),
        deriv (fun w : ℂ => riemannZeta (1 / 2 + w)) ξ = deriv riemannZeta (1 / 2 + ξ) := by
      filter_upwards [hshift_tend.eventually (isOpen_ne.mem_nhds hs1)] with ξ hξ1
      have hd : HasDerivAt (fun w : ℂ => riemannZeta (1 / 2 + w))
          (deriv riemannZeta (1 / 2 + ξ) * 1) ξ :=
        (differentiableAt_riemannZeta hξ1).hasDerivAt.comp ξ
          ((hasDerivAt_const ξ (1 / 2 : ℂ)).add (hasDerivAt_id ξ) |>.congr_deriv (zero_add 1))
      simpa using hd.deriv
    have hprod_deriv : ∀ᶠ ξ in 𝓝 (I * (γ : ℂ)),
        deriv (fun w : ℂ => (w - I * (γ : ℂ)) ^ m * h w) ξ =
          (m : ℂ) * (ξ - I * (γ : ℂ)) ^ (m - 1) * h ξ + (ξ - I * (γ : ℂ)) ^ m * deriv h ξ := by
      filter_upwards [hh_ana.eventually_analyticAt] with ξ hξh
      have hd1 : HasDerivAt (fun w : ℂ => (w - I * (γ : ℂ)) ^ m)
          ((m : ℂ) * (ξ - I * (γ : ℂ)) ^ (m - 1)) ξ := by
        simpa using ((hasDerivAt_id ξ).sub_const (I * (γ : ℂ))).fun_pow m
      exact (hd1.mul hξh.differentiableAt.hasDerivAt).deriv
    filter_upwards [hzeta_ev.eventually_nhds, hcomp_deriv, hprod_deriv] with ξ hzeq hcd hpd
    have hzeq' : (fun w : ℂ => riemannZeta (1 / 2 + w)) =ᶠ[𝓝 ξ]
        fun w : ℂ => (w - I * (γ : ℂ)) ^ m * h w := hzeq
    rw [← hcd, Filter.EventuallyEq.deriv_eq hzeq', hpd]
  have hne_half : ∀ᶠ ξ in 𝓝 (I * (γ : ℂ)), ξ ≠ 1 / 2 :=
    isOpen_ne.mem_nhds fun heq => hs1 (by dsimp only [s₀]; rw [heq]; norm_num)
  have hh_ne : ∀ᶠ ξ in 𝓝 (I * (γ : ℂ)), h ξ ≠ 0 := hh_ana.continuousAt.eventually_ne hh0
  have hrem_ana : AnalyticAt ℂ (fun ξ : ℂ => -(deriv h ξ) / h ξ - 1 / (ξ - 1 / 2)) (I * (γ : ℂ)) := by
    have hξ0_ne : I * (γ : ℂ) - 1 / 2 ≠ 0 := by
      intro h0
      apply hs1
      dsimp only [s₀]
      linear_combination h0
    exact (hh_ana.deriv.neg.div hh_ana hh0).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hξ0_ne)
  refine ⟨-(deriv h (I * (γ : ℂ))) / h (I * (γ : ℂ)) - 1 / (I * (γ : ℂ) - 1 / 2), ?_⟩
  refine hrem_ana.continuousAt.continuousWithinAt.tendsto.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    hzeta_ev.filter_mono nhdsWithin_le_nhds,
    hderiv_zeta.filter_mono nhdsWithin_le_nhds,
    hne_half.filter_mono nhdsWithin_le_nhds,
    hh_ne.filter_mono nhdsWithin_le_nhds] with ξ hξ_ne hze hdz hnh hhn
  have hsub_ne : ξ - I * (γ : ℂ) ≠ 0 := sub_ne_zero.mpr hξ_ne
  have hpow_ne : (ξ - I * (γ : ℂ)) ^ m ≠ 0 := pow_ne_zero m hsub_ne
  have hzeta_ne : riemannZeta (1 / 2 + ξ) ≠ 0 := by
    rw [hze]; exact mul_ne_zero hpow_ne hhn
  rw [phiLambda_eq_raw hnh hzeta_ne, phiLambdaRaw, hze, hdz]
  have hpow_split : (ξ - I * (γ : ℂ)) ^ m = (ξ - I * (γ : ℂ)) ^ (m - 1) * (ξ - I * (γ : ℂ)) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  have hpow1_ne : (ξ - I * (γ : ℂ)) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hsub_ne
  rw [hpow_split]
  field_simp [hsub_ne, hpow1_ne, hhn]
  ring

/-- **Unconditional Simple Pole & Nonzero Residue Theorem at Any Critical-Line Zero**:
For any zero `1 / 2 + i γ` of `riemannZeta`, `(ξ - i γ) * phiLambda ξ → -m_ρ ≠ 0` as `ξ → i γ`. -/
theorem phiLambda_simple_pole_at_zero {γ : ℝ} (hγ : riemannZeta (1 / 2 + I * (γ : ℂ)) = 0) :
    Filter.Tendsto (fun ξ : ℂ => (ξ - I * (γ : ℂ)) * phiLambda ξ)
      (𝓝[≠] (I * (γ : ℂ))) (𝓝 (-((zeroMultiplicity γ : ℕ) : ℂ))) ∧
    (-((zeroMultiplicity γ : ℕ) : ℂ)) ≠ 0 := by
  obtain ⟨L, hL⟩ := phiLambda_simple_pole_principalPart hγ
  have hm_ne : (-((zeroMultiplicity γ : ℕ) : ℂ)) ≠ 0 := by
    have hm_pos : 1 ≤ zeroMultiplicity γ := zeroMultiplicity_pos hγ
    exact neg_ne_zero.mpr (by exact_mod_cast (show zeroMultiplicity γ ≠ 0 by omega))
  refine ⟨?_, hm_ne⟩
  have hsub_cont : ContinuousAt (fun ξ : ℂ => ξ - I * (γ : ℂ)) (I * (γ : ℂ)) :=
    continuousAt_id.sub continuousAt_const
  have hsub0 : Tendsto (fun ξ : ℂ => ξ - I * (γ : ℂ)) (𝓝[≠] (I * (γ : ℂ))) (𝓝 (0 : ℂ)) := by
    have h0 : I * (γ : ℂ) - I * (γ : ℂ) = 0 := sub_self _
    exact h0 ▸ hsub_cont.continuousWithinAt
  have hmul := (hsub0.mul hL).add (tendsto_const_nhds (x := -((zeroMultiplicity γ : ℕ) : ℂ)))
  rw [zero_mul, zero_add] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ξ hξ
  have hsub_ne : ξ - I * (γ : ℂ) ≠ 0 := sub_ne_zero.mpr hξ
  field_simp [hsub_ne]
  ring

/-! ### 5. Role of Mathlib's `RiemannHypothesis`: Holomorphicity on Open Half-Planes & Punctured Wedge -/

/-- **Unconditional Right Half-Plane Holomorphicity**: `phiLambda` is holomorphic on `{ξ | 1/2 ≤ ξ.re}`,
using `riemannZeta_ne_zero_of_one_le_re` and removable singularity cancellation at `ξ = 1 / 2`. -/
theorem phiLambda_analyticOn_right_of_half :
    AnalyticOnNhd ℂ phiLambda {ξ : ℂ | 1 / 2 ≤ ξ.re} := by
  intro ξ hξ
  change 1 / 2 ≤ ξ.re at hξ
  refine phiLambda_analyticAt_of_zeta1_ne_zero ?_
  have hs_re : 1 ≤ ((1 / 2 : ℂ) + ξ).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  exact riemannZeta₁_ne_zero_of_ne (Or.inr (riemannZeta_ne_zero_of_one_le_re hs_re))

/-- **Unconditional Left Half-Plane Holomorphicity (Away from Trivial Zeros)**:
`phiLambda` is holomorphic on `{ξ | ξ.re ≤ -1 / 2 ∧ ξ.im ≠ 0}`, using `riemannZeta_eq_zero_iff_of_re_nonpos`
(which follows from Riemann's functional equation `riemannZeta_one_sub`). -/
theorem phiLambda_analyticOn_left_of_neg_half :
    AnalyticOnNhd ℂ phiLambda {ξ : ℂ | ξ.re ≤ -1 / 2 ∧ ξ.im ≠ 0} := by
  intro ξ hξ
  refine phiLambda_analyticAt_of_zeta1_ne_zero ?_
  have hs_re : ((1 / 2 : ℂ) + ξ).re ≤ 0 := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith [hξ.1]
  refine riemannZeta₁_ne_zero_of_ne (Or.inr fun h0 => ?_)
  obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hs_re).mp h0
  have him := congrArg Complex.im hn
  simp at him
  exact hξ.2 him

/-- Under Mathlib's literal `RiemannHypothesis`, `riemannZeta₁ (1 / 2 + ξ) ≠ 0` whenever
`ξ.re ≠ 0` and `(0 < ξ.re ∨ ξ.im ≠ 0 ∨ -1 / 2 < ξ.re)`. -/
lemma riemannZeta₁_ne_zero_of_RH (hRH : RiemannHypothesis) {ξ : ℂ}
    (hre : ξ.re ≠ 0) (htriv : -1 / 2 < ξ.re ∨ ξ.im ≠ 0) :
    riemannZeta₁ (1 / 2 + ξ) ≠ 0 := by
  intro h0
  obtain ⟨hs1, hζ0⟩ := riemannZeta₁_eq_zero_iff.mp h0
  have hnot_triv : ¬∃ n : ℕ, (1 / 2 : ℂ) + ξ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    rcases htriv with hre_gt | him_ne
    · have hre_eq := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
        Complex.neg_re, Complex.re_ofNat, Complex.natCast_re, Complex.neg_im, Complex.im_ofNat,
        Complex.add_im, Complex.natCast_im, Complex.one_im, add_zero, mul_zero, sub_zero] at hre_eq
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · have him_eq := congrArg Complex.im hn
      simp at him_eq
      exact him_ne him_eq
  have hcrit := hRH ((1 / 2 : ℂ) + ξ) hζ0 hnot_triv hs1
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hcrit
  exact hre (by linarith)

/-- **Exact Role of Mathlib's `RiemannHypothesis` — Holomorphicity on Open Flanking Half-Planes**:
Under `RiemannHypothesis`, `phiLambda` is holomorphic on:
1. `{ξ : ℂ | 0 < ξ.re}` (entire open right half-plane, including the removable pole at `ξ = 1 / 2`),
2. `{ξ : ℂ | -1 / 2 < ξ.re ∧ ξ.re < 0}` (open left half of the critical strip), and
3. `{ξ : ℂ | ξ.re < 0 ∧ ξ.im ≠ 0}` (entire open left half-plane away from the negative real axis). -/
theorem phiLambda_holomorphic_on_open_wedges_of_RH (hRH : RiemannHypothesis) :
    AnalyticOnNhd ℂ phiLambda {ξ : ℂ | 0 < ξ.re} ∧
    AnalyticOnNhd ℂ phiLambda {ξ : ℂ | -1 / 2 < ξ.re ∧ ξ.re < 0} ∧
    AnalyticOnNhd ℂ phiLambda {ξ : ℂ | ξ.re < 0 ∧ ξ.im ≠ 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ
    change 0 < ξ.re at hξ
    exact phiLambda_analyticAt_of_zeta1_ne_zero
      (riemannZeta₁_ne_zero_of_RH hRH (ne_of_gt hξ) (Or.inl (by linarith)))
  · intro ξ hξ
    exact phiLambda_analyticAt_of_zeta1_ne_zero
      (riemannZeta₁_ne_zero_of_RH hRH (ne_of_lt hξ.2) (Or.inl hξ.1))
  · intro ξ hξ
    exact phiLambda_analyticAt_of_zeta1_ne_zero
      (riemannZeta₁_ne_zero_of_RH hRH (ne_of_lt hξ.1) (Or.inr hξ.2))

private lemma criticalLinePosZeros_inter_Icc_finite (R : ℝ) :
    (criticalLinePosZeros ∩ Set.Icc 0 R).Finite := by
  let f : ℝ → ℂ := fun γ => 1 / 2 + I * (γ : ℂ)
  have hf_cont : Continuous f :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hf_inj : Function.Injective f := by
    intro a b hab
    have him := congrArg Complex.im hab
    simpa [f] using him
  have hcomp : IsCompact (f '' Set.Icc 0 R) := isCompact_Icc.image hf_cont
  have hfin_img : ((f '' Set.Icc 0 R) ∩ riemannZetaZeros).Finite :=
    hcomp.inter_riemannZetaZeros_finite
  have hsub : f '' (criticalLinePosZeros ∩ Set.Icc 0 R) ⊆ (f '' Set.Icc 0 R) ∩ riemannZetaZeros := by
    rintro _ ⟨γ, ⟨hγz, hγI⟩, rfl⟩
    exact ⟨⟨γ, hγI, rfl⟩, hγz.2⟩
  exact Set.Finite.of_finite_image (hfin_img.subset hsub) hf_inj.injOn

private lemma criticalLinePosZeros_exists_least {S : Set ℝ}
    (hsub : S ⊆ criticalLinePosZeros) (hne : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, m ≤ x := by
  obtain ⟨x₀, hx₀⟩ := hne
  let T : Set ℝ := S ∩ Set.Icc 0 x₀
  have hT_fin : T.Finite :=
    (criticalLinePosZeros_inter_Icc_finite x₀).subset (Set.inter_subset_inter_left _ hsub)
  have hx₀_pos : 0 < x₀ := (hsub hx₀).1
  have hT_ne : T.Nonempty := ⟨x₀, hx₀, hx₀_pos.le, le_rfl⟩
  let m : ℝ := hT_fin.toFinset.min' (hT_fin.toFinset_nonempty.mpr hT_ne)
  have hm_mem : m ∈ T := hT_fin.mem_toFinset.mp (Finset.min'_mem _ _)
  refine ⟨m, hm_mem.1, fun x hx => ?_⟩
  by_cases hle : x ≤ x₀
  · have hxT : x ∈ T := ⟨hx, (hsub hx).1.le, hle⟩
    exact Finset.min'_le _ _ (hT_fin.mem_toFinset.mpr hxT)
  · exact hm_mem.2.2.trans (le_of_not_ge hle)

private lemma criticalLinePosZeros_above_nonempty (hInf : InfinitelyManyCriticalLineZeros) (a : ℝ) :
    {γ ∈ criticalLinePosZeros | a < γ}.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : criticalLinePosZeros ⊆ criticalLinePosZeros ∩ Set.Icc 0 a := by
    intro γ hγ
    refine ⟨hγ, hγ.1.le, ?_⟩
    by_contra hgt
    push Not at hgt
    have : γ ∈ ({x ∈ criticalLinePosZeros | a < x} : Set ℝ) := ⟨hγ, hgt⟩
    rw [h] at this
    exact this
  exact hInf ((criticalLinePosZeros_inter_Icc_finite a).subset hsub)

/-- Canonical strictly increasing enumeration of ALL positive critical-line zeros of `riemannZeta`,
constructed from `InfinitelyManyCriticalLineZeros` and Mathlib's `IsCompact.inter_riemannZetaZeros_finite`. -/
def criticalLineZeroSeq (hInf : InfinitelyManyCriticalLineZeros) : ℕ → ℝ
  | 0 => Classical.choose (criticalLinePosZeros_exists_least Subset.rfl hInf.nonempty)
  | n + 1 =>
    let a := criticalLineZeroSeq hInf n
    Classical.choose (criticalLinePosZeros_exists_least
      (S := {γ ∈ criticalLinePosZeros | a < γ})
      (fun _ hx => hx.1) (criticalLinePosZeros_above_nonempty hInf a))

lemma criticalLineZeroSeq_mem (hInf : InfinitelyManyCriticalLineZeros) (n : ℕ) :
    criticalLineZeroSeq hInf n ∈ criticalLinePosZeros := by
  cases n with
  | zero =>
    exact (Classical.choose_spec
      (criticalLinePosZeros_exists_least Subset.rfl hInf.nonempty)).1
  | succ n =>
    exact (Classical.choose_spec (criticalLinePosZeros_exists_least
      (S := {γ ∈ criticalLinePosZeros | criticalLineZeroSeq hInf n < γ})
      (fun _ hx => hx.1)
      (criticalLinePosZeros_above_nonempty hInf (criticalLineZeroSeq hInf n)))).1.1

lemma criticalLineZeroSeq_pos (hInf : InfinitelyManyCriticalLineZeros) (n : ℕ) :
    0 < criticalLineZeroSeq hInf n :=
  (criticalLineZeroSeq_mem hInf n).1

lemma criticalLineZeroSeq_zero (hInf : InfinitelyManyCriticalLineZeros) (n : ℕ) :
    riemannZeta (1 / 2 + I * (criticalLineZeroSeq hInf n : ℂ)) = 0 :=
  (criticalLineZeroSeq_mem hInf n).2

lemma criticalLineZeroSeq_strictMono (hInf : InfinitelyManyCriticalLineZeros) :
    StrictMono (criticalLineZeroSeq hInf) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact (Classical.choose_spec (criticalLinePosZeros_exists_least
    (S := {γ ∈ criticalLinePosZeros | criticalLineZeroSeq hInf n < γ})
    (fun _ hx => hx.1)
    (criticalLinePosZeros_above_nonempty hInf (criticalLineZeroSeq hInf n)))).1.2

lemma criticalLineZeroSeq_tendsto_atTop (hInf : InfinitelyManyCriticalLineZeros) :
    Tendsto (criticalLineZeroSeq hInf) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro R
  have hex : ∃ N : ℕ, R ≤ criticalLineZeroSeq hInf N := by
    by_contra! hall
    have hsub : Set.range (criticalLineZeroSeq hInf) ⊆ criticalLinePosZeros ∩ Set.Icc 0 R := by
      rintro _ ⟨n, rfl⟩
      exact ⟨criticalLineZeroSeq_mem hInf n, (criticalLineZeroSeq_pos hInf n).le, (hall n).le⟩
    exact (Set.infinite_range_of_injective (criticalLineZeroSeq_strictMono hInf).injective)
      ((criticalLinePosZeros_inter_Icc_finite R).subset hsub)
  obtain ⟨N, hN⟩ := hex
  exact ⟨N, fun n hn => hN.trans ((criticalLineZeroSeq_strictMono hInf).monotone hn)⟩

/-- `criticalLineZeroSeq hInf` exhausts EVERY positive critical-line zero (no missing zeros!). -/
lemma criticalLineZeroSeq_range (hInf : InfinitelyManyCriticalLineZeros) :
    Set.range (criticalLineZeroSeq hInf) = criticalLinePosZeros := by
  ext γ
  constructor
  · rintro ⟨n, rfl⟩
    exact criticalLineZeroSeq_mem hInf n
  · intro hγ
    classical
    have hex : ∃ n : ℕ, γ ≤ criticalLineZeroSeq hInf n := by
      obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp (criticalLineZeroSeq_tendsto_atTop hInf)) γ
      exact ⟨N, hN N le_rfl⟩
    let n : ℕ := Nat.find hex
    have hn_le : γ ≤ criticalLineZeroSeq hInf n := Nat.find_spec hex
    refine ⟨n, ?_⟩
    cases hne : n with
    | zero =>
      have hmin := (Classical.choose_spec
        (criticalLinePosZeros_exists_least Subset.rfl hInf.nonempty)).2 γ hγ
      rw [hne] at hn_le
      exact le_antisymm hmin hn_le
    | succ k =>
      have hk_lt : criticalLineZeroSeq hInf k < γ := by
        have hnot : ¬(γ ≤ criticalLineZeroSeq hInf k) :=
          Nat.find_min hex (by omega : k < n)
        exact lt_of_not_ge hnot
      have hmin := (Classical.choose_spec (criticalLinePosZeros_exists_least
        (S := {x ∈ criticalLinePosZeros | criticalLineZeroSeq hInf k < x})
        (fun _ hx => hx.1)
        (criticalLinePosZeros_above_nonempty hInf (criticalLineZeroSeq hInf k)))).2 γ ⟨hγ, hk_lt⟩
      rw [hne] at hn_le
      exact le_antisymm hmin hn_le

private lemma exists_zero_free_ball_half :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : ℂ, ‖ξ‖ < ε → riemannZeta₁ (1 / 2 + ξ) ≠ 0 := by
  have hmem : (1 / 2 : ℂ) ∈ riemannZetaZerosᶜ := riemannZeta_half_ne_zero
  obtain ⟨ε, hε_pos, hε_sub⟩ :=
    Metric.isOpen_iff.mp isClosed_riemannZetaZeros.isOpen_compl (1 / 2 : ℂ) hmem
  refine ⟨ε, hε_pos, fun ξ hξ => ?_⟩
  have hball : (1 / 2 : ℂ) + ξ ∈ Metric.ball (1 / 2 : ℂ) ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hξ
  exact riemannZeta₁_ne_zero_of_ne (Or.inr (hε_sub hball))

private lemma exp_I_pi_div_two : Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ)) = I := by
  rw [show I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I by ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two,
    ← Complex.ofReal_sin, Real.sin_pi_div_two]
  simp

private lemma exp_neg_I_pi_div_two : Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ)) = -I := by
  rw [show -I * ((Real.pi / 2 : ℝ) : ℂ) = -(((Real.pi / 2 : ℝ) : ℂ) * I) by ring,
    Complex.exp_neg, show ((Real.pi / 2 : ℝ) : ℂ) * I = I * ((Real.pi / 2 : ℝ) : ℂ) by ring,
    exp_I_pi_div_two, inv_I]

/-- **Holomorphicity on the Entire Rotated Punctured Wedge Around `θ₀ = π / 2` under RH**:
For ANY `α₀ < π / 2` and zero-free disk radius `ε > 0` around `0`, `phiLambda` is holomorphic on
`rotatedPuncturedWedge (Real.pi / 2) α₀ ε (criticalLineZeroSeq hInf)`. -/
theorem phiLambda_analyticOn_rotatedPuncturedWedge_of_RH
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {α₀ ε : ℝ} (hball : ∀ ξ : ℂ, ‖ξ‖ < ε → riemannZeta₁ (1 / 2 + ξ) ≠ 0) :
    AnalyticOnNhd ℂ phiLambda
      (rotatedPuncturedWedge (Real.pi / 2) α₀ ε (criticalLineZeroSeq hInf)) := by
  intro ξ hξ
  refine phiLambda_analyticAt_of_zeta1_ne_zero ?_
  rcases hξ with ⟨hwedge, hnot_pole⟩
  rw [exp_neg_I_pi_div_two] at hwedge hnot_pole
  rcases hwedge with hball_mem | ⟨him_pos, _⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_neg, Complex.norm_I, one_mul] at hball_mem
    exact hball ξ hball_mem
  · have hξ_im : 0 < ξ.im := by
      simpa [Complex.mul_re] using him_pos
    intro h0
    obtain ⟨hs1, hζ0⟩ := riemannZeta₁_eq_zero_iff.mp h0
    have hnot_triv : ¬∃ n : ℕ, (1 / 2 : ℂ) + ξ = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have him := congrArg Complex.im hn
      simp at him
      linarith
    have hcrit := hRH ((1 / 2 : ℂ) + ξ) hζ0 hnot_triv hs1
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hcrit
    have hξ_re : ξ.re = 0 := by linarith
    have hξ_eq : ξ = I * (ξ.im : ℂ) := Complex.ext (by simp [hξ_re]) (by simp)
    have hmem_Z : ξ.im ∈ criticalLinePosZeros := ⟨hξ_im, by rwa [← hξ_eq]⟩
    rw [← criticalLineZeroSeq_range hInf] at hmem_Z
    obtain ⟨m, hm⟩ := hmem_Z
    apply hnot_pole
    refine ⟨m, ?_⟩
    rw [hξ_eq, ← hm]
    have hmul : -I * (I * (criticalLineZeroSeq hInf m : ℂ)) =
        ((-I) * I) * (criticalLineZeroSeq hInf m : ℂ) := by ring
    rw [hmul]
    simp

/-! ### 6. Unconditional Flanking-Ray & Real-Axis Exponential-Type Growth Bounds -/

/-- Uniform `O(1)` bound on `ζ'/ζ` in the half-plane `Re s ≥ 2`, proved directly from
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. -/
private lemma logDeriv_riemannZeta_bounded_of_two_le_re :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ M := by
  have hsum2 : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp)
  have hsum_norm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖) :=
    hsum2.norm
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖,
    tsum_nonneg (fun _ => norm_nonneg _), fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have hnorm_eq : ‖deriv riemannZeta s / riemannZeta s‖ =
      ‖LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s‖ := by
    rw [hL, neg_div, norm_neg]
  rw [hnorm_eq, LSeries]
  have hterm_le : ∀ n : ℕ,
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖ ≤
        ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
    intro n
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte, norm_div]
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have h2re : ((2 : ℂ)).re = 2 := by simp
      rw [h2re]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hn_pos 2)
        (Real.rpow_le_rpow_of_exponent_le hn_ge1 hs)
  have hsum_s : Summable (fun n : ℕ =>
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1).norm
  exact (norm_tsum_le_tsum_norm hsum_s).trans (hsum_s.tsum_le_tsum hterm_le hsum_norm)

/-- Linear growth bound `‖digamma s‖ ≤ C₀ + C₁ ‖s - 1‖` on `{s : ℂ | 1 ≤ s.re}`,
proved from `HolderGamma.trigamma_eq_trigammaSum`, identity theorem on `{z | 0 < z.re}`,
and the fundamental theorem of calculus on `[0, 1]`. -/
private lemma digamma_linear_bound_of_one_le_re :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ s : ℂ, 1 ≤ s.re → ‖Complex.digamma s‖ ≤ C₀ + C₁ * ‖s - 1‖ := by
  -- Step 1: `trigammaSum` is analytic on `{z : ℂ | 0 < z.re}`.
  have hsum_an : AnalyticOnNhd ℂ trigammaSum {z : ℂ | 0 < z.re} := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticOnNhd (fun z₀ hz₀ => ?_) hopen
    let r : ℝ := z₀.re / 2
    have hr_pos : 0 < r := half_pos hz₀
    have hre_gt : ∀ z ∈ Metric.ball z₀ r, r < z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h1 := (abs_lt.mp (hre_diff.trans_lt hz)).1
      dsimp only [r] at *; linarith
    have hbase : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
        Real.summable_one_div_nat_pow.mpr one_lt_two
      exact h0.comp_injective Nat.succ_injective
    let K : ℝ := (1 + 1 / r) ^ 2
    have hu : Summable (fun n : ℕ => K * (1 / (((n + 1 : ℕ) : ℝ) ^ 2))) := hbase.mul_left K
    have hdiff_ball : DifferentiableOn ℂ trigammaSum (Metric.ball z₀ r) := by
      refine Complex.differentiableOn_tsum_of_summable_norm hu (fun n => ?_) Metric.isOpen_ball
        (fun n z hz => ?_)
      · refine DifferentiableOn.div (differentiableOn_const _)
          ((differentiableOn_id.add (differentiableOn_const _)).pow 2) fun z hz => ?_
        have hre := hre_gt z hz
        have hne : z + (n : ℂ) ≠ 0 := by
          intro h0
          have hre0 := congrArg Complex.re h0
          simp at hre0
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact pow_ne_zero 2 hne
      · have hre := hre_gt z hz
        have hnorm_ge : r + (n : ℝ) ≤ ‖z + (n : ℂ)‖ := by
          have h1 : (z + (n : ℂ)).re ≤ ‖z + (n : ℂ)‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
          simp only [Complex.add_re, Complex.natCast_re] at h1
          linarith
        have hratio : ((n + 1 : ℕ) : ℝ) ≤ (1 + 1 / r) * (r + (n : ℝ)) := by
          push_cast
          have h1 : (1 + 1 / r) * (r + (n : ℝ)) = r + (n : ℝ) + 1 + (n : ℝ) / r := by
            field_simp [hr_pos.ne']
            ring
          rw [h1]
          have hnn : 0 ≤ (n : ℝ) / r := by positivity
          linarith
        have hsq : (((n + 1 : ℕ) : ℝ) ^ 2) ≤ K * (r + (n : ℝ)) ^ 2 := by
          dsimp only [K]
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hratio 2
        have hden_pos : 0 < (r + (n : ℝ)) ^ 2 := by positivity
        have hstep1 : ‖(1 : ℂ) / (z + (n : ℂ)) ^ 2‖ ≤ 1 / (r + (n : ℝ)) ^ 2 := by
          rw [norm_div, norm_one, norm_pow]
          exact div_le_div_of_nonneg_left zero_le_one hden_pos
            (pow_le_pow_left₀ (by positivity) hnorm_ge 2)
        have hstep2 : 1 / (r + (n : ℝ)) ^ 2 ≤ K * (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [mul_one_div, div_le_div_iff₀ hden_pos (by positivity)]
          linarith
        exact hstep1.trans hstep2
    exact (hdiff_ball.differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))).differentiableWithinAt
  -- Step 2: Identity theorem on `{z : ℂ | 0 < z.re}` gives `trigamma z = trigammaSum z` everywhere.
  have hpre : IsPreconnected {z : ℂ | 0 < z.re} := by
    refine Convex.isPreconnected fun x hx y hy a b ha hb hab => ?_
    change 0 < x.re at hx
    change 0 < y.re at hy
    change 0 < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; linarith
    · nlinarith
  have hdiff_an : AnalyticOnNhd ℂ (fun z : ℂ => trigamma z - trigammaSum z) {z : ℂ | 0 < z.re} :=
    trigamma_analyticOnNhd_re_pos.sub hsum_an
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), trigamma z - trigammaSum z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [Metric.mem_nhdsWithin_iff] at hU
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := hU
    let x : ℝ := 1 + δ / 2
    have hx_pos : 0 < x := by dsimp only [x]; linarith
    have hx_ball : (x : ℂ) ∈ Metric.ball (1 : ℂ) δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : (x : ℂ) - 1 = ((δ / 2 : ℝ) : ℂ) := by dsimp only [x]; push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ_pos)]
      linarith
    have hx_ne : (x : ℂ) ≠ 1 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp [x] at hre
      linarith
    refine ⟨(x : ℂ), hδ_sub ⟨hx_ball, hx_ne⟩, ?_⟩
    rw [trigamma_eq_trigammaSum hx_pos, sub_self]
  have hEqOn := hdiff_an.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hpre (show (1 : ℂ) ∈ {z : ℂ | 0 < z.re} by simp) hfreq
  -- Step 3: Uniform bound `‖trigamma w‖ ≤ C₁` for all `1 ≤ w.re`.
  have hsum_inv_sq : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
  let C₁ : ℝ := ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2)
  have hC₁_nn : 0 ≤ C₁ := tsum_nonneg fun _ => by positivity
  have htrig_bd : ∀ w : ℂ, 1 ≤ w.re → ‖trigamma w‖ ≤ C₁ := by
    intro w hw
    have hw_pos : 0 < w.re := by linarith
    have heq_w : trigamma w = trigammaSum w := sub_eq_zero.mp (hEqOn hw_pos)
    rw [heq_w, trigammaSum]
    have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (w + (n : ℂ)) ^ 2‖ ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro n
      have hge : ((n + 1 : ℕ) : ℝ) ≤ ‖w + (n : ℂ)‖ := by
        have h1 : (w + (n : ℂ)).re ≤ ‖w + (n : ℂ)‖ :=
          (le_abs_self _).trans (Complex.abs_re_le_norm _)
        simp only [Complex.add_re, Complex.natCast_re] at h1
        push_cast; linarith
      rw [norm_div, norm_one, norm_pow]
      exact div_le_div_of_nonneg_left zero_le_one (by positivity)
        (pow_le_pow_left₀ (by positivity) hge 2)
    have hsum_n : Summable (fun n : ℕ => ‖(1 : ℂ) / (w + (n : ℂ)) ^ 2‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum_inv_sq
    exact (norm_tsum_le_tsum_norm hsum_n).trans (hsum_n.tsum_le_tsum hterm hsum_inv_sq)
  -- Step 4: FTC along `t ↦ 1 + t * (s - 1)` for `t ∈ [0, 1]`.
  refine ⟨‖Complex.digamma 1‖, C₁, norm_nonneg _, hC₁_nn, fun s hs => ?_⟩
  let γ : ℝ → ℂ := fun t => 1 + (t : ℂ) * (s - 1)
  have hγ_re : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 1 ≤ (γ t).re := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [γ, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
    nlinarith [ht.1]
  have hdigamma_diff : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Complex.digamma w := by
    intro w hw
    have hne : ∀ m : ℕ, w ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hG_an_on : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
      refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
        (isOpen_lt continuous_const Complex.continuous_re)
      change 0 < z.re at hz
      refine (Complex.differentiableAt_Gamma z fun m hm => ?_).differentiableWithinAt
      have hre := congrArg Complex.re hm
      simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hG_ana : AnalyticAt ℂ Complex.Gamma w := hG_an_on w hw
    have hG_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hne
    have hdig_eq : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
      ext z; simp [Complex.digamma_def, logDeriv_apply]
    rw [hdig_eq]
    exact (hG_ana.deriv.div hG_ana hG_ne).differentiableAt
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => Complex.digamma (γ x)) ((s - 1) * trigamma (γ t)) t := by
    intro t ht
    have hre_pos : 0 < (γ t).re := lt_of_lt_of_le zero_lt_one (hγ_re t ht)
    have hγ_deriv : HasDerivAt γ (s - 1) t := by
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) t :=
        (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun x : ℝ => (1 : ℂ) + (x : ℂ) * (s - 1)) (0 + 1 * (s - 1)) t :=
        (hasDerivAt_const t (1 : ℂ)).fun_add (h1.mul_const (s - 1))
      simpa [γ] using h2
    have hsc : HasDerivAt (fun x : ℝ => Complex.digamma (γ x))
        ((s - 1) • deriv Complex.digamma (γ t)) t :=
      (hdigamma_diff (γ t) hre_pos).hasDerivAt.scomp t hγ_deriv
    simpa [trigamma, smul_eq_mul] using hsc
  have hcont : ContinuousOn (fun t : ℝ => (s - 1) * trigamma (γ t)) (Set.uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.mul ?_
    intro t ht
    have hre_pos : 0 < (γ t).re := lt_of_lt_of_le zero_lt_one (hγ_re t ht)
    have hγ_cont : ContinuousAt γ t :=
      continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    exact (ContinuousAt.comp (g := trigamma) (f := γ)
      (trigamma_analyticOnNhd_re_pos (γ t) hre_pos).continuousAt hγ_cont).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hγ0 : γ 0 = 1 := by simp [γ]
  have hγ1 : γ 1 = s := by simp [γ]
  rw [hγ0, hγ1] at hint
  have hnorm_sub : ‖Complex.digamma s - Complex.digamma 1‖ ≤ C₁ * ‖s - 1‖ := by
    rw [← hint]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := C₁ * ‖s - 1‖) (f := fun t : ℝ => (s - 1) * trigamma (γ t)) fun t ht => by
        rw [Set.uIoc_of_le zero_le_one] at ht
        have hre := hγ_re t (by rw [Set.uIcc_of_le zero_le_one]; exact ⟨ht.1.le, ht.2⟩)
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (htrig_bd (γ t) hre) (norm_nonneg _)
    simpa using hbd
  have htri : ‖Complex.digamma s‖ ≤ ‖Complex.digamma 1‖ + ‖Complex.digamma s - Complex.digamma 1‖ := by
    simpa [add_sub_cancel] using norm_add_le (Complex.digamma 1) (Complex.digamma s - Complex.digamma 1)
  linarith

private lemma tan_bounded_of_im_le_neg_one {z : ℂ} (hz : z.im ≤ -1) :
    ‖Complex.tan z‖ ≤ 4 := by
  rw [Complex.tan_eq_sin_div_cos, Complex.sin, Complex.cos]
  have hnum : ((Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2) /
      ((Complex.exp (z * I) + Complex.exp (-z * I)) / 2) =
      ((Complex.exp (-z * I) - Complex.exp (z * I)) * I) /
        (Complex.exp (z * I) + Complex.exp (-z * I)) := by
    field_simp
  rw [hnum, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hre1 : (-z * I).re = z.im := by simp [Complex.mul_re]
  have hre2 : (z * I).re = -z.im := by simp [Complex.mul_re]
  have hn1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp, hre1]
  have hn2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp, hre2]
  have hexp_pos : 0 < Real.exp (-z.im) := Real.exp_pos _
  have hle_ratio : Real.exp z.im ≤ Real.exp (-z.im) / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hmul : Real.exp z.im * 2 ≤ Real.exp (-z.im) := by
      calc Real.exp z.im * 2 ≤ Real.exp z.im * Real.exp 2 :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = Real.exp (z.im + 2) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-z.im) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hnum_le : ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ ≤ 2 * Real.exp (-z.im) := by
    calc ‖Complex.exp (-z * I) - Complex.exp (z * I)‖
        ≤ ‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖ := norm_sub_le _ _
      _ = Real.exp z.im + Real.exp (-z.im) := by rw [hn1, hn2]
      _ ≤ 2 * Real.exp (-z.im) := by linarith
  have hden_ge : Real.exp (-z.im) / 2 ≤ ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ := by
    have htri : ‖Complex.exp (z * I)‖ - ‖Complex.exp (-z * I)‖ ≤
        ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ := by
      simpa [sub_neg_eq_add] using norm_sub_norm_le (Complex.exp (z * I)) (-Complex.exp (-z * I))
    rw [hn1, hn2] at htri
    linarith
  have hden_pos : 0 < Real.exp (-z.im) / 2 := by positivity
  calc ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ /
        ‖Complex.exp (z * I) + Complex.exp (-z * I)‖
      ≤ (2 * Real.exp (-z.im)) / (Real.exp (-z.im) / 2) :=
        div_le_div₀ (by positivity) hnum_le hden_pos hden_ge
    _ = 4 := by field_simp [hexp_pos.ne']; ring

/-- **Unconditional Right-Half-Plane Ray Exponential-Type Bound (under RH)**:
Along ANY ray `e^{i σ} ℝ_{≥0}` in the open right half-plane (`cos σ > 0`), including BOTH
the positive real axis (`σ = 0`) and the right flanking ray (`σ = π / 2 - θ`), `phiLambda` is
uniformly bounded (`ExpType` with exponent `0`). -/
theorem phiLambda_expType_right_ray (hRH : RiemannHypothesis) {σ : ℝ} (hcos : 0 < Real.cos σ) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) phiLambda) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I σ
  have hμ_re : μ.re = Real.cos σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re σ
  let R₀ : ℝ := 2 / Real.cos σ
  have hR₀_pos : 0 < R₀ := div_pos two_pos hcos
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ phiLambda v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ phiLambda (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simpa using phiLambda_analyticAt_zero
      · have hre_pos : 0 < (μ * (v : ℂ)).re := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
          exact mul_pos hcos hv_pos
        exact (phiLambda_holomorphic_on_open_wedges_of_RH hRH).1 (μ * (v : ℂ)) hre_pos
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiLambda (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiLambda) (f := fun x : ℝ => μ * (x : ℂ)) hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁_nn, hM₁⟩ := logDeriv_riemannZeta_bounded_of_two_le_re
  let C : ℝ := max (max M₀ 0) (M₁ + 1)
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 0, hC_nn, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hvR : v ≤ R₀
  · exact (hM₀ v ⟨hv, hvR⟩).trans ((le_max_left M₀ 0).trans (le_max_left _ _))
  · push Not at hvR
    have hv_re : 2 < (μ * (v : ℂ)).re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have h1 : 2 < Real.cos σ * v := by
        have := (div_lt_iff₀ hcos).mp hvR
        linarith
      exact h1
    have hs_re : 2 ≤ ((1 / 2 : ℂ) + μ * (v : ℂ)).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hξ_ne : μ * (v : ℂ) ≠ 1 / 2 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.div_ofNat_re, Complex.one_re] at hre
      linarith
    have hζ_ne : riemannZeta (1 / 2 + μ * (v : ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hsub_ge : 1 ≤ ‖μ * (v : ℂ) - 1 / 2‖ := by
      have h1 : (μ * (v : ℂ) - 1 / 2).re ≤ ‖μ * (v : ℂ) - 1 / 2‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at h1
      linarith
    have hphi_le : ‖phiLambda (μ * (v : ℂ))‖ ≤ M₁ + 1 := by
      rw [phiLambda_eq_raw hξ_ne hζ_ne, phiLambdaRaw]
      calc ‖-(deriv riemannZeta (1 / 2 + μ * (v : ℂ))) / riemannZeta (1 / 2 + μ * (v : ℂ)) -
              1 / (μ * (v : ℂ) - 1 / 2)‖
          ≤ ‖-(deriv riemannZeta (1 / 2 + μ * (v : ℂ))) / riemannZeta (1 / 2 + μ * (v : ℂ))‖ +
              ‖(1 : ℂ) / (μ * (v : ℂ) - 1 / 2)‖ := norm_sub_le _ _
        _ = ‖deriv riemannZeta (1 / 2 + μ * (v : ℂ)) / riemannZeta (1 / 2 + μ * (v : ℂ))‖ +
              1 / ‖μ * (v : ℂ) - 1 / 2‖ := by rw [neg_div, norm_neg, norm_div (1 : ℂ), norm_one]
        _ ≤ M₁ + 1 := add_le_add (hM₁ _ hs_re) (by rw [div_le_one (by linarith)]; exact hsub_ge)
    change ‖μ * phiLambda (μ * (v : ℂ))‖ ≤ C
    rw [norm_mul, hμ_norm, one_mul]
    exact hphi_le.trans (le_max_right _ _)

/-- **Unconditional Left-Half-Plane Flanking-Ray Exponential-Type Bound (under RH)**:
Along ANY ray `e^{i σ} ℝ_{≥0}` in the open second quadrant (`cos σ < 0`, `sin σ > 0`),
including the left flanking ray `σ = π / 2 + θ` (`0 < θ < π / 2`), `phiLambda` has linear
growth `O(r)` and hence `ExpType`, proved from `logDeriv_riemannZeta_one_sub`,
`logDeriv_riemannZeta_bounded_of_two_le_re`, `digamma_linear_bound_of_one_le_re`, and
`tan_bounded_of_im_le_neg_one`. -/
theorem phiLambda_expType_left_ray (hRH : RiemannHypothesis) {σ : ℝ}
    (hcos : Real.cos σ < 0) (hsin : 0 < Real.sin σ) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) phiLambda) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hμ_norm : ‖μ‖ = 1 := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I σ
  have hμ_re : μ.re = Real.cos σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re σ
  have hμ_im : μ.im = Real.sin σ := by
    dsimp only [μ]
    rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_im σ
  let R₀ : ℝ := max (2 / (-Real.cos σ)) (2 / Real.sin σ)
  have hR₀_pos : 0 < R₀ := lt_of_lt_of_le (div_pos two_pos (neg_pos.mpr hcos)) (le_max_left _ _)
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ phiLambda v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ phiLambda (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simpa using phiLambda_analyticAt_zero
      · have hre_neg : (μ * (v : ℂ)).re < 0 := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
          exact mul_neg_of_neg_of_pos hcos hv_pos
        have him_ne : (μ * (v : ℂ)).im ≠ 0 := by
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hμ_im]
          exact (mul_pos hsin hv_pos).ne'
        exact (phiLambda_holomorphic_on_open_wedges_of_RH hRH).2.2 (μ * (v : ℂ)) ⟨hre_neg, him_ne⟩
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiLambda (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiLambda) (f := fun x : ℝ => μ * (x : ℂ)) hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁_nn, hM₁⟩ := logDeriv_riemannZeta_bounded_of_two_le_re
  obtain ⟨C₀, C₁, hC₀_nn, hC₁_nn, hdig⟩ := digamma_linear_bound_of_one_le_re
  let K₀ : ℝ := M₁ + ‖Complex.log (2 * (Real.pi : ℂ))‖ + C₀ + C₁ + 2 * Real.pi + 1
  let C : ℝ := max (max M₀ 0) (K₀ + C₁)
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 1, hC_nn, zero_le_one, fun v hv => ?_⟩
  rw [one_mul]
  by_cases hvR : v ≤ R₀
  · calc ‖Minor.pull μ phiLambda v‖ ≤ M₀ := hM₀ v ⟨hv, hvR⟩
      _ ≤ max M₀ 0 := le_max_left _ _
      _ ≤ C := le_max_left _ _
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_left (Real.one_le_exp hv) hC_nn
  · push Not at hvR
    have hv_pos : 0 < v := lt_trans hR₀_pos hvR
    have hv_gt_cos : 2 / (-Real.cos σ) < v := lt_of_le_of_lt (le_max_left _ _) hvR
    have hv_gt_sin : 2 / Real.sin σ < v := lt_of_le_of_lt (le_max_right _ _) hvR
    have hre_le : (μ * (v : ℂ)).re < -2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have := (div_lt_iff₀ (neg_pos.mpr hcos)).mp hv_gt_cos
      linarith
    have him_gt : 2 < (μ * (v : ℂ)).im := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hμ_im]
      have := (div_lt_iff₀ hsin).mp hv_gt_sin
      linarith
    let ξ : ℂ := μ * (v : ℂ)
    let s : ℂ := 1 / 2 + ξ
    let w : ℂ := 1 - s
    have hw_re : 2 ≤ w.re := by
      simp only [w, s, Complex.sub_re, Complex.one_re, Complex.add_re, Complex.div_ofNat_re]
      linarith
    have hw_im : w.im < -2 := by
      simp only [w, s, Complex.sub_im, Complex.one_im, Complex.add_im, Complex.div_ofNat_im,
        zero_div, zero_add, zero_sub]
      linarith
    have hw_not_int : ∀ n : ℤ, w ≠ (n : ℂ) := by
      intro n hn
      have him := congrArg Complex.im hn
      simp at him
      linarith
    have hw_zeta_ne : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hs_re : s.re ≤ 0 := by
      simp only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hs_zeta_ne : riemannZeta s ≠ 0 := by
      intro h0
      obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hs_re).mp h0
      have him := congrArg Complex.im hn
      simp only [s, Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add,
        Complex.mul_im, Complex.neg_re, Complex.re_ofNat, Complex.natCast_im, add_zero,
        mul_zero, Complex.neg_im, Complex.im_ofNat] at him
      linarith
    have hξ_ne : ξ ≠ 1 / 2 := by
      intro h0
      have him := congrArg Complex.im h0
      simp at him
      linarith
    have hfe := logDeriv_riemannZeta_one_sub hw_not_int hw_zeta_ne
    have h1w : 1 - w = s := by dsimp only [w]; ring
    rw [h1w] at hfe
    have hneg_logDeriv : -(deriv riemannZeta s) / riemannZeta s =
        deriv riemannZeta w / riemannZeta w - Complex.log (2 * (Real.pi : ℂ)) +
          Complex.digamma w - (Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2) := by
      have hld_w : logDeriv riemannZeta w = deriv riemannZeta w / riemannZeta w := logDeriv_apply _ _
      have hld_s : logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s := logDeriv_apply _ _
      rw [hld_w, hld_s] at hfe
      linear_combination -hfe
    have htan_im : ((Real.pi : ℂ) * w / 2).im ≤ -1 := by
      have him_eq : ((Real.pi : ℂ) * w / 2).im = Real.pi / 2 * w.im := by
        simp [Complex.mul_im]
        ring
      rw [him_eq]
      nlinarith [Real.pi_gt_three]
    have htan_le : ‖(Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2)‖ ≤ 2 * Real.pi := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_ofNat]
      have ht := tan_bounded_of_im_le_neg_one htan_im
      nlinarith [Real.pi_pos]
    have hw_sub1_norm : ‖w - 1‖ ≤ v + 1 := by
      have hw1 : w - 1 = -(1 / 2 : ℂ) - ξ := by dsimp only [w, s]; ring
      rw [hw1]
      have h1 : ‖-(1 / 2 : ℂ) - ξ‖ ≤ ‖-(1 / 2 : ℂ)‖ + ‖ξ‖ := norm_sub_le _ _
      have hξ_norm : ‖ξ‖ = v := by
        dsimp only [ξ]
        rw [norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
      have hhalf : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      linarith
    have hdig_le : ‖Complex.digamma w‖ ≤ C₀ + C₁ * (v + 1) := by
      have h1 := hdig w (by linarith)
      have h2 := mul_le_mul_of_nonneg_left hw_sub1_norm hC₁_nn
      linarith
    have hsub_ge : 1 ≤ ‖ξ - 1 / 2‖ := by
      have h1 : (ξ - 1 / 2).im ≤ ‖ξ - 1 / 2‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
      simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero] at h1
      linarith
    have hphi_le : ‖phiLambda ξ‖ ≤ K₀ + C₁ * v := by
      rw [phiLambda_eq_raw hξ_ne hs_zeta_ne, phiLambdaRaw, hneg_logDeriv]
      have hstep1 := norm_sub_le
        (deriv riemannZeta w / riemannZeta w - Complex.log (2 * (Real.pi : ℂ)) +
          Complex.digamma w - (Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2))
        (1 / (ξ - 1 / 2))
      have hstep2 := norm_sub_le
        (deriv riemannZeta w / riemannZeta w - Complex.log (2 * (Real.pi : ℂ)) +
          Complex.digamma w)
        ((Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2))
      have hstep3 := norm_add_le
        (deriv riemannZeta w / riemannZeta w - Complex.log (2 * (Real.pi : ℂ)))
        (Complex.digamma w)
      have hstep4 := norm_sub_le
        (deriv riemannZeta w / riemannZeta w)
        (Complex.log (2 * (Real.pi : ℂ)))
      have hinv : ‖(1 : ℂ) / (ξ - 1 / 2)‖ ≤ 1 := by
        rw [norm_div, norm_one, div_le_one (by linarith)]; exact hsub_ge
      have hw_bd := hM₁ w hw_re
      dsimp only [K₀]
      linarith
    change ‖μ * phiLambda ξ‖ ≤ C * Real.exp v
    rw [norm_mul, hμ_norm, one_mul]
    have h1_le_exp : 1 ≤ Real.exp v := Real.one_le_exp hv
    have hv_le_exp : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
    have hK0_nn : 0 ≤ K₀ := by
      dsimp only [K₀]; linarith [norm_nonneg (Complex.log (2 * (Real.pi : ℂ))), Real.pi_pos]
    calc ‖phiLambda ξ‖ ≤ K₀ + C₁ * v := hphi_le
      _ ≤ K₀ * Real.exp v + C₁ * Real.exp v :=
        add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hv_le_exp hC₁_nn)
      _ = (K₀ + C₁) * Real.exp v := by ring
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos v).le

/-! ### 7. Assembly of `HigherOrderBorelData` & Master Differential Transcendence Theorems -/

/-- **Critical-Line `HigherOrderBorelData` Witness on `phiLambda`**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`,
`phiLambda` satisfies `HigherOrderBorelData` along the rotated critical-line ray `θ₀ = π / 2`
with simple poles (`ord _ = 1`) at `i * criticalLineZeroSeq hInf m` of exact nonzero negative
integer residue `-zeroMultiplicity (criticalLineZeroSeq hInf m) ∈ ℤ_{<0}`, and flanking rays
`θ₀ ± π / 4` (`3π / 4` and `π / 4`). -/
def phiLambda_higherOrderBorelData
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros) :
    HigherOrderBorelData phiLambda (Real.pi / 2) (criticalLineZeroSeq hInf) (fun _ => 1)
      (fun m s => if s = 1 then -((zeroMultiplicity (criticalLineZeroSeq hInf m) : ℕ) : ℂ) else 0) where
  α₀ := 3 * Real.pi / 8
  θ := Real.pi / 4
  ε := Classical.choose exists_zero_free_ball_half
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := (Classical.choose_spec exists_zero_free_ball_half).1
  ω_pos := criticalLineZeroSeq_pos hInf 0
  ω_mono := criticalLineZeroSeq_strictMono hInf
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by
    simp only [↓reduceIte]
    exact (phiLambda_simple_pole_at_zero (criticalLineZeroSeq_zero hInf m)).2
  analyticOn :=
    phiLambda_analyticOn_rotatedPuncturedWedge_of_RH hRH hInf
      (Classical.choose_spec exists_zero_free_ball_half).2
  pole_principalPart := fun m => by
    obtain ⟨L, hL⟩ := phiLambda_simple_pole_principalPart (criticalLineZeroSeq_zero hInf m)
    refine ⟨L, ?_⟩
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one, exp_I_pi_div_two]
    exact hL
  expType_plus := by
    have hcos : Real.cos (Real.pi / 2 + Real.pi / 4) < 0 := by
      rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub,
        Real.sin_pi_div_four]
      linarith [Real.sqrt_pos.mpr zero_lt_two]
    have hsin : 0 < Real.sin (Real.pi / 2 + Real.pi / 4) := by
      rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two, one_mul, zero_mul, add_zero,
        Real.cos_pi_div_four]
      positivity
    exact phiLambda_expType_left_ray hRH hcos hsin
  expType_minus := by
    have hcos : 0 < Real.cos (Real.pi / 2 - Real.pi / 4) := by
      rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add,
        Real.sin_pi_div_four]
      positivity
    exact phiLambda_expType_right_ray hRH hcos

/-- **Master Theorem 1 (`ℂ[u]` Formal Differential Transcendence of `G_Lambda`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, the formal
Von Mangoldt critical-line Borel–Laplace series `G_Lambda` satisfies NO nonzero non-autonomous
polynomial differential equation over `ℂ[u]`. -/
theorem riemannHypothesis_implies_G_Lambda_no_poly_ade
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly G_Lambda P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_ade (phiLambda_higherOrderBorelData hRH hInf) P hP

/-- **Master Theorem 2 (`ℂ(u)` Formal Differential Transcendence of `G_Lambda`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, the formal
Von Mangoldt critical-line Borel–Laplace series `G_Lambda` satisfies NO nonzero rational-coefficient
algebraic differential equation over `ℂ(u)`. -/
theorem riemannHypothesis_implies_G_Lambda_dTrans
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat G_Lambda P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade (phiLambda_higherOrderBorelData hRH hInf) P hP

/-- **Master Theorem 3 (Autonomous Formal Differential Transcendence of `G_Lambda`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, `G_Lambda`
satisfies NO nonzero autonomous polynomial differential equation over `ℂ`. -/
theorem riemannHypothesis_implies_G_Lambda_no_autonomous_ade
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval G_Lambda P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_autonomous_ade (phiLambda_higherOrderBorelData hRH hInf) P hP

/-! #### Regularized Real-Axis Laplace Integral `G_Lambda_laplace` and All-Orders Asymptotics -/

private lemma minor_value_hasAsympExp (a : Minor) {U : Set ℂ} {d : ℂ}
    (hU : Domain U) (ray : ContainsRay U d) (ha : a.Good U d) (hd : 0 < d.re) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ))) (d_u^[j] a.toSeries) := by
  let ej : BorelExpr := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  obtain ⟨good_j, rep_j⟩ := ej.represents hU ray ha
  have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU ray ha hd j).1
  have hser_j : (ej.residual a).toSeries = d_u^[j] a.toSeries := by
    have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
    clear good_j rep_j hjet_eq
    induction j with
    | zero => rfl
    | succ k ih =>
      have hgk := ((Nat.iterate BorelExpr.jet k BorelExpr.leaf).represents hU ray ha).1.1 0 h0
      dsimp only [ej]
      rw [Function.iterate_succ_apply' BorelExpr.jet k BorelExpr.leaf,
        Function.iterate_succ_apply' d_u k a.toSeries]
      exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
  have ht_far : Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far d) := by
    rw [BorelStokesVandermonde.far, tendsto_comap_iff]
    have heq : ((fun p : ℂ => (p * d).re) ∘ fun u : ℝ => (u : ℂ)) = fun u : ℝ => u * d.re := by
      funext u; simp [Complex.mul_re]
    rw [heq]
    exact tendsto_id.atTop_mul_const hd
  intro M
  cases M with
  | zero =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU ray good_j hd 0
    refine ⟨C + ‖(ej.residual a).atom‖, ?_⟩
    filter_upwards [hC, hjet_eq, ht_far.eventually rep_j, eventually_ge_atTop (1 : ℝ)] with u hu hje hre hu1
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add, pow_one] at hu
    rw [← hje, hre]
    have h1 : ‖(ej.residual a).value d (u : ℂ)‖ ≤
        ‖(ej.residual a).value d (u : ℂ) - (ej.residual a).atom‖ + ‖(ej.residual a).atom‖ := by
      simpa [sub_add_cancel] using
        norm_add_le ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom) (ej.residual a).atom
    have hC0 : 0 ≤ C := by
      have hnn := norm_nonneg ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom)
      exact (div_nonneg_iff.mp (hnn.trans hu)).resolve_right (fun h => by linarith) |>.1
    have hCu : C / u ≤ C := by
      calc C / u ≤ C / 1 := div_le_div_of_nonneg_left hC0 zero_lt_one hu1
        _ = C := div_one C
    linarith
  | succ m =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU ray good_j hd m
    refine ⟨C, ?_⟩
    filter_upwards [hC, hjet_eq, ht_far.eventually rep_j] with u hu hje hre
    rw [← hje, hre]
    have hsum : ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (d_u^[j] a.toSeries) * ((u : ℂ)⁻¹ ^ k) =
        (ej.residual a).atom + ∑ k ∈ Finset.range m,
          iteratedDeriv k (ej.residual a).density 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
      rw [← hser_j, Finset.sum_range_succ']
      simp only [Minor.toSeries, PowerSeries.coeff_mk, pow_zero, mul_one, add_comm]
    rw [hsum]
    exact hu

/-- **All-Orders Asymptotic Expansion of `G_Lambda_laplace` (under RH)**:
For every derivative order `j : ℕ`, `iteratedDeriv j G_Lambda_laplace` shares the exact all-orders
`1 / u` asymptotic expansion `d_u^[j] G_Lambda` as `u → +∞`. -/
theorem G_Lambda_laplace_hasAsympExp (hRH : RiemannHypothesis) (j : ℕ) :
    HasAsympExp (iteratedDeriv j G_Lambda_laplace) (d_u^[j] G_Lambda) := by
  obtain ⟨ε, hε_pos, hball⟩ := exists_zero_free_ball_half
  let U : Set ℂ := Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re}
  have hU : Domain U := by
    refine ⟨Metric.isOpen_ball.union (isOpen_lt continuous_const Complex.continuous_re),
      fun z hz t ht => ?_⟩
    rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left
      simp [Metric.mem_ball, hε_pos]
    · rcases hz with hzb | hzr
      · left
        rw [Metric.mem_ball, dist_zero_right] at hzb ⊢
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hzb
      · right
        change 0 < ((t : ℂ) * z).re
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_pos ht_pos hzr
  have hray : ContainsRay U 1 := by
    intro v hv
    rw [one_mul]
    rcases eq_or_lt_of_le hv with rfl | hv_pos
    · left; simp [Metric.mem_ball, hε_pos]
    · right; simpa using hv_pos
  let a : Minor := Minor.mk 0 phiLambda
  have ha_good : a.Good U 1 := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases hz with hzb | hzr
      · rw [Metric.mem_ball, dist_zero_right] at hzb
        exact phiLambda_analyticAt_of_zeta1_ne_zero (hball z hzb)
      · exact (phiLambda_holomorphic_on_open_wedges_of_RH hRH).1 z hzr
    · have hexp0 := phiLambda_expType_right_ray hRH (σ := 0) (by simp)
      simpa using hexp0
  have hval : (fun u : ℝ => a.value 1 (u : ℂ)) = G_Lambda_laplace := by
    funext u
    simp [a, Minor.value, complexLaplace, damped, Minor.pull, G_Lambda_laplace]
  have hser : a.toSeries = G_Lambda := by
    ext n
    cases n <;> simp [a, Minor.toSeries, G_Lambda, formalSeries]
  rw [← hval, ← hser]
  exact minor_value_hasAsympExp a hU hray ha_good (by simp) j

/-- **Master Theorem 4 (`ℂ[u]` Analytic Differential Transcendence of `G_Lambda_laplace`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, the regularized
real-axis Laplace integral `G_Lambda_laplace` satisfies NO nonzero non-autonomous polynomial
differential equation over `ℂ[u]` eventually as `u → +∞`. -/
theorem riemannHypothesis_implies_G_Lambda_laplace_no_poly_ade
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalU P (u : ℂ)) = 0) : P = 0 :=
  no_nonautonomous_ade_of_higher_order_borel (phiLambda_higherOrderBorelData hRH hInf)
    (G_Lambda_laplace_hasAsympExp hRH) P hP

/-- **Master Theorem 5 (`ℂ(u)` Analytic Differential Transcendence of `G_Lambda_laplace`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, the regularized
real-axis Laplace integral `G_Lambda_laplace` satisfies NO nonzero rational-coefficient algebraic
differential equation over `ℂ(u)` eventually as `u → +∞`. -/
theorem riemannHypothesis_implies_G_Lambda_laplace_dTrans
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  no_rat_ade_of_higher_order_borel (phiLambda_higherOrderBorelData hRH hInf)
    (G_Lambda_laplace_hasAsympExp hRH) P hP

/-- **Master Theorem 6 (Autonomous Analytic Differential Transcendence of `G_Lambda_laplace`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, the regularized
real-axis Laplace integral `G_Lambda_laplace` satisfies NO nonzero autonomous polynomial
differential equation over `ℂ` eventually as `u → +∞`. -/
theorem riemannHypothesis_implies_G_Lambda_laplace_no_autonomous_ade
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u) P = 0) :
    P = 0 :=
  no_autonomous_ade_of_higher_order_borel (phiLambda_higherOrderBorelData hRH hInf)
    (G_Lambda_laplace_hasAsympExp hRH) P hP

end
end PakPrimes.RiemannHypothesisStokes
