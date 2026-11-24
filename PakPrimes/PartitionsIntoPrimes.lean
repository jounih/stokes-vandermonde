module

public import PakPrimes.MainTheorem
public import PakPrimes.GeneralTheorem2
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Differential Transcendence of Partitions into Primes & Distinct-Prime Partitions

Assuming ONLY `PNTAllOrders`, this module proves differential transcendence over `ℂ(q)` for:
1. `partLogDerivSeries(q) = ∑_{p prime} p q^p / (1 - q^p)` (`partLogDeriv_algebraicIndependent_of_pnt`),
2. **Partitions into primes** `P_prime(q) = ∏_{p prime} (1 - q^p)^{-1}` (OEIS A000607)
   (`partitionPrimes_algebraicIndependent_of_pnt`),
3. **Distinct-prime partitions** `Q_prime(q) = ∏_{p prime} (1 + q^p)` (OEIS A000586)
   (`distinctPrimes_algebraicIndependent_of_pnt`).

Both results are conditional ONLY on `PNTAllOrders` and use strictly the standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.PartitionsIntoPrimes

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.PrimeNome PakPrimes.Main
open scoped Topology Interval Nat.Prime

noncomputable section

/-! ### 1. Analytic Continuation & `MeromorphicBorelData` for `phiPart(ξ) = ζ(2 - ξ) Γ(2 - ξ)` -/

/-- Closed functional-equation form of `phiPart` valid for `ξ ∉ ℤ` and analytic on `{Re ξ > 1} \ {2, 3, 5, 7, ...}`. -/
@[expose] def phiPartClosed (ξ : ℂ) : ℂ :=
  (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - ξ) /
    Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2) * riemannZeta (ξ - 1)

/-- Clean Borel kernel agreeing with `phiPart` on `{Re ξ < 2}` and with `phiPartClosed` on `{1 < Re ξ}`.
In particular, all even integers `2m + 4` are regular (analytic) points of `phiPartClean`. -/
@[expose] def phiPartClean (ξ : ℂ) : ℂ :=
  if 3 / 2 < ξ.re then phiPartClosed ξ else phiPart ξ

/-- Nonzero simple-pole residues of `phiPartClean` at `ωPart m ∈ {1, 2, 3, 5, 7, ...}`. -/
@[expose] def resPart : ℕ → ℂ
  | 0 => -1
  | 1 => 1 / 2
  | k + 2 =>
    (-1 : ℂ) ^ (k + 1) * 2 * (2 * (Real.pi : ℂ)) ^ (-((2 * k + 2 : ℕ) : ℂ)) *
      riemannZeta ((2 * k + 2 : ℕ) : ℂ)

private lemma two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

private lemma phiPartClosed_eq_phiPart_of_re_band {ξ : ℂ} (h1 : 1 < ξ.re) (h2 : ξ.re < 2) :
    phiPartClosed ξ = phiPart ξ := by
  have hs_ne_neg : ∀ n : ℕ, ξ - 1 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs_ne_one : ξ - 1 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2) ≠ 0 := by
    intro h
    rw [Complex.sin_eq_zero_iff] at h
    rcases h with ⟨k, hk⟩
    have hk' : (Real.pi : ℂ) * (ξ - 1) = (Real.pi : ℂ) * (2 * (k : ℂ)) := by
      linear_combination 2 * hk
    have hξ : ξ - 1 = 2 * (k : ℂ) := mul_left_cancel₀ hpi_ne hk'
    have hre := congrArg Complex.re hξ
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero] at hre
    have hk_int : (0 : ℤ) < 2 * k ∧ 2 * k < 1 := by
      constructor
      · exact_mod_cast (by linarith : (0 : ℝ) < 2 * (k : ℝ))
      · exact_mod_cast (by linarith : 2 * (k : ℝ) < 1)
    omega
  have hcos_ne : Complex.cos ((Real.pi : ℂ) * (ξ - 1) / 2) ≠ 0 := by
    intro h
    rw [Complex.cos_eq_zero_iff] at h
    rcases h with ⟨k, hk⟩
    have hk' : (Real.pi : ℂ) * (ξ - 1) = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination 2 * hk
    have hξ : ξ - 1 = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi_ne hk'
    have hre := congrArg Complex.re hξ
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero] at hre
    have hk_int : (0 : ℤ) < 2 * k + 1 ∧ 2 * k + 1 < 1 := by
      constructor
      · exact_mod_cast (by linarith : (0 : ℝ) < 2 * (k : ℝ) + 1)
      · exact_mod_cast (by linarith : 2 * (k : ℝ) + 1 < 1)
    omega
  have hsin2 : Complex.sin ((Real.pi : ℂ) * (ξ - 1)) =
      2 * Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2) * Complex.cos ((Real.pi : ℂ) * (ξ - 1) / 2) := by
    simpa [mul_div_cancel₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)] using
      Complex.sin_two_mul ((Real.pi : ℂ) * (ξ - 1) / 2)
  have hsin2_ne : Complex.sin ((Real.pi : ℂ) * (ξ - 1)) ≠ 0 := by
    rw [hsin2]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hsin_ne) hcos_ne
  have hzeta := riemannZeta_one_sub hs_ne_neg hs_ne_one
  have h1sub : (1 : ℂ) - (ξ - 1) = 2 - ξ := by ring
  have hneg : -(ξ - 1) = 1 - ξ := by ring
  rw [h1sub, hneg] at hzeta
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (ξ - 1)
  rw [h1sub] at hrefl
  dsimp only [phiPart, phiPartClosed]
  rw [hzeta]
  calc (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - ξ) /
        Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2) * riemannZeta (ξ - 1)
      = 2 * (2 * (Real.pi : ℂ)) ^ (1 - ξ) *
          ((Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2) *
            Complex.cos ((Real.pi : ℂ) * (ξ - 1) / 2))) *
          Complex.cos ((Real.pi : ℂ) * (ξ - 1) / 2) * riemannZeta (ξ - 1) := by
        field_simp [hsin_ne, hcos_ne]
    _ = 2 * (2 * (Real.pi : ℂ)) ^ (1 - ξ) *
          (Complex.Gamma (ξ - 1) * Complex.Gamma (2 - ξ)) *
          Complex.cos ((Real.pi : ℂ) * (ξ - 1) / 2) * riemannZeta (ξ - 1) := by
        rw [← hsin2, ← hrefl]
    _ = (2 * (2 * (Real.pi : ℂ)) ^ (1 - ξ) * Complex.Gamma (ξ - 1) *
          Complex.cos ((Real.pi : ℂ) * (ξ - 1) / 2) * riemannZeta (ξ - 1)) *
          Complex.Gamma (2 - ξ) := by ring

lemma phiPartClean_eq_phiPart_of_re_lt_two {ξ : ℂ} (hξ : ξ.re < 2) :
    phiPartClean ξ = phiPart ξ := by
  dsimp only [phiPartClean]
  split_ifs with h
  · exact phiPartClosed_eq_phiPart_of_re_band (by linarith) hξ
  · rfl

lemma phiPartClean_eq_phiPartClosed_of_one_lt_re {ξ : ℂ} (hξ : 1 < ξ.re) :
    phiPartClean ξ = phiPartClosed ξ := by
  dsimp only [phiPartClean]
  split_ifs with h
  · rfl
  · exact (phiPartClosed_eq_phiPart_of_re_band hξ (by linarith)).symm

lemma formalSeries_phiPartClean_eq : formalSeries phiPartClean = formalSeries phiPart := by
  have heq : phiPartClean =ᶠ[𝓝 (0 : ℂ)] phiPart := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (by simp : (0 : ℂ).re < 2)] with z hz
    exact phiPartClean_eq_phiPart_of_re_lt_two hz
  ext n
  cases n with
  | zero => simp [formalSeries]
  | succ k =>
    simp only [formalSeries, PowerSeries.coeff_mk]
    exact heq.iteratedDeriv_eq k

theorem resPart_ne_zero (m : ℕ) : resPart m ≠ 0 := by
  rcases m with _ | _ | k
  · norm_num [resPart]
  · norm_num [resPart]
  · unfold resPart
    have hz : riemannZeta ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [Complex.natCast_re]
      exact_mod_cast (by omega : 1 ≤ 2 * k + 2)
    have hpow1 : (-1 : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpow2 : (2 * (Real.pi : ℂ)) ^ (-((2 * k + 2 : ℕ) : ℂ)) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero two_pi_ne_zero]
      exact Complex.exp_ne_zero _
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpow1 two_ne_zero) hpow2) hz

private lemma cpow_const_analyticAt (a : ℂ) (ha : a ≠ 0) (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (fun w => a ^ f w) z := by
  have heq : (fun w => a ^ f w) = fun w => Complex.exp (Complex.log a * f w) := by
    funext w; exact Complex.cpow_def_of_ne_zero ha (f w)
  rw [heq]
  exact (analyticAt_const.mul hf).cexp

private lemma phiPart_analyticAt_of_re_lt_two {z : ℂ} (hz_re : z.re < 2) (hz1 : z ≠ 1) :
    AnalyticAt ℂ phiPart z := by
  let U : Set ℂ := {w : ℂ | w.re < 2} ∩ {w : ℂ | w ≠ 1}
  have hU_open : IsOpen U :=
    (isOpen_lt Complex.continuous_re continuous_const).inter isOpen_ne
  have hdiff : DifferentiableOn ℂ phiPart U := by
    intro w ⟨hw_re, hw1⟩
    change w.re < 2 at hw_re
    change w ≠ 1 at hw1
    have hz_diff : DifferentiableAt ℂ (fun ζ => riemannZeta (2 - ζ)) w := by
      refine (differentiableAt_riemannZeta ?_).comp w ((differentiableAt_const 2).sub differentiableAt_id)
      intro h0; exact hw1 (by linear_combination -h0)
    have hg_diff : DifferentiableAt ℂ (fun ζ => Complex.Gamma (2 - ζ)) w := by
      refine (Complex.differentiableAt_Gamma _ ?_).comp w ((differentiableAt_const 2).sub differentiableAt_id)
      intro m hm
      have hre := congrArg Complex.re hm
      simp only [Complex.sub_re, Complex.re_ofNat, Complex.neg_re, Complex.natCast_re] at hre
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (hz_diff.mul hg_diff).differentiableWithinAt
  exact (hdiff.analyticOnNhd hU_open) z ⟨hz_re, hz1⟩

private lemma phiPartClosed_analyticAt_of_one_lt_re {z : ℂ} (hz_re : 1 < z.re)
    (hz2 : z ≠ 2) (hsin : Complex.sin ((Real.pi : ℂ) * (z - 1) / 2) ≠ 0) :
    AnalyticAt ℂ phiPartClosed z := by
  let U : Set ℂ := {w : ℂ | 1 < w.re} ∩ {w : ℂ | w ≠ 2} ∩
    {w : ℂ | Complex.sin ((Real.pi : ℂ) * (w - 1) / 2) ≠ 0}
  have hU_open : IsOpen U :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).inter
      (isOpen_ne.preimage (by fun_prop : Continuous fun w : ℂ => Complex.sin ((Real.pi : ℂ) * (w - 1) / 2)))
  have hdiff : DifferentiableOn ℂ phiPartClosed U := by
    intro w ⟨⟨_, hw2⟩, hw_sin⟩
    change w ≠ 2 at hw2
    change Complex.sin ((Real.pi : ℂ) * (w - 1) / 2) ≠ 0 at hw_sin
    have h1 : DifferentiableAt ℂ (fun ζ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - ζ)) w := by
      have hc : (fun ζ => (2 * (Real.pi : ℂ)) ^ (1 - ζ)) =
          fun ζ => Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * (1 - ζ)) := by
        funext ζ; exact Complex.cpow_def_of_ne_zero two_pi_ne_zero _
      have hce : (fun ζ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - ζ)) =
          fun ζ => (Real.pi : ℂ) * Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * (1 - ζ)) := by
        funext ζ; rw [congrFun hc ζ]
      rw [hce]
      exact (differentiableAt_const (Real.pi : ℂ)).mul
        (((differentiableAt_const _).mul ((differentiableAt_const 1).sub differentiableAt_id)).cexp)
    have h2 : DifferentiableAt ℂ (fun ζ => Complex.sin ((Real.pi : ℂ) * (ζ - 1) / 2)) w :=
      (((differentiableAt_const (Real.pi : ℂ)).mul (differentiableAt_id.sub_const 1)).div_const 2).csin
    have h3 : DifferentiableAt ℂ (fun ζ => riemannZeta (ζ - 1)) w := by
      refine (differentiableAt_riemannZeta ?_).comp w (differentiableAt_id.sub_const 1)
      intro h0; exact hw2 (by linear_combination h0)
    exact ((h1.div h2 hw_sin).mul h3).differentiableWithinAt
  exact (hdiff.analyticOnNhd hU_open) z ⟨⟨hz_re, hz2⟩, hsin⟩

lemma phiPartClean_analyticOn :
    AnalyticOnNhd ℂ phiPartClean (puncturedWedge (Real.pi / 3) (1 / 2) ωPart) := by
  intro z hz
  have h_avoid : ∀ m : ℕ, z ≠ (ωPart m : ℂ) := fun m heq => hz.2 ⟨m, heq.symm⟩
  by_cases hz_re : z.re < 2
  · have hnhds : phiPartClean =ᶠ[𝓝 z] phiPart := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz_re] with w hw
      exact phiPartClean_eq_phiPart_of_re_lt_two hw
    have hz1 : z ≠ 1 := by simpa [ωPart] using h_avoid 0
    exact (phiPart_analyticAt_of_re_lt_two hz_re hz1).congr hnhds.symm
  · have hz_ge2 : 2 ≤ z.re := le_of_not_gt hz_re
    have hz1 : 1 < z.re := by linarith
    have hnhds : phiPartClean =ᶠ[𝓝 z] phiPartClosed := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz1] with w hw
      exact phiPartClean_eq_phiPartClosed_of_one_lt_re hw
    have hz2 : z ≠ 2 := by simpa [ωPart] using h_avoid 1
    have hsin : Complex.sin ((Real.pi : ℂ) * (z - 1) / 2) ≠ 0 := by
      intro h
      rw [Complex.sin_eq_zero_iff] at h
      rcases h with ⟨k, hk⟩
      have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hk' : (Real.pi : ℂ) * (z - 1) = (Real.pi : ℂ) * (2 * (k : ℂ)) := by
        linear_combination 2 * hk
      have hz_eq : z = 2 * (k : ℂ) + 1 := by
        have := mul_left_cancel₀ hpi_ne hk'
        linear_combination this
      have hre := congrArg Complex.re hz_eq
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero, Complex.one_re] at hre
      have hk_bd : (2 : ℝ) ≤ 2 * (k : ℝ) + 1 := by linarith
      have hk_int : (2 : ℤ) ≤ 2 * k + 1 := by exact_mod_cast hk_bd
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
      apply h_avoid (m + 2)
      rw [hz_eq]
      dsimp only [ωPart]
      push_cast
      ring
    exact (phiPartClosed_analyticAt_of_one_lt_re hz1 hz2 hsin).congr hnhds.symm

lemma phiPartClean_simple_pole (m : ℕ) :
    Tendsto (fun z : ℂ => (z - (ωPart m : ℂ)) * phiPartClean z)
      (𝓝[≠] (ωPart m : ℂ)) (𝓝 (resPart m)) := by
  rcases m with _ | _ | k
  · -- m = 0: ωPart 0 = 1, resPart 0 = -1
    have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ),
        (z - 1) * phiPartClean z =
          -((((2 : ℂ) - z) - 1) * riemannZeta ((2 : ℂ) - z)) * Complex.Gamma ((2 : ℂ) - z) := by
      have hopen : {w : ℂ | w.re < 2} ∈ 𝓝 (1 : ℂ) :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hopen] with z hz
      rw [phiPartClean_eq_phiPart_of_re_lt_two hz, phiPart]
      ring
    have hmap : Tendsto (fun z : ℂ => (2 : ℂ) - z) (𝓝[≠] (1 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hcont : ContinuousAt (fun z : ℂ => (2 : ℂ) - z) 1 :=
          continuousAt_const.sub continuousAt_id
        simpa [show (2 : ℂ) - 1 = 1 by ring] using hcont.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        intro h0
        rw [Set.mem_singleton_iff] at h0
        apply hz
        rw [Set.mem_singleton_iff]
        linear_combination -h0
    have hzeta := riemannZeta_residue_one.comp hmap
    have hgam : Tendsto (fun z : ℂ => Complex.Gamma ((2 : ℂ) - z)) (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
      have hd : DifferentiableAt ℂ Complex.Gamma ((2 : ℂ) - 1) := by
        refine Complex.differentiableAt_Gamma _ fun n hn => ?_
        have hre := congrArg Complex.re hn
        simp only [Complex.sub_re, Complex.re_ofNat, Complex.one_re, Complex.neg_re,
          Complex.natCast_re] at hre
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hc : ContinuousAt (fun z : ℂ => Complex.Gamma ((2 : ℂ) - z)) 1 :=
        hd.continuousAt.comp (continuousAt_const.sub continuousAt_id)
      simpa [show (2 : ℂ) - 1 = 1 by ring, Complex.Gamma_one] using
        hc.tendsto.mono_left nhdsWithin_le_nhds
    have htot : Tendsto (fun z : ℂ => -((((2 : ℂ) - z) - 1) * riemannZeta ((2 : ℂ) - z)) *
        Complex.Gamma ((2 : ℂ) - z)) (𝓝[≠] (1 : ℂ)) (𝓝 (-1)) := by
      simpa [neg_mul, one_mul] using (hzeta.neg.mul hgam)
    simpa [ωPart, resPart] using htot.congr' (hev.mono fun _ h => h.symm)
  · -- m = 1: ωPart 1 = 2, resPart 1 = 1/2
    have hev : ∀ᶠ z in 𝓝[≠] (2 : ℂ),
        (z - 2) * phiPartClean z =
          ((Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z) /
            Complex.sin ((Real.pi : ℂ) * (z - 1) / 2)) *
            (((z - 1) - 1) * riemannZeta (z - 1)) := by
      have hopen : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hopen] with z hz
      rw [phiPartClean_eq_phiPartClosed_of_one_lt_re hz, phiPartClosed]
      ring
    have hmap : Tendsto (fun z : ℂ => z - (1 : ℂ)) (𝓝[≠] (2 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hcont : ContinuousAt (fun z : ℂ => z - (1 : ℂ)) 2 :=
          continuousAt_id.sub continuousAt_const
        simpa [show (2 : ℂ) - 1 = 1 by ring] using
          hcont.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        intro h0
        rw [Set.mem_singleton_iff] at h0
        apply hz
        rw [Set.mem_singleton_iff]
        linear_combination h0
    have hzeta := riemannZeta_residue_one.comp hmap
    have hpre_cont : ContinuousAt
        (fun z : ℂ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z) /
          Complex.sin ((Real.pi : ℂ) * (z - 1) / 2)) 2 := by
      have h1 : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z)) 2 := by
        have hc := (cpow_const_analyticAt (2 * (Real.pi : ℂ)) two_pi_ne_zero
          (fun z => 1 - z) 2 (analyticAt_const.sub analyticAt_id)).continuousAt
        exact continuousAt_const.mul hc
      have h2 : ContinuousAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * (z - 1) / 2)) 2 :=
        (by fun_prop : Continuous fun z : ℂ => Complex.sin ((Real.pi : ℂ) * (z - 1) / 2)).continuousAt
      have hsin2 : Complex.sin ((Real.pi : ℂ) * ((2 : ℂ) - 1) / 2) ≠ 0 := by
        have heq : (Real.pi : ℂ) * ((2 : ℂ) - 1) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
          push_cast; ring
        rw [heq, ← Complex.ofReal_sin, Real.sin_pi_div_two]
        norm_num
      exact h1.div h2 hsin2
    have hpre_val : (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - (2 : ℂ)) /
        Complex.sin ((Real.pi : ℂ) * ((2 : ℂ) - 1) / 2) = 1 / 2 := by
      have heq : (Real.pi : ℂ) * ((2 : ℂ) - 1) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [heq, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one, div_one,
        show (1 - (2 : ℂ)) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp [hpi]
    have hpre : Tendsto (fun z : ℂ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z) /
        Complex.sin ((Real.pi : ℂ) * (z - 1) / 2)) (𝓝[≠] (2 : ℂ)) (𝓝 (1 / 2)) := by
      simpa [hpre_val] using hpre_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := ({2}ᶜ : Set ℂ)))
    have htot := hpre.mul hzeta
    rw [mul_one] at htot
    simpa [ωPart, resPart] using htot.congr' (hev.mono fun _ h => h.symm)
  · -- m = k + 2: ωPart (k + 2) = 2 * k + 3
    let z₀ : ℂ := ((2 * k + 3 : ℕ) : ℂ)
    let S : ℂ → ℂ := fun z => Complex.sin ((Real.pi : ℂ) * (z - 1) / 2)
    have hS0 : S z₀ = 0 := by
      dsimp only [S, z₀]
      have heq : (Real.pi : ℂ) * (((2 * k + 3 : ℕ) : ℂ) - 1) / 2 =
          ((k + 1 : ℕ) : ℂ) * (Real.pi : ℂ) := by
        push_cast; ring
      rw [heq, Complex.sin_nat_mul_pi]
    have hcos_val : Complex.cos ((Real.pi : ℂ) * (z₀ - 1) / 2) = (-1 : ℂ) ^ (k + 1) := by
      dsimp only [z₀]
      have heq : (Real.pi : ℂ) * (((2 * k + 3 : ℕ) : ℂ) - 1) / 2 =
          (((k + 1 : ℕ) * Real.pi : ℝ) : ℂ) := by
        push_cast; ring
      rw [heq, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
      push_cast; ring
    have hS_deriv : HasDerivAt S ((Real.pi : ℂ) / 2 * (-1 : ℂ) ^ (k + 1)) z₀ := by
      have harg : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * (z - 1) / 2) ((Real.pi : ℂ) / 2) z₀ := by
        have h1 := ((hasDerivAt_id z₀).sub_const 1).const_mul (Real.pi : ℂ)
        simpa [div_eq_mul_inv] using h1.div_const (2 : ℂ)
      have hcomp := (Complex.hasDerivAt_sin _).comp z₀ harg
      refine hcomp.congr_deriv ?_
      rw [hcos_val]; ring
    have hderiv_ne : (Real.pi : ℂ) / 2 * (-1 : ℂ) ^ (k + 1) ≠ 0 :=
      mul_ne_zero (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero)
        (pow_ne_zero _ (by norm_num))
    have hslope := hasDerivAt_iff_tendsto_slope.mp hS_deriv
    have hinv_slope : Tendsto (fun z : ℂ => (z - z₀) / S z) (𝓝[≠] z₀)
        (𝓝 ((-1 : ℂ) ^ (k + 1) * (2 / (Real.pi : ℂ)))) := by
      have hinv := hslope.inv₀ hderiv_ne
      have heq_slope : ∀ᶠ z in 𝓝[≠] z₀, (slope S z₀ z)⁻¹ = (z - z₀) / S z := by
        filter_upwards [self_mem_nhdsWithin] with z _
        rw [slope_def_field, hS0, sub_zero, inv_div]
      have hval_inv : ((Real.pi : ℂ) / 2 * (-1 : ℂ) ^ (k + 1))⁻¹ =
          (-1 : ℂ) ^ (k + 1) * (2 / (Real.pi : ℂ)) := by
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hpow2 : ((-1 : ℂ) ^ (k + 1)) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        field_simp [hpi]
        rw [hpow2]
      rw [hval_inv] at hinv
      exact hinv.congr' heq_slope
    have hrest_cont : ContinuousAt
        (fun z : ℂ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z) * riemannZeta (z - 1)) z₀ := by
      have h1 : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z)) z₀ :=
        continuousAt_const.mul
          (cpow_const_analyticAt (2 * (Real.pi : ℂ)) two_pi_ne_zero (fun z => 1 - z) z₀
            (analyticAt_const.sub analyticAt_id)).continuousAt
      have h2 : ContinuousAt (fun z : ℂ => riemannZeta (z - 1)) z₀ := by
        refine (differentiableAt_riemannZeta ?_).continuousAt.comp (continuousAt_id.sub continuousAt_const)
        intro h0
        have hre := congrArg Complex.re h0
        dsimp only [z₀] at hre
        simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re] at hre
        push_cast at hre
        have : (2 * k + 3 : ℕ) = 2 := by exact_mod_cast (by linarith : ((2 * k + 3 : ℕ) : ℝ) = 2)
        omega
      exact h1.mul h2
    have hrest : Tendsto (fun z : ℂ => (Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z) *
        riemannZeta (z - 1)) (𝓝[≠] z₀)
        (𝓝 ((Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z₀) * riemannZeta (z₀ - 1))) :=
      hrest_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := ({z₀}ᶜ : Set ℂ)))
    have hev : ∀ᶠ z in 𝓝[≠] z₀,
        (z - z₀) * phiPartClean z =
          ((Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z) * riemannZeta (z - 1)) * ((z - z₀) / S z) := by
      have hopen : {w : ℂ | 1 < w.re} ∈ 𝓝 z₀ :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
          dsimp [z₀]; exact_mod_cast (by omega : 1 < 2 * k + 3))
      filter_upwards [nhdsWithin_le_nhds hopen] with z hz
      rw [phiPartClean_eq_phiPartClosed_of_one_lt_re hz, phiPartClosed]
      dsimp only [S]
      ring
    have htot := hrest.mul hinv_slope
    have hval_tot : ((Real.pi : ℂ) * (2 * (Real.pi : ℂ)) ^ (1 - z₀) * riemannZeta (z₀ - 1)) *
        ((-1 : ℂ) ^ (k + 1) * (2 / (Real.pi : ℂ))) = resPart (k + 2) := by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hz0_1 : z₀ - 1 = ((2 * k + 2 : ℕ) : ℂ) := by
        dsimp only [z₀]; push_cast; ring
      have h1z0 : 1 - z₀ = -((2 * k + 2 : ℕ) : ℂ) := by
        dsimp only [z₀]; push_cast; ring
      rw [hz0_1, h1z0]
      dsimp only [resPart]
      field_simp [hpi]
    rw [hval_tot] at htot
    simpa [ωPart, z₀] using htot.congr' (hev.mono fun _ h => h.symm)

lemma phiPartClean_ray_decay {d : ℂ} (hd_re : d.re = Real.sqrt 2 / 2)
    (hd_im : |d.im| = Real.sqrt 2 / 2) (hd_norm : ‖d‖ = 1) :
    ExpType (Minor.pull d phiPartClean) := by
  have havoid : ∀ v : ℝ, 0 ≤ v → d * (v : ℂ) ∈ puncturedWedge (Real.pi / 3) (1 / 2) ωPart := by
    intro v hv
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hv with rfl | hv_pos
      · left; simp [Metric.mem_ball]
      · right
        have hre : 0 < (d * (v : ℂ)).re := by
          simp [Complex.mul_re, hd_re]; positivity
        have htan : Real.sqrt 2 / 2 < Real.tan (Real.pi / 3) * (Real.sqrt 2 / 2) := by
          rw [Real.tan_pi_div_three]
          have h1 : (1 : ℝ) < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
          have hs : 0 < Real.sqrt 2 / 2 := by positivity
          nlinarith
        refine ⟨hre, ?_⟩
        have him' : (d * (v : ℂ)).im = d.im * v := by simp [Complex.mul_im]
        have hre' : (d * (v : ℂ)).re = d.re * v := by simp [Complex.mul_re]
        rw [him', hre', abs_mul, hd_im, abs_of_pos hv_pos, hd_re]
        nlinarith
    · rintro ⟨m, hm⟩
      have him := congrArg Complex.im hm
      simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero] at him
      have him' : d.im * v = 0 := by linarith
      have hdim_ne : d.im ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hd_im; exact absurd hd_im.symm (by positivity)
      have hv0 : v = 0 := (mul_eq_zero.mp him').resolve_left hdim_ne
      subst hv0
      have hre := congrArg Complex.re hm
      simp only [Complex.ofReal_zero, mul_zero, Complex.zero_re, Complex.ofReal_re] at hre
      linarith [ωPart_ge_one m]
  have hcont : ContinuousOn (fun v : ℝ => ‖Minor.pull d phiPartClean v‖) (Icc 0 5) := by
    refine ContinuousOn.norm (continuousOn_const.mul fun v hv => ?_)
    have hmul : Continuous (fun x : ℝ => d * (x : ℂ)) := continuous_const.mul Complex.continuous_ofReal
    exact ((phiPartClean_analyticOn _ (havoid v hv.1)).continuousAt.comp
      (f := fun x : ℝ => d * (x : ℂ)) hmul.continuousAt).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let Z₂ : ℝ := ∑' n : ℕ, ((n + 1 : ℝ) ^ 2)⁻¹
  have hZ₂_summ : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ 2)⁻¹) := by
    have h1 := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_right_cancel h)
    refine h1.congr fun n => ?_
    simp
  have hZ₂_nonneg : 0 ≤ Z₂ := tsum_nonneg fun _ => by positivity
  let C : ℝ := max C₀ (Real.pi * 2 * Z₂)
  refine ⟨C, 0, by positivity, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hv5 : v ≤ 5
  · have hb := hC₀ v ⟨hv, hv5⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    exact hb.trans (le_max_left _ _)
  · have hv_gt : 5 < v := lt_of_not_ge hv5
    let ξ : ℂ := d * (v : ℂ)
    have hξ_re_gt : 3 < ξ.re := by
      have hre : ξ.re = (Real.sqrt 2 / 2) * v := by simp [ξ, Complex.mul_re, hd_re]
      rw [hre]
      have hrt2 : (9 : ℝ) < (5 * Real.sqrt 2 / 2) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt zero_le_two]
        norm_num
      have h3 : 3 < 5 * Real.sqrt 2 / 2 := by nlinarith [Real.sqrt_nonneg 2]
      nlinarith
    have hξ_re1 : 1 < ξ.re := by linarith
    have hpull : ‖Minor.pull d phiPartClean v‖ = ‖phiPartClosed ξ‖ := by
      rw [Minor.pull, norm_mul, hd_norm, one_mul]
      exact congrArg norm (phiPartClean_eq_phiPartClosed_of_one_lt_re hξ_re1)
    rw [hpull, phiPartClosed, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hcpow_le : ‖(2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ ≤ 1 := by
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos h2pi]
      exact Real.rpow_le_one_of_one_le_of_nonpos h2pi_ge1 (by simp; linarith)
    have hzeta_le : ‖riemannZeta (ξ - 1)‖ ≤ Z₂ := by
      have hs_re : 1 < (ξ - 1).re := by simp; linarith
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs_re]
      have hterm_le : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ (ξ - 1)‖ ≤ ((n + 1 : ℝ) ^ 2)⁻¹ := fun n => by
        rw [norm_div, norm_one, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < n + 1)]
        simp only [one_div, Complex.sub_re, Complex.one_re]
        rw [← Real.rpow_neg (by positivity), show ((n + 1 : ℝ) ^ 2)⁻¹ = (n + 1 : ℝ) ^ (-2 : ℝ) by
          rw [Real.rpow_neg (by positivity)]; norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [show (0 : ℝ) ≤ n by positivity]) (by linarith)
      have hnorm_summ : Summable (fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ (ξ - 1)‖) :=
        hZ₂_summ.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le
      exact (norm_tsum_le_tsum_norm hnorm_summ).trans (hnorm_summ.tsum_le_tsum hterm_le hZ₂_summ)
    have hsin_ge : (1 / 2 : ℝ) ≤ ‖Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2)‖ := by
      let w : ℂ := (Real.pi : ℂ) * (ξ - 1) / 2
      have hw_im : 1 ≤ |w.im| := by
        have him : w.im = (Real.pi / 2) * (d.im * v) := by
          simp [w, ξ, Complex.mul_im]; ring
        rw [him, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2), hd_im,
          abs_of_pos (by linarith)]
        have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
        have hpi : 2 ≤ Real.pi := Real.two_le_pi
        calc (1 : ℝ) ≤ (2 / 2) * (1 / 2 * 5) := by norm_num
          _ ≤ (Real.pi / 2) * (Real.sqrt 2 / 2 * v) := by gcongr
      have hsin_sq : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sin_eq,
          ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.I_re, Complex.I_im, mul_one, zero_sub,
          Complex.add_im, Complex.mul_im, add_zero]
        have hcosh : Real.cosh w.im ^ 2 = 1 + Real.sinh w.im ^ 2 := by
          linarith [Real.cosh_sq_sub_sinh_sq w.im]
        have htrig : Real.sin w.re ^ 2 + Real.cos w.re ^ 2 = 1 := Real.sin_sq_add_cos_sq w.re
        nlinarith
      have hsinh_ge : (1 / 2 : ℝ) ≤ |Real.sinh w.im| := by
        rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hexp_diff : 1 ≤ |Real.exp w.im - Real.exp (-w.im)| := by
          rcases le_or_gt 0 w.im with hw0 | hw0
          · rw [abs_of_nonneg hw0] at hw_im
            have h_e1 : 2 ≤ Real.exp w.im :=
              (by linarith [Real.add_one_lt_exp (one_ne_zero)] : (2 : ℝ) ≤ Real.exp 1).trans
                (Real.exp_le_exp.mpr hw_im)
            have h_e2 : Real.exp (-w.im) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            exact (by linarith : (1 : ℝ) ≤ Real.exp w.im - Real.exp (-w.im)).trans (le_abs_self _)
          · rw [abs_of_neg hw0] at hw_im
            have h_e1 : 2 ≤ Real.exp (-w.im) :=
              (by linarith [Real.add_one_lt_exp (one_ne_zero)] : (2 : ℝ) ≤ Real.exp 1).trans
                (Real.exp_le_exp.mpr hw_im)
            have h_e2 : Real.exp w.im ≤ 1 := Real.exp_le_one_iff.mpr hw0.le
            have hneg : 1 ≤ -(Real.exp w.im - Real.exp (-w.im)) := by linarith
            exact hneg.trans (neg_le_abs _)
        linarith
      have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
        have hs1 : (1 / 2 : ℝ) ^ 2 ≤ Real.sinh w.im ^ 2 := by
          rw [← sq_abs (Real.sinh w.im)]
          nlinarith
        nlinarith [sq_nonneg (Real.sin w.re)]
      nlinarith [norm_nonneg (Complex.sin w)]
    have hinv_sin : (‖Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2)‖)⁻¹ ≤ 2 := by
      have hpos : (0 : ℝ) < 1 / 2 := by norm_num
      simpa using inv_anti₀ hpos hsin_ge
    calc Real.pi * ‖(2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ /
          ‖Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2)‖ * ‖riemannZeta (ξ - 1)‖
        ≤ (Real.pi * 1 * 2) * Z₂ := by
          rw [div_eq_mul_inv]
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hcpow_le Real.pi_pos.le)
            hinv_sin (by positivity) (by positivity)) hzeta_le (norm_nonneg _) (by positivity)
      _ = Real.pi * 2 * Z₂ := by ring
      _ ≤ C := le_max_right _ _

/-- Genuine `MeromorphicBorelData` witness for `phiPartClean` (`ζ(2 - ξ) Γ(2 - ξ)` analytically
continued across even integers `2m + 4`), with simple poles `ωPart = {1, 2, 3, 5, 7, ...}`
and nonzero residues `resPart`. -/
@[expose] def phiPart_borelData : MeromorphicBorelData phiPartClean ωPart resPart where
  θ₀ := Real.pi / 3
  θ := theta4
  ε := 1 / 2
  hθ_pos := theta4_pos
  hθ_lt := by unfold theta4; linarith [Real.pi_pos]
  hθ₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by simp [ωPart]
  ω_mono := ωPart_strictMono
  res_ne_zero := resPart_ne_zero
  analyticOn := phiPartClean_analyticOn
  simple_pole := phiPartClean_simple_pole
  expType_plus := by
    have heq : Complex.exp (I * (theta4 : ℂ)) = dPlus := rfl
    rw [heq]
    exact phiPartClean_ray_decay dPlus_re (by rw [dPlus_im, abs_of_pos (by positivity)]) norm_dPlus
  expType_minus := by
    have heq : Complex.exp (-I * (theta4 : ℂ)) = dMinus := rfl
    rw [heq]
    exact phiPartClean_ray_decay dMinus_re
      (by rw [dMinus_im, abs_neg, abs_of_pos (by positivity)]) norm_dMinus

/-! ### 2. `PNTAllOrders` $\implies$ All-Orders Asymptotics for `fPart(u) = e^{-2u} G_P(e^{-e^{-u}})` -/

private def primeReal (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

private lemma integrableOn_pow_mul_exp_neg_Ioi (k : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-t * x)) (Ioi 0) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have hlim : Tendsto (fun y : ℝ => y ^ k * Real.exp (-y)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  obtain ⟨Y₀, hY₀⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists_forall_of_atTop
  have hcont' : ContinuousOn (fun y : ℝ => y ^ k * Real.exp (-y)) (Icc 0 (max 1 Y₀)) := by fun_prop
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont'
  let B : ℝ := max 1 B₀
  have hbd_y : ∀ y : ℝ, 0 ≤ y → y ^ k * Real.exp (-y) ≤ B := by
    intro y hy
    by_cases hyM : y ≤ max 1 Y₀
    · have hb := hB₀ y ⟨hy, hyM⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hy k) (Real.exp_pos _).le)] at hb
      exact hb.trans (le_max_right _ _)
    · have hY : Y₀ ≤ y := le_trans (le_max_right 1 Y₀) (le_of_not_ge hyM)
      exact (hY₀ y hY).le.trans (le_max_left _ _)
  let C : ℝ := B * (2 / t) ^ k
  refine ((integrableOn_exp_mul_Ioi (show -(t / 2) < 0 by linarith) 0).const_mul C).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun x : ℝ => x ^ k * Real.exp (-t * x))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    change 0 < x at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.le k) (Real.exp_pos _).le)]
    have h1 := hbd_y ((t / 2) * x) (mul_nonneg ht2.le hx.le)
    have hpow : x ^ k = (2 / t) ^ k * ((t / 2) * x) ^ k := by
      rw [← mul_pow]; congr 1; field_simp [ht.ne']
    have hexp : Real.exp (-t * x) = Real.exp (-((t / 2) * x)) * Real.exp (-(t / 2) * x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hpow, hexp]
    calc (2 / t) ^ k * ((t / 2) * x) ^ k * (Real.exp (-((t / 2) * x)) * Real.exp (-(t / 2) * x))
        = ((t / 2) * x) ^ k * Real.exp (-((t / 2) * x)) * (2 / t) ^ k * Real.exp (-(t / 2) * x) := by
          ring
      _ ≤ B * (2 / t) ^ k * Real.exp (-(t / 2) * x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) (Real.exp_pos _).le
      _ = C * Real.exp (-(t / 2) * x) := by ring

private lemma integral_pow_mul_exp_neg_Ioi (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-r * x) = (k.factorial : ℝ) / r ^ (k + 1) := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k + 1 : ℝ)) (r := r) (by positivity) hr
  have hfn : (fun t : ℝ => t ^ ((k + 1 : ℝ) - 1) * Real.exp (-(r * t))) =
      fun t : ℝ => t ^ k * Real.exp (-r * t) := by
    funext t
    rw [show (k + 1 : ℝ) - 1 = (k : ℝ) by ring, Real.rpow_natCast, neg_mul]
  rw [hfn] at hg
  rw [hg, show (k + 1 : ℝ) = (k : ℝ) + 1 from rfl, Real.Gamma_nat_eq_factorial,
    show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, one_div, inv_pow]
  ring

private lemma primeReal_linearGrowth : LinearGrowthOnIoi2 primeReal := by
  refine ⟨?_, 2, by norm_num, fun x hx => ?_⟩
  · exact ((measurable_of_countable (fun n : ℕ => (Nat.primeCounting n : ℝ))).comp
      Nat.measurable_floor).aestronglyMeasurable
  · rw [primeReal, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 : Nat.primeCounting ⌊x⌋₊ ≤ ⌊x⌋₊ + 1 := by
      rw [Nat.primeCounting_eq_primeCounting'_succ]
      exact Nat.count_le Nat.Prime
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ x + 1 := by linarith [Nat.floor_le (by linarith [hx] : 0 ≤ x)]
    calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast h1
      _ ≤ x + 1 := h2
      _ ≤ 2 * x := by linarith

private lemma momentInt_integrableOn {B : ℝ → ℝ} (hB : LinearGrowthOnIoi2 B)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => B x * x ^ k * Real.exp (-t * x)) (Ioi 2) := by
  obtain ⟨mB, K₀, _, bB⟩ := hB
  have hmeas : AEStronglyMeasurable (fun x : ℝ => B x * x ^ k * Real.exp (-t * x))
      (volume.restrict (Ioi 2)) :=
    (mB.mul (by fun_prop : Measurable (fun x : ℝ => x ^ k)).aestronglyMeasurable).mul
      (by fun_prop : Measurable (fun x : ℝ => Real.exp (-t * x))).aestronglyMeasurable
  have hdom : IntegrableOn (fun x : ℝ => K₀ * (x ^ (k + 1) * Real.exp (-t * x))) (Ioi 2) :=
    ((integrableOn_pow_mul_exp_neg_Ioi (k + 1) ht).mono_set (Ioi_subset_Ioi (by norm_num))).const_mul K₀
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  change 2 < x at hx
  have hx0 : 0 ≤ x := by linarith [hx]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (pow_nonneg hx0 k)]
  calc |B x| * x ^ k * Real.exp (-t * x)
      ≤ (K₀ * x) * x ^ k * Real.exp (-t * x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (bB x hx) (pow_nonneg hx0 k))
          (Real.exp_pos _).le
    _ = K₀ * (x ^ (k + 1) * Real.exp (-t * x)) := by rw [pow_succ']; ring

private lemma momentInt_hasDerivAt {B : ℝ → ℝ} (hB : LinearGrowthOnIoi2 B) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (momentInt B k) (-momentInt B (k + 1) t) t := by
  obtain ⟨mB, K₀, hK₀, bB⟩ := hB
  let F : ℝ → ℝ → ℝ := fun s x => B x * x ^ k * Real.exp (-s * x)
  let F' : ℝ → ℝ → ℝ := fun s x => -(B x * x ^ (k + 1) * Real.exp (-s * x))
  let bound : ℝ → ℝ := fun x => K₀ * (x ^ (k + 2) * Real.exp (-(t / 2) * x))
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (volume.restrict (Ioi 2)) :=
    .of_forall fun s =>
      (mB.mul (by fun_prop : Measurable (fun x : ℝ => x ^ k)).aestronglyMeasurable).mul
        (by fun_prop : Measurable (fun x : ℝ => Real.exp (-s * x))).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' t) (volume.restrict (Ioi 2)) :=
    ((mB.mul (by fun_prop : Measurable (fun x : ℝ => x ^ (k + 1))).aestronglyMeasurable).mul
      (by fun_prop : Measurable (fun x : ℝ => Real.exp (-t * x))).aestronglyMeasurable).neg
  have hbound_int : IntegrableOn bound (Ioi 2) :=
    ((integrableOn_pow_mul_exp_neg_Ioi (k + 2) (half_pos ht)).mono_set
      (Ioi_subset_Ioi (by norm_num))).const_mul K₀
  have hbound : ∀ᵐ x ∂volume.restrict (Ioi (2 : ℝ)), ∀ s ∈ Metric.ball t (t / 2), ‖F' s x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    change 2 < x at hx
    have hx0 : 0 ≤ x := by linarith [hx]
    intro s hs
    have hs2 : t / 2 < s := by rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs; linarith
    rw [Real.norm_eq_abs]
    simp only [F', abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (pow_nonneg hx0 (k + 1))]
    have hexp : Real.exp (-s * x) ≤ Real.exp (-(t / 2) * x) := Real.exp_le_exp.mpr (by nlinarith)
    calc |B x| * x ^ (k + 1) * Real.exp (-s * x)
        ≤ (K₀ * x) * x ^ (k + 1) * Real.exp (-(t / 2) * x) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (bB x hx) (pow_nonneg hx0 (k + 1)))
            hexp (Real.exp_pos _).le (by positivity)
      _ = bound x := by dsimp [bound]; rw [pow_succ' x (k + 1)]; ring
  have hderiv : ∀ᵐ x ∂volume.restrict (Ioi (2 : ℝ)), ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun r => F r x) (F' s x) s := by
    refine .of_forall fun x s _ => ?_
    have h1 : HasDerivAt (fun r => Real.exp (-r * x)) (-x * Real.exp (-s * x)) s := by
      have hr : HasDerivAt (fun r => -r * x) (-x) s := by
        simpa using ((hasDerivAt_id s).neg.mul_const x)
      convert hr.exp using 1; ring
    convert h1.const_mul (B x * x ^ k) using 1
    dsimp [F, F']; rw [pow_succ]; ring
  have res := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t (half_pos ht))
    hmeas (momentInt_integrableOn ⟨mB, K₀, hK₀, bB⟩ k ht) hmeas' hbound hbound_int hderiv).2
  convert res using 1
  · funext s; simp only [momentInt, F, neg_mul]
  · simp only [momentInt, F', integral_neg, neg_mul]

private def towerCoeff2 : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, k => -((k + 2 : ℕ) : ℝ) * towerCoeff2 j k +
      if k = 0 then 0 else towerCoeff2 j (k - 1)

private lemma towerCoeff2_eq_zero_of_lt {j k : ℕ} (h : j < k) : towerCoeff2 j k = 0 := by
  induction j generalizing k with
  | zero =>
    have hk : k ≠ 0 := by omega
    simp [towerCoeff2, hk]
  | succ j ih =>
    have hk0 : k ≠ 0 := by omega
    rw [towerCoeff2]
    simp [hk0, ih (k := k) (by omega), ih (k := k - 1) (by omega)]

private lemma scaledMoment_hasDerivAt {B : ℝ → ℝ} (hB : LinearGrowthOnIoi2 B) (k : ℕ) (u : ℝ) :
    HasDerivAt (scaledMoment B k)
      (-((k + 2 : ℕ) : ℝ) * scaledMoment B k u + scaledMoment B (k + 1) u) u := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-((k + 2 : ℕ) : ℝ) * x))
      (-((k + 2 : ℕ) : ℝ) * Real.exp (-((k + 2 : ℕ) : ℝ) * u)) u := by
    simpa [mul_comm] using ((hasDerivAt_id u).const_mul (-((k + 2 : ℕ) : ℝ))).exp
  have ht : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u := by
    simpa [mul_comm] using (hasDerivAt_id u).neg.exp
  have hm := (momentInt_hasDerivAt hB k (Real.exp_pos (-u))).comp u ht
  refine (he.mul hm).congr_deriv ?_
  have hpow : Real.exp (-((k + 2 : ℕ) : ℝ) * u) * Real.exp (-u) =
      Real.exp (-((k + 1 + 2 : ℕ) : ℝ) * u) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  unfold scaledMoment scaledOn
  calc -((k + 2 : ℕ) : ℝ) * Real.exp (-((k + 2 : ℕ) : ℝ) * u) * momentInt B k (Real.exp (-u)) +
        Real.exp (-((k + 2 : ℕ) : ℝ) * u) * (-momentInt B (k + 1) (Real.exp (-u)) * -Real.exp (-u))
      = -((k + 2 : ℕ) : ℝ) * (Real.exp (-((k + 2 : ℕ) : ℝ) * u) * momentInt B k (Real.exp (-u))) +
          (Real.exp (-((k + 2 : ℕ) : ℝ) * u) * Real.exp (-u)) * momentInt B (k + 1) (Real.exp (-u)) := by
        ring
    _ = _ := by rw [hpow]

private lemma scaledMoment_iteratedDeriv {B : ℝ → ℝ} (hB : LinearGrowthOnIoi2 B) (j : ℕ) :
    (∀ u : ℝ, iteratedDeriv j (scaledMoment B 0) u =
      ∑ k ∈ Finset.range (j + 1), towerCoeff2 j k * scaledMoment B k u) ∧
    Differentiable ℝ (iteratedDeriv j (scaledMoment B 0)) := by
  induction j with
  | zero =>
    refine ⟨fun u => by simp [towerCoeff2], fun u => (scaledMoment_hasDerivAt hB 0 u).differentiableAt⟩
  | succ j ih =>
    have heq : iteratedDeriv j (scaledMoment B 0) =
        fun u : ℝ => ∑ k ∈ Finset.range (j + 1), towerCoeff2 j k * scaledMoment B k u :=
      funext ih.1
    have hderiv (u : ℝ) : HasDerivAt (iteratedDeriv j (scaledMoment B 0))
        (∑ k ∈ Finset.range (j + 2), towerCoeff2 (j + 1) k * scaledMoment B k u) u := by
      rw [heq]
      have hsum := HasDerivAt.fun_sum fun k (_ : k ∈ Finset.range (j + 1)) =>
        (scaledMoment_hasDerivAt hB k u).const_mul (towerCoeff2 j k)
      refine hsum.congr_deriv ?_
      have hsplit1 : (∑ k ∈ Finset.range (j + 1), towerCoeff2 j k *
          (-((k + 2 : ℕ) : ℝ) * scaledMoment B k u + scaledMoment B (k + 1) u)) =
          (∑ k ∈ Finset.range (j + 1), -((k + 2 : ℕ) : ℝ) * towerCoeff2 j k * scaledMoment B k u) +
            ∑ k ∈ Finset.range (j + 1), towerCoeff2 j k * scaledMoment B (k + 1) u := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      have hpad : ∑ k ∈ Finset.range (j + 1), -((k + 2 : ℕ) : ℝ) * towerCoeff2 j k * scaledMoment B k u =
          ∑ k ∈ Finset.range (j + 2), -((k + 2 : ℕ) : ℝ) * towerCoeff2 j k * scaledMoment B k u := by
        symm
        rw [Finset.sum_range_succ, towerCoeff2_eq_zero_of_lt (Nat.lt_succ_self j)]
        simp
      have hshift : ∑ k ∈ Finset.range (j + 1), towerCoeff2 j k * scaledMoment B (k + 1) u =
          ∑ k ∈ Finset.range (j + 2), (if k = 0 then 0 else towerCoeff2 j (k - 1)) * scaledMoment B k u := by
        symm
        rw [Finset.sum_range_succ']
        simp only [↓reduceIte, zero_mul, add_zero, Nat.succ_ne_zero, Nat.add_sub_cancel]
      rw [hsplit1, hpad, hshift, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by simp [towerCoeff2, add_mul]
    refine ⟨fun u => by rw [iteratedDeriv_succ, (hderiv u).deriv], fun u => ?_⟩
    have heq' : iteratedDeriv (j + 1) (scaledMoment B 0) =
        fun x : ℝ => ∑ k ∈ Finset.range (j + 2), towerCoeff2 (j + 1) k * scaledMoment B k x :=
      funext fun x => by rw [iteratedDeriv_succ, (hderiv x).deriv]
    rw [heq']
    exact DifferentiableAt.fun_sum fun k _ =>
      (scaledMoment_hasDerivAt hB k u).differentiableAt.const_mul (towerCoeff2 (j + 1) k)

private lemma scaledMoment_uniform_bound {B : ℝ → ℝ} (hB : LinearGrowthOnIoi2 B) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, |scaledMoment B k u| ≤ M := by
  have hB' := hB
  obtain ⟨_, K₀, hK₀, bB⟩ := hB
  refine ⟨K₀ * ((k + 1).factorial : ℝ), by positivity, fun u => ?_⟩
  let t : ℝ := Real.exp (-u)
  have ht : 0 < t := Real.exp_pos (-u)
  have hint_full := integrableOn_pow_mul_exp_neg_Ioi (k + 1) ht
  have hint_B := momentInt_integrableOn hB' k ht
  have hm_le : |momentInt B k t| ≤ K₀ * (((k + 1).factorial : ℝ) / t ^ (k + 2)) := by
    calc |∫ x in Ioi (2 : ℝ), B x * x ^ k * Real.exp (-t * x)|
        ≤ ∫ x in Ioi (2 : ℝ), |B x * x ^ k * Real.exp (-t * x)| := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun x => B x * x ^ k * Real.exp (-t * x))
      _ ≤ ∫ x in Ioi (2 : ℝ), K₀ * (x ^ (k + 1) * Real.exp (-t * x)) := by
          refine setIntegral_mono_on hint_B.norm ((hint_full.mono_set (Ioi_subset_Ioi (by norm_num))).const_mul K₀)
            measurableSet_Ioi fun x hx => ?_
          change 2 < x at hx
          have hx0 : 0 ≤ x := by linarith
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (pow_nonneg hx0 k)]
          calc |B x| * x ^ k * Real.exp (-t * x)
              ≤ (K₀ * x) * x ^ k * Real.exp (-t * x) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (bB x hx) (pow_nonneg hx0 k))
                  (Real.exp_pos _).le
            _ = K₀ * (x ^ (k + 1) * Real.exp (-t * x)) := by rw [pow_succ']; ring
      _ ≤ ∫ x in Ioi (0 : ℝ), K₀ * (x ^ (k + 1) * Real.exp (-t * x)) := by
          refine setIntegral_mono_set (hint_full.const_mul K₀) ?_
            (Ioi_subset_Ioi (show (0 : ℝ) ≤ 2 by norm_num)).eventuallySubset
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          change 0 < x at hx
          exact mul_nonneg hK₀ (mul_nonneg (pow_nonneg hx.le (k + 1)) (Real.exp_pos _).le)
      _ = K₀ * (((k + 1).factorial : ℝ) / t ^ (k + 2)) := by
          rw [integral_const_mul, integral_pow_mul_exp_neg_Ioi (k + 1) ht]
  unfold scaledMoment scaledOn
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp_eq : Real.exp (-((k + 2 : ℕ) : ℝ) * u) = t ^ (k + 2) := by
    dsimp [t]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [show Real.exp (-u) = t from rfl, hexp_eq]
  calc t ^ (k + 2) * |momentInt B k t|
      ≤ t ^ (k + 2) * (K₀ * (((k + 1).factorial : ℝ) / t ^ (k + 2))) :=
        mul_le_mul_of_nonneg_left hm_le (pow_nonneg ht.le _)
    _ = K₀ * ((k + 1).factorial : ℝ) := by field_simp [(pow_pos ht (k + 2)).ne']

private lemma scaledRay_I_prime_eq (u : ℝ) :
    scaledRay I_prime u = ((scaledMoment primeReal 0 u : ℝ) : ℂ) := by
  let a : ℕ → ℝ := fun n => if Nat.Prime n then 1 else 0
  let S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), a k
  have hS : ∀ n : ℕ, S n = (Nat.primeCounting n : ℝ) := fun n => by
    have hcount : Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
      rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_eq_card_filter_range]
    dsimp [S, a]
    rw [hcount, Finset.sum_boole]
  have ha0 : a 0 = 0 := by simp [a, Nat.not_prime_zero]
  have ha1 : a 1 = 0 := by simp [a, Nat.not_prime_one]
  have hab : ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C := ⟨1, fun n => by dsimp [a]; split_ifs <;> simp⟩
  have hAbel := tsum_mul_exp_eq_integral a ha0 ha1 hab S (fun _ => rfl) (Real.exp_pos (-u))
  have hprime_eq : (fun x : ℝ => S ⌊x⌋₊ * Real.exp (-Real.exp (-u) * x)) =
      fun x : ℝ => primeReal x * x ^ 0 * Real.exp (-Real.exp (-u) * x) := by
    funext x; simp [primeReal, hS]
  rw [hprime_eq] at hAbel
  have hval : value I_prime (qRay u) = ((∑' n : ℕ, a n * Real.exp (-Real.exp (-u) * (n : ℝ)) : ℝ) : ℂ) := by
    unfold value
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    simp only [PrimeNome.term, I_prime, PowerSeries.coeff_mk, qRay, Complex.ofReal_mul]
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    split_ifs with hp
    · simp only [a, hp, ↓reduceIte, one_mul, Complex.ofReal_one]
      congr 2; ring
    · simp only [a, hp, ↓reduceIte, zero_mul, Complex.ofReal_zero]
  unfold scaledRay scaledMoment scaledOn momentInt
  rw [tRay, hval, ← Complex.ofReal_mul, hAbel, ← mul_assoc, ← Real.exp_add]
  congr 1; congr 1
  rw [show -((0 + 2 : ℕ) : ℝ) * u = -u + -u by push_cast; ring]

private lemma iteratedDeriv_ofReal_eq (f : ℝ → ℝ)
    (hf : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k f)) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun t : ℝ => (f t : ℂ)) u = ((iteratedDeriv j f u : ℝ) : ℂ) := by
  induction j generalizing u with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, show iteratedDeriv j (fun t : ℝ => (f t : ℂ)) =
        fun t : ℝ => ((iteratedDeriv j f t : ℝ) : ℂ) from funext ih]
    exact ((hf j u).hasDerivAt.ofReal_comp).deriv

private lemma scaledRay_I_prime_uniform_bound (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : ℝ, ‖iteratedDeriv j (scaledRay I_prime) v‖ ≤ B := by
  choose Mk hMk_nonneg hMk_bd using fun k => scaledMoment_uniform_bound primeReal_linearGrowth k
  refine ⟨∑ k ∈ Finset.range (j + 1), |towerCoeff2 j k| * Mk k,
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (hMk_nonneg k), fun v => ?_⟩
  have heq : scaledRay I_prime = fun t : ℝ => (scaledMoment primeReal 0 t : ℂ) :=
    funext scaledRay_I_prime_eq
  have hdiff : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k (scaledMoment primeReal 0)) :=
    fun k => (scaledMoment_iteratedDeriv primeReal_linearGrowth k).2
  rw [heq, iteratedDeriv_ofReal_eq _ hdiff j v, Complex.norm_real, Real.norm_eq_abs,
    (scaledMoment_iteratedDeriv primeReal_linearGrowth j).1 v]
  calc |∑ k ∈ Finset.range (j + 1), towerCoeff2 j k * scaledMoment primeReal k v|
      ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff2 j k * scaledMoment primeReal k v| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff2 j k| * Mk k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hMk_bd k v) (abs_nonneg _)

/-- Scaled logarithmic derivative of partitions into primes:
`fPart u = e^{-2u} ∑_{n ≥ 1} σ_P(n) e^{-n e^{-u}} = e^{-u} scaledRay partLogDerivSeries u`. -/
@[expose] def fPart (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)) * scaledRay partLogDerivSeries u

private def hI (v : ℝ) : ℂ :=
  deriv (scaledRay I_prime) v + scaledRay I_prime v

private lemma hI_uniform_bound (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : ℝ, ‖iteratedDeriv j hI v‖ ≤ B := by
  obtain ⟨B₀, hB₀, hb₀⟩ := scaledRay_I_prime_uniform_bound j
  obtain ⟨B₁, hB₁, hb₁⟩ := scaledRay_I_prime_uniform_bound (j + 1)
  refine ⟨B₁ + B₀, add_nonneg hB₁ hB₀, fun v => ?_⟩
  have hcd0 : ContDiff ℝ ⊤ (scaledRay I_prime) :=
    contDiff_iff_contDiffAt.mpr fun w =>
      (scaledRay_analytic I_prime_polyBound.to_diskCoeffBound w).contDiffAt
  have hcd1 : ContDiff ℝ ⊤ (deriv (scaledRay I_prime)) :=
    contDiff_iff_contDiffAt.mpr fun w =>
      (scaledRay_analytic I_prime_polyBound.to_diskCoeffBound w).deriv.contDiffAt
  have heq : hI = fun i => deriv (scaledRay I_prime) i + scaledRay I_prime i := rfl
  rw [heq, iteratedDeriv_fun_add (hcd1.contDiffAt.of_le le_top) (hcd0.contDiffAt.of_le le_top),
    ← iteratedDeriv_succ']
  exact (norm_add_le _ _).trans (add_le_add (hb₁ v) (hb₀ v))

private lemma d_u_add (S T : PowerSeries ℂ) : d_u (S + T) = d_u S + d_u T := by
  simp only [d_u, map_add, mul_add]
  ring

private lemma d_u_iter_add (j : ℕ) (S T : PowerSeries ℂ) :
    d_u^[j] (S + T) = d_u^[j] S + d_u^[j] T := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, d_u_add]

private lemma formalSeries_Gamma_two_sub :
    d_u gHat + gHat = formalSeries (fun ξ : ℂ => Complex.Gamma (2 - ξ)) := by
  have han0 : AnalyticAt ℂ phi 0 := phi_analyticAt_of_avoids_posNat fun n hn h0 => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℂ) = 0 := h0.symm
    have hre := congrArg Complex.re hn0
    simp at hre
    linarith
  have hjet := Minor.toSeries_jet (a := aGamma) han0
  rw [aGamma_toSeries] at hjet
  have hgam_loc : (fun ξ : ℂ => -ξ * phi ξ + phi ξ) =ᶠ[𝓝 (0 : ℂ)]
      fun ξ : ℂ => Complex.Gamma (2 - ξ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with ξ hξ
    have h1ξ : (1 : ℂ) - ξ ≠ 0 := by
      intro h0
      have hn : ‖ξ‖ = 1 := by
        have : ξ = 1 := by linear_combination -h0
        rw [this, norm_one]
      rw [Metric.mem_ball, dist_zero_right] at hξ
      linarith
    have hgam := Complex.Gamma_add_one (1 - ξ) h1ξ
    rw [show (1 - ξ) + 1 = 2 - ξ by ring] at hgam
    dsimp only [phi]
    linear_combination -hgam
  ext n
  cases n with
  | zero => simp [d_u, gHat, formalSeries]
  | succ k =>
    rw [map_add, ← hjet]
    simp only [aGamma, Minor.jet, Minor.toSeries, PowerSeries.coeff_mk, gHat, formalSeries]
    have hcd1 : ContDiffAt ℂ k (fun ξ : ℂ => -ξ * phi ξ) 0 :=
      ((analyticAt_id.neg.mul han0).contDiffAt).of_le le_top
    have hcd2 : ContDiffAt ℂ k phi 0 := (han0.contDiffAt).of_le le_top
    rw [← iteratedDeriv_fun_add hcd1 hcd2]
    exact hgam_loc.iteratedDeriv_eq k

private lemma hI_hasAsympExp (hpnt : PNTAllOrders) (j : ℕ) :
    HasAsympExp (iteratedDeriv j hI)
      (d_u^[j] (formalSeries (fun ξ : ℂ => Complex.Gamma (2 - ξ)))) := by
  have hcd0 : ContDiff ℝ ⊤ (scaledRay I_prime) :=
    contDiff_iff_contDiffAt.mpr fun w =>
      (scaledRay_analytic I_prime_polyBound.to_diskCoeffBound w).contDiffAt
  have hcd1 : ContDiff ℝ ⊤ (deriv (scaledRay I_prime)) :=
    contDiff_iff_contDiffAt.mpr fun w =>
      (scaledRay_analytic I_prime_polyBound.to_diskCoeffBound w).deriv.contDiffAt
  have heq : iteratedDeriv j hI =
      fun u => iteratedDeriv (j + 1) (scaledRay I_prime) u + iteratedDeriv j (scaledRay I_prime) u := by
    funext u
    have hh : hI = fun i => deriv (scaledRay I_prime) i + scaledRay I_prime i := rfl
    rw [hh, iteratedDeriv_fun_add (hcd1.contDiffAt.of_le le_top) (hcd0.contDiffAt.of_le le_top),
      ← iteratedDeriv_succ']
  rw [heq, ← formalSeries_Gamma_two_sub, d_u_iter_add, ← Function.iterate_succ_apply d_u j gHat]
  exact (pnt_implies_g_asymptotic hpnt (j + 1)).add (pnt_implies_g_asymptotic hpnt j)

private lemma hI_eq (v : ℝ) :
    hI v = (tRay v) ^ 2 * ∑' n : ℕ, (if Nat.Prime n then (n : ℂ) else 0) * (qRay v) ^ n := by
  have hq : ‖qRay v‖ < 1 := qRay_disk v
  have hd_t : HasDerivAt tRay (-tRay v) v := tRay_deriv v
  have hd_val : HasDerivAt (fun x : ℝ => analyticCoordinates I_prime (qRay x) 1)
      (tRay v * qRay v * value (seriesJet I_prime 1) (qRay v)) v := by
    simpa [analyticCoordinates] using ray_source_deriv I_prime_polyBound.to_diskCoeffBound 0 v
  have hd_sr : HasDerivAt (scaledRay I_prime)
      ((-tRay v) * value I_prime (qRay v) +
        tRay v * (tRay v * qRay v * value (seriesJet I_prime 1) (qRay v))) v := by
    convert hd_t.mul hd_val using 1
    · funext _; rfl
    · simp [analyticCoordinates, seriesJet]
  have hh : hI v = (tRay v) ^ 2 * (qRay v * value (seriesJet I_prime 1) (qRay v)) := by
    dsimp only [hI]
    rw [hd_sr.deriv]
    unfold scaledRay
    ring
  rw [hh]
  congr 1
  have hs_abs := seriesJet_abs I_prime_polyBound.to_diskCoeffBound 1 hq
  have hs_summ : Summable (fun n : ℕ => PrimeNome.term (seriesJet I_prime 1) (qRay v) n) :=
    hs_abs.of_norm
  have hadd : Summable (fun n : ℕ => (if Nat.Prime (n + 1) then ((n + 1 : ℕ) : ℂ) else 0) *
      (qRay v) ^ (n + 1)) := by
    refine (hs_summ.mul_left (qRay v)).congr fun n => ?_
    simp only [PrimeNome.term, seriesJet, Function.iterate_one,
      PowerSeries.coeff_derivative, I_prime, PowerSeries.coeff_mk]
    rw [pow_succ']
    split_ifs <;> [push_cast; skip] <;> ring
  have hshift_summ : Summable (fun n : ℕ => (if Nat.Prime n then (n : ℂ) else 0) * (qRay v) ^ n) :=
    (summable_nat_add_iff 1).mp hadd
  trans ∑' n : ℕ, (if Nat.Prime (n + 1) then ((n + 1 : ℕ) : ℂ) else 0) * (qRay v) ^ (n + 1)
  · rw [value, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [PrimeNome.term, seriesJet, Function.iterate_one, PowerSeries.coeff_derivative,
      I_prime, PowerSeries.coeff_mk]
    rw [pow_succ']
    split_ifs <;> [push_cast; skip] <;> ring
  · rw [hshift_summ.tsum_eq_zero_add]
    simp only [Nat.not_prime_zero, ↓reduceIte, zero_mul, zero_add]

private lemma part_sigma_ext {n₁ n₂ : ℕ} {d₁ : Nat.divisors (n₁ + 1)} {d₂ : Nat.divisors (n₂ + 1)}
    (hn : n₁ = n₂) (hd : d₁.1 = d₂.1) : (⟨n₁, d₁⟩ : Σ k, Nat.divisors (k + 1)) = ⟨n₂, d₂⟩ := by
  subst hn
  congr 1
  exact Subtype.ext hd

private def partDivisorEquiv : ℕ × ℕ ≃ Σ n : ℕ, Nat.divisors (n + 1) where
  toFun p := ⟨(p.1 + 1) * (p.2 + 1) - 1,
    ⟨p.1 + 1, Nat.mem_divisors.mpr ⟨by
      have h1 : 1 ≤ (p.1 + 1) * (p.2 + 1) := Nat.succ_le_of_lt (by positivity)
      rw [Nat.sub_add_cancel h1]
      exact dvd_mul_right _ _, by omega⟩⟩⟩
  invFun s := (s.2.1 - 1, (s.1 + 1) / s.2.1 - 1)
  left_inv p := by
    ext <;> dsimp only
    · omega
    · have hmul : (p.1 + 1) * (p.2 + 1) - 1 + 1 = (p.1 + 1) * (p.2 + 1) :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))
      rw [hmul, Nat.mul_div_right _ (Nat.succ_pos _)]
      omega
  right_inv s := by
    rcases s with ⟨n, ⟨d, hd⟩⟩
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_dvd : d ∣ n + 1 := Nat.dvd_of_mem_divisors hd
    have hq_pos : 0 < (n + 1) / d :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hd_dvd) hd_pos
    have hfst : (d - 1 + 1) * ((n + 1) / d - 1 + 1) - 1 = n := by
      rw [Nat.sub_add_cancel hd_pos, Nat.sub_add_cancel hq_pos, Nat.mul_div_cancel' hd_dvd]
      omega
    exact part_sigma_ext hfst (Nat.sub_add_cancel hd_pos)

private def partPairTerm (r : ℝ) (p k : ℕ) : ℝ :=
  if Nat.Prime (p + 1) then ((p + 1 : ℕ) : ℝ) * r ^ ((p + 1) * (k + 1)) else 0

private lemma partPair_summable {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun q : ℕ × ℕ => partPairTerm r q.1 q.2) := by
  have hrow : ∀ p : ℕ, Summable (fun k : ℕ => partPairTerm r p k) := fun p => by
    dsimp [partPairTerm]
    split_ifs
    · have hp1 : 0 < r ^ (p + 1) := pow_pos hr0 _
      have hp_lt : r ^ (p + 1) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero p)
      refine ((summable_geometric_of_lt_one hp1.le hp_lt).mul_left
        (((p + 1 : ℕ) : ℝ) * r ^ (p + 1))).congr fun k => ?_
      rw [show (p + 1) * (k + 1) = (p + 1) + (p + 1) * k by ring, pow_add r (p + 1) ((p + 1) * k),
        pow_mul r (p + 1) k]
      ring
    · simp
  have hcol : Summable (fun p : ℕ => ∑' k : ℕ, partPairTerm r p k) := by
    have hnorm : ‖r‖ < 1 := by simpa [abs_of_pos hr0] using hr1
    have hdom : Summable (fun p : ℕ => ((p + 1 : ℝ) * r ^ (p + 1)) / (1 - r)) := by
      have h1 := ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).comp_injective
        (show Function.Injective (fun p : ℕ => p + 1) from fun _ _ h => Nat.add_right_cancel h)).mul_right
        (1 - r)⁻¹
      refine h1.congr fun p => ?_
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_one, div_eq_mul_inv]
    refine hdom.of_nonneg_of_le (fun p => tsum_nonneg fun k => by
      dsimp [partPairTerm]; split_ifs <;> positivity) fun p => ?_
    dsimp [partPairTerm]
    split_ifs
    · have hp1 : 0 < r ^ (p + 1) := pow_pos hr0 _
      have hp_lt : r ^ (p + 1) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero p)
      have heq : (fun k : ℕ => ((p + 1 : ℕ) : ℝ) * r ^ ((p + 1) * (k + 1))) =
          fun k : ℕ => ((p + 1 : ℕ) : ℝ) * r ^ (p + 1) * (r ^ (p + 1)) ^ k := by
        funext k
        rw [show (p + 1) * (k + 1) = (p + 1) + (p + 1) * k by ring, pow_add r (p + 1) ((p + 1) * k),
          pow_mul r (p + 1) k]
        ring
      rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hp1.le hp_lt]
      have hden : 1 - r ≤ 1 - r ^ (p + 1) := by
        have hle : r ^ (p + 1) ≤ r := by
          rw [pow_succ']
          exact mul_le_of_le_one_right hr0.le (pow_le_one₀ hr0.le hr1.le)
        linarith
      have h1mr : 0 < 1 - r := sub_pos.mpr hr1
      push_cast
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by positivity) h1mr hden
    · simp only [tsum_zero]; positivity
  exact (summable_prod_of_nonneg fun q => by dsimp [partPairTerm]; split_ifs <;> positivity).mpr ⟨hrow, hcol⟩

private lemma tsum_sigmaP_eq_double_sum {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((∑' n : ℕ, sigmaP n * r ^ n) =
      ∑' k : ℕ, ∑' n : ℕ, (if Nat.Prime n then (n : ℝ) else 0) * r ^ ((k + 1) * n)) ∧
    Summable (fun k : ℕ => ∑' n : ℕ, (if Nat.Prime n then (n : ℝ) else 0) * r ^ ((k + 1) * n)) := by
  have hr_norm : ‖r‖ < 1 := by simpa [abs_of_pos hr0] using hr1
  have hg : Summable (fun q : ℕ × ℕ => partPairTerm r q.1 q.2) := partPair_summable hr0 hr1
  have hg_sigma : Summable (fun s : Σ n : ℕ, Nat.divisors (n + 1) =>
      partPairTerm r (partDivisorEquiv.symm s).1 (partDivisorEquiv.symm s).2) :=
    (partDivisorEquiv.symm.summable_iff).mpr hg
  have hsum_sig : Summable (fun n : ℕ => sigmaP n * r ^ n) := by
    have habs := seriesJet_abs partLogDeriv_polyBound.to_diskCoeffBound 0
      (show ‖(r : ℂ)‖ < 1 by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1)
    refine habs.congr fun n => ?_
    simp only [seriesJet, Function.iterate_zero, id_eq, PrimeNome.term, partLogDerivSeries,
      PowerSeries.coeff_mk, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    congr 1
    have hsig_c : (∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, if p ∣ n then (p : ℂ) else 0) =
        ((sigmaP n : ℝ) : ℂ) := by
      dsimp [sigmaP]
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
    rw [hsig_c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sigmaP_nonneg n)]
  have h1 : (∑' q : ℕ × ℕ, partPairTerm r q.1 q.2) = ∑' n : ℕ, sigmaP n * r ^ n := by
    rw [← partDivisorEquiv.symm.tsum_eq (fun q : ℕ × ℕ => partPairTerm r q.1 q.2),
      hg_sigma.tsum_sigma' (fun _ => Summable.of_finite)]
    have hsucc : (∑' n : ℕ, ∑' d : Nat.divisors (n + 1),
        partPairTerm r (partDivisorEquiv.symm ⟨n, d⟩).1 (partDivisorEquiv.symm ⟨n, d⟩).2) =
        ∑' n : ℕ, sigmaP (n + 1) * r ^ (n + 1) := by
      refine tsum_congr fun n => ?_
      rw [tsum_fintype]
      have hterm : (∑ d : Nat.divisors (n + 1),
          partPairTerm r (partDivisorEquiv.symm ⟨n, d⟩).1 (partDivisorEquiv.symm ⟨n, d⟩).2) =
          ∑ d ∈ (n + 1).divisors, (if Nat.Prime d then (d : ℝ) else 0) * r ^ (n + 1) := by
        rw [← Finset.sum_coe_sort (n + 1).divisors fun d =>
          (if Nat.Prime d then (d : ℝ) else 0) * r ^ (n + 1)]
        refine Finset.sum_congr rfl fun d _ => ?_
        have hd_pos : 0 < d.1 := Nat.pos_of_mem_divisors d.2
        have hd_dvd : d.1 ∣ n + 1 := Nat.dvd_of_mem_divisors d.2
        have hq_pos : 0 < (n + 1) / d.1 :=
          Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hd_dvd) hd_pos
        dsimp [partPairTerm, partDivisorEquiv]
        rw [Nat.sub_add_cancel hd_pos, Nat.sub_add_cancel hq_pos, Nat.mul_div_cancel' hd_dvd]
        split_ifs <;> simp
      rw [hterm, ← Finset.sum_mul]
      congr 1
      dsimp only [sigmaP]
      rw [Finset.sum_filter]
      have hsub : (n + 1).divisors ⊆ Finset.Icc 1 (n + 1) := fun d hd =>
        Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
          Nat.le_of_dvd (Nat.succ_pos n) (Nat.dvd_of_mem_divisors hd)⟩
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun p hp => ?_
        by_cases hpr : Nat.Prime p <;> simp [hpr, Nat.dvd_of_mem_divisors hp]
      · intro p _ hp_not
        by_cases hpr : Nat.Prime p
        · have hnd : ¬ p ∣ n + 1 := fun hdvd =>
            hp_not (Nat.mem_divisors.mpr ⟨hdvd, Nat.succ_ne_zero n⟩)
          simp [hpr, hnd]
        · simp [hpr]
    rw [hsucc, hsum_sig.tsum_eq_zero_add]
    have h0 : sigmaP 0 * r ^ 0 = 0 := by simp [sigmaP]
    rw [h0, zero_add]
  have hg_swap : Summable (fun q : ℕ × ℕ => partPairTerm r q.2 q.1) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr hg
  have hprod_swap := (summable_prod_of_nonneg fun q : ℕ × ℕ => by
    dsimp [partPairTerm]; split_ifs <;> positivity).mp hg_swap
  have hinner : ∀ k : ℕ, (∑' p : ℕ, partPairTerm r p k) =
      ∑' n : ℕ, (if Nat.Prime n then (n : ℝ) else 0) * r ^ ((k + 1) * n) := fun k => by
    have hs_n : Summable (fun n : ℕ => (if Nat.Prime n then (n : ℝ) else 0) * r ^ ((k + 1) * n)) := by
      rw [← summable_nat_add_iff 1]
      refine (hprod_swap.1 k).congr fun p => ?_
      simp [partPairTerm, mul_comm]
    rw [hs_n.tsum_eq_zero_add]
    simp only [Nat.not_prime_zero, ↓reduceIte, zero_mul, zero_add]
    refine tsum_congr fun p => ?_
    simp [partPairTerm, mul_comm]
  have h2 : (∑' q : ℕ × ℕ, partPairTerm r q.1 q.2) =
      ∑' k : ℕ, ∑' n : ℕ, (if Nat.Prime n then (n : ℝ) else 0) * r ^ ((k + 1) * n) := by
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq (fun q : ℕ × ℕ => partPairTerm r q.1 q.2)]
    change (∑' c : ℕ × ℕ, partPairTerm r c.2 c.1) = _
    rw [hg_swap.tsum_prod' hprod_swap.1]
    exact tsum_congr hinner
  exact ⟨h1.symm.trans h2, hprod_swap.2.congr hinner⟩

private lemma fPart_eq_tsum_hI (u : ℝ) :
    fPart u = ∑' k : ℕ, ((k + 1 : ℂ) ^ 2)⁻¹ * hI (u - Real.log (k + 1)) := by
  let t : ℝ := Real.exp (-u)
  let r : ℝ := Real.exp (-t)
  have ht : 0 < t := Real.exp_pos (-u)
  have hr0 : 0 < r := Real.exp_pos (-t)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hterm : ∀ k : ℕ, ((k + 1 : ℂ) ^ 2)⁻¹ * hI (u - Real.log (k + 1)) =
      (tRay u) ^ 2 * ((∑' n : ℕ, (if Nat.Prime n then (n : ℝ) else 0) * r ^ ((k + 1) * n) : ℝ) : ℂ) := by
    intro k
    have hk_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
    have ht_shift : tRay (u - Real.log (k + 1)) = ((k + 1 : ℕ) : ℂ) * tRay u := by
      unfold tRay
      rw [show -(u - Real.log (k + 1)) = -u + Real.log (k + 1) by ring, Real.exp_add,
        Real.exp_log hk_pos]
      push_cast; ring
    have hq_shift : qRay (u - Real.log (k + 1)) = (qRay u) ^ (k + 1) := by
      unfold qRay
      rw [show -(u - Real.log (k + 1)) = -u + Real.log (k + 1) by ring, Real.exp_add,
        Real.exp_log hk_pos, show -(Real.exp (-u) * (k + 1 : ℝ)) = (k + 1 : ℕ) * (-Real.exp (-u)) by
          push_cast; ring,
        Real.exp_nat_mul]
      push_cast; rfl
    rw [hI_eq (u - Real.log (k + 1)), ht_shift, hq_shift]
    have hk_ne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hmul_c : ((k + 1 : ℂ) ^ 2)⁻¹ * ((((k + 1 : ℕ) : ℂ) * tRay u) ^ 2 *
        ∑' n : ℕ, (if Nat.Prime n then (n : ℂ) else 0) * ((qRay u) ^ (k + 1)) ^ n) =
        (tRay u) ^ 2 * ∑' n : ℕ, (if Nat.Prime n then (n : ℂ) else 0) * (qRay u) ^ ((k + 1) * n) := by
      have hpow_k : ∀ n : ℕ, ((qRay u) ^ (k + 1)) ^ n = (qRay u) ^ ((k + 1) * n) :=
        fun n => by rw [← pow_mul]
      simp_rw [hpow_k]
      rw [mul_pow, ← mul_assoc, ← mul_assoc]
      congr 1
      push_cast
      field_simp [hk_ne]
    rw [hmul_c]
    congr 1
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [qRay, r, t, ← Complex.ofReal_pow]
    split_ifs <;> simp
  simp_rw [hterm]
  have hf_val : fPart u = (tRay u) ^ 2 * ((∑' n : ℕ, sigmaP n * r ^ n : ℝ) : ℂ) := by
    unfold fPart scaledRay
    rw [show Complex.exp (-(u : ℂ)) = tRay u from by unfold tRay; rw [Complex.ofReal_exp, Complex.ofReal_neg],
      ← mul_assoc, ← pow_two]
    congr 1
    unfold value
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [PrimeNome.term, partLogDerivSeries, PowerSeries.coeff_mk, sigmaP, qRay, r, t,
      ← Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  obtain ⟨hdbl, _⟩ := tsum_sigmaP_eq_double_sum hr0 hr1
  rw [hf_val, hdbl, Complex.ofReal_tsum, tsum_mul_left]

private lemma iteratedDeriv_fPart_eq_tsum (j : ℕ) (u : ℝ) :
    iteratedDeriv j fPart u =
      ∑' k : ℕ, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1)) := by
  have hinv_summ : Summable (fun k : ℕ => ((k + 1 : ℝ) ^ 2)⁻¹) := by
    have h1 := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (show Function.Injective (fun k : ℕ => k + 1) from fun _ _ h => Nat.add_right_cancel h)
    refine h1.congr fun k => by simp
  have hcd_hI : ∀ k : ℕ, ContDiff ℝ ⊤ hI := fun _ =>
    contDiff_iff_contDiffAt.mpr fun v =>
      ((scaledRay_analytic I_prime_polyBound.to_diskCoeffBound v).deriv.add
        (scaledRay_analytic I_prime_polyBound.to_diskCoeffBound v)).contDiffAt
  have h_step : ∀ (m : ℕ) (x : ℝ),
      HasDerivAt (fun t : ℝ => ∑' k : ℕ, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv m hI (t - Real.log (k + 1)))
        (∑' k : ℕ, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv (m + 1) hI (x - Real.log (k + 1))) x := by
    intro m x
    obtain ⟨Bm, hBm, hb⟩ := hI_uniform_bound (m + 1)
    let g : ℕ → ℝ → ℂ := fun k t => ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv m hI (t - Real.log (k + 1))
    let g' : ℕ → ℝ → ℂ := fun k t => ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv (m + 1) hI (t - Real.log (k + 1))
    have hg_deriv : ∀ (k : ℕ) (y : ℝ), y ∈ (Set.univ : Set ℝ) → HasDerivAt (g k) (g' k y) y := by
      intro k y _
      have hd1 : HasDerivAt (fun t : ℝ => t - Real.log (k + 1)) 1 y :=
        (hasDerivAt_id y).sub_const _
      have hd2 : HasDerivAt (iteratedDeriv m hI) (iteratedDeriv (m + 1) hI (y - Real.log (k + 1)))
          (y - Real.log (k + 1)) := by
        rw [iteratedDeriv_succ]
        exact ((hcd_hI k).differentiable_iteratedDeriv m (by simp) (y - Real.log (k + 1))).hasDerivAt
      have hc : HasDerivAt (fun t : ℝ => iteratedDeriv m hI (t - Real.log (k + 1)))
          (iteratedDeriv (m + 1) hI (y - Real.log (k + 1))) y := by
        simpa [Function.comp_def, one_smul] using hd2.scomp y hd1
      convert hc.const_mul (((k + 1 : ℂ) ^ 2)⁻¹) using 1
    have hg_bound : ∀ (k : ℕ) (y : ℝ), y ∈ (Set.univ : Set ℝ) → ‖g' k y‖ ≤ Bm * ((k + 1 : ℝ) ^ 2)⁻¹ := by
      intro k y _
      dsimp only [g']
      rw [norm_mul, norm_inv, norm_pow, show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < k + 1), mul_comm]
      exact mul_le_mul_of_nonneg_right (hb _) (by positivity)
    obtain ⟨B₀, _, hb₀⟩ := hI_uniform_bound m
    have hg0 : Summable (fun k : ℕ => g k x) := by
      refine Summable.of_norm_bounded (hinv_summ.mul_left B₀) fun k => ?_
      dsimp only [g]
      rw [norm_mul, norm_inv, norm_pow, show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < k + 1), mul_comm]
      exact mul_le_mul_of_nonneg_right (hb₀ _) (by positivity)
    exact hasDerivAt_tsum_of_isPreconnected (hinv_summ.mul_left Bm) isOpen_univ
      convex_univ.isPreconnected hg_deriv hg_bound (Set.mem_univ x) hg0 (Set.mem_univ x)
  have hall : ∀ m : ℕ, ∀ x : ℝ,
      iteratedDeriv m fPart x =
        ∑' k : ℕ, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv m hI (x - Real.log (k + 1)) := by
    intro m
    induction m with
    | zero => intro x; simpa [iteratedDeriv_zero] using fPart_eq_tsum_hI x
    | succ m ih =>
      intro x
      rw [iteratedDeriv_succ, show iteratedDeriv m fPart = fun t : ℝ =>
        ∑' k : ℕ, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv m hI (t - Real.log (k + 1)) from funext ih]
      exact (h_step m x).deriv
  exact hall j u

private def binomSum (s K : ℕ) (x : ℂ) : ℂ :=
  ∑ r ∈ Finset.range K, (Nat.choose (s + r) r : ℂ) * x ^ r

private lemma inv_sub_pow_approx (s K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, ‖x‖ ≤ 1 / 2 →
      ‖(1 - x)⁻¹ ^ (s + 1) - binomSum s K x‖ ≤ C * ‖x‖ ^ K := by
  have hnorm_inv : ∀ x : ℂ, ‖x‖ ≤ 1 / 2 → ‖(1 - x)⁻¹‖ ≤ 2 := fun x hx => by
    have hge : 1 / 2 ≤ ‖1 - x‖ := by
      have := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one] at this
      linarith
    rw [norm_inv]
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hge
  induction s generalizing K with
  | zero =>
    refine ⟨2, by norm_num, fun x hx => ?_⟩
    have h1x : 1 - x ≠ 0 := by
      intro h0
      have : x = 1 := by linear_combination -h0
      rw [this, norm_one] at hx
      linarith
    have hbinom0 : binomSum 0 K x = ∑ r ∈ Finset.range K, x ^ r := by
      dsimp only [binomSum]
      refine Finset.sum_congr rfl fun r _ => by simp
    have hgeom := geom_sum_mul x K
    have hid : (1 - x)⁻¹ ^ 1 - binomSum 0 K x = (1 - x)⁻¹ * (x ^ K) := by
      rw [pow_one, hbinom0]
      have hmul : (1 - x) * (∑ r ∈ Finset.range K, x ^ r) = 1 - x ^ K := by
        rw [mul_comm]; linear_combination -hgeom
      calc (1 - x)⁻¹ - ∑ r ∈ Finset.range K, x ^ r
          = (1 - x)⁻¹ * (1 - (1 - x) * ∑ r ∈ Finset.range K, x ^ r) := by
            rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ h1x, one_mul]
        _ = (1 - x)⁻¹ * (x ^ K) := by rw [hmul]; ring
    rw [hid, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hnorm_inv x hx) (pow_nonneg (norm_nonneg x) K)
  | succ s ih =>
    cases K with
    | zero =>
      refine ⟨2 ^ (s + 2), by positivity, fun x hx => ?_⟩
      simp only [binomSum, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm_inv x hx) (s + 2)
    | succ k =>
      obtain ⟨C₀, hC₀, hih⟩ := ih (k + 1)
      refine ⟨2 * (C₀ + (Nat.choose (s + 1 + k) k : ℝ)), by positivity, fun x hx => ?_⟩
      have h1x : 1 - x ≠ 0 := by
        intro h0
        have : x = 1 := by linear_combination -h0
        rw [this, norm_one] at hx
        linarith
      have hrel : (1 - x) * binomSum (s + 1) (k + 1) x =
          binomSum s (k + 1) x - (Nat.choose (s + 1 + k) k : ℂ) * x ^ (k + 1) := by
        conv_lhs => dsimp only [binomSum]
        rw [sub_mul, one_mul, Finset.mul_sum]
        have h1 : ∑ r ∈ Finset.range (k + 1), (Nat.choose (s + 1 + r) r : ℂ) * x ^ r =
            1 + ∑ r ∈ Finset.range k, (Nat.choose (s + 1 + (r + 1)) (r + 1) : ℂ) * x ^ (r + 1) := by
          rw [Finset.sum_range_succ']
          simp [add_comm]
        have h2 : ∑ r ∈ Finset.range (k + 1), x * ((Nat.choose (s + 1 + r) r : ℂ) * x ^ r) =
            (∑ r ∈ Finset.range k, (Nat.choose (s + 1 + r) r : ℂ) * x ^ (r + 1)) +
              (Nat.choose (s + 1 + k) k : ℂ) * x ^ (k + 1) := by
          rw [Finset.sum_range_succ]
          congr 1
          · refine Finset.sum_congr rfl fun r _ => ?_; rw [pow_succ']; ring
          · rw [pow_succ']; ring
        have h3 : (∑ r ∈ Finset.range k, (Nat.choose (s + 1 + (r + 1)) (r + 1) : ℂ) * x ^ (r + 1)) -
            (∑ r ∈ Finset.range k, (Nat.choose (s + 1 + r) r : ℂ) * x ^ (r + 1)) =
            ∑ r ∈ Finset.range k, (Nat.choose (s + (r + 1)) (r + 1) : ℂ) * x ^ (r + 1) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hch : (s + 1 + (r + 1)).choose (r + 1) = (s + 1 + r).choose r + (s + 1 + r).choose (r + 1) := by
            rw [show s + 1 + (r + 1) = (s + 1 + r).succ by omega]
            exact Nat.choose_succ_succ (s + 1 + r) r
          have hch' : ((Nat.choose (s + 1 + (r + 1)) (r + 1) : ℂ) - (Nat.choose (s + 1 + r) r : ℂ)) =
              (Nat.choose (s + (r + 1)) (r + 1) : ℂ) := by
            rw [show s + (r + 1) = s + 1 + r by omega]
            push_cast [hch]; ring
          rw [← sub_mul, hch']
        have h4 : binomSum s (k + 1) x =
            1 + ∑ r ∈ Finset.range k, (Nat.choose (s + (r + 1)) (r + 1) : ℂ) * x ^ (r + 1) := by
          dsimp only [binomSum]
          rw [Finset.sum_range_succ']
          simp [add_comm]
        rw [h1, h2, h4]
        linear_combination h3
      have hid : (1 - x)⁻¹ ^ (s + 2) - binomSum (s + 1) (k + 1) x =
          (1 - x)⁻¹ * (((1 - x)⁻¹ ^ (s + 1) - binomSum s (k + 1) x) +
            (Nat.choose (s + 1 + k) k : ℂ) * x ^ (k + 1)) := by
        rw [pow_succ']
        field_simp [h1x]
        linear_combination -hrel
      rw [hid, norm_mul]
      have h_in : ‖((1 - x)⁻¹ ^ (s + 1) - binomSum s (k + 1) x) +
          (Nat.choose (s + 1 + k) k : ℂ) * x ^ (k + 1)‖ ≤
          (C₀ + (Nat.choose (s + 1 + k) k : ℝ)) * ‖x‖ ^ (k + 1) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_natCast, norm_pow, add_mul]
        exact add_le_add (hih x hx) le_rfl
      calc ‖(1 - x)⁻¹‖ * ‖((1 - x)⁻¹ ^ (s + 1) - binomSum s (k + 1) x) +
            (Nat.choose (s + 1 + k) k : ℂ) * x ^ (k + 1)‖
          ≤ 2 * ((C₀ + (Nat.choose (s + 1 + k) k : ℝ)) * ‖x‖ ^ (k + 1)) :=
            mul_le_mul (hnorm_inv x hx) h_in (norm_nonneg _) (by positivity)
        _ = (2 * (C₀ + (Nat.choose (s + 1 + k) k : ℝ))) * ‖x‖ ^ (k + 1) := by ring

private lemma inv_sub_pow_u_bound (s K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a u : ℝ), 0 < u → 2 * |a| ≤ u →
      ‖((u - a : ℂ)⁻¹) ^ (s + 1) -
          ∑ r ∈ Finset.range K, (Nat.choose (s + r) r : ℂ) * (a : ℂ) ^ r * (u : ℂ)⁻¹ ^ (s + 1 + r)‖ ≤
        C * |a| ^ K / u ^ (s + 1 + K) := by
  obtain ⟨C, hC, hbd⟩ := inv_sub_pow_approx s K
  refine ⟨C, hC, fun a u hu hau => ?_⟩
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  let x : ℂ := (a : ℂ) / (u : ℂ)
  have hx_le : ‖x‖ ≤ 1 / 2 := by
    dsimp only [x]
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hu, div_le_iff₀ hu]
    linarith
  have heq : ((u - a : ℂ)⁻¹) ^ (s + 1) -
        ∑ r ∈ Finset.range K, (Nat.choose (s + r) r : ℂ) * (a : ℂ) ^ r * (u : ℂ)⁻¹ ^ (s + 1 + r) =
      (u : ℂ)⁻¹ ^ (s + 1) * ((1 - x)⁻¹ ^ (s + 1) - binomSum s K x) := by
    have h1 : ((u - a : ℂ)⁻¹) ^ (s + 1) = (u : ℂ)⁻¹ ^ (s + 1) * (1 - x)⁻¹ ^ (s + 1) := by
      dsimp only [x]
      rw [← mul_pow, ← mul_inv, mul_sub, mul_one, mul_div_cancel₀ _ huc]
    have h2 : (u : ℂ)⁻¹ ^ (s + 1) * binomSum s K x =
        ∑ r ∈ Finset.range K, (Nat.choose (s + r) r : ℂ) * (a : ℂ) ^ r * (u : ℂ)⁻¹ ^ (s + 1 + r) := by
      dsimp only [binomSum, x]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [div_pow, pow_add, div_eq_mul_inv, inv_pow]
      ring
    rw [h1, mul_sub, h2]
  rw [heq, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hbx := hbd x hx_le
  have hx_norm : ‖x‖ = |a| / u := by
    dsimp only [x]
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hu]
  rw [hx_norm, div_pow] at hbx
  calc (u⁻¹) ^ (s + 1) * ‖(1 - x)⁻¹ ^ (s + 1) - binomSum s K x‖
      ≤ (u⁻¹) ^ (s + 1) * (C * (|a| ^ K / u ^ K)) :=
        mul_le_mul_of_nonneg_left hbx (pow_nonneg (inv_nonneg.mpr hu.le) _)
    _ = C * |a| ^ K / u ^ (s + 1 + K) := by
        rw [inv_pow, pow_add]; ring

private lemma real_log_pow_le_rpow (r : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ r ≤ ((4 * ((r : ℝ) + 1)) ^ r) * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hε : 0 < (1 : ℝ) / (4 * ((r : ℝ) + 1)) := by positivity
  have hlog_le : Real.log x ≤ (4 * ((r : ℝ) + 1)) * x ^ ((1 : ℝ) / (4 * ((r : ℝ) + 1))) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / (4 * ((r : ℝ) + 1))))
    rw [Real.log_rpow hx0] at h1
    have h2 : (1 : ℝ) / (4 * ((r : ℝ) + 1)) * Real.log x ≤
        x ^ ((1 : ℝ) / (4 * ((r : ℝ) + 1))) := by linarith
    calc Real.log x = (4 * ((r : ℝ) + 1)) * ((1 : ℝ) / (4 * ((r : ℝ) + 1)) * Real.log x) := by
          field_simp
      _ ≤ (4 * ((r : ℝ) + 1)) * x ^ ((1 : ℝ) / (4 * ((r : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hpow := pow_le_pow_left₀ (Real.log_nonneg hx) hlog_le r
  rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / (4 * ((r : ℝ) + 1)))) r, ← Real.rpow_mul hx0.le] at hpow
  refine hpow.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) (by positivity))
  calc (1 : ℝ) / (4 * ((r : ℝ) + 1)) * (r : ℝ) = (r : ℝ) / (4 * ((r : ℝ) + 1)) := by ring
    _ ≤ ((r : ℝ) + 1) / (4 * ((r : ℝ) + 1)) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / 4 := by field_simp

private lemma zeta_two_sub_iteratedDeriv_zero (r : ℕ) :
    iteratedDeriv r (fun ξ : ℂ => riemannZeta (2 - ξ)) 0 =
      ∑' k : ℕ, (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r := by
  let U : Set ℂ := Metric.ball (0 : ℂ) (1 / 2)
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_conn : IsPreconnected U := (convex_ball (0 : ℂ) (1 / 2)).isPreconnected
  let g : ℕ → ℕ → ℂ → ℂ := fun m k ξ =>
    (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ m *
      Complex.exp ((Real.log (k + 1) : ℂ) * ξ)
  have h_summ : ∀ m : ℕ, Summable fun k : ℕ =>
      (4 * ((m : ℝ) + 1)) ^ m * ((k + 1 : ℝ) ^ (-5 / 4 : ℝ)) := fun m => by
    have hs : Summable fun k : ℕ => ((k + 1 : ℝ) ^ (-5 / 4 : ℝ)) := by
      have h1 := (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4)).comp_injective
        (show Function.Injective (fun k : ℕ => k + 1) from fun _ _ h => Nat.add_right_cancel h)
      refine h1.congr fun k => ?_
      simp only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one]
      rw [show (-5 / 4 : ℝ) = -(5 / 4) by norm_num, Real.rpow_neg (by positivity), inv_eq_one_div]
    exact hs.mul_left _
  have h_deriv : ∀ (m k : ℕ) (ξ : ℂ), ξ ∈ U → HasDerivAt (g m k) (g (m + 1) k ξ) ξ := by
    intro m k ξ _
    have hd : HasDerivAt (fun w : ℂ => Complex.exp ((Real.log (k + 1) : ℂ) * w))
        ((Real.log (k + 1) : ℂ) * Complex.exp ((Real.log (k + 1) : ℂ) * ξ)) ξ := by
      simpa [mul_comm] using ((hasDerivAt_id ξ).const_mul (Real.log (k + 1) : ℂ)).cexp
    refine (hd.const_mul ((((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ m)).congr_deriv ?_
    dsimp only [g]
    rw [pow_succ']
    ring
  have h_bound : ∀ (m k : ℕ) (ξ : ℂ), ξ ∈ U →
      ‖g (m + 1) k ξ‖ ≤ (4 * (((m + 1 : ℕ) : ℝ) + 1)) ^ (m + 1) * ((k + 1 : ℝ) ^ (-5 / 4 : ℝ)) := by
    intro m k ξ hξ
    have hk1 : (1 : ℝ) ≤ k + 1 := by linarith [show (0 : ℝ) ≤ k by positivity]
    have hk_pos : (0 : ℝ) < k + 1 := by positivity
    have hξ_re : ξ.re ≤ 1 / 2 := by
      have hn : ‖ξ‖ < 1 / 2 := by simpa [U, Metric.mem_ball, dist_zero_right] using hξ
      exact (Complex.re_le_norm ξ).trans hn.le
    dsimp only [g]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hk_pos _), norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hk1), Complex.norm_exp]
    have hexp_norm : Real.exp ((Real.log (k + 1) : ℂ) * ξ).re ≤ (k + 1 : ℝ) ^ (1 / 2 : ℝ) := by
      have hre : ((Real.log (k + 1) : ℂ) * ξ).re = Real.log (k + 1) * ξ.re := by
        simp [Complex.mul_re]
      rw [hre, ← Real.rpow_def_of_pos hk_pos]
      exact Real.rpow_le_rpow_of_exponent_le hk1 hξ_re
    have hlog_bd := real_log_pow_le_rpow (m + 1) hk1
    calc (k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ (m + 1) *
          Real.exp ((Real.log (k + 1) : ℂ) * ξ).re
        ≤ (k + 1 : ℝ) ^ (-2 : ℝ) *
            (((4 * (((m + 1 : ℕ) : ℝ) + 1)) ^ (m + 1)) * (k + 1 : ℝ) ^ (1 / 4 : ℝ)) *
            (k + 1 : ℝ) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = (4 * (((m + 1 : ℕ) : ℝ) + 1)) ^ (m + 1) *
            ((k + 1 : ℝ) ^ (-2 : ℝ) * (k + 1 : ℝ) ^ (1 / 4 : ℝ) * (k + 1 : ℝ) ^ (1 / 2 : ℝ)) := by
          ring
      _ = (4 * (((m + 1 : ℕ) : ℝ) + 1)) ^ (m + 1) * ((k + 1 : ℝ) ^ (-5 / 4 : ℝ)) := by
          rw [← Real.rpow_add hk_pos, ← Real.rpow_add hk_pos]
          congr 2; norm_num
  have h_summ_g : ∀ (m : ℕ) (ξ : ℂ), ξ ∈ U → Summable fun k : ℕ => g m k ξ := by
    intro m ξ hξ
    refine Summable.of_norm_bounded (h_summ m) fun k => ?_
    have hk1 : (1 : ℝ) ≤ k + 1 := by linarith [show (0 : ℝ) ≤ k by positivity]
    have hk_pos : (0 : ℝ) < k + 1 := by positivity
    have hξ_re : ξ.re ≤ 1 / 2 := by
      have hn : ‖ξ‖ < 1 / 2 := by simpa [U, Metric.mem_ball, dist_zero_right] using hξ
      exact (Complex.re_le_norm ξ).trans hn.le
    dsimp only [g]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hk_pos _), norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hk1), Complex.norm_exp]
    have hexp_norm : Real.exp ((Real.log (k + 1) : ℂ) * ξ).re ≤ (k + 1 : ℝ) ^ (1 / 2 : ℝ) := by
      have hre : ((Real.log (k + 1) : ℂ) * ξ).re = Real.log (k + 1) * ξ.re := by
        simp [Complex.mul_re]
      rw [hre, ← Real.rpow_def_of_pos hk_pos]
      exact Real.rpow_le_rpow_of_exponent_le hk1 hξ_re
    have hlog_bd := real_log_pow_le_rpow m hk1
    calc (k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ m * Real.exp ((Real.log (k + 1) : ℂ) * ξ).re
        ≤ (k + 1 : ℝ) ^ (-2 : ℝ) *
            (((4 * ((m : ℝ) + 1)) ^ m) * (k + 1 : ℝ) ^ (1 / 4 : ℝ)) *
            (k + 1 : ℝ) ^ (1 / 2 : ℝ) := by gcongr
      _ = (4 * ((m : ℝ) + 1)) ^ m *
            ((k + 1 : ℝ) ^ (-2 : ℝ) * (k + 1 : ℝ) ^ (1 / 4 : ℝ) * (k + 1 : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = (4 * ((m : ℝ) + 1)) ^ m * ((k + 1 : ℝ) ^ (-5 / 4 : ℝ)) := by
          rw [← Real.rpow_add hk_pos, ← Real.rpow_add hk_pos]
          congr 2; norm_num
  have hzeta_eq : ∀ ξ ∈ U, riemannZeta (2 - ξ) = ∑' k : ℕ, g 0 k ξ := by
    intro ξ hξ
    have hξ_norm : ‖ξ‖ < 1 / 2 := by simpa [U, Metric.mem_ball, dist_zero_right] using hξ
    have h2ξ : 1 < (2 - ξ).re := by
      simp only [Complex.sub_re, Complex.re_ofNat]
      linarith [Complex.re_le_norm ξ]
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow h2ξ]
    refine tsum_congr fun k => ?_
    have hk_pos : (0 : ℝ) < k + 1 := by positivity
    have hkc : ((k + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk_pos.ne'
    dsimp only [g]
    rw [pow_zero, mul_one, show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; rfl,
      one_div, ← Complex.cpow_neg]
    rw [Complex.cpow_def_of_ne_zero hkc, ← Complex.ofReal_log hk_pos.le,
      show -(2 - ξ) = (-2 : ℝ) + ξ by push_cast; ring, mul_add, Complex.exp_add,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Real.rpow_def_of_pos hk_pos]
  have h_iter : ∀ (m : ℕ) (ξ : ℂ), ξ ∈ U →
      iteratedDeriv m (fun w : ℂ => riemannZeta (2 - w)) ξ = ∑' k : ℕ, g m k ξ := by
    intro m
    induction m with
    | zero => intro ξ hξ; simpa using hzeta_eq ξ hξ
    | succ m ih =>
      intro ξ hξ
      have hev : iteratedDeriv m (fun w : ℂ => riemannZeta (2 - w)) =ᶠ[𝓝 ξ]
          fun w => ∑' k : ℕ, g m k w := by
        filter_upwards [hU_open.mem_nhds hξ] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hasDerivAt_tsum_of_isPreconnected (h_summ (m + 1)) hU_open hU_conn
        (h_deriv m) (h_bound m) hξ (h_summ_g m ξ hξ) hξ).deriv
  have h0 := h_iter r 0 (Metric.mem_ball_self (by norm_num))
  simpa [g] using h0

private lemma d_u_iter_formalSeries {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0) (j : ℕ) :
    d_u^[j] (formalSeries φ) = formalSeries (fun ξ : ℂ => (-ξ) ^ j * φ ξ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    have h_an : AnalyticAt ℂ (fun ξ : ℂ => (-ξ) ^ j * φ ξ) 0 :=
      (analyticAt_id.neg.pow j).mul hφ
    have hjet := Minor.toSeries_jet (a := ⟨0, fun ξ => (-ξ) ^ j * φ ξ⟩) h_an
    have hser1 : (Minor.mk 0 (fun ξ => (-ξ) ^ j * φ ξ)).toSeries =
        formalSeries (fun ξ => (-ξ) ^ j * φ ξ) := by
      ext n; cases n <;> simp [Minor.toSeries, formalSeries]
    have hser2 : (Minor.mk 0 (fun ξ => (-ξ) ^ j * φ ξ)).jet.toSeries =
        formalSeries (fun ξ => (-ξ) ^ (j + 1) * φ ξ) := by
      ext n
      cases n with
      | zero => simp [Minor.jet, Minor.toSeries, formalSeries]
      | succ k =>
        simp only [Minor.jet, Minor.toSeries, formalSeries, PowerSeries.coeff_mk]
        congr 1; funext ξ; rw [pow_succ']; ring
    rw [hser1, hser2] at hjet
    exact hjet.symm

private lemma formalSeries_mul_exp_coeff_eq (ψ φ : ℂ → ℂ) (hψ : AnalyticAt ℂ ψ 0)
    (hφ : AnalyticAt ℂ φ 0) (j M : ℕ) (u : ℝ) :
    ∑ s ∈ Finset.range (M - 1),
      PowerSeries.coeff (s + 1) (d_u^[j] (formalSeries ψ)) *
        ∑ r ∈ Finset.range (M - 1 - s),
          (Nat.choose (s + r) r : ℂ) * iteratedDeriv r φ 0 * (u : ℂ)⁻¹ ^ (s + 1 + r) =
      ∑ m ∈ Finset.range M,
        PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m := by
  cases M with
  | zero => simp
  | succ m =>
    rw [Nat.succ_sub_one, Finset.sum_range_succ' _ m]
    have hφψ : AnalyticAt ℂ (fun ξ : ℂ => φ ξ * ψ ξ) 0 := hφ.mul hψ
    have h0 : PowerSeries.coeff 0 (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) = 0 := by
      rw [d_u_iter_formalSeries hφψ j]
      simp [formalSeries]
    rw [h0, zero_mul, add_zero]
    let term (s r : ℕ) : ℂ :=
      (Nat.choose (s + r) r : ℂ) * iteratedDeriv r φ 0 *
        PowerSeries.coeff (s + 1) (d_u^[j] (formalSeries ψ)) * (u : ℂ)⁻¹ ^ (s + 1 + r)
    have hL : (∑ s ∈ Finset.range m,
        PowerSeries.coeff (s + 1) (d_u^[j] (formalSeries ψ)) *
          ∑ r ∈ Finset.range (m - s),
            (Nat.choose (s + r) r : ℂ) * iteratedDeriv r φ 0 * (u : ℂ)⁻¹ ^ (s + 1 + r)) =
        ∑ s ∈ Finset.range m, ∑ r ∈ Finset.range (m - s), term s r := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by dsimp [term]; ring
    have hR : (∑ n ∈ Finset.range m,
        PowerSeries.coeff (n + 1) (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ (n + 1)) =
        ∑ n ∈ Finset.range m, ∑ s ∈ Finset.range (n + 1), term s (n - s) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [d_u_iter_formalSeries hφψ j]
      have hψ_d := d_u_iter_formalSeries hψ j
      simp only [formalSeries, PowerSeries.coeff_mk]
      have hfn : (fun ξ : ℂ => (-ξ) ^ j * (φ ξ * ψ ξ)) =
          fun ξ => φ ξ * ((-ξ) ^ j * ψ ξ) := by funext ξ; ring
      have hjψ : AnalyticAt ℂ (fun ξ : ℂ => (-ξ) ^ j * ψ ξ) 0 :=
        (analyticAt_id.neg.pow j).mul hψ
      rw [hfn, iteratedDeriv_fun_mul (hφ.contDiffAt.of_le le_top)
        (hjψ.contDiffAt.of_le le_top), Finset.sum_mul]
      have hreflect := Finset.sum_range_reflect (fun s => term s (n - s)) (n + 1)
      rw [← hreflect]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_range] at hr
      have hrn : r ≤ n := Nat.lt_succ_iff.mp hr
      have hs_eq : n + 1 - 1 - r = n - r := by omega
      have hsub : n - (n - r) = r := by omega
      have hch : Nat.choose ((n - r) + r) r = Nat.choose n r := by
        rw [Nat.sub_add_cancel hrn]
      dsimp only [term]
      rw [hψ_d]
      simp only [formalSeries, PowerSeries.coeff_mk]
      rw [hs_eq, hsub, hch, show n - r + 1 + r = n + 1 by omega]
    have hL' : ∑ s ∈ Finset.range m, ∑ r ∈ Finset.range (m - s), term s r =
        ∑ x ∈ (Finset.range m).sigma fun s => Finset.range (m - s), term x.1 x.2 :=
      Finset.sum_sigma' (Finset.range m) (fun s => Finset.range (m - s)) term
    have hR' : ∑ n ∈ Finset.range m, ∑ s ∈ Finset.range (n + 1), term s (n - s) =
        ∑ y ∈ (Finset.range m).sigma fun n => Finset.range (n + 1), term y.2 (y.1 - y.2) :=
      Finset.sum_sigma' (Finset.range m) (fun n => Finset.range (n + 1))
        (fun n s => term s (n - s))
    rw [hL, hR, hL', hR']
    refine Finset.sum_bij (fun x _ => ⟨x.1 + x.2, x.1⟩) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
      exact ⟨by omega, by omega⟩
    · intro x₁ hx₁ x₂ hx₂ heq
      have hfst : x₁.1 + x₁.2 = x₂.1 + x₂.2 := congrArg Sigma.fst heq
      have hsnd : x₁.1 = x₂.1 := by
        have := Sigma.ext_iff.mp heq
        exact eq_of_heq this.2
      exact Sigma.ext hsnd (heq_of_eq (by omega))
    · intro y hy
      simp only [Finset.mem_sigma, Finset.mem_range] at hy
      refine ⟨⟨y.2, y.1 - y.2⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]
        exact ⟨by omega, by omega⟩
      · exact Sigma.ext (by dsimp only; exact Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hy.2)) (heq_of_eq rfl)
    · intro x _
      dsimp only
      rw [Nat.add_sub_cancel_left]

private lemma iteratedDeriv_sub_const_eq (g : ℝ → ℂ)
    (hg : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k g)) (a : ℝ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun t : ℝ => g (t - a)) u = iteratedDeriv j g (u - a) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    have heq : iteratedDeriv j (fun t : ℝ => g (t - a)) = fun t => iteratedDeriv j g (t - a) :=
      funext ih
    rw [iteratedDeriv_succ, heq]
    have hd1 : HasDerivAt (fun t : ℝ => t - a) 1 u := (hasDerivAt_id u).sub_const a
    have hd2 : HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g (u - a)) (u - a) := by
      rw [iteratedDeriv_succ]
      exact (hg j (u - a)).hasDerivAt
    simpa [Function.comp_def, one_smul] using (hd2.scomp u hd1).deriv

lemma hasAsympExp_shift {g : ℝ → ℂ} {ψ : ℂ → ℂ} (a : ℝ)
    (hψ : AnalyticAt ℂ ψ 0)
    (hg_diff : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k g))
    (hg : ∀ j : ℕ, HasAsympExp (iteratedDeriv j g) (d_u^[j] (formalSeries ψ)))
    (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun u => g (u - a)))
      (d_u^[j] (formalSeries (fun ξ : ℂ => Complex.exp ((a : ℂ) * ξ) * ψ ξ))) := by
  let S := d_u^[j] (formalSeries ψ)
  have hS0 : PowerSeries.coeff 0 S = 0 := by
    rw [show S = d_u^[j] (formalSeries ψ) from rfl, d_u_iter_formalSeries hψ j]
    simp [formalSeries]
  intro M
  obtain ⟨Cg, hCg⟩ := hg j M
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hCg
  choose Cs hCs_nonneg hCs_bd using fun s => inv_sub_pow_u_bound s (M - 1 - s)
  let C_approx : ℝ :=
    ∑ s ∈ Finset.range (M - 1), ‖PowerSeries.coeff (s + 1) S‖ * (Cs s * |a| ^ (M - 1 - s))
  let C_tot : ℝ := max Cg 0 * (2 ^ M) + C_approx
  refine ⟨C_tot, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max (U₀ + |a|) (2 * |a|)) 1)] with u hu
  have hu1 : 1 ≤ u := (le_max_right _ _).trans hu
  have hu_pos : 0 < u := by linarith
  have hau : 2 * |a| ≤ u := (le_max_right _ _).trans ((le_max_left _ _).trans hu)
  have hv_ge : U₀ ≤ u - a := by
    have h1 : U₀ + |a| ≤ u := (le_max_left _ _).trans ((le_max_left _ _).trans hu)
    linarith [le_abs_self a]
  have hv_half : u / 2 ≤ u - a := by linarith [le_abs_self a]
  have hv_pos : 0 < u - a := by linarith
  have h_g := hU₀ (u - a) hv_ge
  have h_sum_split : ∑ m ∈ Finset.range M, PowerSeries.coeff m S * ((u - a : ℝ) : ℂ)⁻¹ ^ m =
      ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S * ((u - a : ℝ) : ℂ)⁻¹ ^ (s + 1) := by
    cases M with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ', hS0, zero_mul, add_zero, Nat.succ_sub_one]
  rw [iteratedDeriv_sub_const_eq g hg_diff a j u]
  let φ : ℂ → ℂ := fun ξ => Complex.exp ((a : ℂ) * ξ)
  have hφ_an : AnalyticAt ℂ φ 0 := (analyticAt_const.mul analyticAt_id).cexp
  have hφ_deriv : ∀ r : ℕ, iteratedDeriv r φ 0 = (a : ℂ) ^ r := fun r => by
    have hall : ∀ m : ℕ, ∀ ξ : ℂ, iteratedDeriv m φ ξ = (a : ℂ) ^ m * φ ξ := fun m => by
      induction m with
      | zero => intro ξ; simp [φ]
      | succ m ihm =>
        intro ξ
        have heq : iteratedDeriv m φ = fun w => (a : ℂ) ^ m * φ w := funext ihm
        rw [iteratedDeriv_succ, heq]
        have hd : HasDerivAt φ ((a : ℂ) * φ ξ) ξ := by
          simpa [φ, mul_comm] using (((hasDerivAt_id ξ).const_mul (a : ℂ)).cexp)
        have hmul : HasDerivAt (fun w : ℂ => (a : ℂ) ^ m * φ w) ((a : ℂ) ^ (m + 1) * φ ξ) ξ := by
          convert hd.const_mul ((a : ℂ) ^ m) using 1
          rw [pow_succ']; ring
        exact hmul.deriv
    simp [φ, hall r 0]
  have h_coeff_eq := formalSeries_mul_exp_coeff_eq ψ φ hψ hφ_an j M u
  simp_rw [hφ_deriv] at h_coeff_eq
  rw [← h_coeff_eq]
  have h_mid : ‖(∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S * ((u - a : ℝ) : ℂ)⁻¹ ^ (s + 1)) -
      ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S *
        ∑ r ∈ Finset.range (M - 1 - s),
          (Nat.choose (s + r) r : ℂ) * (a : ℂ) ^ r * (u : ℂ)⁻¹ ^ (s + 1 + r)‖ ≤ C_approx / u ^ M := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    dsimp only [C_approx]
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [← mul_sub, norm_mul]
    have hbd := hCs_bd s a u hu_pos hau
    have hM_eq : s + 1 + (M - 1 - s) = M := by
      have := Finset.mem_range.mp hs; omega
    rw [hM_eq] at hbd
    have hcast : ((u - a : ℝ) : ℂ) = (u : ℂ) - (a : ℂ) := by push_cast; ring
    rw [hcast]
    calc ‖PowerSeries.coeff (s + 1) S‖ *
          ‖((u : ℂ) - (a : ℂ))⁻¹ ^ (s + 1) -
            ∑ r ∈ Finset.range (M - 1 - s),
              (Nat.choose (s + r) r : ℂ) * (a : ℂ) ^ r * (u : ℂ)⁻¹ ^ (s + 1 + r)‖
        ≤ ‖PowerSeries.coeff (s + 1) S‖ * (Cs s * |a| ^ (M - 1 - s) / u ^ M) :=
          mul_le_mul_of_nonneg_left hbd (norm_nonneg _)
      _ = ‖PowerSeries.coeff (s + 1) S‖ * (Cs s * |a| ^ (M - 1 - s)) / u ^ M := by ring
  have h_g' : ‖iteratedDeriv j g (u - a) -
      ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S * ((u - a : ℝ) : ℂ)⁻¹ ^ (s + 1)‖ ≤
      max Cg 0 * 2 ^ M / u ^ M := by
    rw [← h_sum_split]
    calc ‖iteratedDeriv j g (u - a) - ∑ m ∈ Finset.range M, PowerSeries.coeff m S * ((u - a : ℝ) : ℂ)⁻¹ ^ m‖
        ≤ Cg / (u - a) ^ M := h_g
      _ ≤ max Cg 0 / (u - a) ^ M := div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Cg 0 / (u / 2) ^ M :=
          div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
            (pow_le_pow_left₀ (by positivity) hv_half M)
      _ = max Cg 0 * 2 ^ M / u ^ M := by rw [div_pow]; field_simp [hu_pos.ne']
  calc ‖iteratedDeriv j g (u - a) - _‖
      ≤ ‖iteratedDeriv j g (u - a) -
          ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S * ((u - a : ℝ) : ℂ)⁻¹ ^ (s + 1)‖ +
        ‖(∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S * ((u - a : ℝ) : ℂ)⁻¹ ^ (s + 1)) - _‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ max Cg 0 * 2 ^ M / u ^ M + C_approx / u ^ M := add_le_add h_g' h_mid
    _ = C_tot / u ^ M := by dsimp [C_tot]; ring

/-- **Link 3 for Partitions into Primes**:
Assuming `PNTAllOrders`, `fPart(u) = e^{-2u} G_P(e^{-e^{-u}})` and all its derivatives match
`d_u^[j] (formalSeries phiPartClean)` to all polynomial orders `1/u^M`. -/
theorem fPart_hasAsympExp (hpnt : PNTAllOrders) (j : ℕ) :
    HasAsympExp (iteratedDeriv j fPart) (d_u^[j] (formalSeries phiPartClean)) := by
  let ψ : ℂ → ℂ := fun ξ => Complex.Gamma (2 - ξ)
  let φ : ℂ → ℂ := fun ξ => riemannZeta (2 - ξ)
  have hψ_an : AnalyticAt ℂ ψ 0 := by
    let U : Set ℂ := {w : ℂ | w.re < 2}
    have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
    have hdiff : DifferentiableOn ℂ ψ U := fun w hw => by
      change w.re < 2 at hw
      refine ((Complex.differentiableAt_Gamma _ fun m hm => ?_).comp w
        ((hasDerivAt_id w).const_sub (2 : ℂ)).differentiableAt).differentiableWithinAt
      have hre := congrArg Complex.re hm
      simp only [Complex.sub_re, Complex.re_ofNat, Complex.neg_re, Complex.natCast_re, id_eq] at hre
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (hdiff.analyticOnNhd hU) 0 (by simp [U])
  have hφ_an : AnalyticAt ℂ φ 0 := by
    let U : Set ℂ := {w : ℂ | w ≠ 1}
    have hdiff : DifferentiableOn ℂ φ U := fun w hw => by
      change w ≠ 1 at hw
      refine ((differentiableAt_riemannZeta ?_).comp w
        ((hasDerivAt_id w).const_sub (2 : ℂ)).differentiableAt).differentiableWithinAt
      intro h0
      change (2 : ℂ) - w = 1 at h0
      exact hw (by linear_combination -h0)
    exact (hdiff.analyticOnNhd isOpen_ne) 0 (by norm_num [U])
  have hphi_eq : formalSeries phiPartClean = formalSeries (fun ξ : ℂ => φ ξ * ψ ξ) := by
    rw [formalSeries_phiPartClean_eq]; rfl
  rw [hphi_eq]
  let S := d_u^[j] (formalSeries ψ)
  have hS0 : PowerSeries.coeff 0 S = 0 := by
    rw [show S = d_u^[j] (formalSeries ψ) from rfl, d_u_iter_formalSeries hψ_an j]
    simp [formalSeries]
  have hZ32_summ : Summable fun k : ℕ => (k + 1 : ℝ) ^ (-3 / 2 : ℝ) := by
    have h1 := (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)).comp_injective
      (show Function.Injective (fun k : ℕ => k + 1) from fun _ _ h => Nat.add_right_cancel h)
    refine h1.congr fun k => ?_
    simp only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one]
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.rpow_neg (by positivity), inv_eq_one_div]
  let Z32 : ℝ := ∑' k : ℕ, (k + 1 : ℝ) ^ (-3 / 2 : ℝ)
  have hZ32_nonneg : 0 ≤ Z32 := tsum_nonneg fun _ => by positivity
  have hlog_summ : ∀ r : ℕ, Summable fun k : ℕ => (k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ r := by
    intro r
    refine (hZ32_summ.mul_left ((4 * ((r : ℝ) + 1)) ^ r)).of_nonneg_of_le
      (fun k => mul_nonneg (by positivity) (pow_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k by positivity])) r))
      fun k => ?_
    have hk1 : (1 : ℝ) ≤ k + 1 := by linarith [show (0 : ℝ) ≤ k by positivity]
    have hk_pos : (0 : ℝ) < k + 1 := by positivity
    calc (k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ r
        ≤ (k + 1 : ℝ) ^ (-2 : ℝ) * (((4 * ((r : ℝ) + 1)) ^ r) * (k + 1 : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (real_log_pow_le_rpow r hk1) (by positivity)
      _ = (4 * ((r : ℝ) + 1)) ^ r * ((k + 1 : ℝ) ^ (-2 : ℝ) * (k + 1 : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ ≤ (4 * ((r : ℝ) + 1)) ^ r * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Real.rpow_add hk_pos]
          exact Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  intro M
  obtain ⟨Ch, hCh⟩ := hI_hasAsympExp hpnt j M
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hCh
  obtain ⟨B, hB_nonneg, hB_bd⟩ := hI_uniform_bound j
  choose Cs hCs_nonneg hCs_bd using fun s => inv_sub_pow_u_bound s (M - 1 - s)
  let Z₂ : ℝ := ∑' k : ℕ, ((k + 1 : ℝ) ^ 2)⁻¹
  have hZ₂_summ : Summable fun k : ℕ => ((k + 1 : ℝ) ^ 2)⁻¹ := by
    have h1 := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (show Function.Injective (fun k : ℕ => k + 1) from fun _ _ h => Nat.add_right_cancel h)
    refine h1.congr fun k => by simp
  have hZ₂_nonneg : 0 ≤ Z₂ := tsum_nonneg fun _ => by positivity
  let C_head : ℝ := max Ch 0 * ((4 / 3 : ℝ) ^ M) * Z₂
  let C_tail : ℝ := B * Z32 * ((M.factorial : ℝ) / (1 / 8 : ℝ) ^ M)
  let C_binom : ℝ := ∑ s ∈ Finset.range (M - 1), ‖PowerSeries.coeff (s + 1) S‖ *
    (Cs s * ∑' k : ℕ, (k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ (M - 1 - s))
  let C_trunc : ℝ := ∑ s ∈ Finset.range (M - 1), ‖PowerSeries.coeff (s + 1) S‖ *
    ∑ r ∈ Finset.range (M - 1 - s), (Nat.choose (s + r) r : ℝ) *
      ((4 * ((r : ℝ) + 1)) ^ r * Z32 * ((M.factorial : ℝ) / (1 / 16 : ℝ) ^ M))
  refine ⟨C_head + C_tail + C_binom + C_trunc, ?_⟩
  let U₁ : ℝ := max (max (4 * U₀) 4) 1
  filter_upwards [eventually_ge_atTop U₁] with u hu
  have hu4 : 4 ≤ u := (le_max_right _ _).trans ((le_max_left _ _).trans hu)
  have hu1 : 1 ≤ u := (le_max_right _ _).trans hu
  have hu_pos : 0 < u := by linarith
  have huU₀ : 4 * U₀ ≤ u := (le_max_left _ _).trans ((le_max_left _ _).trans hu)
  let K : ℕ := Nat.floor (Real.exp (u / 4))
  have hK_le : (K : ℝ) ≤ Real.exp (u / 4) := Nat.floor_le (Real.exp_pos _).le
  have h_main_summ : Summable fun k : ℕ =>
      ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1)) := by
    refine Summable.of_norm_bounded (hZ₂_summ.mul_left B) fun k => ?_
    rw [norm_mul, norm_inv, norm_pow, show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < k + 1), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB_bd _) (by positivity)
  have h_split_fPart : iteratedDeriv j fPart u =
      (∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) +
        ∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1)) := by
    rw [iteratedDeriv_fPart_eq_tsum j u, ← h_main_summ.sum_add_tsum_nat_add K]
    congr 1
    refine tsum_congr fun k => ?_
    push_cast; ring_nf
  have h_tail_bd : ‖∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))‖ ≤
      C_tail / u ^ M := by
    have hs_tail : Summable fun k : ℕ => ‖((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))‖ :=
      (h_main_summ.norm.comp_injective (show Function.Injective (fun k : ℕ => k + K) from
        fun _ _ h => Nat.add_right_cancel h)).congr fun k => by simp
    have h_dom_summ : Summable fun k : ℕ => (B * Real.exp (-u / 8)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) :=
      hZ32_summ.mul_left _
    have h_k_bd : ∀ k : ℕ, ‖((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))‖ ≤
        (B * Real.exp (-u / 8)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) := fun k => by
      rw [norm_mul, norm_inv, norm_pow, show ((k : ℂ) + (K : ℂ) + 1) = ((k + K + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < k + K + 1)]
      have hexp_lt : Real.exp (u / 4) < (k + K + 1 : ℝ) := by
        have h1 : Real.exp (u / 4) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith [show (0 : ℝ) ≤ k by positivity]
      have hk1 : (1 : ℝ) ≤ k + K + 1 := by linarith [show (0 : ℝ) ≤ k by positivity, show (0 : ℝ) ≤ K by positivity]
      have hpow_neg : (k + K + 1 : ℝ) ^ (-1 / 2 : ℝ) ≤ Real.exp (-u / 8) := by
        have h1 : (k + K + 1 : ℝ) ^ (-1 / 2 : ℝ) ≤ (Real.exp (u / 4)) ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hexp_lt.le (by norm_num)
        refine h1.trans_eq ?_
        rw [← Real.exp_mul]; congr 1; ring
      have hpow_32 : (k + K + 1 : ℝ) ^ (-3 / 2 : ℝ) ≤ (k + 1 : ℝ) ^ (-3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [show (0 : ℝ) ≤ K by positivity]) (by norm_num)
      have h_inv_sq : ((k + K + 1 : ℝ) ^ 2)⁻¹ =
          (k + K + 1 : ℝ) ^ (-1 / 2 : ℝ) * (k + K + 1 : ℝ) ^ (-3 / 2 : ℝ) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < k + K + 1), show (-1 / 2 : ℝ) + (-3 / 2) = -2 by norm_num,
          Real.rpow_neg (by positivity)]; norm_num
      calc ((k + K + 1 : ℝ) ^ 2)⁻¹ * ‖iteratedDeriv j hI (u - Real.log (k + K + 1))‖
          ≤ ((k + K + 1 : ℝ) ^ 2)⁻¹ * B := mul_le_mul_of_nonneg_left (hB_bd _) (by positivity)
        _ = B * ((k + K + 1 : ℝ) ^ (-1 / 2 : ℝ) * (k + K + 1 : ℝ) ^ (-3 / 2 : ℝ)) := by
            rw [h_inv_sq, mul_comm]
        _ ≤ B * (Real.exp (-u / 8) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hpow_neg hpow_32 (by positivity) (Real.exp_pos _).le) hB_nonneg
        _ = (B * Real.exp (-u / 8)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) := by ring
    calc ‖∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))‖
        ≤ ∑' k : ℕ, ‖((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))‖ :=
          norm_tsum_le_tsum_norm hs_tail
      _ ≤ ∑' k : ℕ, (B * Real.exp (-u / 8)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) :=
          hs_tail.tsum_le_tsum h_k_bd h_dom_summ
      _ = B * Z32 * Real.exp (-(1 / 8 : ℝ) * u) := by
          rw [tsum_mul_left]; dsimp [Z32]
          rw [mul_assoc B, mul_comm (Real.exp (-u / 8)) _, ← mul_assoc]
          congr 2; ring
      _ ≤ B * Z32 * (((M.factorial : ℝ) / (1 / 8 : ℝ) ^ M) / u ^ M) :=
          mul_le_mul_of_nonneg_left (exp_neg_mul_le_inv_pow (1 / 8) (by norm_num) M hu_pos)
            (mul_nonneg hB_nonneg hZ32_nonneg)
      _ = C_tail / u ^ M := by dsimp [C_tail]; ring
  have hk_range_good : ∀ k ∈ Finset.range K,
      0 ≤ Real.log (k + 1) ∧ Real.log (k + 1) ≤ u / 4 ∧
        U₀ ≤ u - Real.log (k + 1) ∧ (3 / 4 : ℝ) * u ≤ u - Real.log (k + 1) := by
    intro k hk
    have hk_lt : k < K := Finset.mem_range.mp hk
    have hk1_le : (k + 1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk_lt
    have hk_exp : (k + 1 : ℝ) ≤ Real.exp (u / 4) := hk1_le.trans hK_le
    have hlog_ge : 0 ≤ Real.log (k + 1) := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k by positivity])
    have hlog_le : Real.log (k + 1) ≤ u / 4 := by
      calc Real.log (k + 1) ≤ Real.log (Real.exp (u / 4)) := Real.log_le_log (by positivity) hk_exp
        _ = u / 4 := Real.log_exp _
    refine ⟨hlog_ge, hlog_le, ?_, ?_⟩
    · have h34 : (3 / 4 : ℝ) * u ≤ u - Real.log (k + 1) := by linarith
      have huU : U₀ ≤ (3 / 4 : ℝ) * u := by
        by_cases hU0 : 0 ≤ U₀
        · linarith
        · linarith [hu_pos]
      exact huU.trans h34
    · linarith
  let head_ser : ℂ := ∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ *
    ∑ m ∈ Finset.range M, PowerSeries.coeff m S * ((u - Real.log (k + 1) : ℝ) : ℂ)⁻¹ ^ m
  have h_head_bd : ‖(∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) -
      head_ser‖ ≤ C_head / u ^ M := by
    dsimp only [head_ser]
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have h_term_bd : ∀ k ∈ Finset.range K,
        ‖((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1)) -
          ((k + 1 : ℂ) ^ 2)⁻¹ *
            ∑ m ∈ Finset.range M, PowerSeries.coeff m S * ((u - Real.log (k + 1) : ℝ) : ℂ)⁻¹ ^ m‖ ≤
        (max Ch 0 * (4 / 3 : ℝ) ^ M / u ^ M) * ((k + 1 : ℝ) ^ 2)⁻¹ := by
      intro k hk
      obtain ⟨_, _, hvU, hv34⟩ := hk_range_good k hk
      have hv_pos : 0 < u - Real.log (k + 1) := by linarith
      rw [← mul_sub, norm_mul, norm_inv, norm_pow,
        show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < k + 1)]
      have h1 := hU₀ (u - Real.log (k + 1)) hvU
      have h2 : Ch / (u - Real.log (k + 1)) ^ M ≤ max Ch 0 * (4 / 3 : ℝ) ^ M / u ^ M := by
        calc Ch / (u - Real.log (k + 1)) ^ M
            ≤ max Ch 0 / (u - Real.log (k + 1)) ^ M :=
              div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max Ch 0 / ((3 / 4 : ℝ) * u) ^ M :=
              div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
                (pow_le_pow_left₀ (by positivity) hv34 M)
          _ = max Ch 0 * (4 / 3 : ℝ) ^ M / u ^ M := by
              have h43 : ((3 / 4 : ℝ) ^ M)⁻¹ = (4 / 3 : ℝ) ^ M := by rw [← inv_pow]; norm_num
              rw [mul_pow, div_eq_mul_inv, mul_inv, ← mul_assoc, h43, div_eq_mul_inv]
              ring
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
    calc ∑ k ∈ Finset.range K, _
        ≤ ∑ k ∈ Finset.range K, (max Ch 0 * (4 / 3 : ℝ) ^ M / u ^ M) * ((k + 1 : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum h_term_bd
      _ = (max Ch 0 * (4 / 3 : ℝ) ^ M / u ^ M) * ∑ k ∈ Finset.range K, ((k + 1 : ℝ) ^ 2)⁻¹ := by
          rw [← Finset.mul_sum]
      _ ≤ (max Ch 0 * (4 / 3 : ℝ) ^ M / u ^ M) * Z₂ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hZ₂_summ.sum_le_tsum (Finset.range K) fun _ _ => by positivity
      _ = C_head / u ^ M := by dsimp [C_head]; ring
  let head_poly : ℂ := ∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ *
    ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S *
      ∑ r ∈ Finset.range (M - 1 - s),
        (Nat.choose (s + r) r : ℂ) * (Real.log (k + 1) : ℂ) ^ r * (u : ℂ)⁻¹ ^ (s + 1 + r)
  have h_binom_bd : ‖head_ser - head_poly‖ ≤ C_binom / u ^ M := by
    have hser_split : head_ser = ∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ *
        ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S *
          ((u - Real.log (k + 1) : ℝ) : ℂ)⁻¹ ^ (s + 1) := by
      dsimp only [head_ser]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      cases M with
      | zero => simp
      | succ m => rw [Finset.sum_range_succ', hS0, zero_mul, add_zero, Nat.succ_sub_one]
    rw [hser_split]
    dsimp only [head_poly]
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have h_k_term : ∀ k ∈ Finset.range K,
        ‖((k + 1 : ℂ) ^ 2)⁻¹ *
            ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S * ((u - Real.log (k + 1) : ℝ) : ℂ)⁻¹ ^ (s + 1) -
          ((k + 1 : ℂ) ^ 2)⁻¹ *
            ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S *
              ∑ r ∈ Finset.range (M - 1 - s),
                (Nat.choose (s + r) r : ℂ) * (Real.log (k + 1) : ℂ) ^ r * (u : ℂ)⁻¹ ^ (s + 1 + r)‖ ≤
          ∑ s ∈ Finset.range (M - 1), ‖PowerSeries.coeff (s + 1) S‖ *
            (Cs s * ((k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ (M - 1 - s))) / u ^ M := by
      intro k hk
      obtain ⟨hlog0, hlog_le, _, _⟩ := hk_range_good k hk
      have hau : 2 * |Real.log (k + 1)| ≤ u := by
        rw [abs_of_nonneg hlog0]; linarith
      rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, norm_pow,
        show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < k + 1)]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s hs => ?_
      rw [← mul_sub, norm_mul]
      have hbd := hCs_bd s (Real.log (k + 1)) u hu_pos hau
      have hM_eq : s + 1 + (M - 1 - s) = M := by
        have := Finset.mem_range.mp hs; omega
      rw [hM_eq, abs_of_nonneg hlog0] at hbd
      have hcast : ((u - Real.log (k + 1) : ℝ) : ℂ) = (u : ℂ) - (Real.log (k + 1) : ℂ) := by
        push_cast; ring
      rw [hcast]
      have hk2_eq : ((k + 1 : ℝ) ^ 2)⁻¹ = (k + 1 : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg (by positivity)]; norm_num
      calc ((k + 1 : ℝ) ^ 2)⁻¹ * (‖PowerSeries.coeff (s + 1) S‖ * _)
          ≤ ((k + 1 : ℝ) ^ 2)⁻¹ * (‖PowerSeries.coeff (s + 1) S‖ *
              (Cs s * (Real.log (k + 1)) ^ (M - 1 - s) / u ^ M)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbd (norm_nonneg _)) (by positivity)
        _ = ‖PowerSeries.coeff (s + 1) S‖ *
              (Cs s * ((k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ (M - 1 - s))) / u ^ M := by
            rw [hk2_eq]; ring
    calc ∑ k ∈ Finset.range K, _
        ≤ ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range (M - 1),
            ‖PowerSeries.coeff (s + 1) S‖ *
              (Cs s * ((k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ (M - 1 - s))) / u ^ M :=
          Finset.sum_le_sum h_k_term
      _ = ∑ s ∈ Finset.range (M - 1), ‖PowerSeries.coeff (s + 1) S‖ *
            (Cs s * ∑ k ∈ Finset.range K, (k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ (M - 1 - s)) / u ^ M := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ s ∈ Finset.range (M - 1), ‖PowerSeries.coeff (s + 1) S‖ *
            (Cs s * ∑' k : ℕ, (k + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + 1)) ^ (M - 1 - s)) / u ^ M := by
          refine Finset.sum_le_sum fun s _ => ?_
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hCs_nonneg s)) (norm_nonneg _)
          exact (hlog_summ (M - 1 - s)).sum_le_tsum (Finset.range K) fun k _ =>
            mul_nonneg (by positivity) (pow_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k by positivity])) _)
      _ = C_binom / u ^ M := by dsimp [C_binom]; rw [Finset.sum_div]
  have h_coeff_match : ∑ m ∈ Finset.range M,
        PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m =
      ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S *
        ∑ r ∈ Finset.range (M - 1 - s),
          (Nat.choose (s + r) r : ℂ) *
            (∑' k : ℕ, (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r) *
            (u : ℂ)⁻¹ ^ (s + 1 + r) := by
    rw [← formalSeries_mul_exp_coeff_eq ψ φ hψ_an hφ_an j M u]
    refine Finset.sum_congr rfl fun s _ => congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
    rw [zeta_two_sub_iteratedDeriv_zero r]
  have h_trunc_bd : ‖head_poly - ∑ m ∈ Finset.range M,
        PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m‖ ≤
      C_trunc / u ^ M := by
    rw [h_coeff_match]
    have hpoly_swap : head_poly = ∑ s ∈ Finset.range (M - 1), PowerSeries.coeff (s + 1) S *
        ∑ r ∈ Finset.range (M - 1 - s),
          (Nat.choose (s + r) r : ℂ) *
            (∑ k ∈ Finset.range K, (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r) *
            (u : ℂ)⁻¹ ^ (s + 1 + r) := by
      have hpoly1 : head_poly = ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range (M - 1),
          PowerSeries.coeff (s + 1) S * ∑ r ∈ Finset.range (M - 1 - s),
            ((k + 1 : ℂ) ^ 2)⁻¹ * ((Nat.choose (s + r) r : ℂ) * (Real.log (k + 1) : ℂ) ^ r *
              (u : ℂ)⁻¹ ^ (s + 1 + r)) := by
        dsimp only [head_poly]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        conv_lhs => rw [← mul_assoc, Finset.mul_sum]
        conv_rhs => rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
      rw [hpoly1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk2_eq : ((k + 1 : ℂ) ^ 2)⁻¹ = (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) := by
        rw [Real.rpow_neg (by positivity), Complex.ofReal_inv]
        norm_num
      rw [hk2_eq]; ring
    rw [hpoly_swap, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    dsimp only [C_trunc]
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← mul_sub, norm_mul, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have h_tsum_c : Summable fun k : ℕ => (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r := by
      refine Summable.of_norm_bounded (hlog_summ r) fun k => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by positivity) _), norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k by positivity]))]
    have h_sub_sum : (∑ k ∈ Finset.range K, (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r) -
          (∑' k : ℕ, (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r) =
        -(∑' k : ℕ, (((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r) := by
      rw [← h_tsum_c.sum_add_tsum_nat_add K]
      have hshift : (∑' k : ℕ, (((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r) =
          ∑' k : ℕ, ((((k + K : ℕ) + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (((k + K : ℕ) + 1 : ℝ))) ^ r := by
        refine tsum_congr fun k => ?_; push_cast; ring_nf
      rw [hshift]; ring
    have h_diff_term :
        (Nat.choose (s + r) r : ℂ) * (∑ k ∈ Finset.range K, (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r) *
            (u : ℂ)⁻¹ ^ (s + 1 + r) -
          (Nat.choose (s + r) r : ℂ) * (∑' k : ℕ, (((k + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + 1) : ℂ) ^ r) *
            (u : ℂ)⁻¹ ^ (s + 1 + r) =
        -((Nat.choose (s + r) r : ℂ) * (∑' k : ℕ, (((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r) *
            (u : ℂ)⁻¹ ^ (s + 1 + r)) := by
      have := congrArg (fun z : ℂ => (Nat.choose (s + r) r : ℂ) * z * (u : ℂ)⁻¹ ^ (s + 1 + r)) h_sub_sum
      linear_combination this
    rw [h_diff_term, norm_neg, norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
    have h_tail_r_summ : Summable fun k : ℕ =>
        ‖(((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r‖ := by
      have h1 := (hlog_summ r).comp_injective (show Function.Injective (fun k : ℕ => k + K) from
        fun _ _ h => Nat.add_right_cancel h)
      refine h1.congr fun k => ?_
      dsimp only [Function.comp_def]
      push_cast
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + K + 1) _),
        norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (k : ℝ) + K by positivity]))]
    have h_r_dom_summ : Summable fun k : ℕ =>
        ((4 * ((r : ℝ) + 1)) ^ r * Real.exp (-u / 16)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) :=
      hZ32_summ.mul_left _
    have h_r_k_bd : ∀ k : ℕ,
        ‖(((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r‖ ≤
          ((4 * ((r : ℝ) + 1)) ^ r * Real.exp (-u / 16)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) := fun k => by
      have hk1 : (1 : ℝ) ≤ k + K + 1 := by linarith [show (0 : ℝ) ≤ k by positivity, show (0 : ℝ) ≤ K by positivity]
      have hk_pos : (0 : ℝ) < k + K + 1 := by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hk_pos _),
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hk1)]
      have hexp_lt : Real.exp (u / 4) < (k + K + 1 : ℝ) := by
        have h1 : Real.exp (u / 4) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith [show (0 : ℝ) ≤ k by positivity]
      have hpow_neg : (k + K + 1 : ℝ) ^ (-1 / 4 : ℝ) ≤ Real.exp (-u / 16) := by
        have h1 : (k + K + 1 : ℝ) ^ (-1 / 4 : ℝ) ≤ (Real.exp (u / 4)) ^ (-1 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hexp_lt.le (by norm_num)
        refine h1.trans_eq ?_
        rw [← Real.exp_mul]; congr 1; ring
      have hpow_32 : (k + K + 1 : ℝ) ^ (-3 / 2 : ℝ) ≤ (k + 1 : ℝ) ^ (-3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [show (0 : ℝ) ≤ K by positivity]) (by norm_num)
      calc (k + K + 1 : ℝ) ^ (-2 : ℝ) * (Real.log (k + K + 1)) ^ r
          ≤ (k + K + 1 : ℝ) ^ (-2 : ℝ) * (((4 * ((r : ℝ) + 1)) ^ r) * (k + K + 1 : ℝ) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (real_log_pow_le_rpow r hk1) (by positivity)
        _ = (4 * ((r : ℝ) + 1)) ^ r * ((k + K + 1 : ℝ) ^ (-2 : ℝ) * (k + K + 1 : ℝ) ^ (1 / 4 : ℝ)) := by ring
        _ = (4 * ((r : ℝ) + 1)) ^ r * ((k + K + 1 : ℝ) ^ (-1 / 4 : ℝ) * (k + K + 1 : ℝ) ^ (-3 / 2 : ℝ)) := by
            congr 1
            rw [← Real.rpow_add hk_pos, ← Real.rpow_add hk_pos]
            congr 1; norm_num
        _ ≤ (4 * ((r : ℝ) + 1)) ^ r * (Real.exp (-u / 16) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hpow_neg hpow_32 (by positivity) (Real.exp_pos _).le)
              (by positivity)
        _ = ((4 * ((r : ℝ) + 1)) ^ r * Real.exp (-u / 16)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) := by ring
    have h_tail_r_norm : ‖∑' k : ℕ, (((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r‖ ≤
        (4 * ((r : ℝ) + 1)) ^ r * Z32 * (((M.factorial : ℝ) / (1 / 16 : ℝ) ^ M) / u ^ M) := by
      calc ‖∑' k : ℕ, (((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r‖
          ≤ ∑' k : ℕ, ‖(((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r‖ :=
            norm_tsum_le_tsum_norm h_tail_r_summ
        _ ≤ ∑' k : ℕ, ((4 * ((r : ℝ) + 1)) ^ r * Real.exp (-u / 16)) * (k + 1 : ℝ) ^ (-3 / 2 : ℝ) :=
            h_tail_r_summ.tsum_le_tsum h_r_k_bd h_r_dom_summ
        _ = (4 * ((r : ℝ) + 1)) ^ r * Z32 * Real.exp (-(1 / 16 : ℝ) * u) := by
            rw [tsum_mul_left]; dsimp [Z32]
            rw [mul_assoc ((4 * ((r : ℝ) + 1)) ^ r), mul_comm (Real.exp (-u / 16)) _, ← mul_assoc]
            congr 2; ring
        _ ≤ (4 * ((r : ℝ) + 1)) ^ r * Z32 * (((M.factorial : ℝ) / (1 / 16 : ℝ) ^ M) / u ^ M) :=
            mul_le_mul_of_nonneg_left (exp_neg_mul_le_inv_pow (1 / 16) (by norm_num) M hu_pos)
              (mul_nonneg (by positivity) hZ32_nonneg)
    have h_uinv_le1 : (u⁻¹) ^ (s + 1 + r) ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr hu_pos.le) (inv_le_one_of_one_le₀ hu1)
    calc ‖PowerSeries.coeff (s + 1) S‖ *
          ((Nat.choose (s + r) r : ℝ) *
            ‖∑' k : ℕ, (((k + K + 1 : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (Real.log (k + K + 1) : ℂ) ^ r‖ *
            (u⁻¹) ^ (s + 1 + r))
        ≤ ‖PowerSeries.coeff (s + 1) S‖ *
            ((Nat.choose (s + r) r : ℝ) *
              ((4 * ((r : ℝ) + 1)) ^ r * Z32 * (((M.factorial : ℝ) / (1 / 16 : ℝ) ^ M) / u ^ M)) * 1) := by
          gcongr
      _ = ‖PowerSeries.coeff (s + 1) S‖ * ((Nat.choose (s + r) r : ℝ) *
            ((4 * ((r : ℝ) + 1)) ^ r * Z32 * ((M.factorial : ℝ) / (1 / 16 : ℝ) ^ M))) / u ^ M := by
          ring
  rw [h_split_fPart]
  have h_tri : ‖((∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) +
          ∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))) -
        ∑ m ∈ Finset.range M,
          PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m‖ ≤
      ‖(∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) - head_ser‖ +
        ‖head_ser - head_poly‖ +
        ‖head_poly - ∑ m ∈ Finset.range M,
          PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m‖ +
        ‖∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))‖ := by
    have hid : ((∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) +
          ∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))) -
        ∑ m ∈ Finset.range M,
          PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m =
        ((∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) - head_ser) +
          (head_ser - head_poly) +
          (head_poly - ∑ m ∈ Finset.range M,
            PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m) +
          ∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1)) := by ring
    rw [hid]
    linarith [norm_add_le
      (((∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) - head_ser) +
        (head_ser - head_poly) +
        (head_poly - ∑ m ∈ Finset.range M,
          PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m))
      (∑' k : ℕ, ((k + K + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + K + 1))),
      norm_add_le
        (((∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) - head_ser) +
          (head_ser - head_poly))
        (head_poly - ∑ m ∈ Finset.range M,
          PowerSeries.coeff m (d_u^[j] (formalSeries (fun ξ => φ ξ * ψ ξ))) * (u : ℂ)⁻¹ ^ m),
      norm_add_le
        ((∑ k ∈ Finset.range K, ((k + 1 : ℂ) ^ 2)⁻¹ * iteratedDeriv j hI (u - Real.log (k + 1))) - head_ser)
        (head_ser - head_poly)]
  calc _ ≤ C_head / u ^ M + C_binom / u ^ M + C_trunc / u ^ M + C_tail / u ^ M := by
        linarith [h_tri, h_head_bd, h_binom_bd, h_trunc_bd, h_tail_bd]
    _ = (C_head + C_tail + C_binom + C_trunc) / u ^ M := by ring

/-! ### 3. Exponential Shift Elimination & Differential Transcendence of Partitions into Primes -/

private lemma alternating_choose_sum {k s : ℕ} (hsk : s ≤ k) :
    ∑ j ∈ Finset.Icc s k,
      (-1 : ℂ) ^ (j - s) * (Nat.choose k j : ℂ) * (Nat.choose j s : ℂ) =
      if s = k then 1 else 0 := by
  have hmul : ∀ j ∈ Finset.Icc s k,
      (-1 : ℂ) ^ (j - s) * (Nat.choose k j : ℂ) * (Nat.choose j s : ℂ) =
        (Nat.choose k s : ℂ) * ((-1 : ℂ) ^ (j - s) * (Nat.choose (k - s) (j - s) : ℂ)) := by
    intro j hj
    have hsj : s ≤ j := (Finset.mem_Icc.mp hj).1
    have hcm : (Nat.choose k j : ℂ) * (Nat.choose j s : ℂ) =
        (Nat.choose k s : ℂ) * (Nat.choose (k - s) (j - s) : ℂ) := by
      exact_mod_cast Nat.choose_mul hsj
    calc (-1 : ℂ) ^ (j - s) * (Nat.choose k j : ℂ) * (Nat.choose j s : ℂ)
        = (-1 : ℂ) ^ (j - s) * ((Nat.choose k j : ℂ) * (Nat.choose j s : ℂ)) := by ring
      _ = (-1 : ℂ) ^ (j - s) * ((Nat.choose k s : ℂ) * (Nat.choose (k - s) (j - s) : ℂ)) := by
          rw [hcm]
      _ = (Nat.choose k s : ℂ) * ((-1 : ℂ) ^ (j - s) * (Nat.choose (k - s) (j - s) : ℂ)) := by ring
  rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum]
  have hreindex : (∑ j ∈ Finset.Icc s k, (-1 : ℂ) ^ (j - s) * (Nat.choose (k - s) (j - s) : ℂ)) =
      ∑ t ∈ Finset.range (k - s + 1), (-1 : ℂ) ^ t * (Nat.choose (k - s) t : ℂ) := by
    refine Finset.sum_bij (fun j _ => j - s) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      omega
    · intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_Icc] at hj₁ hj₂
      omega
    · intro t ht
      rw [Finset.mem_range] at ht
      refine ⟨s + t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro _ _; rfl
  rw [hreindex]
  by_cases heq : s = k
  · subst heq
    simp
  · simp only [heq, ↓reduceIte]
    have hpos : 0 < k - s := by omega
    have hap := add_pow (-1 : ℂ) 1 (k - s)
    rw [show (-1 + 1 : ℂ) = 0 by ring, zero_pow hpos.ne'] at hap
    have hsum0 : ∑ t ∈ Finset.range (k - s + 1), (-1 : ℂ) ^ t * (Nat.choose (k - s) t : ℂ) = 0 := by
      rw [hap]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [one_pow, mul_one]
    rw [hsum0, mul_zero]

private lemma iteratedDeriv_exp_mul {g f : ℝ → ℂ}
    (hg_eq : ∀ u : ℝ, g u = Complex.exp (u : ℂ) * f u)
    (hf_diff : ∀ j : ℕ, Differentiable ℝ (iteratedDeriv j f)) (k : ℕ) (u : ℝ) :
    iteratedDeriv k g u = Complex.exp (u : ℂ) *
      ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv j f u := by
  induction k generalizing u with
  | zero => simp [hg_eq u]
  | succ k ih =>
    have hfun : iteratedDeriv k g = fun t : ℝ => Complex.exp (t : ℂ) *
        ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv j f t :=
      funext ih
    have he : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) (Complex.exp (u : ℂ)) u := by
      simpa [Function.comp_def] using (Complex.hasDerivAt_exp (u : ℂ)).comp_ofReal
    have hs : HasDerivAt (fun t : ℝ =>
        ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv j f t)
        (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv (j + 1) f u) u := by
      have hsum := HasDerivAt.fun_sum fun j (_ : j ∈ Finset.range (k + 1)) =>
        ((hf_diff j u).hasDerivAt).const_mul (Nat.choose k j : ℂ)
      refine hsum.congr_deriv ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDeriv_succ]
    have hder : iteratedDeriv (k + 1) g u = Complex.exp (u : ℂ) *
          (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv j f u) +
        Complex.exp (u : ℂ) *
          (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv (j + 1) f u) := by
      rw [iteratedDeriv_succ, hfun]
      convert (he.mul hs).deriv using 1
    rw [hder, ← mul_add]
    congr 1
    have h1 : (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv j f u) =
        ∑ j ∈ Finset.range (k + 2), (Nat.choose k j : ℂ) * iteratedDeriv j f u := by
      symm
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
      simp
    have h2 : (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℂ) * iteratedDeriv (j + 1) f u) =
        ∑ j ∈ Finset.range (k + 2),
          (if j = 0 then (0 : ℂ) else (Nat.choose k (j - 1) : ℂ)) * iteratedDeriv j f u := by
      symm
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, zero_mul, add_zero, Nat.succ_ne_zero, Nat.add_sub_cancel]
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases j with
    | zero => simp
    | succ m =>
      have hch : Nat.choose (k + 1) (m + 1) = Nat.choose k m + Nat.choose k (m + 1) :=
        Nat.choose_succ_succ k m
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      push_cast [hch]
      ring

private lemma eval_aeval_eq {σ τ : Type*} (x : τ → ℂ) (f : σ → MvPolynomial τ ℂ)
    (Q : MvPolynomial σ ℂ) :
    MvPolynomial.eval (fun i => MvPolynomial.eval x (f i)) Q =
      MvPolynomial.eval x (MvPolynomial.aeval f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X, hP]

private lemma aeval_comp_eq {σ τ ρ : Type*} (g : τ → MvPolynomial ρ ℂ)
    (f : σ → MvPolynomial τ ℂ) (Q : MvPolynomial σ ℂ) :
    MvPolynomial.aeval g (MvPolynomial.aeval f Q) =
      MvPolynomial.aeval (fun i => MvPolynomial.aeval g (f i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, MvPolynomial.aeval_X, hP]

/-- **Exponential Shift Cancellation Theorem**:
Suppose `g(u) = e^u * f(u)` where `f` is `C^∞` and all its derivatives match `d_u^[j] (formalSeries φ)`
to all polynomial orders `1/u^M` for some `MeromorphicBorelData φ ω res`.
Then `g` satisfies NO nonzero autonomous polynomial differential equation over `ℂ`. -/
theorem no_autonomous_ade_of_exp_mul_asymp
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {res : ℕ → ℂ}
    (hB : MeromorphicBorelData φ ω res)
    {g f : ℝ → ℂ}
    (hg_eq : ∀ u : ℝ, g u = Complex.exp (u : ℂ) * f u)
    (hf_diff : ∀ j : ℕ, Differentiable ℝ (iteratedDeriv j f))
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] (formalSeries φ)))
    {J : ℕ} (P : MvPolynomial (Fin J) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val g u) P = 0) :
    P = 0 := by
  classical
  cases J with
  | zero =>
    obtain ⟨u, hu⟩ := hP.exists
    have hP_c : P = MvPolynomial.C (MvPolynomial.eval (fun j : Fin 0 => iteratedDeriv j.val g u) P) := by
      have h0 := MvPolynomial.eq_C_of_isEmpty P
      rw [h0]
      simp [MvPolynomial.eval_C]
    rw [hP_c, hu, map_zero]
  | succ r =>
    by_contra hP_ne
    let deg : (Fin (r + 1) →₀ ℕ) → ℕ := fun α => ∑ k : Fin (r + 1), α k
    let D : ℕ := P.support.sup deg
    have h_le_D : ∀ α ∈ P.support, deg α ≤ D := fun α hα => Finset.le_sup hα
    obtain ⟨α₀, hα₀_mem, hα₀_deg⟩ := Finset.exists_mem_eq_sup P.support
      (MvPolynomial.support_nonempty.mpr hP_ne) deg
    let P_top : MvPolynomial (Fin (r + 1)) ℂ :=
      ∑ α ∈ P.support, if deg α = D then MvPolynomial.monomial α (P.coeff α) else 0
    let P_low : MvPolynomial (Fin (r + 1)) ℂ :=
      ∑ α ∈ P.support, if deg α < D then MvPolynomial.monomial α (P.coeff α) else 0
    have hP_top_ne : P_top ≠ 0 := by
      intro h0
      have hc0 : P_top.coeff α₀ = 0 := by rw [h0]; simp
      have hcoeff : P_top.coeff α₀ = P.coeff α₀ := by
        dsimp only [P_top]
        rw [MvPolynomial.coeff_sum]
        have hsingle : ∀ α ∈ P.support,
            (if deg α = D then MvPolynomial.monomial α (P.coeff α) else 0).coeff α₀ =
              if α = α₀ then P.coeff α₀ else 0 := fun α _ => by
          by_cases hd : deg α = D <;> by_cases hαe : α = α₀
          · subst hαe; simp [hd, MvPolynomial.coeff_monomial]
          · simp [hd, MvPolynomial.coeff_monomial, hαe]
          · subst hαe; exact absurd hα₀_deg.symm hd
          · simp [hd, hαe]
        have hsum_eq : (∑ α ∈ P.support,
            (if deg α = D then MvPolynomial.monomial α (P.coeff α) else 0).coeff α₀) =
            ∑ α ∈ P.support, if α = α₀ then P.coeff α₀ else 0 :=
          Finset.sum_congr rfl hsingle
        rw [hsum_eq, Finset.sum_ite_eq']
        simp [hα₀_mem]
      exact (MvPolynomial.mem_support_iff.mp hα₀_mem) (hcoeff ▸ hc0)
    have hP_split : P = P_top + P_low := by
      conv_lhs => rw [P.as_sum]
      dsimp only [P_top, P_low]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hle := h_le_D α hα
      by_cases heq : deg α = D
      · simp [heq]
      · have hlt : deg α < D := lt_of_le_of_ne hle heq
        simp [heq, hlt]
    let L : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ := fun k =>
      ∑ j ∈ Finset.range (k.1 + 1), if hj : j < r + 1 then
        MvPolynomial.C (Nat.choose k.1 j : ℂ) * MvPolynomial.X ⟨j, hj⟩ else 0
    let M : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ := fun j =>
      ∑ s ∈ Finset.range (j.1 + 1), if hs : s < r + 1 then
        MvPolynomial.C ((-1 : ℂ) ^ (j.1 - s) * (Nat.choose j.1 s : ℂ)) * MvPolynomial.X ⟨s, hs⟩ else 0
    have hML : ∀ k : Fin (r + 1), MvPolynomial.aeval M (L k) = MvPolynomial.X k := by
      intro k
      dsimp only [L]
      rw [map_sum]
      have hterm : ∀ j ∈ Finset.range (k.1 + 1),
          MvPolynomial.aeval M (if hj : j < r + 1 then
            MvPolynomial.C (Nat.choose k.1 j : ℂ) * MvPolynomial.X ⟨j, hj⟩ else 0) =
            ∑ s ∈ Finset.range (j + 1), if hs : s < r + 1 then
              MvPolynomial.C ((-1 : ℂ) ^ (j - s) * (Nat.choose k.1 j : ℂ) * (Nat.choose j s : ℂ)) *
                MvPolynomial.X ⟨s, hs⟩ else 0 := by
        intro j hj
        have hjk : j ≤ k.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hjr : j < r + 1 := lt_of_le_of_lt hjk k.2
        simp only [hjr, ↓reduceDIte, map_mul, MvPolynomial.aeval_C,
          MvPolynomial.algebraMap_eq, MvPolynomial.aeval_X]
        dsimp only [M]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with hs
        · rw [← mul_assoc]
          congr 1
          simp only [map_mul, map_pow, map_neg, map_one]
          ring
        · rw [mul_zero]
      rw [Finset.sum_congr rfl hterm]
      have hpad : ∀ j ∈ Finset.range (k.1 + 1),
          (∑ s ∈ Finset.range (j + 1), if hs : s < r + 1 then
            MvPolynomial.C ((-1 : ℂ) ^ (j - s) * (Nat.choose k.1 j : ℂ) * (Nat.choose j s : ℂ)) *
              (MvPolynomial.X ⟨s, hs⟩ : MvPolynomial (Fin (r + 1)) ℂ) else 0) =
          ∑ s ∈ Finset.range (k.1 + 1), if hs : s < r + 1 then
            (if s ≤ j then
              MvPolynomial.C ((-1 : ℂ) ^ (j - s) * (Nat.choose k.1 j : ℂ) * (Nat.choose j s : ℂ)) *
                (MvPolynomial.X ⟨s, hs⟩ : MvPolynomial (Fin (r + 1)) ℂ) else 0) else 0 := by
        intro j hj
        have hjk : j + 1 ≤ k.1 + 1 := by
          have := Finset.mem_range.mp hj; omega
        rw [← Finset.sum_subset (Finset.range_mono hjk)]
        · refine Finset.sum_congr rfl fun s hs => ?_
          have hsj : s ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
          split_ifs with hsr
          · rfl
          · rfl
        · intro s hs hnot
          have hsj : ¬ s ≤ j := fun h => hnot (Finset.mem_range.mpr (by omega))
          split_ifs with hsr <;> simp
      rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
      have hcol : ∀ s ∈ Finset.range (k.1 + 1),
          (∑ j ∈ Finset.range (k.1 + 1), if hs : s < r + 1 then
            (if s ≤ j then
              MvPolynomial.C ((-1 : ℂ) ^ (j - s) * (Nat.choose k.1 j : ℂ) * (Nat.choose j s : ℂ)) *
                MvPolynomial.X ⟨s, hs⟩ else 0) else 0) =
          if s = k.1 then MvPolynomial.X k else 0 := by
        intro s hs
        have hsk : s ≤ k.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        have hsr : s < r + 1 := lt_of_le_of_lt hsk k.2
        simp only [hsr, ↓reduceDIte]
        have hfilter : (∑ j ∈ Finset.range (k.1 + 1), if s ≤ j then
            MvPolynomial.C ((-1 : ℂ) ^ (j - s) * (Nat.choose k.1 j : ℂ) * (Nat.choose j s : ℂ)) *
              (MvPolynomial.X ⟨s, hsr⟩ : MvPolynomial (Fin (r + 1)) ℂ) else 0) =
            (∑ j ∈ Finset.Icc s k.1,
              MvPolynomial.C ((-1 : ℂ) ^ (j - s) * (Nat.choose k.1 j : ℂ) * (Nat.choose j s : ℂ))) *
              (MvPolynomial.X ⟨s, hsr⟩ : MvPolynomial (Fin (r + 1)) ℂ) := by
          rw [Finset.sum_mul, ← Finset.sum_filter]
          have hf_eq : (Finset.range (k.1 + 1)).filter (fun j => s ≤ j) = Finset.Icc s k.1 := by
            ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
          rw [hf_eq]
        rw [hfilter, ← map_sum, alternating_choose_sum hsk]
        split_ifs with heq
        · subst heq; simp
        · simp
      rw [Finset.sum_congr rfl hcol, Finset.sum_ite_eq']
      simp
    let Q_top : MvPolynomial (Fin (r + 1)) ℂ := MvPolynomial.aeval L P_top
    have hQ_top_ne : Q_top ≠ 0 := by
      intro hQ0
      have hback : MvPolynomial.aeval M Q_top = P_top := by
        dsimp only [Q_top]
        rw [aeval_comp_eq]
        simp_rw [hML]
        induction P_top using MvPolynomial.induction_on with
        | C c => simp
        | add A B _ _ => simp [map_add]
        | mul_X A i _ => simp [map_mul]
      rw [hQ0, map_zero] at hback
      exact hP_top_ne hback.symm
    let xf (u : ℝ) : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.1 f u
    let yk (u : ℝ) : Fin (r + 1) → ℂ := fun k => MvPolynomial.eval (xf u) (L k)
    have h_g_eq_yk : ∀ (k : Fin (r + 1)) (u : ℝ),
        iteratedDeriv k.1 g u = Complex.exp (u : ℂ) * yk u k := fun k u => by
      rw [iteratedDeriv_exp_mul hg_eq hf_diff k.1 u]
      congr 1
      dsimp only [yk, L]
      rw [MvPolynomial.eval_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≤ k.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjr : j < r + 1 := lt_of_le_of_lt hjk k.2
      simp only [hjr, ↓reduceDIte, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rfl
    have h_mon_eval : ∀ (α : Fin (r + 1) →₀ ℕ) (u : ℝ),
        MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.1 g u)
          (MvPolynomial.monomial α (P.coeff α)) =
        Complex.exp ((deg α : ℂ) * (u : ℂ)) *
          (P.coeff α * ∏ k : Fin (r + 1), (yk u k) ^ (α k)) := fun α u => by
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp_rw [h_g_eq_yk _ u, mul_pow]
      rw [Finset.prod_mul_distrib]
      have hexp_prod : (∏ k : Fin (r + 1), (Complex.exp (u : ℂ)) ^ (α k)) =
          Complex.exp ((deg α : ℂ) * (u : ℂ)) := by
        have h1 : ∀ k : Fin (r + 1), (Complex.exp (u : ℂ)) ^ (α k) =
            Complex.exp ((α k : ℂ) * (u : ℂ)) := fun k => by
          rw [← Complex.exp_nat_mul]
        simp_rw [h1, ← Complex.exp_sum, ← Finset.sum_mul]
        dsimp only [deg]
        push_cast; rfl
      rw [hexp_prod]; ring
    have h_Q_id : ∀ᶠ u : ℝ in Filter.atTop,
        MvPolynomial.eval (xf u) Q_top =
          - ∑ α ∈ P.support, if deg α < D then
              Complex.exp (-((D - deg α : ℕ) : ℂ) * (u : ℂ)) *
                (P.coeff α * ∏ k : Fin (r + 1), (yk u k) ^ (α k))
            else 0 := by
      filter_upwards [hP] with u hu
      have htop_eval : MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.1 g u) P_top =
          Complex.exp ((D : ℂ) * (u : ℂ)) * MvPolynomial.eval (xf u) Q_top := by
        dsimp only [P_top, Q_top]
        rw [← eval_aeval_eq, map_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        split_ifs with hd
        · rw [h_mon_eval α u, hd, MvPolynomial.eval_monomial,
            Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        · simp
      have hlow_eval : MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.1 g u) P_low =
          ∑ α ∈ P.support, if deg α < D then
            Complex.exp ((deg α : ℂ) * (u : ℂ)) *
              (P.coeff α * ∏ k : Fin (r + 1), (yk u k) ^ (α k))
          else 0 := by
        dsimp only [P_low]
        rw [map_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        split_ifs with hd
        · exact h_mon_eval α u
        · simp
      have hsum_0 : Complex.exp ((D : ℂ) * (u : ℂ)) * MvPolynomial.eval (xf u) Q_top +
          MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.1 g u) P_low = 0 := by
        rw [← htop_eval, ← map_add, ← hP_split]
        exact hu
      have hmul_neg := congrArg (fun z : ℂ => Complex.exp (-(D : ℂ) * (u : ℂ)) * z) hsum_0
      rw [mul_zero, mul_add, ← mul_assoc, ← Complex.exp_add,
        show -(D : ℂ) * (u : ℂ) + (D : ℂ) * (u : ℂ) = 0 by ring, Complex.exp_zero, one_mul,
        hlow_eval, Finset.mul_sum] at hmul_neg
      have hlow_simp : (∑ α ∈ P.support, Complex.exp (-(D : ℂ) * (u : ℂ)) *
          if deg α < D then Complex.exp ((deg α : ℂ) * (u : ℂ)) *
            (P.coeff α * ∏ k : Fin (r + 1), (yk u k) ^ (α k)) else 0) =
          ∑ α ∈ P.support, if deg α < D then
            Complex.exp (-((D - deg α : ℕ) : ℂ) * (u : ℂ)) *
              (P.coeff α * ∏ k : Fin (r + 1), (yk u k) ^ (α k)) else 0 := by
        refine Finset.sum_congr rfl fun α _ => ?_
        split_ifs with hlt
        · rw [← mul_assoc, ← Complex.exp_add]
          congr 2
          have : (deg α : ℂ) - (D : ℂ) = -((D - deg α : ℕ) : ℂ) := by
            have hle : deg α ≤ D := hlt.le
            push_cast [hle]; ring
          calc -(D : ℂ) * (u : ℂ) + (deg α : ℂ) * (u : ℂ)
              = ((deg α : ℂ) - (D : ℂ)) * (u : ℂ) := by ring
            _ = -((D - deg α : ℕ) : ℂ) * (u : ℂ) := by rw [this]
        · rw [mul_zero]
      rw [hlow_simp] at hmul_neg
      exact eq_neg_of_add_eq_zero_left hmul_neg
    have hf_bdd : ∀ j : Fin (r + 1), ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ᶠ u : ℝ in Filter.atTop,
        ‖xf u j‖ ≤ Cj := fun j => by
      obtain ⟨Cj, hCj⟩ := hf_asymp j.1 0
      refine ⟨max Cj 0, le_max_right _ _, ?_⟩
      filter_upwards [hCj] with u hu
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one] at hu
      exact hu.trans (le_max_left _ _)
    choose Cj hCj_nonneg hCj_bd using hf_bdd
    have hy_bdd : ∀ k : Fin (r + 1), ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ᶠ u : ℝ in Filter.atTop,
        ‖yk u k‖ ≤ Bk := fun k => by
      refine ⟨∑ j ∈ Finset.range (k.1 + 1), if hj : j < r + 1 then
        (Nat.choose k.1 j : ℝ) * Cj ⟨j, hj⟩ else 0,
        Finset.sum_nonneg fun j _ => by split_ifs with hj; exact mul_nonneg (by positivity) (hCj_nonneg _); rfl,
        ?_⟩
      have h_all : ∀ᶠ u : ℝ in Filter.atTop, ∀ j : Fin (r + 1), ‖xf u j‖ ≤ Cj j :=
        Filter.eventually_all.mpr hCj_bd
      filter_upwards [h_all] with u hu
      dsimp only [yk, L]
      rw [MvPolynomial.eval_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      split_ifs with hj
      · rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (hu ⟨j, hj⟩) (by positivity)
      · simp
    choose Bk hBk_nonneg hBk_bd using hy_bdd
    let C_exp : ℝ := ∑ α ∈ P.support, if deg α < D then
      ‖P.coeff α‖ * ∏ k : Fin (r + 1), Bk k ^ (α k) else 0
    have h_flat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in Filter.atTop,
        ‖MvPolynomial.eval (xf u) Q_top‖ ≤ C / u ^ M := fun M => by
      refine ⟨C_exp * (M.factorial : ℝ), ?_⟩
      have h_all_y : ∀ᶠ u : ℝ in Filter.atTop, ∀ k : Fin (r + 1), ‖yk u k‖ ≤ Bk k :=
        Filter.eventually_all.mpr hBk_bd
      filter_upwards [h_Q_id, h_all_y, eventually_gt_atTop (0 : ℝ)] with u hu hyu hpos
      rw [hu, norm_neg]
      refine (norm_sum_le _ _).trans ?_
      have h_term : ∀ α ∈ P.support,
          ‖if deg α < D then Complex.exp (-((D - deg α : ℕ) : ℂ) * (u : ℂ)) *
              (P.coeff α * ∏ k : Fin (r + 1), (yk u k) ^ (α k)) else 0‖ ≤
            (if deg α < D then ‖P.coeff α‖ * ∏ k : Fin (r + 1), Bk k ^ (α k) else 0) *
              Real.exp (-u) := fun α _ => by
        split_ifs with hlt
        · rw [norm_mul, norm_mul, Complex.norm_exp, norm_prod]
          have hexp_re : (-((D - deg α : ℕ) : ℂ) * (u : ℂ)).re =
              -((D - deg α : ℕ) : ℝ) * u := by
            simp [Complex.mul_re]
          have hexp_le : Real.exp ((-((D - deg α : ℕ) : ℂ) * (u : ℂ)).re) ≤ Real.exp (-u) := by
            rw [hexp_re, Real.exp_le_exp]
            have hge1 : (1 : ℝ) ≤ ((D - deg α : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ D - deg α)
            nlinarith
          have hprod_le : (∏ k : Fin (r + 1), ‖(yk u k) ^ (α k)‖) ≤
              ∏ k : Fin (r + 1), Bk k ^ (α k) := by
            gcongr with k _
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hyu k) (α k)
          calc Real.exp ((-((D - deg α : ℕ) : ℂ) * (u : ℂ)).re) *
                (‖P.coeff α‖ * ∏ k : Fin (r + 1), ‖(yk u k) ^ (α k)‖)
              ≤ Real.exp (-u) * (‖P.coeff α‖ * ∏ k : Fin (r + 1), Bk k ^ (α k)) :=
                mul_le_mul hexp_le (mul_le_mul_of_nonneg_left hprod_le (norm_nonneg _))
                  (by positivity) (Real.exp_pos _).le
            _ = (‖P.coeff α‖ * ∏ k : Fin (r + 1), Bk k ^ (α k)) * Real.exp (-u) := by ring
        · simp
      have h_le_exp : (∑ α ∈ P.support, ‖if deg α < D then
            Complex.exp (-((D - deg α : ℕ) : ℂ) * (u : ℂ)) *
              (P.coeff α * ∏ k : Fin (r + 1), (yk u k) ^ (α k)) else 0‖) ≤
          C_exp * Real.exp (-u) := by
        dsimp only [C_exp]
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum h_term
      have hC_nonneg : 0 ≤ C_exp :=
        Finset.sum_nonneg fun α _ => by
          split_ifs
          · exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun k _ => pow_nonneg (hBk_nonneg k) _)
          · rfl
      have h_exp_pow := exp_neg_mul_le_inv_pow 1 zero_lt_one M hpos
      rw [neg_one_mul, one_pow, div_one] at h_exp_pow
      calc _ ≤ C_exp * Real.exp (-u) := h_le_exp
        _ ≤ C_exp * ((M.factorial : ℝ) / u ^ M) := mul_le_mul_of_nonneg_left h_exp_pow hC_nonneg
        _ = C_exp * (M.factorial : ℝ) / u ^ M := by ring
    have hexp_Q : HasAsympExp (fun u => MvPolynomial.eval (xf u) Q_top)
        (formalEval (formalSeries φ) Q_top) :=
      HasAsympExp.mvPolynomial (fun j => hf_asymp j.1) Q_top
    have hformal0 : formalEval (formalSeries φ) Q_top = 0 :=
      hexp_Q.eq_zero_of_flat h_flat
    exact hQ_top_ne (borel_stokes_vandermonde_no_autonomous_ade hB Q_top hformal0)

private lemma fPart_differentiable_iteratedDeriv (j : ℕ) :
    Differentiable ℝ (iteratedDeriv j fPart) := by
  have hcd_exp : ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (-(u : ℂ))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg)
  have hcd_sr : ContDiff ℝ ⊤ (scaledRay partLogDerivSeries) :=
    contDiff_iff_contDiffAt.mpr fun u =>
      (scaledRay_analytic partLogDeriv_polyBound.to_diskCoeffBound u).contDiffAt
  have hcd_f : ContDiff ℝ ⊤ fPart := by
    change ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (-(u : ℂ)) * scaledRay partLogDerivSeries u)
    exact hcd_exp.mul hcd_sr
  exact hcd_f.differentiable_iteratedDeriv j (by simp)

/-- **End-to-End Differential Transcendence of `G_P(q) = ∑_{p prime} p q^p / (1 - q^p)`**:
Assuming `PNTAllOrders`, `partLogDerivCoordinates` `(q, G_P, G_P', G_P'', ...)` is
algebraically independent over `ℂ`. -/
theorem partLogDeriv_algebraicIndependent_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ partLogDerivCoordinates := by
  by_contra hdep
  obtain ⟨J, P, hP_ne, hP_ev⟩ := autonomous_transfer partLogDeriv_polyBound hdep
  have hg_eq : ∀ u : ℝ, scaledRay partLogDerivSeries u = Complex.exp (u : ℂ) * fPart u := fun u => by
    unfold fPart
    rw [← mul_assoc, ← Complex.exp_add, show (u : ℂ) + -(u : ℂ) = 0 by ring, Complex.exp_zero, one_mul]
  exact hP_ne (no_autonomous_ade_of_exp_mul_asymp phiPart_borelData hg_eq
    fPart_differentiable_iteratedDeriv (fPart_hasAsympExp hpnt) P hP_ev)

/-- **End-to-End Differential Transcendence of Partitions into Primes (OEIS A000607)**:
Assuming `PNTAllOrders`, the generating series `P_prime(q) = ∏_{p prime} (1 - q^p)^{-1}`
(`partitionPrimesSeries`) is differentially transcendental over `ℂ(q)`: its differential
coordinates `(q, P_prime, P_prime', P_prime'', ...)` are algebraically independent over `ℂ`. -/
theorem partitionPrimes_algebraicIndependent_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ (seriesCoordinates partitionPrimesSeries) := by
  by_contra hdep
  obtain ⟨J, R, hR_ne, hR_ev⟩ := partitionPrimes_log_deriv_transfer hdep
  have hg_eq : ∀ u : ℝ, scaledRay partLogDerivSeries u = Complex.exp (u : ℂ) * fPart u := fun u => by
    unfold fPart
    rw [← mul_assoc, ← Complex.exp_add, show (u : ℂ) + -(u : ℂ) = 0 by ring, Complex.exp_zero, one_mul]
  exact hR_ne (no_autonomous_ade_of_exp_mul_asymp phiPart_borelData hg_eq
    fPart_differentiable_iteratedDeriv (fPart_hasAsympExp hpnt) R hR_ev)

/-! ### 4. Distinct-Prime Partitions `Q_prime(q) = ∏_{p prime} (1 + q^p)` (OEIS A000586) -/

@[expose] def sigmaPDistinct (n : ℕ) : ℝ :=
  sigmaP n - if 2 ∣ n then 2 * sigmaP (n / 2) else 0

@[expose] def distinctLogDerivSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (sigmaPDistinct n : ℂ)

@[expose] def distinctPrimesCoeff : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
    (∑ k ∈ (Finset.range (n + 1)).attach,
      sigmaPDistinct (k.1 + 1) * distinctPrimesCoeff (n - k.1)) / ((n + 1 : ℕ) : ℝ)
termination_by n => n
decreasing_by
  have hk := Finset.mem_range.mp k.2
  omega

lemma distinctPrimesCoeff_zero : distinctPrimesCoeff 0 = 1 := by
  rw [distinctPrimesCoeff]

lemma distinctPrimesCoeff_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * distinctPrimesCoeff (n + 1) =
      ∑ k ∈ Finset.range (n + 1), sigmaPDistinct (k + 1) * distinctPrimesCoeff (n - k) := by
  conv_lhs => rw [distinctPrimesCoeff]
  have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hne]
  rw [Finset.sum_attach (Finset.range (n + 1)) fun k =>
    sigmaPDistinct (k + 1) * distinctPrimesCoeff (n - k)]

/-- Generating series for partitions into distinct primes `Q_prime(q) = ∏_{p prime} (1 + q^p)`,
defined uniquely by `Q_prime(0) = 1` and `q Q_prime'(q) = G_Q(q) Q_prime(q)` with
`G_Q(q) = G_P(q) - 2 G_P(q^2)`. -/
@[expose] def distinctPrimesSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (distinctPrimesCoeff n : ℂ)

lemma coeff_partLogDeriv_eq (k : ℕ) :
    PowerSeries.coeff k partLogDerivSeries = (sigmaP k : ℂ) := by
  simp only [partLogDerivSeries, PowerSeries.coeff_mk, sigmaP, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

theorem distinctLogDeriv_polyBound : PolyCoeffBound distinctLogDerivSeries := by
  obtain ⟨C, p, hC, hbd⟩ := partLogDeriv_polyBound
  refine ⟨3 * C, p, by positivity, fun n => ?_⟩
  simp only [distinctLogDerivSeries, PowerSeries.coeff_mk, Complex.norm_real, Real.norm_eq_abs]
  have hsig : ∀ k : ℕ, sigmaP k ≤ C * ((k : ℝ) + 1) ^ p := fun k => by
    have hk := hbd k
    rw [coeff_partLogDeriv_eq k, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sigmaP_nonneg k)] at hk
    exact hk
  have hhalf : ((n / 2 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast (show n / 2 + 1 ≤ n + 1 by omega)
  have hpow_le : (((n / 2 : ℕ) : ℝ) + 1) ^ p ≤ ((n : ℝ) + 1) ^ p :=
    pow_le_pow_left₀ (by positivity) hhalf p
  calc |sigmaPDistinct n|
      = |sigmaP n - if 2 ∣ n then 2 * sigmaP (n / 2) else 0| := rfl
    _ ≤ |sigmaP n| + |if 2 ∣ n then 2 * sigmaP (n / 2) else 0| := abs_sub _ _
    _ ≤ sigmaP n + 2 * sigmaP (n / 2) := by
        rw [abs_of_nonneg (sigmaP_nonneg n)]
        refine add_le_add le_rfl ?_
        split_ifs
        · rw [abs_mul, abs_of_pos (by norm_num), abs_of_nonneg (sigmaP_nonneg _)]
        · rw [abs_zero]; exact mul_nonneg zero_le_two (sigmaP_nonneg _)
    _ ≤ C * ((n : ℝ) + 1) ^ p + 2 * (C * (((n / 2 : ℕ) : ℝ) + 1) ^ p) :=
        add_le_add (hsig n) (mul_le_mul_of_nonneg_left (hsig (n / 2)) (by norm_num))
    _ ≤ C * ((n : ℝ) + 1) ^ p + 2 * (C * ((n : ℝ) + 1) ^ p) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_le hC) (by norm_num))
    _ = (3 * C) * ((n : ℝ) + 1) ^ p := by ring

theorem distinctPrimesSeries_constantCoeff :
    PowerSeries.constantCoeff distinctPrimesSeries = 1 := by
  simp [distinctPrimesSeries, distinctPrimesCoeff_zero]

theorem distinctPrimesSeries_ode :
    PowerSeries.X * PowerSeries.derivative distinctPrimesSeries =
      distinctLogDerivSeries * distinctPrimesSeries := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [distinctLogDerivSeries, sigmaPDistinct, sigmaP]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i distinctLogDerivSeries * PowerSeries.coeff j distinctPrimesSeries) (m + 1),
      Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 distinctLogDerivSeries = 0 := by
      simp [distinctLogDerivSeries, sigmaPDistinct, sigmaP]
    rw [h0, zero_mul, add_zero]
    simp only [distinctPrimesSeries, PowerSeries.coeff_mk]
    have hL : (distinctPrimesCoeff (m + 1) : ℂ) * ((m : ℂ) + 1) =
        ((∑ k ∈ Finset.range (m + 1), sigmaPDistinct (k + 1) * distinctPrimesCoeff (m - k) : ℝ) : ℂ) := by
      rw [← distinctPrimesCoeff_succ m]
      push_cast; ring
    rw [hL, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [distinctLogDerivSeries, PowerSeries.coeff_mk, show m + 1 - (k + 1) = m - k by omega]
    push_cast; rfl

theorem distinctPrimesSeries_diskBound : DiskCoeffBound distinctPrimesSeries := by
  intro r hr0 hr1
  obtain ⟨Cg, pg, hCg, hbg⟩ := distinctLogDeriv_polyBound
  have hsum_g : Summable (fun k : ℕ => Cg * ((k + 2 : ℝ) ^ pg * r ^ (k + 1))) := by
    have hs := summable_pow_mul_geometric_of_norm_lt_one pg
      (show ‖r‖ < 1 by simpa [abs_of_pos hr0] using hr1)
    have h := (hs.comp_injective (show Function.Injective (fun k : ℕ => k + 2) from
      fun _ _ hh => Nat.add_right_cancel hh)).mul_right r⁻¹
    refine (h.mul_left Cg).congr fun k => ?_
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, pow_add, pow_two]
    field_simp [hr0.ne']
  have hsum_sig : Summable (fun k : ℕ => |sigmaPDistinct (k + 1)| * r ^ (k + 1)) := by
    refine hsum_g.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hr0.le _)) fun k => ?_
    have hcoeff := hbg (k + 1)
    simp only [distinctLogDerivSeries, PowerSeries.coeff_mk, Complex.norm_real, Real.norm_eq_abs] at hcoeff
    have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hcoeff
    calc |sigmaPDistinct (k + 1)| * r ^ (k + 1)
        ≤ (Cg * ((k : ℝ) + 2) ^ pg) * r ^ (k + 1) :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr0.le _)
      _ = Cg * ((k + 2 : ℝ) ^ pg * r ^ (k + 1)) := by ring
  let B : ℝ := ∑' k : ℕ, |sigmaPDistinct (k + 1)| * r ^ (k + 1)
  obtain ⟨N, hN⟩ := exists_nat_ge (max B 1)
  have hBN : B ≤ (N : ℝ) := (le_max_left B 1).trans hN
  let seq : ℕ → ℝ := fun n => |distinctPrimesCoeff n| * r ^ n
  let M : ℝ := (Finset.range (N + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N)) seq
  have hM_nonneg : 0 ≤ M := by
    have h0 : 0 ≤ seq 0 := mul_nonneg (abs_nonneg _) (pow_nonneg hr0.le 0)
    exact h0.trans (Finset.le_sup' seq (Finset.mem_range.mpr (Nat.zero_lt_succ N)))
  have hseq_le : ∀ n : ℕ, seq n ≤ M := fun n => by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hnN : n ≤ N
      · exact Finset.le_sup' seq (Finset.mem_range.mpr (by omega))
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        have hmN : N ≤ m := by omega
        have hmul : ((m + 1 : ℕ) : ℝ) * seq (m + 1) ≤ ((m + 1 : ℕ) : ℝ) * M := by
          have heq_lhs : ((m + 1 : ℕ) : ℝ) * seq (m + 1) =
              |∑ k ∈ Finset.range (m + 1),
                (sigmaPDistinct (k + 1) * r ^ (k + 1)) * (distinctPrimesCoeff (m - k) * r ^ (m - k))| := by
            dsimp [seq]
            have hrpos : 0 ≤ r ^ (m + 1) := pow_nonneg hr0.le _
            rw [← mul_assoc, ← abs_of_pos (by positivity : (0 : ℝ) < (m + 1 : ℕ)), ← abs_mul,
              distinctPrimesCoeff_succ m, ← abs_of_nonneg hrpos, ← abs_mul, Finset.sum_mul]
            congr 1
            refine Finset.sum_congr rfl fun k hk => ?_
            have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            rw [show m + 1 = (k + 1) + (m - k) by omega, pow_add]
            ring
          rw [heq_lhs]
          have hsum_abs : |∑ k ∈ Finset.range (m + 1),
              (sigmaPDistinct (k + 1) * r ^ (k + 1)) * (distinctPrimesCoeff (m - k) * r ^ (m - k))| ≤
              (∑ k ∈ Finset.range (m + 1), |sigmaPDistinct (k + 1)| * r ^ (k + 1)) * M := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            rw [Finset.sum_mul]
            refine Finset.sum_le_sum fun k hk => ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0.le _)]
            have hseqm : |distinctPrimesCoeff (m - k) * r ^ (m - k)| ≤ M := by
              rw [abs_mul, abs_of_nonneg (pow_nonneg hr0.le _)]
              exact ih (m - k) (by omega)
            exact mul_le_mul_of_nonneg_left hseqm (mul_nonneg (abs_nonneg _) (pow_nonneg hr0.le _))
          have hpart_le_B : ∑ k ∈ Finset.range (m + 1), |sigmaPDistinct (k + 1)| * r ^ (k + 1) ≤ B :=
            hsum_sig.sum_le_tsum (Finset.range (m + 1)) fun k _ =>
              mul_nonneg (abs_nonneg _) (pow_nonneg hr0.le _)
          have hB_le_m1 : B ≤ ((m + 1 : ℕ) : ℝ) :=
            hBN.trans (by exact_mod_cast (by omega : N ≤ m + 1))
          exact hsum_abs.trans
            ((mul_le_mul_of_nonneg_right hpart_le_B hM_nonneg).trans
              (mul_le_mul_of_nonneg_right hB_le_m1 hM_nonneg))
        exact le_of_mul_le_mul_left hmul (by positivity)
  refine ⟨M, hM_nonneg, fun n => ?_⟩
  simp only [distinctPrimesSeries, PowerSeries.coeff_mk, Complex.norm_real, Real.norm_eq_abs]
  have hrn_pos : 0 < r ^ n := pow_pos hr0 n
  rw [inv_pow]
  calc |distinctPrimesCoeff n| = seq n * (r ^ n)⁻¹ := by dsimp [seq]; field_simp [hrn_pos.ne']
    _ ≤ M * (r ^ n)⁻¹ := mul_le_mul_of_nonneg_right (hseq_le n) (inv_nonneg.mpr hrn_pos.le)

private def evenLogDerivSeries : PowerSeries ℂ := by
  classical exact PowerSeries.mk fun n => if Even n then 2 * (sigmaP (n / 2) : ℂ) else 0

private def partitionPrimesEven : PowerSeries ℂ := by
  classical exact PowerSeries.mk fun n => if Even n then (partitionPrimesCoeff (n / 2) : ℂ) else 0

private lemma distinctLogDeriv_add_evenLogDeriv :
    distinctLogDerivSeries + evenLogDerivSeries = partLogDerivSeries := by
  ext n
  rw [map_add, coeff_partLogDeriv_eq]
  simp only [distinctLogDerivSeries, evenLogDerivSeries, PowerSeries.coeff_mk, sigmaPDistinct]
  have hev : Even n ↔ 2 ∣ n := even_iff_two_dvd
  by_cases h2 : 2 ∣ n
  · have hE : Even n := hev.mpr h2
    simp only [h2, hE, ↓reduceIte]
    push_cast; ring
  · have hE : ¬ Even n := fun h => h2 (hev.mp h)
    simp only [h2, hE, ↓reduceIte, sub_zero, add_zero]

private lemma partitionPrimesEven_diskBound : DiskCoeffBound partitionPrimesEven := by
  intro r hr0 hr1
  obtain ⟨M, hM, hbd⟩ := partitionPrimesSeries_diskBound r hr0 hr1
  refine ⟨M, hM, fun n => ?_⟩
  simp only [partitionPrimesEven, PowerSeries.coeff_mk]
  split_ifs with hn
  · have hk := hbd (n / 2)
    simp only [partitionPrimesSeries, PowerSeries.coeff_mk, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (partitionPrimesCoeff_nonneg _)] at hk
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (partitionPrimesCoeff_nonneg _)]
    have h1r : 1 ≤ r⁻¹ := (one_le_inv₀ hr0).mpr hr1.le
    have hpow_le : (r⁻¹) ^ (n / 2) ≤ (r⁻¹) ^ n := pow_le_pow_right₀ h1r (Nat.div_le_self n 2)
    exact hk.trans (mul_le_mul_of_nonneg_left hpow_le hM)
  · simp only [norm_zero]
    exact mul_nonneg hM (pow_nonneg (inv_nonneg.mpr hr0.le) n)

private lemma partitionPrimesEven_ode :
    PowerSeries.X * PowerSeries.derivative partitionPrimesEven =
      evenLogDerivSeries * partitionPrimesEven := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [evenLogDerivSeries, sigmaP]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i evenLogDerivSeries * PowerSeries.coeff j partitionPrimesEven) (m + 1)]
    simp only [partitionPrimesEven, evenLogDerivSeries, PowerSeries.coeff_mk]
    by_cases hev : Even (m + 1)
    · obtain ⟨k, hk⟩ := hev
      have hk_pos : 0 < k := by omega
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
      have hm1 : m + 1 = 2 * (t + 1) := by omega
      have hev_m1 : Even (m + 1) := ⟨t + 1, by omega⟩
      simp only [hev_m1, ↓reduceIte]
      have hdiv : (m + 1) / 2 = t + 1 := by omega
      rw [hdiv]
      have hL : (partitionPrimesCoeff (t + 1) : ℂ) * ((m : ℂ) + 1) =
          2 * ((∑ s ∈ Finset.range (t + 1), sigmaP (s + 1) * partitionPrimesCoeff (t - s) : ℝ) : ℂ) := by
        rw [← partitionPrimesCoeff_succ t]
        have hm_eq : (m : ℂ) + 1 = 2 * ((t : ℂ) + 1) := by exact_mod_cast hm1
        rw [hm_eq]; push_cast; ring
      rw [hL, Complex.ofReal_sum, Finset.mul_sum]
      have hr_eq : (∑ s ∈ Finset.range (t + 1), 2 * ((sigmaP (s + 1) * partitionPrimesCoeff (t - s) : ℝ) : ℂ)) =
          ∑ x ∈ (Finset.range (m + 1 + 1)).filter (fun i => Even i ∧ 0 < i),
            (if Even x then 2 * (sigmaP (x / 2) : ℂ) else 0) *
              (if Even (m + 1 - x) then (partitionPrimesCoeff ((m + 1 - x) / 2) : ℂ) else 0) := by
        refine Finset.sum_bij (fun s _ => 2 * (s + 1)) ?_ ?_ ?_ ?_
        · intro s hs
          rw [Finset.mem_range] at hs
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, ⟨⟨s + 1, by omega⟩, by omega⟩⟩
        · intro s₁ _ s₂ _ h; omega
        · intro x hx
          rw [Finset.mem_filter, Finset.mem_range] at hx
          obtain ⟨a, ha⟩ := hx.2.1
          have ha_pos : 0 < a := by omega
          refine ⟨a - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intro s hs
          rw [Finset.mem_range] at hs
          have hx_ev : Even (2 * (s + 1)) := ⟨s + 1, by omega⟩
          have hy_ev : Even (m + 1 - 2 * (s + 1)) := ⟨t - s, by omega⟩
          have hd1 : (2 * (s + 1)) / 2 = s + 1 := by omega
          have hd2 : (m + 1 - 2 * (s + 1)) / 2 = t - s := by omega
          simp only [hx_ev, hy_ev, ↓reduceIte, hd1, hd2]
          push_cast; ring
      rw [hr_eq, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx_ev : Even x
      · by_cases hx0 : 0 < x
        · simp [hx_ev, hx0]
        · have hx_z : x = 0 := by omega
          subst hx_z
          simp [sigmaP]
      · simp [hx_ev]
    · simp only [hev, ↓reduceIte, zero_mul]
      symm
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx_le : x ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      by_cases hx_ev : Even x
      · have hy_odd : ¬ Even (m + 1 - x) := by
          intro hy_ev
          exact hev (by
            have hadd := hx_ev.add hy_ev
            rwa [Nat.add_sub_cancel' hx_le] at hadd)
        simp [hy_odd]
      · simp [hx_ev]

private lemma powerSeries_ode_unique {G A B : PowerSeries ℂ}
    (hG0 : PowerSeries.coeff 0 G = 0)
    (hA : PowerSeries.X * PowerSeries.derivative A = G * A)
    (hB : PowerSeries.X * PowerSeries.derivative B = G * B)
    (hc : PowerSeries.constantCoeff A = PowerSeries.constantCoeff B) :
    A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      exact hc
    | succ m =>
      have hA_eq := congrArg (PowerSeries.coeff (m + 1)) hA
      have hB_eq := congrArg (PowerSeries.coeff (m + 1)) hB
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
          PowerSeries.coeff i G * PowerSeries.coeff j A) (m + 1),
        Finset.sum_range_succ', hG0, zero_mul, add_zero] at hA_eq
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
          PowerSeries.coeff i G * PowerSeries.coeff j B) (m + 1),
        Finset.sum_range_succ', hG0, zero_mul, add_zero] at hB_eq
      have hr_eq : (∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff (k + 1) G * PowerSeries.coeff (m + 1 - (k + 1)) A) =
          ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff (k + 1) G * PowerSeries.coeff (m + 1 - (k + 1)) B := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show m + 1 - (k + 1) = m - k by omega, ih (m - k) (by omega)]
      have hm_ne : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      exact mul_right_cancel₀ hm_ne (hA_eq.trans (hr_eq.trans hB_eq.symm))

private lemma distinctPrimesSeries_mul_even :
    distinctPrimesSeries * partitionPrimesEven = partitionPrimesSeries := by
  have hG0 : PowerSeries.coeff 0 partLogDerivSeries = 0 := by
    rw [coeff_partLogDeriv_eq 0]; simp [sigmaP]
  have h_ode : PowerSeries.X * PowerSeries.derivative (distinctPrimesSeries * partitionPrimesEven) =
      partLogDerivSeries * (distinctPrimesSeries * partitionPrimesEven) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    calc PowerSeries.X * (distinctPrimesSeries * PowerSeries.derivative partitionPrimesEven +
            partitionPrimesEven * PowerSeries.derivative distinctPrimesSeries)
        = (PowerSeries.X * PowerSeries.derivative distinctPrimesSeries) * partitionPrimesEven +
            distinctPrimesSeries * (PowerSeries.X * PowerSeries.derivative partitionPrimesEven) := by ring
      _ = (distinctLogDerivSeries * distinctPrimesSeries) * partitionPrimesEven +
            distinctPrimesSeries * (evenLogDerivSeries * partitionPrimesEven) := by
          rw [distinctPrimesSeries_ode, partitionPrimesEven_ode]
      _ = (distinctLogDerivSeries + evenLogDerivSeries) *
            (distinctPrimesSeries * partitionPrimesEven) := by ring
      _ = partLogDerivSeries * (distinctPrimesSeries * partitionPrimesEven) := by
          rw [distinctLogDeriv_add_evenLogDeriv]
  have hc : PowerSeries.constantCoeff (distinctPrimesSeries * partitionPrimesEven) =
      PowerSeries.constantCoeff partitionPrimesSeries := by
    rw [map_mul, distinctPrimesSeries_constantCoeff, partitionPrimesSeries_constantCoeff]
    simp [partitionPrimesEven, partitionPrimesCoeff_zero]
  exact powerSeries_ode_unique hG0 h_ode partitionPrimesSeries_ode hc

theorem distinctPrimesSeries_qRay_ne_zero (u : ℝ) :
    value distinctPrimesSeries (qRay u) ≠ 0 := by
  have hS : ∀ b : Bool, AbsAt (if b then distinctPrimesSeries else partitionPrimesEven) (qRay u) := by
    intro b
    cases b
    · simpa [seriesJet] using seriesJet_abs partitionPrimesEven_diskBound 0 (qRay_disk u)
    · simpa [seriesJet] using seriesJet_abs distinctPrimesSeries_diskBound 0 (qRay_disk u)
  have hprod := (polynomial_value (MvPolynomial.X true * MvPolynomial.X false) hS).2
  simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, ↓reduceIte, Bool.false_eq_true] at hprod
  rw [distinctPrimesSeries_mul_even] at hprod
  intro hz
  rw [hz, zero_mul] at hprod
  exact partitionPrimesSeries_qRay_ne_zero u hprod

/-- Simple-pole frequencies `{2, 3, 5, 7, ...}` for distinct-prime partitions `Q_prime`. -/
@[expose] def ωQ (m : ℕ) : ℝ := ωPart (m + 1)

/-- Raw distinct-prime Borel kernel `(1 - 2^{ξ - 1}) * phiPartClean ξ`. -/
@[expose] def phiQRaw (ξ : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (ξ - 1)) * phiPartClean ξ

/-- Analytic Borel kernel for distinct-prime partitions, removing the simple pole of `phiPartClean`
at `ξ = 1` with limiting value `log 2`. -/
@[expose] def phiQClean : ℂ → ℂ :=
  Function.update phiQRaw 1 (Real.log 2 : ℂ)

/-- Nonzero simple-pole residues of `phiQClean` at `ωQ m ∈ {2, 3, 5, 7, ...}`. -/
@[expose] def resQ (m : ℕ) : ℂ :=
  (1 - (2 : ℂ) ^ ((ωQ m : ℂ) - 1)) * resPart (m + 1)

lemma ωQ_strictMono : StrictMono ωQ := fun _ _ hab =>
  ωPart_strictMono (Nat.succ_lt_succ hab)

lemma ωQ_ge_two (m : ℕ) : (2 : ℝ) ≤ ωQ m := by
  have h1 : (ωPart 1 : ℝ) ≤ ωPart (m + 1) := ωPart_strictMono.monotone (Nat.succ_le_succ (Nat.zero_le m))
  simpa [ωQ, ωPart] using h1

lemma resQ_ne_zero (m : ℕ) : resQ m ≠ 0 := by
  dsimp only [resQ]
  have h2_ge : (2 : ℝ) ≤ (2 : ℝ) ^ (ωQ m - 1) := by
    have h1 : (1 : ℝ) ≤ ωQ m - 1 := by linarith [ωQ_ge_two m]
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (ωQ m - 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hcpow : (1 : ℂ) - (2 : ℂ) ^ ((ωQ m : ℂ) - 1) = (((1 : ℝ) - (2 : ℝ) ^ (ωQ m - 1) : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      show ((ωQ m : ℂ) - 1) = ((ωQ m - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have hfac_ne : (1 : ℂ) - (2 : ℂ) ^ ((ωQ m : ℂ) - 1) ≠ 0 := by
    rw [hcpow, Complex.ofReal_ne_zero]
    linarith
  exact mul_ne_zero hfac_ne (resPart_ne_zero (m + 1))

private lemma cpow_two_sub_one_analyticAt (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (w - 1)) z :=
  analyticAt_const.sub (cpow_const_analyticAt 2 (by norm_num) (fun w => w - 1) z
    (analyticAt_id.sub analyticAt_const))

private lemma phiQClean_analyticAt_one : AnalyticAt ℂ phiQClean 1 := by
  have h_diff_nhds : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ phiQClean z := by
    have hball : Metric.ball (1 : ℂ) (1 / 2) \ {1} ∈ 𝓝[≠] (1 : ℂ) := by
      rw [Set.sdiff_eq, Set.inter_comm]
      exact inter_mem_nhdsWithin _
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
    filter_upwards [hball] with z ⟨hz_ball, hz_ne⟩
    have hz1 : z ≠ 1 := hz_ne
    have h_upd : phiQClean =ᶠ[𝓝 z] phiQRaw := by
      filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
      exact Function.update_of_ne hw _ _
    have hz_in : z ∈ puncturedWedge (Real.pi / 3) (1 / 2) ωPart := by
      rw [Metric.mem_ball, dist_eq_norm] at hz_ball
      have hre_abs : |z.re - 1| < 1 / 2 := (Complex.abs_re_le_norm (z - 1)).trans_lt hz_ball
      have hz_re_gt : (1 / 2 : ℝ) < z.re := by linarith [(abs_lt.mp hre_abs).1]
      have hz_re_lt : z.re < 3 / 2 := by linarith [(abs_lt.mp hre_abs).2]
      have him_abs : |z.im| < 1 / 2 := by
        have h := (Complex.abs_im_le_norm (z - 1)).trans_lt hz_ball
        simpa using h
      refine ⟨Or.inr ⟨by linarith, ?_⟩, ?_⟩
      · rw [Real.tan_pi_div_three]
        have hrt3 : (1 : ℝ) < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
        nlinarith
      · rintro ⟨m, hm⟩
        cases m with
        | zero => exact hz1 (by simpa [ωPart] using hm.symm)
        | succ k =>
          have hge2 : (2 : ℝ) ≤ ωPart (k + 1) := by
            have := ωPart_strictMono.monotone (Nat.succ_le_succ (Nat.zero_le k))
            simpa [ωPart] using this
          have hre := congrArg Complex.re hm
          simp only [Complex.ofReal_re] at hre
          linarith
    have h_raw_an : AnalyticAt ℂ phiQRaw z :=
      (cpow_two_sub_one_analyticAt z).mul (phiPartClean_analyticOn z hz_in)
    exact (h_raw_an.congr h_upd.symm).differentiableAt
  have h_tend : Tendsto phiQRaw (𝓝[≠] (1 : ℂ)) (𝓝 (Real.log 2 : ℂ)) := by
    let g₁ : ℂ → ℂ := fun w => 1 - (2 : ℂ) ^ (w - 1)
    have hg₁_eq : g₁ = fun w => 1 - Complex.exp ((Real.log 2 : ℂ) * (w - 1)) := by
      funext w
      dsimp only [g₁]
      rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
        show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    have hg₁_deriv : HasDerivAt g₁ (-(Real.log 2 : ℂ)) 1 := by
      rw [hg₁_eq]
      have hlin : HasDerivAt (fun w : ℂ => (Real.log 2 : ℂ) * (w - 1)) (Real.log 2 : ℂ) 1 := by
        simpa using ((hasDerivAt_id (1 : ℂ)).sub_const 1).const_mul (Real.log 2 : ℂ)
      have hexp : HasDerivAt (fun w : ℂ => Complex.exp ((Real.log 2 : ℂ) * (w - 1)))
          (Complex.exp ((Real.log 2 : ℂ) * ((1 : ℂ) - 1)) * (Real.log 2 : ℂ)) 1 :=
        hlin.cexp
      simp only [sub_self, mul_zero, Complex.exp_zero, one_mul] at hexp
      exact hexp.const_sub 1
    have h_slope : Tendsto (slope g₁ 1) (𝓝[≠] (1 : ℂ)) (𝓝 (-(Real.log 2 : ℂ))) :=
      hasDerivAt_iff_tendsto_slope.mp hg₁_deriv
    have h_pole : Tendsto (fun z : ℂ => (z - 1) * phiPartClean z) (𝓝[≠] (1 : ℂ)) (𝓝 (-1 : ℂ)) := by
      simpa [ωPart, resPart] using phiPartClean_simple_pole 0
    have h_mul := h_slope.mul h_pole
    rw [show (-(Real.log 2 : ℂ)) * (-1 : ℂ) = (Real.log 2 : ℂ) by ring] at h_mul
    have h_eq : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ),
        slope g₁ 1 z * ((z - 1) * phiPartClean z) = phiQRaw z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      have hg1_1 : g₁ 1 = 0 := by simp [g₁]
      rw [slope_def_field, hg1_1, sub_zero]
      dsimp only [phiQRaw, g₁]
      field_simp [hz1]
    exact h_mul.congr' h_eq
  have h_cont : ContinuousAt phiQClean 1 := by
    dsimp only [phiQClean]
    exact continuousAt_update_same.mpr h_tend
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt h_diff_nhds h_cont

lemma phiQClean_analyticOn :
    AnalyticOnNhd ℂ phiQClean (puncturedWedge (Real.pi / 3) (1 / 2) ωQ) := by
  intro z hz
  by_cases hz1 : z = 1
  · subst hz1; exact phiQClean_analyticAt_one
  · have h_upd : phiQClean =ᶠ[𝓝 z] phiQRaw := by
      filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
      exact Function.update_of_ne hw _ _
    have hz_in : z ∈ puncturedWedge (Real.pi / 3) (1 / 2) ωPart := by
      refine ⟨hz.1, ?_⟩
      rintro ⟨m, hm⟩
      cases m with
      | zero => exact hz1 (by simpa [ωPart] using hm.symm)
      | succ k => exact hz.2 ⟨k, by simpa [ωQ] using hm⟩
    have h_raw : AnalyticAt ℂ phiQRaw z :=
      (cpow_two_sub_one_analyticAt z).mul (phiPartClean_analyticOn z hz_in)
    exact h_raw.congr h_upd.symm

lemma phiQClean_simple_pole (m : ℕ) :
    Tendsto (fun z : ℂ => (z - (ωQ m : ℂ)) * phiQClean z)
      (𝓝[≠] (ωQ m : ℂ)) (𝓝 (resQ m)) := by
  have hz1 : (ωQ m : ℂ) ≠ 1 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    linarith [ωQ_ge_two m]
  have h_upd : ∀ᶠ z : ℂ in 𝓝[≠] (ωQ m : ℂ),
      (z - (ωQ m : ℂ)) * phiQClean z =
        (1 - (2 : ℂ) ^ (z - 1)) * ((z - (ωPart (m + 1) : ℂ)) * phiPartClean z) := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz1)] with z hz
    dsimp only [phiQClean, ωQ]
    rw [Function.update_of_ne hz]
    dsimp only [phiQRaw]
    ring
  have h_fac : Tendsto (fun z : ℂ => 1 - (2 : ℂ) ^ (z - 1))
      (𝓝[≠] (ωQ m : ℂ)) (𝓝 (1 - (2 : ℂ) ^ ((ωQ m : ℂ) - 1))) :=
    (cpow_two_sub_one_analyticAt _).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({(ωQ m : ℂ)}ᶜ : Set ℂ)))
  have h_pole : Tendsto (fun z : ℂ => (z - (ωPart (m + 1) : ℂ)) * phiPartClean z)
      (𝓝[≠] (ωQ m : ℂ)) (𝓝 (resPart (m + 1))) := by
    simpa [ωQ] using phiPartClean_simple_pole (m + 1)
  exact (h_fac.mul h_pole).congr' (h_upd.mono fun _ h => h.symm)

lemma phiQClean_ray_decay {d : ℂ} (hd_re : d.re = Real.sqrt 2 / 2)
    (hd_im : |d.im| = Real.sqrt 2 / 2) (hd_norm : ‖d‖ = 1) :
    ExpType (Minor.pull d phiQClean) := by
  have havoid : ∀ v : ℝ, 0 ≤ v → d * (v : ℂ) ∈ puncturedWedge (Real.pi / 3) (1 / 2) ωQ := by
    intro v hv
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hv with rfl | hv_pos
      · left; simp [Metric.mem_ball]
      · right
        have hre : 0 < (d * (v : ℂ)).re := by
          simp [Complex.mul_re, hd_re]; positivity
        have htan : Real.sqrt 2 / 2 < Real.tan (Real.pi / 3) * (Real.sqrt 2 / 2) := by
          rw [Real.tan_pi_div_three]
          have h1 : (1 : ℝ) < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
          have hs : 0 < Real.sqrt 2 / 2 := by positivity
          nlinarith
        refine ⟨hre, ?_⟩
        have him' : (d * (v : ℂ)).im = d.im * v := by simp [Complex.mul_im]
        have hre' : (d * (v : ℂ)).re = d.re * v := by simp [Complex.mul_re]
        rw [him', hre', abs_mul, hd_im, abs_of_pos hv_pos, hd_re]
        nlinarith
    · rintro ⟨m, hm⟩
      have him := congrArg Complex.im hm
      simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero] at him
      have him' : d.im * v = 0 := by linarith
      have hdim_ne : d.im ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hd_im; exact absurd hd_im.symm (by positivity)
      have hv0 : v = 0 := (mul_eq_zero.mp him').resolve_left hdim_ne
      subst hv0
      have hre := congrArg Complex.re hm
      simp only [Complex.ofReal_zero, mul_zero, Complex.zero_re, Complex.ofReal_re] at hre
      linarith [ωQ_ge_two m]
  have hcont : ContinuousOn (fun v : ℝ => ‖Minor.pull d phiQClean v‖) (Icc 0 5) := by
    refine ContinuousOn.norm (continuousOn_const.mul fun v hv => ?_)
    have hmul : Continuous (fun x : ℝ => d * (x : ℂ)) := continuous_const.mul Complex.continuous_ofReal
    exact ((phiQClean_analyticOn _ (havoid v hv.1)).continuousAt.comp
      (f := fun x : ℝ => d * (x : ℂ)) hmul.continuousAt).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let Z₂ : ℝ := ∑' n : ℕ, ((n + 1 : ℝ) ^ 2)⁻¹
  have hZ₂_summ : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ 2)⁻¹) := by
    have h1 := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_right_cancel h)
    refine h1.congr fun n => by simp
  have hZ₂_nonneg : 0 ≤ Z₂ := tsum_nonneg fun _ => by positivity
  let C : ℝ := max C₀ (4 * Real.pi * Z₂)
  refine ⟨C, 0, by positivity, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hv5 : v ≤ 5
  · have hb := hC₀ v ⟨hv, hv5⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    exact hb.trans (le_max_left _ _)
  · have hv_gt : 5 < v := lt_of_not_ge hv5
    let ξ : ℂ := d * (v : ℂ)
    have hξ_re_gt : 3 < ξ.re := by
      have hre : ξ.re = (Real.sqrt 2 / 2) * v := by simp [ξ, Complex.mul_re, hd_re]
      rw [hre]
      have hrt2 : (9 : ℝ) < (5 * Real.sqrt 2 / 2) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt zero_le_two]
        norm_num
      have h3 : 3 < 5 * Real.sqrt 2 / 2 := by nlinarith [Real.sqrt_nonneg 2]
      nlinarith
    have hξ_re1 : 1 < ξ.re := by linarith
    have hξ_ne1 : ξ ≠ 1 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.one_re] at hre
      linarith
    have hpull : ‖Minor.pull d phiQClean v‖ = ‖(1 - (2 : ℂ) ^ (ξ - 1)) * phiPartClosed ξ‖ := by
      rw [Minor.pull, norm_mul, hd_norm, one_mul]
      dsimp only [phiQClean]
      rw [Function.update_of_ne hξ_ne1]
      dsimp only [phiQRaw]
      rw [phiPartClean_eq_phiPartClosed_of_one_lt_re hξ_re1]
    have h_split : (1 - (2 : ℂ) ^ (ξ - 1)) * phiPartClosed ξ =
        ((Real.pi : ℂ) * ((2 * (Real.pi : ℂ)) ^ (1 - ξ) - (2 : ℂ) ^ (ξ - 1) * (2 * (Real.pi : ℂ)) ^ (1 - ξ))) /
          Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2) * riemannZeta (ξ - 1) := by
      dsimp only [phiPartClosed]; ring
    rw [hpull, h_split, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hcpow1_le : ‖(2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ ≤ 1 := by
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
      rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos h2pi]
      exact Real.rpow_le_one_of_one_le_of_nonpos h2pi_ge1 (by simp; linarith)
    have hcpow2_le : ‖(2 : ℂ) ^ (ξ - 1) * (2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ ≤ 1 := by
      have h2pos : (0 : ℝ) < 2 := by positivity
      have h2pipos : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [norm_mul, show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos h2pipos,
        show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos h2pos]
      simp only [Complex.sub_re, Complex.one_re]
      rw [show ξ.re - 1 = -(1 - ξ.re) by ring, Real.rpow_neg h2pos.le,
        Real.mul_rpow h2pos.le Real.pi_pos.le]
      have h2ne : (2 : ℝ) ^ (1 - ξ.re) ≠ 0 := (Real.rpow_pos_of_pos h2pos _).ne'
      rw [← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
    have hdiff_le : ‖(2 * (Real.pi : ℂ)) ^ (1 - ξ) -
        (2 : ℂ) ^ (ξ - 1) * (2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ ≤ 2 := by
      calc _ ≤ ‖(2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ +
            ‖(2 : ℂ) ^ (ξ - 1) * (2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hcpow1_le hcpow2_le
        _ = 2 := by norm_num
    have hzeta_le : ‖riemannZeta (ξ - 1)‖ ≤ Z₂ := by
      have hs_re : 1 < (ξ - 1).re := by simp; linarith
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs_re]
      have hterm_le : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ (ξ - 1)‖ ≤ ((n + 1 : ℝ) ^ 2)⁻¹ := fun n => by
        rw [norm_div, norm_one, show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < n + 1)]
        simp only [one_div, Complex.sub_re, Complex.one_re]
        rw [← Real.rpow_neg (by positivity), show ((n + 1 : ℝ) ^ 2)⁻¹ = (n + 1 : ℝ) ^ (-2 : ℝ) by
          rw [Real.rpow_neg (by positivity)]; norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [show (0 : ℝ) ≤ n by positivity]) (by linarith)
      have hnorm_summ : Summable (fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ (ξ - 1)‖) :=
        hZ₂_summ.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le
      exact (norm_tsum_le_tsum_norm hnorm_summ).trans (hnorm_summ.tsum_le_tsum hterm_le hZ₂_summ)
    have hsin_ge : (1 / 2 : ℝ) ≤ ‖Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2)‖ := by
      let w : ℂ := (Real.pi : ℂ) * (ξ - 1) / 2
      have hw_im : 1 ≤ |w.im| := by
        have him : w.im = (Real.pi / 2) * (d.im * v) := by
          simp [w, ξ, Complex.mul_im]; ring
        rw [him, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2), hd_im,
          abs_of_pos (by linarith)]
        have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
        have hpi : 2 ≤ Real.pi := Real.two_le_pi
        calc (1 : ℝ) ≤ (2 / 2) * (1 / 2 * 5) := by norm_num
          _ ≤ (Real.pi / 2) * (Real.sqrt 2 / 2 * v) := by gcongr
      have hsin_sq : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sin_eq,
          ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.I_re, Complex.I_im, mul_one, zero_sub,
          Complex.add_im, Complex.mul_im, add_zero]
        have hcosh : Real.cosh w.im ^ 2 = 1 + Real.sinh w.im ^ 2 := by
          linarith [Real.cosh_sq_sub_sinh_sq w.im]
        have htrig : Real.sin w.re ^ 2 + Real.cos w.re ^ 2 = 1 := Real.sin_sq_add_cos_sq w.re
        nlinarith
      have hsinh_ge : (1 / 2 : ℝ) ≤ |Real.sinh w.im| := by
        rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hexp_diff : 1 ≤ |Real.exp w.im - Real.exp (-w.im)| := by
          rcases le_or_gt 0 w.im with hw0 | hw0
          · rw [abs_of_nonneg hw0] at hw_im
            have h_e1 : 2 ≤ Real.exp w.im :=
              (by linarith [Real.add_one_lt_exp (one_ne_zero)] : (2 : ℝ) ≤ Real.exp 1).trans
                (Real.exp_le_exp.mpr hw_im)
            have h_e2 : Real.exp (-w.im) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            exact (by linarith : (1 : ℝ) ≤ Real.exp w.im - Real.exp (-w.im)).trans (le_abs_self _)
          · rw [abs_of_neg hw0] at hw_im
            have h_e1 : 2 ≤ Real.exp (-w.im) :=
              (by linarith [Real.add_one_lt_exp (one_ne_zero)] : (2 : ℝ) ≤ Real.exp 1).trans
                (Real.exp_le_exp.mpr hw_im)
            have h_e2 : Real.exp w.im ≤ 1 := Real.exp_le_one_iff.mpr hw0.le
            have hneg : 1 ≤ -(Real.exp w.im - Real.exp (-w.im)) := by linarith
            exact hneg.trans (neg_le_abs _)
        linarith
      have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
        have hs1 : (1 / 2 : ℝ) ^ 2 ≤ Real.sinh w.im ^ 2 := by
          rw [← sq_abs (Real.sinh w.im)]
          nlinarith
        nlinarith [sq_nonneg (Real.sin w.re)]
      nlinarith [norm_nonneg (Complex.sin w)]
    have hinv_sin : (‖Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2)‖)⁻¹ ≤ 2 := by
      have hpos : (0 : ℝ) < 1 / 2 := by norm_num
      simpa using inv_anti₀ hpos hsin_ge
    calc Real.pi * ‖(2 * (Real.pi : ℂ)) ^ (1 - ξ) - (2 : ℂ) ^ (ξ - 1) * (2 * (Real.pi : ℂ)) ^ (1 - ξ)‖ /
          ‖Complex.sin ((Real.pi : ℂ) * (ξ - 1) / 2)‖ * ‖riemannZeta (ξ - 1)‖
        ≤ (Real.pi * 2 * 2) * Z₂ := by
          rw [div_eq_mul_inv]
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hdiff_le Real.pi_pos.le)
            hinv_sin (by positivity) (by positivity)) hzeta_le (norm_nonneg _) (by positivity)
      _ = 4 * Real.pi * Z₂ := by ring
      _ ≤ C := le_max_right _ _

/-- Genuine `MeromorphicBorelData` witness for `phiQClean`, the Borel kernel of
distinct-prime partitions `Q_prime(q) = ∏_{p prime} (1 + q^p)`. -/
@[expose] def phiQ_borelData : MeromorphicBorelData phiQClean ωQ resQ where
  θ₀ := Real.pi / 3
  θ := theta4
  ε := 1 / 2
  hθ_pos := theta4_pos
  hθ_lt := by unfold theta4; linarith [Real.pi_pos]
  hθ₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by simp [ωQ, ωPart]
  ω_mono := ωQ_strictMono
  res_ne_zero := resQ_ne_zero
  analyticOn := phiQClean_analyticOn
  simple_pole := phiQClean_simple_pole
  expType_plus := by
    have heq : Complex.exp (I * (theta4 : ℂ)) = dPlus := rfl
    rw [heq]
    exact phiQClean_ray_decay dPlus_re (by rw [dPlus_im, abs_of_pos (by positivity)]) norm_dPlus
  expType_minus := by
    have heq : Complex.exp (-I * (theta4 : ℂ)) = dMinus := rfl
    rw [heq]
    exact phiQClean_ray_decay dMinus_re
      (by rw [dMinus_im, abs_neg, abs_of_pos (by positivity)]) norm_dMinus

@[expose] def fDistinct (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)) * scaledRay distinctLogDerivSeries u

private lemma fDistinct_eq (u : ℝ) :
    fDistinct u = fPart u - (1 / 2 : ℂ) * fPart (u - Real.log 2) := by
  let t : ℝ := Real.exp (-u)
  let r : ℝ := Real.exp (-t)
  have ht : 0 < t := Real.exp_pos (-u)
  have hr0 : 0 < r := Real.exp_pos (-t)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hlog2 : (0 : ℝ) < 2 := by norm_num
  have ht2 : tRay (u - Real.log 2) = 2 * tRay u := by
    unfold tRay
    rw [show -(u - Real.log 2) = -u + Real.log 2 by ring, Real.exp_add, Real.exp_log hlog2]
    push_cast; ring
  have hq2 : qRay (u - Real.log 2) = (qRay u) ^ 2 := by
    unfold qRay
    rw [show -(u - Real.log 2) = -u + Real.log 2 by ring, Real.exp_add, Real.exp_log hlog2,
      show -(Real.exp (-u) * 2) = (2 : ℕ) * (-Real.exp (-u)) by push_cast; ring,
      Real.exp_nat_mul]
    push_cast; rfl
  have h_sum_sig : Summable (fun n : ℕ => sigmaP n * r ^ n) := by
    have habs := seriesJet_abs partLogDeriv_polyBound.to_diskCoeffBound 0
      (show ‖(r : ℂ)‖ < 1 by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1)
    refine habs.congr fun n => ?_
    simp only [seriesJet, Function.iterate_zero, id_eq, PrimeNome.term, coeff_partLogDeriv_eq,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sigmaP_nonneg n),
      norm_pow, abs_of_pos hr0]
  have h_sum_even : Summable (fun m : ℕ => (if 2 ∣ m then 2 * sigmaP (m / 2) else 0) * r ^ m) := by
    have h_mul2 : Summable (fun m : ℕ => 2 * (sigmaP (m / 2) * r ^ m)) := by
      obtain ⟨C, p, hC, hbd⟩ := partLogDeriv_polyBound
      have hdom : Summable (fun m : ℕ => (2 * C) * ((m : ℝ) + 1) ^ p * r ^ m) := by
        have hs := (summable_pow_mul_geometric_of_norm_lt_one p
          (show ‖r‖ < 1 by simpa [abs_of_pos hr0] using hr1)).mul_left (2 * C * r⁻¹)
        refine (hs.comp_injective (show Function.Injective (fun m : ℕ => m + 1) from
          fun _ _ h => Nat.add_right_cancel h)).congr fun m => ?_
        simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp [hr0.ne']
      refine hdom.of_nonneg_of_le
        (fun m => mul_nonneg zero_le_two (mul_nonneg (sigmaP_nonneg _) (pow_nonneg hr0.le _)))
        fun m => ?_
      have hk := hbd (m / 2)
      rw [coeff_partLogDeriv_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sigmaP_nonneg _)] at hk
      have hm_le : (((m / 2 : ℕ) : ℝ) + 1) ^ p ≤ ((m : ℝ) + 1) ^ p :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show m / 2 + 1 ≤ m + 1 by omega)) p
      calc 2 * (sigmaP (m / 2) * r ^ m)
          ≤ 2 * ((C * (((m / 2 : ℕ) : ℝ) + 1) ^ p) * r ^ m) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (pow_nonneg hr0.le _)) (by norm_num)
        _ ≤ 2 * ((C * ((m : ℝ) + 1) ^ p) * r ^ m) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le hC)
              (pow_nonneg hr0.le _)) (by norm_num)
        _ = (2 * C) * ((m : ℝ) + 1) ^ p * r ^ m := by ring
    refine h_mul2.of_nonneg_of_le
      (fun m => mul_nonneg
        (by split_ifs <;> [exact mul_nonneg zero_le_two (sigmaP_nonneg _); exact le_rfl])
        (pow_nonneg hr0.le _))
      fun m => ?_
    split_ifs
    · rw [mul_assoc]
    · rw [zero_mul]
      exact mul_nonneg zero_le_two (mul_nonneg (sigmaP_nonneg _) (pow_nonneg hr0.le _))
  have hf_val : fPart u = (tRay u) ^ 2 * ((∑' n : ℕ, sigmaP n * r ^ n : ℝ) : ℂ) := by
    unfold fPart scaledRay
    rw [show Complex.exp (-(u : ℂ)) = tRay u from by unfold tRay; rw [Complex.ofReal_exp, Complex.ofReal_neg],
      ← mul_assoc, ← pow_two]
    congr 1
    unfold value
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [PrimeNome.term, coeff_partLogDeriv_eq, qRay, r, t, ← Complex.ofReal_pow,
      Complex.ofReal_mul]
  have hf_shift : (1 / 2 : ℂ) * fPart (u - Real.log 2) =
      (tRay u) ^ 2 * ((∑' n : ℕ, (2 * sigmaP n) * (r ^ 2) ^ n : ℝ) : ℂ) := by
    have ht_eq : Complex.exp (-((u - Real.log 2 : ℝ) : ℂ)) = (tRay (u - Real.log 2) : ℂ) := by
      unfold tRay; rw [Complex.ofReal_exp, Complex.ofReal_neg]
    have hval2 : value partLogDerivSeries ((qRay u) ^ 2) =
        ((∑' n : ℕ, sigmaP n * (r ^ 2) ^ n : ℝ) : ℂ) := by
      unfold value
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun n => ?_
      dsimp only [PrimeNome.term, qRay]
      rw [coeff_partLogDeriv_eq, ← Complex.ofReal_pow r 2, ← Complex.ofReal_pow (r ^ 2) n,
        ← Complex.ofReal_mul]
    have hsum_r2 : Summable (fun n : ℕ => sigmaP n * (r ^ 2) ^ n) := by
      refine h_sum_sig.of_nonneg_of_le
        (fun n => mul_nonneg (sigmaP_nonneg _) (pow_nonneg (sq_nonneg _) _))
        fun n => ?_
      refine mul_le_mul_of_nonneg_left ?_ (sigmaP_nonneg n)
      rw [← pow_mul]
      exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    have h2sig : (∑' n : ℕ, (2 * sigmaP n) * (r ^ 2) ^ n) =
        2 * ∑' n : ℕ, sigmaP n * (r ^ 2) ^ n := by
      simp_rw [mul_assoc]
      exact tsum_mul_left
    calc (1 / 2 : ℂ) * fPart (u - Real.log 2)
        = (1 / 2 : ℂ) * (Complex.exp (-((u - Real.log 2 : ℝ) : ℂ)) *
            (tRay (u - Real.log 2) * value partLogDerivSeries (qRay (u - Real.log 2)))) := rfl
      _ = (1 / 2 : ℂ) * (tRay (u - Real.log 2) * (tRay (u - Real.log 2) *
            value partLogDerivSeries (qRay (u - Real.log 2)))) := by rw [ht_eq]
      _ = (1 / 2 : ℂ) * ((2 * (tRay u : ℂ)) * ((2 * (tRay u : ℂ)) *
            value partLogDerivSeries ((qRay u) ^ 2))) := by
          simp only [ht2, hq2]
      _ = (tRay u) ^ 2 * (2 * value partLogDerivSeries ((qRay u) ^ 2)) := by ring
      _ = (tRay u) ^ 2 * ((∑' n : ℕ, (2 * sigmaP n) * (r ^ 2) ^ n : ℝ) : ℂ) := by
          rw [hval2, h2sig, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have heven_eq : (∑' m : ℕ, (if 2 ∣ m then 2 * sigmaP (m / 2) else 0) * r ^ m) =
      ∑' n : ℕ, (2 * sigmaP n) * (r ^ 2) ^ n := by
    have hinj : Function.Injective (fun n : ℕ => 2 * n) :=
      fun _ _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have hsupp : ∀ m ∉ Set.range (fun n : ℕ => 2 * n),
        (if 2 ∣ m then 2 * sigmaP (m / 2) else 0) * r ^ m = 0 := by
      intro m hm
      have hnd : ¬ 2 ∣ m := fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩
      simp [hnd]
    have hs_comp : Summable ((fun m : ℕ => (if 2 ∣ m then 2 * sigmaP (m / 2) else 0) * r ^ m) ∘
        fun n : ℕ => 2 * n) := h_sum_even.comp_injective hinj
    have hsum := ((hinj.hasSum_iff hsupp).mp hs_comp.hasSum).tsum_eq
    rw [hsum]
    refine tsum_congr fun n => ?_
    simp only [Function.comp_def, dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ (by norm_num : 0 < 2),
      pow_mul]
  have hd_val : fDistinct u = (tRay u) ^ 2 * ((∑' m : ℕ, sigmaPDistinct m * r ^ m : ℝ) : ℂ) := by
    unfold fDistinct scaledRay
    rw [show Complex.exp (-(u : ℂ)) = tRay u from by unfold tRay; rw [Complex.ofReal_exp, Complex.ofReal_neg],
      ← mul_assoc, ← pow_two]
    congr 1
    unfold value
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [PrimeNome.term, distinctLogDerivSeries, PowerSeries.coeff_mk, qRay, r, t,
      ← Complex.ofReal_pow, Complex.ofReal_mul]
  rw [hd_val, hf_val, hf_shift, ← heven_eq, ← mul_sub, ← Complex.ofReal_sub,
    ← h_sum_sig.tsum_sub h_sum_even]
  congr 2
  refine tsum_congr fun m => ?_
  dsimp only [sigmaPDistinct]
  ring

lemma fDistinct_hasAsympExp (hpnt : PNTAllOrders) (j : ℕ) :
    HasAsympExp (iteratedDeriv j fDistinct) (d_u^[j] (formalSeries phiQClean)) := by
  have hf_eq : fDistinct = fun u : ℝ => fPart u - (1 / 2 : ℂ) * fPart (u - Real.log 2) :=
    funext fDistinct_eq
  have hcd_f : ContDiff ℝ ⊤ fPart := by
    have hcd_exp : ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (-(u : ℂ))) :=
      Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg)
    have hcd_sr : ContDiff ℝ ⊤ (scaledRay partLogDerivSeries) :=
      contDiff_iff_contDiffAt.mpr fun u =>
        (scaledRay_analytic partLogDeriv_polyBound.to_diskCoeffBound u).contDiffAt
    change ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (-(u : ℂ)) * scaledRay partLogDerivSeries u)
    exact hcd_exp.mul hcd_sr
  have hcd_shift : ContDiff ℝ ⊤ (fun u : ℝ => fPart (u - Real.log 2)) :=
    hcd_f.comp (contDiff_id.sub contDiff_const)
  have hiter_eq : iteratedDeriv j fDistinct = fun u : ℝ =>
      iteratedDeriv j fPart u +
        (-(1 / 2 : ℂ)) * iteratedDeriv j (fun t : ℝ => fPart (t - Real.log 2)) u := by
    funext u
    rw [hf_eq, show (fun t : ℝ => fPart t - (1 / 2 : ℂ) * fPart (t - Real.log 2)) =
        fun t => fPart t + (-(1 / 2 : ℂ)) * fPart (t - Real.log 2) by funext t; ring]
    rw [iteratedDeriv_fun_add (hcd_f.contDiffAt.of_le le_top)
      ((contDiff_const.mul hcd_shift).contDiffAt.of_le le_top),
      iteratedDeriv_const_mul_field]
  have hψ_an : AnalyticAt ℂ phiPartClean 0 :=
    phiPartClean_analyticOn 0 ⟨Or.inl (by simp [Metric.mem_ball]), by
      rintro ⟨m, hm⟩
      have hre := congrArg Complex.re hm
      simp only [Complex.zero_re, Complex.ofReal_re] at hre
      linarith [ωPart_ge_one m]⟩
  have hshift := hasAsympExp_shift (Real.log 2) hψ_an fPart_differentiable_iteratedDeriv
    (fPart_hasAsympExp hpnt) j
  have hasymp_sum := (fPart_hasAsympExp hpnt j).add ((HasAsympExp.const (-(1 / 2 : ℂ))).mul hshift)
  have hser_eq : d_u^[j] (formalSeries phiPartClean) +
      PowerSeries.C (-(1 / 2 : ℂ)) *
        d_u^[j] (formalSeries (fun ξ : ℂ => Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ)) =
      d_u^[j] (formalSeries phiQClean) := by
    have hd_smul : ∀ (m : ℕ) (c : ℂ) (S : PowerSeries ℂ),
        PowerSeries.C c * d_u^[m] S = d_u^[m] (PowerSeries.C c * S) := fun m c S => by
      induction m with
      | zero => simp
      | succ k ih =>
        calc PowerSeries.C c * d_u^[k + 1] S
            = PowerSeries.C c * d_u (d_u^[k] S) := by rw [Function.iterate_succ_apply']
          _ = d_u (PowerSeries.C c * d_u^[k] S) := by
              dsimp only [d_u]
              rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul,
                mul_zero, add_zero]
              ring
          _ = d_u (d_u^[k] (PowerSeries.C c * S)) := by rw [ih]
          _ = d_u^[k + 1] (PowerSeries.C c * S) := by rw [← Function.iterate_succ_apply' d_u k]
    rw [hd_smul j, ← d_u_iter_add]
    have hser_clean : formalSeries phiPartClean +
        PowerSeries.C (-(1 / 2 : ℂ)) *
          formalSeries (fun ξ : ℂ => Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ) =
        formalSeries phiQClean := by
      have hloc : (fun ξ : ℂ => phiPartClean ξ +
          (-(1 / 2 : ℂ)) * (Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ)) =ᶠ[𝓝 (0 : ℂ)]
          phiQClean := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with ξ hξ
        have hξ1 : ξ ≠ 1 := by
          intro h0
          rw [h0, Metric.mem_ball, dist_zero_right, norm_one] at hξ
          linarith
        have hpow_eq : (1 / 2 : ℂ) * Complex.exp ((Real.log 2 : ℂ) * ξ) = (2 : ℂ) ^ (ξ - 1) := by
          rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
            Complex.cpow_def_of_ne_zero (by norm_num : ((2 : ℝ) : ℂ) ≠ 0),
            ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2),
            mul_sub, mul_one, Complex.exp_sub,
            ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          push_cast; ring
        dsimp only [phiQClean, phiQRaw]
        rw [Function.update_of_ne hξ1]
        calc phiPartClean ξ + (-(1 / 2 : ℂ)) * (Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ)
            = (1 - (1 / 2 : ℂ) * Complex.exp ((Real.log 2 : ℂ) * ξ)) * phiPartClean ξ := by ring
          _ = (1 - (2 : ℂ) ^ (ξ - 1)) * phiPartClean ξ := by rw [hpow_eq]
      ext n
      cases n with
      | zero => simp [formalSeries]
      | succ k =>
        rw [map_add, PowerSeries.coeff_C_mul]
        simp only [formalSeries, PowerSeries.coeff_mk]
        have h1_an : AnalyticAt ℂ (fun ξ : ℂ => Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ) 0 :=
          ((analyticAt_const.mul analyticAt_id).cexp).mul hψ_an
        have h2_an : AnalyticAt ℂ (fun ξ : ℂ =>
            (-(1 / 2 : ℂ)) * (Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ)) 0 :=
          analyticAt_const.mul h1_an
        have heq_deriv : iteratedDeriv k phiPartClean 0 +
            (-(1 / 2 : ℂ)) * iteratedDeriv k
              (fun ξ : ℂ => Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ) 0 =
            iteratedDeriv k (fun ξ : ℂ => phiPartClean ξ +
              (-(1 / 2 : ℂ)) * (Complex.exp ((Real.log 2 : ℂ) * ξ) * phiPartClean ξ)) 0 := by
          have hadd := iteratedDeriv_fun_add (hψ_an.contDiffAt.of_le le_top)
            (h2_an.contDiffAt.of_le le_top) (x := (0 : ℂ)) (n := k)
          rw [iteratedDeriv_const_mul_field] at hadd
          exact hadd.symm
        rw [heq_deriv]
        exact hloc.iteratedDeriv_eq k
    rw [hser_clean]
  rw [hiter_eq, ← hser_eq]
  exact hasymp_sum

private lemma fDistinct_differentiable_iteratedDeriv (j : ℕ) :
    Differentiable ℝ (iteratedDeriv j fDistinct) := by
  have hcd_exp : ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (-(u : ℂ))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg)
  have hcd_sr : ContDiff ℝ ⊤ (scaledRay distinctLogDerivSeries) :=
    contDiff_iff_contDiffAt.mpr fun u =>
      (scaledRay_analytic distinctLogDeriv_polyBound.to_diskCoeffBound u).contDiffAt
  have hcd_f : ContDiff ℝ ⊤ fDistinct := by
    change ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (-(u : ℂ)) * scaledRay distinctLogDerivSeries u)
    exact hcd_exp.mul hcd_sr
  exact hcd_f.differentiable_iteratedDeriv j (by simp)

/-- **End-to-End Differential Transcendence of `G_Q(q) = ∑_{p prime} p q^p / (1 + q^p)`**:
Assuming `PNTAllOrders`, `seriesCoordinates distinctLogDerivSeries` is algebraically
independent over `ℂ`. -/
theorem distinctLogDeriv_algebraicIndependent_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ (seriesCoordinates distinctLogDerivSeries) := by
  by_contra hdep
  obtain ⟨J, P, hP_ne, hP_ev⟩ := autonomous_transfer distinctLogDeriv_polyBound hdep
  have hg_eq : ∀ u : ℝ, scaledRay distinctLogDerivSeries u = Complex.exp (u : ℂ) * fDistinct u :=
    fun u => by
      unfold fDistinct
      rw [← mul_assoc, ← Complex.exp_add, show (u : ℂ) + -(u : ℂ) = 0 by ring, Complex.exp_zero, one_mul]
  exact hP_ne (no_autonomous_ade_of_exp_mul_asymp phiQ_borelData hg_eq
    fDistinct_differentiable_iteratedDeriv (fDistinct_hasAsympExp hpnt) P hP_ev)

/-- **End-to-End Differential Transcendence of Distinct-Prime Partitions (OEIS A000586)**:
Assuming `PNTAllOrders`, the generating series `Q_prime(q) = ∏_{p prime} (1 + q^p)`
(`distinctPrimesSeries`) is differentially transcendental over `ℂ(q)`: its differential
coordinates `(q, Q_prime, Q_prime', Q_prime'', ...)` are algebraically independent over `ℂ`. -/
theorem distinctPrimes_algebraicIndependent_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ (seriesCoordinates distinctPrimesSeries) := by
  by_contra hdep
  obtain ⟨J, R, hR_ne, hR_ev⟩ := autonomous_transfer_log_deriv
    distinctPrimesSeries_diskBound distinctLogDeriv_polyBound.to_diskCoeffBound
    distinctPrimesSeries_ode distinctPrimesSeries_qRay_ne_zero hdep
  have hg_eq : ∀ u : ℝ, scaledRay distinctLogDerivSeries u = Complex.exp (u : ℂ) * fDistinct u :=
    fun u => by
      unfold fDistinct
      rw [← mul_assoc, ← Complex.exp_add, show (u : ℂ) + -(u : ℂ) = 0 by ring, Complex.exp_zero, one_mul]
  exact hR_ne (no_autonomous_ade_of_exp_mul_asymp phiQ_borelData hg_eq
    fDistinct_differentiable_iteratedDeriv (fDistinct_hasAsympExp hpnt) R hR_ev)

end
end PakPrimes.PartitionsIntoPrimes

