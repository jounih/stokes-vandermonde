module

public import PakPrimes.HigherOrderStrongDTrans
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Unconditional (Zero-RH) Strong `ℂ({t})` Differential Transcendence of Prime Von Mangoldt Series

This module proves **100% unconditional** strong differential transcendence over convergent
meromorphic germs `ℂ({t})` — with ZERO `RiemannHypothesis`, ZERO Hardy infinitude, and ZERO
numerical zero tables — for the exact prime-number Borel kernel `phiLambda`, its formal series
`G_Lambda = formalSeries phiLambda`, its OGF `ogfOfEGF phiLambda`, and its regularized real-axis
Laplace integral `G_Lambda_laplace` from `PakPrimes.RiemannHypothesisStokes`.

## Mathematical Architecture
1. **Elementary Critical-Strip Box Certificate (`riemannZeta_ne_zero_on_box`)**:
   Using the 2nd-difference Euler-accelerated Dirichlet eta expansion
   `2 * (1 - 2^(1 - s)) * ζ(s) = (2 - 2 * 2^(-s) + 3^(-s)) + ∑_{k ≥ 1} d_k(s)`,
   where `d_k(s) = (2k+1)^(-s) - 2*(2k+2)^(-s) + (2k+3)^(-s)` satisfies the 2nd-order FTC bound
   `‖d_k(s)‖ ≤ ‖s * (s + 1)‖ * (2k+1)^(-Re s - 2)` and pure arithmetic telescoping
   `∑_{k ≥ 1} 1 / (2k+1)^2 ≤ 1 / 4`, together with the algebraic inequality
   `2 - 2 * 2^(-σ) + 3^(-σ) ≥ 1 + (1 - 2^(-σ))^2 ≥ 1`, we prove unconditionally that
   `Re(twoEta s) ≥ 1 - (t * log 3)^2 / 2 - ‖s * (s + 1)‖ / 4 > 0` on the entire closed box
   `[0, 1] × [-1/2, 1/2]`, yielding `riemannZeta s ≠ 0` away from `s = 1`.
2. **Negative-Real-Axis Trivial-Zero Comb (`θ₀ = π`, `α₀ = π / 4`, `ε = 1 / 4`)**:
   - Every point of `rotatedPuncturedWedge π (π / 4) (1 / 4) (fun m => 2 * m + 5 / 2)` lands
     either in the critical-strip box `[0, 1] × [-1/2, 1/2]` or in `{Re s ≤ 0}` away from the
     trivial zeros `s = -2 * (m + 1)` (`riemannZeta_eq_zero_iff_of_re_nonpos`).
   - Differentiating Riemann's functional equation `riemannZeta_one_sub` at `w₀ = 2 * m + 3`
     proves `deriv riemannZeta (-2 * (m + 1)) ≠ 0`, so every trivial zero is simple and
     `phiLambda` has exact principal part `-1 / (ξ - (-(2 * m + 5 / 2)))`.
3. **Unconditional Flanking-Ray `ExpType` Bounds (`σ = π ± π / 8`)**:
   Both flanking rays lie strictly inside the punctured negative-axis wedge, giving continuity on
   `[0, R₀]` unconditionally; for `v > R₀`, `logDeriv_riemannZeta_one_sub`, the right-half-plane
   Dirichlet series bound, linear digamma growth, and boundedness of `tan` on `|Im z| ≥ 1` give
   linear `O(v)` growth (hence `ExpType`).
4. **Unconditional Real-Axis Laplace Asymptotics (`G_Lambda_laplace_hasAsympExp_unconditional`)**:
   Shrinking the auxiliary star-shaped domain to `borelWedge (π / 4) (1 / 4)` keeps the entire
   domain inside `{Re s ≥ 1} ∪ ([0, 1] × [-1/2, 1/2])`, removing `RiemannHypothesis` completely.
5. **Unconditional Master Theorems**:
   Instantiating `HigherOrderStokes` and `HigherOrderStrongDTrans` with
   `phiLambda_unconditional_higherOrderBorelData` yields zero-hypothesis strong `ℂ({t})`
   differential transcendence and `ℂ{1/u}` / `ℂ(u)` / `ℂ[u]` / `ℂ` ADE obstructions for
   `ogfOfEGF phiLambda`, `G_Lambda = formalSeries phiLambda`, and `G_Lambda_laplace`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.UnconditionalPrimeDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.HigherOrderStokes
open PakPrimes.HigherOrderStrongDTrans
open PakPrimes.FishburnStrongDTrans
open PakPrimes.PakYeliussizovEGF
open PakPrimes.HolderGamma
open PakPrimes.RiemannHypothesisStokes
open scoped Topology Interval

noncomputable section

/-! ### 1. Elementary 2nd-Difference Dirichlet Eta Certificate on `[0, 1] × [-1/2, 1/2]` -/

/-- Second finite difference `d_k(s) = (2k+1)^{-s} - 2(2k+2)^{-s} + (2k+3)^{-s}`. -/
private def etaDiff2 (k : ℕ) (s : ℂ) : ℂ :=
  ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - 2 * ((2 * k + 2 : ℕ) : ℂ) ^ (-s) + ((2 * k + 3 : ℕ) : ℂ) ^ (-s)

/-- Euler-accelerated doubled Dirichlet eta function
`twoEta(s) = (2 - 2 * 2^(-s) + 3^(-s)) + ∑_{k ≥ 0} etaDiff2 (k + 1) s`,
converging locally uniformly on `{s : ℂ | -1 < s.re}`. -/
private def twoEta (s : ℂ) : ℂ :=
  (2 - 2 * (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)) + ∑' k : ℕ, etaDiff2 (k + 1) s

private lemma finset_sum_etaDiff2 (s : ℂ) (N : ℕ) :
    (2 - 2 * (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)) + ∑ k ∈ Finset.range N, etaDiff2 (k + 1) s =
      2 * (∑ k ∈ Finset.range (N + 1),
        (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s))) +
        ((2 * N + 3 : ℕ) : ℂ) ^ (-s) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add, Finset.range_one,
      Finset.sum_singleton, mul_zero, Nat.cast_one, Complex.one_cpow, Nat.cast_ofNat]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    unfold etaDiff2
    have h1 : 2 * (N + 1) + 1 = 2 * N + 3 := by omega
    have h2 : 2 * (N + 1) + 2 = 2 * N + 4 := by omega
    have h3 : 2 * (N + 1) + 3 = 2 * N + 5 := by omega
    rw [h1, h2, h3]
    ring

private lemma etaDiff2_eq_iterated_integral (k : ℕ) (s : ℂ) :
    etaDiff2 k s =
      s * (s + 1) *
        ∫ u in (0 : ℝ)..1,
          ∫ v in (0 : ℝ)..1, ((((2 * k + 1 : ℕ) : ℝ) + u + v : ℝ) : ℂ) ^ (-s - 2) := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  have ha_pos : 0 < a := by positivity
  have hinner : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      ∫ v in (0 : ℝ)..1, s * (s + 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 2)) =
        (-s) * (((a + u + 1 : ℝ) : ℂ) ^ (-s - 1)) - (-s) * (((a + u : ℝ) : ℂ) ^ (-s - 1)) := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    have hderiv : ∀ v ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => (-s) * (((a + u + x : ℝ) : ℂ) ^ (-s - 1)))
          (s * (s + 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 2))) v := by
      intro v hv
      rw [Set.uIcc_of_le zero_le_one] at hv
      have hpos : 0 < a + u + v := by linarith [hu.1, hv.1]
      have hslit : ((a + u + v : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hpos)
      have hlin : HasDerivAt (fun x : ℝ => a + u + x) 1 v := by
        simpa using (hasDerivAt_id v).const_add (a + u)
      have hcpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s - 1))
          ((-s - 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 1 - 1))) (a + u + v) :=
        ((Complex.hasStrictDerivAt_cpow_const (c := -s - 1) hslit).hasDerivAt).comp_ofReal
      have hcomp : HasDerivAt (fun x : ℝ => ((a + u + x : ℝ) : ℂ) ^ (-s - 1))
          ((-s - 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 1 - 1))) v :=
        (hcpow.scomp v hlin).congr_deriv (one_smul _ _)
      have hmul := hcomp.const_mul (-s)
      have hcoef : (-s) * ((-s - 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 1 - 1))) =
          s * (s + 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 2)) := by
        have hexp : (-s - 1 - 1 : ℂ) = -s - 2 := by ring
        rw [hexp]; ring
      exact hmul.congr_deriv hcoef
    have hcont : ContinuousOn (fun v : ℝ => s * (s + 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 2)))
        (Set.uIcc (0 : ℝ) 1) := by
      refine continuousOn_const.mul ?_
      intro v hv
      rw [Set.uIcc_of_le zero_le_one] at hv
      have hpos : 0 < a + u + v := by linarith [hu.1, hv.1]
      have hslit : ((a + u + v : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hpos)
      have hc : ContinuousAt (fun z : ℂ => z ^ (-s - 2)) ((a + u + v : ℝ) : ℂ) :=
        (Complex.hasStrictDerivAt_cpow_const (c := -s - 2) hslit).hasDerivAt.continuousAt
      have hlin : ContinuousAt (fun x : ℝ => ((a + u + x : ℝ) : ℂ)) v :=
        ContinuousAt.comp (g := fun y : ℝ => (y : ℂ)) (f := fun x : ℝ => a + u + x)
          Complex.continuous_ofReal.continuousAt (continuousAt_const.add continuousAt_id)
      exact (ContinuousAt.comp (g := fun z : ℂ => z ^ (-s - 2))
        (f := fun x : ℝ => ((a + u + x : ℝ) : ℂ)) hc hlin).continuousWithinAt
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    simpa [add_zero] using hint
  have houter_deriv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => (((a + x + 1 : ℝ) : ℂ) ^ (-s)) - (((a + x : ℝ) : ℂ) ^ (-s)))
        ((-s) * (((a + u + 1 : ℝ) : ℂ) ^ (-s - 1)) - (-s) * (((a + u : ℝ) : ℂ) ^ (-s - 1))) u := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    have hpos1 : 0 < a + u + 1 := by linarith [hu.1]
    have hpos0 : 0 < a + u := by linarith [hu.1]
    have hslit1 : ((a + u + 1 : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hpos1)
    have hslit0 : ((a + u : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hpos0)
    have hlin1 : HasDerivAt (fun x : ℝ => a + x + 1) 1 u := by
      simpa using ((hasDerivAt_id u).const_add a).add_const (1 : ℝ)
    have hlin0 : HasDerivAt (fun x : ℝ => a + x) 1 u := by
      simpa using (hasDerivAt_id u).const_add a
    have hcpow1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (((a + u + 1 : ℝ) : ℂ) ^ (-s - 1))) (a + u + 1) :=
      ((Complex.hasStrictDerivAt_cpow_const (c := -s) hslit1).hasDerivAt).comp_ofReal
    have hcpow0 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (((a + u : ℝ) : ℂ) ^ (-s - 1))) (a + u) :=
      ((Complex.hasStrictDerivAt_cpow_const (c := -s) hslit0).hasDerivAt).comp_ofReal
    have hd1 : HasDerivAt (fun x : ℝ => ((a + x + 1 : ℝ) : ℂ) ^ (-s))
        ((-s) * (((a + u + 1 : ℝ) : ℂ) ^ (-s - 1))) u := by
      have h := hcpow1.scomp u hlin1
      exact h.congr_deriv (one_smul _ _)
    have hd0 : HasDerivAt (fun x : ℝ => ((a + x : ℝ) : ℂ) ^ (-s))
        ((-s) * (((a + u : ℝ) : ℂ) ^ (-s - 1))) u := by
      have h := hcpow0.scomp u hlin0
      exact h.congr_deriv (one_smul _ _)
    exact hd1.fun_sub hd0
  have houter_cont : ContinuousOn
      (fun u : ℝ => (-s) * (((a + u + 1 : ℝ) : ℂ) ^ (-s - 1)) - (-s) * (((a + u : ℝ) : ℂ) ^ (-s - 1)))
      (Set.uIcc (0 : ℝ) 1) := by
    refine (continuousOn_const.mul ?_).sub (continuousOn_const.mul ?_)
    · intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      have hpos : 0 < a + u + 1 := by linarith [hu.1]
      have hslit : ((a + u + 1 : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hpos)
      have hc := (Complex.hasStrictDerivAt_cpow_const (c := -s - 1) hslit).hasDerivAt.continuousAt
      have hlin : ContinuousAt (fun x : ℝ => ((a + x + 1 : ℝ) : ℂ)) u :=
        ContinuousAt.comp (g := fun y : ℝ => (y : ℂ)) (f := fun x : ℝ => a + x + 1)
          Complex.continuous_ofReal.continuousAt
          ((continuousAt_const.add continuousAt_id).add continuousAt_const)
      exact (ContinuousAt.comp (g := fun z : ℂ => z ^ (-s - 1))
        (f := fun x : ℝ => ((a + x + 1 : ℝ) : ℂ)) hc hlin).continuousWithinAt
    · intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      have hpos : 0 < a + u := by linarith [hu.1]
      have hslit : ((a + u : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hpos)
      have hc := (Complex.hasStrictDerivAt_cpow_const (c := -s - 1) hslit).hasDerivAt.continuousAt
      have hlin : ContinuousAt (fun x : ℝ => ((a + x : ℝ) : ℂ)) u :=
        ContinuousAt.comp (g := fun y : ℝ => (y : ℂ)) (f := fun x : ℝ => a + x)
          Complex.continuous_ofReal.continuousAt (continuousAt_const.add continuousAt_id)
      exact (ContinuousAt.comp (g := fun z : ℂ => z ^ (-s - 1))
        (f := fun x : ℝ => ((a + x : ℝ) : ℂ)) hc hlin).continuousWithinAt
  have houter := intervalIntegral.integral_eq_sub_of_hasDerivAt houter_deriv houter_cont.intervalIntegrable
  have hcongr : (∫ u in (0 : ℝ)..1,
      ∫ v in (0 : ℝ)..1, s * (s + 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 2))) =
      ∫ u in (0 : ℝ)..1,
        ((-s) * (((a + u + 1 : ℝ) : ℂ) ^ (-s - 1)) - (-s) * (((a + u : ℝ) : ℂ) ^ (-s - 1))) :=
    intervalIntegral.integral_congr fun u hu => hinner u hu
  have hpull : (∫ u in (0 : ℝ)..1,
      ∫ v in (0 : ℝ)..1, s * (s + 1) * (((a + u + v : ℝ) : ℂ) ^ (-s - 2))) =
      s * (s + 1) * ∫ u in (0 : ℝ)..1,
        ∫ v in (0 : ℝ)..1, (((a + u + v : ℝ) : ℂ) ^ (-s - 2)) := by
    simp_rw [intervalIntegral.integral_const_mul]
  have hval : ((((a + 1 + 1 : ℝ) : ℂ) ^ (-s)) - (((a + 1 : ℝ) : ℂ) ^ (-s))) -
      ((((a + 0 + 1 : ℝ) : ℂ) ^ (-s)) - (((a + 0 : ℝ) : ℂ) ^ (-s))) = etaDiff2 k s := by
    dsimp only [a, etaDiff2]
    have hc1 : ((((2 * k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) = ((2 * k + 2 : ℕ) : ℂ) := by
      push_cast; ring
    have hc2 : ((((2 * k + 1 : ℕ) : ℝ) + 1 + 1 : ℝ) : ℂ) = ((2 * k + 3 : ℕ) : ℂ) := by
      push_cast; ring
    have hc0 : ((((2 * k + 1 : ℕ) : ℝ) + 0 : ℝ) : ℂ) = ((2 * k + 1 : ℕ) : ℂ) := by
      push_cast; ring
    have hc01 : ((((2 * k + 1 : ℕ) : ℝ) + 0 + 1 : ℝ) : ℂ) = ((2 * k + 2 : ℕ) : ℂ) := by
      push_cast; ring
    rw [hc1, hc2, hc0, hc01]
    ring
  rw [← hval, ← houter, ← hcongr, hpull]

private lemma norm_etaDiff2_le (k : ℕ) {s : ℂ} (hs : -2 < s.re) :
    ‖etaDiff2 k s‖ ≤ ‖s * (s + 1)‖ * (((2 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 2))) := by
  rw [etaDiff2_eq_iterated_integral, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  have ha_pos : 0 < a := by positivity
  have hexp_neg : -(s.re + 2) ≤ 0 := by linarith
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := a ^ (-(s.re + 2)))
    (f := fun u : ℝ => ∫ v in (0 : ℝ)..1, (((a + u + v : ℝ) : ℂ) ^ (-s - 2))) fun u hu => by
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hinner := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := a ^ (-(s.re + 2)))
        (f := fun v : ℝ => (((a + u + v : ℝ) : ℂ) ^ (-s - 2))) fun v hv => by
          rw [Set.uIoc_of_le zero_le_one] at hv
          have hpos : 0 < a + u + v := by linarith [hu.1, hv.1]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
          have hre : (-s - 2).re = -(s.re + 2) := by simp; ring
          rw [hre]
          exact Real.rpow_le_rpow_of_nonpos ha_pos (by linarith [hu.1, hv.1]) hexp_neg
      simpa using hinner
  simpa [a] using houter

private lemma summable_odd_succ_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ => (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ (-p))) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hp
  have hinj : Function.Injective (fun k : ℕ => 2 * (k + 1) + 1) := fun a b h => by
    dsimp at h; omega
  exact hnat.comp_injective hinj

private lemma twoEta_differentiableOn :
    DifferentiableOn ℂ twoEta {s : ℂ | -1 < s.re} := by
  intro s₀ hs₀
  change -1 < s₀.re at hs₀
  let r : ℝ := min ((s₀.re + 1) / 2) 1
  have hr_pos : 0 < r := lt_min (by linarith) one_pos
  have hr_le : r ≤ (s₀.re + 1) / 2 := min_le_left _ _
  have hball_re : ∀ s ∈ Metric.ball s₀ r, (s₀.re - 1) / 2 < s.re := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h1 := (abs_lt.mp (hre.trans_lt hs)).1
    linarith
  have hball_norm : ∀ s ∈ Metric.ball s₀ r, ‖s * (s + 1)‖ ≤ (‖s₀‖ + r) * (‖s₀‖ + r + 1) := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hs_le : ‖s‖ ≤ ‖s₀‖ + r := by
      have htri : ‖s‖ ≤ ‖s - s₀‖ + ‖s₀‖ := by simpa [sub_add_cancel] using norm_add_le (s - s₀) s₀
      linarith
    have hs1_le : ‖s + 1‖ ≤ ‖s₀‖ + r + 1 := by
      have htri : ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le s 1
      rw [norm_one] at htri
      linarith
    rw [norm_mul]
    exact mul_le_mul hs_le hs1_le (norm_nonneg _) (by positivity)
  let M : ℝ := (‖s₀‖ + r) * (‖s₀‖ + r + 1)
  let p : ℝ := 1 + (s₀.re + 1) / 2
  have hp : 1 < p := by dsimp only [p]; linarith
  have hu : Summable (fun k : ℕ => M * (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ (-p))) :=
    (summable_odd_succ_rpow_neg hp).mul_left M
  have htail_diff : DifferentiableOn ℂ (fun s => ∑' k : ℕ, etaDiff2 (k + 1) s) (Metric.ball s₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu (fun k => ?_) Metric.isOpen_ball
      (fun k s hs => ?_)
    · have h1 : ((2 * (k + 1) + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * (k + 1) + 1 ≠ 0 by omega)
      have h2 : ((2 * (k + 1) + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * (k + 1) + 2 ≠ 0 by omega)
      have h3 : ((2 * (k + 1) + 3 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * (k + 1) + 3 ≠ 0 by omega)
      refine ((differentiableOn_id.neg.const_cpow (Or.inl h1)).sub
        ((differentiableOn_const (2 : ℂ)).mul (differentiableOn_id.neg.const_cpow (Or.inl h2)))).add
        (differentiableOn_id.neg.const_cpow (Or.inl h3))
    · have hre_s : (s₀.re - 1) / 2 < s.re := hball_re s hs
      have hre_gt : -2 < s.re := by linarith
      have hle1 := norm_etaDiff2_le (k + 1) hre_gt
      have hbase_ge1 : (1 : ℝ) ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * (k + 1) + 1 by omega)
      have hrpow_le : (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ (-(s.re + 2))) ≤
          (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ (-p)) :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge1 (by dsimp only [p]; linarith)
      exact hle1.trans (mul_le_mul (hball_norm s hs) hrpow_le (by positivity) (by positivity))
  have hlead_diff : DifferentiableOn ℂ (fun s : ℂ => 2 - 2 * (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s))
      (Metric.ball s₀ r) :=
    ((differentiableOn_const (2 : ℂ)).sub
      ((differentiableOn_const (2 : ℂ)).mul
        (differentiableOn_id.neg.const_cpow (Or.inl (by norm_num))))).add
      (differentiableOn_id.neg.const_cpow (Or.inl (by norm_num)))
  exact ((hlead_diff.add htail_diff).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))).differentiableWithinAt

private lemma twoEta_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    2 * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = twoEta s := by
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
  have heta_val : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s =
      (∑' k : ℕ, f (2 * k)) - (∑' k : ℕ, f (2 * k + 1)) := by
    rw [hpow]
    linear_combination hsplit + 2 * hodd_eq
  have hdiff_sum : Summable (fun k : ℕ => etaDiff2 (k + 1) s) := by
    have hp : 1 < s.re + 2 := by linarith
    refine Summable.of_norm_bounded ((summable_odd_succ_rpow_neg hp).mul_left ‖s * (s + 1)‖)
      (fun k => norm_etaDiff2_le (k + 1) (by linarith))
  have htend_lhs : Tendsto
      (fun N : ℕ => (2 - 2 * (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)) +
        ∑ k ∈ Finset.range N, etaDiff2 (k + 1) s)
      atTop (𝓝 (twoEta s)) := by
    unfold twoEta
    exact tendsto_const_nhds.add hdiff_sum.hasSum.tendsto_sum_nat
  have htend_pair : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
        (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      atTop (𝓝 ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) := by
    have hsub_sum : HasSum (fun k : ℕ => f (2 * k) - f (2 * k + 1))
        ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
      rw [heta_val]
      exact heven_sub.hasSum.sub hodd_sub.hasSum
    have hcomp := hsub_sum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine hcomp.congr fun N => ?_
    simp only [Function.comp_def, f]
  have htend_rem : Tendsto (fun N : ℕ => ((2 * N + 3 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm_eq : (fun N : ℕ => ‖((2 * N + 3 : ℕ) : ℂ) ^ (-s)‖) =
        fun N : ℕ => ((2 * N + 3 : ℕ) : ℝ) ^ (-s.re) := by
      funext N
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      simp
    rw [hnorm_eq]
    have hnat_top : Tendsto (fun N : ℕ => ((2 * N + 3 : ℕ) : ℝ)) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt b
      refine ⟨N₀, fun N hN => ?_⟩
      have h1 : (N₀ : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by exact_mod_cast (show N₀ ≤ 2 * N + 3 by omega)
      linarith
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < s.re)).comp hnat_top
  have htend_rhs : Tendsto
      (fun N : ℕ => 2 * (∑ k ∈ Finset.range (N + 1),
        (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s))) +
        ((2 * N + 3 : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 (2 * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) + 0)) :=
    (tendsto_const_nhds.mul htend_pair).add htend_rem
  rw [add_zero, ← mul_assoc] at htend_rhs
  have heq_fn : (fun N : ℕ => (2 - 2 * (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)) +
      ∑ k ∈ Finset.range N, etaDiff2 (k + 1) s) =
      fun N : ℕ => 2 * (∑ k ∈ Finset.range (N + 1),
        (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s))) +
        ((2 * N + 3 : ℕ) : ℂ) ^ (-s) := funext (finset_sum_etaDiff2 s)
  rw [heq_fn] at htend_lhs
  exact tendsto_nhds_unique htend_rhs htend_lhs

private lemma isPreconnected_re_gt_neg_one_sdiff_one :
    IsPreconnected ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) := by
  let U₁ : Set ℂ := {s : ℂ | -1 < s.re ∧ 0 < s.im}
  let U₂ : Set ℂ := {s : ℂ | -1 < s.re ∧ s.im < 0}
  let U₃ : Set ℂ := {s : ℂ | 1 < s.re}
  let U₄ : Set ℂ := {s : ℂ | -1 < s.re ∧ s.re < 1}
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
      have h1 := hconv_pos a b (x.re + 1) (y.re + 1) ha hb hab (by linarith [hx.1]) (by linarith [hy.1])
      nlinarith
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      exact hconv_pos a b x.im y.im ha hb hab hx.2 hy.2
  have hU₂ : IsPreconnected U₂ := by
    refine Convex.isPreconnected fun x hx y hy a b ha hb hab => ?_
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      have h1 := hconv_pos a b (x.re + 1) (y.re + 1) ha hb hab (by linarith [hx.1]) (by linarith [hy.1])
      nlinarith
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
    change -1 < (a • x + b • y).re ∧ (a • x + b • y).re < 1
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    refine ⟨?_, ?_⟩
    · have h1 := hconv_pos a b (x.re + 1) (y.re + 1) ha hb hab (by linarith [hx.1]) (by linarith [hy.1])
      nlinarith
    · have h1 := hconv_pos a b (1 - x.re) (1 - y.re) ha hb hab (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)
      nlinarith
  have h13 : IsPreconnected (U₁ ∪ U₃) := hU₁.union (2 + I) (by simp [U₁]; norm_num) (by simp [U₃]) hU₃
  have h132 : IsPreconnected ((U₁ ∪ U₃) ∪ U₂) :=
    h13.union (2 - I) (Or.inr (by simp [U₃])) (by simp [U₂]; norm_num) hU₂
  have h1324 : IsPreconnected (((U₁ ∪ U₃) ∪ U₂) ∪ U₄) :=
    h132.union (I) (Or.inl (Or.inl (by simp [U₁]))) (by simp [U₄]) hU₄
  have heq : (((U₁ ∪ U₃) ∪ U₂) ∪ U₄) = {s : ℂ | -1 < s.re} \ {(1 : ℂ)} := by
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

private lemma twoEta_eq_of_neg_one_lt_re {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    2 * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = twoEta s := by
  let U : Set ℂ := {z : ℂ | -1 < z.re} \ {(1 : ℂ)}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hLHS : AnalyticOnNhd ℂ (fun z : ℂ => 2 * (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - w)) z :=
      (differentiableAt_const (1 : ℂ)).sub differentiableAt_id |>.const_cpow (Or.inl (by norm_num))
    exact (((differentiableAt_const (2 : ℂ)).mul
      ((differentiableAt_const (1 : ℂ)).sub hpow)).mul
      (differentiableAt_riemannZeta hz.2)).differentiableWithinAt
  have hRHS : AnalyticOnNhd ℂ twoEta U :=
    (twoEta_differentiableOn.mono Set.sdiff_subset).analyticOnNhd hU_open
  have h2_mem : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by norm_num⟩
  have hev : (fun z : ℂ => 2 * (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) =ᶠ[𝓝 (2 : ℂ)] twoEta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    exact twoEta_eq_of_one_lt_re hz
  exact hLHS.eqOn_of_preconnected_of_eventuallyEq hRHS isPreconnected_re_gt_neg_one_sdiff_one
    h2_mem hev ⟨hs, hs1⟩

private lemma tsum_inv_odd_sq_le_quarter :
    ∑' k : ℕ, (1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
  let tel : ℕ → ℝ := fun k => (1 / 4 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ))
  have htel_nn : ∀ k : ℕ, 0 ≤ tel k := fun k => by
    dsimp only [tel]
    have hle : (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
    linarith
  have htel_sum : ∀ N : ℕ, ∑ k ∈ Finset.range N, tel k =
      (1 / 4 : ℝ) * (1 - 1 / ((N + 1 : ℕ) : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp only [tel]
      ring
  have htel_tend : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, tel k) atTop (𝓝 (1 / 4 : ℝ)) := by
    simp_rw [htel_sum]
    have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
    have h := (tendsto_const_nhds (x := (1 / 4 : ℝ))).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv)
    simpa using h
  have htel_hasSum : HasSum tel (1 / 4 : ℝ) :=
    (hasSum_iff_tendsto_nat_of_nonneg htel_nn (1 / 4 : ℝ)).mpr htel_tend
  have hle : ∀ k : ℕ, (1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2 ≤ tel k := fun k => by
    dsimp only [tel]
    have h1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have htel_eq : (1 / 4 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) =
        1 / (4 * ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
      have hdiff : ((k + 2 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
      field_simp [h1.ne', h2.ne']
      linarith
    rw [htel_eq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast
    nlinarith
  have hodd_sum : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle htel_hasSum.summable
  calc ∑' k : ℕ, (1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2
      ≤ ∑' k : ℕ, tel k := hodd_sum.tsum_le_tsum hle htel_hasSum.summable
    _ = 1 / 4 := htel_hasSum.tsum_eq

private lemma ofReal_cpow_neg_re {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((a : ℂ) ^ (-s)).re = a ^ (-s.re) * Real.cos (s.im * Real.log a) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    ← Complex.ofReal_log ha.le, Complex.exp_re]
  have hre : ((Real.log a : ℂ) * (-s)).re = Real.log a * (-s.re) := by simp
  have him : ((Real.log a : ℂ) * (-s)).im = -(s.im * Real.log a) := by simp [mul_comm]
  rw [hre, him, Real.cos_neg, ← Real.rpow_def_of_pos ha]

private lemma re_lead_ge {s : ℂ} (hre0 : 0 ≤ s.re) :
    1 - (s.im * Real.log 3) ^ 2 / 2 ≤
      (2 - 2 * (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)).re := by
  have h2re : ((2 : ℂ) ^ (-s)).re = (2 : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log 2) := by
    simpa using ofReal_cpow_neg_re (a := (2 : ℝ)) (by norm_num) s
  have h3re : ((3 : ℂ) ^ (-s)).re = (3 : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log 3) := by
    simpa using ofReal_cpow_neg_re (a := (3 : ℝ)) (by norm_num) s
  have hexp : (2 - 2 * (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)).re =
      2 - 2 * (2 : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log 2) +
        (3 : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log 3) := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, h2re, h3re]
    ring
  rw [hexp]
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ (-s.re) := by positivity
  have h3pow_nn : 0 ≤ (3 : ℝ) ^ (-s.re) := by positivity
  have h3pow_le1 : (3 : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hcos2 : Real.cos (s.im * Real.log 2) ≤ 1 := Real.cos_le_one _
  have hcos3 : 1 - (s.im * Real.log 3) ^ 2 / 2 ≤ Real.cos (s.im * Real.log 3) :=
    Real.one_sub_sq_div_two_le_cos
  have hsq_le : ((2 : ℝ) ^ (-s.re)) ^ 2 ≤ (3 : ℝ) ^ (-s.re) := by
    have h4 : ((2 : ℝ) ^ (-s.re)) ^ 2 = (4 : ℝ) ^ (-s.re) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      norm_num
    rw [h4]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by linarith)
  have hlead_ge1 : (1 : ℝ) ≤ 2 - 2 * (2 : ℝ) ^ (-s.re) + (3 : ℝ) ^ (-s.re) := by
    nlinarith [sq_nonneg (1 - (2 : ℝ) ^ (-s.re))]
  have hterm2 : 2 * (2 : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log 2) ≤ 2 * (2 : ℝ) ^ (-s.re) := by
    nlinarith
  have hterm3 : (3 : ℝ) ^ (-s.re) * (1 - (s.im * Real.log 3) ^ 2 / 2) ≤
      (3 : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log 3) :=
    mul_le_mul_of_nonneg_left hcos3 h3pow_nn
  have hsq_nn : 0 ≤ (s.im * Real.log 3) ^ 2 / 2 := by positivity
  nlinarith

/-- **Unconditional Critical-Strip Overlap Box Non-Vanishing (`[0, 1] × [-1/2, 1/2]`)**:
For every `s ∈ ℂ` with `0 ≤ s.re ≤ 1`, `|s.im| ≤ 1 / 2`, and `s ≠ 1`, `riemannZeta s ≠ 0`. -/
theorem riemannZeta_ne_zero_on_box :
    ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 / 2 → s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hre0 hre1 him hs1
  have hrel := twoEta_eq_of_neg_one_lt_re (by linarith) hs1
  have hterm_le : ∀ k : ℕ,
      ‖etaDiff2 (k + 1) s‖ ≤ ‖s * (s + 1)‖ * ((1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2) := by
    intro k
    have h1 := norm_etaDiff2_le (k + 1) (by linarith)
    have hbase : (1 : ℝ) ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * (k + 1) + 1 by omega)
    have hrpow : (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ (-(s.re + 2))) ≤
        (((2 * (k + 1) + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hcast : ((2 * (k + 1) + 1 : ℕ) : ℝ) = ((2 * k + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (k + 1) + 1 = 2 * k + 3 by omega)
    have hpow_eq : (((2 * k + 3 : ℕ) : ℝ) ^ (-(2 : ℝ))) = (1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2 := by
      rw [Real.rpow_neg (by positivity), one_div, Real.rpow_two]
    rw [hcast, hpow_eq] at hrpow
    rw [hcast] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hrpow (norm_nonneg _))
  have hsum_inv : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2) := by
    have h0 := summable_odd_succ_rpow_neg (p := (2 : ℝ)) one_lt_two
    refine h0.congr fun k => ?_
    have hcast : ((2 * (k + 1) + 1 : ℕ) : ℝ) = ((2 * k + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (k + 1) + 1 = 2 * k + 3 by omega)
    rw [hcast, Real.rpow_neg (by positivity), one_div, Real.rpow_two]
  have hsum_norm : Summable (fun k : ℕ => ‖etaDiff2 (k + 1) s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le (hsum_inv.mul_left ‖s * (s + 1)‖)
  have htail_norm : ‖∑' k : ℕ, etaDiff2 (k + 1) s‖ ≤ ‖s * (s + 1)‖ / 4 := by
    calc ‖∑' k : ℕ, etaDiff2 (k + 1) s‖
        ≤ ∑' k : ℕ, ‖etaDiff2 (k + 1) s‖ := norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' k : ℕ, ‖s * (s + 1)‖ * ((1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2) :=
          hsum_norm.tsum_le_tsum hterm_le (hsum_inv.mul_left _)
      _ = ‖s * (s + 1)‖ * ∑' k : ℕ, (1 : ℝ) / ((2 * k + 3 : ℕ) : ℝ) ^ 2 := tsum_mul_left
      _ ≤ ‖s * (s + 1)‖ * (1 / 4) :=
          mul_le_mul_of_nonneg_left tsum_inv_odd_sq_le_quarter (norm_nonneg _)
      _ = ‖s * (s + 1)‖ / 4 := by ring
  have hnorm_s_sq : ‖s‖ ^ 2 ≤ 5 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have him_sq : s.im * s.im ≤ (1 / 2 : ℝ) ^ 2 := by
      have h1 : s.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [← sq_abs s.im]
        exact pow_le_pow_left₀ (abs_nonneg _) him 2
      nlinarith
    nlinarith
  have hnorm_s1_sq : ‖s + 1‖ ^ 2 ≤ 17 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
    have him_sq : s.im * s.im ≤ (1 / 2 : ℝ) ^ 2 := by
      have h1 : s.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [← sq_abs s.im]
        exact pow_le_pow_left₀ (abs_nonneg _) him 2
      nlinarith
    nlinarith
  have hnorm_prod : ‖s * (s + 1)‖ ≤ 12 / 5 := by
    have hsq : ‖s * (s + 1)‖ ^ 2 ≤ (12 / 5 : ℝ) ^ 2 := by
      rw [norm_mul, mul_pow]
      nlinarith [sq_nonneg ‖s‖, sq_nonneg ‖s + 1‖]
    nlinarith [norm_nonneg (s * (s + 1))]
  have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3_lt : Real.log 3 < 11 / 10 := lt_trans Real.log_three_lt_d9 (by norm_num)
  have him_log3_sq : (s.im * Real.log 3) ^ 2 ≤ (11 / 20 : ℝ) ^ 2 := by
    have habs : |s.im * Real.log 3| ≤ 11 / 20 := by
      rw [abs_mul, abs_of_nonneg hlog3_nn]
      nlinarith [abs_nonneg s.im]
    rw [← sq_abs (s.im * Real.log 3)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have htail_re : -(∑' k : ℕ, etaDiff2 (k + 1) s).re ≤ ‖∑' k : ℕ, etaDiff2 (k + 1) s‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have htwoEta_re_pos : 0 < (twoEta s).re := by
    unfold twoEta
    rw [Complex.add_re]
    have hlead := re_lead_ge hre0
    linarith
  have htwoEta_ne : twoEta s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at htwoEta_re_pos
    exact lt_irrefl 0 htwoEta_re_pos
  intro hzeta0
  rw [hzeta0, mul_zero] at hrel
  exact htwoEta_ne hrel.symm

/-! ### 2. Negative-Real-Axis Wedge Holomorphicity & Simple Trivial-Zero Poles (`Res = -1`) -/

private lemma exp_I_pi : Complex.exp (I * (Real.pi : ℂ)) = -1 := by
  rw [mul_comm, Complex.exp_pi_mul_I]

private lemma exp_neg_I_pi : Complex.exp (-I * (Real.pi : ℂ)) = -1 := by
  rw [show -I * (Real.pi : ℂ) = -((Real.pi : ℂ) * I) by ring, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  norm_num

/-- **Unconditional Negative-Real-Axis Punctured-Wedge Holomorphicity**:
`phiLambda` is holomorphic on the entire rotated punctured wedge around `θ₀ = π` with half-angle
`α₀ = π / 4`, ball radius `ε = 1 / 4`, and trivial-zero pole sequence `2 * m + 5 / 2`. -/
theorem phiLambda_analyticOn_neg_wedge :
    AnalyticOnNhd ℂ phiLambda
      (rotatedPuncturedWedge Real.pi (Real.pi / 4) (1 / 4) (fun m : ℕ => 2 * (m : ℝ) + 5 / 2)) := by
  intro ξ hξ
  refine phiLambda_analyticAt_of_zeta1_ne_zero ?_
  rcases hξ with ⟨hwedge, hnot_pole⟩
  rw [exp_neg_I_pi, neg_one_mul] at hwedge hnot_pole
  rcases hwedge with hball | ⟨hre_pos, him_lt⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_neg] at hball
    have hre_abs : |ξ.re| < 1 / 4 := (Complex.abs_re_le_norm ξ).trans_lt hball
    have him_abs : |ξ.im| < 1 / 4 := (Complex.abs_im_le_norm ξ).trans_lt hball
    have hre_b := abs_lt.mp hre_abs
    have hs_re0 : 0 ≤ ((1 / 2 : ℂ) + ξ).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hs_re1 : ((1 / 2 : ℂ) + ξ).re ≤ 1 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hs_im : |((1 / 2 : ℂ) + ξ).im| ≤ 1 / 2 := by
      simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add]
      linarith
    have hs_ne1 : (1 / 2 : ℂ) + ξ ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hre
      linarith
    exact riemannZeta₁_ne_zero_of_ne (Or.inr (riemannZeta_ne_zero_on_box _ hs_re0 hs_re1 hs_im hs_ne1))
  · rw [Complex.neg_re] at hre_pos
    rw [Real.tan_pi_div_four, one_mul, Complex.neg_re, Complex.neg_im, abs_neg] at him_lt
    by_cases hstrip : 0 < ((1 / 2 : ℂ) + ξ).re
    · have hs_re1 : ((1 / 2 : ℂ) + ξ).re ≤ 1 := by
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
      have hs_im : |((1 / 2 : ℂ) + ξ).im| ≤ 1 / 2 := by
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hstrip
        simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add]
        linarith
      have hs_ne1 : (1 / 2 : ℂ) + ξ ≠ 1 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hre
        linarith
      exact riemannZeta₁_ne_zero_of_ne
        (Or.inr (riemannZeta_ne_zero_on_box _ hstrip.le hs_re1 hs_im hs_ne1))
    · push Not at hstrip
      refine riemannZeta₁_ne_zero_of_ne (Or.inr fun h0 => ?_)
      obtain ⟨m, hm⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hstrip).mp h0
      apply hnot_pole
      refine ⟨m, ?_⟩
      dsimp only
      have hcast : ((2 * (m : ℝ) + 5 / 2 : ℝ) : ℂ) = 2 * (m : ℂ) + 5 / 2 := by push_cast; ring
      rw [hcast]
      linear_combination hm

/-- Every trivial zero `-2 * (m + 1)` of `riemannZeta` is simple (`deriv riemannZeta (-2*(m+1)) ≠ 0`),
proved directly by differentiating Riemann's functional equation `riemannZeta_one_sub` at `2*m + 3`. -/
theorem deriv_riemannZeta_neg_two_mul_nat_add_one_ne_zero (m : ℕ) :
    deriv riemannZeta (-2 * ((m : ℂ) + 1)) ≠ 0 := by
  let w₀ : ℂ := 2 * (m : ℂ) + 3
  have hw₀_re : w₀.re = 2 * (m : ℝ) + 3 := by
    simp only [w₀, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
      Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
  have h1w₀ : 1 - w₀ = -2 * ((m : ℂ) + 1) := by dsimp only [w₀]; ring
  let H : ℂ → ℂ := fun w => 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w * riemannZeta w
  have hfe_ev : (fun w : ℂ => riemannZeta (1 - w)) =ᶠ[𝓝 w₀]
      fun w : ℂ => H w * Complex.cos ((Real.pi : ℂ) * w / 2) := by
    filter_upwards [Metric.ball_mem_nhds w₀ (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw_re : 2 < w.re := by
      have hre : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h1 := (abs_lt.mp (hre.trans_lt hw)).1
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hw_ne_neg : ∀ n : ℕ, w ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hw_ne_one : w ≠ 1 := by
      intro h1
      have hre := congrArg Complex.re h1
      simp at hre
      linarith
    rw [riemannZeta_one_sub hw_ne_neg hw_ne_one]
    dsimp only [H]
    ring
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hw₀_ne_neg : ∀ k : ℕ, w₀ ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hw₀_ne_one : w₀ ≠ 1 := by
    intro h1
    have hre := congrArg Complex.re h1
    simp at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h1w₀_ne_one : 1 - w₀ ≠ 1 := by
    intro h1
    have hre := congrArg Complex.re h1
    simp only [Complex.sub_re, Complex.one_re, hw₀_re] at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hH_diff : DifferentiableAt ℂ H w₀ := by
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-w)) w₀ :=
      differentiableAt_id.neg.const_cpow (Or.inl h2pi_ne)
    exact (((differentiableAt_const (2 : ℂ)).mul hpow).mul
      (Complex.differentiableAt_Gamma w₀ hw₀_ne_neg)).mul
      (differentiableAt_riemannZeta hw₀_ne_one)
  have hH_ne : H w₀ ≠ 0 := by
    have hpow_ne : (2 * (Real.pi : ℂ)) ^ (-w₀) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero h2pi_ne]
      exact Complex.exp_ne_zero _
    have hG_ne : Complex.Gamma w₀ ≠ 0 := Complex.Gamma_ne_zero hw₀_ne_neg
    have hz_ne : riemannZeta w₀ ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_le_re ?_
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow_ne) hG_ne) hz_ne
  have harg : (Real.pi : ℂ) * w₀ / 2 = (((((m + 1 : ℕ) : ℝ) * Real.pi + Real.pi / 2) : ℝ) : ℂ) := by
    dsimp only [w₀]; push_cast; ring
  have hcos0 : Complex.cos ((Real.pi : ℂ) * w₀ / 2) = 0 := by
    rw [harg, ← Complex.ofReal_cos, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero,
      Complex.ofReal_zero]
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * w₀ / 2) ≠ 0 := by
    intro h0
    have hsq := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * w₀ / 2)
    rw [h0, hcos0] at hsq
    norm_num at hsq
  have hLHS_deriv : HasDerivAt (fun w : ℂ => riemannZeta (1 - w))
      (-(deriv riemannZeta (1 - w₀))) w₀ := by
    have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1 : ℂ) w₀ := by
      simpa using (hasDerivAt_id w₀).const_sub (1 : ℂ)
    exact ((differentiableAt_riemannZeta h1w₀_ne_one).hasDerivAt.comp w₀ h1).congr_deriv (by ring)
  have hcos_deriv : HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w / 2))
      (-Complex.sin ((Real.pi : ℂ) * w₀ / 2) * ((Real.pi : ℂ) / 2)) w₀ := by
    have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w / 2) ((Real.pi : ℂ) / 2) w₀ := by
      have h : (fun w : ℂ => (Real.pi : ℂ) * w / 2) = fun w : ℂ => ((Real.pi : ℂ) / 2) * w := by
        funext w; ring
      rw [h]
      simpa using (hasDerivAt_id w₀).const_mul ((Real.pi : ℂ) / 2)
    exact (Complex.hasDerivAt_cos ((Real.pi : ℂ) * w₀ / 2)).comp w₀ hlin
  have hRHS_deriv := hH_diff.hasDerivAt.fun_mul hcos_deriv
  have hderiv_eq := hfe_ev.deriv_eq
  rw [hLHS_deriv.deriv, hRHS_deriv.deriv, hcos0, mul_zero, zero_add] at hderiv_eq
  have hfinal : deriv riemannZeta (-2 * ((m : ℂ) + 1)) =
      H w₀ * (Complex.sin ((Real.pi : ℂ) * w₀ / 2) * ((Real.pi : ℂ) / 2)) := by
    rw [← h1w₀]
    linear_combination -hderiv_eq
  rw [hfinal]
  have hpi2_ne : (Real.pi : ℂ) / 2 ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero
  exact mul_ne_zero hH_ne (mul_ne_zero hsin_ne hpi2_ne)

/-- **Exact Simple-Pole Principal Part (`Res = -1`) at Every Trivial Zero**:
At `ξ_m = -(2 * m + 5 / 2)` (`m : ℕ`), `phiLambda ξ - (-1) / (ξ - ξ_m)` extends continuously
to `ξ_m`. -/
theorem phiLambda_trivZero_principalPart (m : ℕ) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun ξ : ℂ =>
          phiLambda ξ - (-1 : ℂ) / (ξ - Complex.exp (I * (Real.pi : ℂ)) * ((2 * (m : ℝ) + 5 / 2 : ℝ) : ℂ)))
        (𝓝[≠] (Complex.exp (I * (Real.pi : ℂ)) * ((2 * (m : ℝ) + 5 / 2 : ℝ) : ℂ))) (𝓝 L) := by
  let ξ₀ : ℂ := Complex.exp (I * (Real.pi : ℂ)) * ((2 * (m : ℝ) + 5 / 2 : ℝ) : ℂ)
  have hξ₀_eq : ξ₀ = -2 * (m : ℂ) - 5 / 2 := by
    dsimp only [ξ₀]
    rw [exp_I_pi]
    push_cast; ring
  have hs₀_eq : (1 / 2 : ℂ) + ξ₀ = -2 * ((m : ℂ) + 1) := by rw [hξ₀_eq]; ring
  have hs₀_ne1 : (1 / 2 : ℂ) + ξ₀ ≠ 1 := by
    rw [hs₀_eq]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hξ₀_ne_half : ξ₀ ≠ 1 / 2 := by
    intro h
    apply hs₀_ne1
    rw [h]; norm_num
  let f : ℂ → ℂ := fun w => riemannZeta (1 / 2 + w)
  have hf_zero : f ξ₀ = 0 := by
    dsimp only [f]
    rw [hs₀_eq]
    exact riemannZeta_neg_two_mul_nat_add_one m
  have hf_ana : AnalyticAt ℂ f ξ₀ :=
    (analyticOn_riemannZeta ((1 / 2 : ℂ) + ξ₀) hs₀_ne1).comp (analyticAt_const.add analyticAt_id)
  have hf_deriv : deriv f ξ₀ = deriv riemannZeta (-2 * ((m : ℂ) + 1)) := by
    have hd : HasDerivAt f (deriv riemannZeta ((1 / 2 : ℂ) + ξ₀) * 1) ξ₀ :=
      (differentiableAt_riemannZeta hs₀_ne1).hasDerivAt.comp ξ₀
        ((hasDerivAt_const ξ₀ (1 / 2 : ℂ)).add (hasDerivAt_id ξ₀) |>.congr_deriv (zero_add 1))
    rw [hd.deriv, mul_one, hs₀_eq]
  let g : ℂ → ℂ := dslope f ξ₀
  have hg_ana : AnalyticAt ℂ g ξ₀ := hf_ana.hasFPowerSeriesAt.dslope_fslope.analyticAt
  have hg0 : g ξ₀ ≠ 0 := by
    dsimp only [g]
    rw [dslope_same, hf_deriv]
    exact deriv_riemannZeta_neg_two_mul_nat_add_one_ne_zero m
  have hf_fac : ∀ ξ : ℂ, f ξ = (ξ - ξ₀) * g ξ := fun ξ => by
    have h := sub_smul_dslope f ξ₀ ξ
    rw [hf_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  have hshift_cont : ContinuousAt (fun ξ : ℂ => (1 / 2 : ℂ) + ξ) ξ₀ :=
    continuousAt_const.add continuousAt_id
  have hderiv_eq : ∀ᶠ ξ in 𝓝 ξ₀,
      deriv riemannZeta (1 / 2 + ξ) = g ξ + (ξ - ξ₀) * deriv g ξ := by
    have hcomp_deriv : ∀ᶠ ξ in 𝓝 ξ₀, deriv f ξ = deriv riemannZeta (1 / 2 + ξ) := by
      filter_upwards [hshift_cont.eventually (isOpen_ne.mem_nhds hs₀_ne1)] with ξ hξ1
      have hd : HasDerivAt f (deriv riemannZeta (1 / 2 + ξ) * 1) ξ :=
        (differentiableAt_riemannZeta hξ1).hasDerivAt.comp ξ
          ((hasDerivAt_const ξ (1 / 2 : ℂ)).add (hasDerivAt_id ξ) |>.congr_deriv (zero_add 1))
      simpa using hd.deriv
    filter_upwards [hg_ana.eventually_analyticAt, hcomp_deriv] with ξ hξg hcd
    have hprod : HasDerivAt (fun w : ℂ => (w - ξ₀) * g w) (1 * g ξ + (ξ - ξ₀) * deriv g ξ) ξ :=
      ((hasDerivAt_id ξ).sub_const ξ₀).mul hξg.differentiableAt.hasDerivAt
    have hf_eq : f = fun w : ℂ => (w - ξ₀) * g w := funext hf_fac
    rw [← hcd, hf_eq, hprod.deriv, one_mul]
  have hne_half : ∀ᶠ ξ in 𝓝 ξ₀, ξ ≠ 1 / 2 := isOpen_ne.mem_nhds hξ₀_ne_half
  have hg_ne : ∀ᶠ ξ in 𝓝 ξ₀, g ξ ≠ 0 := hg_ana.continuousAt.eventually_ne hg0
  have hrem_ana : AnalyticAt ℂ (fun ξ : ℂ => -(deriv g ξ) / g ξ - 1 / (ξ - 1 / 2)) ξ₀ :=
    (hg_ana.deriv.neg.div hg_ana hg0).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hξ₀_ne_half))
  refine ⟨-(deriv g ξ₀) / g ξ₀ - 1 / (ξ₀ - 1 / 2), ?_⟩
  refine hrem_ana.continuousAt.continuousWithinAt.tendsto.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    hderiv_eq.filter_mono nhdsWithin_le_nhds,
    hne_half.filter_mono nhdsWithin_le_nhds,
    hg_ne.filter_mono nhdsWithin_le_nhds] with ξ hξ_ne hdz hnh hgn
  have hsub_ne : ξ - ξ₀ ≠ 0 := sub_ne_zero.mpr hξ_ne
  have hzeta_eq : riemannZeta (1 / 2 + ξ) = (ξ - ξ₀) * g ξ := hf_fac ξ
  have hzeta_ne : riemannZeta (1 / 2 + ξ) ≠ 0 := by
    rw [hzeta_eq]; exact mul_ne_zero hsub_ne hgn
  change -(deriv g ξ) / g ξ - 1 / (ξ - 1 / 2) = phiLambda ξ - (-1 : ℂ) / (ξ - ξ₀)
  rw [phiLambda_eq_raw hnh hzeta_ne, phiLambdaRaw, hzeta_eq, hdz]
  field_simp [hsub_ne, hgn]
  ring

/-! ### 3. Unconditional Flanking-Ray (`π ± π / 8`) & Real-Axis Exponential-Type Bounds -/

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

private lemma digamma_linear_bound_of_one_le_re :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ s : ℂ, 1 ≤ s.re → ‖Complex.digamma s‖ ≤ C₀ + C₁ * ‖s - 1‖ := by
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
    have hbase : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
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
          linarith [Nat.cast_nonneg (α := ℝ) n]
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
            field_simp [hr_pos.ne']; ring
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
      linarith [Nat.cast_nonneg (α := ℝ) m]
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

private lemma tan_bounded_of_one_le_abs_im {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖Complex.tan z‖ ≤ 4 := by
  rcases le_abs.mp hz with hpos | hneg
  · have hneg_im : (-z).im ≤ -1 := by simp; linarith
    have h := tan_bounded_of_im_le_neg_one hneg_im
    rwa [Complex.tan_neg, norm_neg] at h
  · exact tan_bounded_of_im_le_neg_one (by linarith)

/-- **Unconditional Negative-Wedge Flanking-Ray `ExpType` Bound**:
Along ANY ray `e^{i σ} ℝ_{≥0}` inside the negative-axis wedge (`cos σ < 0`, `sin σ ≠ 0`,
`|sin σ| < -cos σ`), including BOTH `σ = π - π / 8` and `σ = π + π / 8`, `phiLambda` grows at
most linearly `O(v)` and hence satisfies `ExpType` unconditionally. -/
theorem phiLambda_expType_neg_wedge_ray {σ : ℝ}
    (hcos : Real.cos σ < 0) (hsin : Real.sin σ ≠ 0) (hslope : |Real.sin σ| < -Real.cos σ) :
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
  have hsin_abs_pos : 0 < |Real.sin σ| := abs_pos.mpr hsin
  let R₀ : ℝ := max (2 / (-Real.cos σ)) (2 / |Real.sin σ|)
  have hR₀_pos : 0 < R₀ := lt_of_lt_of_le (div_pos two_pos (neg_pos.mpr hcos)) (le_max_left _ _)
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ phiLambda v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ phiLambda (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simpa using phiLambda_analyticAt_zero
      · refine phiLambda_analyticOn_neg_wedge (μ * (v : ℂ)) ?_
        refine ⟨?_, ?_⟩
        · rw [exp_neg_I_pi, neg_one_mul]
          right
          change 0 < (-(μ * (v : ℂ))).re ∧ |(-(μ * (v : ℂ))).im| < Real.tan (Real.pi / 4) * (-(μ * (v : ℂ))).re
          have hre_val : (-(μ * (v : ℂ))).re = (-Real.cos σ) * v := by
            simp [Complex.mul_re, hμ_re]
          have him_val : |(-(μ * (v : ℂ))).im| = |Real.sin σ| * v := by
            simp [Complex.mul_im, hμ_im, abs_mul, abs_of_pos hv_pos]
          rw [hre_val, him_val, Real.tan_pi_div_four, one_mul]
          exact ⟨mul_pos (neg_pos.mpr hcos) hv_pos, mul_lt_mul_of_pos_right hslope hv_pos⟩
        · rw [exp_neg_I_pi, neg_one_mul]
          rintro ⟨m, hm⟩
          have him := congrArg Complex.im hm
          simp only [Complex.ofReal_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
            mul_zero, zero_add, hμ_im] at him
          exact (mul_ne_zero hsin hv_pos.ne') (by linarith)
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
    have hv_gt_sin : 2 / |Real.sin σ| < v := lt_of_le_of_lt (le_max_right _ _) hvR
    let ξ : ℂ := μ * (v : ℂ)
    have hre_le : ξ.re < -2 := by
      dsimp only [ξ]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have := (div_lt_iff₀ (neg_pos.mpr hcos)).mp hv_gt_cos
      linarith
    have him_abs_gt : 2 < |ξ.im| := by
      dsimp only [ξ]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hμ_im,
        abs_mul, abs_of_pos hv_pos]
      have := (div_lt_iff₀ hsin_abs_pos).mp hv_gt_sin
      linarith
    have him_ne : ξ.im ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at him_abs_gt
      linarith
    let s : ℂ := 1 / 2 + ξ
    let w : ℂ := 1 - s
    have hw_re : 2 ≤ w.re := by
      simp only [w, s, Complex.sub_re, Complex.one_re, Complex.add_re, Complex.div_ofNat_re]
      linarith
    have hw_im_abs : 2 < |w.im| := by
      have hw_im : w.im = -ξ.im := by
        simp [w, s]
      rw [hw_im, abs_neg]
      exact him_abs_gt
    have hw_not_int : ∀ n : ℤ, w ≠ (n : ℂ) := by
      intro n hn
      have him := congrArg Complex.im hn
      simp at him
      rw [him, abs_zero] at hw_im_abs
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
        mul_zero, Complex.neg_im, Complex.im_ofNat, neg_zero, zero_mul] at him
      exact him_ne him
    have hξ_ne : ξ ≠ 1 / 2 := by
      intro h0
      have him := congrArg Complex.im h0
      simp at him
      exact him_ne him
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
    have htan_im : 1 ≤ |((Real.pi : ℂ) * w / 2).im| := by
      have him_eq : ((Real.pi : ℂ) * w / 2).im = Real.pi / 2 * w.im := by
        simp [Complex.mul_im]; ring
      rw [him_eq, abs_mul, abs_of_pos (half_pos Real.pi_pos)]
      nlinarith [Real.pi_gt_three]
    have htan_le : ‖(Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2)‖ ≤ 2 * Real.pi := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_ofNat]
      have ht := tan_bounded_of_one_le_abs_im htan_im
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
      have h1 : |(ξ - 1 / 2).im| ≤ ‖ξ - 1 / 2‖ := Complex.abs_im_le_norm _
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

/-- **Unconditional Positive-Wedge Holomorphicity**:
`phiLambda` is holomorphic on `borelWedge (Real.pi / 4) (1 / 4)` with ZERO hypotheses, because
every point lies either in `{Re s ≥ 1}` (`phiLambda_analyticOn_right_of_half`) or in the
critical-strip box `[0, 1] × [-1/2, 1/2]` (`riemannZeta_ne_zero_on_box`). -/
theorem phiLambda_analyticOn_pos_wedge :
    AnalyticOnNhd ℂ phiLambda (borelWedge (Real.pi / 4) (1 / 4)) := by
  intro z hz
  by_cases hright : 1 / 2 ≤ z.re
  · exact phiLambda_analyticOn_right_of_half z hright
  · push Not at hright
    refine phiLambda_analyticAt_of_zeta1_ne_zero ?_
    have hs_re1 : ((1 / 2 : ℂ) + z).re ≤ 1 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hs_ne1 : (1 / 2 : ℂ) + z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hre
      linarith
    rcases hz with hball | ⟨hre_pos, him_lt⟩
    · rw [Metric.mem_ball, dist_zero_right] at hball
      have hre_abs : |z.re| < 1 / 4 := (Complex.abs_re_le_norm z).trans_lt hball
      have him_abs : |z.im| < 1 / 4 := (Complex.abs_im_le_norm z).trans_lt hball
      have hs_re0 : 0 ≤ ((1 / 2 : ℂ) + z).re := by
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
        linarith [(abs_lt.mp hre_abs).1]
      have hs_im : |((1 / 2 : ℂ) + z).im| ≤ 1 / 2 := by
        simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add]
        linarith
      exact riemannZeta₁_ne_zero_of_ne
        (Or.inr (riemannZeta_ne_zero_on_box _ hs_re0 hs_re1 hs_im hs_ne1))
    · rw [Real.tan_pi_div_four, one_mul] at him_lt
      have hs_re0 : 0 ≤ ((1 / 2 : ℂ) + z).re := by
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
      have hs_im : |((1 / 2 : ℂ) + z).im| ≤ 1 / 2 := by
        simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add]
        linarith
      exact riemannZeta₁_ne_zero_of_ne
        (Or.inr (riemannZeta_ne_zero_on_box _ hs_re0 hs_re1 hs_im hs_ne1))

/-- **Unconditional Positive Real-Axis `ExpType` Bound**:
`phiLambda` is uniformly bounded (`ExpType` with exponent `0`) along `[0, ∞)` with ZERO hypotheses. -/
theorem phiLambda_expType_pos_real_unconditional :
    ExpType (Minor.pull (1 : ℂ) phiLambda) := by
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull (1 : ℂ) phiLambda v) (Icc 0 2) := by
    intro v hv
    have hv_mem : (v : ℂ) ∈ borelWedge (Real.pi / 4) (1 / 4) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · left; simp
      · right
        change 0 < ((v : ℂ)).re ∧ |((v : ℂ)).im| < Real.tan (Real.pi / 4) * ((v : ℂ)).re
        rw [Real.tan_pi_div_four, one_mul]
        simpa using hv_pos
    have hana : AnalyticAt ℂ phiLambda (v : ℂ) := phiLambda_analyticOn_pos_wedge (v : ℂ) hv_mem
    have hcomp : ContinuousAt (fun x : ℝ => phiLambda (x : ℂ)) v :=
      ContinuousAt.comp (g := phiLambda) (f := fun x : ℝ => (x : ℂ))
        hana.continuousAt Complex.continuous_ofReal.continuousAt
    simpa [Minor.pull] using hcomp.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁_nn, hM₁⟩ := logDeriv_riemannZeta_bounded_of_two_le_re
  let C : ℝ := max (max M₀ 0) (M₁ + 1)
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 0, hC_nn, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hv2 : v ≤ 2
  · exact (hM₀ v ⟨hv, hv2⟩).trans ((le_max_left M₀ 0).trans (le_max_left _ _))
  · push Not at hv2
    have hs_re : 2 ≤ ((1 / 2 : ℂ) + (v : ℂ)).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re]; linarith
    have hv_ne : (v : ℂ) ≠ 1 / 2 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re] at hre
      linarith
    have hζ_ne : riemannZeta (1 / 2 + (v : ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hsub_ge : 1 ≤ ‖(v : ℂ) - 1 / 2‖ := by
      have h1 : ((v : ℂ) - 1 / 2).re ≤ ‖(v : ℂ) - 1 / 2‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re] at h1
      linarith
    have hphi_le : ‖phiLambda (v : ℂ)‖ ≤ M₁ + 1 := by
      rw [phiLambda_eq_raw hv_ne hζ_ne, phiLambdaRaw]
      calc ‖-(deriv riemannZeta (1 / 2 + (v : ℂ))) / riemannZeta (1 / 2 + (v : ℂ)) -
              1 / ((v : ℂ) - 1 / 2)‖
          ≤ ‖-(deriv riemannZeta (1 / 2 + (v : ℂ))) / riemannZeta (1 / 2 + (v : ℂ))‖ +
              ‖(1 : ℂ) / ((v : ℂ) - 1 / 2)‖ := norm_sub_le _ _
        _ = ‖deriv riemannZeta (1 / 2 + (v : ℂ)) / riemannZeta (1 / 2 + (v : ℂ))‖ +
              1 / ‖(v : ℂ) - 1 / 2‖ := by rw [neg_div, norm_neg, norm_div (1 : ℂ), norm_one]
        _ ≤ M₁ + 1 := add_le_add (hM₁ _ hs_re) (by rw [div_le_one (by linarith)]; exact hsub_ge)
    change ‖(1 : ℂ) * phiLambda ((1 : ℂ) * (v : ℂ))‖ ≤ C
    rw [one_mul, one_mul]
    exact hphi_le.trans (le_max_right _ _)

/-! ### 4. Unconditional `HigherOrderBorelData` Package & Unconditional `G_Lambda_laplace` Asymptotics -/

private lemma sin_pi_div_eight_lt_cos_pi_div_eight :
    Real.sin (Real.pi / 8) < Real.cos (Real.pi / 8) := by
  have hcos : Real.cos (Real.pi / 8) = Real.sin (3 * Real.pi / 8) := by
    have heq : 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 := by ring
    rw [heq, Real.sin_pi_div_two_sub]
  rw [hcos]
  exact Real.strictMonoOn_sin
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    (by linarith [Real.pi_pos])

/-- **Unconditional `HigherOrderBorelData` Package on `phiLambda` (ZERO Hypotheses!)**:
Along the negative real axis `θ₀ = π` with half-angle `α₀ = π / 4`, flanking offset `θ = π / 8`,
and disk radius `ε = 1 / 4`, `phiLambda` has simple trivial-zero poles at `-(2 * m + 5 / 2)`
(`m : ℕ`) with constant nonzero residue `-1`. -/
def phiLambda_unconditional_higherOrderBorelData :
    HigherOrderBorelData phiLambda Real.pi (fun m : ℕ => 2 * (m : ℝ) + 5 / 2)
      (fun _ => 1) (fun _ s => if s = 1 then -1 else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 8
  ε := 1 / 4
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by norm_num
  ω_mono := fun a b hab => by
    have hlt : (a : ℝ) < (b : ℝ) := Nat.cast_lt.mpr hab
    linarith
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun _ => by norm_num
  analyticOn := phiLambda_analyticOn_neg_wedge
  pole_principalPart := fun m => by
    obtain ⟨L, hL⟩ := phiLambda_trivZero_principalPart m
    refine ⟨L, ?_⟩
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one]
    exact hL
  expType_plus := by
    have hcos_pos : 0 < Real.cos (Real.pi / 8) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hsin_pos : 0 < Real.sin (Real.pi / 8) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have hcos_eq : Real.cos (Real.pi + Real.pi / 8) = -Real.cos (Real.pi / 8) := by
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
    have hsin_eq : Real.sin (Real.pi + Real.pi / 8) = -Real.sin (Real.pi / 8) := by
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
    have hcos : Real.cos (Real.pi + Real.pi / 8) < 0 := by rw [hcos_eq]; linarith
    have hsin : Real.sin (Real.pi + Real.pi / 8) ≠ 0 := by rw [hsin_eq]; linarith
    have hslope : |Real.sin (Real.pi + Real.pi / 8)| < -Real.cos (Real.pi + Real.pi / 8) := by
      rw [hsin_eq, hcos_eq, abs_neg, abs_of_pos hsin_pos, neg_neg]
      exact sin_pi_div_eight_lt_cos_pi_div_eight
    exact phiLambda_expType_neg_wedge_ray hcos hsin hslope
  expType_minus := by
    have hcos_pos : 0 < Real.cos (Real.pi / 8) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hsin_pos : 0 < Real.sin (Real.pi / 8) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have hcos_eq : Real.cos (Real.pi - Real.pi / 8) = -Real.cos (Real.pi / 8) := by
      rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]; ring
    have hsin_eq : Real.sin (Real.pi - Real.pi / 8) = Real.sin (Real.pi / 8) := by
      rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]; ring
    have hcos : Real.cos (Real.pi - Real.pi / 8) < 0 := by rw [hcos_eq]; linarith
    have hsin : Real.sin (Real.pi - Real.pi / 8) ≠ 0 := by rw [hsin_eq]; linarith
    have hslope : |Real.sin (Real.pi - Real.pi / 8)| < -Real.cos (Real.pi - Real.pi / 8) := by
      rw [hsin_eq, hcos_eq, abs_of_pos hsin_pos, neg_neg]
      exact sin_pi_div_eight_lt_cos_pi_div_eight
    exact phiLambda_expType_neg_wedge_ray hcos hsin hslope

private lemma minor_value_hasAsympExp_uncond (a : Minor) {U : Set ℂ} {d : ℂ}
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

/-- **Unconditional All-Orders Asymptotic Expansion of `G_Lambda_laplace` (ZERO `RiemannHypothesis`!)**:
For every derivative order `j : ℕ`, `iteratedDeriv j G_Lambda_laplace` shares the exact all-orders
`1 / u` asymptotic expansion `d_u^[j] (formalSeries phiLambda)` as `u → +∞`. -/
theorem G_Lambda_laplace_hasAsympExp_unconditional (j : ℕ) :
    HasAsympExp (iteratedDeriv j G_Lambda_laplace) (d_u^[j] (formalSeries phiLambda)) := by
  let U : Set ℂ := borelWedge (Real.pi / 4) (1 / 4)
  have hU : Domain U := by
    refine ⟨Metric.isOpen_ball.union ?_, fun z hz t ht => ?_⟩
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im)
          (continuous_const.mul Complex.continuous_re))
    · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · left; simp
      · rcases hz with hzb | ⟨hre, him⟩
        · left
          rw [Metric.mem_ball, dist_zero_right] at hzb ⊢
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
          exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hzb
        · right
          refine ⟨by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero];
                     exact mul_pos ht_pos hre, ?_⟩
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero, add_zero]
          rw [abs_mul, abs_of_pos ht_pos]
          nlinarith
  have hray : ContainsRay U 1 := by
    intro v hv
    rw [one_mul]
    rcases eq_or_lt_of_le hv with rfl | hv_pos
    · left; simp
    · right
      change 0 < ((v : ℂ)).re ∧ |((v : ℂ)).im| < Real.tan (Real.pi / 4) * ((v : ℂ)).re
      rw [Real.tan_pi_div_four, one_mul]
      simpa using hv_pos
  let a : Minor := Minor.mk 0 phiLambda
  have ha_good : a.Good U 1 :=
    ⟨phiLambda_analyticOn_pos_wedge, phiLambda_expType_pos_real_unconditional⟩
  have hval : (fun u : ℝ => a.value 1 (u : ℂ)) = G_Lambda_laplace := by
    funext u
    simp [a, Minor.value, complexLaplace, damped, Minor.pull, G_Lambda_laplace]
  have hser : a.toSeries = formalSeries phiLambda := by
    ext n
    cases n <;> simp [a, Minor.toSeries, formalSeries]
  rw [← hval, ← hser]
  exact minor_value_hasAsympExp_uncond a hU hray ha_good (by simp) j

/-! ### 5. Master Unconditional Prime-Number Strong Differential Transcendence Theorems -/

/-- **Unconditional Master Theorem 1 (`ℂ({t})` Strong D-Transcendence of the Von Mangoldt OGF)**:
With ZERO hypotheses, `ogfOfEGF phiLambda = ∑_{n ≥ 0} Φ_Λ^{(n)}(0) t^n` is strongly
differentially transcendental over convergent meromorphic germs `ℂ({t})`. -/
theorem unconditional_G_Lambda_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF phiLambda) :=
  ogf_stronglyDTrans_of_higherOrderBorel phiLambda_unconditional_higherOrderBorelData

/-- **Unconditional Master Theorem 2 (`ℂ({1/u})` Strong D-Transcendence of `G_Lambda`)**:
With ZERO hypotheses, `G_Lambda = formalSeries phiLambda` is strongly differentially
transcendental over convergent meromorphic germs `ℂ({1/u})`. -/
theorem unconditional_G_Lambda_formalSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (formalSeries phiLambda) :=
  stronglyDTrans_of_higher_order_borel phiLambda_unconditional_higherOrderBorelData

/-- **Unconditional Master Theorem 3 (`ℂ{1/u}` Formal `d_u`-ADE Obstruction for `G_Lambda`)**:
With ZERO hypotheses, `G_Lambda = formalSeries phiLambda` satisfies NO nonzero algebraic
differential equation with coefficients in `ConvergentPowerSeries` (`ℂ{1/u}`). -/
theorem unconditional_G_Lambda_formalSeries_no_conv_ade
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries phiLambda) Q = 0) : Q = 0 :=
  no_conv_ade_of_higher_order_borel phiLambda_unconditional_higherOrderBorelData Q hQ

/-- **Unconditional Master Theorem 4 (`ℂ(u)` Formal ADE Obstruction for `G_Lambda`)**:
With ZERO hypotheses, `G_Lambda = formalSeries phiLambda` satisfies NO nonzero rational-coefficient
algebraic differential equation over `ℂ(u)`. -/
theorem unconditional_G_Lambda_formalSeries_no_rat_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries phiLambda) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade phiLambda_unconditional_higherOrderBorelData P hP

/-- **Unconditional Master Theorem 5 (`ℂ[u]` Formal ADE Obstruction for `G_Lambda`)**:
With ZERO hypotheses, `G_Lambda = formalSeries phiLambda` satisfies NO nonzero polynomial-coefficient
algebraic differential equation over `ℂ[u]`. -/
theorem unconditional_G_Lambda_formalSeries_no_poly_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries phiLambda) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_ade phiLambda_unconditional_higherOrderBorelData P hP

/-- **Unconditional Master Theorem 6 (Autonomous Formal ADE Obstruction for `G_Lambda`)**:
With ZERO hypotheses, `G_Lambda = formalSeries phiLambda` satisfies NO nonzero autonomous
algebraic differential equation over `ℂ`. -/
theorem unconditional_G_Lambda_formalSeries_no_autonomous_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval (formalSeries phiLambda) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_autonomous_ade phiLambda_unconditional_higherOrderBorelData P hP

/-- **Unconditional Master Theorem 7 (`ℂ{1/u}` Analytic ADE Obstruction for `G_Lambda_laplace`)**:
With ZERO hypotheses, the regularized real-axis Laplace integral `G_Lambda_laplace` satisfies NO
nonzero convergent-germ algebraic differential equation over `ℂ{1/u}` eventually as `u → +∞`. -/
theorem unconditional_G_Lambda_laplace_no_conv_ade
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) : Q = 0 :=
  no_conv_ade_of_higher_order_borel_asymp phiLambda_unconditional_higherOrderBorelData
    G_Lambda_laplace_hasAsympExp_unconditional Q hQ

/-- **Unconditional Master Theorem 8 (`ℂ(u)` Analytic ADE Obstruction for `G_Lambda_laplace`)**:
With ZERO hypotheses, the regularized real-axis Laplace integral `G_Lambda_laplace` satisfies NO
nonzero rational-coefficient algebraic differential equation over `ℂ(u)` eventually as `u → +∞`. -/
theorem unconditional_G_Lambda_laplace_no_rat_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  no_rat_ade_of_higher_order_borel phiLambda_unconditional_higherOrderBorelData
    G_Lambda_laplace_hasAsympExp_unconditional P hP

/-- **Unconditional Master Theorem 9 (`ℂ[u]` Analytic ADE Obstruction for `G_Lambda_laplace`)**:
With ZERO hypotheses, the regularized real-axis Laplace integral `G_Lambda_laplace` satisfies NO
nonzero polynomial-coefficient algebraic differential equation over `ℂ[u]` eventually as `u → +∞`. -/
theorem unconditional_G_Lambda_laplace_no_poly_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalU P (u : ℂ)) = 0) : P = 0 :=
  no_nonautonomous_ade_of_higher_order_borel phiLambda_unconditional_higherOrderBorelData
    G_Lambda_laplace_hasAsympExp_unconditional P hP

/-- **Unconditional Master Theorem 10 (Autonomous Analytic ADE Obstruction for `G_Lambda_laplace`)**:
With ZERO hypotheses, the regularized real-axis Laplace integral `G_Lambda_laplace` satisfies NO
nonzero autonomous algebraic differential equation over `ℂ` eventually as `u → +∞`. -/
theorem unconditional_G_Lambda_laplace_no_autonomous_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u) P = 0) :
    P = 0 :=
  no_autonomous_ade_of_higher_order_borel phiLambda_unconditional_higherOrderBorelData
    G_Lambda_laplace_hasAsympExp_unconditional P hP

/-! ### 6. Asymmetric Basepoint `s₀ = 2`: Literal Convergent Von Mangoldt Moments (`phiLambdaAtTwo`) -/

/-- Prime Borel kernel centered at the asymmetric basepoint `s₀ = 2`:
`phiLambdaAtTwo w = -ζ'(2 + w) / ζ(2 + w)`. Its Taylor coefficients at `w = 0` are the literal
convergent von Mangoldt Dirichlet moments `(-1)^n ∑_{m ≥ 2} Λ(m) (log m)^n / m²`, and reflection
`w ↦ -w` does NOT cancel `ζ'/ζ`. -/
@[expose] def phiLambdaAtTwo (w : ℂ) : ℂ :=
  -deriv riemannZeta (2 + w) / riemannZeta (2 + w)

/-- Real-axis Laplace integral of `phiLambdaAtTwo`:
`G_Lambda_atTwo_laplace u = ∫_{0}^{∞} e^{-u w} (-ζ'(2 + w) / ζ(2 + w)) dw`. -/
@[expose] def G_Lambda_atTwo_laplace (u : ℝ) : ℂ :=
  ∫ w in Set.Ioi (0 : ℝ), Complex.exp (-((u : ℂ) * (w : ℂ))) * phiLambdaAtTwo (w : ℂ)

/-- Negative-real-axis pole radii for `phiLambdaAtTwo`:
`omegaAtTwo 0 = 1` (simple pole of `ζ` at `s = 1`, `w = -1`, residue `+1`) and
`omegaAtTwo (k + 1) = 2 * k + 4` (simple trivial zeros of `ζ` at `s = -2(k + 1)`, residue `-1`). -/
@[expose] def omegaAtTwo (m : ℕ) : ℝ :=
  if m = 0 then 1 else 2 * (m : ℝ) + 2

/-- Exact principal-part coefficients for `phiLambdaAtTwo` along `θ₀ = π`:
residue `+1` at `m = 0` (`w = -1`) and `-1` at every trivial zero `m ≥ 1` (`w = -(2m + 2)`). -/
@[expose] def ppAtTwo (m s : ℕ) : ℂ :=
  if s = 1 then (if m = 0 then 1 else -1) else 0

/-- Exact Dirichlet-series identity on the half-plane `Re w > -1` (`Re (2 + w) > 1`):
`phiLambdaAtTwo w` equals the literal von Mangoldt `L`-series at `2 + w`. -/
theorem phiLambdaAtTwo_eq_LSeries_vonMangoldt (w : ℂ) (hw : -1 < w.re) :
    phiLambdaAtTwo w = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (2 + w) := by
  have hs1 : 1 < ((2 : ℂ) + w).re := by
    simp only [Complex.add_re, Complex.re_ofNat]; linarith
  exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1).symm

private lemma phiLambdaAtTwo_analyticAt {w : ℂ} (h1 : (2 : ℂ) + w ≠ 1)
    (hζ : riemannZeta (2 + w) ≠ 0) :
    AnalyticAt ℂ phiLambdaAtTwo w := by
  have hζ_an : AnalyticAt ℂ riemannZeta (2 + w) := analyticOn_riemannZeta (2 + w) h1
  have hadd : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) + z) w := analyticAt_const.add analyticAt_id
  exact (hζ_an.deriv.comp hadd).neg.div (hζ_an.comp hadd) hζ

private lemma tan_pi_div_sixteen_le_quarter : Real.tan (Real.pi / 16) ≤ 1 / 4 := by
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have hx_pos : 0 < Real.pi / 16 := by positivity
  have hx_lt : Real.pi / 16 < 1 / 5 := by linarith
  have hsin : Real.sin (Real.pi / 16) ≤ 1 / 5 := (Real.sin_le hx_pos.le).trans hx_lt.le
  have hcos : 4 / 5 ≤ Real.cos (Real.pi / 16) := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 16)
    nlinarith
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith : 0 < Real.cos (Real.pi / 16))]
  linarith

/-- **Unconditional Negative-Wedge Holomorphicity at Asymmetric Basepoint `s₀ = 2`**:
`phiLambdaAtTwo` is holomorphic on `rotatedPuncturedWedge π (π / 16) (1 / 4) omegaAtTwo`.
Every critical-strip point (`0 ≤ Re (2 + w) ≤ 1`) satisfies `-2 ≤ Re w ≤ -1` and
`|Im w| < 2 * tan (π / 16) ≤ 1 / 2`, landing directly inside `riemannZeta_ne_zero_on_box`. -/
theorem phiLambdaAtTwo_analyticOn_neg_wedge :
    AnalyticOnNhd ℂ phiLambdaAtTwo
      (rotatedPuncturedWedge Real.pi (Real.pi / 16) (1 / 4) omegaAtTwo) := by
  intro w hw
  rcases hw with ⟨hwedge, hnot_pole⟩
  rw [exp_neg_I_pi, neg_one_mul] at hwedge hnot_pole
  rcases hwedge with hball | ⟨hre_pos, him_lt⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_neg] at hball
    have hre_abs : |w.re| < 1 / 4 := (Complex.abs_re_le_norm w).trans_lt hball
    have hs_re : 1 < ((2 : ℂ) + w).re := by
      simp only [Complex.add_re, Complex.re_ofNat]
      linarith [(abs_lt.mp hre_abs).1]
    have hs_ne1 : (2 : ℂ) + w ≠ 1 := by
      intro h; rw [h] at hs_re; simp at hs_re
    exact phiLambdaAtTwo_analyticAt hs_ne1 (riemannZeta_ne_zero_of_one_le_re hs_re.le)
  · rw [Complex.neg_re] at hre_pos
    rw [Complex.neg_re, Complex.neg_im, abs_neg] at him_lt
    by_cases hgt1 : 1 < ((2 : ℂ) + w).re
    · have hs_ne1 : (2 : ℂ) + w ≠ 1 := by
        intro h; rw [h] at hgt1; simp at hgt1
      exact phiLambdaAtTwo_analyticAt hs_ne1 (riemannZeta_ne_zero_of_one_le_re hgt1.le)
    · push Not at hgt1
      by_cases hge0 : 0 ≤ ((2 : ℂ) + w).re
      · have hs_ne1 : (2 : ℂ) + w ≠ 1 := by
          intro h
          apply hnot_pole
          refine ⟨0, ?_⟩
          simp only [omegaAtTwo, ↓reduceIte, Complex.ofReal_one]
          linear_combination h
        have hw_re_ge : -2 ≤ w.re := by
          simp only [Complex.add_re, Complex.re_ofNat] at hge0; linarith
        have hs_im : |((2 : ℂ) + w).im| ≤ 1 / 2 := by
          simp only [Complex.add_im, Complex.im_ofNat, zero_add]
          have htan := tan_pi_div_sixteen_le_quarter
          nlinarith
        exact phiLambdaAtTwo_analyticAt hs_ne1
          (riemannZeta_ne_zero_on_box _ hge0 hgt1 hs_im hs_ne1)
      · push Not at hge0
        have hs_ne1 : (2 : ℂ) + w ≠ 1 := by
          intro h; rw [h] at hge0; simp at hge0; norm_num at hge0
        refine phiLambdaAtTwo_analyticAt hs_ne1 fun h0 => ?_
        obtain ⟨k, hk⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hge0.le).mp h0
        apply hnot_pole
        refine ⟨k + 1, ?_⟩
        simp only [omegaAtTwo, Nat.succ_ne_zero, ↓reduceIte]
        have hcast : ((2 * ((k + 1 : ℕ) : ℝ) + 2 : ℝ) : ℂ) = 2 * ((k : ℂ) + 1) + 2 := by
          push_cast; ring
        rw [hcast]
        linear_combination hk

/-- **Exact Simple-Pole Principal Parts for `phiLambdaAtTwo` along `θ₀ = π`**:
Residue `+1` at `w = -1` (`m = 0`, simple pole `s = 1` of `ζ`) and residue `-1` at every trivial
zero `w = -(2k + 4)` (`m = k + 1`, `s = -2(k + 1)`). -/
theorem phiLambdaAtTwo_pole_principalPart (m : ℕ) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun w : ℂ =>
          phiLambdaAtTwo w -
            ∑ s ∈ Finset.Icc 1 1,
              ppAtTwo m s / (w - Complex.exp (I * (Real.pi : ℂ)) * (omegaAtTwo m : ℂ)) ^ s)
        (𝓝[≠] (Complex.exp (I * (Real.pi : ℂ)) * (omegaAtTwo m : ℂ))) (𝓝 L) := by
  simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, ppAtTwo, ↓reduceIte]
  cases m with
  | zero =>
    simp only [↓reduceIte, omegaAtTwo, Complex.ofReal_one, exp_I_pi, mul_one]
    have hana : AnalyticAt ℂ phiLambda (1 / 2 : ℂ) :=
      phiLambda_analyticOn_right_of_half (1 / 2 : ℂ) (by simp)
    have hshift : ContinuousAt (fun w : ℂ => w + 3 / 2) (-1 : ℂ) :=
      continuousAt_id.add continuousAt_const
    have hcomp : ContinuousAt (fun w : ℂ => phiLambda (w + 3 / 2)) (-1 : ℂ) := by
      have hval : (-1 : ℂ) + 3 / 2 = 1 / 2 := by ring
      exact ContinuousAt.comp (g := phiLambda) (f := fun w : ℂ => w + 3 / 2)
        (hval ▸ hana.continuousAt) hshift
    refine ⟨phiLambda ((-1 : ℂ) + 3 / 2), ?_⟩
    refine (hcomp.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (-1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))]
      with w hw_ne hw_ball
    have hw_ne' : w ≠ -1 := Set.mem_compl_singleton_iff.mp hw_ne
    rw [Metric.mem_ball, dist_eq_norm] at hw_ball
    have hw_ne_half : w + 3 / 2 ≠ 1 / 2 := fun h => hw_ne' (by linear_combination h)
    have hrew : (1 / 2 : ℂ) + (w + 3 / 2) = 2 + w := by ring
    have hs_ne1 : (2 : ℂ) + w ≠ 1 := fun h => hw_ne' (by linear_combination h)
    have hζ_ne : riemannZeta (2 + w) ≠ 0 := by
      by_cases hre1 : 1 ≤ ((2 : ℂ) + w).re
      · exact riemannZeta_ne_zero_of_one_le_re hre1
      · push Not at hre1
        have hre_diff : |(w - (-1 : ℂ)).re| < 1 / 2 :=
          (Complex.abs_re_le_norm _).trans_lt hw_ball
        have him_diff : |(w - (-1 : ℂ)).im| < 1 / 2 :=
          (Complex.abs_im_le_norm _).trans_lt hw_ball
        have hs_re0 : 0 ≤ ((2 : ℂ) + w).re := by
          have h1 := (abs_lt.mp hre_diff).1
          rw [sub_neg_eq_add] at h1
          simp only [Complex.add_re, Complex.one_re, Complex.re_ofNat] at h1 ⊢
          linarith
        have hs_im : |((2 : ℂ) + w).im| ≤ 1 / 2 := by
          simp only [Complex.sub_im, Complex.neg_im, Complex.one_im, neg_zero, sub_zero] at him_diff
          simp only [Complex.add_im, Complex.im_ofNat, zero_add]
          linarith
        exact riemannZeta_ne_zero_on_box _ hs_re0 hre1.le hs_im hs_ne1
    have hζ_ne' : riemannZeta ((1 / 2 : ℂ) + (w + 3 / 2)) ≠ 0 := by rwa [hrew]
    rw [phiLambda_eq_raw hw_ne_half hζ_ne', phiLambdaRaw, hrew]
    have hsub : w + 3 / 2 - 1 / 2 = w - (-1 : ℂ) := by ring
    rw [hsub, phiLambdaAtTwo]
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, omegaAtTwo]
    let w₀ : ℂ := Complex.exp (I * (Real.pi : ℂ)) * ((2 * ((k + 1 : ℕ) : ℝ) + 2 : ℝ) : ℂ)
    let ξ₀ : ℂ := Complex.exp (I * (Real.pi : ℂ)) * ((2 * (k : ℝ) + 5 / 2 : ℝ) : ℂ)
    have hw₀_eq : w₀ = -(2 * (k : ℂ) + 4) := by
      dsimp only [w₀]; rw [exp_I_pi]; push_cast; ring
    have hξ₀_eq : ξ₀ = -(2 * (k : ℂ) + 5 / 2) := by
      dsimp only [ξ₀]; rw [exp_I_pi]; push_cast; ring
    have hshift_eq : w₀ + 3 / 2 = ξ₀ := by rw [hw₀_eq, hξ₀_eq]; ring
    have hw₀1_ne : w₀ + 1 ≠ 0 := by
      rw [hw₀_eq]
      intro h0
      have hre := congrArg Complex.re h0
      simp at hre
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    obtain ⟨L, hL⟩ := phiLambda_trivZero_principalPart k
    have hmap : Filter.Tendsto (fun w : ℂ => w + 3 / 2) (𝓝[≠] w₀) (𝓝[≠] ξ₀) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : ContinuousAt (fun w : ℂ => w + 3 / 2) w₀ :=
          continuousAt_id.add continuousAt_const
        rw [← hshift_eq]
        exact hc.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        have hw' : w ≠ w₀ := Set.mem_compl_singleton_iff.mp hw
        change w + 3 / 2 ≠ ξ₀
        rw [← hshift_eq]
        intro h
        exact hw' (by linear_combination h)
    have h1 : Filter.Tendsto
        (fun w : ℂ => phiLambda (w + 3 / 2) - (-1 : ℂ) / ((w + 3 / 2) - ξ₀))
        (𝓝[≠] w₀) (𝓝 L) := hL.comp hmap
    have h2 : Filter.Tendsto (fun w : ℂ => (1 : ℂ) / (w + 1)) (𝓝[≠] w₀) (𝓝 ((1 : ℂ) / (w₀ + 1))) :=
      (continuousAt_const.div (continuousAt_id.add continuousAt_const) hw₀1_ne).tendsto.mono_left
        nhdsWithin_le_nhds
    refine ⟨L + (1 : ℂ) / (w₀ + 1), ?_⟩
    refine (h1.add h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds w₀ (by norm_num : (0 : ℝ) < 1 / 2))]
      with w hw_ne hw_ball
    rw [Metric.mem_ball, dist_eq_norm] at hw_ball
    have hre_diff : |(w - w₀).re| < 1 / 2 := (Complex.abs_re_le_norm _).trans_lt hw_ball
    have hw₀_re : w₀.re = -(2 * (k : ℝ) + 4) := by
      rw [hw₀_eq]; simp
    have hw_re : w.re < -(2 * (k : ℝ) + 7 / 2) := by
      have h1 := (abs_lt.mp hre_diff).2
      rw [Complex.sub_re, hw₀_re] at h1
      linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hs_re : ((2 : ℂ) + w).re ≤ 0 := by
      simp only [Complex.add_re, Complex.re_ofNat]; linarith
    have hw_ne_half : w + 3 / 2 ≠ 1 / 2 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.re_ofNat, Complex.one_re] at hre
      linarith
    have hζ_ne : riemannZeta (2 + w) ≠ 0 := by
      intro h0
      obtain ⟨j, hj⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hs_re).mp h0
      have hj_eq : w - w₀ = 2 * ((k : ℂ) - (j : ℂ)) := by
        rw [hw₀_eq]; linear_combination hj
      have hj_re : |(w - w₀).re| = 2 * |(k : ℝ) - (j : ℝ)| := by
        rw [hj_eq]
        have hre : (2 * ((k : ℂ) - (j : ℂ))).re = 2 * ((k : ℝ) - (j : ℝ)) := by simp
        rw [hre, abs_mul, abs_of_pos two_pos]
      rcases eq_or_ne k j with rfl | hkj
      · rw [sub_self, mul_zero] at hj_eq
        exact hw_ne (sub_eq_zero.mp hj_eq)
      · have hdist : (1 : ℝ) ≤ |(k : ℝ) - (j : ℝ)| := by
          have hint : (1 : ℤ) ≤ |(k : ℤ) - (j : ℤ)| := by
            have hne_z : (k : ℤ) - (j : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkj)
            exact Int.one_le_abs hne_z
          exact_mod_cast hint
        linarith
    have hrew : (1 / 2 : ℂ) + (w + 3 / 2) = 2 + w := by ring
    have hζ_ne' : riemannZeta ((1 / 2 : ℂ) + (w + 3 / 2)) ≠ 0 := by rwa [hrew]
    rw [phiLambda_eq_raw hw_ne_half hζ_ne', phiLambdaRaw, hrew]
    have hsub1 : (w + 3 / 2) - ξ₀ = w - w₀ := by rw [← hshift_eq]; ring
    have hsub2 : w + 3 / 2 - 1 / 2 = w + 1 := by ring
    rw [hsub1, hsub2, phiLambdaAtTwo]
    ring

/-- **Unconditional Negative-Wedge Flanking-Ray `ExpType` Bound for `phiLambdaAtTwo`**:
Along any ray `e^{i σ} ℝ_{≥0}` inside the `s₀ = 2` negative-axis wedge (`cos σ < 0`, `sin σ ≠ 0`,
`|sin σ| < tan (π / 16) * (-cos σ)`), including `σ = π ± π / 32`, `phiLambdaAtTwo` has `O(v)`
growth and hence satisfies `ExpType` unconditionally. -/
theorem phiLambdaAtTwo_expType_neg_wedge_ray {σ : ℝ}
    (hcos : Real.cos σ < 0) (hsin : Real.sin σ ≠ 0)
    (hslope : |Real.sin σ| < Real.tan (Real.pi / 16) * (-Real.cos σ)) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) phiLambdaAtTwo) := by
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
  have hsin_abs_pos : 0 < |Real.sin σ| := abs_pos.mpr hsin
  let R₀ : ℝ := max (3 / (-Real.cos σ)) (2 / |Real.sin σ|)
  have hR₀_pos : 0 < R₀ := lt_of_lt_of_le (div_pos (by norm_num) (neg_pos.mpr hcos)) (le_max_left _ _)
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ phiLambdaAtTwo v) (Icc 0 R₀) := by
    intro v hv
    have hana : AnalyticAt ℂ phiLambdaAtTwo (μ * (v : ℂ)) := by
      rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
      · simp only [Complex.ofReal_zero, mul_zero]
        exact phiLambdaAtTwo_analyticAt (by norm_num)
          (riemannZeta_ne_zero_of_one_le_re (by simp))
      · refine phiLambdaAtTwo_analyticOn_neg_wedge (μ * (v : ℂ)) ?_
        refine ⟨?_, ?_⟩
        · rw [exp_neg_I_pi, neg_one_mul]
          right
          change 0 < (-(μ * (v : ℂ))).re ∧
            |(-(μ * (v : ℂ))).im| < Real.tan (Real.pi / 16) * (-(μ * (v : ℂ))).re
          have hre_val : (-(μ * (v : ℂ))).re = (-Real.cos σ) * v := by
            simp [Complex.mul_re, hμ_re]
          have him_val : |(-(μ * (v : ℂ))).im| = |Real.sin σ| * v := by
            simp [Complex.mul_im, hμ_im, abs_mul, abs_of_pos hv_pos]
          rw [hre_val, him_val]
          exact ⟨mul_pos (neg_pos.mpr hcos) hv_pos, by nlinarith⟩
        · rw [exp_neg_I_pi, neg_one_mul]
          rintro ⟨m, hm⟩
          have him := congrArg Complex.im hm
          simp only [Complex.ofReal_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
            mul_zero, zero_add, hμ_im] at him
          exact (mul_ne_zero hsin hv_pos.ne') (by linarith)
    have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
      continuous_const.continuousAt.mul Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ => phiLambdaAtTwo (μ * (x : ℂ))) v :=
      ContinuousAt.comp (g := phiLambdaAtTwo) (f := fun x : ℝ => μ * (x : ℂ))
        hana.continuousAt hmul_cont
    exact (hcomp.const_mul μ).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M₁, hM₁_nn, hM₁⟩ := logDeriv_riemannZeta_bounded_of_two_le_re
  obtain ⟨C₀, C₁, hC₀_nn, hC₁_nn, hdig⟩ := digamma_linear_bound_of_one_le_re
  let K₀ : ℝ := M₁ + ‖Complex.log (2 * (Real.pi : ℂ))‖ + C₀ + 2 * C₁ + 2 * Real.pi
  let C : ℝ := max (max M₀ 0) (K₀ + C₁)
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 1, hC_nn, zero_le_one, fun v hv => ?_⟩
  rw [one_mul]
  by_cases hvR : v ≤ R₀
  · calc ‖Minor.pull μ phiLambdaAtTwo v‖ ≤ M₀ := hM₀ v ⟨hv, hvR⟩
      _ ≤ max M₀ 0 := le_max_left _ _
      _ ≤ C := le_max_left _ _
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_left (Real.one_le_exp hv) hC_nn
  · push Not at hvR
    have hv_pos : 0 < v := lt_trans hR₀_pos hvR
    have hv_gt_cos : 3 / (-Real.cos σ) < v := lt_of_le_of_lt (le_max_left _ _) hvR
    have hv_gt_sin : 2 / |Real.sin σ| < v := lt_of_le_of_lt (le_max_right _ _) hvR
    let ξ : ℂ := μ * (v : ℂ)
    have hre_le : ξ.re < -3 := by
      dsimp only [ξ]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hμ_re]
      have := (div_lt_iff₀ (neg_pos.mpr hcos)).mp hv_gt_cos
      linarith
    have him_abs_gt : 2 < |ξ.im| := by
      dsimp only [ξ]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hμ_im,
        abs_mul, abs_of_pos hv_pos]
      have := (div_lt_iff₀ hsin_abs_pos).mp hv_gt_sin
      linarith
    let s : ℂ := 2 + ξ
    let w : ℂ := 1 - s
    have hw_re : 2 ≤ w.re := by
      simp only [w, s, Complex.sub_re, Complex.one_re, Complex.add_re, Complex.re_ofNat]
      linarith
    have hw_im_abs : 2 < |w.im| := by
      have hw_im : w.im = -ξ.im := by simp [w, s]
      rw [hw_im, abs_neg]
      exact him_abs_gt
    have hw_not_int : ∀ n : ℤ, w ≠ (n : ℂ) := by
      intro n hn
      have him := congrArg Complex.im hn
      simp at him
      rw [him, abs_zero] at hw_im_abs
      linarith
    have hw_zeta_ne : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hfe := logDeriv_riemannZeta_one_sub hw_not_int hw_zeta_ne
    have h1w : 1 - w = s := by dsimp only [w]; ring
    rw [h1w] at hfe
    have hneg_logDeriv : phiLambdaAtTwo ξ =
        deriv riemannZeta w / riemannZeta w - Complex.log (2 * (Real.pi : ℂ)) +
          Complex.digamma w - (Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2) := by
      have hld_w : logDeriv riemannZeta w = deriv riemannZeta w / riemannZeta w := logDeriv_apply _ _
      have hld_s : logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s := logDeriv_apply _ _
      rw [hld_w, hld_s] at hfe
      dsimp only [phiLambdaAtTwo, s]
      linear_combination -hfe
    have htan_im : 1 ≤ |((Real.pi : ℂ) * w / 2).im| := by
      have him_eq : ((Real.pi : ℂ) * w / 2).im = Real.pi / 2 * w.im := by
        simp [Complex.mul_im]; ring
      rw [him_eq, abs_mul, abs_of_pos (half_pos Real.pi_pos)]
      nlinarith [Real.pi_gt_three]
    have htan_le : ‖(Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2)‖ ≤ 2 * Real.pi := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_ofNat]
      have ht := tan_bounded_of_one_le_abs_im htan_im
      nlinarith [Real.pi_pos]
    have hw_sub1_norm : ‖w - 1‖ ≤ v + 2 := by
      have hw1 : w - 1 = -(2 : ℂ) - ξ := by dsimp only [w, s]; ring
      rw [hw1]
      have h1 : ‖-(2 : ℂ) - ξ‖ ≤ ‖-(2 : ℂ)‖ + ‖ξ‖ := norm_sub_le _ _
      have hξ_norm : ‖ξ‖ = v := by
        dsimp only [ξ]
        rw [norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
      have htwo : ‖-(2 : ℂ)‖ = 2 := by norm_num
      linarith
    have hdig_le : ‖Complex.digamma w‖ ≤ C₀ + C₁ * (v + 2) := by
      have h1 := hdig w (by linarith)
      have h2 := mul_le_mul_of_nonneg_left hw_sub1_norm hC₁_nn
      linarith
    have hphi_le : ‖phiLambdaAtTwo ξ‖ ≤ K₀ + C₁ * v := by
      rw [hneg_logDeriv]
      have hstep1 := norm_sub_le
        (deriv riemannZeta w / riemannZeta w - Complex.log (2 * (Real.pi : ℂ)) +
          Complex.digamma w)
        ((Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * w / 2))
      have hstep2 := norm_add_le
        (deriv riemannZeta w / riemannZeta w - Complex.log (2 * (Real.pi : ℂ)))
        (Complex.digamma w)
      have hstep3 := norm_sub_le
        (deriv riemannZeta w / riemannZeta w)
        (Complex.log (2 * (Real.pi : ℂ)))
      have hw_bd := hM₁ w hw_re
      dsimp only [K₀]
      linarith
    change ‖μ * phiLambdaAtTwo ξ‖ ≤ C * Real.exp v
    rw [norm_mul, hμ_norm, one_mul]
    have h1_le_exp : 1 ≤ Real.exp v := Real.one_le_exp hv
    have hv_le_exp : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
    have hK0_nn : 0 ≤ K₀ := by
      dsimp only [K₀]; linarith [norm_nonneg (Complex.log (2 * (Real.pi : ℂ))), Real.pi_pos]
    calc ‖phiLambdaAtTwo ξ‖ ≤ K₀ + C₁ * v := hphi_le
      _ ≤ K₀ * Real.exp v + C₁ * Real.exp v :=
        add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hv_le_exp hC₁_nn)
      _ = (K₀ + C₁) * Real.exp v := by ring
      _ ≤ C * Real.exp v := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos v).le

private lemma sin_pi_div_32_lt_tan_pi_div_16_mul_cos :
    Real.sin (Real.pi / 32) < Real.tan (Real.pi / 16) * Real.cos (Real.pi / 32) := by
  have hcos_pos : 0 < Real.cos (Real.pi / 32) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [← div_lt_iff₀ hcos_pos, ← Real.tan_eq_sin_div_cos]
  exact Real.strictMonoOn_tan
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    (by linarith [Real.pi_pos])

/-- **Unconditional `HigherOrderBorelData` Package on `phiLambdaAtTwo` (Asymmetric Basepoint `s₀ = 2`)**:
Along `θ₀ = π` with half-angle `α₀ = π / 16`, flanking offset `θ = π / 32`, and disk radius `ε = 1 / 4`,
`phiLambdaAtTwo` has simple poles at `w = -1` (residue `+1`) and `w = -(2k + 4)` (residue `-1`). -/
def phiLambdaAtTwo_higherOrderBorelData :
    HigherOrderBorelData phiLambdaAtTwo Real.pi omegaAtTwo (fun _ => 1) ppAtTwo where
  α₀ := Real.pi / 16
  θ := Real.pi / 32
  ε := 1 / 4
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by simp [omegaAtTwo]
  ω_mono := fun a b hab => by
    unfold omegaAtTwo
    split_ifs with ha hb
    · omega
    · have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
      linarith
    · omega
    · have hlt : (a : ℝ) < (b : ℝ) := Nat.cast_lt.mpr hab
      linarith
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by
    unfold ppAtTwo
    simp only [↓reduceIte]
    split_ifs <;> norm_num
  analyticOn := phiLambdaAtTwo_analyticOn_neg_wedge
  pole_principalPart := phiLambdaAtTwo_pole_principalPart
  expType_plus := by
    have hcos_pos : 0 < Real.cos (Real.pi / 32) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hsin_pos : 0 < Real.sin (Real.pi / 32) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have hcos_eq : Real.cos (Real.pi + Real.pi / 32) = -Real.cos (Real.pi / 32) := by
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
    have hsin_eq : Real.sin (Real.pi + Real.pi / 32) = -Real.sin (Real.pi / 32) := by
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
    have hcos : Real.cos (Real.pi + Real.pi / 32) < 0 := by rw [hcos_eq]; linarith
    have hsin : Real.sin (Real.pi + Real.pi / 32) ≠ 0 := by rw [hsin_eq]; linarith
    have hslope : |Real.sin (Real.pi + Real.pi / 32)| <
        Real.tan (Real.pi / 16) * (-Real.cos (Real.pi + Real.pi / 32)) := by
      rw [hsin_eq, hcos_eq, abs_neg, abs_of_pos hsin_pos, neg_neg]
      exact sin_pi_div_32_lt_tan_pi_div_16_mul_cos
    exact phiLambdaAtTwo_expType_neg_wedge_ray hcos hsin hslope
  expType_minus := by
    have hcos_pos : 0 < Real.cos (Real.pi / 32) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hsin_pos : 0 < Real.sin (Real.pi / 32) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have hcos_eq : Real.cos (Real.pi - Real.pi / 32) = -Real.cos (Real.pi / 32) := by
      rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]; ring
    have hsin_eq : Real.sin (Real.pi - Real.pi / 32) = Real.sin (Real.pi / 32) := by
      rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]; ring
    have hcos : Real.cos (Real.pi - Real.pi / 32) < 0 := by rw [hcos_eq]; linarith
    have hsin : Real.sin (Real.pi - Real.pi / 32) ≠ 0 := by rw [hsin_eq]; linarith
    have hslope : |Real.sin (Real.pi - Real.pi / 32)| <
        Real.tan (Real.pi / 16) * (-Real.cos (Real.pi - Real.pi / 32)) := by
      rw [hsin_eq, hcos_eq, abs_of_pos hsin_pos, neg_neg]
      exact sin_pi_div_32_lt_tan_pi_div_16_mul_cos
    exact phiLambdaAtTwo_expType_neg_wedge_ray hcos hsin hslope

/-- **Unconditional All-Orders Asymptotic Expansion of `G_Lambda_atTwo_laplace`**:
Every point of `borelWedge (π / 4) (1 / 4)` satisfies `Re (2 + w) > 7 / 4 > 1`, where
`riemannZeta (2 + w) ≠ 0` directly from `riemannZeta_ne_zero_of_one_le_re`, and `phiLambdaAtTwo` is
uniformly bounded on `[0, ∞)`. -/
theorem G_Lambda_atTwo_laplace_hasAsympExp (j : ℕ) :
    HasAsympExp (iteratedDeriv j G_Lambda_atTwo_laplace) (d_u^[j] (formalSeries phiLambdaAtTwo)) := by
  let U : Set ℂ := borelWedge (Real.pi / 4) (1 / 4)
  have hU : Domain U := by
    refine ⟨Metric.isOpen_ball.union ?_, fun z hz t ht => ?_⟩
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im)
          (continuous_const.mul Complex.continuous_re))
    · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · left; simp
      · rcases hz with hzb | ⟨hre, him⟩
        · left
          rw [Metric.mem_ball, dist_zero_right] at hzb ⊢
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
          exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hzb
        · right
          refine ⟨by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero];
                     exact mul_pos ht_pos hre, ?_⟩
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero, add_zero]
          rw [abs_mul, abs_of_pos ht_pos]
          nlinarith
  have hray : ContainsRay U 1 := by
    intro v hv
    rw [one_mul]
    rcases eq_or_lt_of_le hv with rfl | hv_pos
    · left; simp
    · right
      change 0 < ((v : ℂ)).re ∧ |((v : ℂ)).im| < Real.tan (Real.pi / 4) * ((v : ℂ)).re
      rw [Real.tan_pi_div_four, one_mul]
      simpa using hv_pos
  have hana_U : AnalyticOnNhd ℂ phiLambdaAtTwo U := by
    intro z hz
    have hre : 1 < ((2 : ℂ) + z).re := by
      simp only [Complex.add_re, Complex.re_ofNat]
      rcases hz with hball | ⟨hre_pos, _⟩
      · rw [Metric.mem_ball, dist_zero_right] at hball
        have hre_abs : |z.re| < 1 / 4 := (Complex.abs_re_le_norm z).trans_lt hball
        linarith [(abs_lt.mp hre_abs).1]
      · linarith
    have hne1 : (2 : ℂ) + z ≠ 1 := by
      intro h0; rw [h0] at hre; simp at hre
    exact phiLambdaAtTwo_analyticAt hne1 (riemannZeta_ne_zero_of_one_le_re hre.le)
  have hexp_pos : ExpType (Minor.pull (1 : ℂ) phiLambdaAtTwo) := by
    obtain ⟨M₁, hM₁_nn, hM₁⟩ := logDeriv_riemannZeta_bounded_of_two_le_re
    refine ⟨M₁, 0, hM₁_nn, le_rfl, fun v hv => ?_⟩
    rw [zero_mul, Real.exp_zero, mul_one]
    change ‖(1 : ℂ) * phiLambdaAtTwo ((1 : ℂ) * (v : ℂ))‖ ≤ M₁
    rw [one_mul, one_mul, phiLambdaAtTwo, neg_div, norm_neg]
    exact hM₁ (2 + (v : ℂ)) (by simp only [Complex.add_re, Complex.re_ofNat, Complex.ofReal_re]; linarith)
  let a : Minor := Minor.mk 0 phiLambdaAtTwo
  have ha_good : a.Good U 1 := ⟨hana_U, hexp_pos⟩
  have hval : (fun u : ℝ => a.value 1 (u : ℂ)) = G_Lambda_atTwo_laplace := by
    funext u
    simp [a, Minor.value, complexLaplace, damped, Minor.pull, G_Lambda_atTwo_laplace]
  have hser : a.toSeries = formalSeries phiLambdaAtTwo := by
    ext n
    cases n <;> simp [a, Minor.toSeries, formalSeries]
  rw [← hval, ← hser]
  exact minor_value_hasAsympExp_uncond a hU hray ha_good (by simp) j

/-- **Asymmetric `s₀ = 2` Master Theorem 1 (`ℂ({t})` Strong D-Transcendence of Literal Von Mangoldt Moments OGF)**:
With ZERO hypotheses, `ogfOfEGF phiLambdaAtTwo` (whose `n`-th coefficient is the literal convergent
moment `(-1)^n ∑_{m ≥ 2} Λ(m) (log m)^n / m²`) is strongly differentially transcendental over
convergent meromorphic germs `ℂ({t})`. -/
theorem unconditional_G_Lambda_atTwo_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF phiLambdaAtTwo) :=
  ogf_stronglyDTrans_of_higherOrderBorel phiLambdaAtTwo_higherOrderBorelData

/-- **Asymmetric `s₀ = 2` Master Theorem 2 (`ℂ({1/u})` Strong D-Transcendence of Formal Series)**:
With ZERO hypotheses, `formalSeries phiLambdaAtTwo` is strongly differentially transcendental over
convergent meromorphic germs `ℂ({1/u})`. -/
theorem unconditional_G_Lambda_atTwo_formalSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (formalSeries phiLambdaAtTwo) :=
  stronglyDTrans_of_higher_order_borel phiLambdaAtTwo_higherOrderBorelData

/-- **Asymmetric `s₀ = 2` Master Theorem 3 (`ℂ{1/u}` Analytic ADE Obstruction for `G_Lambda_atTwo_laplace`)**:
With ZERO hypotheses, `G_Lambda_atTwo_laplace` satisfies NO nonzero convergent-germ algebraic
differential equation over `ℂ{1/u}` eventually as `u → +∞`. -/
theorem unconditional_G_Lambda_atTwo_laplace_no_conv_ade
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_atTwo_laplace u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) : Q = 0 :=
  no_conv_ade_of_higher_order_borel_asymp phiLambdaAtTwo_higherOrderBorelData
    G_Lambda_atTwo_laplace_hasAsympExp Q hQ

/-- **Asymmetric `s₀ = 2` Master Theorem 4 (`ℂ(u)` Analytic ADE Obstruction for `G_Lambda_atTwo_laplace`)**:
With ZERO hypotheses, `G_Lambda_atTwo_laplace` satisfies NO nonzero rational-coefficient algebraic
differential equation over `ℂ(u)` eventually as `u → +∞`. -/
theorem unconditional_G_Lambda_atTwo_laplace_no_rat_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_atTwo_laplace u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  no_rat_ade_of_higher_order_borel phiLambdaAtTwo_higherOrderBorelData
    G_Lambda_atTwo_laplace_hasAsympExp P hP

end
end PakPrimes.UnconditionalPrimeDTrans
