module

public import PakPrimes.BorelStokesVandermonde
public import PakPrimes.AutonomousTransfer
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Pak's ICM 2018 Conjecture 2.5b, Smooth Log Series, and Partitions into Primes

This module completes Links 3, 4, and 5 of the Borel–Stokes–Vandermonde proof:
1. **Abel summation & universal moment tower**:
   Expresses `scaledRay F u = e^{-u} F(e^{-e^{-u}})` as `scaledMoment S 0 u`, with unified
   `scaledOn` moment towers differentiating `scaledMoment`, `compactScaled`, and `remScaled`.
2. **Link 3 (`PNTAllOrders → HasAsympExp` / Watson's Lemma)**:
   Decomposes `scaledMoment li 0 u` via integration by parts and Fubini swap into the
   `Γ(1 - ξ)` Laplace transform `mainGamInt u` plus exponentially decaying boundary terms,
   proving all-orders `1/u` asymptotics `d_u^[j] gHat`.
3. **Main Theorems**:
   - `indicator_algebraicIndependent_of_pnt` & `pak_conjecture_2_5b_of_pnt`:
     Conditional on `PNTAllOrders`, both `I_prime` and `Pi_series` are differentially
     transcendental over `ℂ(q)`.
   - `logReciprocal_algebraicIndependent`:
     Unconditional (zero PNT hypothesis) differential transcendence of `∑_{n ≥ 2} q^n / log n`.
4. **Partitions into Primes (`∏_p (1 - q^p)^{-1}`)**:
   Constructs `partitionPrimesSeries`, proves `DiskCoeffBound partitionPrimesSeries`,
   `value partitionPrimesSeries (qRay u) ≠ 0`, `cPart_ne_zero` for the `ζ(2 - ξ)Γ(2 - ξ)`
   Stokes residues at `ξ ∈ {1, 2, 3, 5, 7, ...}`, `partitionPrimes_stokes_no_ade`,
   and `partitionPrimes_log_deriv_transfer`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.Main

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde PakPrimes.PrimeNome
open scoped Topology Nat.Prime

noncomputable section

/-! ### 1. Exponential Integrability, Abel Summation & Moment Towers -/

private lemma integrableOn_pow_mul_exp_neg_Ioi (k : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-t * x)) (Ioi 0) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have hlim : Tendsto (fun y : ℝ => y ^ k * Real.exp (-y)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  obtain ⟨Y₀, hY₀⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists_forall_of_atTop
  have hcont' : ContinuousOn (fun y : ℝ => y ^ k * Real.exp (-y)) (Icc 0 (max 1 Y₀)) := by fun_prop
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont'
  let B : ℝ := max 1 B₀
  have hB_nonneg : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
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
      _ ≤ B * (2 / t) ^ k * Real.exp (-(t / 2) * x) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
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

lemma exp_neg_mul_le_inv_pow (c : ℝ) (hc : 0 < c) (M : ℕ) {u : ℝ} (hu : 0 < u) :
    Real.exp (-c * u) ≤ (M.factorial : ℝ) / c ^ M / u ^ M := by
  have h1 := Real.pow_div_factorial_le_exp (c * u) (mul_nonneg hc.le hu.le) M
  have hpos_pow : 0 < (c * u) ^ M / (M.factorial : ℝ) := by positivity
  have hexp : Real.exp (-c * u) = (Real.exp (c * u))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hexp]
  calc (Real.exp (c * u))⁻¹ ≤ ((c * u) ^ M / (M.factorial : ℝ))⁻¹ := inv_anti₀ hpos_pow h1
    _ = (M.factorial : ℝ) / c ^ M / u ^ M := by
        rw [inv_div, mul_pow]
        field_simp [hc.ne', hu.ne']

/-- Abel summation relating bounded sequences with `a 0 = a 1 = 0` to `t * ∫_{Ioi 2} S ⌊x⌋₊ e^{-tx}`. -/
lemma tsum_mul_exp_eq_integral (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (ha_bdd : ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C) (S : ℕ → ℝ)
    (hS : ∀ n : ℕ, S n = ∑ k ∈ Finset.range (n + 1), a k) {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, a n * Real.exp (-t * (n : ℝ))) =
      t * ∫ x in Ioi (2 : ℝ), S ⌊x⌋₊ * Real.exp (-t * x) := by
  obtain ⟨C, hC⟩ := ha_bdd
  let C₀ : ℝ := max C 0
  have hC₀ : ∀ n : ℕ, |a n| ≤ C₀ := fun n => (hC n).trans (le_max_left _ _)
  have hC₀_nonneg : 0 ≤ C₀ := le_max_right _ _
  have hS_bdd : ∀ n : ℕ, |S n| ≤ C₀ * (n + 1 : ℝ) := fun n => by
    rw [hS n]
    calc |∑ k ∈ Finset.range (n + 1), a k|
        ≤ ∑ k ∈ Finset.range (n + 1), |a k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), C₀ := Finset.sum_le_sum fun k _ => hC₀ k
      _ = C₀ * (n + 1 : ℝ) := by simp [Finset.card_range, mul_comm]
  have hS1 : S 1 = 0 := by
    rw [hS 1, Finset.sum_range_succ, Finset.sum_range_one, ha0, ha1, add_zero]
  have hmeas_S : Measurable (fun x : ℝ => S ⌊x⌋₊) :=
    (measurable_of_countable S).comp Nat.measurable_floor
  have hmeas_f : Measurable (fun x : ℝ => S ⌊x⌋₊ * Real.exp (-t * x)) :=
    hmeas_S.mul (by fun_prop)
  have hint_dom : IntegrableOn (fun x : ℝ => C₀ * (x * Real.exp (-t * x) + Real.exp (-t * x))) (Ioi 2) := by
    have h1' : IntegrableOn (fun x : ℝ => x * Real.exp (-t * x)) (Ioi 0) := by
      simpa using integrableOn_pow_mul_exp_neg_Ioi 1 ht
    have h0' : IntegrableOn (fun x : ℝ => Real.exp (-t * x)) (Ioi 0) := by
      simpa using integrableOn_pow_mul_exp_neg_Ioi 0 ht
    exact ((h1'.mono_set (Ioi_subset_Ioi (by norm_num))).add
      (h0'.mono_set (Ioi_subset_Ioi (by norm_num)))).const_mul C₀
  have hint_Ioi : IntegrableOn (fun x : ℝ => S ⌊x⌋₊ * Real.exp (-t * x)) (Ioi 2) := by
    refine hint_dom.mono' hmeas_f.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    change 2 < x at hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hfl : (⌊x⌋₊ : ℝ) + 1 ≤ x + 1 := by
      linarith [Nat.floor_le (by linarith [hx] : 0 ≤ x)]
    calc |S ⌊x⌋₊| * Real.exp (-t * x) ≤ (C₀ * (⌊x⌋₊ + 1 : ℝ)) * Real.exp (-t * x) :=
          mul_le_mul_of_nonneg_right (hS_bdd ⌊x⌋₊) (Real.exp_pos _).le
      _ ≤ (C₀ * (x + 1)) * Real.exp (-t * x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfl hC₀_nonneg) (Real.exp_pos _).le
      _ = C₀ * (x * Real.exp (-t * x) + Real.exp (-t * x)) := by ring
  have hcell (N : ℕ) :
      t * ∫ x in (N : ℝ)..((N + 1 : ℕ) : ℝ), S ⌊x⌋₊ * Real.exp (-t * x) =
        S N * (Real.exp (-t * (N : ℝ)) - Real.exp (-t * ((N + 1 : ℕ) : ℝ))) := by
    have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
    have hcongr : ∫ x in Ioo (N : ℝ) ((N + 1 : ℕ) : ℝ), S ⌊x⌋₊ * Real.exp (-t * x) =
        ∫ x in Ioo (N : ℝ) ((N + 1 : ℕ) : ℝ), S N * Real.exp (-t * x) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg N) hx.1.le
      have hfl : ⌊x⌋₊ = N := (Nat.floor_eq_iff hx0).mpr ⟨hx.1.le, by exact_mod_cast hx.2⟩
      rw [hfl]
    rw [hcongr, integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle]
    have hderiv : ∀ x ∈ uIcc (N : ℝ) ((N + 1 : ℕ) : ℝ),
        HasDerivAt (fun y : ℝ => -(Real.exp (-t * y)) / t) (Real.exp (-t * x)) x := by
      intro x _
      have hlin : HasDerivAt (fun y : ℝ => -t * y) (-t) x := by
        simpa using (hasDerivAt_id x).const_mul (-t)
      have hd := hlin.exp.neg.div_const t
      refine hd.congr_deriv ?_
      field_simp [ht.ne']
    have hint_exp : IntervalIntegrable (fun x : ℝ => Real.exp (-t * x)) volume N ((N + 1 : ℕ) : ℝ) :=
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (-t * x))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_exp]
    field_simp [ht.ne']
    ring
  have hfinite (M : ℕ) :
      t * ∫ x in (2 : ℝ)..((M + 2 : ℕ) : ℝ), S ⌊x⌋₊ * Real.exp (-t * x) =
        (∑ k ∈ Finset.range M, a (k + 2) * Real.exp (-t * ((k + 2 : ℕ) : ℝ))) -
          S (M + 1) * Real.exp (-t * ((M + 2 : ℕ) : ℝ)) := by
    induction M with
    | zero => simp [hS1]
    | succ M ih =>
      have hi1 : IntervalIntegrable (fun x : ℝ => S ⌊x⌋₊ * Real.exp (-t * x)) volume 2 ((M + 2 : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast (by omega : 2 ≤ M + 2))).mpr
          (hint_Ioi.mono_set fun x hx => hx.1)
      have hi2 : IntervalIntegrable (fun x : ℝ => S ⌊x⌋₊ * Real.exp (-t * x)) volume
          ((M + 2 : ℕ) : ℝ) ((M + 3 : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast (by omega : M + 2 ≤ M + 3))).mpr
          (hint_Ioi.mono_set fun x hx => lt_of_le_of_lt (by exact_mod_cast (by omega : 2 ≤ M + 2)) hx.1)
      have hc' := hcell (M + 2)
      rw [show (M + 2 + 1 : ℕ) = M + 1 + 2 by omega] at hc'
      rw [show (M + 1 + 2 : ℕ) = M + 3 by omega]
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
        mul_add, ih, hc', Finset.sum_range_succ, show M + 3 = M + 1 + 2 by omega]
      have hS_step : S (M + 2) = S (M + 1) + a (M + 2) := by
        rw [hS (M + 2), hS (M + 1), Finset.sum_range_succ]
      rw [hS_step]
      ring
  have hlim_int : Tendsto (fun M : ℕ => t * ∫ x in (2 : ℝ)..((M + 2 : ℕ) : ℝ), S ⌊x⌋₊ * Real.exp (-t * x))
      atTop (𝓝 (t * ∫ x in Ioi (2 : ℝ), S ⌊x⌋₊ * Real.exp (-t * x))) := by
    refine tendsto_const_nhds.mul ?_
    exact intervalIntegral_tendsto_integral_Ioi (a := 2) hint_Ioi
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hsum_a : Summable (fun n : ℕ => a n * Real.exp (-t * (n : ℝ))) := by
    have hr : ‖Real.exp (-t)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]; linarith
    refine ((summable_geometric_of_norm_lt_one hr).mul_left C₀).of_norm_bounded fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      show Real.exp (-t * (n : ℝ)) = Real.exp (-t) ^ n by rw [← Real.exp_nat_mul]; congr 1; ring]
    exact mul_le_mul_of_nonneg_right (hC₀ n) (pow_nonneg (Real.exp_pos _).le n)
  have hsum_tail : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, a (k + 2) * Real.exp (-t * ((k + 2 : ℕ) : ℝ)))
      atTop (𝓝 (∑' n : ℕ, a n * Real.exp (-t * (n : ℝ)))) := by
    have hsplit : ∑' n : ℕ, a n * Real.exp (-t * (n : ℝ)) =
        ∑' k : ℕ, a (k + 2) * Real.exp (-t * ((k + 2 : ℕ) : ℝ)) := by
      have h2 := hsum_a.sum_add_tsum_nat_add 2
      rw [Finset.sum_range_succ, Finset.sum_range_one, ha0, ha1, zero_mul, zero_mul, add_zero,
        zero_add] at h2
      exact h2.symm
    rw [hsplit]
    exact (hsum_a.comp_injective fun _ _ h => Nat.add_right_cancel h).hasSum.tendsto_sum_nat
  have hlim_rem : Tendsto (fun M : ℕ => S (M + 1) * Real.exp (-t * ((M + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun M : ℕ => C₀ * (((M + 2 : ℕ) : ℝ) * Real.exp (-t * ((M + 2 : ℕ) : ℝ)))) ?_ ?_
    · refine .of_forall fun M => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |S (M + 1)| * Real.exp (-t * ((M + 2 : ℕ) : ℝ))
          ≤ (C₀ * ((M + 1 : ℕ) + 1 : ℝ)) * Real.exp (-t * ((M + 2 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (hS_bdd (M + 1)) (Real.exp_pos _).le
        _ = C₀ * (((M + 2 : ℕ) : ℝ) * Real.exp (-t * ((M + 2 : ℕ) : ℝ))) := by push_cast; ring
    · have h1 : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have h2 : Tendsto (fun M : ℕ => ((M + 2 : ℕ) : ℝ) * Real.exp (-t * ((M + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
        have hcomp := h1.comp (tendsto_id.const_mul_atTop ht |>.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)))
        have hdiv := hcomp.const_mul t⁻¹
        rw [mul_zero] at hdiv
        refine hdiv.congr fun M => ?_
        simp only [Function.comp_def, id_eq, neg_mul]
        field_simp [ht.ne']
      simpa using h2.const_mul C₀
  have hlim_rhs := hsum_tail.sub hlim_rem
  rw [sub_zero] at hlim_rhs
  have heq : (fun M : ℕ => t * ∫ x in (2 : ℝ)..((M + 2 : ℕ) : ℝ), S ⌊x⌋₊ * Real.exp (-t * x)) =
      fun M => (∑ k ∈ Finset.range M, a (k + 2) * Real.exp (-t * ((k + 2 : ℕ) : ℝ))) -
        S (M + 1) * Real.exp (-t * ((M + 2 : ℕ) : ℝ)) := funext hfinite
  rw [heq] at hlim_int
  exact tendsto_nhds_unique hlim_rhs hlim_int

/-- Linear growth and measurability on `(2, ∞)`. -/
@[expose] def LinearGrowthOnIoi2 (B : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable B (volume.restrict (Ioi 2)) ∧
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ x : ℝ, 2 < x → |B x| ≤ K₀ * x

lemma LinearGrowthOnIoi2.sub {A B : ℝ → ℝ} (hA : LinearGrowthOnIoi2 A) (hB : LinearGrowthOnIoi2 B) :
    LinearGrowthOnIoi2 (fun x => A x - B x) := by
  obtain ⟨mA, KA, hKA, bA⟩ := hA
  obtain ⟨mB, KB, hKB, bB⟩ := hB
  refine ⟨mA.sub mB, KA + KB, add_nonneg hKA hKB, fun x hx => ?_⟩
  calc |A x - B x| ≤ |A x| + |B x| := abs_sub _ _
    _ ≤ KA * x + KB * x := add_le_add (bA x hx) (bB x hx)
    _ = (KA + KB) * x := by ring

@[expose] def momentInt (B : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x in Ioi (2 : ℝ), B x * x ^ k * Real.exp (-t * x)

@[expose] def scaledOn (shift : ℕ) (B : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-((k + shift : ℕ) : ℝ) * u) * momentInt B k (Real.exp (-u))

@[expose] def scaledMoment (B : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  scaledOn 2 B k u

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

private def towerCoeff (shift : ℕ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, k => -((k + shift : ℕ) : ℝ) * towerCoeff shift j k +
      if k = 0 then 0 else towerCoeff shift j (k - 1)

private lemma towerCoeff_eq_zero_of_lt (shift : ℕ) {j k : ℕ} (h : j < k) : towerCoeff shift j k = 0 := by
  induction j generalizing k with
  | zero =>
    have hk : k ≠ 0 := by omega
    simp [towerCoeff, hk]
  | succ j ih =>
    have hk0 : k ≠ 0 := by omega
    rw [towerCoeff]
    simp [hk0, ih (k := k) (by omega), ih (k := k - 1) (by omega)]

private lemma expScaled_hasDerivAt (shift : ℕ) {M : ℕ → ℝ → ℝ}
    (hM : ∀ k : ℕ, ∀ {t : ℝ}, 0 < t → HasDerivAt (M k) (-M (k + 1) t) t) (k : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-((k + shift : ℕ) : ℝ) * x) * M k (Real.exp (-x)))
      (-((k + shift : ℕ) : ℝ) * (Real.exp (-((k + shift : ℕ) : ℝ) * u) * M k (Real.exp (-u))) +
        Real.exp (-((k + 1 + shift : ℕ) : ℝ) * u) * M (k + 1) (Real.exp (-u))) u := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-((k + shift : ℕ) : ℝ) * x))
      (-((k + shift : ℕ) : ℝ) * Real.exp (-((k + shift : ℕ) : ℝ) * u)) u := by
    simpa [mul_comm] using ((hasDerivAt_id u).const_mul (-((k + shift : ℕ) : ℝ))).exp
  have ht : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u := by
    simpa [mul_comm] using (hasDerivAt_id u).neg.exp
  have hm := (hM k (Real.exp_pos (-u))).comp u ht
  refine (he.mul hm).congr_deriv ?_
  have hpow : Real.exp (-((k + shift : ℕ) : ℝ) * u) * Real.exp (-u) =
      Real.exp (-((k + 1 + shift : ℕ) : ℝ) * u) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  calc -((k + shift : ℕ) : ℝ) * Real.exp (-((k + shift : ℕ) : ℝ) * u) * M k (Real.exp (-u)) +
        Real.exp (-((k + shift : ℕ) : ℝ) * u) * (-M (k + 1) (Real.exp (-u)) * -Real.exp (-u))
      = -((k + shift : ℕ) : ℝ) * (Real.exp (-((k + shift : ℕ) : ℝ) * u) * M k (Real.exp (-u))) +
          (Real.exp (-((k + shift : ℕ) : ℝ) * u) * Real.exp (-u)) * M (k + 1) (Real.exp (-u)) := by ring
    _ = _ := by rw [hpow]

private lemma expScaled_iteratedDeriv (shift : ℕ) {M : ℕ → ℝ → ℝ}
    (hM : ∀ k : ℕ, ∀ {t : ℝ}, 0 < t → HasDerivAt (M k) (-M (k + 1) t) t) (j : ℕ) :
    (∀ u : ℝ, iteratedDeriv j (fun x => Real.exp (-((0 + shift : ℕ) : ℝ) * x) * M 0 (Real.exp (-x))) u =
      ∑ k ∈ Finset.range (j + 1), towerCoeff shift j k *
        (Real.exp (-((k + shift : ℕ) : ℝ) * u) * M k (Real.exp (-u)))) ∧
    Differentiable ℝ (iteratedDeriv j (fun x => Real.exp (-((0 + shift : ℕ) : ℝ) * x) * M 0 (Real.exp (-x)))) := by
  let S : ℕ → ℝ → ℝ := fun k u => Real.exp (-((k + shift : ℕ) : ℝ) * u) * M k (Real.exp (-u))
  change (∀ u : ℝ, iteratedDeriv j (S 0) u = ∑ k ∈ Finset.range (j + 1), towerCoeff shift j k * S k u) ∧
    Differentiable ℝ (iteratedDeriv j (S 0))
  induction j with
  | zero =>
    refine ⟨fun u => by simp [towerCoeff], fun u => (expScaled_hasDerivAt shift hM 0 u).differentiableAt⟩
  | succ j ih =>
    have heq : iteratedDeriv j (S 0) =
        fun u : ℝ => ∑ k ∈ Finset.range (j + 1), towerCoeff shift j k * S k u :=
      funext ih.1
    have hderiv (u : ℝ) : HasDerivAt (iteratedDeriv j (S 0))
        (∑ k ∈ Finset.range (j + 2), towerCoeff shift (j + 1) k * S k u) u := by
      rw [heq]
      have hsum := HasDerivAt.fun_sum fun k (_ : k ∈ Finset.range (j + 1)) =>
        ((expScaled_hasDerivAt shift hM k u).const_mul (towerCoeff shift j k))
      refine hsum.congr_deriv ?_
      have hsplit1 : (∑ k ∈ Finset.range (j + 1), towerCoeff shift j k *
          (-((k + shift : ℕ) : ℝ) * S k u + S (k + 1) u)) =
          (∑ k ∈ Finset.range (j + 1), -((k + shift : ℕ) : ℝ) * towerCoeff shift j k * S k u) +
            ∑ k ∈ Finset.range (j + 1), towerCoeff shift j k * S (k + 1) u := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      have hpad : ∑ k ∈ Finset.range (j + 1), -((k + shift : ℕ) : ℝ) * towerCoeff shift j k * S k u =
          ∑ k ∈ Finset.range (j + 2), -((k + shift : ℕ) : ℝ) * towerCoeff shift j k * S k u := by
        symm
        rw [Finset.sum_range_succ, towerCoeff_eq_zero_of_lt shift (Nat.lt_succ_self j)]
        simp
      have hshift : ∑ k ∈ Finset.range (j + 1), towerCoeff shift j k * S (k + 1) u =
          ∑ k ∈ Finset.range (j + 2), (if k = 0 then 0 else towerCoeff shift j (k - 1)) * S k u := by
        symm
        rw [Finset.sum_range_succ']
        simp only [↓reduceIte, zero_mul, add_zero, Nat.succ_ne_zero, Nat.add_sub_cancel]
      rw [hsplit1, hpad, hshift, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by simp [towerCoeff, add_mul]
    refine ⟨fun u => by rw [iteratedDeriv_succ, (hderiv u).deriv], fun u => ?_⟩
    have heq' : iteratedDeriv (j + 1) (S 0) =
        fun x : ℝ => ∑ k ∈ Finset.range (j + 2), towerCoeff shift (j + 1) k * S k x :=
      funext fun x => by rw [iteratedDeriv_succ, (hderiv x).deriv]
    rw [heq']
    exact DifferentiableAt.fun_sum fun k _ =>
      ((expScaled_hasDerivAt shift hM k u).differentiableAt.const_mul (towerCoeff shift (j + 1) k))

private lemma scaledOn_iteratedDeriv (shift : ℕ) {B : ℝ → ℝ} (hB : LinearGrowthOnIoi2 B) (j : ℕ) :
    (∀ u : ℝ, iteratedDeriv j (scaledOn shift B 0) u =
      ∑ k ∈ Finset.range (j + 1), towerCoeff shift j k * scaledOn shift B k u) ∧
    Differentiable ℝ (iteratedDeriv j (scaledOn shift B 0)) :=
  expScaled_iteratedDeriv shift (fun k {_} ht => momentInt_hasDerivAt hB k ht) j

private lemma scaledMoment_sub {A B : ℝ → ℝ} (hA : LinearGrowthOnIoi2 A) (hB : LinearGrowthOnIoi2 B)
    (k : ℕ) (u : ℝ) :
    scaledMoment A k u - scaledMoment B k u = scaledMoment (fun x => A x - B x) k u := by
  unfold scaledMoment scaledOn momentInt
  rw [← mul_sub, ← integral_sub (momentInt_integrableOn hA k (Real.exp_pos (-u)))
    (momentInt_integrableOn hB k (Real.exp_pos (-u)))]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring

/-- Compact-interval moment tower on `(0, 2]` for integrable kernels `W`. -/
@[expose] def compactMoment (W : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) 2, W x * x ^ k * Real.exp (-t * x)

@[expose] def compactScaled (W : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-((k + 1 : ℕ) : ℝ) * u) * compactMoment W k (Real.exp (-u))

private lemma compactMoment_integrableOn {W : ℝ → ℝ} (hW : IntegrableOn W (Ioc 0 2))
    (k : ℕ) (t : ℝ) :
    IntegrableOn (fun x : ℝ => W x * x ^ k * Real.exp (-t * x)) (Ioc 0 2) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => W x * x ^ k * Real.exp (-t * x))
      (volume.restrict (Ioc 0 2)) :=
    (hW.aestronglyMeasurable.mul (by fun_prop : Measurable (fun x : ℝ => x ^ k)).aestronglyMeasurable).mul
      (by fun_prop : Measurable (fun x : ℝ => Real.exp (-t * x))).aestronglyMeasurable
  let C : ℝ := 2 ^ k * max (Real.exp (-2 * t)) 1
  refine (hW.norm.const_mul C).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (pow_nonneg hx.1.le k)]
  have hxk : x ^ k ≤ 2 ^ k := pow_le_pow_left₀ hx.1.le hx.2 k
  have hexp : Real.exp (-t * x) ≤ max (Real.exp (-2 * t)) 1 := by
    by_cases ht0 : 0 ≤ t
    · exact (Real.exp_le_one_iff.mpr (by nlinarith [hx.1])).trans (le_max_right _ _)
    · exact (Real.exp_le_exp.mpr (by nlinarith [hx.2])).trans (le_max_left _ _)
  calc |W x| * x ^ k * Real.exp (-t * x)
      ≤ |W x| * 2 ^ k * max (Real.exp (-2 * t)) 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hxk (abs_nonneg _)) hexp (Real.exp_pos _).le (by positivity)
    _ = C * ‖W x‖ := by rw [Real.norm_eq_abs]; dsimp [C]; ring

private lemma compactMoment_hasDerivAt {W : ℝ → ℝ} (hW : IntegrableOn W (Ioc 0 2)) (k : ℕ) (t : ℝ) :
    HasDerivAt (compactMoment W k) (-compactMoment W (k + 1) t) t := by
  let F : ℝ → ℝ → ℝ := fun s x => W x * x ^ k * Real.exp (-s * x)
  let F' : ℝ → ℝ → ℝ := fun s x => -(W x * x ^ (k + 1) * Real.exp (-s * x))
  let B : ℝ := 2 ^ (k + 1) * Real.exp (2 * (|t| + 1))
  let bound : ℝ → ℝ := fun x => B * |W x|
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (volume.restrict (Ioc 0 2)) :=
    .of_forall fun s =>
      (hW.aestronglyMeasurable.mul (by fun_prop : Measurable (fun x : ℝ => x ^ k)).aestronglyMeasurable).mul
        (by fun_prop : Measurable (fun x : ℝ => Real.exp (-s * x))).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' t) (volume.restrict (Ioc 0 2)) :=
    ((hW.aestronglyMeasurable.mul (by fun_prop : Measurable (fun x : ℝ => x ^ (k + 1))).aestronglyMeasurable).mul
      (by fun_prop : Measurable (fun x : ℝ => Real.exp (-t * x))).aestronglyMeasurable).neg
  have hbound_int : IntegrableOn bound (Ioc 0 2) :=
    IntegrableOn.congr_fun (hW.norm.const_mul B)
      (fun x _ => by simp [bound, Real.norm_eq_abs]) measurableSet_Ioc
  have hbound : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 2), ∀ s ∈ Metric.ball t 1, ‖F' s x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    intro s hs
    have hsabs : |s| ≤ |t| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hs; linarith [abs_sub_abs_le_abs_sub s t]
    rw [Real.norm_eq_abs]
    simp only [F', abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (pow_nonneg hx.1.le (k + 1))]
    have hexp : Real.exp (-s * x) ≤ Real.exp (2 * (|t| + 1)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : -s * x ≤ |s| * x := by nlinarith [hx.1, neg_le_abs s]
      have h2 : |s| * x ≤ (|t| + 1) * 2 := mul_le_mul hsabs hx.2 hx.1.le (by positivity)
      linarith
    calc |W x| * x ^ (k + 1) * Real.exp (-s * x)
        ≤ |W x| * 2 ^ (k + 1) * Real.exp (2 * (|t| + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1.le hx.2 _) (abs_nonneg _))
            hexp (Real.exp_pos _).le (by positivity)
      _ = bound x := by dsimp [bound]; ring
  have hderiv : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 2), ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun r => F r x) (F' s x) s := by
    refine .of_forall fun x s _ => ?_
    have h1 : HasDerivAt (fun r => Real.exp (-r * x)) (-x * Real.exp (-s * x)) s := by
      have hr : HasDerivAt (fun r => -r * x) (-x) s := by
        simpa using ((hasDerivAt_id s).neg.mul_const x)
      convert hr.exp using 1; ring
    convert h1.const_mul (W x * x ^ k) using 1
    dsimp [F, F']; rw [pow_succ]; ring
  have res := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t zero_lt_one)
    hmeas (compactMoment_integrableOn hW k t) hmeas' hbound hbound_int hderiv).2
  convert res using 1
  · funext s; simp only [compactMoment, F, neg_mul]
  · simp only [compactMoment, F', integral_neg, neg_mul]

private lemma compactScaled_iteratedDeriv {W : ℝ → ℝ} (hW : IntegrableOn W (Ioc 0 2)) (j : ℕ) :
    (∀ u : ℝ, iteratedDeriv j (compactScaled W 0) u =
      ∑ k ∈ Finset.range (j + 1), towerCoeff 1 j k * compactScaled W k u) ∧
    Differentiable ℝ (iteratedDeriv j (compactScaled W 0)) :=
  expScaled_iteratedDeriv 1 (fun k {_} _ => compactMoment_hasDerivAt hW k _) j

private lemma compactScaled_exp_decay {W : ℝ → ℝ} (hW : IntegrableOn W (Ioc 0 2)) (j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      |iteratedDeriv j (compactScaled W 0) u| ≤ C * Real.exp (-u) := by
  let I : ℝ := ∫ x in Ioc (0 : ℝ) 2, |W x|
  let C : ℝ := ∑ k ∈ Finset.range (j + 1), |towerCoeff 1 j k| * (2 ^ k * I)
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [(compactScaled_iteratedDeriv hW j).1 u]
  calc |∑ k ∈ Finset.range (j + 1), towerCoeff 1 j k * compactScaled W k u|
      ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff 1 j k * compactScaled W k u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff 1 j k| * (2 ^ k * I) * Real.exp (-u) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        have hk_bd : |compactScaled W k u| ≤ 2 ^ k * I * Real.exp (-u) := by
          unfold compactScaled compactMoment
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hint_le : |∫ x in Ioc (0 : ℝ) 2, W x * x ^ k * Real.exp (-Real.exp (-u) * x)| ≤ 2 ^ k * I := by
            calc |∫ x in Ioc (0 : ℝ) 2, W x * x ^ k * Real.exp (-Real.exp (-u) * x)|
                ≤ ∫ x in Ioc (0 : ℝ) 2, |W x * x ^ k * Real.exp (-Real.exp (-u) * x)| := by
                  simpa only [Real.norm_eq_abs] using
                    norm_integral_le_integral_norm (fun x => W x * x ^ k * Real.exp (-Real.exp (-u) * x))
              _ ≤ ∫ x in Ioc (0 : ℝ) 2, 2 ^ k * |W x| := by
                  refine setIntegral_mono_on (compactMoment_integrableOn hW k _).norm
                    (IntegrableOn.congr_fun (hW.norm.const_mul (2 ^ k))
                      (fun x _ => by simp [Real.norm_eq_abs]) measurableSet_Ioc)
                    measurableSet_Ioc fun x hx => ?_
                  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
                    abs_of_nonneg (pow_nonneg hx.1.le k)]
                  have hle1 : Real.exp (-Real.exp (-u) * x) ≤ 1 :=
                    Real.exp_le_one_iff.mpr (by nlinarith [hx.1, Real.exp_pos (-u)])
                  calc |W x| * x ^ k * Real.exp (-Real.exp (-u) * x)
                      ≤ |W x| * 2 ^ k * 1 :=
                        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1.le hx.2 _) (abs_nonneg _))
                          hle1 (Real.exp_pos _).le (by positivity)
                    _ = 2 ^ k * |W x| := by ring
              _ = 2 ^ k * I := by rw [integral_const_mul]
          have hexp_le : Real.exp (-((k + 1 : ℕ) : ℝ) * u) ≤ Real.exp (-u) := by
            rw [Real.exp_le_exp]; push_cast; nlinarith
          calc Real.exp (-((k + 1 : ℕ) : ℝ) * u) *
                |∫ x in Ioc (0 : ℝ) 2, W x * x ^ k * Real.exp (-Real.exp (-u) * x)|
              ≤ Real.exp (-u) * (2 ^ k * I) :=
                mul_le_mul hexp_le hint_le (abs_nonneg _) (Real.exp_pos _).le
            _ = 2 ^ k * I * Real.exp (-u) := by ring
        calc |towerCoeff 1 j k| * |compactScaled W k u|
            ≤ |towerCoeff 1 j k| * (2 ^ k * I * Real.exp (-u)) :=
              mul_le_mul_of_nonneg_left hk_bd (abs_nonneg _)
          _ = |towerCoeff 1 j k| * (2 ^ k * I) * Real.exp (-u) := by ring
    _ = C * Real.exp (-u) := by rw [← Finset.sum_mul]

/-! ### 2. Logarithmic Integral, `li`-Approximation & Link 3 (Watson's Lemma) -/

/-- The logarithmic integral `li(x) = ∫_2^x dt / log t`. -/
@[expose] def li (x : ℝ) : ℝ :=
  ∫ v in (2 : ℝ)..x, (Real.log v)⁻¹

/-- All-orders Prime Number Theorem error hypothesis. -/
@[expose] def PNTAllOrders : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - li x| ≤ C * x / (Real.log x) ^ M

/-- Unified `li`-approximation hypothesis for real functions `A` on `[2, ∞)`. -/
@[expose] def ApproxLi (A : ℝ → ℝ) : Prop :=
  LinearGrowthOnIoi2 A ∧
    ∀ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, |A x - li x| ≤ C * x / (Real.log x) ^ M

private lemma li_integrand_contOn : ContinuousOn (fun v : ℝ => (Real.log v)⁻¹) (Ici 2) := fun v hv =>
  (Real.continuousAt_log (by linarith [Set.mem_Ici.mp hv] : v ≠ 0)).continuousWithinAt.inv₀
    (Real.log_pos (by linarith [Set.mem_Ici.mp hv] : 1 < v)).ne'

private lemma li_intervalIntegrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun v : ℝ => (Real.log v)⁻¹) volume 2 x :=
  (li_integrand_contOn.mono (by rw [uIcc_of_le hx]; exact Icc_subset_Ici_self)).intervalIntegrable

private lemma li_hasDerivAt {x : ℝ} (hx : 2 < x) : HasDerivAt li (Real.log x)⁻¹ x := by
  have hint := li_intervalIntegrable hx.le
  have hcontAt : ContinuousAt (fun v : ℝ => (Real.log v)⁻¹) x :=
    (Real.continuousAt_log (by linarith : x ≠ 0)).inv₀ (Real.log_pos (by linarith : 1 < x)).ne'
  have hmeas : StronglyMeasurableAtFilter (fun v : ℝ => (Real.log v)⁻¹) (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (show IsOpen (Ioi (2 : ℝ)) from isOpen_Ioi) (fun y hy =>
      (Real.continuousAt_log (by linarith [Set.mem_Ioi.mp hy] : y ≠ 0)).inv₀
        (Real.log_pos (by linarith [Set.mem_Ioi.mp hy] : 1 < y)).ne') x hx
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt

private lemma li_bounds {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ li x ∧ li x ≤ (Real.log 2)⁻¹ * (x - 2) := by
  have hcont := li_intervalIntegrable hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnonneg : ∀ v ∈ Ioc (2 : ℝ) x, 0 ≤ (Real.log v)⁻¹ := fun v hv =>
    inv_nonneg.mpr (Real.log_pos (by linarith [hv.1])).le
  have hle : ∀ v ∈ Ioc (2 : ℝ) x, (Real.log v)⁻¹ ≤ (Real.log 2)⁻¹ := fun v hv =>
    inv_anti₀ hlog2 (Real.log_le_log (by norm_num) hv.1.le)
  have h1 : 0 ≤ li x := by
    unfold li
    rw [intervalIntegral.integral_of_le hx]
    exact setIntegral_nonneg measurableSet_Ioc hnonneg
  have h2 : li x ≤ (Real.log 2)⁻¹ * (x - 2) := by
    unfold li
    rw [intervalIntegral.integral_of_le hx]
    have hint1 : IntegrableOn (fun _ : ℝ => (Real.log 2)⁻¹) (Ioc 2 x) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have := setIntegral_mono_on hcont.1 hint1 measurableSet_Ioc hle
    simpa [Real.volume_Ioc, hx, mul_comm] using this
  exact ⟨h1, h2⟩

private lemma li_linearGrowth : LinearGrowthOnIoi2 li := by
  refine ⟨?_, (Real.log 2)⁻¹, inv_nonneg.mpr (Real.log_nonneg one_le_two), fun x hx => ?_⟩
  · have hdiff : DifferentiableOn ℝ li (Ioi 2) := fun x hx =>
      (li_hasDerivAt hx).differentiableAt.differentiableWithinAt
    exact (hdiff.continuousOn).aestronglyMeasurable measurableSet_Ioi
  · obtain ⟨h0, hle⟩ := li_bounds hx.le
    rw [abs_of_nonneg h0]
    have hlog2 : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_nonneg one_le_two)
    exact hle.trans (mul_le_mul_of_nonneg_left (by linarith) hlog2)

private lemma inv_log_eq_integral_rpow {x : ℝ} (hx : 1 < x) :
    (Real.log x)⁻¹ = (∫ ξ in (0 : ℝ)..(1 / 2), x ^ (-ξ)) + x ^ (-(1 / 2 : ℝ)) / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hderiv : ∀ ξ ∈ uIcc (0 : ℝ) (1 / 2),
      HasDerivAt (fun s : ℝ => -(Real.log x)⁻¹ * Real.exp (-Real.log x * s)) (x ^ (-ξ)) ξ := by
    intro ξ _
    have hd : HasDerivAt (fun s : ℝ => -Real.log x * s) (-Real.log x) ξ := by
      simpa using (hasDerivAt_id ξ).const_mul (-Real.log x)
    convert (hd.exp.const_mul (-(Real.log x)⁻¹)) using 1
    rw [Real.rpow_def_of_pos hx0]
    field_simp [hlog.ne']
  have hint : IntervalIntegrable (fun ξ : ℝ => x ^ (-ξ)) volume 0 (1 / 2) :=
    (Continuous.rpow continuous_const continuous_neg (fun _ => Or.inl hx0.ne')).intervalIntegrable 0 (1 / 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    show Real.exp (-Real.log x * 0) = 1 by simp,
    show Real.exp (-Real.log x * (1 / 2)) = x ^ (-(1 / 2 : ℝ)) by
      rw [Real.rpow_def_of_pos hx0]; congr 1; ring]
  ring

private def cutKernel (x : ℝ) : ℝ :=
  ∫ ξ in (0 : ℝ)..(1 / 2), x ^ (-ξ)

private def remLogKernel (x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) / Real.log x

private lemma cutKernel_integrableOn : IntegrableOn cutKernel (Ioc 0 2) := by
  have heq : cutKernel = fun x : ℝ => ∫ ξ in Ioc (0 : ℝ) (1 / 2), x ^ (-ξ) := by
    funext x; exact intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [heq]
  have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) + 1) (Ioc 0 2) := by
    have hr : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2)))
    exact hr.add (integrableOn_const (hs := measure_Ioc_lt_top.ne))
  have hprod_dom : Integrable (fun p : ℝ × ℝ => p.1 ^ (-(1 / 2 : ℝ)) + 1)
      ((volume.restrict (Ioc (0 : ℝ) 2)).prod (volume.restrict (Ioc (0 : ℝ) (1 / 2)))) :=
    hrpow_int.comp_fst _
  have hprod_meas : Measurable (fun p : ℝ × ℝ => p.1 ^ (-p.2)) :=
    measurable_fst.pow measurable_snd.neg
  have hprod_int : Integrable (fun p : ℝ × ℝ => p.1 ^ (-p.2))
      ((volume.restrict (Ioc (0 : ℝ) 2)).prod (volume.restrict (Ioc (0 : ℝ) (1 / 2)))) := by
    refine hprod_dom.mono' hprod_meas.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with ⟨x, ξ⟩ ⟨hx, hξ⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    by_cases hx1 : x ≤ 1
    · have h1 : x ^ (-ξ) ≤ x ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hx.1 hx1 (by linarith [hξ.2])
      linarith
    · have h1 : x ^ (-ξ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hx1) (by linarith [hξ.1])
      have hnonneg : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.1.le _
      linarith
  exact hprod_int.integral_prod_left

private lemma remLogKernel_linearGrowth : LinearGrowthOnIoi2 remLogKernel := by
  refine ⟨?_, (Real.log 2)⁻¹, inv_nonneg.mpr (Real.log_nonneg one_le_two), fun x hx => ?_⟩
  · exact ((measurable_id.pow measurable_const).div Real.measurable_log).aestronglyMeasurable
  · have hx1 : 1 ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx.le
    rw [remLogKernel, abs_div, abs_of_nonneg (Real.rpow_nonneg hx_pos.le _),
      abs_of_pos (hlog2.trans_le hlogx), div_eq_mul_inv]
    have hrpow : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have hinv : (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2 hlogx
    have hlogx_inv : 0 ≤ (Real.log x)⁻¹ := inv_nonneg.mpr (hlog2.trans_le hlogx).le
    calc x ^ (-(1 / 2 : ℝ)) * (Real.log x)⁻¹ ≤ 1 * (Real.log 2)⁻¹ :=
          mul_le_mul hrpow hinv hlogx_inv zero_le_one
      _ = (Real.log 2)⁻¹ := one_mul _
      _ ≤ (Real.log 2)⁻¹ * x := le_mul_of_one_le_right (inv_nonneg.mpr hlog2.le) hx1

private lemma remLogKernel_exp_decay (j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      |iteratedDeriv j (scaledOn 1 remLogKernel 0) u| ≤ C * Real.exp (-(1 / 2 : ℝ) * u) := by
  let B : ℕ → ℝ := fun k => (Real.log 2)⁻¹ * Real.Gamma ((k : ℝ) + 1 / 2)
  let C : ℝ := ∑ k ∈ Finset.range (j + 1), |towerCoeff 1 j k| * B k
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u _
  rw [(scaledOn_iteratedDeriv 1 remLogKernel_linearGrowth j).1 u]
  calc |∑ k ∈ Finset.range (j + 1), towerCoeff 1 j k * scaledOn 1 remLogKernel k u|
      ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff 1 j k * scaledOn 1 remLogKernel k u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff 1 j k| * B k * Real.exp (-(1 / 2 : ℝ) * u) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        have hscaled : |scaledOn 1 remLogKernel k u| ≤ B k * Real.exp (-(1 / 2 : ℝ) * u) := by
          unfold scaledOn momentInt
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hr_pos : 0 < Real.exp (-u) := Real.exp_pos _
          have ha_pos : 0 < (k : ℝ) + 1 / 2 := by positivity
          have hint_Ioc01 : IntegrableOn
              (fun x : ℝ => x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x))) (Ioc 0 1) := by
            have h0 : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
              (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
                (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2)))
            refine h0.mono'
              ((measurable_id.pow measurable_const).mul
                (by fun_prop : Measurable (fun x : ℝ => Real.exp (-(Real.exp (-u) * x))))).aestronglyMeasurable ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
            simp only [Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le)]
            have hpow : x ^ (((k : ℝ) + 1 / 2) - 1) ≤ x ^ (-(1 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith [show (0 : ℝ) ≤ k by positivity])
            exact (mul_le_of_le_one_right (Real.rpow_nonneg hx.1.le _)
              (Real.exp_le_one_iff.mpr (by nlinarith [hx.1]))).trans hpow
          have hint_Ioi1 : IntegrableOn
              (fun x : ℝ => x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x))) (Ioi 1) := by
            have hk1 : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(Real.exp (-u) * x))) (Ioi 1) := by
              simpa [neg_mul] using (integrableOn_pow_mul_exp_neg_Ioi k hr_pos).mono_set
                (Ioi_subset_Ioi zero_le_one)
            refine hk1.mono'
              ((measurable_id.pow measurable_const).mul
                (by fun_prop : Measurable (fun x : ℝ => Real.exp (-(Real.exp (-u) * x))))).aestronglyMeasurable ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            change 1 < x at hx
            simp only [Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [hx]) _) (Real.exp_pos _).le)]
            have hpow : x ^ (((k : ℝ) + 1 / 2) - 1) ≤ x ^ k := by
              rw [← Real.rpow_natCast x k]
              exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
            exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
          have hint_Ioi0 : IntegrableOn
              (fun x : ℝ => x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x))) (Ioi 0) := by
            rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
            exact hint_Ioc01.union hint_Ioi1
          have hm_le : |∫ x in Ioi (2 : ℝ), remLogKernel x * x ^ k * Real.exp (-Real.exp (-u) * x)| ≤
              (Real.log 2)⁻¹ * ∫ x in Ioi (0 : ℝ), x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x)) := by
            calc |∫ x in Ioi (2 : ℝ), remLogKernel x * x ^ k * Real.exp (-Real.exp (-u) * x)|
                ≤ ∫ x in Ioi (2 : ℝ), |remLogKernel x * x ^ k * Real.exp (-Real.exp (-u) * x)| := by
                  simpa only [Real.norm_eq_abs] using
                    norm_integral_le_integral_norm (fun x => remLogKernel x * x ^ k * Real.exp (-Real.exp (-u) * x))
              _ ≤ ∫ x in Ioi (2 : ℝ),
                    (Real.log 2)⁻¹ * (x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x))) := by
                  refine setIntegral_mono_on (momentInt_integrableOn remLogKernel_linearGrowth k hr_pos).norm
                    ((hint_Ioi0.mono_set (Ioi_subset_Ioi (by norm_num))).const_mul _) measurableSet_Ioi fun x hx => ?_
                  change 2 < x at hx
                  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
                  have hinv : (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ :=
                    inv_anti₀ hlog2 (Real.log_le_log (by norm_num) hx.le)
                  have hpow_eq : x ^ (-(1 / 2 : ℝ)) * x ^ k = x ^ (((k : ℝ) + 1 / 2) - 1) := by
                    rw [← Real.rpow_natCast x k, ← Real.rpow_add (by linarith)]
                    congr 1; ring
                  rw [remLogKernel, abs_mul, abs_mul, abs_div, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
                    abs_of_pos (Real.log_pos (by linarith)), abs_of_nonneg (pow_nonneg (by linarith) k),
                    abs_of_pos (Real.exp_pos _), div_eq_mul_inv]
                  calc x ^ (-(1 / 2 : ℝ)) * (Real.log x)⁻¹ * x ^ k * Real.exp (-Real.exp (-u) * x)
                      ≤ x ^ (-(1 / 2 : ℝ)) * (Real.log 2)⁻¹ * x ^ k * Real.exp (-Real.exp (-u) * x) :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_right
                            (mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg (by linarith) _))
                            (pow_nonneg (by linarith) k))
                          (Real.exp_pos _).le
                    _ = (Real.log 2)⁻¹ * ((x ^ (-(1 / 2 : ℝ)) * x ^ k) * Real.exp (-(Real.exp (-u) * x))) := by
                        rw [neg_mul]; ring
                    _ = (Real.log 2)⁻¹ * (x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x))) := by
                        rw [hpow_eq]
              _ ≤ ∫ x in Ioi (0 : ℝ),
                    (Real.log 2)⁻¹ * (x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x))) := by
                  refine setIntegral_mono_set (hint_Ioi0.const_mul _) ?_
                    (Ioi_subset_Ioi (show (0 : ℝ) ≤ 2 by norm_num)).eventuallySubset
                  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
                  change 0 < x at hx
                  exact mul_nonneg (inv_nonneg.mpr (Real.log_nonneg one_le_two))
                    (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)
              _ = (Real.log 2)⁻¹ * ∫ x in Ioi (0 : ℝ),
                    x ^ (((k : ℝ) + 1 / 2) - 1) * Real.exp (-(Real.exp (-u) * x)) :=
                  integral_const_mul _ _
          rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha_pos hr_pos] at hm_le
          have hexp_eq : Real.exp (-((k + 1 : ℕ) : ℝ) * u) *
              (1 / Real.exp (-u)) ^ ((k : ℝ) + 1 / 2) = Real.exp (-(1 / 2 : ℝ) * u) := by
            rw [one_div, Real.inv_rpow hr_pos.le, Real.rpow_def_of_pos hr_pos, Real.log_exp,
              ← Real.exp_neg, ← Real.exp_add]
            congr 1; push_cast; ring
          calc Real.exp (-((k + 1 : ℕ) : ℝ) * u) *
                |∫ x in Ioi (2 : ℝ), remLogKernel x * x ^ k * Real.exp (-Real.exp (-u) * x)|
              ≤ Real.exp (-((k + 1 : ℕ) : ℝ) * u) *
                  ((Real.log 2)⁻¹ * ((1 / Real.exp (-u)) ^ ((k : ℝ) + 1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2))) :=
                mul_le_mul_of_nonneg_left hm_le (Real.exp_pos _).le
            _ = B k * (Real.exp (-((k + 1 : ℕ) : ℝ) * u) * (1 / Real.exp (-u)) ^ ((k : ℝ) + 1 / 2)) := by
                dsimp [B]; ring
            _ = B k * Real.exp (-(1 / 2 : ℝ) * u) := by rw [hexp_eq]
        calc |towerCoeff 1 j k| * |scaledOn 1 remLogKernel k u|
            ≤ |towerCoeff 1 j k| * (B k * Real.exp (-(1 / 2 : ℝ) * u)) :=
              mul_le_mul_of_nonneg_left hscaled (abs_nonneg _)
          _ = |towerCoeff 1 j k| * B k * Real.exp (-(1 / 2 : ℝ) * u) := by ring
    _ = C * Real.exp (-(1 / 2 : ℝ) * u) := by rw [← Finset.sum_mul]

@[expose] def mainGamInt (u : ℝ) : ℝ :=
  ∫ ξ in (0 : ℝ)..(1 / 2), Real.exp (-ξ * u) * Real.Gamma (1 - ξ)

private lemma scaledMoment_li_eq (u : ℝ) :
    scaledMoment li 0 u = mainGamInt u - compactScaled cutKernel 0 u + scaledOn 1 remLogKernel 0 u := by
  let t : ℝ := Real.exp (-u)
  have ht : 0 < t := Real.exp_pos (-u)
  have hlog2 : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_nonneg one_le_two)
  have hu_deriv : ∀ x ∈ Ioi (2 : ℝ), HasDerivAt li ((Real.log x)⁻¹) x := fun x hx => li_hasDerivAt hx
  have hv_deriv : ∀ x ∈ Ioi (2 : ℝ), HasDerivAt (fun y => Real.exp (-t * y)) (-t * Real.exp (-t * x)) x :=
    fun x _ => by
      have h1 : HasDerivAt (fun y : ℝ => -t * y) (-t) x := by simpa using (hasDerivAt_id x).const_mul (-t)
      convert h1.exp using 1; ring
  have huv'_int : IntegrableOn (fun x => li x * (-t * Real.exp (-t * x))) (Ioi 2) := by
    have heq : (fun x => li x * (-t * Real.exp (-t * x))) = fun x => -t * (li x * x ^ 0 * Real.exp (-t * x)) := by
      funext x; simp; ring
    rw [heq]
    exact (momentInt_integrableOn li_linearGrowth 0 ht).const_mul (-t)
  have hu'v_int : IntegrableOn (fun x => (Real.log x)⁻¹ * Real.exp (-t * x)) (Ioi 2) := by
    refine ((integrableOn_pow_mul_exp_neg_Ioi 0 ht).mono_set (Ioi_subset_Ioi (by norm_num))).const_mul
      (Real.log 2)⁻¹ |>.mono' ?_ ?_
    · exact ((Real.measurable_log.inv).mul (by fun_prop : Measurable (fun x : ℝ => Real.exp (-t * x)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      change 2 < x at hx
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (Real.log_pos (by linarith)),
        abs_of_pos (Real.exp_pos _)]
      have hinv := inv_anti₀ (Real.log_pos one_lt_two) (Real.log_le_log (by norm_num) hx.le)
      simpa using mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
  have hzero : Tendsto (fun x => li x * Real.exp (-t * x)) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => (Real.log 2)⁻¹ * (x - 2)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change 2 < x at hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (li_bounds hx.le).1, abs_of_pos (Real.exp_pos _)]
      have hexp1 : Real.exp (-t * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc li x * Real.exp (-t * x) ≤ li x * 1 := mul_le_mul_of_nonneg_left hexp1 (li_bounds hx.le).1
        _ = li x := mul_one _
        _ ≤ (Real.log 2)⁻¹ * (x - 2) := (li_bounds hx.le).2
    · have hsub : Tendsto (fun x : ℝ => (Real.log 2)⁻¹ * (x - 2)) (𝓝 (2 : ℝ)) (𝓝 ((Real.log 2)⁻¹ * (2 - 2))) :=
        tendsto_const_nhds.mul (continuousAt_id.sub continuousAt_const)
      simpa using hsub.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (fun x => li x * Real.exp (-t * x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => (Real.log 2)⁻¹ * (x * Real.exp (-t * x))) ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (li_bounds hx).1, abs_of_pos (Real.exp_pos _)]
      calc li x * Real.exp (-t * x)
          ≤ ((Real.log 2)⁻¹ * (x - 2)) * Real.exp (-t * x) :=
            mul_le_mul_of_nonneg_right (li_bounds hx).2 (Real.exp_pos _).le
        _ ≤ ((Real.log 2)⁻¹ * x) * Real.exp (-t * x) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hlog2) (Real.exp_pos _).le
        _ = (Real.log 2)⁻¹ * (x * Real.exp (-t * x)) := by ring
    · have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop ht)
      have h2 : Tendsto (fun x : ℝ => (Real.log 2)⁻¹ * (x * Real.exp (-t * x))) atTop
          (𝓝 ((t⁻¹ * (Real.log 2)⁻¹) * 0)) :=
        (h1.const_mul (t⁻¹ * (Real.log 2)⁻¹)).congr fun x => by
          simp only [Function.comp_def, id_eq, pow_one, neg_mul]
          field_simp [ht.ne', (Real.log_pos one_lt_two).ne']
      rwa [mul_zero] at h2
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu_deriv hv_deriv huv'_int hu'v_int hzero hinfty
  have h_ibp_eq : scaledMoment li 0 u = t * ∫ x in Ioi (2 : ℝ), (Real.log x)⁻¹ * Real.exp (-t * x) := by
    have hL : ∫ x in Ioi (2 : ℝ), li x * (-t * Real.exp (-t * x)) =
        -t * ∫ x in Ioi (2 : ℝ), li x * Real.exp (-t * x) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
    rw [hL, sub_self, zero_sub] at hibp
    have hmul : t * ∫ x in Ioi (2 : ℝ), li x * Real.exp (-t * x) =
        ∫ x in Ioi (2 : ℝ), (Real.log x)⁻¹ * Real.exp (-t * x) := by
      linarith [hibp, hL]
    unfold scaledMoment scaledOn momentInt
    calc Real.exp (-((0 + 2 : ℕ) : ℝ) * u) * ∫ x in Ioi (2 : ℝ), li x * x ^ 0 * Real.exp (-Real.exp (-u) * x)
        = t * (t * ∫ x in Ioi (2 : ℝ), li x * Real.exp (-t * x)) := by
          have he2 : Real.exp (-((0 + 2 : ℕ) : ℝ) * u) = t * t := by
            dsimp [t]; rw [← Real.exp_add]; congr 1; ring
          rw [he2, mul_assoc]
          congr 1; congr 1
          exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp [t]
      _ = t * ∫ x in Ioi (2 : ℝ), (Real.log x)⁻¹ * Real.exp (-t * x) := by rw [hmul]
  have hcut_Ioi2_int : IntegrableOn (fun x : ℝ => cutKernel x * Real.exp (-t * x)) (Ioi 2) := by
    have hdiff : IntegrableOn (fun x : ℝ => (Real.log x)⁻¹ * Real.exp (-t * x) - remLogKernel x * Real.exp (-t * x))
        (Ioi 2) :=
      hu'v_int.sub (by simpa using momentInt_integrableOn remLogKernel_linearGrowth 0 ht)
    refine hdiff.congr_fun (fun x hx => ?_) measurableSet_Ioi
    change 2 < x at hx
    dsimp only
    rw [inv_log_eq_integral_rpow (by linarith [hx] : 1 < x)]
    change (cutKernel x + remLogKernel x) * Real.exp (-t * x) - remLogKernel x * Real.exp (-t * x) =
      cutKernel x * Real.exp (-t * x)
    ring
  have hrem_Ioi2_int : IntegrableOn (fun x : ℝ => remLogKernel x * Real.exp (-t * x)) (Ioi 2) := by
    simpa using momentInt_integrableOn remLogKernel_linearGrowth 0 ht
  have hsplit_invlog : (∫ x in Ioi (2 : ℝ), (Real.log x)⁻¹ * Real.exp (-t * x)) =
      (∫ x in Ioi (2 : ℝ), cutKernel x * Real.exp (-t * x)) +
        ∫ x in Ioi (2 : ℝ), remLogKernel x * Real.exp (-t * x) := by
    rw [← integral_add hcut_Ioi2_int hrem_Ioi2_int]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    change 2 < x at hx
    rw [inv_log_eq_integral_rpow (by linarith [hx] : 1 < x)]
    change (cutKernel x + remLogKernel x) * Real.exp (-t * x) =
      cutKernel x * Real.exp (-t * x) + remLogKernel x * Real.exp (-t * x)
    ring
  have hprod_Ioi2 : Integrable (fun p : ℝ × ℝ => p.2 ^ (-p.1) * Real.exp (-t * p.2))
      ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod (volume.restrict (Ioi (2 : ℝ)))) := by
    have h0' : IntegrableOn (fun x : ℝ => Real.exp (-t * x)) (Ioi 0) := by
      simpa using integrableOn_pow_mul_exp_neg_Ioi 0 ht
    have hdom_x : IntegrableOn (fun x : ℝ => Real.exp (-t * x)) (Ioi 2) :=
      h0'.mono_set (Ioi_subset_Ioi (by norm_num))
    have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-t * p.2))
        ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod (volume.restrict (Ioi (2 : ℝ)))) :=
      hdom_x.comp_snd _
    have hmeas : Measurable (fun p : ℝ × ℝ => p.2 ^ (-p.1) * Real.exp (-t * p.2)) :=
      (measurable_snd.pow measurable_fst.neg).mul (by fun_prop)
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with ⟨ξ, x⟩ ⟨hξ, hx⟩
    change 2 < x at hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [hξ.1]))
  have hswap1 : (∫ x in Ioi (2 : ℝ), cutKernel x * Real.exp (-t * x)) =
      ∫ ξ in Ioc (0 : ℝ) (1 / 2), ∫ x in Ioi (2 : ℝ), x ^ (-ξ) * Real.exp (-t * x) := by
    calc ∫ x in Ioi (2 : ℝ), cutKernel x * Real.exp (-t * x)
        = ∫ x in Ioi (2 : ℝ), ∫ ξ in Ioc (0 : ℝ) (1 / 2), x ^ (-ξ) * Real.exp (-t * x) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
          unfold cutKernel
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), integral_mul_const]
      _ = ∫ ξ in Ioc (0 : ℝ) (1 / 2), ∫ x in Ioi (2 : ℝ), x ^ (-ξ) * Real.exp (-t * x) :=
          (integral_integral_swap hprod_Ioi2).symm
  have hprod_Ioc2 : Integrable (fun p : ℝ × ℝ => p.2 ^ (-p.1) * Real.exp (-t * p.2))
      ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod (volume.restrict (Ioc (0 : ℝ) 2))) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) + 1) (Ioc 0 2) := by
      have hr : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 2) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
          (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2)))
      exact hr.add (integrableOn_const (hs := measure_Ioc_lt_top.ne))
    have hdom : Integrable (fun p : ℝ × ℝ => p.2 ^ (-(1 / 2 : ℝ)) + 1)
        ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod (volume.restrict (Ioc (0 : ℝ) 2))) :=
      hrpow_int.comp_snd _
    have hmeas : Measurable (fun p : ℝ × ℝ => p.2 ^ (-p.1) * Real.exp (-t * p.2)) :=
      (measurable_snd.pow measurable_fst.neg).mul (by fun_prop)
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with ⟨ξ, x⟩ ⟨hξ, hx⟩
    dsimp only at hξ hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _),
      abs_of_pos (Real.exp_pos _)]
    have hexp1 : Real.exp (-t * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
    have hr1 : x ^ (-ξ) ≤ x ^ (-(1 / 2 : ℝ)) + 1 := by
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx.1 hx1 (by linarith [hξ.2])).trans
          (le_add_of_nonneg_right zero_le_one)
      · exact (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hx1) (by linarith [hξ.1])).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hx.1.le _))
    calc x ^ (-ξ) * Real.exp (-t * x) ≤ x ^ (-ξ) * 1 :=
          mul_le_mul_of_nonneg_left hexp1 (Real.rpow_nonneg hx.1.le _)
      _ = x ^ (-ξ) := mul_one _
      _ ≤ x ^ (-(1 / 2 : ℝ)) + 1 := hr1
  have hrpow_Ioi0_int (ξ : ℝ) (hξ : ξ ∈ Ioc (0 : ℝ) (1 / 2)) :
      IntegrableOn (fun x : ℝ => x ^ (-ξ) * Real.exp (-t * x)) (Ioi 0) := by
    have hsplit_union : Ioi (0 : ℝ) = Ioc (0 : ℝ) 2 ∪ Ioi (2 : ℝ) := (Ioc_union_Ioi_eq_Ioi zero_le_two).symm
    rw [hsplit_union, integrableOn_union]
    constructor
    · have hr0 : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) + 1) (Ioc 0 2) := by
        have hr : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 2) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
            (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2)))
        exact hr.add (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      refine hr0.mono' ((measurable_id.pow measurable_const).mul (by fun_prop)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _),
        abs_of_pos (Real.exp_pos _)]
      have hexp1 : Real.exp (-t * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
      refine (mul_le_of_le_one_right (Real.rpow_nonneg hx.1.le _) hexp1).trans ?_
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx.1 hx1 (by linarith [hξ.2])).trans
          (le_add_of_nonneg_right zero_le_one)
      · exact (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hx1) (by linarith [hξ.1])).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hx.1.le _))
    · refine ((integrableOn_pow_mul_exp_neg_Ioi 0 ht).mono_set (Ioi_subset_Ioi (by norm_num))).mono'
        ((measurable_id.pow measurable_const).mul (by fun_prop)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change 2 < x at hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
        abs_of_pos (Real.exp_pos _), pow_zero, one_mul]
      exact mul_le_of_le_one_left (Real.exp_pos _).le
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [hξ.1]))
  have hsplit_inner (ξ : ℝ) (hξ : ξ ∈ Ioc (0 : ℝ) (1 / 2)) :
      (∫ x in Ioi (2 : ℝ), x ^ (-ξ) * Real.exp (-t * x)) =
        (∫ x in Ioi (0 : ℝ), x ^ (-ξ) * Real.exp (-t * x)) -
          ∫ x in Ioc (0 : ℝ) 2, x ^ (-ξ) * Real.exp (-t * x) := by
    have hi := hrpow_Ioi0_int ξ hξ
    have h1 := hi.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 2 ⊆ Ioi 0)
    have h2 := hi.mono_set (Ioi_subset_Ioi zero_le_two)
    have hunion := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2
    rw [Ioc_union_Ioi_eq_Ioi zero_le_two] at hunion
    linarith
  have hgam_inner (ξ : ℝ) (hξ : ξ ∈ Ioc (0 : ℝ) (1 / 2)) :
      t * (∫ x in Ioi (0 : ℝ), x ^ (-ξ) * Real.exp (-t * x)) = Real.exp (-ξ * u) * Real.Gamma (1 - ξ) := by
    have hgam := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - ξ) (r := t) (by linarith [hξ.2]) ht
    have hfn : (fun x : ℝ => x ^ ((1 - ξ) - 1) * Real.exp (-(t * x))) =
        fun x : ℝ => x ^ (-ξ) * Real.exp (-t * x) := by
      funext x; rw [show (1 - ξ) - 1 = -ξ by ring, neg_mul]
    rw [hfn] at hgam
    rw [hgam, ← mul_assoc]
    congr 1
    rw [one_div, Real.inv_rpow ht.le, show t = Real.exp (-u) from rfl,
      ← Real.exp_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  have hint_main : IntegrableOn (fun ξ : ℝ => t * ∫ x in Ioi (0 : ℝ), x ^ (-ξ) * Real.exp (-t * x))
      (Ioc (0 : ℝ) (1 / 2)) := by
    refine IntegrableOn.congr_fun ?_ (fun ξ hξ => (hgam_inner ξ hξ).symm) measurableSet_Ioc
    have hcont : ContinuousOn (fun ξ : ℝ => Real.exp (-ξ * u) * Real.Gamma (1 - ξ)) (Icc 0 (1 / 2)) := by
      refine (by fun_prop : Continuous (fun ξ : ℝ => Real.exp (-ξ * u))).continuousOn.mul ?_
      intro ξ hξ
      have hne : ∀ m : ℕ, (1 - ξ) ≠ -(m : ℝ) := fun m hm => by
        have : (1 : ℝ) - ξ ≥ 1 / 2 := by linarith [hξ.2]
        have : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
        linarith
      exact ((Real.differentiableAt_Gamma hne).continuousAt.comp
        ((continuousAt_const.sub continuousAt_id) : ContinuousAt (fun x : ℝ => 1 - x) ξ)).continuousWithinAt
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint_cut : IntegrableOn (fun ξ : ℝ => t * ∫ x in Ioc (0 : ℝ) 2, x ^ (-ξ) * Real.exp (-t * x))
      (Ioc (0 : ℝ) (1 / 2)) :=
    hprod_Ioc2.integral_prod_left.const_mul t
  have hswap2 : (∫ ξ in Ioc (0 : ℝ) (1 / 2), t * ∫ x in Ioc (0 : ℝ) 2, x ^ (-ξ) * Real.exp (-t * x)) =
      compactScaled cutKernel 0 u := by
    calc ∫ ξ in Ioc (0 : ℝ) (1 / 2), t * ∫ x in Ioc (0 : ℝ) 2, x ^ (-ξ) * Real.exp (-t * x)
        = t * ∫ ξ in Ioc (0 : ℝ) (1 / 2), ∫ x in Ioc (0 : ℝ) 2, x ^ (-ξ) * Real.exp (-t * x) :=
          integral_const_mul _ _
      _ = t * ∫ x in Ioc (0 : ℝ) 2, ∫ ξ in Ioc (0 : ℝ) (1 / 2), x ^ (-ξ) * Real.exp (-t * x) := by
          rw [integral_integral_swap hprod_Ioc2]
      _ = t * ∫ x in Ioc (0 : ℝ) 2, cutKernel x * Real.exp (-t * x) := by
          congr 1; refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
          unfold cutKernel
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), integral_mul_const]
      _ = compactScaled cutKernel 0 u := by
          unfold compactScaled compactMoment
          have he1 : Real.exp (-((0 + 1 : ℕ) : ℝ) * u) = t := by simp [t]
          rw [he1]
          congr 1; refine setIntegral_congr_fun measurableSet_Ioc fun x _ => by simp [t]
  rw [h_ibp_eq, hsplit_invlog, mul_add, hswap1, ← integral_const_mul]
  have h1 : (∫ ξ in Ioc (0 : ℝ) (1 / 2), t * ∫ x in Ioi (2 : ℝ), x ^ (-ξ) * Real.exp (-t * x)) =
      mainGamInt u - compactScaled cutKernel 0 u := by
    calc ∫ ξ in Ioc (0 : ℝ) (1 / 2), t * ∫ x in Ioi (2 : ℝ), x ^ (-ξ) * Real.exp (-t * x)
        = ∫ ξ in Ioc (0 : ℝ) (1 / 2),
            (t * ∫ x in Ioi (0 : ℝ), x ^ (-ξ) * Real.exp (-t * x)) -
              (t * ∫ x in Ioc (0 : ℝ) 2, x ^ (-ξ) * Real.exp (-t * x)) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun ξ hξ => ?_
          rw [hsplit_inner ξ hξ, mul_sub]
      _ = (∫ ξ in Ioc (0 : ℝ) (1 / 2), t * ∫ x in Ioi (0 : ℝ), x ^ (-ξ) * Real.exp (-t * x)) -
            (∫ ξ in Ioc (0 : ℝ) (1 / 2), t * ∫ x in Ioc (0 : ℝ) 2, x ^ (-ξ) * Real.exp (-t * x)) :=
          integral_sub hint_main hint_cut
      _ = mainGamInt u - compactScaled cutKernel 0 u := by
          rw [hswap2]
          congr 1
          unfold mainGamInt
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          exact setIntegral_congr_fun measurableSet_Ioc fun ξ hξ => hgam_inner ξ hξ
  have hrem : t * ∫ x in Ioi (2 : ℝ), remLogKernel x * Real.exp (-t * x) =
      scaledOn 1 remLogKernel 0 u := by
    unfold scaledOn momentInt
    have he1 : Real.exp (-((0 + 1 : ℕ) : ℝ) * u) = t := by simp [t]
    rw [he1]
    congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp [t]
  rw [h1, hrem]

private def phiJet : ℕ → Minor
  | 0 => aGamma
  | j + 1 => (phiJet j).jet

private lemma phi_analyticAt_closedBall {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) (1 / 2)) :
    AnalyticAt ℂ phi z := by
  refine phi_analyticAt_of_avoids_posNat fun n hn he => ?_
  have hlt : ‖z‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hge : (1 : ℝ) ≤ ‖z‖ := by rw [he, Complex.norm_natCast]; exact_mod_cast hn
  linarith

private lemma phiJet_spec (j : ℕ) :
    (phiJet j).atom = 0 ∧
    (phiJet j).density = (fun ξ : ℂ => (-ξ) ^ j * phi ξ) ∧
    (phiJet j).toSeries = d_u^[j] gHat := by
  induction j with
  | zero =>
    refine ⟨rfl, funext fun ξ => by simp [phiJet, aGamma], ?_⟩
    rw [phiJet]
    exact aGamma_toSeries
  | succ j ih =>
    have hdens : (phiJet (j + 1)).density = fun ξ => (-ξ) ^ (j + 1) * phi ξ := by
      funext ξ
      simp only [phiJet, Minor.jet, ih.2.1]
      rw [pow_succ']
      ring
    have han : AnalyticAt ℂ (phiJet j).density 0 := by
      rw [ih.2.1]
      exact ((analyticAt_id.neg.pow j).mul (phi_analyticAt_closedBall
        (Metric.mem_closedBall_self (by norm_num)))).congr (.of_forall fun _ => rfl)
    have hser : (phiJet (j + 1)).toSeries = d_u^[j + 1] gHat := by
      rw [phiJet, Minor.toSeries_jet han, ih.2.2, Function.iterate_succ_apply']
    exact ⟨rfl, hdens, hser⟩

private lemma coeff_zero_d_u_iter (j : ℕ) : PowerSeries.coeff 0 (d_u^[j] gHat) = 0 := by
  rw [← (phiJet_spec j).2.2]
  simp [Minor.toSeries, (phiJet_spec j).1]

private lemma coeff_succ_d_u_iter (j k : ℕ) :
    PowerSeries.coeff (k + 1) (d_u^[j] gHat) = iteratedDeriv k (fun ξ : ℂ => (-ξ) ^ j * phi ξ) 0 := by
  rw [← (phiJet_spec j).2.2, ← (phiJet_spec j).2.1]
  simp [Minor.toSeries]

private lemma mainGamInt_coe (u : ℝ) :
    (mainGamInt u : ℂ) = ∫ ξ in Ioc (0 : ℝ) (1 / 2), Complex.exp (-(ξ : ℂ) * (u : ℂ)) * phi (ξ : ℂ) := by
  unfold mainGamInt
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioc fun ξ _ => ?_
  have hgam : Complex.Gamma ((1 - ξ : ℝ) : ℂ) = ((Real.Gamma (1 - ξ) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal (1 - ξ)
  simp only [Complex.ofReal_mul, ← hgam, phi, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_exp, Complex.ofReal_neg]

private lemma mainGamInt_iteratedDeriv (j : ℕ) :
    (∀ u : ℝ, iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) u =
      ∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) ∧
    Differentiable ℝ (iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ))) := by
  have hphi_cont : ContinuousOn (fun ξ : ℝ => phi (ξ : ℂ)) (Icc 0 (1 / 2)) := fun ξ hξ =>
    ((phi_analyticAt_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hξ.1]
      exact hξ.2)).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hint_fn : ∀ (k : ℕ) (u : ℝ), IntegrableOn
      (fun ξ : ℝ => (-(ξ : ℂ)) ^ k * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)))
      (Ioc 0 (1 / 2)) := fun k u => by
    have hcont : ContinuousOn
        (fun ξ : ℝ => (-(ξ : ℂ)) ^ k * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)))
        (Icc 0 (1 / 2)) :=
      (((continuous_neg.comp Complex.continuous_ofReal).pow k).continuousOn.mul hphi_cont).mul
        (by fun_prop : Continuous (fun ξ : ℝ => Complex.exp (-(ξ : ℂ) * (u : ℂ)))).continuousOn
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hstep : ∀ (k : ℕ) (u : ℝ), HasDerivAt
      (fun t : ℝ => ∫ ξ in Ioc (0 : ℝ) (1 / 2),
        (-(ξ : ℂ)) ^ k * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (t : ℂ)))
      (∫ ξ in Ioc (0 : ℝ) (1 / 2),
        (-(ξ : ℂ)) ^ (k + 1) * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) u := by
    intro k u
    obtain ⟨B_phi, hB_phi⟩ := isCompact_Icc.exists_bound_of_continuousOn hphi_cont
    let F : ℝ → ℝ → ℂ := fun t ξ => (-(ξ : ℂ)) ^ k * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (t : ℂ))
    let F' : ℝ → ℝ → ℂ := fun t ξ => (-(ξ : ℂ)) ^ (k + 1) * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (t : ℂ))
    let Cbd : ℝ := (1 / 2) ^ (k + 1) * max B_phi 0 * Real.exp ((|u| + 1) / 2)
    have hmeas : ∀ᶠ t in 𝓝 u, AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 (1 / 2))) :=
      .of_forall fun t => (hint_fn k t).aestronglyMeasurable
    have hmeas' : AEStronglyMeasurable (F' u) (volume.restrict (Ioc 0 (1 / 2))) :=
      (hint_fn (k + 1) u).aestronglyMeasurable
    have hbound : ∀ᵐ ξ ∂volume.restrict (Ioc (0 : ℝ) (1 / 2)), ∀ t ∈ Metric.ball u 1, ‖F' t ξ‖ ≤ Cbd := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with ξ hξ t ht
      have htabs : |t| ≤ |u| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at ht; linarith [abs_sub_abs_le_abs_sub t u]
      have hre : (-(ξ : ℂ) * (t : ℂ)).re ≤ (|u| + 1) / 2 := by
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        have h1 : -ξ * t ≤ ξ * |t| := by nlinarith [neg_le_abs t, hξ.1]
        have h2 : ξ * |t| ≤ (1 / 2) * (|u| + 1) := mul_le_mul hξ.2 htabs (abs_nonneg t) (by positivity)
        linarith
      rw [show F' t ξ = (-(ξ : ℂ)) ^ (k + 1) * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (t : ℂ)) from rfl,
        norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hξ.1, Complex.norm_exp]
      have h1 : ξ ^ (k + 1) ≤ (1 / 2 : ℝ) ^ (k + 1) := pow_le_pow_left₀ hξ.1.le hξ.2 _
      have h2 : ‖phi (ξ : ℂ)‖ ≤ max B_phi 0 :=
        (hB_phi ξ ⟨hξ.1.le, hξ.2⟩).trans (le_max_left _ _)
      have h3 : Real.exp (-(ξ : ℂ) * (t : ℂ)).re ≤ Real.exp ((|u| + 1) / 2) := Real.exp_le_exp.mpr hre
      calc ξ ^ (k + 1) * ‖phi (ξ : ℂ)‖ * Real.exp (-(ξ : ℂ) * (t : ℂ)).re
          ≤ (1 / 2) ^ (k + 1) * max B_phi 0 * Real.exp ((|u| + 1) / 2) :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (Real.exp_pos _).le (by positivity)
        _ = Cbd := rfl
    have hbound_int : IntegrableOn (fun _ : ℝ => Cbd) (Ioc 0 (1 / 2)) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have hderiv : ∀ᵐ ξ ∂volume.restrict (Ioc (0 : ℝ) (1 / 2)), ∀ t ∈ Metric.ball u 1,
        HasDerivAt (fun s => F s ξ) (F' t ξ) t := by
      refine .of_forall fun ξ t _ => ?_
      have hr : HasDerivAt (fun s : ℝ => -(ξ : ℂ) * (s : ℂ)) (-(ξ : ℂ)) t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(ξ : ℂ))
      convert hr.cexp.const_mul ((-(ξ : ℂ)) ^ k * phi (ξ : ℂ)) using 1
      dsimp [F, F']; rw [pow_succ]; ring
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds u zero_lt_one)
      hmeas (hint_fn k u) hmeas' hbound hbound_int hderiv).2
  induction j with
  | zero =>
    have heq : (fun t : ℝ => (mainGamInt t : ℂ)) = fun t : ℝ =>
        ∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ 0 * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (t : ℂ)) := by
      funext t; rw [mainGamInt_coe]; refine setIntegral_congr_fun measurableSet_Ioc fun ξ _ => by simp [mul_comm]
    refine ⟨fun u => by simpa using congrFun heq u, fun u => ?_⟩
    rw [heq]; exact (hstep 0 u).differentiableAt
  | succ j ih =>
    have heq : iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) =
        fun t : ℝ => ∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (t : ℂ)) :=
      funext ih.1
    refine ⟨fun u => by rw [iteratedDeriv_succ, heq, (hstep j u).deriv], fun u => ?_⟩
    have heq' : iteratedDeriv (j + 1) (fun t : ℝ => (mainGamInt t : ℂ)) =
        fun t : ℝ => ∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ (j + 1) * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (t : ℂ)) := by
      funext t; rw [iteratedDeriv_succ, heq, (hstep j t).deriv]
    rw [heq']; exact (hstep (j + 1) u).differentiableAt

private lemma mainGamInt_hasAsympExp (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ))) (d_u^[j] gHat) := by
  intro M
  let ψ : ℂ → ℂ := fun z => (-z) ^ j * phi z
  have hψ_cont : ContinuousOn ψ (Metric.closedBall 0 (1 / 2)) := fun z hz =>
    (((continuousAt_id.neg.pow j).mul (phi_analyticAt_closedBall hz).continuousAt).continuousWithinAt)
  cases M with
  | zero =>
    obtain ⟨Bψ, hBψ⟩ := isCompact_closedBall (0 : ℂ) (1 / 2) |>.exists_bound_of_continuousOn hψ_cont
    refine ⟨(1 / 2) * max Bψ 0, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [(mainGamInt_iteratedDeriv j).1 u, Finset.range_zero, Finset.sum_empty, sub_zero]
    simp only [pow_zero, div_one]
    have hint : IntegrableOn (fun ξ : ℝ => ψ (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) (Ioc 0 (1 / 2)) := by
      have hc : ContinuousOn (fun ξ : ℝ => ψ (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) (Icc 0 (1 / 2)) :=
        (hψ_cont.comp Complex.continuous_ofReal.continuousOn fun ξ hξ => by
          simpa [Metric.mem_closedBall, dist_zero_right, abs_of_nonneg hξ.1] using hξ.2).mul
          (by fun_prop : Continuous (fun ξ : ℝ => Complex.exp (-(ξ : ℂ) * (u : ℂ)))).continuousOn
      exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    calc ‖∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))‖
        ≤ ∫ ξ in Ioc (0 : ℝ) (1 / 2), ‖ψ (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _ξ in Ioc (0 : ℝ) (1 / 2), max Bψ 0 := by
          refine setIntegral_mono_on hint.norm (integrableOn_const (hs := measure_Ioc_lt_top.ne))
            measurableSet_Ioc fun ξ hξ => ?_
          have hmem : (ξ : ℂ) ∈ Metric.closedBall 0 (1 / 2) := by
            simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos hξ.1] using hξ.2
          have hexp : ‖Complex.exp (-(ξ : ℂ) * (u : ℂ))‖ ≤ 1 := by
            rw [Complex.norm_exp]
            simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            exact Real.exp_le_one_iff.mpr (by nlinarith [hξ.1])
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) hexp |>.trans ((hBψ _ hmem).trans (le_max_left _ _))
      _ = (1 / 2) * max Bψ 0 := by simp
  | succ m =>
    have hψ_an0 : AnalyticAt ℂ ψ 0 :=
      (analyticAt_id.neg.pow j).mul (phi_analyticAt_closedBall (Metric.mem_closedBall_self (by norm_num)))
    obtain ⟨R, hR_an, hR_eq⟩ := hψ_an0.exists_eq_sum_add_pow_mul m
    obtain ⟨δ₀, hδ₀, hK₁_lt⟩ := Metric.eventually_nhds_iff.mp
      (hR_an.continuousAt.norm.eventually
        (gt_mem_nhds (by linarith [norm_nonneg (R 0)] : ‖R 0‖ < ‖R 0‖ + 1)))
    let K₁ : ℝ := ‖R 0‖ + 1
    have hK₁_bd : ∀ w ∈ Metric.ball (0 : ℂ) δ₀, ‖R w‖ ≤ K₁ := fun w hw =>
      (hK₁_lt (Metric.mem_ball.mp hw)).le
    let δ : ℝ := min δ₀ (1 / 2) / 2
    have hδ_pos : 0 < δ := by dsimp [δ]; positivity
    have hδ_lt_δ₀ : δ < δ₀ := by dsimp [δ]; linarith [min_le_left δ₀ (1 / 2)]
    let Ppoly : ℂ → ℂ := fun z => ∑ k ∈ Finset.range m, (z ^ k / (k.factorial : ℂ)) • iteratedDeriv k ψ 0
    have hPcont : Continuous (fun ξ : ℝ => Ppoly (ξ : ℂ)) := by
      dsimp only [Ppoly]
      fun_prop
    have hdiff_cont : ContinuousOn (fun ξ : ℝ => ‖ψ (ξ : ℂ) - Ppoly (ξ : ℂ)‖ / ξ ^ m) (Icc δ (1 / 2)) := by
      refine ContinuousOn.div ?_ (Continuous.continuousOn (continuous_pow m)) fun ξ hξ => ?_
      · refine ContinuousOn.norm ((hψ_cont.comp Complex.continuous_ofReal.continuousOn fun ξ hξ => ?_).sub
          hPcont.continuousOn)
        simpa [Metric.mem_closedBall, dist_zero_right, abs_of_nonneg (hδ_pos.le.trans hξ.1)] using hξ.2
      · exact pow_ne_zero m (lt_of_lt_of_le hδ_pos hξ.1).ne'
    obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hdiff_cont
    let B : ℝ := max K₁ (max K₂ 0)
    have hB_nonneg : 0 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
    have hR_bd : ∀ ξ ∈ Ioc (0 : ℝ) (1 / 2), ‖R (ξ : ℂ)‖ ≤ B := fun ξ hξ => by
      by_cases hle : ξ < δ
      · have hw : (ξ : ℂ) ∈ Metric.ball 0 δ₀ := by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ.1]
          exact hle.trans hδ_lt_δ₀
        exact (hK₁_bd _ hw).trans (le_max_left _ _)
      · have hge : δ ≤ ξ := le_of_not_gt hle
        have heq := hR_eq (ξ : ℂ)
        have hsub : (ξ : ℂ) ^ m * R (ξ : ℂ) = ψ (ξ : ℂ) - Ppoly (ξ : ℂ) := by
          rw [smul_eq_mul] at heq
          linear_combination -heq
        have hRnorm : ‖R (ξ : ℂ)‖ = ‖ψ (ξ : ℂ) - Ppoly (ξ : ℂ)‖ / ξ ^ m := by
          have h1 := congrArg norm hsub
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ.1, mul_comm] at h1
          exact eq_div_of_mul_eq (pow_pos hξ.1 m).ne' h1
        rw [hRnorm]
        have hb := hK₂ ξ ⟨hge, hξ.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg hξ.1.le m))] at hb
        exact hb.trans ((le_max_left K₂ 0).trans (le_max_right K₁ _))
    let C_rem : ℝ := B * (m.factorial : ℝ)
    let C_tail : ℝ := ∑ k ∈ Finset.range m,
      ‖iteratedDeriv k ψ 0‖ / (k.factorial : ℝ) * ((k.factorial : ℝ) * Real.exp (1 / 2) *
        (((m + 1).factorial : ℝ) / (1 / 2 : ℝ) ^ (m + 1)))
    refine ⟨C_rem + C_tail, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
    have hu_pos : 0 < u := by linarith
    rw [(mainGamInt_iteratedDeriv j).1 u]
    have hsplit_ψ (ξ : ℝ) : (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) =
        (∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
          ((ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ)))) +
          (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) := by
      have heq := hR_eq (ξ : ℂ)
      change ψ (ξ : ℂ) = _ at heq
      calc (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))
          = ψ (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) := rfl
        _ = ((∑ k ∈ Finset.range m, ((ξ : ℂ) ^ k / (k.factorial : ℂ)) • iteratedDeriv k ψ 0) +
              (ξ : ℂ) ^ m • R (ξ : ℂ)) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) := by rw [← heq]
        _ = (∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              ((ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ)))) +
              (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) := by
            rw [add_mul, Finset.sum_mul]
            refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) ?_
            · rw [smul_eq_mul]; ring
            · rw [smul_eq_mul]
    have hint_k (k : ℕ) : IntegrableOn
        (fun ξ : ℝ => (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) * ((ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ))))
        (Ioc 0 (1 / 2)) :=
      (by fun_prop : Continuous fun ξ : ℝ =>
        (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) * ((ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ)))).integrableOn_Ioc
    have hint_rem : IntegrableOn
        (fun ξ : ℝ => (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) (Ioc 0 (1 / 2)) := by
      have hsub : (fun ξ : ℝ => (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) =
          fun ξ : ℝ => (ψ (ξ : ℂ) - Ppoly (ξ : ℂ)) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) := by
        funext ξ
        have heq := hR_eq (ξ : ℂ)
        change ψ (ξ : ℂ) = Ppoly (ξ : ℂ) + (ξ : ℂ) ^ m • R (ξ : ℂ) at heq
        rw [smul_eq_mul] at heq
        have h1 : (ξ : ℂ) ^ m * R (ξ : ℂ) = ψ (ξ : ℂ) - Ppoly (ξ : ℂ) := by linear_combination -heq
        rw [h1]
      rw [hsub]
      have hψ_contR : ContinuousOn (fun ξ : ℝ => ψ (ξ : ℂ)) (Icc 0 (1 / 2)) :=
        hψ_cont.comp Complex.continuous_ofReal.continuousOn fun ξ hξ => by
          simpa [Metric.mem_closedBall, dist_zero_right, abs_of_nonneg hξ.1] using hξ.2
      exact ((hψ_contR.sub hPcont.continuousOn).mul
        (by fun_prop : Continuous (fun ξ : ℝ => Complex.exp (-(ξ : ℂ) * (u : ℂ)))).continuousOn).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hint_sum := integrable_finsetSum (Finset.range m) fun k _ => hint_k k
    have h_int_split : (∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) =
        (∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
          ∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ))) +
          ∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) := by
      have hc0 : ∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) =
          ∫ ξ in Ioc (0 : ℝ) (1 / 2),
            (∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              ((ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ)))) +
              (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ)) :=
        setIntegral_congr_fun measurableSet_Ioc fun ξ _ => hsplit_ψ ξ
      rw [hc0, integral_add hint_sum hint_rem, integral_finsetSum (Finset.range m) fun k _ => hint_k k]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    have h_series_split : ∑ n ∈ Finset.range (m + 1), PowerSeries.coeff n (d_u^[j] gHat) * ((u : ℂ)⁻¹ ^ n) =
        ∑ k ∈ Finset.range m, iteratedDeriv k ψ 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
      rw [Finset.sum_range_succ', coeff_zero_d_u_iter j, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_succ_d_u_iter j k]
    have h_Ioi_half (k : ℕ) : (∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ))) =
        (((k.factorial : ℂ) * (u : ℂ)⁻¹ ^ (k + 1)) -
          ((∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) : ℝ) : ℂ)) := by
      have hc : (∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ))) =
          ((∫ ξ in Ioc (0 : ℝ) (1 / 2), ξ ^ k * Real.exp (-u * ξ) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine setIntegral_congr_fun measurableSet_Ioc fun ξ _ => ?_
        simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp, Complex.ofReal_neg]
        congr 2; ring
      have hfull := integral_pow_mul_exp_neg_Ioi k hu_pos
      have hi_full := integrableOn_pow_mul_exp_neg_Ioi k hu_pos
      have hunion := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hi_full.mono_set Ioc_subset_Ioi_self) (hi_full.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2)))
      rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2), hfull] at hunion
      have hsubR : ∫ ξ in Ioc (0 : ℝ) (1 / 2), ξ ^ k * Real.exp (-u * ξ) =
          (k.factorial : ℝ) / u ^ (k + 1) - ∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) := by
        linarith
      rw [hc, hsubR]
      push_cast
      rw [inv_pow]
      ring
    have h_term_sub :
        (∫ ξ in Ioc (0 : ℝ) (1 / 2), (-(ξ : ℂ)) ^ j * phi (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) -
          ∑ n ∈ Finset.range (m + 1), PowerSeries.coeff n (d_u^[j] gHat) * ((u : ℂ)⁻¹ ^ n) =
        (∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) -
          ∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
            ((∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) : ℝ) : ℂ) := by
      rw [h_int_split, h_series_split]
      have hsum_k : (∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
          ∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ k * Complex.exp (-(ξ : ℂ) * (u : ℂ))) -
          ∑ k ∈ Finset.range m, iteratedDeriv k ψ 0 * ((u : ℂ)⁻¹ ^ (k + 1)) =
          -(∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
            ((∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) : ℝ) : ℂ)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [h_Ioi_half k]
        have hkfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        field_simp [hkfac]
        ring
      linear_combination hsum_k
    have h_rem_norm :
        ‖∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))‖ ≤
          C_rem / u ^ (m + 1) := by
      calc ‖∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))‖
          ≤ ∫ ξ in Ioc (0 : ℝ) (1 / 2), ‖(ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ ξ in Ioc (0 : ℝ) (1 / 2), B * (ξ ^ m * Real.exp (-u * ξ)) := by
            refine setIntegral_mono_on hint_rem.norm
              (((integrableOn_pow_mul_exp_neg_Ioi m hu_pos).mono_set Ioc_subset_Ioi_self).const_mul B)
              measurableSet_Ioc fun ξ hξ => ?_
            rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ.1,
              Complex.norm_exp]
            simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            have hrb := hR_bd ξ hξ
            calc ξ ^ m * ‖R (ξ : ℂ)‖ * Real.exp (-ξ * u)
                ≤ ξ ^ m * B * Real.exp (-ξ * u) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hrb (pow_nonneg hξ.1.le m)) (Real.exp_pos _).le
              _ = B * (ξ ^ m * Real.exp (-u * ξ)) := by
                  rw [show -ξ * u = -u * ξ by ring]; ring
        _ ≤ ∫ ξ in Ioi (0 : ℝ), B * (ξ ^ m * Real.exp (-u * ξ)) := by
            refine setIntegral_mono_set ((integrableOn_pow_mul_exp_neg_Ioi m hu_pos).const_mul B) ?_
              (Ioc_subset_Ioi_self : Ioc (0 : ℝ) (1 / 2) ⊆ Ioi 0).eventuallySubset
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
            change 0 < ξ at hξ
            exact mul_nonneg hB_nonneg (mul_nonneg (pow_nonneg hξ.le m) (Real.exp_pos _).le)
        _ = C_rem / u ^ (m + 1) := by
            rw [integral_const_mul, integral_pow_mul_exp_neg_Ioi m hu_pos]
            dsimp [C_rem]; ring
    have h_tail_norm :
        ‖∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
          ((∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) : ℝ) : ℂ)‖ ≤ C_tail / u ^ (m + 1) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      have hnonneg_tail : 0 ≤ ∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) :=
        setIntegral_nonneg measurableSet_Ioi fun ξ hξ =>
          mul_nonneg (pow_nonneg (by linarith [Set.mem_Ioi.mp hξ]) k) (Real.exp_pos _).le
      rw [abs_of_nonneg hnonneg_tail]
      have hint_dom_tail : IntegrableOn
          (fun ξ : ℝ => Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) * (ξ ^ k * Real.exp (-ξ)))
          (Ioi 0) := by
        have h0 : IntegrableOn (fun ξ : ℝ => Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) *
            (ξ ^ k * Real.exp (-(1 : ℝ) * ξ))) (Ioi 0) :=
          (integrableOn_pow_mul_exp_neg_Ioi k one_pos).const_mul _
        exact h0.congr_fun (fun ξ _ => by
          dsimp only
          rw [show (-1 : ℝ) * ξ = -ξ by ring, show -(1 / 2 : ℝ) * u = -(1 / 2 * u) by ring]) measurableSet_Ioi
      have h_int_tail : ∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) ≤
          (k.factorial : ℝ) * Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) := by
        calc ∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ)
            ≤ ∫ ξ in Ioi (1 / 2 : ℝ), Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) *
                (ξ ^ k * Real.exp (-ξ)) := by
              refine setIntegral_mono_on
                ((integrableOn_pow_mul_exp_neg_Ioi k hu_pos).mono_set (Ioi_subset_Ioi (by norm_num)))
                (hint_dom_tail.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 / 2 by norm_num)))
                measurableSet_Ioi fun ξ hξ => ?_
              change (1 / 2 : ℝ) < ξ at hξ
              have hexp_le : Real.exp (-u * ξ) ≤ Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) * Real.exp (-ξ) := by
                rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
                nlinarith
              calc ξ ^ k * Real.exp (-u * ξ)
                  ≤ ξ ^ k * (Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) * Real.exp (-ξ)) :=
                    mul_le_mul_of_nonneg_left hexp_le (pow_nonneg (by linarith) k)
                _ = Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) * (ξ ^ k * Real.exp (-ξ)) := by
                    ring
          _ ≤ ∫ ξ in Ioi (0 : ℝ), Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) * (ξ ^ k * Real.exp (-ξ)) := by
              refine setIntegral_mono_set hint_dom_tail ?_
                (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 / 2 by norm_num)).eventuallySubset
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
              change 0 < ξ at hξ
              exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hξ.le k) (Real.exp_pos _).le)
          _ = (k.factorial : ℝ) * Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) := by
              rw [integral_const_mul]
              have h1 := integral_pow_mul_exp_neg_Ioi k one_pos
              simp only [one_mul, neg_mul] at h1
              rw [h1, one_pow, div_one]
              ring
      have hexp_u := exp_neg_mul_le_inv_pow (1 / 2) (by norm_num) (m + 1) hu_pos
      have hk_bd : ∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) ≤
          ((k.factorial : ℝ) * Real.exp (1 / 2) * (((m + 1).factorial : ℝ) / (1 / 2 : ℝ) ^ (m + 1))) / u ^ (m + 1) := by
        calc ∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ)
            ≤ (k.factorial : ℝ) * Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * u) := h_int_tail
          _ ≤ (k.factorial : ℝ) * Real.exp (1 / 2) * (((m + 1).factorial : ℝ) / (1 / 2 : ℝ) ^ (m + 1) / u ^ (m + 1)) :=
              mul_le_mul_of_nonneg_left hexp_u (by positivity)
          _ = _ := by ring
      calc ‖iteratedDeriv k ψ 0‖ / (k.factorial : ℝ) * ∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ)
          ≤ ‖iteratedDeriv k ψ 0‖ / (k.factorial : ℝ) *
              (((k.factorial : ℝ) * Real.exp (1 / 2) * (((m + 1).factorial : ℝ) / (1 / 2 : ℝ) ^ (m + 1))) / u ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hk_bd (by positivity)
        _ = _ := by ring
    rw [h_term_sub]
    calc ‖(∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))) -
            ∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              ((∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) : ℝ) : ℂ)‖
        ≤ ‖∫ ξ in Ioc (0 : ℝ) (1 / 2), (ξ : ℂ) ^ m * R (ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ))‖ +
            ‖∑ k ∈ Finset.range m, (iteratedDeriv k ψ 0 / (k.factorial : ℂ)) *
              ((∫ ξ in Ioi (1 / 2 : ℝ), ξ ^ k * Real.exp (-u * ξ) : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ C_rem / u ^ (m + 1) + C_tail / u ^ (m + 1) := add_le_add h_rem_norm h_tail_norm
      _ = (C_rem + C_tail) / u ^ (m + 1) := by ring

private lemma approxLi_error_flat {A : ℝ → ℝ} (hA : ApproxLi A) (j M : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      |iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u| ≤ C / u ^ M := by
  let D : ℝ → ℝ := fun x => A x - li x
  have hD : LinearGrowthOnIoi2 D := hA.1.sub li_linearGrowth
  have ⟨_, KD, hKD, bD⟩ := hD
  obtain ⟨CM, hCM_pos, hCM_ev⟩ := hA.2 M
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hCM_ev
  let U₀ : ℝ := max 2 (2 * Real.log (max X₀ 2) + 2)
  have hbound_k (k : ℕ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ u ≥ U₀,
      |scaledMoment D k u| ≤ Ck / u ^ M := by
    let Ck₁ : ℝ := KD * ((M.factorial : ℝ) / (1 : ℝ) ^ M)
    let Ck₂ : ℝ := CM * (2 ^ M) * ((k + 1).factorial : ℝ)
    refine ⟨Ck₁ + Ck₂, by positivity, fun u hu => ?_⟩
    have hu2 : 2 ≤ u := le_trans (le_max_left _ _) hu
    have hu_pos : 0 < u := by linarith
    have hexp_u2_ge : max X₀ 2 ≤ Real.exp (u / 2) := by
      have hlog : Real.log (max X₀ 2) ≤ u / 2 := by
        have h2 : 2 * Real.log (max X₀ 2) + 2 ≤ u := le_trans (le_max_right _ _) hu
        linarith
      rw [← Real.exp_log (show 0 < max X₀ 2 by positivity)]
      exact Real.exp_le_exp.mpr hlog
    have h2_lt_exp : 2 < Real.exp (u / 2) := by
      have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
      exact lt_of_lt_of_le h1 (Real.exp_le_exp.mpr (by linarith))
    have hx_big : ∀ x : ℝ, Real.exp (u / 2) < x → X₀ ≤ x := fun x hx =>
      (le_max_left X₀ 2).trans (hexp_u2_ge.trans hx.le)
    let t : ℝ := Real.exp (-u)
    have ht : 0 < t := Real.exp_pos (-u)
    have hint_full := momentInt_integrableOn hD k ht
    have hunion : Ioi (2 : ℝ) = Ioc 2 (Real.exp (u / 2)) ∪ Ioi (Real.exp (u / 2)) :=
      (Ioc_union_Ioi_eq_Ioi h2_lt_exp.le).symm
    have hi1 : IntegrableOn (fun x => D x * x ^ k * Real.exp (-t * x)) (Ioc 2 (Real.exp (u / 2))) :=
      hint_full.mono_set (hunion ▸ subset_union_left)
    have hi2 : IntegrableOn (fun x => D x * x ^ k * Real.exp (-t * x)) (Ioi (Real.exp (u / 2))) :=
      hint_full.mono_set (hunion ▸ subset_union_right)
    have hsplit : momentInt D k t =
        (∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)) +
          ∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x) := by
      unfold momentInt
      rw [hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2]
    have hpiece1 : Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
        |∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)| ≤ Ck₁ / u ^ M := by
      have hint_abs : |∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)| ≤
          KD * Real.exp ((k + 2 : ℝ) * (u / 2)) := by
        calc |∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)|
            ≤ ∫ x in Ioc 2 (Real.exp (u / 2)), |D x * x ^ k * Real.exp (-t * x)| :=
              by simpa only [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (fun x => D x * x ^ k * Real.exp (-t * x))
          _ ≤ ∫ _x in Ioc 2 (Real.exp (u / 2)), KD * (Real.exp (u / 2)) ^ (k + 1) := by
              refine setIntegral_mono_on hi1.norm (integrableOn_const (hs := measure_Ioc_lt_top.ne))
                measurableSet_Ioc fun x hx => ?_
              have hx0 : 0 ≤ x := by linarith [hx.1]
              rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (pow_nonneg hx0 k)]
              have hexp1 : Real.exp (-t * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
              have hxk : x ^ (k + 1) ≤ (Real.exp (u / 2)) ^ (k + 1) :=
                pow_le_pow_left₀ hx0 hx.2 (k + 1)
              calc |D x| * x ^ k * Real.exp (-t * x)
                  ≤ (KD * x) * x ^ k * 1 :=
                    mul_le_mul (mul_le_mul_of_nonneg_right (bD x hx.1) (pow_nonneg hx0 k))
                      hexp1 (Real.exp_pos _).le (by positivity)
                _ = KD * x ^ (k + 1) := by rw [pow_succ']; ring
                _ ≤ KD * (Real.exp (u / 2)) ^ (k + 1) := mul_le_mul_of_nonneg_left hxk hKD
          _ = (Real.exp (u / 2) - 2) * (KD * (Real.exp (u / 2)) ^ (k + 1)) := by
              simp [h2_lt_exp.le]
          _ ≤ Real.exp (u / 2) * (KD * (Real.exp (u / 2)) ^ (k + 1)) := by
              exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = KD * Real.exp ((k + 2 : ℝ) * (u / 2)) := by
              rw [mul_left_comm, ← pow_succ', ← Real.exp_nat_mul]
              congr 2; push_cast; ring
      have hpow_exp : Real.exp (-((k + 2 : ℕ) : ℝ) * u) * Real.exp ((k + 2 : ℝ) * (u / 2)) ≤ Real.exp (-u) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        push_cast
        have hk2 : (2 : ℝ) ≤ (k + 2 : ℝ) := by linarith [show (0 : ℝ) ≤ k by positivity]
        nlinarith
      calc Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
            |∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)|
          ≤ Real.exp (-((k + 2 : ℕ) : ℝ) * u) * (KD * Real.exp ((k + 2 : ℝ) * (u / 2))) :=
            mul_le_mul_of_nonneg_left hint_abs (Real.exp_pos _).le
        _ = KD * (Real.exp (-((k + 2 : ℕ) : ℝ) * u) * Real.exp ((k + 2 : ℝ) * (u / 2))) := by ring
        _ ≤ KD * Real.exp (-u) := mul_le_mul_of_nonneg_left hpow_exp hKD
        _ ≤ Ck₁ / u ^ M := by
            have h1 := exp_neg_mul_le_inv_pow 1 zero_lt_one M hu_pos
            simpa [Ck₁, one_mul, mul_div_assoc] using mul_le_mul_of_nonneg_left h1 hKD
    have hpiece2 : Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
        |∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)| ≤ Ck₂ / u ^ M := by
      let fac : ℝ := CM * 2 ^ M / u ^ M
      have hfac_nonneg : 0 ≤ fac := by positivity
      have hint_abs : |∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)| ≤
          fac * ∫ x in Ioi (0 : ℝ), x ^ (k + 1) * Real.exp (-t * x) := by
        calc |∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)|
            ≤ ∫ x in Ioi (Real.exp (u / 2)), |D x * x ^ k * Real.exp (-t * x)| :=
              by simpa only [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (fun x => D x * x ^ k * Real.exp (-t * x))
          _ ≤ ∫ x in Ioi (Real.exp (u / 2)), fac * (x ^ (k + 1) * Real.exp (-t * x)) := by
              refine setIntegral_mono_on hi2.norm
                (((integrableOn_pow_mul_exp_neg_Ioi (k + 1) ht).mono_set
                  (Ioi_subset_Ioi (Real.exp_pos _).le)).const_mul fac) measurableSet_Ioi fun x hx => ?_
              change Real.exp (u / 2) < x at hx
              have hxpos : 0 < x := lt_trans (Real.exp_pos _) hx
              have hDx := hX₀ x (hx_big x hx)
              have hlog_ge : u / 2 ≤ Real.log x := by
                rw [← Real.log_exp (u / 2)]
                exact Real.log_le_log (Real.exp_pos _) hx.le
              have hpow_log : (u / 2) ^ M ≤ (Real.log x) ^ M :=
                pow_le_pow_left₀ (by positivity) hlog_ge M
              have hD_le : |D x| ≤ fac * x := by
                calc |D x| ≤ CM * x / (Real.log x) ^ M := hDx
                  _ ≤ CM * x / (u / 2) ^ M :=
                      div_le_div_of_nonneg_left (mul_nonneg hCM_pos.le hxpos.le) (by positivity) hpow_log
                  _ = fac * x := by
                      dsimp [fac]; rw [div_pow]; field_simp [hu_pos.ne']
              rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hxpos.le k), abs_of_pos (Real.exp_pos _)]
              calc |D x| * x ^ k * Real.exp (-t * x)
                  ≤ (fac * x) * x ^ k * Real.exp (-t * x) :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right hD_le (pow_nonneg hxpos.le k)) (Real.exp_pos _).le
                _ = fac * (x ^ (k + 1) * Real.exp (-t * x)) := by rw [pow_succ']; ring
          _ ≤ ∫ x in Ioi (0 : ℝ), fac * (x ^ (k + 1) * Real.exp (-t * x)) := by
              refine setIntegral_mono_set ((integrableOn_pow_mul_exp_neg_Ioi (k + 1) ht).const_mul fac) ?_
                (Ioi_subset_Ioi (Real.exp_pos _).le).eventuallySubset
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
              change 0 < x at hx
              exact mul_nonneg hfac_nonneg (mul_nonneg (pow_nonneg hx.le (k + 1)) (Real.exp_pos _).le)
          _ = fac * ∫ x in Ioi (0 : ℝ), x ^ (k + 1) * Real.exp (-t * x) := integral_const_mul _ _
      rw [integral_pow_mul_exp_neg_Ioi (k + 1) ht] at hint_abs
      have hexp_cancel : Real.exp (-((k + 2 : ℕ) : ℝ) * u) / t ^ (k + 2) = 1 := by
        dsimp [t]; rw [← Real.exp_nat_mul, ← Real.exp_sub]
        have : -((k + 2 : ℕ) : ℝ) * u - ((k + 2 : ℕ) : ℝ) * -u = 0 := by ring
        rw [this, Real.exp_zero]
      calc Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
            |∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)|
          ≤ Real.exp (-((k + 2 : ℕ) : ℝ) * u) * (fac * (((k + 1).factorial : ℝ) / t ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left hint_abs (Real.exp_pos _).le
        _ = (fac * ((k + 1).factorial : ℝ)) * (Real.exp (-((k + 2 : ℕ) : ℝ) * u) / t ^ (k + 2)) := by ring
        _ = Ck₂ / u ^ M := by rw [hexp_cancel, mul_one]; dsimp [fac, Ck₂]; ring
    unfold scaledMoment scaledOn
    rw [hsplit, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
          |(∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)) +
            ∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)|
        ≤ Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
            (|∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)| +
              |∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (Real.exp_pos _).le
      _ = Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
            |∫ x in Ioc 2 (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)| +
            Real.exp (-((k + 2 : ℕ) : ℝ) * u) *
              |∫ x in Ioi (Real.exp (u / 2)), D x * x ^ k * Real.exp (-t * x)| := by ring
      _ ≤ Ck₁ / u ^ M + Ck₂ / u ^ M := add_le_add hpiece1 hpiece2
      _ = (Ck₁ + Ck₂) / u ^ M := by ring
  choose Ck _ hCk_bd using hbound_k
  refine ⟨∑ k ∈ Finset.range (j + 1), |towerCoeff 2 j k| * Ck k, ?_⟩
  filter_upwards [eventually_ge_atTop U₀] with u hu
  unfold scaledMoment
  rw [(scaledOn_iteratedDeriv 2 hD j).1 u, Finset.sum_div]
  calc |∑ k ∈ Finset.range (j + 1), towerCoeff 2 j k * scaledMoment D k u|
      ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff 2 j k * scaledMoment D k u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (j + 1), |towerCoeff 2 j k| * Ck k / u ^ M := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hCk_bd k u hu) (abs_nonneg _)

private lemma iteratedDeriv_ofReal_eq (f : ℝ → ℝ)
    (hf : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k f)) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun t : ℝ => (f t : ℂ)) u = ((iteratedDeriv j f u : ℝ) : ℂ) := by
  induction j generalizing u with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, show iteratedDeriv j (fun t : ℝ => (f t : ℂ)) =
        fun t : ℝ => ((iteratedDeriv j f t : ℝ) : ℂ) from funext ih]
    exact ((hf j u).hasDerivAt.ofReal_comp).deriv

private lemma approxLi_hasAsympExp {A : ℝ → ℝ} (hA : ApproxLi A) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun u : ℝ => (scaledMoment A 0 u : ℂ))) (d_u^[j] gHat) := by
  have hdiffErr : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k (scaledMoment (fun x => A x - li x) 0)) :=
    fun k => (scaledOn_iteratedDeriv 2 (hA.1.sub li_linearGrowth) k).2
  have hdiffCut : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k (compactScaled cutKernel 0)) :=
    fun k => (compactScaled_iteratedDeriv cutKernel_integrableOn k).2
  have hdiffRem : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k (scaledOn 1 remLogKernel 0)) :=
    fun k => (scaledOn_iteratedDeriv 1 remLogKernel_linearGrowth k).2
  have hcd_err : ContDiff ℝ j (fun t : ℝ => (scaledMoment (fun x => A x - li x) 0 t : ℂ)) :=
    contDiff_of_differentiable_iteratedDeriv fun m _ => by
      have heq : iteratedDeriv m (fun t : ℝ => (scaledMoment (fun x => A x - li x) 0 t : ℂ)) =
          fun t => ((iteratedDeriv m (scaledMoment (fun x => A x - li x) 0) t : ℝ) : ℂ) :=
        funext (iteratedDeriv_ofReal_eq _ hdiffErr m)
      rw [heq]; exact fun t => (hdiffErr m t).hasDerivAt.ofReal_comp.differentiableAt
  have hcd_main : ContDiff ℝ j (fun t : ℝ => (mainGamInt t : ℂ)) :=
    contDiff_of_differentiable_iteratedDeriv fun m _ => (mainGamInt_iteratedDeriv m).2
  have hcd_cut : ContDiff ℝ j (fun t : ℝ => (compactScaled cutKernel 0 t : ℂ)) :=
    contDiff_of_differentiable_iteratedDeriv fun m _ => by
      have heq : iteratedDeriv m (fun t : ℝ => (compactScaled cutKernel 0 t : ℂ)) =
          fun t => ((iteratedDeriv m (compactScaled cutKernel 0) t : ℝ) : ℂ) :=
        funext (iteratedDeriv_ofReal_eq _ hdiffCut m)
      rw [heq]; exact fun t => (hdiffCut m t).hasDerivAt.ofReal_comp.differentiableAt
  have hcd_rem : ContDiff ℝ j (fun t : ℝ => (scaledOn 1 remLogKernel 0 t : ℂ)) :=
    contDiff_of_differentiable_iteratedDeriv fun m _ => by
      have heq : iteratedDeriv m (fun t : ℝ => (scaledOn 1 remLogKernel 0 t : ℂ)) =
          fun t => ((iteratedDeriv m (scaledOn 1 remLogKernel 0) t : ℝ) : ℂ) :=
        funext (iteratedDeriv_ofReal_eq _ hdiffRem m)
      rw [heq]; exact fun t => (hdiffRem m t).hasDerivAt.ofReal_comp.differentiableAt
  have heq_fn : (fun u : ℝ => (scaledMoment A 0 u : ℂ)) =
      fun u : ℝ => ((scaledMoment (fun x => A x - li x) 0 u : ℝ) : ℂ) +
        ((mainGamInt u : ℂ) - (compactScaled cutKernel 0 u : ℂ) +
          (scaledOn 1 remLogKernel 0 u : ℂ)) := by
    funext u
    have hs := scaledMoment_sub hA.1 li_linearGrowth 0 u
    rw [scaledMoment_li_eq u] at hs
    have hAeq : scaledMoment A 0 u = scaledMoment (fun x => A x - li x) 0 u +
        (mainGamInt u - compactScaled cutKernel 0 u + scaledOn 1 remLogKernel 0 u) := by
      linear_combination hs
    exact_mod_cast hAeq
  intro M
  obtain ⟨Cm, hCm⟩ := mainGamInt_hasAsympExp j M
  obtain ⟨Ce, hCe⟩ := approxLi_error_flat hA j M
  obtain ⟨Cc, hCc⟩ := compactScaled_exp_decay cutKernel_integrableOn j
  obtain ⟨Cr, hCr⟩ := remLogKernel_exp_decay j
  refine ⟨max Ce 0 + (max Cc 0 * (M.factorial : ℝ) / (1 : ℝ) ^ M) +
      (max Cr 0 * (M.factorial : ℝ) / (1 / 2 : ℝ) ^ M) + Cm, ?_⟩
  filter_upwards [hCm, hCe, hCc, hCr, eventually_gt_atTop (0 : ℝ)] with u huM huE huC huR hupos
  have hmain_split : iteratedDeriv j (fun u : ℝ => (scaledMoment A 0 u : ℂ)) u =
      ((iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u : ℝ) : ℂ) +
        (iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) u -
          ((iteratedDeriv j (compactScaled cutKernel 0) u : ℝ) : ℂ) +
          ((iteratedDeriv j (scaledOn 1 remLogKernel 0) u : ℝ) : ℂ)) := by
    rw [heq_fn, iteratedDeriv_fun_add hcd_err.contDiffAt (((hcd_main.sub hcd_cut).add hcd_rem).contDiffAt),
      iteratedDeriv_fun_add (hcd_main.sub hcd_cut).contDiffAt hcd_rem.contDiffAt,
      iteratedDeriv_fun_sub hcd_main.contDiffAt hcd_cut.contDiffAt,
      iteratedDeriv_ofReal_eq _ hdiffErr j u,
      iteratedDeriv_ofReal_eq _ hdiffCut j u,
      iteratedDeriv_ofReal_eq _ hdiffRem j u]
  rw [hmain_split]
  have htri :
      ‖((iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u : ℝ) : ℂ) +
          (iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) u -
            ((iteratedDeriv j (compactScaled cutKernel 0) u : ℝ) : ℂ) +
            ((iteratedDeriv j (scaledOn 1 remLogKernel 0) u : ℝ) : ℂ)) -
          ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] gHat) * (u : ℂ)⁻¹ ^ k‖ ≤
        |iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u| +
          |iteratedDeriv j (compactScaled cutKernel 0) u| +
          |iteratedDeriv j (scaledOn 1 remLogKernel 0) u| +
          ‖iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) u -
            ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] gHat) * (u : ℂ)⁻¹ ^ k‖ := by
    have hsplit_norm :
        ((iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u : ℝ) : ℂ) +
          (iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) u -
            ((iteratedDeriv j (compactScaled cutKernel 0) u : ℝ) : ℂ) +
            ((iteratedDeriv j (scaledOn 1 remLogKernel 0) u : ℝ) : ℂ)) -
          ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] gHat) * (u : ℂ)⁻¹ ^ k =
        ((iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u : ℝ) : ℂ) -
          ((iteratedDeriv j (compactScaled cutKernel 0) u : ℝ) : ℂ) +
          ((iteratedDeriv j (scaledOn 1 remLogKernel 0) u : ℝ) : ℂ) +
          (iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) u -
            ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] gHat) * (u : ℂ)⁻¹ ^ k) := by
      ring
    rw [hsplit_norm]
    have h1 := norm_add_le
      (((iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u : ℝ) : ℂ) -
        ((iteratedDeriv j (compactScaled cutKernel 0) u : ℝ) : ℂ) +
        ((iteratedDeriv j (scaledOn 1 remLogKernel 0) u : ℝ) : ℂ))
      (iteratedDeriv j (fun t : ℝ => (mainGamInt t : ℂ)) u -
        ∑ k ∈ Finset.range M, PowerSeries.coeff k (d_u^[j] gHat) * (u : ℂ)⁻¹ ^ k)
    have h2 := norm_add_le
      (((iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u : ℝ) : ℂ) -
        ((iteratedDeriv j (compactScaled cutKernel 0) u : ℝ) : ℂ))
      ((iteratedDeriv j (scaledOn 1 remLogKernel 0) u : ℝ) : ℂ)
    have h3 := norm_sub_le
      ((iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u : ℝ) : ℂ)
      ((iteratedDeriv j (compactScaled cutKernel 0) u : ℝ) : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs] at h1 h2 h3
    linarith
  have huE' : |iteratedDeriv j (scaledMoment (fun x => A x - li x) 0) u| ≤ max Ce 0 / u ^ M :=
    huE.trans (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg hupos.le _))
  have huC' : |iteratedDeriv j (compactScaled cutKernel 0) u| ≤
      (max Cc 0 * (M.factorial : ℝ) / (1 : ℝ) ^ M) / u ^ M := by
    calc |iteratedDeriv j (compactScaled cutKernel 0) u|
        ≤ Cc * Real.exp (-u) := huC
      _ ≤ max Cc 0 * Real.exp (-u) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max Cc 0 * ((M.factorial : ℝ) / (1 : ℝ) ^ M / u ^ M) := by
          simpa using mul_le_mul_of_nonneg_left (exp_neg_mul_le_inv_pow 1 zero_lt_one M hupos) (le_max_right Cc 0)
      _ = (max Cc 0 * (M.factorial : ℝ) / (1 : ℝ) ^ M) / u ^ M := by ring
  have huR' : |iteratedDeriv j (scaledOn 1 remLogKernel 0) u| ≤
      (max Cr 0 * (M.factorial : ℝ) / (1 / 2 : ℝ) ^ M) / u ^ M := by
    calc |iteratedDeriv j (scaledOn 1 remLogKernel 0) u|
        ≤ Cr * Real.exp (-(1 / 2 : ℝ) * u) := huR
      _ ≤ max Cr 0 * Real.exp (-(1 / 2 : ℝ) * u) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max Cr 0 * ((M.factorial : ℝ) / (1 / 2 : ℝ) ^ M / u ^ M) :=
          mul_le_mul_of_nonneg_left (exp_neg_mul_le_inv_pow (1 / 2) (by norm_num) M hupos) (le_max_right Cr 0)
      _ = (max Cr 0 * (M.factorial : ℝ) / (1 / 2 : ℝ) ^ M) / u ^ M := by ring
  calc _ ≤ max Ce 0 / u ^ M + (max Cc 0 * (M.factorial : ℝ) / (1 : ℝ) ^ M) / u ^ M +
            (max Cr 0 * (M.factorial : ℝ) / (1 / 2 : ℝ) ^ M) / u ^ M + Cm / u ^ M := by
          linarith [htri, huE', huC', huR', huM]
    _ = _ := by ring

/-! ### 3. Main Theorems: Pak Conjecture 2.5b (`I_prime` & `Pi_series`) and Unconditional `logReciprocalSeries` -/

private def primeReal (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

private def logReciprocalReal (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, (Real.log (k : ℝ))⁻¹

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

private lemma scaledRay_logReciprocal_eq (u : ℝ) :
    scaledRay logReciprocalSeries u = ((scaledMoment logReciprocalReal 0 u : ℝ) : ℂ) := by
  let a : ℕ → ℝ := fun n => if 2 ≤ n then (Real.log (n : ℝ))⁻¹ else 0
  let S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), a k
  have hS : ∀ n : ℕ, S n = ∑ k ∈ Finset.Icc 2 n, (Real.log (k : ℝ))⁻¹ := fun n => by
    dsimp [S, a]
    have hsplit : ∑ k ∈ Finset.range (n + 1), (if 2 ≤ k then (Real.log (k : ℝ))⁻¹ else 0) =
        ∑ k ∈ (Finset.range (n + 1)).filter (2 ≤ ·), (Real.log (k : ℝ))⁻¹ :=
      (Finset.sum_filter _ _).symm
    rw [hsplit]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have ha0 : a 0 = 0 := by simp [a]
  have ha1 : a 1 = 0 := by simp [a]
  have hab : ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C := ⟨(Real.log 2)⁻¹, fun n => by
    dsimp [a]
    split_ifs with hn
    · have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      rw [abs_inv, abs_of_pos (hlog2.trans_le hlogn)]
      exact inv_anti₀ hlog2 hlogn
    · simp [inv_nonneg.mpr (Real.log_nonneg one_le_two)]⟩
  have hAbel := tsum_mul_exp_eq_integral a ha0 ha1 hab S (fun _ => rfl) (Real.exp_pos (-u))
  have hlog_eq : (fun x : ℝ => S ⌊x⌋₊ * Real.exp (-Real.exp (-u) * x)) =
      fun x : ℝ => logReciprocalReal x * x ^ 0 * Real.exp (-Real.exp (-u) * x) := by
    funext x; simp [logReciprocalReal, hS]
  rw [hlog_eq] at hAbel
  have hval : value logReciprocalSeries (qRay u) =
      ((∑' n : ℕ, a n * Real.exp (-Real.exp (-u) * (n : ℝ)) : ℝ) : ℂ) := by
    unfold value
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    simp only [PrimeNome.term, logReciprocalSeries, PowerSeries.coeff_mk, qRay, Complex.ofReal_mul]
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    split_ifs with hn
    · simp only [a, hn, ↓reduceIte, Complex.ofReal_inv]
      rw [show (n : ℝ) * -Real.exp (-u) = -Real.exp (-u) * n by ring]
    · simp only [a, hn, ↓reduceIte, zero_mul, Complex.ofReal_zero]
  unfold scaledRay scaledMoment scaledOn momentInt
  rw [tRay, hval, ← Complex.ofReal_mul, hAbel, ← mul_assoc, ← Real.exp_add]
  congr 1; congr 1
  rw [show -((0 + 2 : ℕ) : ℝ) * u = -u + -u by push_cast; ring]

private lemma approxLi_primeReal (hpnt : PNTAllOrders) : ApproxLi primeReal := by
  refine ⟨⟨?_, 2, by norm_num, fun x hx => ?_⟩, hpnt⟩
  · have hS : Measurable (fun n : ℕ => (Nat.primeCounting n : ℝ)) := measurable_of_countable _
    exact (hS.comp Nat.measurable_floor).aestronglyMeasurable
  · rw [primeReal, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 : Nat.primeCounting ⌊x⌋₊ ≤ ⌊x⌋₊ + 1 := by
      rw [Nat.primeCounting_eq_primeCounting'_succ]
      exact Nat.count_le Nat.Prime
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ x + 1 := by
      linarith [Nat.floor_le (by linarith [hx] : 0 ≤ x)]
    calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast h1
      _ ≤ x + 1 := h2
      _ ≤ 2 * x := by linarith

private lemma approxLi_logReciprocalReal : ApproxLi logReciprocalReal := by
  refine ⟨⟨?_, (Real.log 2)⁻¹, inv_nonneg.mpr (Real.log_nonneg one_le_two), fun x hx => ?_⟩, ?_⟩
  · have hS : Measurable (fun n : ℕ => ∑ k ∈ Finset.Icc 2 n, (Real.log (k : ℝ))⁻¹) :=
      measurable_of_countable _
    exact (hS.comp Nat.measurable_floor).aestronglyMeasurable
  · rw [logReciprocalReal]
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hnonneg : 0 ≤ ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, (Real.log (k : ℝ))⁻¹ :=
      Finset.sum_nonneg fun k hk =>
        inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (by have := (Finset.mem_Icc.mp hk).1; omega : 1 ≤ k)))
    rw [abs_of_nonneg hnonneg]
    calc ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, (Real.log (k : ℝ))⁻¹
        ≤ ∑ _k ∈ Finset.Icc 2 ⌊x⌋₊, (Real.log 2)⁻¹ := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
          exact inv_anti₀ hlog2 (Real.log_le_log (by norm_num) hk2)
      _ ≤ (⌊x⌋₊ : ℝ) * (Real.log 2)⁻¹ := by
          simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Nat.sub_le ⌊x⌋₊ 1)) (inv_nonneg.mpr hlog2.le)
      _ ≤ (Real.log 2)⁻¹ * x := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith [hx])) (inv_nonneg.mpr hlog2.le)
  · intro M
    have hdiff_bd : ∀ x ≥ (2 : ℝ), |logReciprocalReal x - li x| ≤ (Real.log 2)⁻¹ := fun x hx => by
      let n : ℕ := ⌊x⌋₊
      have hn2 : 2 ≤ n := (Nat.le_floor_iff (by linarith)).mpr hx
      have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hxn1 : x < (n + 1 : ℝ) := Nat.lt_floor_add_one x
      have hint_2n : IntervalIntegrable (fun v : ℝ => (Real.log v)⁻¹) volume 2 (n : ℝ) :=
        li_intervalIntegrable (by exact_mod_cast hn2)
      have hint_nx : IntervalIntegrable (fun v : ℝ => (Real.log v)⁻¹) volume (n : ℝ) x :=
        (li_integrand_contOn.mono (by
          rw [uIcc_of_le hnx]
          exact fun v hv => le_trans (by exact_mod_cast hn2) hv.1)).intervalIntegrable
      have hli_split : li x =
          (∑ k ∈ Finset.Ico 2 n, ∫ v in (k : ℝ)..((k + 1 : ℕ) : ℝ), (Real.log v)⁻¹) +
            ∫ v in (n : ℝ)..x, (Real.log v)⁻¹ := by
        unfold li
        rw [← intervalIntegral.integral_add_adjacent_intervals hint_2n hint_nx]
        congr 1
        symm
        refine intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k : ℕ => (k : ℝ)) hn2 fun k hk => ?_
        have hk2 : 2 ≤ k := hk.1
        refine (li_integrand_contOn.mono ?_).intervalIntegrable
        rw [uIcc_of_le (by exact_mod_cast Nat.le_succ k)]
        exact fun v hv => le_trans (by exact_mod_cast hk2) hv.1
      have hcell_lo (k : ℕ) (hk : k ∈ Finset.Ico 2 n) :
          (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ ≤ ∫ v in (k : ℝ)..((k + 1 : ℕ) : ℝ), (Real.log v)⁻¹ := by
        have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
        have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        have hi : IntervalIntegrable (fun v : ℝ => (Real.log v)⁻¹) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
          (li_integrand_contOn.mono (by rw [uIcc_of_le hle]; exact fun v hv => le_trans (by exact_mod_cast hk2) hv.1)).intervalIntegrable
        rw [intervalIntegral.integral_of_le hle]
        have hconst : (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ =
            ∫ _v in Ioc (k : ℝ) ((k + 1 : ℕ) : ℝ), (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
            Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [hle])]
          push_cast; ring
        rw [hconst]
        refine setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne)) hi.1 measurableSet_Ioc fun v hv => ?_
        have hv1 : 1 < v := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
          linarith [hv.1]
        exact inv_anti₀ (Real.log_pos hv1) (Real.log_le_log (by positivity) hv.2)
      have hcell_hi (k : ℕ) (hk : k ∈ Finset.Ico 2 n) :
          ∫ v in (k : ℝ)..((k + 1 : ℕ) : ℝ), (Real.log v)⁻¹ ≤ (Real.log (k : ℝ))⁻¹ := by
        have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
        have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        have hi : IntervalIntegrable (fun v : ℝ => (Real.log v)⁻¹) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
          (li_integrand_contOn.mono (by rw [uIcc_of_le hle]; exact fun v hv => le_trans (by exact_mod_cast hk2) hv.1)).intervalIntegrable
        rw [intervalIntegral.integral_of_le hle]
        have hconst : (Real.log (k : ℝ))⁻¹ =
            ∫ _v in Ioc (k : ℝ) ((k + 1 : ℕ) : ℝ), (Real.log (k : ℝ))⁻¹ := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
            Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [hle])]
          push_cast; ring
        rw [hconst]
        refine setIntegral_mono_on hi.1 (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc fun v hv => ?_
        have hkpos : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
        exact inv_anti₀ (Real.log_pos hkpos) (Real.log_le_log (by positivity) hv.1.le)
      have htail_lo : 0 ≤ ∫ v in (n : ℝ)..x, (Real.log v)⁻¹ := by
        rw [intervalIntegral.integral_of_le hnx]
        exact setIntegral_nonneg measurableSet_Ioc fun v hv =>
          inv_nonneg.mpr (Real.log_nonneg (by
            have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
            linarith [hv.1]))
      have htail_hi : ∫ v in (n : ℝ)..x, (Real.log v)⁻¹ ≤ (Real.log (n : ℝ))⁻¹ := by
        rw [intervalIntegral.integral_of_le hnx]
        have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
        have h1 : ∫ v in Ioc (n : ℝ) x, (Real.log v)⁻¹ ≤ ∫ _v in Ioc (n : ℝ) x, (Real.log (n : ℝ))⁻¹ :=
          setIntegral_mono_on hint_nx.1 (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc fun v hv =>
            inv_anti₀ (Real.log_pos hn1) (Real.log_le_log (by positivity) hv.1.le)
        have h2 : ∫ _v in Ioc (n : ℝ) x, (Real.log (n : ℝ))⁻¹ = (x - n) * (Real.log (n : ℝ))⁻¹ := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
            Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [hnx])]
        have h3 : (x - n) * (Real.log (n : ℝ))⁻¹ ≤ 1 * (Real.log (n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (Real.log_nonneg hn1.le))
        linarith
      have hsum_lo : logReciprocalReal x - (Real.log 2)⁻¹ ≤ ∑ k ∈ Finset.Ico 2 n, (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ := by
        have hshift : ∑ k ∈ Finset.Ico 2 n, (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ =
            ∑ j ∈ Finset.Ico 3 (n + 1), (Real.log (j : ℝ))⁻¹ := by
          have hmap : Finset.Ico 3 (n + 1) = (Finset.Ico 2 n).map ⟨fun k => k + 1, Nat.succ_injective⟩ := by
            ext j; simp only [Finset.mem_Ico, Finset.mem_map, Function.Embedding.coeFn_mk]
            exact ⟨fun ⟨h3, hjn⟩ => ⟨j - 1, ⟨by omega, by omega⟩, by omega⟩, fun ⟨k, ⟨hk2, hkn⟩, hkj⟩ => by omega⟩
          rw [hmap, Finset.sum_map]
          rfl
        have hIcc_eq : Finset.Icc 2 n = Finset.Ico 2 (n + 1) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        have hadd2 : logReciprocalReal x = (Real.log 2)⁻¹ + ∑ j ∈ Finset.Ico 3 (n + 1), (Real.log (j : ℝ))⁻¹ := by
          unfold logReciprocalReal
          change ∑ k ∈ Finset.Icc 2 n, (Real.log (k : ℝ))⁻¹ = _
          rw [hIcc_eq, Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < n + 1)]
          simp
        linarith [hshift, hadd2]
      have hsum_hi : (∑ k ∈ Finset.Ico 2 n, (Real.log (k : ℝ))⁻¹) + (Real.log (n : ℝ))⁻¹ = logReciprocalReal x := by
        have hIcc_eq : Finset.Icc 2 n = Finset.Ico 2 (n + 1) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        unfold logReciprocalReal
        change _ = ∑ k ∈ Finset.Icc 2 n, (Real.log (k : ℝ))⁻¹
        rw [hIcc_eq, Finset.sum_Ico_succ_top hn2]
      have hli_lo : logReciprocalReal x - (Real.log 2)⁻¹ ≤ li x := by
        calc logReciprocalReal x - (Real.log 2)⁻¹
            ≤ ∑ k ∈ Finset.Ico 2 n, (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ := hsum_lo
          _ ≤ ∑ k ∈ Finset.Ico 2 n, ∫ v in (k : ℝ)..((k + 1 : ℕ) : ℝ), (Real.log v)⁻¹ :=
              Finset.sum_le_sum hcell_lo
          _ ≤ (∑ k ∈ Finset.Ico 2 n, ∫ v in (k : ℝ)..((k + 1 : ℕ) : ℝ), (Real.log v)⁻¹) +
                ∫ v in (n : ℝ)..x, (Real.log v)⁻¹ := le_add_of_nonneg_right htail_lo
          _ = li x := hli_split.symm
      have hli_hi : li x ≤ logReciprocalReal x := by
        rw [hli_split, ← hsum_hi]
        exact add_le_add (Finset.sum_le_sum hcell_hi) htail_hi
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    refine ⟨(Real.log 2)⁻¹, inv_pos.mpr (Real.log_pos one_lt_two), ?_⟩
    have hlog_littleO := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / ((M : ℝ) + 1) by positivity)
    have hlog_ev : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ (1 / ((M : ℝ) + 1))‖ :=
      hlog_littleO.bound zero_lt_one
    filter_upwards [eventually_ge_atTop (2 : ℝ), hlog_ev] with x hx hlogx
    have hx1 : 1 ≤ x := by linarith
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlog_le : Real.log x ≤ x ^ (1 / ((M : ℝ) + 1)) := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hlog_nonneg,
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hlogx
      exact hlogx
    have hpow_le : (Real.log x) ^ M ≤ x := by
      calc (Real.log x) ^ M ≤ (x ^ (1 / ((M : ℝ) + 1))) ^ M := pow_le_pow_left₀ hlog_nonneg hlog_le M
        _ = x ^ ((M : ℝ) / ((M : ℝ) + 1)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; ring
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by
            rw [div_le_one (by positivity)]; linarith)
        _ = x := Real.rpow_one x
    have hlogM_pos : 0 < (Real.log x) ^ M := pow_pos (Real.log_pos (by linarith)) M
    have hx_div : 1 ≤ x / (Real.log x) ^ M := (one_le_div hlogM_pos).mpr hpow_le
    calc |logReciprocalReal x - li x| ≤ (Real.log 2)⁻¹ := hdiff_bd x hx
      _ ≤ (Real.log 2)⁻¹ * (x / (Real.log x) ^ M) :=
          le_mul_of_one_le_right (inv_nonneg.mpr (Real.log_nonneg one_le_two)) hx_div
      _ = (Real.log 2)⁻¹ * x / (Real.log x) ^ M := by ring

/-- **Link 3 (`pnt_implies_g_asymptotic`)**:
Assuming `PNTAllOrders`, all derivatives of `scaledRay I_prime` match `d_u^[j] gHat`
to all polynomial orders `1/u^M`. -/
theorem pnt_implies_g_asymptotic (hpnt : PNTAllOrders) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (scaledRay I_prime)) (d_u^[j] gHat) := by
  have heq : scaledRay I_prime = fun u : ℝ => (scaledMoment primeReal 0 u : ℂ) :=
    funext scaledRay_I_prime_eq
  rw [heq]
  exact approxLi_hasAsympExp (approxLi_primeReal hpnt) j

/-- **Conditional Pak Conjecture 2.5b (Indicator Series)**:
Assuming `PNTAllOrders`, `I_prime(q) = ∑_{p prime} q^p` is differentially transcendental
over `ℂ(q)` (`AlgebraicIndependent ℂ PrimeNome.indicatorCoordinates`). -/
theorem indicator_algebraicIndependent_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ indicatorCoordinates := by
  by_contra hdep
  obtain ⟨J, P, hP_ne, hP_zero⟩ := autonomous_transfer_indicator hdep
  cases J with
  | zero =>
    have hc : P = MvPolynomial.C (P.coeff 0) := by
      ext m
      have hm : m = 0 := Subsingleton.elim m 0
      subst hm; simp
    obtain ⟨u, hu⟩ := hP_zero.exists
    rw [hc, MvPolynomial.eval_C] at hu
    exact hP_ne (hc.trans (by rw [hu, map_zero]))
  | succ r =>
    exact hP_ne (no_autonomous_ade_of_asymptotic (pnt_implies_g_asymptotic hpnt) P hP_zero)

/-- **Pak's ICM 2018 Conjecture 2.5b (Combined Theorem)**:
Assuming `PNTAllOrders`, BOTH `I_prime(q) = ∑_{p prime} q^p` AND `Π(q) = ∑_{n ≥ 0} π(n) q^n`
are differentially transcendental over `ℂ(q)`. -/
theorem pak_conjecture_2_5b_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ indicatorCoordinates ∧ AlgebraicIndependent ℂ piCoordinates := by
  have hind := indicator_algebraicIndependent_of_pnt hpnt
  exact ⟨hind, piCoordinates_independent_iff_indicatorCoordinates.mpr hind⟩

/-- **Unconditional D-Transcendence Corollary (Zero PNT Hypothesis)**:
The smooth logarithmic reciprocal series `∑_{n ≥ 2} q^n / log n` is unconditionally
differentially transcendental over `ℂ(q)`. -/
theorem logReciprocal_algebraicIndependent :
    AlgebraicIndependent ℂ logReciprocalCoordinates := by
  by_contra hdep
  obtain ⟨J, P, hP_ne, hP_zero⟩ := autonomous_transfer_logReciprocal hdep
  have hasymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j (scaledRay logReciprocalSeries)) (d_u^[j] gHat) := by
    intro j
    have heq : scaledRay logReciprocalSeries = fun u : ℝ => (scaledMoment logReciprocalReal 0 u : ℂ) :=
      funext scaledRay_logReciprocal_eq
    rw [heq]
    exact approxLi_hasAsympExp approxLi_logReciprocalReal j
  cases J with
  | zero =>
    have hc : P = MvPolynomial.C (P.coeff 0) := by
      ext m
      have hm : m = 0 := Subsingleton.elim m 0
      subst hm; simp
    obtain ⟨u, hu⟩ := hP_zero.exists
    rw [hc, MvPolynomial.eval_C] at hu
    exact hP_ne (hc.trans (by rw [hu, map_zero]))
  | succ r =>
    exact hP_ne (no_autonomous_ade_of_asymptotic hasymp P hP_zero)

/-! ### 4. Partitions into Primes `∏_{p prime} (1 - q^p)^{-1}` -/

/-- Borel kernel for the logarithmic derivative of partitions into primes: `ζ(2 - ξ) Γ(2 - ξ)`. -/
@[expose] def phiPart (ξ : ℂ) : ℂ :=
  riemannZeta (2 - ξ) * Complex.Gamma (2 - ξ)

/-- Simple-pole frequencies `{1, 2, 3, 5, 7, ...}` of `ζ(2 - ξ) Γ(2 - ξ)`. -/
@[expose] def ωPart : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | k + 2 => ((2 * k + 3 : ℕ) : ℝ)

/-- Exact Stokes residues `-2πi * Res_{ξ = ωPart m} (ζ(2-ξ)Γ(2-ξ))`. -/
@[expose] def cPart : ℕ → ℂ
  | 0 => -(2 * (Real.pi : ℂ) * I)
  | 1 => (Real.pi : ℂ) * I
  | k + 2 => -(2 * (Real.pi : ℂ) * I) * (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2).factorial : ℂ)

lemma ωPart_strictMono : StrictMono ωPart := by
  intro a b hab
  rcases a with _ | _ | a <;> rcases b with _ | _ | b
  · omega
  · norm_num [ωPart]
  · simp only [ωPart]; exact_mod_cast (by omega : 1 < 2 * b + 3)
  · omega
  · omega
  · simp only [ωPart]; exact_mod_cast (by omega : 2 < 2 * b + 3)
  · omega
  · omega
  · simp only [ωPart]; exact_mod_cast (by omega : 2 * a + 3 < 2 * b + 3)

lemma ωPart_ge_one (m : ℕ) : (1 : ℝ) ≤ ωPart m := by
  rcases m with _ | _ | k <;> simp [ωPart]
  exact_mod_cast (by omega : 1 ≤ 2 * k + 3)

lemma bernoulli_two_mul_ne_zero {m : ℕ} (hm : m ≠ 0) : bernoulli (2 * m) ≠ 0 := by
  have hz_eq := riemannZeta_two_mul_nat hm
  have hz_ne : riemannZeta (2 * m) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat,
      Complex.natCast_im, mul_zero, sub_zero]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm
    linarith
  intro hb
  rw [hb, Rat.cast_zero, mul_zero, zero_div] at hz_eq
  exact hz_ne hz_eq

lemma riemannZeta_neg_odd_eq {k : ℕ} :
    riemannZeta (-((2 * k + 1 : ℕ) : ℂ)) = -(bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2 : ℕ) : ℂ) := by
  have h := riemannZeta_neg_nat_eq_bernoulli (2 * k + 1)
  have hpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_succ, show (-1 : ℂ) ^ (2 * k) = 1 from by rw [pow_mul]; simp]
    ring
  rw [hpow, neg_one_mul] at h
  convert h using 2
  push_cast; ring

theorem cPart_ne_zero (m : ℕ) : cPart m ≠ 0 := by
  have h2piI : -(2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rcases m with _ | _ | k
  · exact h2piI
  · simp [cPart, Real.pi_ne_zero, Complex.I_ne_zero]
  · unfold cPart
    have hb_ne : (bernoulli (2 * k + 2) : ℂ) ≠ 0 := by
      have hq : bernoulli (2 * (k + 1)) ≠ 0 := bernoulli_two_mul_ne_zero (Nat.succ_ne_zero k)
      rw [show 2 * k + 2 = 2 * (k + 1) by omega]
      exact Rat.cast_ne_zero.mpr hq
    have hfac_ne : ((2 * k + 2).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k + 2)
    exact div_ne_zero (mul_ne_zero h2piI hb_ne) hfac_ne

@[expose] def sigmaP (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 k).filter Nat.Prime, if p ∣ k then (p : ℝ) else 0

lemma sigmaP_nonneg (k : ℕ) : 0 ≤ sigmaP k :=
  Finset.sum_nonneg fun p _ => by split_ifs <;> positivity

private lemma coeff_partLogDerivSeries (k : ℕ) :
    PowerSeries.coeff k partLogDerivSeries = (sigmaP k : ℂ) := by
  simp only [partLogDerivSeries, PowerSeries.coeff_mk, sigmaP, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

@[expose] def partitionPrimesCoeff : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
    (∑ k ∈ (Finset.range (n + 1)).attach,
      sigmaP (k.1 + 1) * partitionPrimesCoeff (n - k.1)) / ((n + 1 : ℕ) : ℝ)
termination_by n => n
decreasing_by
  have hk := Finset.mem_range.mp k.2
  omega

lemma partitionPrimesCoeff_zero : partitionPrimesCoeff 0 = 1 := by
  rw [partitionPrimesCoeff]

lemma partitionPrimesCoeff_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * partitionPrimesCoeff (n + 1) =
      ∑ k ∈ Finset.range (n + 1), sigmaP (k + 1) * partitionPrimesCoeff (n - k) := by
  conv_lhs => rw [partitionPrimesCoeff]
  have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hne]
  rw [Finset.sum_attach (Finset.range (n + 1)) fun k => sigmaP (k + 1) * partitionPrimesCoeff (n - k)]

lemma partitionPrimesCoeff_nonneg (n : ℕ) : 0 ≤ partitionPrimesCoeff n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rw [partitionPrimesCoeff_zero]; exact zero_le_one
    | succ m =>
      have hmul : 0 ≤ ((m + 1 : ℕ) : ℝ) * partitionPrimesCoeff (m + 1) := by
        rw [partitionPrimesCoeff_succ]
        exact Finset.sum_nonneg fun k hk =>
          mul_nonneg (sigmaP_nonneg _) (ih (m - k) (by omega))
      exact nonneg_of_mul_nonneg_right hmul (by positivity)

/-- Generating series for partitions into primes `P_primes(q) = ∏_{p prime} (1 - q^p)^{-1}`,
defined uniquely by `P_primes(0) = 1` and `q P_primes'(q) = G(q) P_primes(q)`. -/
@[expose] def partitionPrimesSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (partitionPrimesCoeff n : ℂ)

theorem partitionPrimesSeries_constantCoeff :
    PowerSeries.constantCoeff partitionPrimesSeries = 1 := by
  simp [partitionPrimesSeries, partitionPrimesCoeff_zero]

theorem partitionPrimesSeries_ode :
    PowerSeries.X * PowerSeries.derivative partitionPrimesSeries =
      partLogDerivSeries * partitionPrimesSeries := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_partLogDerivSeries 0]
    simp [sigmaP]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i partLogDerivSeries * PowerSeries.coeff j partitionPrimesSeries) (m + 1),
      Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 partLogDerivSeries = 0 := by
      rw [coeff_partLogDerivSeries 0]; simp [sigmaP]
    rw [h0, zero_mul, add_zero]
    simp only [partitionPrimesSeries, PowerSeries.coeff_mk]
    have hL : (partitionPrimesCoeff (m + 1) : ℂ) * ((m : ℂ) + 1) =
        ((∑ k ∈ Finset.range (m + 1), sigmaP (k + 1) * partitionPrimesCoeff (m - k) : ℝ) : ℂ) := by
      rw [← partitionPrimesCoeff_succ m]
      push_cast; ring
    rw [hL, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [coeff_partLogDerivSeries (k + 1), show m + 1 - (k + 1) = m - k by omega]
    push_cast; rfl

theorem partitionPrimesSeries_diskBound : DiskCoeffBound partitionPrimesSeries := by
  intro r hr0 hr1
  obtain ⟨Cg, pg, hCg, hbg⟩ := partLogDeriv_polyBound
  have hsum_g : Summable (fun k : ℕ => Cg * ((k + 2 : ℝ) ^ pg * r ^ (k + 1))) := by
    have hs := summable_pow_mul_geometric_of_norm_lt_one pg
      (show ‖r‖ < 1 by simpa [abs_of_pos hr0] using hr1)
    have h := (hs.comp_injective (show Function.Injective (fun k : ℕ => k + 2) from
      fun _ _ hh => Nat.add_right_cancel hh)).mul_right r⁻¹
    refine (h.mul_left Cg).congr fun k => ?_
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, pow_add, pow_two]
    field_simp [hr0.ne']
  have hsum_sig : Summable (fun k : ℕ => sigmaP (k + 1) * r ^ (k + 1)) := by
    refine hsum_g.of_nonneg_of_le (fun k => mul_nonneg (sigmaP_nonneg _) (pow_nonneg hr0.le _)) fun k => ?_
    have hcoeff := hbg (k + 1)
    rw [coeff_partLogDerivSeries (k + 1), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sigmaP_nonneg _)] at hcoeff
    have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hcoeff
    calc sigmaP (k + 1) * r ^ (k + 1)
        ≤ (Cg * ((k : ℝ) + 2) ^ pg) * r ^ (k + 1) :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr0.le _)
      _ = Cg * ((k + 2 : ℝ) ^ pg * r ^ (k + 1)) := by ring
  let B : ℝ := ∑' k : ℕ, sigmaP (k + 1) * r ^ (k + 1)
  obtain ⟨N, hN⟩ := exists_nat_ge (max B 1)
  have hBN : B ≤ (N : ℝ) := (le_max_left B 1).trans hN
  let seq : ℕ → ℝ := fun n => partitionPrimesCoeff n * r ^ n
  let M : ℝ := (Finset.range (N + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N)) seq
  have hM_nonneg : 0 ≤ M := by
    have h0 : 0 ≤ seq 0 := mul_nonneg (partitionPrimesCoeff_nonneg 0) (pow_nonneg hr0.le 0)
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
              ∑ k ∈ Finset.range (m + 1), (sigmaP (k + 1) * r ^ (k + 1)) * seq (m - k) := by
            dsimp [seq]
            rw [← mul_assoc, partitionPrimesCoeff_succ m, Finset.sum_mul]
            refine Finset.sum_congr rfl fun k hk => ?_
            have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            rw [show m + 1 = (k + 1) + (m - k) by omega, pow_add]
            ring
          rw [heq_lhs]
          have hsum_bd : ∑ k ∈ Finset.range (m + 1), (sigmaP (k + 1) * r ^ (k + 1)) * seq (m - k) ≤
              (∑ k ∈ Finset.range (m + 1), sigmaP (k + 1) * r ^ (k + 1)) * M := by
            rw [Finset.sum_mul]
            refine Finset.sum_le_sum fun k hk => ?_
            refine mul_le_mul_of_nonneg_left (ih (m - k) (by omega))
              (mul_nonneg (sigmaP_nonneg _) (pow_nonneg hr0.le _))
          have hpart_le_B : ∑ k ∈ Finset.range (m + 1), sigmaP (k + 1) * r ^ (k + 1) ≤ B :=
            hsum_sig.sum_le_tsum (Finset.range (m + 1)) fun k _ =>
              mul_nonneg (sigmaP_nonneg _) (pow_nonneg hr0.le _)
          have hB_le_m1 : B ≤ ((m + 1 : ℕ) : ℝ) :=
            hBN.trans (by exact_mod_cast (by omega : N ≤ m + 1))
          calc _ ≤ (∑ k ∈ Finset.range (m + 1), sigmaP (k + 1) * r ^ (k + 1)) * M := hsum_bd
            _ ≤ B * M := mul_le_mul_of_nonneg_right hpart_le_B hM_nonneg
            _ ≤ ((m + 1 : ℕ) : ℝ) * M := mul_le_mul_of_nonneg_right hB_le_m1 hM_nonneg
        exact le_of_mul_le_mul_left hmul (by positivity)
  refine ⟨M, hM_nonneg, fun n => ?_⟩
  simp only [partitionPrimesSeries, PowerSeries.coeff_mk, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (partitionPrimesCoeff_nonneg n)]
  have hrn_pos : 0 < r ^ n := pow_pos hr0 n
  rw [inv_pow]
  calc partitionPrimesCoeff n = seq n * (r ^ n)⁻¹ := by dsimp [seq]; field_simp [hrn_pos.ne']
    _ ≤ M * (r ^ n)⁻¹ := mul_le_mul_of_nonneg_right (hseq_le n) (inv_nonneg.mpr hrn_pos.le)

theorem partitionPrimesSeries_qRay_ne_zero (u : ℝ) :
    value partitionPrimesSeries (qRay u) ≠ 0 := by
  have habs := seriesJet_abs partitionPrimesSeries_diskBound 0 (qRay_disk u)
  let termR : ℕ → ℝ := fun n => partitionPrimesCoeff n * (Real.exp (-Real.exp (-u))) ^ n
  have hsumR : Summable termR := by
    refine habs.of_nonneg_of_le (fun n =>
      mul_nonneg (partitionPrimesCoeff_nonneg n) (pow_nonneg (Real.exp_pos _).le n)) fun n => ?_
    simp only [seriesJet, Function.iterate_zero, id_eq, PrimeNome.term, partitionPrimesSeries,
      PowerSeries.coeff_mk, qRay, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (partitionPrimesCoeff_nonneg n), norm_pow, abs_of_pos (Real.exp_pos _)]
    exact le_rfl
  have hval : value partitionPrimesSeries (qRay u) = ((∑' n : ℕ, termR n : ℝ) : ℂ) := by
    unfold value
    rw [Complex.ofReal_tsum]
    congr 1; funext n
    simp [PrimeNome.term, partitionPrimesSeries, qRay, termR]
  have hpos : 0 < ∑' n : ℕ, termR n := by
    have h0 : termR 0 = 1 := by simp [termR, partitionPrimesCoeff_zero]
    calc (0 : ℝ) < 1 := zero_lt_one
      _ = termR 0 := h0.symm
      _ ≤ ∑' n : ℕ, termR n := hsumR.le_tsum 0 fun k _ =>
          mul_nonneg (partitionPrimesCoeff_nonneg k) (pow_nonneg (Real.exp_pos _).le k)
  rw [hval]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

/-- **Borel–Stokes–Vandermonde Transcendence Engine for Partitions into Primes**:
Because `cPart m ≠ 0` at every odd/small pole frequency `ωPart m ∈ {1, 2, 3, 5, 7, ...}`
(spaced by `≥ 1`), any lateral Borel pair `(g_pos, g_neg)` satisfying the bridge and Stokes
residue expansion for `ζ(2 - ξ)Γ(2 - ξ)` admits NO minimal-degree nonzero autonomous ADE. -/
theorem partitionPrimes_stokes_no_ade {r : ℕ}
    (IsFormalZero : MvPolynomial (Fin (r + 1)) ℂ → Prop)
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP_min : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 → Q.totalDegree < P.totalDegree → ¬ IsFormalZero Q)
    (hP_const : MvPolynomial.eval 0 P = 0)
    (g_pos g_neg : ℝ → ℂ)
    (h_diff : ∀ k < r, (∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv k g_pos) u) ∧
      (∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv k g_neg) u))
    (hP_pos : ∀ᶠ u in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u) P = 0)
    (hP_neg : ∀ᶠ u in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_neg u) P = 0)
    (hg_bdd : ∀ j : Fin (r + 1), ∃ C : ℝ, ∀ᶠ u in atTop, ‖iteratedDeriv j.val g_pos u‖ ≤ C)
    (h_exp : ∀ (n : ℕ) (j : Fin (r + 1)), n ≤ r →
      ∃ C : ℝ, ∀ᶠ u in atTop,
        ‖iteratedDeriv j.val (fun t => g_neg t - g_pos t) u -
          ∑ m ∈ Finset.range (n + 1), cPart m * (-(ωPart m : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(ωPart m : ℂ) * (u : ℂ))‖ ≤
          C * Real.exp (-(ωPart n + 1) * u))
    (h_bridge : ∀ (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∃ C : ℝ, ∀ᶠ u in atTop,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u) Q‖ ≤
          C * Real.exp (-u)) →
      IsFormalZero Q) :
    P = 0 :=
  stokes_vandermonde_general_eq_zero IsFormalZero P hP_min hP_const
    ωPart 1 zero_lt_one ωPart_ge_one ωPart_strictMono
    cPart (fun m _ => cPart_ne_zero m)
    g_pos g_neg h_diff hP_pos hP_neg hg_bdd
    (fun n j hn => h_exp n j (Nat.lt_succ_iff.mp hn))
    (fun Q hQ => h_bridge Q (by simpa [neg_one_mul] using hQ))

/-- **Logarithmic-Derivative Autonomous Transfer for `∏_p (1 - q^p)^{-1}`**:
Any formal differential algebraic relation over `ℂ(q)` satisfied by `partitionPrimesSeries`
transfers unconditionally to a nonzero autonomous polynomial ODE for `scaledRay partLogDerivSeries`. -/
theorem partitionPrimes_log_deriv_transfer
    (hdep : ¬ AlgebraicIndependent ℂ (seriesCoordinates partitionPrimesSeries)) :
    ∃ (J : ℕ) (R : MvPolynomial (Fin J) ℂ), R ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay partLogDerivSeries) u) R = 0 :=
  autonomous_transfer_log_deriv
    partitionPrimesSeries_diskBound partLogDeriv_polyBound.to_diskCoeffBound
    partitionPrimesSeries_ode partitionPrimesSeries_qRay_ne_zero hdep

end
end PakPrimes.Main