module

public import PakStokes.AllD.MockModularAlgebraCore
import all PakStokes.AllD.MockModularAlgebraCore
public import PakStokes.AllD.MockModularRotatedRays
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Wave 15 (Module 2): Single-Cusp `y = 1` Eichler Split, Cauchy `q₁`-Descent, & End-to-End Paper #10 Assembly

Formalizes **100% unconditionally from Mathlib** (zero placeholders) the cusp-to-Stokes
descent engine and end-to-end assembly theorems for Paper #10 (Sections 3.1, 4, 5.3, and 6):

1. **Proposition 3.1 — Single-Cusp `y = 1` Eichler Integral Split:**
   Exact Möbius coordinate pullback `τ(u) = -1/M + i u / M²`, `γ τ(u) = 1/M + i / u`,
   `θ_q = -(M² / (2 π)) d/du`, exact `t = 1 / (M² y)` integral substitution combining
   `∫_α^{1/M²} + ∫_{1/M²}^∞` with `∫_{1/u}^∞` into `Φ_{[1,∞)}(u) + F_hol(u) + E_elem(u)`,
   holomorphy of `F_hol` on the open unit disk `𝔻₁`, and exact miraculous zero-mode
   cancellations for both `k ≠ 1` and `k = 1`.
2. **Lemma 4.1 — Uniform Cauchy `q₁`-Tail Bound:**
   `D`-fold Cauchy convolution polynomial growth bound and uniform exponential tail bound
   `‖∑_{m > r₀} C_m(u) q₁^{(m-r₀)/L}‖ ≤ K₁(r₀) exp(-π / (L u))` on `(0, u₀ / 2]`.
3. **Proposition 4.2 — Logarithmic/Puiseux Scale Separation, `q₁`-Induction, & Minimal-Degree Descent:**
   Exact asymptotic decoupling of `∑_{ε ∈ {0,1}} ∑_{a=0}^D u^{ε/2} (log u)^a A_{ε,a}(u) = O(e^{-c/u})`,
   finite `q₁`-induction (`m = -D N₀, …, 0`) via `watson_of_gevrey1_zero`, exact top-degree
   survival `[Z^α] Q_{0,0,0}(u; Z) = u^{N₁} ([X^α] P_D) γ^α ≠ 0`, and minimal-total-degree
   descent into `ℂ{x}[Z]`.
4. **Proposition 5.3 & End-to-End Paper #10 Master Assembly Theorems:**
   Simultaneous lateral annihilation of convergent polynomial relations, collision-free
   translation-invariance induction (`W_n^{int} · ∇_Z R = 0` and `W_n^{half} · ∇_Z R = 0`),
   and complete end-to-end proofs of:
   - `mockModular_scalar_diff_trans_of_cuspSplit` (Paper #10 Theorem A, via `mockModular_minimal_annihilator_contradiction`);
   - `mockModular_joint_shadow_rank_of_cuspSplit` (Paper #10 Theorem B, via `positiveWeight_modular_thetaQ_diff_indep`).
-/

open scoped Topology BigOperators
open Filter MeasureTheory

namespace CubicTheta.AllD

@[expose] public section
noncomputable section

private lemma continuousAt_cpow_const_comp {α : Type*} [TopologicalSpace α] {f : α → ℂ} {x : α} {c : ℂ}
    (hf : ContinuousAt f x) (hsl : f x ∈ Complex.slitPlane) :
    ContinuousAt (fun t ↦ (f t) ^ c) x :=
  (((hasDerivAt_id (f x)).cpow_const (c := c) hsl).continuousAt).comp hf

private lemma differentiableOn_finset_prod {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → ℂ → ℂ} {U : Set ℂ} (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun u ↦ ∏ i ∈ s, f i u) U := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    have hfun : (fun u ↦ ∏ i ∈ insert a s, f i u) = fun u ↦ f a u * ∏ i ∈ s, f i u := by
      ext u; exact Finset.prod_insert ha
    rw [hfun]; exact h1.mul h2

private lemma powerSeries_mul_ne_zero {f g : PowerSeries ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  classical
  have hfx : ∃ n, f.coeff n ≠ 0 := by
    by_contra h; push Not at h; exact hf (PowerSeries.ext fun n ↦ by simp [h n])
  have hgx : ∃ n, g.coeff n ≠ 0 := by
    by_contra h; push Not at h; exact hg (PowerSeries.ext fun n ↦ by simp [h n])
  let m := Nat.find hfx
  let n := Nat.find hgx
  intro h0
  have hc := congrArg (PowerSeries.coeff (m + n)) h0
  rw [map_zero, PowerSeries.coeff_mul, Finset.sum_eq_single (m, n)] at hc
  · exact mul_ne_zero (Nat.find_spec hfx) (Nat.find_spec hgx) hc
  · intro x hx hne
    have hsum : x.1 + x.2 = m + n := Finset.mem_antidiagonal.mp hx
    by_cases h1 : x.1 < m
    · rw [not_not.mp (Nat.find_min hfx h1), zero_mul]
    · have h2 : x.2 < n := by
        have : x.1 ≠ m ∨ x.2 ≠ n := by by_contra h; push Not at h; exact hne (Prod.ext h.1 h.2)
        omega
      rw [not_not.mp (Nat.find_min hgx h2), mul_zero]
  · intro hnot
    have hmn : (m, n) ∈ Finset.antidiagonal (m + n) := Finset.mem_antidiagonal.mpr rfl
    exact absurd hmn hnot

instance : NoZeroDivisors convergentSubring where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    by_contra hne; push Not at hne
    have hval : a.val * b.val = 0 := congrArg Subtype.val h
    exact powerSeries_mul_ne_zero (fun h0 ↦ hne.1 (Subtype.ext h0))
      (fun h0 ↦ hne.2 (Subtype.ext h0)) hval

instance : Nontrivial convergentSubring :=
  ⟨⟨0, 1, fun h ↦ by
    have hc := congrArg (fun x : convergentSubring ↦ x.val.coeff 0) h.symm
    simp at hc⟩⟩

instance : IsDomain convergentSubring :=
  NoZeroDivisors.to_isDomain convergentSubring

instance : CharZero convergentSubring where
  cast_injective m n h := by
    have hc := congrArg (fun x : convergentSubring ↦ x.val.coeff 0) h
    have hcm : ((m : convergentSubring).val).coeff 0 = (m : ℂ) := by
      have : (m : convergentSubring).val = (m : PowerSeries ℂ) := map_natCast convergentSubring.subtype m
      rw [this, ← map_natCast PowerSeries.C, PowerSeries.coeff_zero_C]
    have hcn : ((n : convergentSubring).val).coeff 0 = (n : ℂ) := by
      have : (n : convergentSubring).val = (n : PowerSeries ℂ) := map_natCast convergentSubring.subtype n
      rw [this, ← map_natCast PowerSeries.C, PowerSeries.coeff_zero_C]
    rw [hcm, hcn] at hc
    exact Nat.cast_injective hc

private lemma integral_Ioi_eq_interval_add_Ioi {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf_ab : IntervalIntegrable f volume a b) (hf_hi : IntegrableOn f (Set.Ioi b)) :
    ∫ x in Set.Ioi a, f x = (∫ x in a..b, f x) + ∫ x in Set.Ioi b, f x := by
  have hf_ioc : IntegrableOn f (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf_ab
  have hdisj : Disjoint (Set.Ioc a b) (Set.Ioi b) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 ↦ not_lt.mpr hx1.2 hx2
  have hunion : Set.Ioc a b ∪ Set.Ioi b = Set.Ioi a := by
    ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · exact lt_of_le_of_lt hab h2
    · intro h
      by_cases hb : x ≤ b
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr (lt_of_not_ge hb)
  rw [intervalIntegral.integral_of_le hab,
      ← setIntegral_union hdisj measurableSet_Ioi hf_ioc hf_hi, hunion]

/-! ### Section 1: Proposition 3.1 — Single-Cusp `y = 1` Eichler Integral Split -/

/-- Single-cusp Möbius coordinate `τ(u) = -1/M + i u / M²`. -/
def tauOfU (M : ℝ) (u : ℂ) : ℂ :=
  -(1 / (M : ℂ)) + Complex.I * u / ((M : ℂ) ^ 2)

/-- Image `γ τ(u) = 1/M + i / u` under `γ = (1 0; M 1)`. -/
def gammaTauOfU (M : ℝ) (u : ℂ) : ℂ :=
  (1 / (M : ℂ)) + Complex.I / u

/-- Parabolic Möbius transformation `γ τ = τ / (M τ + 1)`. -/
def gammaMobius (M : ℝ) (τ : ℂ) : ℂ :=
  τ / ((M : ℂ) * τ + 1)

theorem M_mul_tauOfU_add_one {M : ℝ} (hM : M ≠ 0) (u : ℂ) :
    (M : ℂ) * tauOfU M u + 1 = Complex.I * u / (M : ℂ) := by
  have hMC : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM
  dsimp [tauOfU]
  field_simp [hMC]
  ring

theorem gammaMobius_tauOfU {M : ℝ} (hM : M ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    gammaMobius M (tauOfU M u) = gammaTauOfU M u := by
  have hMC : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM
  dsimp [gammaMobius, gammaTauOfU]
  rw [M_mul_tauOfU_add_one hM u]
  dsimp [tauOfU]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp [hMC, hu, hI]
  have hmul : Complex.I * (u + (M : ℂ) * Complex.I) = Complex.I * u + (M : ℂ) * Complex.I ^ 2 := by ring
  rw [hmul, Complex.I_sq]
  ring

theorem tauOfU_mem_upperHalfPlane {M u : ℝ} (hM : 0 < M) (hu : 0 < u) :
    tauOfU M (u : ℂ) ∈ upperHalfPlane := by
  change 0 < (tauOfU M (u : ℂ)).im
  have him : (tauOfU M (u : ℂ)).im = u / M ^ 2 := by
    have h12 : tauOfU M (u : ℂ) =
        (((-(1 / M) : ℝ) : ℂ)) + (((u / M ^ 2 : ℝ) : ℂ)) * Complex.I := by
      dsimp [tauOfU]; push_cast; ring
    rw [h12, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [him]
  positivity

theorem gammaTauOfU_mem_upperHalfPlane {M u : ℝ} (_hM : 0 < M) (hu : 0 < u) :
    gammaTauOfU M (u : ℂ) ∈ upperHalfPlane := by
  change 0 < (gammaTauOfU M (u : ℂ)).im
  have him : (gammaTauOfU M (u : ℂ)).im = 1 / u := by
    dsimp [gammaTauOfU]
    have h1 : (1 / (M : ℂ)) = ((1 / M : ℝ) : ℂ) := by push_cast; rfl
    have h2 : Complex.I / (u : ℂ) = ((1 / u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1, h2]
    simp
  rw [him]
  positivity

/-- Pullback of `iteratedDeriv j` along `t ↦ tauOfU M t`:
`d^j/du^j (f(τ(u))) = (i / M²)^j f^{(j)}(τ(u))`. -/
theorem iteratedDeriv_comp_tauOfU {M : ℝ} (hM : 0 < M) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (j : ℕ) :
    ∀ u : ℝ, 0 < u →
      iteratedDeriv j (fun t : ℝ ↦ f (tauOfU M (t : ℂ))) u =
        (Complex.I / ((M : ℂ) ^ 2)) ^ j * iteratedDeriv j f (tauOfU M (u : ℂ)) := by
  have hdiff_iter : ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m f) upperHalfPlane := by
    intro m
    induction m with
    | zero => simpa [iteratedDeriv_zero] using hf
    | succ m ih => simpa [iteratedDeriv_succ] using ih.deriv isOpen_upperHalfPlane
  have htau_deriv : ∀ u : ℝ, HasDerivAt (fun t : ℝ ↦ tauOfU M (t : ℂ)) (Complex.I / ((M : ℂ) ^ 2)) u := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) (1 : ℂ) u := Complex.ofRealCLM.hasDerivAt
    have h2 := ((h1.const_mul Complex.I).div_const ((M : ℂ) ^ 2)).const_add (-(1 / (M : ℂ)))
    simpa only [tauOfU, mul_one] using h2
  induction j with
  | zero => intro u _; simp [iteratedDeriv_zero]
  | succ j ih =>
    intro u hu
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hev : iteratedDeriv j (fun t : ℝ ↦ f (tauOfU M (t : ℂ))) =ᶠ[𝓝 u]
        fun t : ℝ ↦ (Complex.I / ((M : ℂ) ^ 2)) ^ j * iteratedDeriv j f (tauOfU M (t : ℂ)) := by
      filter_upwards [eventually_gt_nhds hu] with t ht
      exact ih t ht
    rw [hev.deriv_eq]
    have hmem : tauOfU M (u : ℂ) ∈ upperHalfPlane := tauOfU_mem_upperHalfPlane hM hu
    have hd_f : HasDerivAt (iteratedDeriv j f) (deriv (iteratedDeriv j f) (tauOfU M (u : ℂ)))
        (tauOfU M (u : ℂ)) :=
      ((hdiff_iter j _ hmem).differentiableAt (isOpen_upperHalfPlane.mem_nhds hmem)).hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ ↦ iteratedDeriv j f (tauOfU M (t : ℂ)))
        ((Complex.I / ((M : ℂ) ^ 2)) * deriv (iteratedDeriv j f) (tauOfU M (u : ℂ))) u := by
      have hs := hd_f.scomp u (htau_deriv u)
      simpa [Function.comp_def, smul_eq_mul] using hs
    rw [(hcomp.const_mul ((Complex.I / ((M : ℂ) ^ 2)) ^ j)).deriv, pow_succ]
    ring

/-- Pullback of `θ_q^j = (1 / (2 π i))^j ∂_τ^j` along `τ(u)`:
`θ_q^j f(τ(u)) = (-M² / (2 π))^j ∂_u^j (f ∘ τ)(u)` (`eq:theta-pullback`). -/
theorem theta_pullback_iteratedDeriv {M : ℝ} (hM : 0 < M) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j * iteratedDeriv j f (tauOfU M (u : ℂ)) =
      (-((M : ℂ) ^ 2) / (2 * (Real.pi : ℂ))) ^ j *
        iteratedDeriv j (fun t : ℝ ↦ f (tauOfU M (t : ℂ))) u := by
  rw [iteratedDeriv_comp_tauOfU hM hf j u hu, ← mul_assoc, ← mul_pow]
  congr 1
  congr 1
  have hMne : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp [hMne, hpi, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- Principal-branch power of `I * a` for positive real `a > 0`:
`(I * a)^k = exp(I * π / 2 * k) * a^k`. -/
theorem cpow_I_mul_ofReal_pos {a : ℝ} (ha : 0 < a) (k : ℂ) :
    (Complex.I * (a : ℂ)) ^ k =
      Complex.exp (Complex.I * (Real.pi : ℂ) / 2 * k) * (a : ℂ) ^ k := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hIa : Complex.I * (a : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero haC
  have hlog : Complex.log (Complex.I * (a : ℂ)) =
      ((Real.log a : ℝ) : ℂ) + Complex.I * (Real.pi : ℂ) / 2 := by
    have hexp : Complex.exp (((Real.log a : ℝ) : ℂ) + Complex.I * (Real.pi : ℂ) / 2) =
        Complex.I * (a : ℂ) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha,
          show Complex.I * (Real.pi : ℂ) / 2 = (Real.pi : ℂ) / 2 * Complex.I by ring,
          Complex.exp_pi_div_two_mul_I, mul_comm]
    rw [← hexp, Complex.log_exp]
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero hIa, Complex.cpow_def_of_ne_zero haC,
      hlog, Complex.ofReal_log ha.le, add_mul, Complex.exp_add, mul_comm]

/-- Principal-branch power of `-I * a` for positive real `a > 0`:
`(-I * a)^k = exp(-I * π / 2 * k) * a^k`. -/
theorem cpow_neg_I_mul_ofReal_pos {a : ℝ} (ha : 0 < a) (k : ℂ) :
    (-Complex.I * (a : ℂ)) ^ k =
      Complex.exp (-Complex.I * (Real.pi : ℂ) / 2 * k) * (a : ℂ) ^ k := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hIa : -Complex.I * (a : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) haC
  have hlog : Complex.log (-Complex.I * (a : ℂ)) =
      ((Real.log a : ℝ) : ℂ) + (-Complex.I * (Real.pi : ℂ) / 2) := by
    have hexp : Complex.exp (((Real.log a : ℝ) : ℂ) + (-Complex.I * (Real.pi : ℂ) / 2)) =
        -Complex.I * (a : ℂ) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha,
          show -Complex.I * (Real.pi : ℂ) / 2 = -((Real.pi : ℂ) / 2 * Complex.I) by ring,
          Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
      ring
    rw [← hexp, Complex.log_exp]
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero hIa, Complex.cpow_def_of_ne_zero haC,
      hlog, Complex.ofReal_log ha.le, add_mul, Complex.exp_add, mul_comm]

/-- Positive-real power multiplication `((a * b : ℝ) : ℂ)^k = a^k * b^k`. -/
theorem ofReal_mul_cpow_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℂ) :
    ((a * b : ℝ) : ℂ) ^ k = (a : ℂ) ^ k * (b : ℂ) ^ k := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have habC : ((a * b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos ha hb).ne'
  rw [Complex.cpow_def_of_ne_zero habC, Complex.cpow_def_of_ne_zero haC,
      Complex.cpow_def_of_ne_zero hbC, ← Complex.exp_add, ← add_mul,
      ← Complex.ofReal_log (mul_pos ha hb).le, ← Complex.ofReal_log ha.le,
      ← Complex.ofReal_log hb.le, Real.log_mul ha.ne' hb.ne', Complex.ofReal_add]

/-- Positive-real power division `((a / b : ℝ) : ℂ)^k = a^k * b^(-k)`. -/
theorem ofReal_div_cpow_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℂ) :
    ((a / b : ℝ) : ℂ) ^ k = (a : ℂ) ^ k * (b : ℂ) ^ (-k) := by
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have h := ofReal_mul_cpow_of_pos (div_pos ha hb) hb k
  rw [div_mul_cancel₀ a hb.ne'] at h
  have hmul := congrArg (· * (b : ℂ) ^ (-k)) h
  rw [mul_assoc, ← Complex.cpow_add _ _ hbC, add_neg_cancel, Complex.cpow_zero, mul_one] at hmul
  exact hmul.symm

/-- Exact interval substitution `t = 1 / (c * y)` (`c > 0`, `0 < a ≤ b`) for continuous `f : ℝ → ℂ`. -/
theorem intervalIntegral_comp_inv_mul {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ t in a..b, f t =
      ∫ y in (1 / (c * b))..(1 / (c * a)), f (1 / (c * y)) * ((1 / (c * y ^ 2) : ℝ) : ℂ) := by
  let y₀ : ℝ := 1 / (c * b)
  let y₁ : ℝ := 1 / (c * a)
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hy₀_pos : 0 < y₀ := by positivity
  have hy₀_le : y₀ ≤ y₁ := by
    dsimp [y₀, y₁]
    exact one_div_le_one_div_of_le (mul_pos hc ha) (mul_le_mul_of_nonneg_left hab hc.le)
  have hmem_t : ∀ y ∈ Set.Icc y₀ y₁, 1 / (c * y) ∈ Set.Icc a b := by
    intro y hy
    have hy_pos : 0 < y := lt_of_lt_of_le hy₀_pos hy.1
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ (mul_pos hc hy_pos)]
      have h1 : y ≤ 1 / (c * a) := hy.2
      rw [le_div_iff₀ (mul_pos hc ha)] at h1
      nlinarith
    · rw [div_le_iff₀ (mul_pos hc hy_pos)]
      have h1 : 1 / (c * b) ≤ y := hy.1
      rw [div_le_iff₀ (mul_pos hc hb)] at h1
      nlinarith
  let G : ℝ → ℂ := fun y ↦
    (∫ t in (1 / (c * y))..b, f t) -
      ∫ s in y₀..y, f (1 / (c * s)) * ((1 / (c * s ^ 2) : ℝ) : ℂ)
  have hcont_rhs : ContinuousOn (fun s : ℝ ↦ f (1 / (c * s)) * ((1 / (c * s ^ 2) : ℝ) : ℂ))
      (Set.Icc y₀ y₁) := by
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le hy₀_pos hs.1
    have hinv_cont : ContinuousWithinAt (fun x : ℝ ↦ 1 / (c * x)) (Set.Icc y₀ y₁) s :=
      (continuousAt_const.div (continuousAt_const.mul continuousAt_id) (mul_pos hc hs_pos).ne').continuousWithinAt
    have hf_comp : ContinuousWithinAt (fun x : ℝ ↦ f (1 / (c * x))) (Set.Icc y₀ y₁) s :=
      ContinuousWithinAt.comp (f := fun x : ℝ ↦ 1 / (c * x))
        (hf (1 / (c * s)) (hmem_t s hs)) hinv_cont (fun x hx ↦ hmem_t x hx)
    have hjac : ContinuousWithinAt (fun x : ℝ ↦ ((1 / (c * x ^ 2) : ℝ) : ℂ)) (Set.Icc y₀ y₁) s :=
      (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 2))
          (mul_pos hc (sq_pos_of_pos hs_pos)).ne')).continuousWithinAt
    exact hf_comp.mul hjac
  have hmem_t_oo : ∀ y ∈ Set.Ioo y₀ y₁, 1 / (c * y) ∈ Set.Ioo a b := by
    intro y hy
    have hy_pos : 0 < y := lt_trans hy₀_pos hy.1
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (mul_pos hc hy_pos)]
      have h1 : y < 1 / (c * a) := hy.2
      rw [lt_div_iff₀ (mul_pos hc ha)] at h1
      nlinarith
    · rw [div_lt_iff₀ (mul_pos hc hy_pos)]
      have h1 : 1 / (c * b) < y := hy.1
      rw [div_lt_iff₀ (mul_pos hc hb)] at h1
      nlinarith
  have hf_int_a : ∀ u ∈ Set.Icc a b, IntervalIntegrable f volume a u := fun u hu ↦
    (hf.mono (Set.Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1
  have hf_int_ub : ∀ u ∈ Set.Icc a b, IntervalIntegrable f volume u b := fun u hu ↦
    (hf.mono (Set.Icc_subset_Icc hu.1 le_rfl)).intervalIntegrable_of_Icc hu.2
  have hsplit_u : ∀ u ∈ Set.Icc a b, ∫ t in u..b, f t = (∫ t in a..b, f t) - ∫ t in a..u, f t := by
    intro u hu
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hf_int_a u hu) (hf_int_ub u hu)
    linear_combination hadd
  have hG_cont : ContinuousOn G (Set.Icc y₀ y₁) := by
    have hcont_prim1 : ContinuousOn (fun u : ℝ ↦ (∫ t in a..b, f t) - ∫ t in a..u, f t) (Set.Icc a b) := by
      have hp : ContinuousOn (fun u : ℝ ↦ ∫ t in a..u, f t) (Set.Icc a b) := by
        have hint : IntegrableOn f (Set.uIcc a b) volume := by
          rw [Set.uIcc_of_le hab]; exact hf.integrableOn_Icc
        simpa [Set.uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval (μ := volume) hint
      exact continuousOn_const.sub hp
    have hcont_inv : ContinuousOn (fun s : ℝ ↦ 1 / (c * s)) (Set.Icc y₀ y₁) := fun s hs ↦
      (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
        (mul_pos hc (lt_of_lt_of_le hy₀_pos hs.1)).ne').continuousWithinAt
    have hcont1 : ContinuousOn (fun s : ℝ ↦ ∫ t in (1 / (c * s))..b, f t) (Set.Icc y₀ y₁) :=
      (hcont_prim1.comp hcont_inv (fun s hs ↦ hmem_t s hs)).congr fun s hs ↦ hsplit_u _ (hmem_t s hs)
    have hcont2 : ContinuousOn
        (fun s : ℝ ↦ ∫ r in y₀..s, f (1 / (c * r)) * ((1 / (c * r ^ 2) : ℝ) : ℂ)) (Set.Icc y₀ y₁) := by
      have hint2 : IntegrableOn (fun s : ℝ ↦ f (1 / (c * s)) * ((1 / (c * s ^ 2) : ℝ) : ℂ))
          (Set.uIcc y₀ y₁) volume := by
        rw [Set.uIcc_of_le hy₀_le]; exact hcont_rhs.integrableOn_Icc
      simpa [Set.uIcc_of_le hy₀_le] using intervalIntegral.continuousOn_primitive_interval (μ := volume) hint2
    exact hcont1.sub hcont2
  have hG_deriv : ∀ y ∈ Set.Ioo y₀ y₁, HasDerivAt G 0 y := by
    intro y hy
    have hy_pos : 0 < y := lt_trans hy₀_pos hy.1
    have hty_oo : 1 / (c * y) ∈ Set.Ioo a b := hmem_t_oo y hy
    have hty_cc : 1 / (c * y) ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hty_oo
    have hIcc_nhds : Set.Icc a b ∈ 𝓝 (1 / (c * y)) := Icc_mem_nhds hty_oo.1 hty_oo.2
    have hf_meas_at : StronglyMeasurableAtFilter f (𝓝 (1 / (c * y))) volume := by
      rw [← nhdsWithin_eq_nhds.mpr hIcc_nhds]
      exact hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc (1 / (c * y))
    have hprim_at : HasDerivAt (fun u : ℝ ↦ ∫ t in a..u, f t) (f (1 / (c * y))) (1 / (c * y)) :=
      intervalIntegral.integral_hasDerivAt_right (hf_int_a _ hty_cc) hf_meas_at
        ((hf _ hty_cc).continuousAt hIcc_nhds)
    have hI1_at : HasDerivAt (fun u : ℝ ↦ (∫ t in a..b, f t) - ∫ t in a..u, f t)
        (-f (1 / (c * y))) (1 / (c * y)) := by
      simpa using hprim_at.const_sub (∫ t in a..b, f t)
    have hphi_deriv : HasDerivAt (fun s : ℝ ↦ 1 / (c * s)) (-(1 / (c * y ^ 2))) y := by
      have hmul : HasDerivAt (fun s : ℝ ↦ c * s) c y := by
        simpa using (hasDerivAt_id y).const_mul c
      have h2 := hmul.inv (mul_pos hc hy_pos).ne'
      have hval : -c / (c * y) ^ 2 = -(1 / (c * y ^ 2)) := by field_simp [hc.ne', hy_pos.ne']
      rw [hval] at h2
      have hfun : (fun s : ℝ ↦ 1 / (c * s)) = (fun s : ℝ ↦ c * s)⁻¹ := by ext s; simp [one_div]
      rw [hfun]; exact h2
    have hcomp1_raw : HasDerivAt (fun s : ℝ ↦ (∫ t in a..b, f t) - ∫ t in a..(1 / (c * s)), f t)
        (f (1 / (c * y)) * ((1 / (c * y ^ 2) : ℝ) : ℂ)) y := by
      have h1 : HasDerivAt ((fun u : ℝ ↦ (∫ t in a..b, f t) - ∫ t in a..u, f t) ∘ fun s ↦ 1 / (c * s))
          ((-(1 / (c * y ^ 2))) • (-f (1 / (c * y)))) y := hI1_at.scomp y hphi_deriv
      have hsmul : (-(1 / (c * y ^ 2))) • (-f (1 / (c * y))) =
          f (1 / (c * y)) * ((1 / (c * y ^ 2) : ℝ) : ℂ) := by
        rw [Complex.real_smul]; push_cast; ring
      rw [hsmul] at h1
      exact h1
    have hcomp1 : HasDerivAt (fun s : ℝ ↦ ∫ t in (1 / (c * s))..b, f t)
        (f (1 / (c * y)) * ((1 / (c * y ^ 2) : ℝ) : ℂ)) y := by
      refine hcomp1_raw.congr_of_eventuallyEq ?_
      filter_upwards [Icc_mem_nhds hy.1 hy.2] with s hs
      exact hsplit_u _ (hmem_t s hs)
    have hcomp2 : HasDerivAt
        (fun s : ℝ ↦ ∫ r in y₀..s, f (1 / (c * r)) * ((1 / (c * r ^ 2) : ℝ) : ℂ))
        (f (1 / (c * y)) * ((1 / (c * y ^ 2) : ℝ) : ℂ)) y := by
      have hint_y : IntervalIntegrable (fun r : ℝ ↦ f (1 / (c * r)) * ((1 / (c * r ^ 2) : ℝ) : ℂ))
          volume y₀ y :=
        (hcont_rhs.mono (Set.Icc_subset_Icc le_rfl hy.2.le)).intervalIntegrable_of_Icc hy.1.le
      have hy_nhds : Set.Icc y₀ y₁ ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
      have hmeas2 : StronglyMeasurableAtFilter
          (fun r : ℝ ↦ f (1 / (c * r)) * ((1 / (c * r ^ 2) : ℝ) : ℂ)) (𝓝 y) volume := by
        rw [← nhdsWithin_eq_nhds.mpr hy_nhds]
        exact hcont_rhs.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc y
      exact intervalIntegral.integral_hasDerivAt_right hint_y hmeas2
        ((hcont_rhs y (Set.Ioo_subset_Icc_self hy)).continuousAt hy_nhds)
    have hsub := hcomp1.sub hcomp2
    rw [sub_self] at hsub
    exact hsub
  have hG_eq : G y₁ - G y₀ = 0 := by
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy₀_le hG_cont hG_deriv
      intervalIntegrable_const
    simpa using h1.symm
  have hGy₀ : G y₀ = 0 := by
    dsimp [G, y₀]
    have hcb : 1 / (c * (1 / (c * b))) = b := by field_simp [hc.ne', hb.ne']
    rw [hcb, intervalIntegral.integral_same, intervalIntegral.integral_same, sub_self]
  have hGy₁ : G y₁ = (∫ t in a..b, f t) -
      ∫ y in y₀..y₁, f (1 / (c * y)) * ((1 / (c * y ^ 2) : ℝ) : ℂ) := by
    dsimp [G, y₁]
    have hca : 1 / (c * (1 / (c * a))) = a := by field_simp [hc.ne', ha.ne']
    rw [hca]
  rw [hGy₀, sub_zero, hGy₁] at hG_eq
  exact sub_eq_zero.mp hG_eq

/-- Holomorphic tail integral `F_hol(u) = 2^{k-1} ∫_{1/M²}^∞ conj(g_cusp(-1/M + i t)) (t + u / M²)^{-k} dt`
(`eq:Fhol-def`). -/
def FHol (M : ℝ) (k : ℂ) (g_cusp : ℂ → ℂ) (u : ℂ) : ℂ :=
  (2 : ℂ) ^ (k - 1) *
    ∫ t in Set.Ioi (1 / M ^ 2 : ℝ),
      starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) *
        ((t : ℂ) + u / ((M : ℂ) ^ 2)) ^ (-k)

/-- Exact elementary zero-mode closed form for `k ≠ 1` (`eq:Eelem-def`, first line). -/
def EElemNonOne (M : ℝ) (k c0 : ℂ) (u : ℂ) : ℂ :=
  ((2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 / (1 - k)) * (1 + u) ^ (1 - k) *
    ((Complex.I / (M : ℂ)) ^ (-k) * u⁻¹ - ((M : ℂ) ^ (2 * k - 2)))

/-- Exact elementary zero-mode closed form for `k = 1` (`eq:Eelem-def`, second line). -/
def EElemOne (M : ℝ) (c0 : ℂ) (u : ℝ) : ℂ :=
  starRingEnd ℂ c0 *
    ((M : ℂ) / (Complex.I * (u : ℂ)) * ((Real.log ((1 + u) / (2 * u)) : ℝ) : ℂ) +
      ((Real.log (2 * M ^ 2 / (1 + u)) : ℝ) : ℂ))

/-- Canonical non-holomorphic cusp Eichler integral along `τ = x₀ + i α` (`main.tex:541, 567`):
`h_cusp^-(x₀ + i α) = -2^{k-1} ∫_α^∞ conj(g_cusp(x₀ + i t)) (t + α)^{-k} dt`. -/
def hCuspMinusRay (k : ℂ) (g_cusp : ℂ → ℂ) (x₀ α : ℝ) : ℂ :=
  -(2 : ℂ) ^ (k - 1) *
    ∫ t in Set.Ioi α,
      starRingEnd ℂ (g_cusp ((x₀ : ℂ) + (t : ℂ) * Complex.I)) * ((t + α : ℝ) : ℂ) ^ (-k)

/-- Exact elementary integral `∫_{x₁}^{x₂} (t + a)^{-k} dt = ((x₂ + a)^{1-k} - (x₁ + a)^{1-k}) / (1 - k)`
for `k ≠ 1`, `a > 0`, `0 < x₁ ≤ x₂`. -/
theorem integral_add_cpow_neg_nonOne {k : ℂ} (hk : k ≠ 1) {a x₁ x₂ : ℝ}
    (ha : 0 < a) (hx₁ : 0 < x₁) (hle : x₁ ≤ x₂) :
    ∫ t in x₁..x₂, ((t + a : ℝ) : ℂ) ^ (-k) =
      (((x₂ + a : ℝ) : ℂ) ^ (1 - k) - ((x₁ + a : ℝ) : ℂ) ^ (1 - k)) / (1 - k) := by
  have h1k : (1 : ℂ) - k ≠ 0 := sub_ne_zero.mpr hk.symm
  have hderiv : ∀ t ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun s : ℝ ↦ ((s + a : ℝ) : ℂ) ^ (1 - k) / (1 - k))
        (((t + a : ℝ) : ℂ) ^ (-k)) t := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have hpos : 0 < t + a := by linarith [ht.1]
    have hsl : ((t + a : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hpos))
    have hlin : HasDerivAt (fun s : ℝ ↦ ((s + a : ℝ) : ℂ)) (1 : ℂ) t := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const (a : ℂ)
      have hfun : (fun s : ℝ ↦ ((s + a : ℝ) : ℂ)) = fun s : ℝ ↦ (Complex.ofRealCLM s) + (a : ℂ) := by
        ext s; simp [Complex.ofRealCLM_apply]
      rw [hfun]; exact h
    have hpow : HasDerivAt (fun s : ℝ ↦ ((s + a : ℝ) : ℂ) ^ (1 - k))
        ((1 - k) * ((t + a : ℝ) : ℂ) ^ (-k)) t := by
      have h1 : HasDerivAt (fun z : ℂ ↦ z ^ (1 - k))
          ((1 - k) * ((t + a : ℝ) : ℂ) ^ ((1 - k) - 1)) ((t + a : ℝ) : ℂ) := by
        simpa using (hasDerivAt_id ((t + a : ℝ) : ℂ)).cpow_const (c := 1 - k) hsl
      have h2 := h1.scomp t hlin
      simpa only [Function.comp_def, smul_eq_mul, one_mul, show (1 - k) - 1 = -k by ring] using h2
    have hdiv := hpow.div_const (1 - k)
    convert hdiv using 1
    field_simp [h1k]
  have hcont : ContinuousOn (fun t : ℝ ↦ ((t + a : ℝ) : ℂ) ^ (-k)) (Set.uIcc x₁ x₂) := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have hpos : 0 < t + a := by linarith [ht.1]
    have hsl : ((t + a : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hpos))
    have harg : ContinuousAt (fun s : ℝ ↦ ((s + a : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.add continuousAt_const)
    exact (continuousAt_cpow_const_comp harg hsl).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hftc, sub_div]

/-- Exact elementary integral `∫_{x₁}^{x₂} (t + a)^{-1} dt = log(x₂ + a) - log(x₁ + a)`
for `a > 0`, `0 < x₁ ≤ x₂`. -/
theorem integral_add_cpow_neg_one {a x₁ x₂ : ℝ} (ha : 0 < a) (hx₁ : 0 < x₁) (hle : x₁ ≤ x₂) :
    ∫ t in x₁..x₂, ((t + a : ℝ) : ℂ) ^ (-(1 : ℂ)) =
      ((Real.log (x₂ + a) - Real.log (x₁ + a) : ℝ) : ℂ) := by
  have hderiv : ∀ t ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun s : ℝ ↦ ((Real.log (s + a) : ℝ) : ℂ))
        (((t + a : ℝ) : ℂ) ^ (-(1 : ℂ))) t := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have hpos : 0 < t + a := by linarith [ht.1]
    have hd_real : HasDerivAt (fun s : ℝ ↦ Real.log (s + a)) ((t + a)⁻¹) t := by
      have h1 := ((hasDerivAt_id t).add_const a).log hpos.ne'
      simpa using h1
    have hd_C : HasDerivAt (fun s : ℝ ↦ ((Real.log (s + a) : ℝ) : ℂ)) (((t + a)⁻¹ : ℝ) : ℂ) t := by
      have h1 := Complex.ofRealCLM.hasDerivAt (x := Real.log (t + a)) |>.scomp t hd_real
      simpa [Function.comp_def, Complex.ofRealCLM_apply, Complex.real_smul] using h1
    convert hd_C using 1
    rw [Complex.cpow_neg_one, Complex.ofReal_inv]
  have hcont : ContinuousOn (fun t : ℝ ↦ ((t + a : ℝ) : ℂ) ^ (-(1 : ℂ))) (Set.uIcc x₁ x₂) := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have hpos : 0 < t + a := by linarith [ht.1]
    have hsl : ((t + a : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hpos))
    have harg : ContinuousAt (fun s : ℝ ↦ ((s + a : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.add continuousAt_const)
    exact (continuousAt_cpow_const_comp harg hsl).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hftc, Complex.ofReal_sub]

/-- **Proposition 3.1 (Zero-Mode Miraculous Cancellation, `k ≠ 1`)**:
Combines `h₀^-(γ τ) - (i u / M)^k h₀^-(τ)` with the two zero-mode boundary integrals from the
`y = 1` split, cancelling BOTH `u^{k-1}` and `(u/M²)^{1-k}` identically (`1 - 2^{k-1} 2^{1-k} = 0`)
and leaving `EElemNonOne M k c0 u`! -/
theorem eichler_y1_zero_mode_nonOne {M u : ℝ} (hM : 0 < M) (hu0 : 0 < u) (hu1 : u < 1)
    {k : ℂ} (hk : k ≠ 1) (c0 : ℂ) :
    ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) *
      (((starRingEnd ℂ c0 / (1 - k)) * (((1 / u : ℝ) : ℂ) ^ (1 - k) -
          ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) * (((u / M ^ 2 : ℝ) : ℂ) ^ (1 - k)))) -
        (2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 *
          (∫ y in (1 : ℝ)..(1 / u), ((y + 1 / u : ℝ) : ℂ) ^ (-k)) -
        (2 : ℂ) ^ (k - 1) * ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) * starRingEnd ℂ c0 *
          (∫ t in (u / M ^ 2)..(1 / M ^ 2), ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k))) =
    EElemNonOne M k c0 (u : ℂ) := by
  have h1u_ge : (1 : ℝ) ≤ 1 / u := (one_le_div hu0).mpr hu1.le
  have hα_pos : 0 < u / M ^ 2 := div_pos hu0 (sq_pos_of_pos hM)
  have hα_le : u / M ^ 2 ≤ 1 / M ^ 2 := div_le_div_of_nonneg_right hu1.le (sq_nonneg M)
  rw [integral_add_cpow_neg_nonOne hk (div_pos one_pos hu0) zero_lt_one h1u_ge,
      integral_add_cpow_neg_nonOne hk hα_pos hα_pos hα_le]
  have h2pow : (2 : ℂ) ^ (k - 1) * (2 : ℂ) ^ (1 - k) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show (k - 1) + (1 - k) = 0 by ring, Complex.cpow_zero]
  have h1u2 : (((1 / u + 1 / u : ℝ) : ℂ) ^ (1 - k)) = (2 : ℂ) ^ (1 - k) * ((1 / u : ℝ) : ℂ) ^ (1 - k) := by
    rw [show (1 / u + 1 / u : ℝ) = 2 * (1 / u) by ring,
        ofReal_mul_cpow_of_pos two_pos (div_pos one_pos hu0) (1 - k)]
    simp
  have h1u1 : (((1 + 1 / u : ℝ) : ℂ) ^ (1 - k)) = ((1 + u : ℝ) : ℂ) ^ (1 - k) * (u : ℂ) ^ (-(1 - k)) := by
    rw [show (1 + 1 / u : ℝ) = (1 + u) / u by field_simp [hu0.ne']; ring,
        ofReal_div_cpow_of_pos (by linarith) hu0 (1 - k)]
  have h2α : (((u / M ^ 2 + u / M ^ 2 : ℝ) : ℂ) ^ (1 - k)) =
      (2 : ℂ) ^ (1 - k) * ((u / M ^ 2 : ℝ) : ℂ) ^ (1 - k) := by
    rw [show (u / M ^ 2 + u / M ^ 2 : ℝ) = 2 * (u / M ^ 2) by ring,
        ofReal_mul_cpow_of_pos two_pos hα_pos (1 - k)]
    simp
  have h1α : (((1 / M ^ 2 + u / M ^ 2 : ℝ) : ℂ) ^ (1 - k)) =
      ((1 + u : ℝ) : ℂ) ^ (1 - k) * ((M ^ 2 : ℝ) : ℂ) ^ (-(1 - k)) := by
    rw [show (1 / M ^ 2 + u / M ^ 2 : ℝ) = (1 + u) / M ^ 2 by ring,
        ofReal_div_cpow_of_pos (by linarith) (sq_pos_of_pos hM) (1 - k)]
  have hiuM : (Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k) =
      (Complex.I / (M : ℂ)) ^ (-k) * (u : ℂ) ^ (-k) := by
    have h1 : Complex.I * (u : ℂ) / (M : ℂ) = Complex.I * ((u / M : ℝ) : ℂ) := by push_cast; ring
    have h2 : Complex.I / (M : ℂ) = Complex.I * ((1 / M : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, cpow_I_mul_ofReal_pos (div_pos hu0 hM), cpow_I_mul_ofReal_pos (div_pos one_pos hM),
        show (u / M : ℝ) = (1 / M) * u by ring,
        ofReal_mul_cpow_of_pos (div_pos one_pos hM) hu0 (-k)]
    ring
  have hiuM_cancel : (Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k) * (Complex.I * (u : ℂ) / (M : ℂ)) ^ k = 1 := by
    have hne : Complex.I * (u : ℂ) / (M : ℂ) ≠ 0 :=
      div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hu0.ne'))
        (Complex.ofReal_ne_zero.mpr hM.ne')
    rw [← Complex.cpow_add _ _ hne, neg_add_cancel, Complex.cpow_zero]
  have hu_pow : (u : ℂ) ^ (-k) * (u : ℂ) ^ (-(1 - k)) = (u : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu0.ne'),
        show -k + -(1 - k) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  have hM_pow : ((M ^ 2 : ℝ) : ℂ) ^ (-(1 - k)) = (M : ℂ) ^ (2 * k - 2) := by
    have hMC : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (sq_pos_of_pos hM).ne'),
        Complex.cpow_def_of_ne_zero hMC, ← Complex.ofReal_log (sq_pos_of_pos hM).le,
        ← Complex.ofReal_log hM.le, Real.log_pow]
    congr 1; push_cast; ring
  have h1uC : ((1 + u : ℝ) : ℂ) = 1 + (u : ℂ) := by push_cast; rfl
  rw [h1u2, h1u1, h2α, h1α, hM_pow, h1uC]
  dsimp [EElemNonOne]
  have h1k : (1 : ℂ) - k ≠ 0 := sub_ne_zero.mpr hk.symm
  -- Cancel the two matching `2^{k-1} * 2^{1-k} = 1` pairs and divide by `(i u / M)^k`!
  have hinner :
      starRingEnd ℂ c0 / (1 - k) *
          (((1 / u : ℝ) : ℂ) ^ (1 - k) -
            (Complex.I * (u : ℂ) / (M : ℂ)) ^ k * ((u / M ^ 2 : ℝ) : ℂ) ^ (1 - k)) -
        (2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 *
          (((2 : ℂ) ^ (1 - k) * ((1 / u : ℝ) : ℂ) ^ (1 - k) -
              (1 + (u : ℂ)) ^ (1 - k) * (u : ℂ) ^ (-(1 - k))) / (1 - k)) -
        (2 : ℂ) ^ (k - 1) * (Complex.I * (u : ℂ) / (M : ℂ)) ^ k * starRingEnd ℂ c0 *
          (((1 + (u : ℂ)) ^ (1 - k) * (M : ℂ) ^ (2 * k - 2) -
              (2 : ℂ) ^ (1 - k) * ((u / M ^ 2 : ℝ) : ℂ) ^ (1 - k)) / (1 - k)) =
      ((2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 / (1 - k)) * (1 + (u : ℂ)) ^ (1 - k) *
        ((u : ℂ) ^ (-(1 - k)) - (Complex.I * (u : ℂ) / (M : ℂ)) ^ k * (M : ℂ) ^ (2 * k - 2)) := by
    field_simp [h1k]
    linear_combination
      -(starRingEnd ℂ c0 * ((1 / u : ℝ) : ℂ) ^ (1 - k)) * h2pow +
      (starRingEnd ℂ c0 * (Complex.I * (u : ℂ) / (M : ℂ)) ^ k * ((u / M ^ 2 : ℝ) : ℂ) ^ (1 - k)) * h2pow
  rw [hinner]
  calc (Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k) *
        ((2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 / (1 - k) * (1 + (u : ℂ)) ^ (1 - k) *
          ((u : ℂ) ^ (-(1 - k)) - (Complex.I * (u : ℂ) / (M : ℂ)) ^ k * (M : ℂ) ^ (2 * k - 2)))
      = (2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 / (1 - k) * (1 + (u : ℂ)) ^ (1 - k) *
          (((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) * (u : ℂ) ^ (-(1 - k)) -
            ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k) * (Complex.I * (u : ℂ) / (M : ℂ)) ^ k) *
              (M : ℂ) ^ (2 * k - 2)) := by ring
    _ = (2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 / (1 - k) * (1 + (u : ℂ)) ^ (1 - k) *
          ((Complex.I / (M : ℂ)) ^ (-k) * ((u : ℂ) ^ (-k) * (u : ℂ) ^ (-(1 - k))) -
            1 * (M : ℂ) ^ (2 * k - 2)) := by rw [hiuM_cancel, hiuM]; ring
    _ = _ := by rw [hu_pow, one_mul]

/-- **Proposition 3.1 (Zero-Mode Miraculous Cancellation, `k = 1`)**:
Combines `h₀^-(γ τ) - (i u / M) h₀^-(τ)` with the two weight-`1` log integrals, cancelling
`±log u` inside the `u⁰` bracket identically and leaving `EElemOne M c0 u`! -/
theorem eichler_y1_zero_mode_one {M u : ℝ} (hM : 0 < M) (hu0 : 0 < u) (hu1 : u < 1) (c0 : ℂ) :
    ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-(1 : ℂ))) *
      ((starRingEnd ℂ c0 * (((Real.log (1 / u) : ℝ) : ℂ) -
          (Complex.I * (u : ℂ) / (M : ℂ)) * ((Real.log (u / M ^ 2) : ℝ) : ℂ))) -
        starRingEnd ℂ c0 * (∫ y in (1 : ℝ)..(1 / u), ((y + 1 / u : ℝ) : ℂ) ^ (-(1 : ℂ))) -
        (Complex.I * (u : ℂ) / (M : ℂ)) * starRingEnd ℂ c0 *
          (∫ t in (u / M ^ 2)..(1 / M ^ 2), ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-(1 : ℂ)))) =
    EElemOne M c0 u := by
  have h1u_ge : (1 : ℝ) ≤ 1 / u := (one_le_div hu0).mpr hu1.le
  have hα_pos : 0 < u / M ^ 2 := div_pos hu0 (sq_pos_of_pos hM)
  have hα_le : u / M ^ 2 ≤ 1 / M ^ 2 := div_le_div_of_nonneg_right hu1.le (sq_nonneg M)
  rw [integral_add_cpow_neg_one (div_pos one_pos hu0) zero_lt_one h1u_ge,
      integral_add_cpow_neg_one hα_pos hα_pos hα_le, Complex.cpow_neg_one]
  have hlog1 : Real.log (1 / u) - (Real.log (1 / u + 1 / u) - Real.log (1 + 1 / u)) =
      Real.log ((1 + u) / (2 * u)) := by
    have h1 : (1 / u + 1 / u : ℝ) = 2 / u := by ring
    have h2 : (1 + 1 / u : ℝ) = (1 + u) / u := by field_simp [hu0.ne']; ring
    rw [h1, h2, Real.log_div one_ne_zero hu0.ne', Real.log_div two_ne_zero hu0.ne',
        Real.log_div (by linarith) hu0.ne', Real.log_div (by linarith) (by positivity),
        Real.log_mul two_ne_zero hu0.ne', Real.log_one]
    ring
  have hlog2 : -Real.log (u / M ^ 2) - (Real.log (1 / M ^ 2 + u / M ^ 2) - Real.log (u / M ^ 2 + u / M ^ 2)) =
      Real.log (2 * M ^ 2 / (1 + u)) := by
    have h1 : (1 / M ^ 2 + u / M ^ 2 : ℝ) = (1 + u) / M ^ 2 := by ring
    have h2 : (u / M ^ 2 + u / M ^ 2 : ℝ) = (2 * u) / M ^ 2 := by ring
    have hM2 : M ^ 2 ≠ 0 := (sq_pos_of_pos hM).ne'
    rw [h1, h2, Real.log_div hu0.ne' hM2, Real.log_div (by linarith) hM2,
        Real.log_div (by positivity) hM2, Real.log_mul two_ne_zero hu0.ne',
        Real.log_div (by positivity) (by linarith), Real.log_mul two_ne_zero hM2]
    ring
  have hinv : (Complex.I * (u : ℂ) / (M : ℂ))⁻¹ = (M : ℂ) / (Complex.I * (u : ℂ)) := by
    rw [inv_div]
  have hcancel : (Complex.I * (u : ℂ) / (M : ℂ))⁻¹ * (Complex.I * (u : ℂ) / (M : ℂ)) = 1 :=
    inv_mul_cancel₀ (div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hu0.ne'))
      (Complex.ofReal_ne_zero.mpr hM.ne'))
  dsimp [EElemOne]
  have hlog1C : ((Real.log (1 / u) : ℝ) : ℂ) -
      (((Real.log (1 / u + 1 / u) - Real.log (1 + 1 / u) : ℝ) : ℂ)) =
      ((Real.log ((1 + u) / (2 * u)) : ℝ) : ℂ) := by
    exact_mod_cast hlog1
  have hlog2C : -((Real.log (u / M ^ 2) : ℝ) : ℂ) -
      (((Real.log (1 / M ^ 2 + u / M ^ 2) - Real.log (u / M ^ 2 + u / M ^ 2) : ℝ) : ℂ)) =
      ((Real.log (2 * M ^ 2 / (1 + u)) : ℝ) : ℂ) := by
    exact_mod_cast hlog2
  calc (Complex.I * (u : ℂ) / (M : ℂ))⁻¹ *
        (starRingEnd ℂ c0 *
            (((Real.log (1 / u) : ℝ) : ℂ) -
              Complex.I * (u : ℂ) / (M : ℂ) * ((Real.log (u / M ^ 2) : ℝ) : ℂ)) -
          starRingEnd ℂ c0 * ((Real.log (1 / u + 1 / u) - Real.log (1 + 1 / u) : ℝ) : ℂ) -
          Complex.I * (u : ℂ) / (M : ℂ) * starRingEnd ℂ c0 *
            ((Real.log (1 / M ^ 2 + u / M ^ 2) - Real.log (u / M ^ 2 + u / M ^ 2) : ℝ) : ℂ))
      = starRingEnd ℂ c0 *
          ((Complex.I * (u : ℂ) / (M : ℂ))⁻¹ *
            (((Real.log (1 / u) : ℝ) : ℂ) -
              ((Real.log (1 / u + 1 / u) - Real.log (1 + 1 / u) : ℝ) : ℂ)) +
          ((Complex.I * (u : ℂ) / (M : ℂ))⁻¹ * (Complex.I * (u : ℂ) / (M : ℂ))) *
            (-((Real.log (u / M ^ 2) : ℝ) : ℂ) -
              ((Real.log (1 / M ^ 2 + u / M ^ 2) - Real.log (u / M ^ 2 + u / M ^ 2) : ℝ) : ℂ))) := by ring
    _ = _ := by rw [hcancel, hinv, one_mul, hlog1C, hlog2C]

/-- **Proposition 3.1 (Cusp Integral `y = 1` Split Identity)**:
Combines `h_cusp^-(γ τ(u)) - (i u / M)^k h_cusp^-(τ(u))` via the exact change of variables
`t = 1 / (M² y)` on `[u/M², 1/M²]` into
`-2^{k-1} (i/M)^{-k} Φ_{[1,∞)}(u) + F_hol(u)` plus the two exact zero-mode boundary integrals! -/
theorem eichler_y1_split_cusp {M u : ℝ} (hM : 0 < M) (hu0 : 0 < u) (hu1 : u < 1)
    (k c0 : ℂ) {g_cusp : ℂ → ℂ} {b : ℂ → ℂ}
    (hb_eq : ∀ y : ℝ, 0 < y → b (y : ℂ) = starRingEnd ℂ (g_cusp ((1 / (M : ℂ)) + (y : ℂ) * Complex.I)))
    (hg_inv : ∀ y : ℝ, 0 < y →
      starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + ((1 / (M ^ 2 * y) : ℝ) : ℂ) * Complex.I)) =
        (Complex.I * (M : ℂ) * (y : ℂ)) ^ (2 - k) * b (y : ℂ) +
        (Complex.I * (M : ℂ) * (y : ℂ)) ^ (2 - k) * starRingEnd ℂ c0 - starRingEnd ℂ c0)
    (hg_cont : ContinuousOn (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)))
      (Set.Icc (u / M ^ 2) (1 / M ^ 2)))
    (hb_cont : ContinuousOn (fun y : ℝ ↦ b (y : ℂ)) (Set.Icc 1 (1 / u)))
    (hg_int_hi : IntegrableOn
      (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) *
        ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) (Set.Ioi (1 / M ^ 2)))
    (hb_int_hi : IntegrableOn (fun y : ℝ ↦ b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) (Set.Ioi (1 / u))) :
    ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) *
      (hCuspMinusRay k g_cusp (1 / M) (1 / u) -
        ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) * hCuspMinusRay k g_cusp (-(1 / M)) (u / M ^ 2)) =
    -(2 : ℂ) ^ (k - 1) * (Complex.I / (M : ℂ)) ^ (-k) * PhiReal k b (u : ℂ) +
      FHol M k g_cusp (u : ℂ) +
      ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) *
        (-(2 : ℂ) ^ (k - 1) * starRingEnd ℂ c0 *
            (∫ y in (1 : ℝ)..(1 / u), ((y + 1 / u : ℝ) : ℂ) ^ (-k)) -
          (2 : ℂ) ^ (k - 1) * ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) * starRingEnd ℂ c0 *
            (∫ t in (u / M ^ 2)..(1 / M ^ 2), ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k))) := by
  have hα_pos : 0 < u / M ^ 2 := div_pos hu0 (sq_pos_of_pos hM)
  have hα_le : u / M ^ 2 ≤ 1 / M ^ 2 := div_le_div_of_nonneg_right hu1.le (sq_nonneg M)
  have h1u_ge : (1 : ℝ) ≤ 1 / u := (one_le_div hu0).mpr hu1.le
  -- Split `∫_{α}^∞ = ∫_{α}^{1/M²} + ∫_{1/M²}^∞`!
  have hg_cont_full : ContinuousOn
      (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) *
        ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) (Set.Icc (u / M ^ 2) (1 / M ^ 2)) := by
    refine hg_cont.mul (fun t ht ↦ ?_)
    have hpos : 0 < t + u / M ^ 2 := by linarith [ht.1]
    have hsl : ((t + u / M ^ 2 : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.ofReal_re]; exact hpos))
    exact (continuousAt_cpow_const_comp
      (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.add continuousAt_const)) hsl).continuousWithinAt
  have hg_split :
      (∫ t in Set.Ioi (u / M ^ 2 : ℝ),
          starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) * ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) =
        (∫ t in (u / M ^ 2)..(1 / M ^ 2),
          starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) * ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) +
        (∫ t in Set.Ioi (1 / M ^ 2 : ℝ),
          starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) * ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) :=
    integral_Ioi_eq_interval_add_Ioi hα_le
      (hg_cont_full.intervalIntegrable_of_Icc hα_le) hg_int_hi
  -- Change of variables `t = 1 / (M² y)` on `[u/M², 1/M²]`!
  have hsub_t := intervalIntegral_comp_inv_mul hα_pos hα_le (sq_pos_of_pos hM) hg_cont_full
  have heq_y0 : 1 / (M ^ 2 * (1 / M ^ 2)) = (1 : ℝ) := by field_simp [(sq_pos_of_pos hM).ne']
  have heq_y1 : 1 / (M ^ 2 * (u / M ^ 2)) = 1 / u := by field_simp [(sq_pos_of_pos hM).ne', hu0.ne']
  rw [heq_y0, heq_y1] at hsub_t
  -- Exact complex power cancellation factor along `y ∈ [1, 1/u]`!
  have hfac_eq : ∀ y : ℝ, 0 < y →
      ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) * ((Complex.I * (M : ℂ) * (y : ℂ)) ^ (2 - k)) *
        (((1 / (M ^ 2 * y) + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) * (((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ)) =
      -(((y + 1 / u : ℝ) : ℂ) ^ (-k)) := by
    intro y hy
    have h1 : Complex.I * (u : ℂ) / (M : ℂ) = Complex.I * ((u / M : ℝ) : ℂ) := by push_cast; ring
    have h2 : Complex.I * (M : ℂ) * (y : ℂ) = Complex.I * ((M * y : ℝ) : ℂ) := by push_cast; ring
    have h3 : (1 / (M ^ 2 * y) + u / M ^ 2 : ℝ) = (u / (M ^ 2 * y)) * (y + 1 / u) := by
      field_simp [hM.ne', hy.ne', hu0.ne']; ring
    rw [h1, h2, h3, cpow_I_mul_ofReal_pos (div_pos hu0 hM) k,
        cpow_I_mul_ofReal_pos (mul_pos hM hy) (2 - k),
        ofReal_mul_cpow_of_pos (div_pos hu0 (mul_pos (sq_pos_of_pos hM) hy)) (by positivity) (-k)]
    have hexp_pi : Complex.exp (Complex.I * (Real.pi : ℂ) / 2 * k) *
        Complex.exp (Complex.I * (Real.pi : ℂ) / 2 * (2 - k)) = -1 := by
      rw [← Complex.exp_add, show Complex.I * (Real.pi : ℂ) / 2 * k +
        Complex.I * (Real.pi : ℂ) / 2 * (2 - k) = (Real.pi : ℂ) * Complex.I by ring,
        Complex.exp_pi_mul_I]
    have hreal_fac : ((u / M : ℝ) : ℂ) ^ k * ((M * y : ℝ) : ℂ) ^ (2 - k) *
        ((u / (M ^ 2 * y) : ℝ) : ℂ) ^ (-k) * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ) = 1 := by
      have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
      have hMC : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
      have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have hM2y : ((M ^ 2 * y : ℝ) : ℂ) ^ k = (M : ℂ) ^ k * (M : ℂ) ^ k * (y : ℂ) ^ k := by
        rw [show (M ^ 2 * y : ℝ) = M * (M * y) by ring,
            ofReal_mul_cpow_of_pos hM (mul_pos hM hy) k,
            ofReal_mul_cpow_of_pos hM hy k, mul_assoc]
      rw [ofReal_div_cpow_of_pos hu0 hM k, ofReal_mul_cpow_of_pos hM hy (2 - k),
          ofReal_div_cpow_of_pos hu0 (mul_pos (sq_pos_of_pos hM) hy) (-k), neg_neg, hM2y]
      have hu_c : (u : ℂ) ^ k * (u : ℂ) ^ (-k) = 1 := by
        rw [← Complex.cpow_add _ _ huC, add_neg_cancel, Complex.cpow_zero]
      have hM_c : (M : ℂ) ^ (-k) * (M : ℂ) ^ (2 - k) * ((M : ℂ) ^ k * (M : ℂ) ^ k) = (M : ℂ) ^ 2 := by
        rw [← Complex.cpow_add _ _ hMC, ← Complex.cpow_add _ _ hMC, ← Complex.cpow_add _ _ hMC,
            show -k + (2 - k) + (k + k) = (2 : ℂ) by ring, Complex.cpow_two]
      have hy_c : (y : ℂ) ^ (2 - k) * (y : ℂ) ^ k = (y : ℂ) ^ 2 := by
        rw [← Complex.cpow_add _ _ hyC, show (2 - k) + k = (2 : ℂ) by ring, Complex.cpow_two]
      calc (u : ℂ) ^ k * (M : ℂ) ^ (-k) * ((M : ℂ) ^ (2 - k) * (y : ℂ) ^ (2 - k)) *
            ((u : ℂ) ^ (-k) * ((M : ℂ) ^ k * (M : ℂ) ^ k * (y : ℂ) ^ k)) *
            ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ)
          = ((u : ℂ) ^ k * (u : ℂ) ^ (-k)) *
            ((M : ℂ) ^ (-k) * (M : ℂ) ^ (2 - k) * ((M : ℂ) ^ k * (M : ℂ) ^ k)) *
            ((y : ℂ) ^ (2 - k) * (y : ℂ) ^ k) * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ) := by ring
        _ = 1 * (M : ℂ) ^ 2 * (y : ℂ) ^ 2 * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ) := by
            rw [hu_c, hM_c, hy_c]
        _ = 1 := by push_cast; field_simp [hMC, hyC]
    calc Complex.exp (Complex.I * (Real.pi : ℂ) / 2 * k) * ((u / M : ℝ) : ℂ) ^ k *
          (Complex.exp (Complex.I * (Real.pi : ℂ) / 2 * (2 - k)) * ((M * y : ℝ) : ℂ) ^ (2 - k)) *
          (((u / (M ^ 2 * y) : ℝ) : ℂ) ^ (-k) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) *
          ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ)
        = (Complex.exp (Complex.I * (Real.pi : ℂ) / 2 * k) *
            Complex.exp (Complex.I * (Real.pi : ℂ) / 2 * (2 - k))) *
          (((u / M : ℝ) : ℂ) ^ k * ((M * y : ℝ) : ℂ) ^ (2 - k) *
            ((u / (M ^ 2 * y) : ℝ) : ℂ) ^ (-k) * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ)) *
          ((y + 1 / u : ℝ) : ℂ) ^ (-k) := by ring
      _ = (-1) * 1 * ((y + 1 / u : ℝ) : ℂ) ^ (-k) := by rw [hexp_pi, hreal_fac]
      _ = -((y + 1 / u : ℝ) : ℂ) ^ (-k) := by ring
  -- Apply `hg_inv` to split the lower integral into `b(y)` + two `c0` terms!
  have hcont_y1 : ContinuousOn (fun y : ℝ ↦ b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) (Set.Icc 1 (1 / u)) := by
    refine hb_cont.mul (fun y hy ↦ ?_)
    have hsl : ((y + 1 / u : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.ofReal_re]; linarith [hy.1, div_pos one_pos hu0]))
    exact (continuousAt_cpow_const_comp
      (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.add continuousAt_const)) hsl).continuousWithinAt
  have hcont_y2 : ContinuousOn (fun y : ℝ ↦ ((y + 1 / u : ℝ) : ℂ) ^ (-k)) (Set.Icc 1 (1 / u)) := fun y hy ↦ by
    have hsl : ((y + 1 / u : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.ofReal_re]; linarith [hy.1, div_pos one_pos hu0]))
    exact (continuousAt_cpow_const_comp
      (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.add continuousAt_const)) hsl).continuousWithinAt
  have hcont_y3 : ContinuousOn (fun y : ℝ ↦
      ((1 / (M ^ 2 * y) + u / M ^ 2 : ℝ) : ℂ) ^ (-k) * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ)) (Set.Icc 1 (1 / u)) := by
    intro y hy
    have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
    have h1 : ContinuousWithinAt (fun s : ℝ ↦ ((1 / (M ^ 2 * s) + u / M ^ 2 : ℝ) : ℂ) ^ (-k))
        (Set.Icc 1 (1 / u)) y := by
      have hsl : ((1 / (M ^ 2 * y) + u / M ^ 2 : ℝ) : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.ofReal_re]; positivity))
      exact (continuousAt_cpow_const_comp
        (Complex.continuous_ofReal.continuousAt.comp
          ((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
            (mul_pos (sq_pos_of_pos hM) hy_pos).ne').add continuousAt_const)) hsl).continuousWithinAt
    have h2 : ContinuousWithinAt (fun s : ℝ ↦ ((1 / (M ^ 2 * s ^ 2) : ℝ) : ℂ)) (Set.Icc 1 (1 / u)) y :=
      (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 2))
          (mul_pos (sq_pos_of_pos hM) (sq_pos_of_pos hy_pos)).ne')).continuousWithinAt
    exact h1.mul h2
  have hsub_t_const :
      ∫ t in (u / M ^ 2)..(1 / M ^ 2), ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k) =
      ∫ y in (1 : ℝ)..(1 / u),
        ((1 / (M ^ 2 * y) + u / M ^ 2 : ℝ) : ℂ) ^ (-k) * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ) := by
    have hc : ContinuousOn (fun t : ℝ ↦ ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) (Set.Icc (u / M ^ 2) (1 / M ^ 2)) := by
      intro t ht
      have hsl : ((t + u / M ^ 2 : ℝ) : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.ofReal_re]; linarith [ht.1]))
      exact (continuousAt_cpow_const_comp
        (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.add continuousAt_const)) hsl).continuousWithinAt
    have h := intervalIntegral_comp_inv_mul hα_pos hα_le (sq_pos_of_pos hM) hc
    rwa [heq_y0, heq_y1] at h
  have hlow_eq :
      ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) *
        (∫ t in (u / M ^ 2)..(1 / M ^ 2),
          starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) * ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) =
      -(∫ y in (1 : ℝ)..(1 / u), b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) -
      starRingEnd ℂ c0 * (∫ y in (1 : ℝ)..(1 / u), ((y + 1 / u : ℝ) : ℂ) ^ (-k)) -
      ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) * starRingEnd ℂ c0 *
        (∫ t in (u / M ^ 2)..(1 / M ^ 2), ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) := by
    rw [hsub_t, hsub_t_const, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    have hi1_raw : IntervalIntegrable (fun y : ℝ ↦ b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) volume 1 (1 / u) :=
      hcont_y1.intervalIntegrable_of_Icc h1u_ge
    have hi1 : IntervalIntegrable (fun y : ℝ ↦ -(b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k))) volume 1 (1 / u) :=
      hi1_raw.neg
    have hi2_raw : IntervalIntegrable (fun y : ℝ ↦ ((y + 1 / u : ℝ) : ℂ) ^ (-k)) volume 1 (1 / u) :=
      hcont_y2.intervalIntegrable_of_Icc h1u_ge
    have hi2 : IntervalIntegrable (fun y : ℝ ↦ starRingEnd ℂ c0 * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) volume 1 (1 / u) :=
      hi2_raw.const_mul _
    have hi3_raw : IntervalIntegrable (fun y : ℝ ↦
        ((1 / (M ^ 2 * y) + u / M ^ 2 : ℝ) : ℂ) ^ (-k) * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ))
        volume 1 (1 / u) :=
      hcont_y3.intervalIntegrable_of_Icc h1u_ge
    have hi3 : IntervalIntegrable (fun y : ℝ ↦
        (Complex.I * (u : ℂ) / (M : ℂ)) ^ k * starRingEnd ℂ c0 *
          (((1 / (M ^ 2 * y) + u / M ^ 2 : ℝ) : ℂ) ^ (-k) * ((1 / (M ^ 2 * y ^ 2) : ℝ) : ℂ)))
        volume 1 (1 / u) :=
      hi3_raw.const_mul _
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub hi1 hi2,
        ← intervalIntegral.integral_sub (hi1.sub hi2) hi3]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le h1u_ge] at hy
    have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
    dsimp only
    rw [hg_inv y hy_pos]
    have hfac := hfac_eq y hy_pos
    linear_combination (b (y : ℂ) + starRingEnd ℂ c0) * hfac
  -- Combine `∫_1^{1/u} + ∫_{1/u}^∞ = ∫_1^∞`!
  have hb_combine :
      (∫ y in (1 : ℝ)..(1 / u), b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) +
      (∫ y in Set.Ioi (1 / u : ℝ), b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) =
      ∫ y in Set.Ioi (1 : ℝ), b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k) :=
    (integral_Ioi_eq_interval_add_Ioi h1u_ge (hcont_y1.intervalIntegrable_of_Icc h1u_ge) hb_int_hi).symm
  -- Rewrite `∫_1^∞ b(y) (y + 1/u)^{-k} dy` via `(i u / M)^{-k} (y + 1/u)^{-k} = (i / M)^{-k} (1 + u y)^{-k}`!
  have hphi_scale :
      ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) *
        (∫ y in Set.Ioi (1 : ℝ), b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) =
      (Complex.I / (M : ℂ)) ^ (-k) * PhiReal k b (u : ℂ) := by
    dsimp [PhiReal]
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy_pos : 0 < y := lt_trans zero_lt_one (Set.mem_Ioi.mp hy)
    have hiuM : (Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k) =
        (Complex.I / (M : ℂ)) ^ (-k) * (u : ℂ) ^ (-k) := by
      have h1 : Complex.I * (u : ℂ) / (M : ℂ) = Complex.I * ((u / M : ℝ) : ℂ) := by push_cast; ring
      have h2 : Complex.I / (M : ℂ) = Complex.I * ((1 / M : ℝ) : ℂ) := by push_cast; ring
      rw [h1, h2, cpow_I_mul_ofReal_pos (div_pos hu0 hM), cpow_I_mul_ofReal_pos (div_pos one_pos hM),
          show (u / M : ℝ) = (1 / M) * u by ring,
          ofReal_mul_cpow_of_pos (div_pos one_pos hM) hu0 (-k)]
      ring
    have h1uy : (u : ℂ) ^ (-k) * ((y + 1 / u : ℝ) : ℂ) ^ (-k) = (1 + (u : ℂ) * (y : ℂ)) ^ (-k) := by
      rw [← ofReal_mul_cpow_of_pos hu0 (by positivity) (-k)]
      congr 1; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hu0.ne']; ring
    rw [hiuM]
    linear_combination (Complex.I / (M : ℂ)) ^ (-k) * b (y : ℂ) * h1uy
  -- Match `hCuspMinusRay k g_cusp (1/M) (1/u)` with `b(y)` and `FHol`!
  have hcusp_gamma : hCuspMinusRay k g_cusp (1 / M) (1 / u) =
      -(2 : ℂ) ^ (k - 1) * ∫ y in Set.Ioi (1 / u : ℝ), b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k) := by
    dsimp [hCuspMinusRay]; congr 1
    apply setIntegral_congr_fun measurableSet_Ioi; intro y hy
    have hy_pos : 0 < y := lt_trans (div_pos one_pos hu0) (Set.mem_Ioi.mp hy)
    dsimp only; rw [hb_eq y hy_pos]; push_cast; rfl
  have hFhol_eq : FHol M k g_cusp (u : ℂ) =
      (2 : ℂ) ^ (k - 1) * ∫ t in Set.Ioi (1 / M ^ 2 : ℝ),
        starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) * ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k) := by
    dsimp [FHol]; congr 1
    apply setIntegral_congr_fun measurableSet_Ioi; intro t _; push_cast; rfl
  have hcusp_tau : hCuspMinusRay k g_cusp (-(1 / M)) (u / M ^ 2) =
      -(2 : ℂ) ^ (k - 1) * ∫ t in Set.Ioi (u / M ^ 2 : ℝ),
        starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) * ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k) := by
    dsimp [hCuspMinusRay]; congr 1
    apply setIntegral_congr_fun measurableSet_Ioi; intro t _; push_cast; rfl
  have hiuM_cancel : (Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k) * (Complex.I * (u : ℂ) / (M : ℂ)) ^ k = 1 := by
    have hne : Complex.I * (u : ℂ) / (M : ℂ) ≠ 0 :=
      div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hu0.ne'))
        (Complex.ofReal_ne_zero.mpr hM.ne')
    rw [← Complex.cpow_add _ _ hne, neg_add_cancel, Complex.cpow_zero]
  rw [hcusp_gamma, hcusp_tau, hg_split, hFhol_eq]
  linear_combination
    (2 : ℂ) ^ (k - 1) * ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) * hlow_eq -
    (2 : ℂ) ^ (k - 1) * ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) * hb_combine -
    (2 : ℂ) ^ (k - 1) * hphi_scale +
    (2 : ℂ) ^ (k - 1) * (∫ t in Set.Ioi (1 / M ^ 2 : ℝ),
      starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) * ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) *
      hiuM_cancel

/-- **Proposition 3.1 (Complete `y = 1` Eichler Split, `k ≠ 1`)**:
Combines `eichler_y1_split_cusp` with `eichler_y1_zero_mode_nonOne` into the exact closed form
`eq:y1-split`:
`(i u / M)^{-k} * ((h_cusp^-(γ τ) + h_0^-(γ τ)) - (i u / M)^k (h_cusp^-(τ) + h_0^-(τ)))`
`= -2^{k-1} (i/M)^{-k} Φ_{[1,∞)}(u) + F_hol(u) + EElemNonOne M k c0 u`! -/
theorem eichler_y1_split_nonOne {M u : ℝ} (hM : 0 < M) (hu0 : 0 < u) (hu1 : u < 1)
    {k : ℂ} (hk : k ≠ 1) (c0 : ℂ) {g_cusp : ℂ → ℂ} {b : ℂ → ℂ}
    (hb_eq : ∀ y : ℝ, 0 < y → b (y : ℂ) = starRingEnd ℂ (g_cusp ((1 / (M : ℂ)) + (y : ℂ) * Complex.I)))
    (hg_inv : ∀ y : ℝ, 0 < y →
      starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + ((1 / (M ^ 2 * y) : ℝ) : ℂ) * Complex.I)) =
        (Complex.I * (M : ℂ) * (y : ℂ)) ^ (2 - k) * b (y : ℂ) +
        (Complex.I * (M : ℂ) * (y : ℂ)) ^ (2 - k) * starRingEnd ℂ c0 - starRingEnd ℂ c0)
    (hg_cont : ContinuousOn (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)))
      (Set.Icc (u / M ^ 2) (1 / M ^ 2)))
    (hb_cont : ContinuousOn (fun y : ℝ ↦ b (y : ℂ)) (Set.Icc 1 (1 / u)))
    (hg_int_hi : IntegrableOn
      (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) *
        ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-k)) (Set.Ioi (1 / M ^ 2 : ℝ)))
    (hb_int_hi : IntegrableOn (fun y : ℝ ↦ b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-k)) (Set.Ioi (1 / u : ℝ))) :
    ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-k)) *
      ((hCuspMinusRay k g_cusp (1 / M) (1 / u) +
          (starRingEnd ℂ c0 / (1 - k)) * ((1 / u : ℝ) : ℂ) ^ (1 - k)) -
        ((Complex.I * (u : ℂ) / (M : ℂ)) ^ k) *
          (hCuspMinusRay k g_cusp (-(1 / M)) (u / M ^ 2) +
            (starRingEnd ℂ c0 / (1 - k)) * ((u / M ^ 2 : ℝ) : ℂ) ^ (1 - k))) =
    -(2 : ℂ) ^ (k - 1) * (Complex.I / (M : ℂ)) ^ (-k) * PhiReal k b (u : ℂ) +
      FHol M k g_cusp (u : ℂ) + EElemNonOne M k c0 (u : ℂ) := by
  have hcusp := eichler_y1_split_cusp hM hu0 hu1 k c0 hb_eq hg_inv hg_cont hb_cont hg_int_hi hb_int_hi
  have hzero := eichler_y1_zero_mode_nonOne hM hu0 hu1 hk c0
  linear_combination hcusp + hzero

/-- **Proposition 3.1 (Complete `y = 1` Eichler Split, `k = 1`)**:
Combines `eichler_y1_split_cusp` with `eichler_y1_zero_mode_one` into the exact closed form
`eq:y1-split` at weight `k = 1`, with exact miraculous cancellation of `±log u`! -/
theorem eichler_y1_split_one {M u : ℝ} (hM : 0 < M) (hu0 : 0 < u) (hu1 : u < 1)
    (c0 : ℂ) {g_cusp : ℂ → ℂ} {b : ℂ → ℂ}
    (hb_eq : ∀ y : ℝ, 0 < y → b (y : ℂ) = starRingEnd ℂ (g_cusp ((1 / (M : ℂ)) + (y : ℂ) * Complex.I)))
    (hg_inv : ∀ y : ℝ, 0 < y →
      starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + ((1 / (M ^ 2 * y) : ℝ) : ℂ) * Complex.I)) =
        (Complex.I * (M : ℂ) * (y : ℂ)) ^ (2 - (1 : ℂ)) * b (y : ℂ) +
        (Complex.I * (M : ℂ) * (y : ℂ)) ^ (2 - (1 : ℂ)) * starRingEnd ℂ c0 - starRingEnd ℂ c0)
    (hg_cont : ContinuousOn (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)))
      (Set.Icc (u / M ^ 2) (1 / M ^ 2)))
    (hb_cont : ContinuousOn (fun y : ℝ ↦ b (y : ℂ)) (Set.Icc 1 (1 / u)))
    (hg_int_hi : IntegrableOn
      (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) *
        ((t + u / M ^ 2 : ℝ) : ℂ) ^ (-(1 : ℂ))) (Set.Ioi (1 / M ^ 2 : ℝ)))
    (hb_int_hi : IntegrableOn (fun y : ℝ ↦ b (y : ℂ) * ((y + 1 / u : ℝ) : ℂ) ^ (-(1 : ℂ))) (Set.Ioi (1 / u : ℝ))) :
    ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (-(1 : ℂ))) *
      ((hCuspMinusRay 1 g_cusp (1 / M) (1 / u) + starRingEnd ℂ c0 * ((Real.log (1 / u) : ℝ) : ℂ)) -
        ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (1 : ℂ)) *
          (hCuspMinusRay 1 g_cusp (-(1 / M)) (u / M ^ 2) + starRingEnd ℂ c0 * ((Real.log (u / M ^ 2) : ℝ) : ℂ))) =
    -(Complex.I / (M : ℂ)) ^ (-(1 : ℂ)) * PhiReal 1 b (u : ℂ) +
      FHol M 1 g_cusp (u : ℂ) + EElemOne M c0 u := by
  have hcusp := eichler_y1_split_cusp hM hu0 hu1 1 c0 hb_eq hg_inv hg_cont hb_cont hg_int_hi hb_int_hi
  have hzero := eichler_y1_zero_mode_one hM hu0 hu1 c0
  have h20 : (2 : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
  have hp1 : ((Complex.I * (u : ℂ) / (M : ℂ)) ^ (1 : ℂ)) = Complex.I * (u : ℂ) / (M : ℂ) :=
    Complex.cpow_one _
  rw [h20, hp1] at hcusp
  rw [hp1]
  linear_combination hcusp + hzero

/-- **Proposition 3.1(b) — Holomorphy of `F_hol` on the Open Unit Disk `𝔻₁`**:
If `t ↦ conj(g_cusp(-1/M + i t))` is continuous and exponentially decaying (`≤ C exp(-c t)`)
on `t > 1 / M²`, then `FHol M k g_cusp` is holomorphic on `Metric.ball 0 1`! -/
theorem FHol_differentiableOn_ball {M : ℝ} (hM : 0 < M) (k : ℂ) {g_cusp : ℂ → ℂ}
    {C_g c_g : ℝ} (hCg : 0 ≤ C_g) (hcg : 0 < c_g)
    (hg_cont : ContinuousOn (fun t : ℝ ↦ starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)))
      (Set.Ioi (1 / M ^ 2)))
    (hg_bd : ∀ t : ℝ, 1 / M ^ 2 < t →
      ‖starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I))‖ ≤ C_g * Real.exp (-c_g * t)) :
    DifferentiableOn ℂ (FHol M k g_cusp) (Metric.ball (0 : ℂ) 1) := by
  intro u₀ hu₀
  have hu₀_lt : ‖u₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hu₀
  let r : ℝ := (1 + ‖u₀‖) / 2
  have hr_lt1 : r < 1 := by dsimp [r]; linarith
  have hu₀_lt_r : ‖u₀‖ < r := by dsimp [r]; linarith
  let ε : ℝ := (1 - ‖u₀‖) / 2
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  have hball_sub : Metric.ball u₀ ε ⊆ Metric.ball (0 : ℂ) r := by
    intro u hu
    rw [Metric.mem_ball, Complex.dist_eq] at hu
    rw [Metric.mem_ball, dist_zero_right]
    have h1 := norm_sub_norm_le u u₀
    dsimp [r, ε] at *; linarith
  let a : ℝ := (1 - r) / M ^ 2
  have ha_pos : 0 < a := div_pos (by linarith) (sq_pos_of_pos hM)
  have hsl_lb : ∀ u ∈ Metric.ball (0 : ℂ) r, ∀ t : ℝ, 1 / M ^ 2 < t →
      (t : ℂ) + u / ((M : ℂ) ^ 2) ∈ Complex.slitPlane ∧
      a ≤ ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ ∧
      ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ ≤ t + 1 / M ^ 2 := by
    intro u hu t ht
    have hun : ‖u‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hu
    have hre_u : -r ≤ u.re := by linarith [neg_abs_le u.re, Complex.abs_re_le_norm u]
    have hre_ge : a ≤ ((t : ℂ) + u / ((M : ℂ) ^ 2)).re := by
      have hre : ((t : ℂ) + u / ((M : ℂ) ^ 2)).re = t + u.re / M ^ 2 := by
        rw [show ((M : ℂ) ^ 2) = ((M ^ 2 : ℝ) : ℂ) by push_cast; rfl,
            Complex.add_re, Complex.ofReal_re, Complex.div_ofReal_re]
      rw [hre]; dsimp [a]
      have h1 : (-r) / M ^ 2 ≤ u.re / M ^ 2 := div_le_div_of_nonneg_right hre_u (sq_nonneg M)
      have h2 : (1 - r) / M ^ 2 = 1 / M ^ 2 + (-r) / M ^ 2 := by ring
      linarith
    have hsl : (t : ℂ) + u / ((M : ℂ) ^ 2) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le ha_pos hre_ge))
    have hng : a ≤ ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ := hre_ge.trans (Complex.re_le_norm _)
    have hup : ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ ≤ t + 1 / M ^ 2 := by
      calc ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ ≤ ‖(t : ℂ)‖ + ‖u / ((M : ℂ) ^ 2)‖ := norm_add_le _ _
        _ = t + ‖u‖ / M ^ 2 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans (by positivity) ht),
                norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
        _ ≤ t + 1 / M ^ 2 := by
            have := div_le_div_of_nonneg_right (hun.le.trans hr_lt1.le) (sq_nonneg M); linarith
    exact ⟨hsl, hng, hup⟩
  -- Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `Metric.ball u₀ ε`!
  let F : ℂ → ℝ → ℂ := fun u t ↦
    starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) *
      ((t : ℂ) + u / ((M : ℂ) ^ 2)) ^ (-k)
  let F' : ℂ → ℝ → ℂ := fun u t ↦
    starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I)) *
      (-k * ((t : ℂ) + u / ((M : ℂ) ^ 2)) ^ (-k - 1) * (1 / ((M : ℂ) ^ 2)))
  have hmeas_F : ∀ u ∈ Metric.ball u₀ ε, AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi (1 / M ^ 2))) := by
    intro u hu
    refine (hg_cont.mul (fun t ht ↦ ?_)).aestronglyMeasurable measurableSet_Ioi
    have hsl := (hsl_lb u (hball_sub hu) t (Set.mem_Ioi.mp ht)).1
    exact (continuousAt_cpow_const_comp
      (Complex.continuous_ofReal.continuousAt.add continuousAt_const) hsl).continuousWithinAt
  have hmeas_F' : AEStronglyMeasurable (F' u₀) (volume.restrict (Set.Ioi (1 / M ^ 2))) := by
    refine (hg_cont.mul (fun t ht ↦ ?_)).aestronglyMeasurable measurableSet_Ioi
    have hsl := (hsl_lb u₀ (hball_sub (Metric.mem_ball_self hε_pos)) t (Set.mem_Ioi.mp ht)).1
    exact ((continuousAt_const.mul (continuousAt_cpow_const_comp
      (Complex.continuous_ofReal.continuousAt.add continuousAt_const) hsl)).mul continuousAt_const).continuousWithinAt
  -- Integrability of `t^d * exp(-c_g t)` on `Ioi (1 / M²)`:
  have hint_pow : ∀ d : ℕ, IntegrableOn (fun t : ℝ ↦ t ^ d * Real.exp (-c_g * t)) (Set.Ioi (1 / M ^ 2)) :=
    fun d ↦ (integral_pow_mul_exp_Ioi_le d hcg).1.mono_set (Set.Ioi_subset_Ioi (by positivity))
  -- Common bound on `‖(t + u / M²)^w‖` for `u ∈ ball 0 r`, `t > 1/M²`:
  have hpow_bd : ∀ w : ℂ, ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧
      ∀ u ∈ Metric.ball (0 : ℂ) r, ∀ t : ℝ, 1 / M ^ 2 < t →
        ‖((t : ℂ) + u / ((M : ℂ) ^ 2)) ^ w‖ ≤ K * t ^ d := by
    intro w
    by_cases hw : w.re ≤ 0
    · refine ⟨a ^ w.re * Real.exp (|w.im| * Real.pi), 0, by positivity, fun u hu t ht ↦ ?_⟩
      have ⟨hsl, hng, _⟩ := hsl_lb u hu t ht
      have hcp := norm_cpow_le_rpow_mul_exp (w := w) (Complex.slitPlane_ne_zero hsl)
      have hrp := Real.rpow_le_rpow_of_nonpos ha_pos hng hw
      simpa using hcp.trans (mul_le_mul_of_nonneg_right hrp (Real.exp_pos _).le)
    · push Not at hw
      let d : ℕ := Nat.ceil w.re
      refine ⟨(2 ^ w.re * Real.exp (|w.im| * Real.pi)) * (max 1 (M ^ 2)) ^ d, d, by positivity, fun u hu t ht ↦ ?_⟩
      have ⟨hsl, _, hup⟩ := hsl_lb u hu t ht
      have ht_pos : 0 < t := lt_trans (by positivity) ht
      have hup2 : ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ ≤ 2 * t := by linarith
      have hcp := norm_cpow_le_rpow_mul_exp (w := w) (Complex.slitPlane_ne_zero hsl)
      have hrp : ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ ^ w.re ≤ 2 ^ w.re * (max 1 (M ^ 2) * t) ^ d := by
        have h1 : ‖(t : ℂ) + u / ((M : ℂ) ^ 2)‖ ^ w.re ≤ (2 * t) ^ w.re :=
          Real.rpow_le_rpow (norm_nonneg _) hup2 hw.le
        rw [Real.mul_rpow two_pos.le ht_pos.le] at h1
        have hmt1 : 1 ≤ max 1 (M ^ 2) * t := by
          have h1' : M ^ 2 ≤ max 1 (M ^ 2) := le_max_right _ _
          have h2' : 1 ≤ M ^ 2 * t := by rw [div_lt_iff₀ (sq_pos_of_pos hM)] at ht; nlinarith
          nlinarith
        have h2 : t ^ w.re ≤ (max 1 (M ^ 2) * t) ^ w.re :=
          Real.rpow_le_rpow ht_pos.le (le_mul_of_one_le_left ht_pos.le (le_max_left _ _)) hw.le
        have h3 : (max 1 (M ^ 2) * t) ^ w.re ≤ (max 1 (M ^ 2) * t) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmt1 (Nat.le_ceil w.re)
        rw [Real.rpow_natCast] at h3
        exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity))
      rw [mul_pow] at hrp
      calc ‖((t : ℂ) + u / ((M : ℂ) ^ 2)) ^ w‖
          ≤ (2 ^ w.re * ((max 1 (M ^ 2)) ^ d * t ^ d)) * Real.exp (|w.im| * Real.pi) :=
            hcp.trans (mul_le_mul_of_nonneg_right hrp (Real.exp_pos _).le)
        _ = (2 ^ w.re * Real.exp (|w.im| * Real.pi)) * (max 1 (M ^ 2)) ^ d * t ^ d := by ring
  obtain ⟨K₀, d₀, hK₀, hbd0⟩ := hpow_bd (-k)
  obtain ⟨K₁, d₁, hK₁, hbd1⟩ := hpow_bd (-k - 1)
  have hF_int : Integrable (F u₀) (volume.restrict (Set.Ioi (1 / M ^ 2))) := by
    refine ((hint_pow d₀).const_mul (C_g * K₀)).mono' (hmeas_F u₀ (Metric.mem_ball_self hε_pos)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [F]; rw [norm_mul]
    have h1 := hg_bd t (Set.mem_Ioi.mp ht)
    have h2 := hbd0 u₀ (hball_sub (Metric.mem_ball_self hε_pos)) t (Set.mem_Ioi.mp ht)
    calc ‖starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I))‖ * ‖((t : ℂ) + u₀ / ((M : ℂ) ^ 2)) ^ (-k)‖
        ≤ (C_g * Real.exp (-c_g * t)) * (K₀ * t ^ d₀) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C_g * K₀ * (t ^ d₀ * Real.exp (-c_g * t)) := by ring
  let bound : ℝ → ℝ := fun t ↦ (C_g * ‖k‖ * K₁ / M ^ 2) * (t ^ d₁ * Real.exp (-c_g * t))
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi (1 / M ^ 2))) :=
    (hint_pow d₁).const_mul _
  have hbound_ae : ∀ᵐ t ∂volume.restrict (Set.Ioi (1 / M ^ 2)),
      ∀ u ∈ Metric.ball u₀ ε, ‖F' u t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht u hu
    dsimp [F', bound]
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_one, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
    have h1 := hg_bd t (Set.mem_Ioi.mp ht)
    have h2 := hbd1 u (hball_sub hu) t (Set.mem_Ioi.mp ht)
    calc ‖starRingEnd ℂ (g_cusp (-(1 / (M : ℂ)) + (t : ℂ) * Complex.I))‖ *
          (‖k‖ * ‖((t : ℂ) + u / ((M : ℂ) ^ 2)) ^ (-k - 1)‖ * (1 / M ^ 2))
        ≤ (C_g * Real.exp (-c_g * t)) * (‖k‖ * (K₁ * t ^ d₁) * (1 / M ^ 2)) :=
          mul_le_mul h1
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) (by positivity))
            (by positivity) (by positivity)
      _ = (C_g * ‖k‖ * K₁ / M ^ 2) * (t ^ d₁ * Real.exp (-c_g * t)) := by ring
  have hderiv_ae : ∀ᵐ t ∂volume.restrict (Set.Ioi (1 / M ^ 2)),
      ∀ u ∈ Metric.ball u₀ ε, HasDerivAt (fun w ↦ F w t) (F' u t) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht u hu
    have hsl := (hsl_lb u (hball_sub hu) t (Set.mem_Ioi.mp ht)).1
    have hlin : HasDerivAt (fun w : ℂ ↦ (t : ℂ) + w / ((M : ℂ) ^ 2)) (1 / ((M : ℂ) ^ 2)) u := by
      simpa using ((hasDerivAt_id u).div_const ((M : ℂ) ^ 2)).const_add (t : ℂ)
    exact (hlin.cpow_const (c := -k) hsl).const_mul _
  have hhd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds u₀ hε_pos)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds u₀ hε_pos) hmeas_F)
    hF_int hmeas_F' hbound_ae hbound_int hderiv_ae).2
  change DifferentiableWithinAt ℂ (fun y ↦ (2 : ℂ) ^ (k - 1) * ∫ a in Set.Ioi (1 / M ^ 2 : ℝ), F y a) _ _
  exact (hhd.const_mul ((2 : ℂ) ^ (k - 1))).differentiableAt.differentiableWithinAt

/-! ### Section 2: Lemma 4.1 — Uniform Cauchy `q₁`-Tail Bound -/

/-- Elementary `D`-fold Cauchy convolution polynomial growth bound:
if `a : Fin D → ℕ → ℂ` satisfies `‖a i n‖ ≤ K₀ * (n + 1)^A * ρ₁^(-n)` (`0 < ρ₁ < 1`),
then the `D`-fold Cauchy convolution at index `m` is bounded by
`K₀^D * (m + 1)^(D * (A + 1)) * ρ₁^(-m)`! -/
theorem cauchy_product_poly_bound {D A : ℕ} {K₀ ρ₁ : ℝ} (hK₀ : 0 ≤ K₀) (hρ₁ : 0 < ρ₁) :
    ∀ (a : Fin D → ℕ → ℂ),
      (∀ (i : Fin D) (n : ℕ), ‖a i n‖ ≤ K₀ * ((n + 1 : ℕ) : ℝ) ^ A * ρ₁ ^ (-(n : ℤ))) →
      ∀ m : ℕ,
        ‖∑ f ∈ (Finset.univ.pi fun _ : Fin D ↦ Finset.range (m + 1)).filter
            (fun f ↦ ∑ i : Fin D, f i (Finset.mem_univ i) = m),
          ∏ i : Fin D, a i (f i (Finset.mem_univ i))‖ ≤
        K₀ ^ D * ((m + 1 : ℕ) : ℝ) ^ (D * (A + 1)) * ρ₁ ^ (-(m : ℤ)) := by
  intro a ha m
  let S := (Finset.univ.pi fun _ : Fin D ↦ Finset.range (m + 1)).filter
    (fun f ↦ ∑ i : Fin D, f i (Finset.mem_univ i) = m)
  have hcard : (S.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ D := by
    have hsub : S.card ≤ (Finset.univ.pi fun _ : Fin D ↦ Finset.range (m + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_pi] at hsub
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hsub
    exact_mod_cast hsub
  have hterm : ∀ f ∈ S,
      ‖∏ i : Fin D, a i (f i (Finset.mem_univ i))‖ ≤
        K₀ ^ D * ((m + 1 : ℕ) : ℝ) ^ (D * A) * ρ₁ ^ (-(m : ℤ)) := by
    intro f hf
    have hf_mem := (Finset.mem_filter.mp hf).1
    have hf_sum : ∑ i : Fin D, f i (Finset.mem_univ i) = m := (Finset.mem_filter.mp hf).2
    rw [norm_prod]
    have hprod_le : ∏ i : Fin D, ‖a i (f i (Finset.mem_univ i))‖ ≤
        ∏ i : Fin D, (K₀ * ((m + 1 : ℕ) : ℝ) ^ A * ρ₁ ^ (-((f i (Finset.mem_univ i) : ℤ)))) := by
      gcongr with i _
      have hfi_le : f i (Finset.mem_univ i) ≤ m :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_pi.mp hf_mem i (Finset.mem_univ i)))
      have h1 := ha i (f i (Finset.mem_univ i))
      have h2 : ((f i (Finset.mem_univ i) + 1 : ℕ) : ℝ) ^ A ≤ ((m + 1 : ℕ) : ℝ) ^ A :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hfi_le 1) A
      exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK₀)
        (zpow_nonneg hρ₁.le _))
    refine hprod_le.trans_eq ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm A D]
    congr 1
    have hprod_zpow : ∀ (s : Finset (Fin D)) (e : Fin D → ℤ),
        ∏ i ∈ s, ρ₁ ^ (e i) = ρ₁ ^ (∑ i ∈ s, e i) := by
      intro s e
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hρ₁.ne']
    rw [hprod_zpow]
    congr 1
    rw [Finset.sum_neg_distrib]
    congr 1
    exact_mod_cast hf_sum
  calc ‖∑ f ∈ S, ∏ i : Fin D, a i (f i (Finset.mem_univ i))‖
      ≤ ∑ f ∈ S, ‖∏ i : Fin D, a i (f i (Finset.mem_univ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ S, (K₀ ^ D * ((m + 1 : ℕ) : ℝ) ^ (D * A) * ρ₁ ^ (-(m : ℤ))) :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (K₀ ^ D * ((m + 1 : ℕ) : ℝ) ^ (D * A) * ρ₁ ^ (-(m : ℤ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ D * (K₀ ^ D * ((m + 1 : ℕ) : ℝ) ^ (D * A) * ρ₁ ^ (-(m : ℤ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K₀ ^ D * ((m + 1 : ℕ) : ℝ) ^ (D * (A + 1)) * ρ₁ ^ (-(m : ℤ)) := by
        rw [show D * (A + 1) = D + D * A by ring, pow_add]; ring

/-- Elementary helper: `(t + c)^A * r^t` is summable for any `c ≥ 0`, `A : ℕ`, `0 ≤ r < 1`. -/
theorem summable_poly_mul_geom {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) (A : ℕ) :
    Summable (fun t : ℕ ↦ ((t : ℝ) + c) ^ A * r ^ t) := by
  by_cases hr_zero : r = 0
  · subst hr_zero
    refine (summable_nat_add_iff 1).mp ?_
    simp [zero_pow (Nat.succ_ne_zero _)]
  · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_zero)
    let r' : ℝ := (1 + r) / 2
    have hr'_lt1 : r' < 1 := by dsimp [r']; linarith
    have hr'_pos : 0 < r' := by dsimp [r']; linarith
    have hratio : 1 < r' / r := (one_lt_div hr_pos).mpr (by dsimp [r']; linarith)
    have htend : Tendsto (fun t : ℕ ↦ ((t : ℝ) ^ A) / (r' / r) ^ t) atTop (𝓝 0) :=
      tendsto_pow_const_div_const_pow_of_one_lt A hratio
    have hshift : Tendsto (fun t : ℕ ↦ (((t : ℝ) + c) ^ A) / (r' / r) ^ t) atTop (𝓝 0) := by
      -- Compare `(t + c)^A ≤ (2 * t)^A = 2^A * t^A` for `t ≥ c`!
      refine squeeze_zero_norm' ?_ (htend.const_mul ((2 : ℝ) ^ A) |>.trans (by rw [mul_zero]))
      filter_upwards [Filter.eventually_ge_atTop (Nat.ceil c)] with t ht
      have hct : c ≤ (t : ℝ) := (Nat.le_ceil c).trans (by exact_mod_cast ht)
      rw [Real.norm_of_nonneg (by positivity)]
      calc ((t : ℝ) + c) ^ A / (r' / r) ^ t
          ≤ (2 * (t : ℝ)) ^ A / (r' / r) ^ t := by
            gcongr; linarith
        _ = 2 ^ A * ((t : ℝ) ^ A / (r' / r) ^ t) := by rw [mul_pow]; ring
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hshift) 1 zero_lt_one
    refine (summable_nat_add_iff N).mp ?_
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      ((summable_nat_add_iff N).mpr (summable_geometric_of_lt_one hr'_pos.le hr'_lt1))
    have hk := hN (k + N) (Nat.le_add_left N k)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hk
    have hrr : r ^ (k + N) = r' ^ (k + N) / (r' / r) ^ (k + N) := by
      rw [div_pow r' r (k + N), div_div_eq_mul_div, mul_comm,
          mul_div_cancel_right₀ _ (pow_pos hr'_pos _).ne']
    rw [hrr, mul_div_assoc', ← div_mul_eq_mul_div]
    calc (((k + N : ℕ) : ℝ) + c) ^ A / (r' / r) ^ (k + N) * r' ^ (k + N)
        ≤ 1 * r' ^ (k + N) := mul_le_mul_of_nonneg_right hk.le (pow_nonneg hr'_pos.le _)
      _ = r' ^ (k + N) := one_mul _

/-- Elementary log-exponential absorption on `(0, u₀]`: for `u₀ ∈ (0, 1]`, `α > 0`, `D : ℕ`,
there exists `K ≥ 0` such that `(1 + |log u|)^D * exp(-α / u) ≤ K` for all `u ∈ (0, u₀]`. -/
theorem pow_log_mul_exp_neg_div_le {u₀ α : ℝ} (_hu₀_pos : 0 < u₀) (hu₀_le : u₀ ≤ 1)
    (hα : 0 < α) (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
      (1 + |Real.log u|) ^ D * Real.exp (-α / u) ≤ K := by
  let K : ℝ := (2 : ℝ) ^ D * ((D.factorial : ℝ) / α ^ D) + 1
  refine ⟨K, by positivity, fun u hu0 hu1 ↦ ?_⟩
  have hu_le1 : u ≤ 1 := hu1.trans hu₀_le
  have hlog_le : |Real.log u| ≤ 1 / u := by
    rw [abs_of_nonpos (Real.log_nonpos hu0.le hu_le1), ← Real.log_inv]
    have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hu0)
    rw [one_div]; linarith
  have h1u : 1 ≤ 1 / u := (one_le_div hu0).mpr hu_le1
  have hbase : 1 + |Real.log u| ≤ 2 / u := by linarith [show 2 / u = 1 / u + 1 / u by ring]
  have hexp_ge : (α / u) ^ D / (D.factorial : ℝ) ≤ Real.exp (α / u) :=
    Real.pow_div_factorial_le_exp (α / u) (by positivity) D
  have hexp_le : Real.exp (-α / u) ≤ (D.factorial : ℝ) / (α / u) ^ D := by
    rw [neg_div, Real.exp_neg]
    have hpos_lhs : 0 < (α / u) ^ D / (D.factorial : ℝ) := by positivity
    calc (Real.exp (α / u))⁻¹ ≤ ((α / u) ^ D / (D.factorial : ℝ))⁻¹ :=
          inv_anti₀ hpos_lhs hexp_ge
      _ = (D.factorial : ℝ) / (α / u) ^ D := by rw [inv_div]
  calc (1 + |Real.log u|) ^ D * Real.exp (-α / u)
      ≤ (2 / u) ^ D * ((D.factorial : ℝ) / (α / u) ^ D) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hbase D) hexp_le (Real.exp_pos _).le (by positivity)
    _ = (2 : ℝ) ^ D * ((D.factorial : ℝ) / α ^ D) := by
        rw [div_pow, div_pow]
        field_simp [hu0.ne', hα.ne']
    _ ≤ K := by dsimp [K]; linarith

/-- **Lemma 4.1 — Uniform Cauchy `q₁`-Tail Bound with Arbitrary Poles at `i ∞`**:
For any `u₀ ∈ (0, 1/2]`, `L ≥ 1`, pole floor `N_shift : ℤ`, `ρ₁ := exp(-π / (L u₀))`,
and coefficients `C : ℤ → ℝ → ℂ` obeying
`‖C m u‖ ≤ K₂ * ((m - N_shift).toNat + 1)^A * (1 + |log u|)^D * ρ₁^{-m}` on `u ∈ (0, u₀]`,
for EVERY integer `r₀ ≥ N_shift` there exists `K₁ > 0` (independent of `u`) such that for
ALL `u ∈ (0, u₀ / 2]`, the tail series converges and satisfies
`‖∑' t : ℕ, C (r₀ + t + 1) u * (exp(-2π / (L u)))^(t + 1)‖ ≤ K₁ * exp(-π / (L u))`! -/
theorem cauchy_q1_tail_bound {u₀ L : ℝ} (hu₀_pos : 0 < u₀) (hu₀_le : u₀ ≤ 1 / 2) (hL : 1 ≤ L)
    {N_shift : ℤ} {K₂ : ℝ} (hK₂ : 0 ≤ K₂) (A D : ℕ)
    {C : ℤ → ℝ → ℂ}
    (hC_bd : ∀ m : ℤ, N_shift ≤ m → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      ‖C m u‖ ≤ K₂ * (((m - N_shift).toNat + 1 : ℕ) : ℝ) ^ A * (1 + |Real.log u|) ^ D *
        (Real.exp (-Real.pi / (L * u₀))) ^ (-m))
    (r₀ : ℤ) (hr₀ : N_shift ≤ r₀) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ / 2 →
      Summable (fun t : ℕ ↦
        C (r₀ + ((t + 1 : ℕ) : ℤ)) u * ((Real.exp (-2 * Real.pi / (L * u))) ^ (t + 1) : ℂ)) ∧
      ‖∑' t : ℕ, C (r₀ + ((t + 1 : ℕ) : ℤ)) u *
          ((Real.exp (-2 * Real.pi / (L * u))) ^ (t + 1) : ℂ)‖ ≤
        K₁ * Real.exp (-Real.pi / (L * u)) := by
  let ρ₁ : ℝ := Real.exp (-Real.pi / (L * u₀))
  have hL_pos : 0 < L := by linarith
  have hρ₁_pos : 0 < ρ₁ := Real.exp_pos _
  have hρ₁_lt1 : ρ₁ < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (by positivity))
  have hρ₁3_lt1 : ρ₁ ^ 3 < 1 := pow_lt_one₀ hρ₁_pos.le hρ₁_lt1 (by decide)
  let c₀ : ℝ := ((r₀ - N_shift).toNat + 2 : ℕ)
  have hsum_dom : Summable (fun t : ℕ ↦ ((t : ℝ) + c₀) ^ A * (ρ₁ ^ 3) ^ t) :=
    summable_poly_mul_geom (by positivity) (pow_nonneg hρ₁_pos.le 3) hρ₁3_lt1 A
  let S_dom : ℝ := ∑' t : ℕ, ((t : ℝ) + c₀) ^ A * (ρ₁ ^ 3) ^ t
  have hS_nn : 0 ≤ S_dom := tsum_nonneg fun _ ↦ by positivity
  obtain ⟨K_log, hK_log_pos, hlog_bd⟩ :=
    pow_log_mul_exp_neg_div_le (u₀ := u₀ / 2) (by linarith) (by linarith) (div_pos Real.pi_pos hL_pos) D
  let K₁ : ℝ := K₂ * ρ₁ ^ (-r₀ - 1) * S_dom * K_log + 1
  refine ⟨K₁, by positivity, fun u hu0 hu1 ↦ ?_⟩
  let q : ℝ := Real.exp (-2 * Real.pi / (L * u))
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_div_le : q / ρ₁ ≤ ρ₁ ^ 3 := by
    dsimp [q, ρ₁]
    rw [← Real.exp_sub, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : 2 / u₀ ≤ 1 / u := by
      rw [div_le_div_iff₀ hu₀_pos hu0]; linarith
    have h2 : 4 * Real.pi / (L * u₀) ≤ 2 * Real.pi / (L * u) := by
      have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * Real.pi / L by positivity)
      calc 4 * Real.pi / (L * u₀) = (2 * Real.pi / L) * (2 / u₀) := by ring
        _ ≤ (2 * Real.pi / L) * (1 / u) := hmul
        _ = 2 * Real.pi / (L * u) := by ring
    push_cast; linarith [show -2 * Real.pi / (L * u) - -Real.pi / (L * u₀) =
      -(2 * Real.pi / (L * u)) + Real.pi / (L * u₀) by ring,
      show 3 * (-Real.pi / (L * u₀)) = -(3 * Real.pi / (L * u₀)) by ring,
      show 4 * Real.pi / (L * u₀) = 3 * Real.pi / (L * u₀) + Real.pi / (L * u₀) by ring]
  have hterm_le : ∀ t : ℕ,
      ‖C (r₀ + ((t + 1 : ℕ) : ℤ)) u * ((q ^ (t + 1) : ℝ) : ℂ)‖ ≤
        (K₂ * (1 + |Real.log u|) ^ D * ρ₁ ^ (-r₀ - 1) * q) * (((t : ℝ) + c₀) ^ A * (ρ₁ ^ 3) ^ t) := by
    intro t
    have hm_ge : N_shift ≤ r₀ + ((t + 1 : ℕ) : ℤ) := by omega
    have hbd := hC_bd (r₀ + ((t + 1 : ℕ) : ℤ)) hm_ge u hu0 (by linarith)
    have htoNat : ((r₀ + ((t + 1 : ℕ) : ℤ) - N_shift).toNat + 1 : ℕ) = t + ((r₀ - N_shift).toNat + 2) := by
      omega
    rw [htoNat] at hbd
    have hcast : ((t + ((r₀ - N_shift).toNat + 2) : ℕ) : ℝ) = (t : ℝ) + c₀ := by
      dsimp [c₀]; push_cast; ring
    rw [hcast] at hbd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hq_pos _)]
    have hzpow : ρ₁ ^ (-(r₀ + ((t + 1 : ℕ) : ℤ))) = ρ₁ ^ (-r₀ - 1) * (ρ₁⁻¹) ^ t := by
      rw [show -(r₀ + ((t + 1 : ℕ) : ℤ)) = (-r₀ - 1) + (-(t : ℤ)) by push_cast; ring,
          zpow_add₀ hρ₁_pos.ne', zpow_neg, zpow_natCast, inv_pow]
    have hq_split : (ρ₁⁻¹) ^ t * q ^ (t + 1) = q * (q / ρ₁) ^ t := by
      rw [pow_succ', div_eq_mul_inv, mul_pow]; ring
    calc ‖C (r₀ + ((t + 1 : ℕ) : ℤ)) u‖ * q ^ (t + 1)
        ≤ (K₂ * ((t : ℝ) + c₀) ^ A * (1 + |Real.log u|) ^ D * ρ₁ ^ (-(r₀ + ((t + 1 : ℕ) : ℤ)))) * q ^ (t + 1) :=
          mul_le_mul_of_nonneg_right hbd (pow_nonneg hq_pos.le _)
      _ = (K₂ * (1 + |Real.log u|) ^ D * ρ₁ ^ (-r₀ - 1) * q) * (((t : ℝ) + c₀) ^ A * (q / ρ₁) ^ t) := by
          rw [hzpow]; linear_combination
            (K₂ * ((t : ℝ) + c₀) ^ A * (1 + |Real.log u|) ^ D * ρ₁ ^ (-r₀ - 1)) * hq_split
      _ ≤ (K₂ * (1 + |Real.log u|) ^ D * ρ₁ ^ (-r₀ - 1) * q) * (((t : ℝ) + c₀) ^ A * (ρ₁ ^ 3) ^ t) := by
          gcongr
  have hsum_c : Summable (fun t : ℕ ↦ C (r₀ + ((t + 1 : ℕ) : ℤ)) u * ((q ^ (t + 1) : ℝ) : ℂ)) :=
    Summable.of_norm_bounded (hsum_dom.mul_left _) hterm_le
  have hnorm_le := norm_tsum_le_tsum_norm hsum_c.norm
  have htsum_le : ∑' t : ℕ, ‖C (r₀ + ((t + 1 : ℕ) : ℤ)) u * ((q ^ (t + 1) : ℝ) : ℂ)‖ ≤
      (K₂ * (1 + |Real.log u|) ^ D * ρ₁ ^ (-r₀ - 1) * q) * S_dom := by
    have h1 := Summable.tsum_le_tsum hterm_le hsum_c.norm (hsum_dom.mul_left _)
    rwa [tsum_mul_left] at h1
  have hq_factor : q = Real.exp (-Real.pi / (L * u)) * Real.exp (-Real.pi / (L * u)) := by
    dsimp [q]; rw [← Real.exp_add]; congr 1; ring
  have hlog_u : (1 + |Real.log u|) ^ D * Real.exp (-Real.pi / (L * u)) ≤ K_log := by
    have h := hlog_bd u hu0 hu1
    rwa [show -(Real.pi / L) / u = -Real.pi / (L * u) by ring] at h
  refine ⟨by simpa [q] using hsum_c, ?_⟩
  calc ‖∑' t : ℕ, C (r₀ + ((t + 1 : ℕ) : ℤ)) u * ((Real.exp (-2 * Real.pi / (L * u))) ^ (t + 1) : ℂ)‖
      = ‖∑' t : ℕ, C (r₀ + ((t + 1 : ℕ) : ℤ)) u * ((q ^ (t + 1) : ℝ) : ℂ)‖ := by
        simp [q]
    _ ≤ (K₂ * (1 + |Real.log u|) ^ D * ρ₁ ^ (-r₀ - 1) * q) * S_dom := hnorm_le.trans htsum_le
    _ = (K₂ * ρ₁ ^ (-r₀ - 1) * S_dom) *
          ((1 + |Real.log u|) ^ D * Real.exp (-Real.pi / (L * u))) * Real.exp (-Real.pi / (L * u)) := by
        rw [hq_factor]; ring
    _ ≤ (K₂ * ρ₁ ^ (-r₀ - 1) * S_dom) * K_log * Real.exp (-Real.pi / (L * u)) := by
        gcongr
    _ ≤ K₁ * Real.exp (-Real.pi / (L * u)) := by
        have : K₂ * ρ₁ ^ (-r₀ - 1) * S_dom * K_log ≤ K₁ := by dsimp [K₁]; linarith
        exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-! ### Section 3: Proposition 4.2 — Logarithmic/Puiseux Scale Separation, `q₁`-Induction, & Minimal-Degree Descent -/

/-- Elementary bound `u^{1/2} * |log u|^D ≤ (4 * max D 1)^D * u^{1/4}` for all `u ∈ (0, 1]`. -/
private lemma sqrt_mul_abs_log_pow_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (D : ℕ) :
    u ^ (1 / 2 : ℝ) * |Real.log u| ^ D ≤ ((4 * (max D 1 : ℕ) : ℝ) ^ D) * u ^ (1 / 4 : ℝ) := by
  let M : ℝ := (4 * (max D 1 : ℕ) : ℝ)
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have hlog : |Real.log u| ≤ M * u ^ (-(1 / M)) := by
    rw [abs_of_nonpos (Real.log_nonpos hu0.le hu1)]
    have hpow_pos : 0 < u ^ (-(1 / M)) := Real.rpow_pos_of_pos hu0 _
    have h1 := Real.log_le_sub_one_of_pos hpow_pos
    rw [Real.log_rpow hu0] at h1
    have h2 : -(1 / M) * Real.log u ≤ u ^ (-(1 / M)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left h2 hM_pos.le
    have hlhs : M * (-(1 / M) * Real.log u) = -Real.log u := by field_simp [hM_pos.ne']
    linarith
  have hpowD : |Real.log u| ^ D ≤ M ^ D * u ^ (-(D : ℝ) / M) := by
    calc |Real.log u| ^ D ≤ (M * u ^ (-(1 / M))) ^ D := pow_le_pow_left₀ (abs_nonneg _) hlog D
      _ = M ^ D * (u ^ (-(1 / M))) ^ D := mul_pow _ _ _
      _ = M ^ D * u ^ (-(D : ℝ) / M) := by
          rw [← Real.rpow_natCast (u ^ (-(1 / M))) D, ← Real.rpow_mul hu0.le]
          congr 2; ring
  have hexp_ge : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) + (-(D : ℝ) / M) := by
    have hDM : (D : ℝ) / M ≤ 1 / 4 := by
      rw [div_le_iff₀ hM_pos]
      have hD_le : (D : ℝ) ≤ ((max D 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left D 1
      dsimp [M]; linarith
    rw [neg_div]; linarith
  have hrpow_le : u ^ ((1 / 2 : ℝ) + (-(D : ℝ) / M)) ≤ u ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hexp_ge
  calc u ^ (1 / 2 : ℝ) * |Real.log u| ^ D
      ≤ u ^ (1 / 2 : ℝ) * (M ^ D * u ^ (-(D : ℝ) / M)) :=
        mul_le_mul_of_nonneg_left hpowD (Real.rpow_nonneg hu0.le _)
    _ = M ^ D * (u ^ (1 / 2 : ℝ) * u ^ (-(D : ℝ) / M)) := by ring
    _ = M ^ D * u ^ ((1 / 2 : ℝ) + (-(D : ℝ) / M)) := by rw [← Real.rpow_add hu0]
    _ ≤ M ^ D * u ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hrpow_le (by positivity)

/-- **Proposition 4.2 (Logarithmic/Puiseux Scale Separation Theorem)**:
If `∑_{ε ∈ {0, 1}} ∑_{a = 0}^D u^{ε/2} (log u)^a A_{ε,a}(u) = O(exp(-c / u))` on `(0, u₀)`,
where each `A_{ε,a}` admits a real asymptotic expansion `a_hat ε a ∈ ℂ[[u]]`, then
**EVERY formal power series coefficient `a_hat ε a n = 0` identically**! -/
theorem log_puiseux_scale_separation {u₀ c K : ℝ} (hu₀ : 0 < u₀) (hc : 0 < c) (hK : 0 ≤ K)
    (D : ℕ) (A : Fin 2 → Fin (D + 1) → ℝ → ℂ) (a_hat : Fin 2 → Fin (D + 1) → ℕ → ℂ)
    (hasymp : ∀ (ε : Fin 2) (a : Fin (D + 1)), HasRealAsymp u₀ (A ε a) (a_hat ε a))
    (hbound : ∀ u ∈ Set.Ioo (0 : ℝ) u₀,
      ‖∑ ε : Fin 2, ∑ a : Fin (D + 1),
        (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * A ε a u‖ ≤
        K * Real.exp (-c / u)) :
    ∀ (ε : Fin 2) (a : Fin (D + 1)) (n : ℕ), a_hat ε a n = 0 := by
  by_contra hnot
  push Not at hnot
  obtain ⟨ε₁, a₁, n₁, hne₁⟩ := hnot
  have hex : ∃ v : ℕ, ∃ a : Fin (D + 1),
      a_hat ⟨v % 2, Nat.mod_lt v (by decide)⟩ a (v / 2) ≠ 0 := by
    refine ⟨2 * n₁ + ε₁.val, a₁, ?_⟩
    have hmod : (2 * n₁ + ε₁.val) % 2 = ε₁.val := by have := ε₁.isLt; omega
    have hdiv : (2 * n₁ + ε₁.val) / 2 = n₁ := by have := ε₁.isLt; omega
    have hε : (⟨(2 * n₁ + ε₁.val) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = ε₁ := Fin.ext hmod
    rw [hε, hdiv]; exact hne₁
  classical
  let v₀ : ℕ := Nat.find hex
  have hv₀_spec := Nat.find_spec hex
  have hv₀_min : ∀ (ε : Fin 2) (a : Fin (D + 1)) (n : ℕ), 2 * n + ε.val < v₀ → a_hat ε a n = 0 := by
    intro ε a n hlt
    by_contra hne
    have hlt_spec := Nat.find_min hex hlt
    push Not at hlt_spec
    have hmod : (2 * n + ε.val) % 2 = ε.val := by have := ε.isLt; omega
    have hdiv : (2 * n + ε.val) / 2 = n := by have := ε.isLt; omega
    have hε : (⟨(2 * n + ε.val) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = ε := Fin.ext hmod
    have h0 := hlt_spec a
    rw [hε, hdiv] at h0
    exact hne h0
  let n₀ : ℕ := v₀ / 2
  let ε₀ : Fin 2 := ⟨v₀ % 2, Nat.mod_lt v₀ (by decide)⟩
  have hv₀_eq : 2 * n₀ + ε₀.val = v₀ := by dsimp [n₀, ε₀]; omega
  let S_a : Finset (Fin (D + 1)) := Finset.univ.filter fun a ↦ a_hat ε₀ a n₀ ≠ 0
  have hS_non : S_a.Nonempty := by
    obtain ⟨a, ha⟩ := hv₀_spec
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  let a₀ : Fin (D + 1) := S_a.max' hS_non
  have ha₀_ne : a_hat ε₀ a₀ n₀ ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S_a hS_non)).2
  have ha₀_max : ∀ a : Fin (D + 1), a₀.val < a.val → a_hat ε₀ a n₀ = 0 := by
    intro a hlt
    by_contra hne
    have hle := Finset.le_max' S_a a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩)
    exact absurd hlt (not_lt.mpr hle)
  -- Expand each `A ε a u` to order `N = n₀ + 1`!
  have hrem_ex : ∀ (ε : Fin 2) (a : Fin (D + 1)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Ioo (0 : ℝ) u₀,
        ‖A ε a u - ∑ n ∈ Finset.range (n₀ + 1), a_hat ε a n * (u : ℂ) ^ n‖ ≤ C * u ^ (n₀ + 1) :=
    fun ε a ↦ hasymp ε a (n₀ + 1)
  choose C_rem hC_rem_nn hC_rem_bd using hrem_ex
  let η : ℝ := ‖a_hat ε₀ a₀ n₀‖
  have hη_pos : 0 < η := norm_pos_iff.mpr ha₀_ne
  let L₂ : ℝ := Real.log 2
  have hL₂_pos : 0 < L₂ := Real.log_pos one_lt_two
  -- Total error constants for: (i) lower log powers at `(n₀, ε₀)`, (ii) higher `u`-powers + remainders, (iii) exp RHS!
  let M_log : ℝ := ∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖ / L₂ ^ a₀.val * (1 + L₂ ^ a₀.val)
  let M_hi : ℝ :=
    (∑ ε : Fin 2, ∑ a : Fin (D + 1), ∑ n ∈ Finset.range (n₀ + 1), ‖a_hat ε a n‖) +
    (∑ ε : Fin 2, ∑ a : Fin (D + 1), C_rem ε a)
  let C_logD : ℝ := ((4 * (max D 1 : ℕ) : ℝ) ^ D)
  have hM_hi_nn : 0 ≤ M_hi :=
    add_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ hC_rem_nn _ _)
  -- Choose ONE explicit positive `u` strictly smaller than `min (u₀ / 2) (1 / 2)` making all 3 errors `< η / 4`!
  let B_log : ℝ := (4 * (∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖) + 1) / η
  let u₁ : ℝ := Real.exp (-B_log)
  let u₂ : ℝ := (η * L₂ ^ a₀.val / (4 * (M_hi + 1) * (C_logD + 1))) ^ 4
  let u₃ : ℝ := η * L₂ ^ a₀.val * c ^ (v₀ + 1) / (4 * (K + 1) * ((v₀ + 1).factorial : ℝ))
  let u : ℝ := min (min (u₀ / 2) (1 / 2)) (min u₁ (min u₂ u₃))
  have hu_pos : 0 < u := by
    have h1 : 0 < u₁ := Real.exp_pos _
    have h2 : 0 < u₂ := by dsimp [u₂, C_logD]; positivity
    have h3 : 0 < u₃ := by dsimp [u₃]; positivity
    exact lt_min (lt_min (by linarith) (by norm_num)) (lt_min h1 (lt_min h2 h3))
  have hu_lt_u₀ : u < u₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hu_le_half : u ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hu_le_one : u ≤ 1 := hu_le_half.trans (by norm_num)
  have hu_le_u₁ : u ≤ u₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hu_le_u₂ : u ≤ u₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hu_le_u₃ : u ≤ u₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlog_neg : Real.log u < 0 := Real.log_neg hu_pos (lt_of_le_of_lt hu_le_half (by norm_num))
  have habs_log_ge_L₂ : L₂ ≤ |Real.log u| := by
    rw [abs_of_neg hlog_neg]
    have h1 := Real.log_le_log hu_pos hu_le_half
    rw [one_div, Real.log_inv] at h1
    dsimp [L₂]; linarith
  have habs_log_ge_B : B_log ≤ |Real.log u| := by
    rw [abs_of_neg hlog_neg]
    have h1 := Real.log_le_log hu_pos hu_le_u₁
    rw [Real.log_exp] at h1
    linarith
  have habs_log_pos : 0 < |Real.log u| := lt_of_lt_of_le hL₂_pos habs_log_ge_L₂
  -- Denominator `d = u^{v₀/2} * (log u)^{a₀}` (nonzero!)
  let d : ℂ := (((u ^ ((v₀ : ℝ) / 2) : ℝ) : ℂ)) * ((Real.log u : ℝ) : ℂ) ^ a₀.val
  have hd_norm : ‖d‖ = u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val := by
    dsimp [d]
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]
  have hd_ne : d ≠ 0 := by
    rw [← norm_pos_iff, hd_norm]; positivity
  -- Write `S = ∑ ε a, u^{ε/2} (log u)^a A ε a u`:
  let S : ℂ := ∑ ε : Fin 2, ∑ a : Fin (D + 1),
    (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * A ε a u
  -- Bound (iii): `‖S / d‖ < η / 4`!
  have hS_div_lt : ‖S / d‖ < η / 4 := by
    rw [norm_div, hd_norm]
    have hbd := hbound u ⟨hu_pos, hu_lt_u₀⟩
    have hexp_ge : (c / u) ^ (v₀ + 1) / ((v₀ + 1).factorial : ℝ) ≤ Real.exp (c / u) :=
      Real.pow_div_factorial_le_exp (c / u) (by positivity) (v₀ + 1)
    have hexp_le : Real.exp (-c / u) ≤ ((v₀ + 1).factorial : ℝ) * u ^ (v₀ + 1) / c ^ (v₀ + 1) := by
      rw [neg_div, Real.exp_neg]
      have hpos_l : 0 < (c / u) ^ (v₀ + 1) / ((v₀ + 1).factorial : ℝ) := by positivity
      calc (Real.exp (c / u))⁻¹ ≤ ((c / u) ^ (v₀ + 1) / ((v₀ + 1).factorial : ℝ))⁻¹ :=
            inv_anti₀ hpos_l hexp_ge
        _ = ((v₀ + 1).factorial : ℝ) * u ^ (v₀ + 1) / c ^ (v₀ + 1) := by
            rw [inv_div, div_pow, div_div_eq_mul_div]
    have hu_pow_le : u ^ (v₀ + 1) / u ^ ((v₀ : ℝ) / 2) ≤ u := by
      have h1 : u ^ (v₀ + 1) = u ^ ((v₀ : ℝ) + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
      rw [h1, ← Real.rpow_sub hu_pos]
      have hexp : (1 : ℝ) ≤ (v₀ : ℝ) + 1 - (v₀ : ℝ) / 2 := by
        have : (0 : ℝ) ≤ (v₀ : ℝ) := Nat.cast_nonneg v₀; linarith
      simpa using Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one hexp
    have hden_ge : u ^ ((v₀ : ℝ) / 2) * L₂ ^ a₀.val ≤ u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL₂_pos.le habs_log_ge_L₂ _) (Real.rpow_nonneg hu_pos.le _)
    calc ‖S‖ / (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val)
        ≤ (K * Real.exp (-c / u)) / (u ^ ((v₀ : ℝ) / 2) * L₂ ^ a₀.val) :=
          div_le_div₀ (by positivity) hbd (by positivity) hden_ge
      _ ≤ (K * (((v₀ + 1).factorial : ℝ) * u ^ (v₀ + 1) / c ^ (v₀ + 1))) /
            (u ^ ((v₀ : ℝ) / 2) * L₂ ^ a₀.val) := by
          gcongr
      _ = (K * ((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) *
            (u ^ (v₀ + 1) / u ^ ((v₀ : ℝ) / 2)) := by ring
      _ ≤ (K * ((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) * u := by
          gcongr
      _ ≤ (K * ((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) * u₃ := by
          gcongr
      _ < ((K + 1) * ((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) * u₃ := by
          have hu₃_pos : 0 < u₃ := by dsimp [u₃]; positivity
          have hfac_pos : 0 < ((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1)) := by positivity
          have h1 : K * (((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) <
              (K + 1) * (((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) := by nlinarith
          have h2 := mul_lt_mul_of_pos_right h1 hu₃_pos
          linarith [show K * ((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1)) * u₃ =
              K * (((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) * u₃ by ring,
            show (K + 1) * ((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1)) * u₃ =
              (K + 1) * (((v₀ + 1).factorial : ℝ) / (L₂ ^ a₀.val * c ^ (v₀ + 1))) * u₃ by ring]
      _ = η / 4 := by
          dsimp [u₃]
          have hL₂_ne : L₂ ^ a₀.val ≠ 0 := (pow_pos hL₂_pos _).ne'
          have hc_ne : c ^ (v₀ + 1) ≠ 0 := (pow_pos hc _).ne'
          have hK_ne : K + 1 ≠ 0 := by linarith
          have hf_ne : ((v₀ + 1).factorial : ℝ) ≠ 0 := by positivity
          field_simp [hL₂_ne, hc_ne, hK_ne, hf_ne]
  -- Decompose `S = d * a_hat ε₀ a₀ n₀ + Err_log + Err_hi + Err_rem`!
  let R_rem : Fin 2 → Fin (D + 1) → ℂ := fun ε a ↦
    A ε a u - ∑ n ∈ Finset.range (n₀ + 1), a_hat ε a n * (u : ℂ) ^ n
  let Err_log : ℂ := ∑ a ∈ Finset.univ.filter (fun a : Fin (D + 1) ↦ a.val < a₀.val),
    (((u : ℝ) ^ ((ε₀.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
      (a_hat ε₀ a n₀ * (u : ℂ) ^ n₀)
  let Err_hi : ℂ := ∑ ε : Fin 2, ∑ a : Fin (D + 1),
    ∑ n ∈ (Finset.range (n₀ + 1)).filter (fun n ↦ v₀ < 2 * n + ε.val),
      (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
        (a_hat ε a n * (u : ℂ) ^ n)
  let Err_rem : ℂ := ∑ ε : Fin 2, ∑ a : Fin (D + 1),
    (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * R_rem ε a
  have hS_decomp : S = d * a_hat ε₀ a₀ n₀ + Err_log + Err_hi + Err_rem := by
    have h1 : S = (∑ ε : Fin 2, ∑ a : Fin (D + 1), ∑ n ∈ Finset.range (n₀ + 1),
        (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
          (a_hat ε a n * (u : ℂ) ^ n)) + Err_rem := by
      dsimp [S, Err_rem, R_rem]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro ε _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro a _
      rw [← Finset.mul_sum]; ring
    rw [h1]
    congr 1
    -- Split the inner `n` sum into `2n + ε < v₀` (zero!), `2n + ε = v₀`, and `2n + ε > v₀` (`Err_hi`)!
    have hsplit_n :
        (∑ ε : Fin 2, ∑ a : Fin (D + 1), ∑ n ∈ Finset.range (n₀ + 1),
          (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
            (a_hat ε a n * (u : ℂ) ^ n)) =
        (∑ ε : Fin 2, ∑ a : Fin (D + 1),
          ∑ n ∈ (Finset.range (n₀ + 1)).filter (fun n ↦ 2 * n + ε.val = v₀),
            (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
              (a_hat ε a n * (u : ℂ) ^ n)) + Err_hi := by
      dsimp [Err_hi]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro ε _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro a _
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n₀ + 1)) (fun n ↦ 2 * n + ε.val = v₀)]
      congr 1
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range (n₀ + 1)).filter (fun n ↦ ¬ 2 * n + ε.val = v₀))
        (fun n ↦ v₀ < 2 * n + ε.val)]
      have hlt0 : ∑ n ∈ ((Finset.range (n₀ + 1)).filter (fun n ↦ ¬ 2 * n + ε.val = v₀)).filter
          (fun n ↦ ¬ v₀ < 2 * n + ε.val),
          (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
            (a_hat ε a n * (u : ℂ) ^ n) = 0 := by
        apply Finset.sum_eq_zero; intro n hn
        have h1 := (Finset.mem_filter.mp hn).1
        have hne := (Finset.mem_filter.mp h1).2
        have hle := (Finset.mem_filter.mp hn).2
        rw [hv₀_min ε a n (by omega)]; ring
      rw [hlt0, add_zero]
      apply Finset.sum_congr _ (fun _ _ ↦ rfl)
      ext n; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hn1, _⟩, hgt⟩; exact ⟨hn1, hgt⟩
      · rintro ⟨hn1, hgt⟩; exact ⟨⟨hn1, by omega⟩, hgt⟩
    rw [hsplit_n]; congr 1
    -- In the `2 * n + ε = v₀` sum, ONLY `(ε, n) = (ε₀, n₀)` survives!
    have hdiag :
        (∑ ε : Fin 2, ∑ a : Fin (D + 1),
          ∑ n ∈ (Finset.range (n₀ + 1)).filter (fun n ↦ 2 * n + ε.val = v₀),
            (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
              (a_hat ε a n * (u : ℂ) ^ n)) =
        ∑ a : Fin (D + 1),
          (((u : ℝ) ^ ((ε₀.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
            (a_hat ε₀ a n₀ * (u : ℂ) ^ n₀) := by
      rw [Finset.sum_eq_single ε₀]
      · apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_eq_single n₀]
        · intro n hn hne
          have heq := (Finset.mem_filter.mp hn).2; omega
        · intro hnot
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self n₀), hv₀_eq⟩) hnot
      · intro ε _ hεne
        apply Finset.sum_eq_zero; intro a _
        apply Finset.sum_eq_zero; intro n hn
        have heq := (Finset.mem_filter.mp hn).2
        have hε_lt := ε.isLt; have hε₀_lt := ε₀.isLt
        exfalso; exact hεne (Fin.ext (by omega))
      · intro hnot; exact absurd (Finset.mem_univ ε₀) hnot
    rw [hdiag]
    -- Split `a : Fin (D + 1)` into `a = a₀`, `a < a₀`, and `a > a₀` (zero!)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin (D + 1) ↦ a.val < a₀.val), add_comm]
    congr 1
    rw [Finset.sum_eq_single a₀]
    · have hpow_u : (((u : ℝ) ^ ((ε₀.val : ℝ) / 2) : ℝ) : ℂ) * (u : ℂ) ^ n₀ =
          ((u ^ ((v₀ : ℝ) / 2) : ℝ) : ℂ) := by
        rw [show (u : ℂ) ^ n₀ = ((u ^ n₀ : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_mul,
            ← Real.rpow_natCast u n₀, ← Real.rpow_add hu_pos]
        congr 1; congr 1
        have hv : (v₀ : ℝ) = 2 * (n₀ : ℝ) + (ε₀.val : ℝ) := by exact_mod_cast hv₀_eq.symm
        linarith
      dsimp [d]; linear_combination ((Real.log u : ℝ) : ℂ) ^ a₀.val * a_hat ε₀ a₀ n₀ * hpow_u
    · intro a ha hne
      have hge : ¬ a.val < a₀.val := (Finset.mem_filter.mp ha).2
      have hgt : a₀.val < a.val := lt_of_le_of_ne (not_lt.mp hge) (fun h ↦ hne (Fin.ext h.symm))
      rw [ha₀_max a hgt]; ring
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ a₀, lt_irrefl _⟩) hnot
  -- Bound (i): `‖Err_log / d‖ < η / 4`!
  have hErr_log_lt : ‖Err_log / d‖ < η / 4 := by
    rw [norm_div, hd_norm]
    have hpow_u : u ^ ((ε₀.val : ℝ) / 2) * u ^ n₀ = u ^ ((v₀ : ℝ) / 2) := by
      rw [← Real.rpow_natCast u n₀, ← Real.rpow_add hu_pos]
      congr 1
      have hv : (v₀ : ℝ) = 2 * (n₀ : ℝ) + (ε₀.val : ℝ) := by exact_mod_cast hv₀_eq.symm
      linarith
    have hsum_le : ‖Err_log‖ ≤ (∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖) *
        (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val / |Real.log u|) := by
      dsimp [Err_log]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a ∈ Finset.univ.filter (fun a : Fin (D + 1) ↦ a.val < a₀.val),
              ‖(((u : ℝ) ^ ((ε₀.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val *
                (a_hat ε₀ a n₀ * (u : ℂ) ^ n₀)‖
          ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin (D + 1) ↦ a.val < a₀.val),
              ‖a_hat ε₀ a n₀‖ * (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val / |Real.log u|) := by
            apply Finset.sum_le_sum; intro a ha
            have hlt : a.val < a₀.val := (Finset.mem_filter.mp ha).2
            rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
                Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_pos (Real.rpow_pos_of_pos hu_pos _), abs_of_pos hu_pos]
            have hlog_pow : |Real.log u| ^ a.val ≤ |Real.log u| ^ a₀.val / |Real.log u| := by
              have hge1 : 1 ≤ |Real.log u| := by
                have h1 : 1 ≤ B_log := by
                  dsimp [B_log]; rw [one_le_div hη_pos]
                  have hge : η ≤ ∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖ :=
                    Finset.single_le_sum (f := fun a : Fin (D + 1) ↦ ‖a_hat ε₀ a n₀‖)
                      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a₀)
                  linarith
                exact h1.trans habs_log_ge_B
              rw [le_div_iff₀ habs_log_pos, ← pow_succ]
              exact pow_le_pow_right₀ hge1 (Nat.succ_le_of_lt hlt)
            calc u ^ ((ε₀.val : ℝ) / 2) * |Real.log u| ^ a.val * (‖a_hat ε₀ a n₀‖ * u ^ n₀)
                = ‖a_hat ε₀ a n₀‖ * (u ^ ((ε₀.val : ℝ) / 2) * u ^ n₀) * |Real.log u| ^ a.val := by ring
              _ = ‖a_hat ε₀ a n₀‖ * u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a.val := by rw [hpow_u]
              _ ≤ ‖a_hat ε₀ a n₀‖ * u ^ ((v₀ : ℝ) / 2) * (|Real.log u| ^ a₀.val / |Real.log u|) :=
                  mul_le_mul_of_nonneg_left hlog_pow (by positivity)
              _ = ‖a_hat ε₀ a n₀‖ * (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val / |Real.log u|) := by ring
        _ ≤ ∑ a : Fin (D + 1),
              ‖a_hat ε₀ a n₀‖ * (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val / |Real.log u|) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ ↦ by positivity
        _ = (∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖) *
              (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val / |Real.log u|) := by
            rw [← Finset.sum_mul]
    have hden_pos : 0 < u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val := by positivity
    calc ‖Err_log‖ / (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val)
        ≤ ((∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖) *
            (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val / |Real.log u|)) /
            (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val) :=
          div_le_div_of_nonneg_right hsum_le hden_pos.le
      _ = (∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖) / |Real.log u| := by
          field_simp [hden_pos.ne', habs_log_pos.ne']
      _ ≤ (∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖) / B_log :=
          div_le_div_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (by dsimp [B_log]; positivity)
            habs_log_ge_B
      _ < (∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖ + 1 / 4) / B_log := by
          have hBpos : 0 < B_log := by dsimp [B_log]; positivity
          exact div_lt_div_of_pos_right (by linarith) hBpos
      _ = η / 4 := by
          dsimp [B_log]
          have hnum : 4 * (∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖) + 1 ≠ 0 := by
            have : 0 ≤ ∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
            linarith
          field_simp [hη_pos.ne', hnum]
  -- Bound (ii): `‖(Err_hi + Err_rem) / d‖ < η / 4`!
  have hErr_hi_lt : ‖(Err_hi + Err_rem) / d‖ < η / 4 := by
    rw [norm_div, hd_norm]
    have habs_ge1 : 1 ≤ |Real.log u| := by
      have h1 : 1 ≤ B_log := by
        dsimp [B_log]; rw [one_le_div hη_pos]
        have hge : η ≤ ∑ a : Fin (D + 1), ‖a_hat ε₀ a n₀‖ :=
          Finset.single_le_sum (f := fun a : Fin (D + 1) ↦ ‖a_hat ε₀ a n₀‖)
            (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a₀)
        linarith
      exact h1.trans habs_log_ge_B
    have hhi_le : ‖Err_hi‖ ≤ (∑ ε : Fin 2, ∑ a : Fin (D + 1), ∑ n ∈ Finset.range (n₀ + 1), ‖a_hat ε a n‖) *
        (u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ) * |Real.log u| ^ D) := by
      dsimp [Err_hi]
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ε _ ↦ ?_)
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn ↦ ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity))
      have hgt : v₀ < 2 * n + ε.val := (Finset.mem_filter.mp hn).2
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hu_pos _), abs_of_pos hu_pos]
      have hu_ge : u ^ ((ε.val : ℝ) / 2) * u ^ n ≤ u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast u n, ← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]
        apply Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
        have hnat : (v₀ : ℝ) + 1 ≤ 2 * (n : ℝ) + (ε.val : ℝ) := by exact_mod_cast hgt
        linarith
      have hlog_D : |Real.log u| ^ a.val ≤ |Real.log u| ^ D :=
        pow_le_pow_right₀ habs_ge1 (Nat.lt_succ_iff.mp a.isLt)
      calc u ^ ((ε.val : ℝ) / 2) * |Real.log u| ^ a.val * (‖a_hat ε a n‖ * u ^ n)
          = ‖a_hat ε a n‖ * ((u ^ ((ε.val : ℝ) / 2) * u ^ n) * |Real.log u| ^ a.val) := by ring
        _ ≤ ‖a_hat ε a n‖ * ((u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ)) * |Real.log u| ^ D) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hu_ge hlog_D (by positivity) (by positivity)) (norm_nonneg _)
        _ = ‖a_hat ε a n‖ * (u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ) * |Real.log u| ^ D) := by ring
    have hrem_le : ‖Err_rem‖ ≤ (∑ ε : Fin 2, ∑ a : Fin (D + 1), C_rem ε a) *
        (u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ) * |Real.log u| ^ D) := by
      dsimp [Err_rem]
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ε _ ↦ ?_)
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]
      have hrb := hC_rem_bd ε a u ⟨hu_pos, hu_lt_u₀⟩
      have hu_ge : u ^ ((ε.val : ℝ) / 2) * u ^ (n₀ + 1) ≤ u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast u (n₀ + 1), ← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]
        apply Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
        have hnat : (v₀ : ℝ) + 1 ≤ 2 * ((n₀ + 1 : ℕ) : ℝ) + (ε.val : ℝ) := by
          have : v₀ + 1 ≤ 2 * (n₀ + 1) + ε.val := by omega
          exact_mod_cast this
        linarith
      have hlog_D : |Real.log u| ^ a.val ≤ |Real.log u| ^ D :=
        pow_le_pow_right₀ habs_ge1 (Nat.lt_succ_iff.mp a.isLt)
      calc u ^ ((ε.val : ℝ) / 2) * |Real.log u| ^ a.val * ‖R_rem ε a‖
          ≤ u ^ ((ε.val : ℝ) / 2) * |Real.log u| ^ a.val * (C_rem ε a * u ^ (n₀ + 1)) :=
            mul_le_mul_of_nonneg_left hrb (by positivity)
        _ = C_rem ε a * ((u ^ ((ε.val : ℝ) / 2) * u ^ (n₀ + 1)) * |Real.log u| ^ a.val) := by ring
        _ ≤ C_rem ε a * ((u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ)) * |Real.log u| ^ D) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hu_ge hlog_D (by positivity) (by positivity)) (hC_rem_nn ε a)
        _ = C_rem ε a * (u ^ ((v₀ : ℝ) / 2) * u ^ (1 / 2 : ℝ) * |Real.log u| ^ D) := by ring
    have hcomb : ‖Err_hi + Err_rem‖ ≤
        M_hi * (u ^ ((v₀ : ℝ) / 2) * (C_logD * u ^ (1 / 4 : ℝ))) := by
      calc ‖Err_hi + Err_rem‖ ≤ ‖Err_hi‖ + ‖Err_rem‖ := norm_add_le _ _
        _ ≤ M_hi * (u ^ ((v₀ : ℝ) / 2) * (u ^ (1 / 2 : ℝ) * |Real.log u| ^ D)) := by
            dsimp [M_hi]; linarith
        _ ≤ M_hi * (u ^ ((v₀ : ℝ) / 2) * (C_logD * u ^ (1 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (sqrt_mul_abs_log_pow_le hu_pos hu_le_one D)
                (Real.rpow_nonneg hu_pos.le _)) hM_hi_nn
    have hu14 : u ^ (1 / 4 : ℝ) ≤ η * L₂ ^ a₀.val / (4 * (M_hi + 1) * (C_logD + 1)) := by
      have h1 := Real.rpow_le_rpow hu_pos.le hu_le_u₂ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      dsimp [u₂] at h1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by dsimp [C_logD]; positivity)] at h1
      simpa [show ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 by norm_num] using h1
    have hden_ge : u ^ ((v₀ : ℝ) / 2) * L₂ ^ a₀.val ≤ u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL₂_pos.le habs_log_ge_L₂ _) (Real.rpow_nonneg hu_pos.le _)
    calc ‖Err_hi + Err_rem‖ / (u ^ ((v₀ : ℝ) / 2) * |Real.log u| ^ a₀.val)
        ≤ (M_hi * (u ^ ((v₀ : ℝ) / 2) * (C_logD * u ^ (1 / 4 : ℝ)))) / (u ^ ((v₀ : ℝ) / 2) * L₂ ^ a₀.val) :=
          div_le_div₀ (by positivity) hcomb (by positivity) hden_ge
      _ = (M_hi * C_logD / L₂ ^ a₀.val) * u ^ (1 / 4 : ℝ) := by
          have hu_v0 : u ^ ((v₀ : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hu_pos _).ne'
          field_simp [hu_v0, (pow_pos hL₂_pos _).ne']
      _ ≤ (M_hi * C_logD / L₂ ^ a₀.val) * (η * L₂ ^ a₀.val / (4 * (M_hi + 1) * (C_logD + 1))) := by
          gcongr
      _ < ((M_hi + 1) * (C_logD + 1) / L₂ ^ a₀.val) *
            (η * L₂ ^ a₀.val / (4 * (M_hi + 1) * (C_logD + 1))) := by
          have hC_nn : 0 ≤ C_logD := by dsimp [C_logD]; positivity
          have hfac : 0 < η * L₂ ^ a₀.val / (4 * (M_hi + 1) * (C_logD + 1)) := by positivity
          have hlt1 : M_hi * C_logD < (M_hi + 1) * (C_logD + 1) := by nlinarith
          exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hlt1 (pow_pos hL₂_pos _)) hfac
      _ = η / 4 := by
          have hL_ne : L₂ ^ a₀.val ≠ 0 := (pow_pos hL₂_pos _).ne'
          have hM1 : M_hi + 1 ≠ 0 := by linarith
          have hC1 : C_logD + 1 ≠ 0 := by dsimp [C_logD]; positivity
          field_simp [hL_ne, hM1, hC1]
  -- Final triangle-inequality contradiction: `η = ‖a_hat ε₀ a₀ n₀‖ < 3 η / 4`!
  have hmain_eq : a_hat ε₀ a₀ n₀ = S / d - Err_log / d - (Err_hi + Err_rem) / d := by
    rw [hS_decomp]; field_simp [hd_ne]; ring
  have htri : η ≤ ‖S / d‖ + ‖Err_log / d‖ + ‖(Err_hi + Err_rem) / d‖ := by
    dsimp [η]; rw [hmain_eq]
    calc ‖S / d - Err_log / d - (Err_hi + Err_rem) / d‖
        ≤ ‖S / d - Err_log / d‖ + ‖(Err_hi + Err_rem) / d‖ := norm_sub_le _ _
      _ ≤ ‖S / d‖ + ‖Err_log / d‖ + ‖(Err_hi + Err_rem) / d‖ := by linarith [norm_sub_le (S / d) (Err_log / d)]
  linarith

/-- **`x^{1/2}`-Parity Scale Separation (`D = 0` specialization of `log_puiseux_scale_separation`)**:
Used directly in Proposition 5.3 to decouple integer weights (`k = 1`) from half-integer weights! -/
theorem half_parity_scale_separation {u₀ c K : ℝ} (hu₀ : 0 < u₀) (hc : 0 < c) (hK : 0 ≤ K)
    {A₀ A₁ : ℝ → ℂ} {a₀ a₁ : ℕ → ℂ}
    (hA₀ : HasRealAsymp u₀ A₀ a₀) (hA₁ : HasRealAsymp u₀ A₁ a₁)
    (hbound : ∀ u ∈ Set.Ioo (0 : ℝ) u₀,
      ‖A₀ u + ((Real.sqrt u : ℝ) : ℂ) * A₁ u‖ ≤ K * Real.exp (-c / u)) :
    (∀ n : ℕ, a₀ n = 0) ∧ (∀ n : ℕ, a₁ n = 0) := by
  let A : Fin 2 → Fin 1 → ℝ → ℂ := fun ε _ ↦ if ε.val = 0 then A₀ else A₁
  let a_hat : Fin 2 → Fin 1 → ℕ → ℂ := fun ε _ ↦ if ε.val = 0 then a₀ else a₁
  have hasymp : ∀ ε a, HasRealAsymp u₀ (A ε a) (a_hat ε a) := fun ε _ ↦ by
    fin_cases ε <;> simpa [A, a_hat]
  have hbd : ∀ u ∈ Set.Ioo (0 : ℝ) u₀,
      ‖∑ ε : Fin 2, ∑ a : Fin 1,
        (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * A ε a u‖ ≤
      K * Real.exp (-c / u) := by
    intro u hu
    have hsum : (∑ ε : Fin 2, ∑ a : Fin 1,
        (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * A ε a u) =
        A₀ u + ((Real.sqrt u : ℝ) : ℂ) * A₁ u := by
      rw [Fin.sum_univ_two]
      simp [A, Real.sqrt_eq_rpow]
    rw [hsum]; exact hbound u hu
  have hall := log_puiseux_scale_separation hu₀ hc hK 0 A a_hat hasymp hbd
  exact ⟨fun n ↦ by simpa [a_hat] using hall 0 0 n, fun n ↦ by simpa [a_hat] using hall 1 0 n⟩

/-- **Proposition 4.2 (Finite `q₁`-Induction via Uniform Cauchy Tail + Scale Separation + Watson)**:
Inducting on `m = N_shift, …, 0` kills EVERY `F m ε a` identically on `slitDisk ρ₀`
and kills EVERY formal expansion `f_hat m ε a ≡ 0`! -/
theorem q1_induction_kill {u₀ ρ₀ L : ℝ} (hu₀_pos : 0 < u₀) (hu₀_le : u₀ ≤ 1 / 2)
    (huρ : u₀ < ρ₀) (hL : 1 ≤ L)
    {N_shift : ℤ} (_hN_le : N_shift ≤ 0) {K₂ : ℝ} (hK₂ : 0 ≤ K₂) (A_deg D : ℕ)
    (F : ℤ → Fin 2 → Fin (D + 1) → ℂ → ℂ)
    (f_hat : ℤ → Fin 2 → Fin (D + 1) → ℕ → ℂ)
    (hF_holo : ∀ m : ℤ, N_shift ≤ m → m ≤ 0 → ∀ ε a, DifferentiableOn ℂ (F m ε a) (slitDisk ρ₀))
    (hF_gev : ∀ m : ℤ, N_shift ≤ m → m ≤ 0 → ∀ ε a, HasGevrey1Asymp (sector34 u₀) (F m ε a) (f_hat m ε a))
    (C : ℤ → ℝ → ℂ)
    (hC_eq : ∀ m : ℤ, N_shift ≤ m → m ≤ 0 → ∀ u ∈ Set.Ioo (0 : ℝ) (u₀ / 2),
      C m u = ∑ ε : Fin 2, ∑ a : Fin (D + 1),
        (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * F m ε a (u : ℂ))
    (hC_bd : ∀ m : ℤ, N_shift ≤ m → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      ‖C m u‖ ≤ K₂ * (((m - N_shift).toNat + 1 : ℕ) : ℝ) ^ A_deg * (1 + |Real.log u|) ^ D *
        (Real.exp (-Real.pi / (L * u₀))) ^ (-m))
    (hzero : ∀ u ∈ Set.Ioo (0 : ℝ) (u₀ / 2),
      ∑' t : ℕ, C (N_shift + (t : ℤ)) u *
        (((Real.exp (-2 * Real.pi / (L * u))) ^ (N_shift + (t : ℤ)) : ℝ) : ℂ) = 0) :
    ∀ m : ℤ, N_shift ≤ m → m ≤ 0 → ∀ ε a,
      (∀ u ∈ slitDisk ρ₀, F m ε a u = 0) ∧ (∀ n : ℕ, f_hat m ε a n = 0) := by
  have hL_pos : 0 < L := by linarith
  -- Strong induction on `k : ℕ` where `m = N_shift + k ≤ 0`!
  have hind : ∀ k : ℕ, N_shift + (k : ℤ) ≤ 0 → ∀ ε a,
      (∀ u ∈ slitDisk ρ₀, F (N_shift + (k : ℤ)) ε a u = 0) ∧
      (∀ n : ℕ, f_hat (N_shift + (k : ℤ)) ε a n = 0) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk_le
      let m : ℤ := N_shift + (k : ℤ)
      have hm_ge : N_shift ≤ m := by dsimp [m]; omega
      -- All earlier `j < k` satisfy `C (N_shift + j) u = 0` on `(0, u₀ / 2)`!
      have hC_prev : ∀ j : ℕ, j < k → ∀ u ∈ Set.Ioo (0 : ℝ) (u₀ / 2), C (N_shift + (j : ℤ)) u = 0 := by
        intro j hjk u hu
        rw [hC_eq (N_shift + (j : ℤ)) (by omega) (by omega) u hu]
        apply Finset.sum_eq_zero; intro ε _
        apply Finset.sum_eq_zero; intro a _
        have hu_slit : (u : ℂ) ∈ slitDisk ρ₀ := by
          refine ⟨?_, ?_, Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hu.1))⟩
          · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]; exact hu.1
          · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]; linarith [hu.2]
        rw [(ih j hjk (by omega) ε a).1 (u : ℂ) hu_slit, mul_zero]
      -- Apply Lemma 4.1 (`cauchy_q1_tail_bound`) at `r₀ = m`!
      obtain ⟨K₁, hK₁_pos, htail⟩ := cauchy_q1_tail_bound hu₀_pos hu₀_le hL hK₂ A_deg D hC_bd m hm_ge
      have hCm_exp : ∀ u ∈ Set.Ioo (0 : ℝ) (u₀ / 2),
          ‖∑ ε : Fin 2, ∑ a : Fin (D + 1),
            (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * F m ε a (u : ℂ)‖ ≤
            K₁ * Real.exp (-(Real.pi / L) / u) := by
        intro u hu
        rw [← hC_eq m hm_ge hk_le u hu]
        obtain ⟨hsum_tail, hbd_tail⟩ := htail u hu.1 hu.2.le
        let q : ℝ := Real.exp (-2 * Real.pi / (L * u))
        have hq_pos : 0 < q := Real.exp_pos _
        have hqC_ne : ((q ^ m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_pos hq_pos m).ne'
        -- Show `C m u = -(∑' t, C (m + t + 1) u * q^(t + 1))` by dividing `hzero u hu` by `q^m`!
        let f_term : ℕ → ℂ := fun t ↦ C (N_shift + (t : ℤ)) u * (((q ^ (N_shift + (t : ℤ)) : ℝ) : ℂ))
        have hf_shift : Summable (fun t : ℕ ↦ f_term (t + (k + 1))) := by
          have heq : (fun t : ℕ ↦ f_term (t + (k + 1))) =
              fun t : ℕ ↦ ((q ^ m : ℝ) : ℂ) * (C (m + ((t + 1 : ℕ) : ℤ)) u * ((q ^ (t + 1) : ℝ) : ℂ)) := by
            ext t; dsimp [f_term, m]
            have hexp : N_shift + ((t : ℤ) + ((k : ℤ) + 1)) = (N_shift + (k : ℤ)) + ((t : ℤ) + 1) := by ring
            have hcast2 : ((t : ℤ) + 1) = ((t + 1 : ℕ) : ℤ) := by push_cast; ring
            rw [hexp, zpow_add₀ hq_pos.ne', hcast2, zpow_natCast, Complex.ofReal_mul]; ring
          rw [heq]; simpa [q] using hsum_tail.mul_left ((q ^ m : ℝ) : ℂ)
        have hf_sum : Summable f_term := (summable_nat_add_iff (k + 1)).mp hf_shift
        have hsplit := hf_sum.sum_add_tsum_nat_add (k + 1)
        have h0 := hzero u hu
        change ∑' t : ℕ, f_term t = 0 at h0
        rw [h0] at hsplit
        have hfin : ∑ j ∈ Finset.range (k + 1), f_term j = ((q ^ m : ℝ) : ℂ) * C m u := by
          rw [Finset.sum_range_succ]
          have hprev0 : ∑ j ∈ Finset.range k, f_term j = 0 := by
            apply Finset.sum_eq_zero; intro j hj
            dsimp [f_term]; rw [hC_prev j (Finset.mem_range.mp hj) u hu, zero_mul]
          rw [hprev0, zero_add]; dsimp [f_term, m]; ring
        have htail_eq : ∑' t : ℕ, f_term (t + (k + 1)) =
            ((q ^ m : ℝ) : ℂ) * ∑' t : ℕ, C (m + ((t + 1 : ℕ) : ℤ)) u * ((q ^ (t + 1) : ℝ) : ℂ) := by
          rw [← tsum_mul_left]
          apply tsum_congr; intro t; dsimp [f_term, m]
          have hexp : N_shift + ((t : ℤ) + ((k : ℤ) + 1)) = (N_shift + (k : ℤ)) + ((t : ℤ) + 1) := by ring
          have hcast2 : ((t : ℤ) + 1) = ((t + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [hexp, zpow_add₀ hq_pos.ne', hcast2, zpow_natCast, Complex.ofReal_mul]; ring
        rw [hfin, htail_eq, ← mul_add] at hsplit
        have hCm_eq : C m u = -(∑' t : ℕ, C (m + ((t + 1 : ℕ) : ℤ)) u * ((q ^ (t + 1) : ℝ) : ℂ)) :=
          eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hsplit).resolve_left hqC_ne)
        rw [hCm_eq, norm_neg, show -(Real.pi / L) / u = -Real.pi / (L * u) by ring]
        simpa [q] using hbd_tail
      -- Scale separation kills every `f_hat m ε a n = 0`!
      have hasymp_real : ∀ ε a, HasRealAsymp (u₀ / 2) (fun u : ℝ ↦ F m ε a (u : ℂ)) (f_hat m ε a) := by
        intro ε a
        refine hasRealAsymp_of_hasGevrey1Asymp (fun u hu ↦ ?_) (hF_gev m hm_ge hk_le ε a)
        have hu_pos : 0 < u := hu.1
        refine ⟨?_, ?_, ?_⟩
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]; exact hu_pos
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]; linarith [hu.2]
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos, Complex.ofReal_re]
          have : 0 ≤ Real.sqrt 2 / 2 * u := by positivity
          linarith
      have hhat0 := log_puiseux_scale_separation (u₀ := u₀ / 2) (by linarith) (div_pos Real.pi_pos hL_pos)
        hK₁_pos.le D (fun ε a u ↦ F m ε a (u : ℂ)) (f_hat m) hasymp_real hCm_exp
      -- Watson uniqueness kills `F m ε a` identically on `slitDisk ρ₀`!
      intro ε a
      have hgev0 : HasGevrey1Asymp (sector34 u₀) (F m ε a) (fun _ ↦ 0) :=
        hasGevrey1Asymp_congr (fun _ _ ↦ rfl) (fun n ↦ hhat0 ε a n) (hF_gev m hm_ge hk_le ε a)
      exact ⟨watson_of_gevrey1_zero hu₀_pos huρ (hF_holo m hm_ge hk_le ε a) hgev0, hhat0 ε a⟩
  intro m hm_ge hm_le ε a
  have hk_eq : N_shift + ((m - N_shift).toNat : ℤ) = m := by omega
  have h := hind (m - N_shift).toNat (by omega) ε a
  rwa [hk_eq] at h

/-- **Exact Top-Degree Survival Algebra Lemma**:
Over ANY commutative ring `R`, substituting `X_i ↦ γ_i X_i + B_i` into a polynomial
`P ∈ MvPolynomial ι R` leaves every top-degree monomial `α` (`|α| = P.totalDegree`)
completely uncorrupted by `B`:
`[X^α] P(γ_i X_i + B_i) = ([X^α] P) * ∏_{i ∈ α.support} γ_i^{α_i}`! -/
theorem mvPoly_shift_top_coeff {ι R : Type*} [CommRing R] [DecidableEq ι]
    (P : MvPolynomial ι R) (γ B : ι → R) (α : ι →₀ ℕ)
    (hα : α.sum (fun _ k ↦ k) = P.totalDegree) :
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.C (γ i) * MvPolynomial.X i + MvPolynomial.C (B i)) P).coeff α =
      P.coeff α * ∏ i ∈ α.support, (γ i) ^ (α i) := by
  let φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.aeval (fun i ↦ MvPolynomial.C (γ i) * MvPolynomial.X i + MvPolynomial.C (B i))
  -- Step 1: For ANY monomial `β`, every `μ` in `supp(φ(X^β))` satisfies `μ ≤ β` pointwise,
  -- and `[X^β] φ(X^β) = ∏_{i ∈ β.support} γ_i^{β_i}`!
  have hmono : ∀ β : ι →₀ ℕ,
      (∀ μ : ι →₀ ℕ, (φ (MvPolynomial.monomial β (1 : R))).coeff μ ≠ 0 → μ ≤ β) ∧
      (φ (MvPolynomial.monomial β (1 : R))).coeff β = ∏ i ∈ β.support, (γ i) ^ (β i) := by
    intro β
    induction β using Finsupp.induction with
    | zero =>
      simp only [MvPolynomial.monomial_zero', map_one, Finsupp.support_zero, Finset.prod_empty,
        MvPolynomial.coeff_one]
      refine ⟨fun μ hμ ↦ ?_, by simp⟩
      by_cases h0 : μ = 0
      · subst h0; exact le_rfl
      · simp [Ne.symm h0] at hμ
    | single_add i k β hi hk ih =>
      -- Decompose `monomial (single i k + β) 1 = (X i)^k * monomial β 1`!
      have hfac : MvPolynomial.monomial (Finsupp.single i k + β) (1 : R) =
          (MvPolynomial.X i) ^ k * MvPolynomial.monomial β (1 : R) := by
        rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one]
      rw [hfac, map_mul, map_pow]
      have hXi : φ (MvPolynomial.X i) = MvPolynomial.C (γ i) * MvPolynomial.X i + MvPolynomial.C (B i) := by
        simp [φ]
      rw [hXi, add_pow]
      have hterm_supp : ∀ m ∈ Finset.range (k + 1),
          ((MvPolynomial.C (γ i) * MvPolynomial.X i) ^ m * (MvPolynomial.C (B i)) ^ (k - m) *
            ((Nat.choose k m : ℕ) : MvPolynomial ι R)) =
          MvPolynomial.monomial (Finsupp.single i m)
            ((γ i) ^ m * (B i) ^ (k - m) * (Nat.choose k m : R)) := by
        intro m _
        rw [mul_pow, ← map_pow, ← map_pow, MvPolynomial.X_pow_eq_monomial,
            MvPolynomial.C_mul_monomial, mul_one, mul_comm _ (MvPolynomial.C ((B i) ^ (k - m))),
            MvPolynomial.C_mul_monomial, ← MvPolynomial.C_eq_natCast, mul_comm _ (MvPolynomial.C _),
            MvPolynomial.C_mul_monomial]
        congr 1; ring
      rw [Finset.sum_congr rfl hterm_supp, Finset.sum_mul]
      have hcoeff_mu : ∀ μ : ι →₀ ℕ,
          (∑ m ∈ Finset.range (k + 1),
            MvPolynomial.monomial (Finsupp.single i m) ((γ i) ^ m * (B i) ^ (k - m) * (Nat.choose k m : R)) *
            φ (MvPolynomial.monomial β (1 : R))).coeff μ =
          ∑ m ∈ Finset.range (k + 1),
            if m ≤ μ i then
              ((γ i) ^ m * (B i) ^ (k - m) * (Nat.choose k m : R)) *
                (φ (MvPolynomial.monomial β (1 : R))).coeff (μ - Finsupp.single i m)
            else 0 := by
        intro μ
        rw [MvPolynomial.coeff_sum]
        apply Finset.sum_congr rfl; intro m _
        rw [MvPolynomial.coeff_monomial_mul']
        have hle_iff : Finsupp.single i m ≤ μ ↔ m ≤ μ i := by
          constructor
          · intro h; simpa using h i
          · intro h j
            by_cases hji : j = i
            · subst hji; simpa using h
            · rw [Finsupp.single_eq_of_ne hji]; exact Nat.zero_le _
        simp [hle_iff]
      refine ⟨fun μ hμ ↦ ?_, ?_⟩
      · rw [hcoeff_mu] at hμ
        obtain ⟨m, hm, hterm_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
        have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        split_ifs at hterm_ne with hle
        · have hβ_le := ih.1 (μ - Finsupp.single i m) (right_ne_zero_of_mul hterm_ne)
          intro j
          by_cases hji : j = i
          · subst j
            have h1 := hβ_le i
            simp only [Finsupp.tsub_apply, Finsupp.single_eq_same,
              Finsupp.add_apply] at h1 ⊢
            omega
          · have h1 := hβ_le j
            rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hji, tsub_zero] at h1
            rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hji, zero_add]
            exact h1
        · exact absurd rfl hterm_ne
      · rw [hcoeff_mu]
        have hβi0 : β i = 0 := Finsupp.notMem_support_iff.mp hi
        rw [Finset.sum_eq_single k]
        · have hle : k ≤ (Finsupp.single i k + β) i := by simp [hβi0]
          have hsub : Finsupp.single i k + β - Finsupp.single i k = β := by
            ext j; simp
          simp only [hle, ↓reduceIte, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
            hsub, ih.2]
          have hsupp_s : (Finsupp.single i k).support = {i} := by
            ext j; simp [hk]
          rw [Finsupp.support_add_eq (by
            rw [Finset.disjoint_left]; intro j hj
            have hji : j = i := by
              have := Finsupp.support_single_subset hj; simpa using this
            subst hji; exact hi),
            Finset.prod_union (by
              rw [Finset.disjoint_left]; intro j hj
              have hji : j = i := by
                have := Finsupp.support_single_subset hj; simpa using this
              subst hji; exact hi),
            hsupp_s, Finset.prod_singleton]
          simp only [Finsupp.add_apply, Finsupp.single_eq_same, hβi0, add_zero]
          congr 1
          apply Finset.prod_congr rfl; intro j hj
          have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
          rw [Finsupp.single_eq_of_ne hji, zero_add]
        · intro m hm hmk
          have hmlt : m < k := by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm); omega
          split_ifs with hle
          · suffices (φ (MvPolynomial.monomial β (1 : R))).coeff
                (Finsupp.single i k + β - Finsupp.single i m) = 0 by rw [this, mul_zero]
            by_contra hne
            have hleβ := ih.1 _ hne i
            simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hβi0, add_zero] at hleβ
            omega
          · rfl
        · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hnot
  -- Step 2: Expand `P = ∑ β ∈ P.support, C (P.coeff β) * monomial β 1`!
  have hP_eq : P = ∑ β ∈ P.support, MvPolynomial.C (P.coeff β) * MvPolynomial.monomial β (1 : R) := by
    conv_lhs => rw [P.as_sum]
    apply Finset.sum_congr rfl; intro β _
    rw [MvPolynomial.C_mul_monomial, mul_one]
  conv_lhs => rw [hP_eq]
  rw [map_sum, MvPolynomial.coeff_sum]
  by_cases hα_mem : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul, (hmono α).2]
    · intro β hβ hβα
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]
      suffices (φ (MvPolynomial.monomial β (1 : R))).coeff α = 0 by rw [this, mul_zero]
      by_contra hne
      have hα_le_β : α ≤ β := (hmono β).1 α hne
      have hβ_sum_le : β.sum (fun _ k ↦ k) ≤ P.totalDegree := MvPolynomial.le_totalDegree hβ
      have hα_eq_β : α = β := by
        apply Finsupp.ext; intro i
        by_contra hneq
        have hlt : α i < β i := lt_of_le_of_ne (hα_le_β i) hneq
        have hsum_lt : α.sum (fun _ k ↦ k) < β.sum (fun _ k ↦ k) := by
          have hsub : α.support ⊆ β.support := by
            intro j hj
            rw [Finsupp.mem_support_iff] at hj ⊢
            have := hα_le_β j; omega
          have hi_mem : i ∈ β.support := Finsupp.mem_support_iff.mpr (by omega)
          calc α.sum (fun _ k ↦ k) = ∑ j ∈ α.support, α j := rfl
            _ ≤ ∑ j ∈ β.support, α j := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Nat.zero_le _
            _ < ∑ j ∈ β.support, β j :=
                Finset.sum_lt_sum (fun j _ ↦ hα_le_β j) ⟨i, hi_mem, hlt⟩
            _ = β.sum (fun _ k ↦ k) := rfl
        omega
      exact hβα hα_eq_β.symm
    · intro hnot; exact absurd hα_mem hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα_mem
    rw [hP0, zero_mul]
    apply Finset.sum_eq_zero; intro β hβ
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]
    suffices (φ (MvPolynomial.monomial β (1 : R))).coeff α = 0 by rw [this, mul_zero]
    by_contra hne
    have hα_le_β : α ≤ β := (hmono β).1 α hne
    have hβ_sum_le : β.sum (fun _ k ↦ k) ≤ P.totalDegree := MvPolynomial.le_totalDegree hβ
    have hα_eq_β : α = β := by
      apply Finsupp.ext; intro i
      by_contra hneq
      have hlt : α i < β i := lt_of_le_of_ne (hα_le_β i) hneq
      have hsum_lt : α.sum (fun _ k ↦ k) < β.sum (fun _ k ↦ k) := by
        have hsub : α.support ⊆ β.support := by
          intro j hj; rw [Finsupp.mem_support_iff] at hj ⊢; have := hα_le_β j; omega
        have hi_mem : i ∈ β.support := Finsupp.mem_support_iff.mpr (by omega)
        calc α.sum (fun _ k ↦ k) = ∑ j ∈ α.support, α j := rfl
          _ ≤ ∑ j ∈ β.support, α j := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Nat.zero_le _
          _ < ∑ j ∈ β.support, β j := Finset.sum_lt_sum (fun j _ ↦ hα_le_β j) ⟨i, hi_mem, hlt⟩
          _ = β.sum (fun _ k ↦ k) := rfl
      omega
    exact hα_mem (hα_eq_β ▸ hβ)

/-- **Proposition 4.2 (Top-Degree Survival in `Q_{0,0,0}(u; Z) ∈ ℂ{u}[Z]`)**:
If `P ∈ ℂ[X]` has positive total degree `D := P.totalDegree ≥ 1`, `γ : ι → ℂ` has all
entries nonzero, and `Q : MvPolynomial ι convergentSubring` has top-degree coefficients
`(Q.coeff α).val = X^{N₁} * C (P.coeff α * ∏_{i ∈ α.support} γ_i^{α_i})` for every `|α| = D`,
then **`Q ≠ 0` AND `D ≤ Q.totalDegree`** (in particular `1 ≤ Q.totalDegree`)! -/
theorem top_degree_survival {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial ι ℂ) (hP_deg : 1 ≤ P.totalDegree)
    (γ : ι → ℂ) (hγ : ∀ i, γ i ≠ 0) (N₁ : ℕ)
    (Q : MvPolynomial ι convergentSubring)
    (htop : ∀ α : ι →₀ ℕ, α.sum (fun _ k ↦ k) = P.totalDegree →
      (Q.coeff α).val = PowerSeries.X ^ N₁ * PowerSeries.C (P.coeff α * ∏ i ∈ α.support, (γ i) ^ (α i))) :
    Q ≠ 0 ∧ P.totalDegree ≤ Q.totalDegree := by
  have hP_ne : P ≠ 0 := by
    intro h0; rw [h0, MvPolynomial.totalDegree_zero] at hP_deg; omega
  have hsupp_non : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP_ne
  obtain ⟨α, hα_mem, hα_deg⟩ := Finset.exists_mem_eq_sup' hsupp_non (fun s : ι →₀ ℕ ↦ s.sum fun _ k ↦ k)
  have hα_eq : α.sum (fun _ k ↦ k) = P.totalDegree := by
    rw [MvPolynomial.totalDegree, ← Finset.sup'_eq_sup hsupp_non]
    exact hα_deg.symm
  have hPα_ne : P.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα_mem
  have hprod_ne : ∏ i ∈ α.support, (γ i) ^ (α i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hγ i)
  have hQα_ne : Q.coeff α ≠ 0 := by
    intro h0
    have hval := congrArg Subtype.val h0
    rw [htop α hα_eq] at hval
    have hc := congrArg (PowerSeries.coeff N₁) hval
    simp only [PowerSeries.coeff_X_pow_mul', le_rfl, ↓reduceIte, Nat.sub_self,
      PowerSeries.coeff_zero_C, ZeroMemClass.coe_zero, map_zero] at hc
    exact mul_ne_zero hPα_ne hprod_ne hc
  have hα_in_Q : α ∈ Q.support := MvPolynomial.mem_support_iff.mpr hQα_ne
  refine ⟨fun h0 ↦ hQα_ne (by rw [h0]; simp), ?_⟩
  rw [← hα_eq]
  exact MvPolynomial.le_totalDegree hα_in_Q

/-- **Proposition 4.2 (Minimal-Total-Degree Descent into `ℂ{x}[Z]`)**:
Given ANY nonzero convergent annihilator `Rtilde ∈ MvPolynomial ι convergentSubring`
of a formal jet `Yhat : ι → PowerSeries ℂ`, there exists a nonzero minimal-total-degree
annihilator `R ∈ MvPolynomial ι convergentSubring` with `0 < R.totalDegree`! -/
theorem minimal_degree_descent {ι : Type*} (Yhat : ι → PowerSeries ℂ)
    (Rtilde : MvPolynomial ι convergentSubring) (hRtilde_ne : Rtilde ≠ 0)
    (hRtilde_ann : MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype Rtilde) = 0) :
    ∃ R : MvPolynomial ι convergentSubring,
      R ≠ 0 ∧ 0 < R.totalDegree ∧
      MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype R) = 0 ∧
      ∀ Q : MvPolynomial ι convergentSubring,
        Q ≠ 0 →
        MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype Q) = 0 →
        R.totalDegree ≤ Q.totalDegree := by
  classical
  have hex : ∃ d : ℕ, ∃ R : MvPolynomial ι convergentSubring,
      R ≠ 0 ∧ MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype R) = 0 ∧
      R.totalDegree = d :=
    ⟨Rtilde.totalDegree, Rtilde, hRtilde_ne, hRtilde_ann, rfl⟩
  let d₀ := Nat.find hex
  obtain ⟨R, hR_ne, hR_ann, hR_deg⟩ := Nat.find_spec hex
  have hR_pos : 0 < R.totalDegree := by
    by_contra h0
    have hd0 : R.totalDegree = 0 := Nat.eq_zero_of_not_pos h0
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd0
    rw [hC, MvPolynomial.map_C, MvPolynomial.aeval_C] at hR_ann
    have hc0 : R.coeff 0 = 0 := Subtype.ext (by simpa using hR_ann)
    exact hR_ne (by rw [hC, hc0, MvPolynomial.C_0])
  refine ⟨R, hR_ne, hR_pos, hR_ann, fun Q hQ_ne hQ_ann ↦ ?_⟩
  rw [hR_deg]
  exact Nat.find_min' hex ⟨Q, hQ_ne, hQ_ann, rfl⟩

/-! ### Section 4: Convergent Polynomial Evaluation, Proposition 5.3, & End-to-End Paper #10 Assembly -/

/-- Ring homomorphism embedding `ℂ[x]` into `convergentSubring` (`ℂ{x}`). -/
def convPolyEmb : Polynomial ℂ →+* convergentSubring where
  toFun p := ⟨(p : PowerSeries ℂ), 1, ∑ d ∈ p.support, ‖p.coeff d‖, zero_lt_one,
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, fun n ↦ by
      rw [one_pow, mul_one, Polynomial.coeff_coe]
      by_cases hn : n ∈ p.support
      · exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hn
      · rw [Polynomial.notMem_support_iff.mp hn, norm_zero]
        exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' p q := Subtype.ext (by simp)

theorem convPolyEmb_injective : Function.Injective convPolyEmb := by
  intro p q h
  have hval : (p : PowerSeries ℂ) = (q : PowerSeries ℂ) := congrArg Subtype.val h
  ext n
  have hn := congrArg (PowerSeries.coeff n) hval
  simpa [Polynomial.coeff_coe] using hn

theorem psEval_convPolyEmb (p : Polynomial ℂ) (z : ℂ) :
    psEval (convPolyEmb p).val z = p.eval z := by
  dsimp [psEval, convPolyEmb]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self p.natDegree),
      tsum_eq_sum (s := Finset.range (p.natDegree + 1))]
  · apply Finset.sum_congr rfl; intro n _; rw [Polynomial.coeff_coe]
  · intro n hn
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt
      (by have := Finset.mem_range.not.mp hn; omega), zero_mul]

/-- Multiplication by a polynomial commutes with `psEval` on the entire disk of convergence! -/
theorem psEval_poly_mul {ρ M : ℝ} {q : PowerSeries ℂ} (hq : IsConvergentOn ρ M q)
    (p : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ < ρ) :
    psEval ((p : PowerSeries ℂ) * q) z = p.eval z * psEval q z := by
  have hq_sum : Summable (fun n : ℕ ↦ q.coeff n * z ^ n) := isConvergentOn_summable hq hz
  -- Helper: `psEval (X^d * q) z = z^d * psEval q z`
  have hXpow : ∀ d : ℕ, psEval ((PowerSeries.X : PowerSeries ℂ) ^ d * q) z = z ^ d * psEval q z := by
    intro d
    dsimp [psEval]
    have hcoeff : ∀ n : ℕ, ((PowerSeries.X : PowerSeries ℂ) ^ d * q).coeff n * z ^ n =
        if d ≤ n then q.coeff (n - d) * z ^ n else 0 := fun n ↦ by
      rw [PowerSeries.coeff_X_pow_mul']
      split_ifs <;> simp
    simp_rw [hcoeff]
    have hshift : Summable (fun m : ℕ ↦ if d ≤ m + d then q.coeff (m + d - d) * z ^ (m + d) else 0) := by
      have heq : (fun m : ℕ ↦ if d ≤ m + d then q.coeff (m + d - d) * z ^ (m + d) else 0) =
          fun m : ℕ ↦ z ^ d * (q.coeff m * z ^ m) := by
        ext m; simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]; ring
      rw [heq]; exact hq_sum.mul_left _
    have hsum : Summable (fun n : ℕ ↦ if d ≤ n then q.coeff (n - d) * z ^ n else 0) :=
      (summable_nat_add_iff d).mp hshift
    rw [← hsum.sum_add_tsum_nat_add d]
    have hfin0 : ∑ n ∈ Finset.range d, (if d ≤ n then q.coeff (n - d) * z ^ n else 0) = 0 := by
      apply Finset.sum_eq_zero; intro n hn
      have hlt : n < d := Finset.mem_range.mp hn
      simp [not_le.mpr hlt]
    rw [hfin0, zero_add, ← tsum_mul_left]
    apply tsum_congr; intro m
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]; ring
  -- Expand `p = ∑ d ∈ range (p.natDegree + 1), C (p.coeff d) * X^d`!
  have hp_eq : (p : PowerSeries ℂ) =
      ∑ d ∈ Finset.range (p.natDegree + 1), PowerSeries.C (p.coeff d) * PowerSeries.X ^ d := by
    ext n; rw [Polynomial.coeff_coe, map_sum]
    by_cases hn : n < p.natDegree + 1
    · rw [Finset.sum_eq_single n]
      · simp only [mul_comm, PowerSeries.coeff_X_pow_mul', le_rfl, ↓reduceIte, Nat.sub_self,
          PowerSeries.coeff_zero_C]
      · intro d _ hdn
        rw [mul_comm, PowerSeries.coeff_X_pow_mul']
        split_ifs with hle
        · have hne0 : n - d ≠ 0 := by omega
          simp only [PowerSeries.coeff_C, hne0, ↓reduceIte]
        · rfl
      · intro hnot; exact absurd (Finset.mem_range.mpr hn) hnot
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      symm; apply Finset.sum_eq_zero; intro d hd
      have hlt : d < p.natDegree + 1 := Finset.mem_range.mp hd
      rw [mul_comm, PowerSeries.coeff_X_pow_mul']
      split_ifs with hle
      · have hne0 : n - d ≠ 0 := by omega
        simp only [PowerSeries.coeff_C, hne0, ↓reduceIte]
      · rfl
  have hterm_sum : ∀ d : ℕ,
      Summable (fun n : ℕ ↦ (PowerSeries.C (p.coeff d) * PowerSeries.X ^ d * q).coeff n * z ^ n) := by
    intro d
    have hcoeff : (fun n : ℕ ↦ (PowerSeries.C (p.coeff d) * PowerSeries.X ^ d * q).coeff n * z ^ n) =
        fun n : ℕ ↦ p.coeff d * (((PowerSeries.X : PowerSeries ℂ) ^ d * q).coeff n * z ^ n) := by
      ext n; rw [mul_assoc, PowerSeries.coeff_C_mul]; ring
    rw [hcoeff]
    have hsh : Summable (fun n : ℕ ↦ ((PowerSeries.X : PowerSeries ℂ) ^ d * q).coeff n * z ^ n) := by
      refine (summable_nat_add_iff d).mp ?_
      have heq : (fun m : ℕ ↦ ((PowerSeries.X : PowerSeries ℂ) ^ d * q).coeff (m + d) * z ^ (m + d)) =
          fun m : ℕ ↦ z ^ d * (q.coeff m * z ^ m) := by
        ext m; simp only [PowerSeries.coeff_X_pow_mul', Nat.le_add_left, ↓reduceIte,
          Nat.add_sub_cancel, pow_add]; ring
      rw [heq]; exact hq_sum.mul_left _
    exact hsh.mul_left _
  rw [hp_eq, Finset.sum_mul, Polynomial.eval_eq_sum_range' (Nat.lt_succ_self p.natDegree), Finset.sum_mul]
  change ∑' n : ℕ, (∑ d ∈ Finset.range (p.natDegree + 1),
      PowerSeries.C (p.coeff d) * PowerSeries.X ^ d * q).coeff n * z ^ n = _
  have hcoeff_sum : (fun n : ℕ ↦ (∑ d ∈ Finset.range (p.natDegree + 1),
        PowerSeries.C (p.coeff d) * PowerSeries.X ^ d * q).coeff n * z ^ n) =
      fun n : ℕ ↦ ∑ d ∈ Finset.range (p.natDegree + 1),
        (PowerSeries.C (p.coeff d) * PowerSeries.X ^ d * q).coeff n * z ^ n := by
    ext n; rw [map_sum, Finset.sum_mul]
  rw [hcoeff_sum, Summable.tsum_finsetSum (fun d _ ↦ hterm_sum d)]
  apply Finset.sum_congr rfl; intro d _
  have hcm : (fun n : ℕ ↦ (PowerSeries.C (p.coeff d) * PowerSeries.X ^ d * q).coeff n * z ^ n) =
      fun n : ℕ ↦ p.coeff d * (((PowerSeries.X : PowerSeries ℂ) ^ d * q).coeff n * z ^ n) := by
    ext n; rw [mul_assoc, PowerSeries.coeff_C_mul]; ring
  rw [hcm, tsum_mul_left]
  change p.coeff d * psEval ((PowerSeries.X : PowerSeries ℂ) ^ d * q) z = _
  rw [hXpow d]; ring

/-- Uniform common convergence radius & bound for all coefficients of `R ∈ MvPolynomial ι convergentSubring`. -/
theorem mvPoly_conv_common_radius {ι : Type*} (R : MvPolynomial ι convergentSubring) :
    ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ∀ m : ι →₀ ℕ, IsConvergentOn ρ M (R.coeff m).val := by
  classical
  have hex : ∀ m ∈ R.support, ∃ ρ M : ℝ, IsConvergentOn ρ M (R.coeff m).val :=
    fun m _ ↦ (R.coeff m).property
  by_cases hne : R.support.Nonempty
  · choose ρ_m M_m hconv using fun m : {m // m ∈ R.support} ↦ hex m.1 m.2
    let ρ : ℝ := R.support.attach.inf' (Finset.attach_nonempty_iff.mpr hne) ρ_m
    let M : ℝ := R.support.attach.sup' (Finset.attach_nonempty_iff.mpr hne) M_m
    have hρ_pos : 0 < ρ := (Finset.lt_inf'_iff _).mpr fun m _ ↦ (hconv m).1
    have hM_nn : 0 ≤ M := by
      obtain ⟨m₀, hm₀⟩ := hne
      exact le_trans (hconv ⟨m₀, hm₀⟩).2.1
        (Finset.le_sup' M_m (Finset.mem_attach R.support ⟨m₀, hm₀⟩))
    refine ⟨ρ, M, hρ_pos, hM_nn, fun m ↦ ?_⟩
    by_cases hm : m ∈ R.support
    · have hρ_le : ρ ≤ ρ_m ⟨m, hm⟩ := Finset.inf'_le ρ_m (Finset.mem_attach R.support ⟨m, hm⟩)
      have hM_le : M_m ⟨m, hm⟩ ≤ M := Finset.le_sup' M_m (Finset.mem_attach R.support ⟨m, hm⟩)
      refine ⟨hρ_pos, hM_nn, fun n ↦ ?_⟩
      calc ‖(R.coeff m).val.coeff n‖ * ρ ^ n
          ≤ ‖(R.coeff m).val.coeff n‖ * (ρ_m ⟨m, hm⟩) ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ_pos.le hρ_le n) (norm_nonneg _)
        _ ≤ M_m ⟨m, hm⟩ := (hconv ⟨m, hm⟩).2.2 n
        _ ≤ M := hM_le
    · have h0 : R.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
      refine ⟨hρ_pos, hM_nn, fun n ↦ ?_⟩
      rw [h0]; simp [hM_nn]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, 0, zero_lt_one, le_rfl, fun m ↦ ⟨zero_lt_one, le_rfl, fun n ↦ ?_⟩⟩
    have h0 : R.coeff m = 0 := MvPolynomial.notMem_support_iff.mp (by rw [hne]; exact Finset.notMem_empty m)
    rw [h0]; simp

/-- Evaluate the coefficients of `R ∈ MvPolynomial ι convergentSubring` at `u : ℂ`,
yielding an ordinary polynomial `evalAtConv u R ∈ MvPolynomial ι ℂ`! -/
def evalAtConv {ι : Type*} [DecidableEq ι] (u : ℂ) (R : MvPolynomial ι convergentSubring) :
    MvPolynomial ι ℂ :=
  ∑ m ∈ R.support, MvPolynomial.monomial m (psEval (R.coeff m).val u)

theorem coeff_evalAtConv {ι : Type*} [DecidableEq ι] (u : ℂ)
    (R : MvPolynomial ι convergentSubring) (m : ι →₀ ℕ) :
    (evalAtConv u R).coeff m = psEval (R.coeff m).val u := by
  dsimp [evalAtConv]
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m ∈ R.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hkm; simp [MvPolynomial.coeff_monomial, hkm]
    · intro hnot; exact absurd hm hnot
  · rw [Finset.sum_eq_zero (fun k hk ↦ by
      have hkm : k ≠ m := fun h ↦ hm (h ▸ hk)
      simp [MvPolynomial.coeff_monomial, hkm])]
    have h0 : R.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    rw [h0]; simp [psEval]

theorem aeval_evalAtConv {ι : Type*} [DecidableEq ι] (u : ℂ)
    (R : MvPolynomial ι convergentSubring) (Z : ι → ℂ) :
    MvPolynomial.aeval Z (evalAtConv u R) =
      ∑ m ∈ R.support, psEval (R.coeff m).val u * ∏ i ∈ m.support, (Z i) ^ (m i) := by
  dsimp [evalAtConv]
  rw [map_sum]
  apply Finset.sum_congr rfl; intro m _
  rw [MvPolynomial.eval_monomial, Finsupp.prod]

theorem evalAtConv_pderiv {ι : Type*} [DecidableEq ι] (u : ℂ)
    (R : MvPolynomial ι convergentSubring) (j : ι) :
    MvPolynomial.pderiv j (evalAtConv u R) = evalAtConv u (MvPolynomial.pderiv j R) := by
  apply MvPolynomial.ext; intro m
  rw [MvPolynomial.coeff_pderiv, coeff_evalAtConv, coeff_evalAtConv, MvPolynomial.coeff_pderiv]
  have hnat : ((R.coeff (m + Finsupp.single j 1) * ((m j : convergentSubring) + 1)).val) =
      (R.coeff (m + Finsupp.single j 1)).val * ((m j + 1 : ℕ) : PowerSeries ℂ) := by
    simp
  rw [hnat]
  dsimp [psEval]
  rw [← tsum_mul_right]
  apply tsum_congr; intro n
  rw [mul_comm _ (((m j + 1 : ℕ) : PowerSeries ℂ)),
      show (((m j + 1 : ℕ) : PowerSeries ℂ)) = PowerSeries.C ((m j + 1 : ℕ) : ℂ) from
        (map_natCast PowerSeries.C (m j + 1)).symm,
      PowerSeries.coeff_C_mul]
  push_cast; ring

theorem evalAtConv_dirDeriv_poly {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ M : ℝ} (R : MvPolynomial ι convergentSubring)
    (hR_conv : ∀ m : ι →₀ ℕ, IsConvergentOn ρ M (R.coeff m).val)
    (W : ι → Polynomial ℂ) {u : ℂ} (hu : ‖u‖ < ρ) :
    dirDeriv (fun j ↦ (W j).eval u) (evalAtConv u R) =
      evalAtConv u (dirDeriv (fun j ↦ convPolyEmb (W j)) R) := by
  apply MvPolynomial.ext; intro m
  rw [coeff_evalAtConv, dirDeriv, dirDeriv, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  have hterm_sum : ∀ j : ι,
      Summable (fun n : ℕ ↦ ((convPolyEmb (W j) * (MvPolynomial.pderiv j R).coeff m).val).coeff n * u ^ n) := by
    intro j
    have hpd_conv : IsConvergentOn ρ (M * ((m j + 1 : ℕ) : ℝ)) ((MvPolynomial.pderiv j R).coeff m).val := by
      refine ⟨(hR_conv 0).1, by have := (hR_conv 0).2.1; positivity, fun n ↦ ?_⟩
      rw [MvPolynomial.coeff_pderiv]
      have hval : (R.coeff (m + Finsupp.single j 1) * ((m j : convergentSubring) + 1)).val.coeff n =
          (R.coeff (m + Finsupp.single j 1)).val.coeff n * ((m j + 1 : ℕ) : ℂ) := by
        have h1 : (R.coeff (m + Finsupp.single j 1) * ((m j : convergentSubring) + 1)).val =
            PowerSeries.C ((m j + 1 : ℕ) : ℂ) * (R.coeff (m + Finsupp.single j 1)).val := by
          rw [map_natCast PowerSeries.C, mul_comm]; simp
        rw [h1, PowerSeries.coeff_C_mul]; ring
      rw [hval, norm_mul, Complex.norm_natCast]
      calc ‖(R.coeff (m + Finsupp.single j 1)).val.coeff n‖ * ((m j + 1 : ℕ) : ℝ) * ρ ^ n
          = (‖(R.coeff (m + Finsupp.single j 1)).val.coeff n‖ * ρ ^ n) * ((m j + 1 : ℕ) : ℝ) := by ring
        _ ≤ M * ((m j + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right ((hR_conv _).2.2 n) (Nat.cast_nonneg _)
    -- Multiply by polynomial `W j` preserves summability at `u` (`‖u‖ < ρ`)!
    have hp_sum : ∀ d : ℕ, Summable (fun n : ℕ ↦
        (PowerSeries.C ((W j).coeff d) * PowerSeries.X ^ d * ((MvPolynomial.pderiv j R).coeff m).val).coeff n * u ^ n) := by
      intro d
      have hq_s := isConvergentOn_summable hpd_conv hu
      have h1 : Summable (fun n : ℕ ↦
          ((PowerSeries.X : PowerSeries ℂ) ^ d * ((MvPolynomial.pderiv j R).coeff m).val).coeff n * u ^ n) := by
        refine (summable_nat_add_iff d).mp ?_
        have heq : (fun k : ℕ ↦ ((PowerSeries.X : PowerSeries ℂ) ^ d *
              ((MvPolynomial.pderiv j R).coeff m).val).coeff (k + d) * u ^ (k + d)) =
            fun k : ℕ ↦ u ^ d * (((MvPolynomial.pderiv j R).coeff m).val.coeff k * u ^ k) := by
          ext k; simp only [PowerSeries.coeff_X_pow_mul', Nat.le_add_left, ↓reduceIte,
            Nat.add_sub_cancel, pow_add]; ring
        rw [heq]; exact hq_s.mul_left _
      have h2 : (fun n : ℕ ↦ (PowerSeries.C ((W j).coeff d) * PowerSeries.X ^ d *
            ((MvPolynomial.pderiv j R).coeff m).val).coeff n * u ^ n) =
          fun n : ℕ ↦ (W j).coeff d * (((PowerSeries.X : PowerSeries ℂ) ^ d *
            ((MvPolynomial.pderiv j R).coeff m).val).coeff n * u ^ n) := by
        ext n; rw [mul_assoc, PowerSeries.coeff_C_mul]; ring
      rw [h2]; exact h1.mul_left _
    have hW_eq : ((convPolyEmb (W j) * (MvPolynomial.pderiv j R).coeff m).val) =
        ∑ d ∈ Finset.range ((W j).natDegree + 1),
          PowerSeries.C ((W j).coeff d) * PowerSeries.X ^ d * ((MvPolynomial.pderiv j R).coeff m).val := by
      have hp : ((W j : PowerSeries ℂ)) =
          ∑ d ∈ Finset.range ((W j).natDegree + 1), PowerSeries.C ((W j).coeff d) * PowerSeries.X ^ d := by
        ext n; rw [Polynomial.coeff_coe, map_sum]
        by_cases hn : n < (W j).natDegree + 1
        · rw [Finset.sum_eq_single n]
          · simp only [mul_comm, PowerSeries.coeff_X_pow_mul', le_rfl, ↓reduceIte, Nat.sub_self,
              PowerSeries.coeff_zero_C]
          · intro d _ hdn
            rw [mul_comm, PowerSeries.coeff_X_pow_mul']
            split_ifs with hle
            · have hne0 : n - d ≠ 0 := by omega
              simp only [PowerSeries.coeff_C, hne0, ↓reduceIte]
            · rfl
          · intro hnot; exact absurd (Finset.mem_range.mpr hn) hnot
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
          symm; apply Finset.sum_eq_zero; intro d hd
          have hlt := Finset.mem_range.mp hd
          rw [mul_comm, PowerSeries.coeff_X_pow_mul']
          split_ifs with hle
          · have hne0 : n - d ≠ 0 := by omega
            simp only [PowerSeries.coeff_C, hne0, ↓reduceIte]
          · rfl
      change (W j : PowerSeries ℂ) * ((MvPolynomial.pderiv j R).coeff m).val = _
      rw [hp, Finset.sum_mul]
    rw [hW_eq]
    have hfn : (fun n : ℕ ↦ (∑ d ∈ Finset.range ((W j).natDegree + 1),
          PowerSeries.C ((W j).coeff d) * PowerSeries.X ^ d * ((MvPolynomial.pderiv j R).coeff m).val).coeff n * u ^ n) =
        fun n : ℕ ↦ ∑ d ∈ Finset.range ((W j).natDegree + 1),
          (PowerSeries.C ((W j).coeff d) * PowerSeries.X ^ d * ((MvPolynomial.pderiv j R).coeff m).val).coeff n * u ^ n := by
      ext n; rw [map_sum, Finset.sum_mul]
    rw [hfn]
    exact summable_sum fun d _ ↦ hp_sum d
  have hsum_val : (∑ x : ι, (MvPolynomial.C (convPolyEmb (W x)) * MvPolynomial.pderiv x R).coeff m).val =
      ∑ x : ι, ((convPolyEmb (W x) * (MvPolynomial.pderiv x R).coeff m).val) := by
    have hsub : (∑ x : ι, (MvPolynomial.C (convPolyEmb (W x)) * MvPolynomial.pderiv x R).coeff m).val =
        convergentSubring.subtype (∑ x : ι, (MvPolynomial.C (convPolyEmb (W x)) * MvPolynomial.pderiv x R).coeff m) := rfl
    rw [hsub, map_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [MvPolynomial.coeff_C_mul]; rfl
  rw [hsum_val]
  change _ = ∑' n : ℕ, (∑ x : ι, (convPolyEmb (W x) * (MvPolynomial.pderiv x R).coeff m).val).coeff n * u ^ n
  have hfn_u : (fun n : ℕ ↦ (∑ x : ι, (convPolyEmb (W x) * (MvPolynomial.pderiv x R).coeff m).val).coeff n * u ^ n) =
      fun n : ℕ ↦ ∑ x : ι, ((convPolyEmb (W x) * (MvPolynomial.pderiv x R).coeff m).val).coeff n * u ^ n := by
    ext n; rw [map_sum, Finset.sum_mul]
  rw [hfn_u, Summable.tsum_finsetSum (fun j _ ↦ hterm_sum j)]
  apply Finset.sum_congr rfl; intro j _
  rw [MvPolynomial.coeff_C_mul, evalAtConv_pderiv, coeff_evalAtConv]
  have hpd_conv : IsConvergentOn ρ (M * ((m j + 1 : ℕ) : ℝ)) ((MvPolynomial.pderiv j R).coeff m).val := by
    refine ⟨(hR_conv 0).1, by have := (hR_conv 0).2.1; positivity, fun n ↦ ?_⟩
    rw [MvPolynomial.coeff_pderiv]
    have hval : (R.coeff (m + Finsupp.single j 1) * ((m j : convergentSubring) + 1)).val.coeff n =
        (R.coeff (m + Finsupp.single j 1)).val.coeff n * ((m j + 1 : ℕ) : ℂ) := by
      have h1 : (R.coeff (m + Finsupp.single j 1) * ((m j : convergentSubring) + 1)).val =
          PowerSeries.C ((m j + 1 : ℕ) : ℂ) * (R.coeff (m + Finsupp.single j 1)).val := by
        rw [map_natCast PowerSeries.C, mul_comm]; simp
      rw [h1, PowerSeries.coeff_C_mul]; ring
    rw [hval, norm_mul, Complex.norm_natCast]
    calc ‖(R.coeff (m + Finsupp.single j 1)).val.coeff n‖ * ((m j + 1 : ℕ) : ℝ) * ρ ^ n
        = (‖(R.coeff (m + Finsupp.single j 1)).val.coeff n‖ * ρ ^ n) * ((m j + 1 : ℕ) : ℝ) := by ring
      _ ≤ M * ((m j + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right ((hR_conv _).2.2 n) (Nat.cast_nonneg _)
  exact (psEval_poly_mul hpd_conv (W j) hu).symm

/-- Sign-flip ring automorphism `u ↦ -u` on `PowerSeries ℂ`: `coeff n ↦ (-1)^n * coeff n`. -/
def negPowerSeriesHom : PowerSeries ℂ →+* PowerSeries ℂ where
  toFun p := PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ n * p.coeff n)
  map_one' := by
    ext n; rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · simp
  map_mul' p q := by
    ext n; rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x hx
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk,
        show n = x.1 + x.2 from (Finset.mem_antidiagonal.mp hx).symm, pow_add]; ring
  map_zero' := by ext n; simp
  map_add' p q := by ext n; simp [mul_add]

/-- Helper: `HasGevrey1Asymp` closure under finite products & powers. -/
private lemma hasGevrey1Asymp_pow {S : Set ℂ}
    (hS : ∀ ε : ℝ, 0 < ε → ∃ u ∈ S, 0 < ‖u‖ ∧ ‖u‖ < ε)
    {f : ℂ → ℂ} {p : PowerSeries ℂ} (hf : HasGevrey1Asymp S f (fun n ↦ p.coeff n)) (k : ℕ) :
    HasGevrey1Asymp S (fun u ↦ (f u) ^ k) (fun n ↦ (p ^ k).coeff n) := by
  induction k with
  | zero =>
    simpa [pow_zero] using hasGevrey1Asymp_congr (fun _ _ ↦ rfl)
      (fun _ ↦ rfl) (hasGevrey1Asymp_const S 1)
  | succ k ih =>
    have hmul := hasGevrey1Asymp_mul hS ih hf
    refine hasGevrey1Asymp_congr (fun u _ ↦ by rw [pow_succ]) (fun n ↦ ?_) hmul
    rw [pow_succ, PowerSeries.coeff_mul]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦ (p ^ k).coeff a * p.coeff b) n).symm

/-- Helper: `HasGevrey1Asymp` closure under `Finset.prod`. -/
private lemma hasGevrey1Asymp_finset_prod {ι : Type*} [DecidableEq ι]
    {S : Set ℂ} (hS : ∀ ε : ℝ, 0 < ε → ∃ u ∈ S, 0 < ‖u‖ ∧ ‖u‖ < ε)
    (s : Finset ι) (f : ι → ℂ → ℂ) (p : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, HasGevrey1Asymp S (f i) (fun n ↦ (p i).coeff n)) :
    HasGevrey1Asymp S (fun u ↦ ∏ i ∈ s, f i u) (fun n ↦ (∏ i ∈ s, p i).coeff n) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasGevrey1Asymp_congr (fun _ _ ↦ rfl)
      (fun _ ↦ rfl) (hasGevrey1Asymp_const S 1)
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    have hmul := hasGevrey1Asymp_mul hS h1 h2
    refine hasGevrey1Asymp_congr (fun u _ ↦ by rw [Finset.prod_insert ha]) (fun n ↦ ?_) hmul
    rw [Finset.prod_insert ha, PowerSeries.coeff_mul]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ (p a).coeff i * (∏ x ∈ s, p x).coeff j) n).symm

/-- Helper: `HasGevrey1Asymp` closure under `Finset.sum`. -/
private lemma hasGevrey1Asymp_finset_sum {ι : Type*} [DecidableEq ι] {S : Set ℂ}
    (s : Finset ι) (f : ι → ℂ → ℂ) (p : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, HasGevrey1Asymp S (f i) (fun n ↦ (p i).coeff n)) :
    HasGevrey1Asymp S (fun u ↦ ∑ i ∈ s, f i u) (fun n ↦ (∑ i ∈ s, p i).coeff n) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasGevrey1Asymp_congr (fun _ _ ↦ rfl)
      (fun n ↦ by simp) (hasGevrey1Asymp_const S 0)
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    have hadd := hasGevrey1Asymp_add h1 h2
    refine hasGevrey1Asymp_congr (fun u _ ↦ by rw [Finset.sum_insert ha]) (fun n ↦ ?_) hadd
    rw [Finset.sum_insert ha, map_add]

/-- Helper: `HasRealAsymp` closure under `const`, `add`, `mul`, `pow`, `Finset.prod`, `Finset.sum`. -/
private lemma hasRealAsymp_const' {u₀ : ℝ} (c : ℂ) :
    HasRealAsymp u₀ (fun _ ↦ c) (fun n ↦ if n = 0 then c else 0) := fun N ↦ by
  cases N with
  | zero => exact ⟨‖c‖, norm_nonneg _, fun _ _ ↦ by simp⟩
  | succ N =>
    refine ⟨0, le_rfl, fun u _ ↦ ?_⟩
    rw [Finset.sum_eq_single 0]
    · simp
    · intro n _ hn0; simp [hn0]
    · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) hnot

private lemma hasRealAsymp_add {u₀ : ℝ} {f₁ f₂ : ℝ → ℂ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : HasRealAsymp u₀ f₁ a₁) (h₂ : HasRealAsymp u₀ f₂ a₂) :
    HasRealAsymp u₀ (fun x ↦ f₁ x + f₂ x) (fun n ↦ a₁ n + a₂ n) := fun N ↦ by
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁ N
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂ N
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun x hx ↦ ?_⟩
  have h1 := hb₁ x hx; have h2 := hb₂ x hx
  have heq : f₁ x + f₂ x - ∑ n ∈ Finset.range N, (a₁ n + a₂ n) * (x : ℂ) ^ n =
      (f₁ x - ∑ n ∈ Finset.range N, a₁ n * (x : ℂ) ^ n) +
      (f₂ x - ∑ n ∈ Finset.range N, a₂ n * (x : ℂ) ^ n) := by
    simp only [add_mul, Finset.sum_add_distrib]; ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

private lemma hasRealAsymp_mul {u₀ : ℝ} (_hu₀ : 0 < u₀) {f₁ f₂ : ℝ → ℂ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : HasRealAsymp u₀ f₁ a₁) (h₂ : HasRealAsymp u₀ f₂ a₂) :
    HasRealAsymp u₀ (fun x ↦ f₁ x * f₂ x)
      (fun m ↦ ∑ p ∈ Finset.range (m + 1), a₁ p * a₂ (m - p)) := fun N ↦ by
  obtain ⟨C₀, hC₀, hb₂0⟩ := h₂ 0
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁ N
  have h₂_all : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ioo (0 : ℝ) u₀,
      ‖f₂ x - ∑ q ∈ Finset.range (N - p), a₂ q * (x : ℂ) ^ q‖ ≤ C * x ^ (N - p) :=
    fun p ↦ h₂ (N - p)
  choose C₂ hC₂ hb₂ using h₂_all
  refine ⟨C₁ * C₀ + ∑ p ∈ Finset.range N, ‖a₁ p‖ * C₂ p,
    add_nonneg (mul_nonneg hC₁ hC₀) (Finset.sum_nonneg fun p _ ↦ mul_nonneg (norm_nonneg _) (hC₂ p)),
    fun x hx ↦ ?_⟩
  let R₁ := f₁ x - ∑ p ∈ Finset.range N, a₁ p * (x : ℂ) ^ p
  let R₂ : ℕ → ℂ := fun M ↦ f₂ x - ∑ q ∈ Finset.range M, a₂ q * (x : ℂ) ^ q
  have hident : f₁ x * f₂ x -
      ∑ m ∈ Finset.range N, (∑ p ∈ Finset.range (m + 1), a₁ p * a₂ (m - p)) * (x : ℂ) ^ m =
      R₁ * f₂ x + ∑ p ∈ Finset.range N, a₁ p * (x : ℂ) ^ p * R₂ (N - p) := by
    have hsum_eq : ∑ p ∈ Finset.range N, a₁ p * (x : ℂ) ^ p * (∑ q ∈ Finset.range (N - p), a₂ q * (x : ℂ) ^ q) =
        ∑ m ∈ Finset.range N, (∑ p ∈ Finset.range (m + 1), a₁ p * a₂ (m - p)) * (x : ℂ) ^ m := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij (fun y ↦ ⟨y.1 + y.2, y.1⟩) ?_ ?_ ?_ ?_
      · intro ⟨p, q⟩ h; simp only [Finset.mem_sigma, Finset.mem_range] at h ⊢; omega
      · intro ⟨p₁, q₁⟩ _ ⟨p₂, q₂⟩ _ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        obtain ⟨hsum, hp⟩ := heq; subst hp; congr 1; omega
      · intro ⟨m, p⟩ h
        have hmp := Finset.mem_sigma.mp h
        have hm : m < N := Finset.mem_range.mp hmp.1
        have hp : p < m + 1 := Finset.mem_range.mp hmp.2
        refine ⟨⟨p, m - p⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by dsimp; omega),
          Finset.mem_range.mpr (by dsimp; omega)⟩, ?_⟩
        refine Sigma.ext (by dsimp; omega) (by simp)
      · intro ⟨p, q⟩ _; dsimp; rw [Nat.add_sub_cancel_left, pow_add]; ring
    have hR₂ : ∑ p ∈ Finset.range N, a₁ p * (x : ℂ) ^ p * R₂ (N - p) =
        (∑ p ∈ Finset.range N, a₁ p * (x : ℂ) ^ p) * f₂ x -
          ∑ p ∈ Finset.range N, a₁ p * (x : ℂ) ^ p * (∑ q ∈ Finset.range (N - p), a₂ q * (x : ℂ) ^ q) := by
      simp only [R₂, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hR₂, hsum_eq]; dsimp [R₁]; ring
  rw [hident]
  have hx_pos : 0 < x := hx.1
  have ht1 : ‖R₁ * f₂ x‖ ≤ C₁ * C₀ * x ^ N := by
    rw [norm_mul]
    have h1 := hb₁ x hx
    have h2 : ‖f₂ x‖ ≤ C₀ := by simpa using hb₂0 x hx
    calc ‖R₁‖ * ‖f₂ x‖ ≤ (C₁ * x ^ N) * C₀ := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C₁ * C₀ * x ^ N := by ring
  have ht2 : ‖∑ p ∈ Finset.range N, a₁ p * (x : ℂ) ^ p * R₂ (N - p)‖ ≤
      (∑ p ∈ Finset.range N, ‖a₁ p‖ * C₂ p) * x ^ N := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    have hlt : p < N := Finset.mem_range.mp hp
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
    have h2 := hb₂ p x hx
    calc ‖a₁ p‖ * x ^ p * ‖R₂ (N - p)‖
        ≤ ‖a₁ p‖ * x ^ p * (C₂ p * x ^ (N - p)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ‖a₁ p‖ * C₂ p * (x ^ p * x ^ (N - p)) := by ring
      _ = ‖a₁ p‖ * C₂ p * x ^ N := by rw [← pow_add, Nat.add_sub_of_le hlt.le]
  exact (norm_add_le _ _).trans (by linarith)

private lemma hasRealAsymp_pow {u₀ : ℝ} (hu₀ : 0 < u₀) {f : ℝ → ℂ} {p : PowerSeries ℂ}
    (hf : HasRealAsymp u₀ f (fun n ↦ p.coeff n)) (k : ℕ) :
    HasRealAsymp u₀ (fun x ↦ (f x) ^ k) (fun n ↦ (p ^ k).coeff n) := by
  induction k with
  | zero =>
    intro N
    obtain ⟨C, hC, hb⟩ := hasRealAsymp_const' (u₀ := u₀) (1 : ℂ) N
    refine ⟨C, hC, fun x hx ↦ ?_⟩
    simpa [PowerSeries.coeff_one] using hb x hx
  | succ k ih =>
    intro N
    obtain ⟨C, hC, hb⟩ := hasRealAsymp_mul hu₀ ih hf N
    refine ⟨C, hC, fun x hx ↦ ?_⟩
    have hsum : ∑ n ∈ Finset.range N, (p ^ (k + 1)).coeff n * (x : ℂ) ^ n =
        ∑ n ∈ Finset.range N, (∑ m ∈ Finset.range (n + 1), (p ^ k).coeff m * p.coeff (n - m)) * (x : ℂ) ^ n := by
      apply Finset.sum_congr rfl; intro n _
      rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦ (p ^ k).coeff a * p.coeff b) n]
    have hb' := hb x hx
    rw [← hsum] at hb'
    simpa only [pow_succ] using hb'

private lemma hasRealAsymp_finset_prod {ι : Type*} [DecidableEq ι] {u₀ : ℝ} (hu₀ : 0 < u₀)
    (s : Finset ι) (f : ι → ℝ → ℂ) (p : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, HasRealAsymp u₀ (f i) (fun n ↦ (p i).coeff n)) :
    HasRealAsymp u₀ (fun x ↦ ∏ i ∈ s, f i x) (fun n ↦ (∏ i ∈ s, p i).coeff n) := by
  induction s using Finset.induction_on with
  | empty =>
    intro N
    obtain ⟨C, hC, hb⟩ := hasRealAsymp_const' (u₀ := u₀) (1 : ℂ) N
    refine ⟨C, hC, fun x hx ↦ ?_⟩
    simpa [PowerSeries.coeff_one] using hb x hx
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    intro N
    obtain ⟨C, hC, hb⟩ := hasRealAsymp_mul hu₀ h1 h2 N
    refine ⟨C, hC, fun x hx ↦ ?_⟩
    have hsum : ∑ n ∈ Finset.range N, (∏ i ∈ insert a s, p i).coeff n * (x : ℂ) ^ n =
        ∑ n ∈ Finset.range N, (∑ m ∈ Finset.range (n + 1), (p a).coeff m * (∏ i ∈ s, p i).coeff (n - m)) * (x : ℂ) ^ n := by
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.prod_insert ha, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ (p a).coeff i * (∏ x ∈ s, p x).coeff j) n]
    have hb' := hb x hx
    rw [← hsum] at hb'
    simpa only [Finset.prod_insert ha] using hb'

private lemma hasRealAsymp_finset_sum {ι : Type*} [DecidableEq ι] {u₀ : ℝ}
    (s : Finset ι) (f : ι → ℝ → ℂ) (p : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, HasRealAsymp u₀ (f i) (fun n ↦ (p i).coeff n)) :
    HasRealAsymp u₀ (fun x ↦ ∑ i ∈ s, f i x) (fun n ↦ (∑ i ∈ s, p i).coeff n) := by
  induction s using Finset.induction_on with
  | empty =>
    intro N; exact ⟨0, le_rfl, fun _ _ ↦ by simp⟩
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    intro N
    obtain ⟨C, hC, hb⟩ := hasRealAsymp_add h1 h2 N
    refine ⟨C, hC, fun x hx ↦ ?_⟩
    simpa [Finset.sum_insert ha, map_add] using hb x hx

/-- `HasRealAsymp` for evaluating `evalAtConv x Q` at a jet `Y : ι → ℝ → ℂ` with real asymptotics `Yhat`! -/
theorem evalAtConv_hasRealAsymp {ι : Type*} [DecidableEq ι]
    {ρ M x₀ : ℝ} (hx₀_pos : 0 < x₀) (hx₀_le : x₀ ≤ ρ / 2)
    (Q : MvPolynomial ι convergentSubring)
    (hQ_conv : ∀ m : ι →₀ ℕ, IsConvergentOn ρ M (Q.coeff m).val)
    {Y : ι → ℝ → ℂ} {Yhat : ι → PowerSeries ℂ}
    (hY : ∀ i, HasRealAsymp x₀ (Y i) (fun n ↦ (Yhat i).coeff n)) :
    HasRealAsymp x₀ (fun x : ℝ ↦ MvPolynomial.aeval (fun i ↦ Y i x) (evalAtConv (x : ℂ) Q))
      (fun n ↦ (MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype Q)).coeff n) := by
  have hQ_eq : MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype Q) =
      ∑ m ∈ Q.support, (Q.coeff m).val * ∏ i ∈ m.support, (Yhat i) ^ (m i) := by
    conv_lhs => rw [Q.as_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, Algebra.algebraMap_self,
        RingHom.id_apply, Finsupp.prod]; rfl
  have hterm : ∀ m ∈ Q.support,
      HasRealAsymp x₀ (fun x : ℝ ↦ psEval (Q.coeff m).val (x : ℂ) * ∏ i ∈ m.support, (Y i x) ^ (m i))
        (fun n ↦ ((Q.coeff m).val * ∏ i ∈ m.support, (Yhat i) ^ (m i)).coeff n) := by
    intro m _
    have hps_gev := hasGevrey1Asymp_psEval (hQ_conv m)
    have hps_real : HasRealAsymp x₀ (fun x : ℝ ↦ psEval (Q.coeff m).val (x : ℂ))
        (fun n ↦ (Q.coeff m).val.coeff n) :=
      hasRealAsymp_of_hasGevrey1Asymp (fun x hx ↦ by
        change ‖(x : ℂ)‖ ≤ ρ / 2
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
        linarith [hx.2]) hps_gev
    have hprod := hasRealAsymp_finset_prod hx₀_pos m.support (fun i x ↦ (Y i x) ^ (m i))
      (fun i ↦ (Yhat i) ^ (m i)) (fun i _ ↦ hasRealAsymp_pow hx₀_pos (hY i) (m i))
    intro N
    obtain ⟨C, hC, hb⟩ := hasRealAsymp_mul hx₀_pos hps_real hprod N
    refine ⟨C, hC, fun x hx ↦ ?_⟩
    have hsum : ∑ n ∈ Finset.range N, ((Q.coeff m).val * ∏ i ∈ m.support, (Yhat i) ^ (m i)).coeff n * (x : ℂ) ^ n =
        ∑ n ∈ Finset.range N, (∑ p ∈ Finset.range (n + 1),
          (Q.coeff m).val.coeff p * (∏ i ∈ m.support, (Yhat i) ^ (m i)).coeff (n - p)) * (x : ℂ) ^ n := by
      apply Finset.sum_congr rfl; intro n _
      rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b ↦ (Q.coeff m).val.coeff a * (∏ i ∈ m.support, (Yhat i) ^ (m i)).coeff b) n]
    simpa [hsum] using hb x hx
  have hsum := hasRealAsymp_finset_sum Q.support
    (fun m x ↦ psEval (Q.coeff m).val (x : ℂ) * ∏ i ∈ m.support, (Y i x) ^ (m i))
    (fun m ↦ (Q.coeff m).val * ∏ i ∈ m.support, (Yhat i) ^ (m i)) hterm
  intro N
  obtain ⟨C, hC, hb⟩ := hsum N
  refine ⟨C, hC, fun x hx ↦ ?_⟩
  dsimp only
  rw [aeval_evalAtConv, hQ_eq]
  exact hb x hx

/-- **Lemma 5.1(b) Bridge for Convergent Polynomial Relations**:
If `R ∈ MvPolynomial (Fin s × Fin (r + 1)) convergentSubring` annihilates the formal jet
`Yhat (i, j) = PowerSeries.mk (fun n ↦ (-1)^{n + j} phiFormalCoeff (k i) (b i) j n)`,
then on `x ∈ (0, x₀)` (where `x₀ := min (ρ_R / 2) (1 / 4)`), BOTH lateral rotated-ray jets
`YPlus x` and `YMinus x` vanish under `evalAtConv x R`:
`MvPolynomial.aeval (YPlus x) (evalAtConv x R) = 0 ∧ MvPolynomial.aeval (YMinus x) (evalAtConv x R) = 0`! -/
theorem mvPoly_conv_lateral_simultaneous_annihilation {s r : ℕ}
    (k : Fin s → ℂ) (b : Fin s → ℂ → ℂ) (C_b c_b : Fin s → ℝ)
    (hb : ∀ i, ExpDecayKernel (b i) (C_b i) (c_b i))
    (R : MvPolynomial (Fin s × Fin (r + 1)) convergentSubring)
    {ρ M : ℝ} (hρ_pos : 0 < ρ)
    (hR_conv : ∀ m : (Fin s × Fin (r + 1)) →₀ ℕ, IsConvergentOn ρ M (R.coeff m).val)
    (hR_ann : MvPolynomial.aeval
      (fun p : Fin s × Fin (r + 1) ↦
        PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n))
      (MvPolynomial.map convergentSubring.subtype R) = 0) :
    let x₀ : ℝ := min (ρ / 2) (1 / 4)
    ∀ x ∈ Set.Ioo (0 : ℝ) x₀,
      MvPolynomial.aeval (fun p : Fin s × Fin (r + 1) ↦
          iteratedDeriv p.2.val (fun t : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(t : ℂ))) x)
        (evalAtConv (x : ℂ) R) = 0 ∧
      MvPolynomial.aeval (fun p : Fin s × Fin (r + 1) ↦
          iteratedDeriv p.2.val (fun t : ℝ ↦ PhiMinus (k p.1) (b p.1) (-(t : ℂ))) x)
        (evalAtConv (x : ℂ) R) = 0 := by
  intro x₀
  have hx₀_pos : 0 < x₀ := lt_min (by linarith) (by norm_num)
  have hx₀_le_quarter : x₀ ≤ 1 / 4 := min_le_right _ _
  have hx₀_le_half : x₀ ≤ ρ / 2 := min_le_left _ _
  have hx₀_lt_ρ : x₀ < ρ := lt_of_le_of_lt hx₀_le_half (by linarith)
  -- Define `F`, `Fp`, `Fm` on `u`-plane via `evalAtConv (-u) R` and `(-1)^j Φ_i^{(j)}(u)`!
  let F : ℂ → ℂ := fun u ↦
    MvPolynomial.aeval (fun p : Fin s × Fin (r + 1) ↦
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiReal (k p.1) (b p.1)) u)
      (evalAtConv (-u) R)
  let Fp : ℂ → ℂ := fun u ↦
    MvPolynomial.aeval (fun p : Fin s × Fin (r + 1) ↦
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiPlus (k p.1) (b p.1)) u)
      (evalAtConv (-u) R)
  let Fm : ℂ → ℂ := fun u ↦
    MvPolynomial.aeval (fun p : Fin s × Fin (r + 1) ↦
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiMinus (k p.1) (b p.1)) u)
      (evalAtConv (-u) R)
  -- Holomorphy of `u ↦ psEval (R.coeff m).val (-u)` on `Metric.ball 0 ρ`:
  have hps_neg_diff : ∀ m, DifferentiableOn ℂ (fun u : ℂ ↦ psEval (R.coeff m).val (-u)) (Metric.ball 0 ρ) := by
    intro m u hu
    have hneg_mem : -u ∈ Metric.ball (0 : ℂ) ρ := by simpa [Metric.mem_ball] using hu
    have hd1 := (psEval_differentiableOn (hR_conv m) (-u) hneg_mem).differentiableAt
      (Metric.isOpen_ball.mem_nhds hneg_mem)
    exact (hd1.comp u differentiableAt_id.neg).differentiableWithinAt
  have hF_diff : DifferentiableOn ℂ F (slitDisk ρ) := by
    have hsub : slitDisk ρ ⊆ Metric.ball 0 ρ := fun u hu ↦ by
      simpa [Metric.mem_ball, dist_zero_right] using hu.2.1
    have hsub_slit : slitDisk ρ ⊆ Complex.slitPlane := fun u hu ↦ hu.2.2
    have hEq : F = fun u ↦ ∑ m ∈ R.support, psEval (R.coeff m).val (-u) *
        ∏ p ∈ m.support, ((-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiReal (k p.1) (b p.1)) u) ^ (m p) := by
      ext u; exact aeval_evalAtConv (-u) R _
    rw [hEq]
    refine DifferentiableOn.fun_sum fun m _ ↦
      ((hps_neg_diff m).mono hsub).mul (differentiableOn_finset_prod fun p _ ↦
        (((PhiReal_iteratedDeriv (hb p.1) (k p.1) p.2.val).1.mono hsub_slit).const_mul _).pow _)
  have hFp_diff : DifferentiableOn ℂ Fp (UPlus x₀) := by
    have hsub : UPlus x₀ ⊆ Metric.ball 0 ρ := fun u hu ↦ by
      rw [Metric.mem_ball, dist_zero_right]; exact lt_trans hu.2.1 hx₀_lt_ρ
    have hEq : Fp = fun u ↦ ∑ m ∈ R.support, psEval (R.coeff m).val (-u) *
        ∏ p ∈ m.support, ((-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiPlus (k p.1) (b p.1)) u) ^ (m p) := by
      ext u; exact aeval_evalAtConv (-u) R _
    rw [hEq]
    refine DifferentiableOn.fun_sum fun m _ ↦
      ((hps_neg_diff m).mono hsub).mul (differentiableOn_finset_prod fun p _ ↦
        (((PhiPlus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) p.2.val).1).const_mul _).pow _)
  have hFm_diff : DifferentiableOn ℂ Fm (UMinus x₀) := by
    have hsub : UMinus x₀ ⊆ Metric.ball 0 ρ := fun u hu ↦ by
      rw [Metric.mem_ball, dist_zero_right]; exact lt_trans hu.2.1 hx₀_lt_ρ
    have hEq : Fm = fun u ↦ ∑ m ∈ R.support, psEval (R.coeff m).val (-u) *
        ∏ p ∈ m.support, ((-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiMinus (k p.1) (b p.1)) u) ^ (m p) := by
      ext u; exact aeval_evalAtConv (-u) R _
    rw [hEq]
    refine DifferentiableOn.fun_sum fun m _ ↦
      ((hps_neg_diff m).mono hsub).mul (differentiableOn_finset_prod fun p _ ↦
        (((PhiMinus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) p.2.val).1).const_mul _).pow _)
  -- Overlap agreement `Fp x = F x` and `Fm x = F x` on `x ∈ (0, x₀)`!
  have hoverlap_iter : ∀ (i : Fin s) (j : ℕ), ∀ x ∈ Set.Ioo (0 : ℝ) x₀,
      iteratedDeriv j (PhiPlus (k i) (b i)) (x : ℂ) = iteratedDeriv j (PhiReal (k i) (b i)) (x : ℂ) ∧
      iteratedDeriv j (PhiMinus (k i) (b i)) (x : ℂ) = iteratedDeriv j (PhiReal (k i) (b i)) (x : ℂ) := by
    intro i j x hx
    -- Use `PhiPlus = PhiReal` on `(0, x₀)` + Identity Theorem on open ball around `(x : ℂ)` inside `UPlus x₀ ∩ slitPlane`!
    have hball_ex : ∃ δ : ℝ, 0 < δ ∧
        Metric.ball (x : ℂ) δ ⊆ UPlus x₀ ∧ Metric.ball (x : ℂ) δ ⊆ UMinus x₀ ∧
        Metric.ball (x : ℂ) δ ⊆ Complex.slitPlane := by
      have h1 := Metric.isOpen_iff.mp (isOpen_UPlus x₀) (x : ℂ) (ofReal_mem_UPlus hx.1 hx.2)
      have h2 := Metric.isOpen_iff.mp (isOpen_UMinus x₀) (x : ℂ) (ofReal_mem_UMinus hx.1 hx.2)
      have h3 := Metric.isOpen_iff.mp Complex.isOpen_slitPlane (x : ℂ)
        (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hx.1)))
      obtain ⟨δ₁, hδ₁, hb₁⟩ := h1
      obtain ⟨δ₂, hδ₂, hb₂⟩ := h2
      obtain ⟨δ₃, hδ₃, hb₃⟩ := h3
      let δ := min δ₁ (min δ₂ (min δ₃ (min (x / 2) ((x₀ - x) / 2))))
      refine ⟨δ, lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ (lt_min (by linarith [hx.1]) (by linarith [hx.2])))),
        (Metric.ball_subset_ball (min_le_left _ _)).trans hb₁,
        (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))).trans hb₂,
        (Metric.ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).trans hb₃⟩
    obtain ⟨δ, hδ_pos, hbP, hbM, hbS⟩ := hball_ex
    have hAnR : AnalyticOnNhd ℂ (PhiReal (k i) (b i)) (Metric.ball (x : ℂ) δ) :=
      ((PhiReal_iteratedDeriv (hb i) (k i) 0).1.mono hbS).analyticOnNhd Metric.isOpen_ball
    have hAnP : AnalyticOnNhd ℂ (PhiPlus (k i) (b i)) (Metric.ball (x : ℂ) δ) :=
      ((PhiPlus_iteratedDeriv (hb i) hx₀_le_quarter (k i) 0).1.mono hbP).analyticOnNhd Metric.isOpen_ball
    have hAnM : AnalyticOnNhd ℂ (PhiMinus (k i) (b i)) (Metric.ball (x : ℂ) δ) :=
      ((PhiMinus_iteratedDeriv (hb i) hx₀_le_quarter (k i) 0).1.mono hbM).analyticOnNhd Metric.isOpen_ball
    have hfreqP : ∃ᶠ z in 𝓝[≠] (x : ℂ), PhiPlus (k i) (b i) z = PhiReal (k i) (b i) z := by
      rw [Filter.frequently_iff]; intro U hU
      rw [mem_nhdsWithin] at hU
      obtain ⟨V, hVopen, hxV, hVsub⟩ := hU
      obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hVopen (x : ℂ) hxV
      let t : ℝ := x + min (ε / 2) ((x₀ - x) / 2)
      have ht_pos : 0 < t := by dsimp [t]; linarith [hx.1, lt_min (by linarith : 0 < ε / 2) (by linarith [hx.2] : 0 < (x₀ - x) / 2)]
      have ht_ne : (t : ℂ) ≠ (x : ℂ) := fun h0 ↦ by
        have := Complex.ofReal_injective h0; dsimp [t] at this
        linarith [lt_min (by linarith : 0 < ε / 2) (by linarith [hx.2] : 0 < (x₀ - x) / 2)]
      have ht_ball : (t : ℂ) ∈ Metric.ball (x : ℂ) ε := by
        rw [Metric.mem_ball, Complex.dist_eq, show (t : ℂ) - (x : ℂ) = ((min (ε / 2) ((x₀ - x) / 2) : ℝ) : ℂ) by
          dsimp [t]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (lt_min (by linarith) (by linarith [hx.2]))]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      exact ⟨(t : ℂ), hVsub ⟨hball ht_ball, ht_ne⟩, (PhiPlus_PhiMinus_eq_PhiReal_of_pos (hb i) (k i) ht_pos).1⟩
    have hfreqM : ∃ᶠ z in 𝓝[≠] (x : ℂ), PhiMinus (k i) (b i) z = PhiReal (k i) (b i) z := by
      rw [Filter.frequently_iff]; intro U hU
      rw [mem_nhdsWithin] at hU
      obtain ⟨V, hVopen, hxV, hVsub⟩ := hU
      obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hVopen (x : ℂ) hxV
      let t : ℝ := x + min (ε / 2) ((x₀ - x) / 2)
      have ht_pos : 0 < t := by dsimp [t]; linarith [hx.1, lt_min (by linarith : 0 < ε / 2) (by linarith [hx.2] : 0 < (x₀ - x) / 2)]
      have ht_ne : (t : ℂ) ≠ (x : ℂ) := fun h0 ↦ by
        have := Complex.ofReal_injective h0; dsimp [t] at this
        linarith [lt_min (by linarith : 0 < ε / 2) (by linarith [hx.2] : 0 < (x₀ - x) / 2)]
      have ht_ball : (t : ℂ) ∈ Metric.ball (x : ℂ) ε := by
        rw [Metric.mem_ball, Complex.dist_eq, show (t : ℂ) - (x : ℂ) = ((min (ε / 2) ((x₀ - x) / 2) : ℝ) : ℂ) by
          dsimp [t]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (lt_min (by linarith) (by linarith [hx.2]))]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      exact ⟨(t : ℂ), hVsub ⟨hball ht_ball, ht_ne⟩, (PhiPlus_PhiMinus_eq_PhiReal_of_pos (hb i) (k i) ht_pos).2⟩
    have heqP : Set.EqOn (PhiPlus (k i) (b i)) (PhiReal (k i) (b i)) (Metric.ball (x : ℂ) δ) :=
      hAnP.eqOn_of_preconnected_of_frequently_eq hAnR (convex_ball _ _).isPreconnected
        (Metric.mem_ball_self hδ_pos) hfreqP
    have heqM : Set.EqOn (PhiMinus (k i) (b i)) (PhiReal (k i) (b i)) (Metric.ball (x : ℂ) δ) :=
      hAnM.eqOn_of_preconnected_of_frequently_eq hAnR (convex_ball _ _).isPreconnected
        (Metric.mem_ball_self hδ_pos) hfreqM
    have hevP : PhiPlus (k i) (b i) =ᶠ[𝓝 (x : ℂ)] PhiReal (k i) (b i) :=
      Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (x : ℂ) hδ_pos) heqP
    have hevM : PhiMinus (k i) (b i) =ᶠ[𝓝 (x : ℂ)] PhiReal (k i) (b i) :=
      Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (x : ℂ) hδ_pos) heqM
    exact ⟨hevP.iteratedDeriv_eq j, hevM.iteratedDeriv_eq j⟩
  have hFp_eq : ∀ x ∈ Set.Ioo (0 : ℝ) x₀, Fp (x : ℂ) = F (x : ℂ) := fun x hx ↦ by
    have harg : (fun p : Fin s × Fin (r + 1) ↦
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiPlus (k p.1) (b p.1)) (x : ℂ)) =
        fun p : Fin s × Fin (r + 1) ↦
          (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiReal (k p.1) (b p.1)) (x : ℂ) :=
      funext fun p ↦ by rw [(hoverlap_iter p.1 p.2.val x hx).1]
    dsimp [Fp, F]; rw [harg]
  have hFm_eq : ∀ x ∈ Set.Ioo (0 : ℝ) x₀, Fm (x : ℂ) = F (x : ℂ) := fun x hx ↦ by
    have harg : (fun p : Fin s × Fin (r + 1) ↦
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiMinus (k p.1) (b p.1)) (x : ℂ)) =
        fun p : Fin s × Fin (r + 1) ↦
          (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiReal (k p.1) (b p.1)) (x : ℂ) :=
      funext fun p ↦ by rw [(hoverlap_iter p.1 p.2.val x hx).2]
    dsimp [Fm, F]; rw [harg]
  -- Gevrey-1 zero formal expansion of `F` on `sector34 x₀` using `negPowerSeriesHom`!
  have hF_gev0 : HasGevrey1Asymp (sector34 x₀) F (fun _ ↦ 0) := by
    have hS_acc : ∀ ε : ℝ, 0 < ε → ∃ u ∈ sector34 x₀, 0 < ‖u‖ ∧ ‖u‖ < ε := by
      intro ε hε
      let t : ℝ := min (x₀ / 2) (ε / 2)
      have ht_pos : 0 < t := lt_min (by linarith) (by linarith)
      refine ⟨(t : ℂ), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]; exact ht_pos
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact (min_le_left _ _).trans (by linarith)
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos, Complex.ofReal_re]
        have : 0 ≤ Real.sqrt 2 / 2 * t := by positivity
        linarith
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]; exact ht_pos
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact (min_le_right _ _).trans_lt (by linarith)
    let Zhat : Fin s × Fin (r + 1) → PowerSeries ℂ := fun p ↦
      PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ p.2.val * phiFormalCoeff (k p.1) (b p.1) p.2.val n)
    have hZ_gev : ∀ p : Fin s × Fin (r + 1),
        HasGevrey1Asymp (sector34 x₀)
          (fun u ↦ (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiReal (k p.1) (b p.1)) u)
          (fun n ↦ (Zhat p).coeff n) := fun p ↦ by
      have h1 := hasGevrey1Asymp_const_mul ((-1 : ℂ) ^ p.2.val)
        (PhiReal_iteratedDeriv_hasGevrey1Asymp (hb p.1) (k p.1) p.2.val hx₀_pos)
      exact hasGevrey1Asymp_congr (fun _ _ ↦ rfl) (fun n ↦ by simp [Zhat]) h1
    have hps_gev : ∀ m, HasGevrey1Asymp (sector34 x₀) (fun u ↦ psEval (R.coeff m).val (-u))
        (fun n ↦ (negPowerSeriesHom (R.coeff m).val).coeff n) := fun m ↦ by
      obtain ⟨C, B, hC, hB, hbd⟩ := hasGevrey1Asymp_psEval (hR_conv m)
      refine ⟨C, B, hC, hB, fun N u hu ↦ ?_⟩
      have hneg_mem : -u ∈ {z : ℂ | ‖z‖ ≤ ρ / 2} := by
        change ‖-u‖ ≤ ρ / 2
        rw [norm_neg]
        exact hu.2.1.trans hx₀_le_half
      have h1 := hbd N (-u) hneg_mem
      rw [norm_neg] at h1
      have hsum_eq : ∑ n ∈ Finset.range N, (negPowerSeriesHom (R.coeff m).val).coeff n * u ^ n =
          ∑ n ∈ Finset.range N, (R.coeff m).val.coeff n * (-u) ^ n := by
        apply Finset.sum_congr rfl; intro n _
        rw [negPowerSeriesHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
            PowerSeries.coeff_mk, show (-u) ^ n = (-1 : ℂ) ^ n * u ^ n by rw [← mul_pow]; simp]
        ring
      rw [hsum_eq]; exact h1
    have hterm_gev : ∀ m ∈ R.support,
        HasGevrey1Asymp (sector34 x₀)
          (fun u ↦ psEval (R.coeff m).val (-u) *
            ∏ p ∈ m.support, ((-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiReal (k p.1) (b p.1)) u) ^ (m p))
          (fun n ↦ (negPowerSeriesHom (R.coeff m).val * ∏ p ∈ m.support, (Zhat p) ^ (m p)).coeff n) := by
      intro m _
      have hprod := hasGevrey1Asymp_finset_prod hS_acc m.support
        (fun p u ↦ ((-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiReal (k p.1) (b p.1)) u) ^ (m p))
        (fun p ↦ (Zhat p) ^ (m p)) (fun p _ ↦ hasGevrey1Asymp_pow hS_acc (hZ_gev p) (m p))
      have hmul := hasGevrey1Asymp_mul hS_acc (hps_gev m) hprod
      exact hasGevrey1Asymp_congr (fun _ _ ↦ rfl)
        (fun n ↦ by
          rw [PowerSeries.coeff_mul]
          exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b ↦ (negPowerSeriesHom (R.coeff m).val).coeff a *
              (∏ p ∈ m.support, (Zhat p) ^ (m p)).coeff b) n).symm) hmul
    have hsum_gev := hasGevrey1Asymp_finset_sum R.support _ _ hterm_gev
    -- Show `∑ m ∈ R.support, negPowerSeriesHom (R.coeff m).val * ∏ (Zhat p)^(m p) = negPowerSeriesHom 0 = 0`!
    have hformal_zero : ∑ m ∈ R.support, negPowerSeriesHom (R.coeff m).val * ∏ p ∈ m.support, (Zhat p) ^ (m p) = 0 := by
      have hZhat_neg : ∀ p : Fin s × Fin (r + 1),
          Zhat p = negPowerSeriesHom (PowerSeries.mk
            (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n)) := by
        intro p; ext n
        simp only [Zhat, negPowerSeriesHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          PowerSeries.coeff_mk]
        rw [← mul_assoc, ← pow_add, show n + (n + p.2.val) = 2 * n + p.2.val by omega,
            pow_add, pow_mul]; simp
      have hcomm : ∑ m ∈ R.support, negPowerSeriesHom (R.coeff m).val * ∏ p ∈ m.support, (Zhat p) ^ (m p) =
          negPowerSeriesHom (MvPolynomial.aeval
            (fun p : Fin s × Fin (r + 1) ↦
              PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n))
            (MvPolynomial.map convergentSubring.subtype R)) := by
        conv_rhs => rw [R.as_sum, map_sum, map_sum, map_sum]
        apply Finset.sum_congr rfl; intro m _
        rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, Algebra.algebraMap_self,
            RingHom.id_apply, map_mul, Finsupp.prod, map_prod]
        congr 1; apply Finset.prod_congr rfl; intro p _
        rw [map_pow, hZhat_neg p]
      rw [hcomm, hR_ann, map_zero]
    refine hasGevrey1Asymp_congr (fun u _ ↦ (aeval_evalAtConv (-u) R _).symm) (fun n ↦ ?_) hsum_gev
    rw [hformal_zero, map_zero]
  -- Apply `lateral_simultaneous_annihilation` (`Lemma 5.1(b)`)!
  have hlat := (lateral_simultaneous_annihilation hx₀_pos hx₀_lt_ρ hF_diff hF_gev0 hFp_diff hFm_diff hFp_eq hFm_eq).2.2
  intro x hx
  have ⟨hFp0, hFm0⟩ := hlat x hx
  have hiterP : (fun p : Fin s × Fin (r + 1) ↦
        iteratedDeriv p.2.val (fun t : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(t : ℂ))) x) =
      fun p : Fin s × Fin (r + 1) ↦
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiPlus (k p.1) (b p.1)) (-(x : ℂ)) :=
    funext fun p ↦
      iteratedDeriv_comp_neg_ofReal (isOpen_UPlus x₀) (PhiPlus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) 0).1
        p.2.val x (neg_ofReal_mem_UPlus hx.1 hx.2)
  have hiterM : (fun p : Fin s × Fin (r + 1) ↦
        iteratedDeriv p.2.val (fun t : ℝ ↦ PhiMinus (k p.1) (b p.1) (-(t : ℂ))) x) =
      fun p : Fin s × Fin (r + 1) ↦
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (PhiMinus (k p.1) (b p.1)) (-(x : ℂ)) :=
    funext fun p ↦
      iteratedDeriv_comp_neg_ofReal (isOpen_UMinus x₀) (PhiMinus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) 0).1
        p.2.val x (neg_ofReal_mem_UMinus hx.1 hx.2)
  dsimp [Fp, Fm] at hFp0 hFm0
  rw [neg_neg] at hFp0 hFm0
  refine ⟨?_, ?_⟩
  · rw [hiterP]; exact hFp0
  · rw [hiterM]; exact hFm0

/-- Non-Bol weight predicate `k ∈ {1} ∪ (1/2 + ℤ)_{≤ 3/2}` (`main.tex` Theorem A & B). -/
def NonBolWeight (k : ℂ) : Prop :=
  k = 1 ∨ ∃ m : ℤ, k = (m : ℂ) + 1 / 2 ∧ m ≤ 1

/-- Exact parity indicator `true` iff `k ∈ 1/2 + ℤ` (for `NonBolWeight k`). -/
noncomputable def nonBolIsHalf (k : ℂ) : Bool :=
  decide (k ≠ 1)

/-- Integer `x`-shift `K₀ - k - σ_I` with `K₀ = 3`: equals `2` if `k = 1` and `(2 - m).toNat ≥ 1`
if `k = m + 1/2` (`m ≤ 1`). -/
noncomputable def nonBolShift (k : ℂ) : ℕ :=
  if k = 1 then 2 else Int.toNat (2 - Int.floor k.re)

theorem nonBolWeight_inv_Gamma_ne_zero {k : ℂ} (hk : NonBolWeight k) :
    (Complex.Gamma k)⁻¹ ≠ 0 := by
  apply one_div_Gamma_ne_zero_nonBol
  rcases hk with rfl | ⟨m, rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨m, rfl⟩

theorem nonBolWeight_x_power_eq {k : ℂ} (hk : NonBolWeight k) (r : ℕ) {j : ℕ} (hj : j ≤ r)
    (ω : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ (3 + 2 * r)) * ((x : ℂ) ^ (-k - 2 * (j : ℂ)) * (mockJetQAt k j ω).eval (x : ℂ)) =
      (if nonBolIsHalf k then ((Real.sqrt x : ℝ) : ℂ) else 1) *
        (Polynomial.X ^ nonBolShift k * mockJetP k r j ω).eval (x : ℂ) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  -- Unfold `mockJetP k r j ω = X^(2*(r - j)) * mockJetQAt k j ω`!
  have hP_eval : (mockJetP k r j ω).eval (x : ℂ) = (x : ℂ) ^ (2 * (r - j)) * (mockJetQAt k j ω).eval (x : ℂ) := by
    dsimp [mockJetP]; rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hP_eval]
  rcases hk with rfl | ⟨m, rfl, hm_le⟩
  · -- Case `k = 1`: `nonBolIsHalf 1 = false`, `nonBolShift 1 = 2`!
    simp only [nonBolIsHalf, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
      nonBolShift, one_mul]
    have hpow : (x : ℂ) ^ (3 + 2 * r) * (x : ℂ) ^ (-(1 : ℂ) - 2 * (j : ℂ)) =
        (x : ℂ) ^ 2 * (x : ℂ) ^ (2 * (r - j)) := by
      rw [← Complex.cpow_natCast (x : ℂ) (3 + 2 * r), ← Complex.cpow_add _ _ hxC,
          ← pow_add, ← Complex.cpow_natCast (x : ℂ) (2 + 2 * (r - j))]
      congr 1
      have hsub : ((r - j : ℕ) : ℂ) = (r : ℂ) - (j : ℂ) := Nat.cast_sub hj
      push_cast; rw [hsub]; ring
    linear_combination (mockJetQAt 1 j ω).eval (x : ℂ) * hpow
  · -- Case `k = m + 1/2` (`m ≤ 1`): `nonBolIsHalf = true`, `nonBolShift = (2 - m).toNat`!
    have hne1 : (m : ℂ) + 1 / 2 ≠ 1 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.intCast_re, Complex.div_ofNat_re, Complex.one_re] at hre
      have h2m : 2 * m = 1 := by exact_mod_cast (by linarith : (2 * m : ℝ) = 1)
      omega
    have hfloor : Int.floor (((m : ℂ) + 1 / 2).re) = m := by
      have hre : ((m : ℂ) + 1 / 2).re = (m : ℝ) + 1 / 2 := by simp
      rw [hre, Int.floor_eq_iff]; constructor <;> linarith
    have hshift : nonBolShift ((m : ℂ) + 1 / 2) = (2 - m).toNat := by
      unfold nonBolShift
      simp only [hne1, ↓reduceIte, hfloor]
    have hhalf : nonBolIsHalf ((m : ℂ) + 1 / 2) = true := by
      unfold nonBolIsHalf
      simp only [ne_eq, hne1, not_false_eq_true, decide_true]
    simp only [hhalf, hshift, ↓reduceIte]
    have hsqrt : ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
      congr 1; push_cast; ring
    have hpow : (x : ℂ) ^ (3 + 2 * r) * (x : ℂ) ^ (-((m : ℂ) + 1 / 2) - 2 * (j : ℂ)) =
        (x : ℂ) ^ (1 / 2 : ℂ) * ((x : ℂ) ^ (2 - m).toNat * (x : ℂ) ^ (2 * (r - j))) := by
      rw [← Complex.cpow_natCast (x : ℂ) (3 + 2 * r), ← Complex.cpow_add _ _ hxC,
          ← pow_add, ← Complex.cpow_natCast (x : ℂ) _, ← Complex.cpow_add _ _ hxC]
      congr 1
      have hsub : ((r - j : ℕ) : ℂ) = (r : ℂ) - (j : ℂ) := Nat.cast_sub hj
      have h2m : (((2 - m).toNat : ℕ) : ℂ) = 2 - (m : ℂ) := by
        have : (((2 - m).toNat : ℕ) : ℤ) = 2 - m := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      push_cast; rw [hsub, h2m]; ring
    rw [hsqrt]
    linear_combination (mockJetQAt ((m : ℂ) + 1 / 2) j ω).eval (x : ℂ) * hpow

/-- Minimal `x`-coefficient of `mockJetQAt k j ω` equals `ω ^ j` (exact formula `eq:Pj-lead`)! -/
theorem mockJetQAt_coeff_zero (k : ℂ) (j : ℕ) (ω : ℂ) :
    (mockJetQAt k j ω).coeff 0 = ω ^ j := by
  induction j with
  | zero => simp [mockJetQAt, mockJetQ]
  | succ j ih =>
    unfold mockJetQAt mockJetQ
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_X, eval_C_mapDeriv,
        Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul,
        Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Finset.sum_singleton]
    simp only [Polynomial.coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, zero_mul, zero_add,
      Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
      mul_zero, sub_zero]
    change ω * (mockJetQAt k j ω).coeff 0 = ω ^ (j + 1)
    rw [ih, pow_succ']

/-- Minimal `x`-valuation of `mockJetP k r j ω`: zero below `2 * (r - j)` and equals `ω ^ j` at `2 * (r - j)`! -/
theorem mockJetP_coeff_le {k : ℂ} {r j : ℕ} (ω : ℂ) (d : ℕ) :
    (mockJetP k r j ω).coeff d =
      if d < 2 * (r - j) then 0
      else if d = 2 * (r - j) then ω ^ j
      else (mockJetQAt k j ω).coeff (d - 2 * (r - j)) := by
  unfold mockJetP
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hlt : d < 2 * (r - j)
  · simp [hlt, not_le.mpr hlt]
  · have hge : 2 * (r - j) ≤ d := not_lt.mp hlt
    by_cases heq : d = 2 * (r - j)
    · subst heq; simp [mockJetQAt_coeff_zero]
    · simp [hlt, hge, heq]

/-- Elementary bound on the degree-`≥ 2` Taylor remainder of `R(Z + δ)` (`mockModular_taylor_expansion`)! -/
theorem norm_taylor_rem_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : MvPolynomial ι ℂ) (Z δ : ι → ℂ) {B_Z B_δ : ℝ} (hBZ : 1 ≤ B_Z)
    (hBδ0 : 0 ≤ B_δ) (hBδ1 : B_δ ≤ 1)
    (hZ : ∀ j, ‖Z j‖ ≤ B_Z) (hδ : ∀ j, ‖δ j‖ ≤ B_δ) :
    let F : Polynomial ℂ :=
      MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap ℂ ℂ))
        (fun j ↦ Polynomial.C (Z j) + Polynomial.C (δ j) * Polynomial.X) R
    ‖∑ m ∈ (Finset.range (F.natDegree + 1)).filter (2 ≤ ·), F.coeff m‖ ≤
      (∑ μ ∈ R.support, ‖R.coeff μ‖ * (2 * B_Z) ^ R.totalDegree) * B_δ ^ 2 := by
  intro F
  -- Bound each monomial `μ ∈ R.support` individually!
  let shiftP : MvPolynomial ι ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun j ↦ Polynomial.C (Z j) + Polynomial.C (δ j) * Polynomial.X)
  have hF_eq : F = ∑ μ ∈ R.support, Polynomial.C (R.coeff μ) *
      ∏ i ∈ μ.support, (Polynomial.C (Z i) + Polynomial.C (δ i) * Polynomial.X) ^ (μ i) := by
    change shiftP R = _
    conv_lhs => rw [R.as_sum, map_sum]
    apply Finset.sum_congr rfl; intro μ _
    rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
  -- Key polynomial bound: for any `p, q : Polynomial ℂ`, if `‖p.coeff m‖ ≤ C_p * B_δ ^ m` and
  -- `‖q.coeff m‖ ≤ C_q * B_δ ^ m`, then `∑_m ‖(p * q).coeff m‖` works via `∑_m ‖p.coeff m‖ / B_δ^m`!
  -- Even simpler: bound `∑ m ≥ 2, ‖P.coeff m‖ ≤ C * B_δ^2` directly using `eval₂` at nonnegative reals `B_Z + B_δ * X`!
  have hdom_poly : ∀ (P : Polynomial ℂ) (Q : Polynomial ℝ),
      (∀ m, ‖P.coeff m‖ ≤ Q.coeff m) →
      ∀ (P' : Polynomial ℂ) (Q' : Polynomial ℝ),
      (∀ m, ‖P'.coeff m‖ ≤ Q'.coeff m) →
      ∀ m, ‖(P * P').coeff m‖ ≤ (Q * Q').coeff m := by
    intro P Q hPQ P' Q' hPQ' m
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul (hPQ x.1) (hPQ' x.2) (norm_nonneg _) (le_trans (norm_nonneg _) (hPQ x.1))
  have hdom_lin : ∀ i : ι, ∀ m,
      ‖(Polynomial.C (Z i) + Polynomial.C (δ i) * Polynomial.X).coeff m‖ ≤
        (Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X).coeff m := by
    intro i m
    rcases m with _ | _ | m
    · simp [hZ i]
    · simp [hδ i]
    · simp
  have hdom_pow : ∀ (i : ι) (k : ℕ) (m : ℕ),
      ‖((Polynomial.C (Z i) + Polynomial.C (δ i) * Polynomial.X) ^ k).coeff m‖ ≤
        ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ k).coeff m := by
    intro i k
    induction k with
    | zero => intro m; cases m <;> simp [Polynomial.coeff_one]
    | succ k ih =>
      intro m; rw [pow_succ, pow_succ]
      exact hdom_poly _ _ ih _ _ (hdom_lin i) m
  have hdom_prod : ∀ (μ : ι →₀ ℕ) (m : ℕ),
      ‖(∏ i ∈ μ.support, (Polynomial.C (Z i) + Polynomial.C (δ i) * Polynomial.X) ^ (μ i)).coeff m‖ ≤
        ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ (μ.sum fun _ k ↦ k)).coeff m := by
    intro μ
    have hprod_aux : ∀ (s : Finset ι) (m : ℕ),
        ‖(∏ i ∈ s, (Polynomial.C (Z i) + Polynomial.C (δ i) * Polynomial.X) ^ (μ i)).coeff m‖ ≤
          ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ (∑ i ∈ s, μ i)).coeff m := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro m; cases m <;> simp [Polynomial.coeff_one]
      | insert a s ha ih =>
        intro m
        rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
        exact hdom_poly _ _ (hdom_pow a (μ a)) _ _ ih m
    exact hprod_aux μ.support
  -- Bound the tail `∑ m ≥ 2, ((B_Z + B_δ X)^d).coeff m ≤ (2 * B_Z)^d * B_δ^2`!
  have hdom_F : ∀ m : ℕ, 2 ≤ m →
      ‖F.coeff m‖ ≤ ∑ μ ∈ R.support, ‖R.coeff μ‖ *
        ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ (μ.sum fun _ k ↦ k)).coeff m := by
    intro m _
    rw [hF_eq]
    have hcs : (∑ μ ∈ R.support, Polynomial.C (R.coeff μ) *
        ∏ i ∈ μ.support, (Polynomial.C (Z i) + Polynomial.C (δ i) * Polynomial.X) ^ (μ i)).coeff m =
        ∑ μ ∈ R.support, R.coeff μ *
          (∏ i ∈ μ.support, (Polynomial.C (Z i) + Polynomial.C (δ i) * Polynomial.X) ^ (μ i)).coeff m := by
      change (Polynomial.lcoeff ℂ m) _ = _; rw [map_sum]
      apply Finset.sum_congr rfl; intro μ _; rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul]
    rw [hcs]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hdom_prod μ m) (norm_nonneg _)
  have hbinom_tail : ∀ d : ℕ, ∀ N : ℕ,
      ∑ m ∈ (Finset.range N).filter (2 ≤ ·),
        ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ d).coeff m ≤
      (2 * B_Z) ^ d * B_δ ^ 2 := by
    intro d N
    have hcoeff_d : ∀ m : ℕ, ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ d).coeff m =
        if m ≤ d then (Nat.choose d m : ℝ) * B_Z ^ (d - m) * B_δ ^ m else 0 := by
      intro m
      rw [add_comm, add_pow]
      change (Polynomial.lcoeff ℝ m) _ = _; rw [map_sum]
      have hterm_simp : ∀ k : ℕ,
          (Polynomial.C B_δ * Polynomial.X) ^ k * Polynomial.C B_Z ^ (d - k) * ((d.choose k : ℕ) : Polynomial ℝ) =
          Polynomial.C ((d.choose k : ℝ) * B_Z ^ (d - k) * B_δ ^ k) * Polynomial.X ^ k := fun k ↦ by
        rw [mul_pow, ← map_pow, ← map_pow, ← Polynomial.C_eq_natCast]
        simp only [map_mul]; ring
      by_cases hm : m ≤ d
      · simp only [hm, ↓reduceIte]
        rw [Finset.sum_eq_single m]
        · rw [Polynomial.lcoeff_apply, hterm_simp m, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
        · intro k _ hkm
          rw [Polynomial.lcoeff_apply, hterm_simp k, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          simp only [Ne.symm hkm, ↓reduceIte, mul_zero]
        · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)) hnot
      · simp only [hm, ↓reduceIte]; apply Finset.sum_eq_zero; intro k hk
        have hkm : k ≠ m := by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk); omega
        rw [Polynomial.lcoeff_apply, hterm_simp k, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp only [Ne.symm hkm, ↓reduceIte, mul_zero]
    have hsub_le : ∑ m ∈ (Finset.range N).filter (2 ≤ ·),
          ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ d).coeff m ≤
        ∑ m ∈ (Finset.range (d + 1)).filter (2 ≤ ·),
          (Nat.choose d m : ℝ) * B_Z ^ (d - m) * B_δ ^ m := by
      have hpos : ∀ m : ℕ, 0 ≤ ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ d).coeff m := fun m ↦ by
        rw [hcoeff_d]; split_ifs <;> positivity
      calc ∑ m ∈ (Finset.range N).filter (2 ≤ ·), ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ d).coeff m
          ≤ ∑ m ∈ (Finset.range (max N (d + 1))).filter (2 ≤ ·),
              ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ d).coeff m :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset_filter _ (Finset.range_mono (le_max_left _ _))) fun m _ _ ↦ hpos m
        _ = ∑ m ∈ (Finset.range (d + 1)).filter (2 ≤ ·),
              ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ d).coeff m := by
            symm
            refine Finset.sum_subset (Finset.filter_subset_filter _ (Finset.range_mono (le_max_right _ _))) ?_
            intro m hm hnot
            have hnot_le : ¬ m ≤ d := fun hle ↦
              hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), (Finset.mem_filter.mp hm).2⟩)
            simp only [hcoeff_d, hnot_le, ↓reduceIte]
        _ = ∑ m ∈ (Finset.range (d + 1)).filter (2 ≤ ·),
              (Nat.choose d m : ℝ) * B_Z ^ (d - m) * B_δ ^ m := by
            apply Finset.sum_congr rfl; intro m hm
            have hle : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
            simp only [hcoeff_d, hle, ↓reduceIte]
    refine hsub_le.trans ?_
    calc ∑ m ∈ (Finset.range (d + 1)).filter (2 ≤ ·), (Nat.choose d m : ℝ) * B_Z ^ (d - m) * B_δ ^ m
        ≤ ∑ m ∈ (Finset.range (d + 1)).filter (2 ≤ ·), (Nat.choose d m : ℝ) * B_Z ^ d * B_δ ^ 2 := by
          apply Finset.sum_le_sum; intro m hm
          have h2m : 2 ≤ m := (Finset.mem_filter.mp hm).2
          have hBZm : B_Z ^ (d - m) ≤ B_Z ^ d := pow_le_pow_right₀ hBZ (Nat.sub_le d m)
          have hBδm : B_δ ^ m ≤ B_δ ^ 2 := pow_le_pow_of_le_one hBδ0 hBδ1 h2m
          exact mul_le_mul (mul_le_mul_of_nonneg_left hBZm (Nat.cast_nonneg _)) hBδm (by positivity) (by positivity)
      _ ≤ ∑ m ∈ Finset.range (d + 1), (Nat.choose d m : ℝ) * B_Z ^ d * B_δ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity
      _ = (∑ m ∈ Finset.range (d + 1), (Nat.choose d m : ℝ)) * (B_Z ^ d * B_δ ^ 2) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; ring
      _ = (2 : ℝ) ^ d * (B_Z ^ d * B_δ ^ 2) := by
          rw [show (∑ m ∈ Finset.range (d + 1), (Nat.choose d m : ℝ)) = ((∑ m ∈ Finset.range (d + 1), Nat.choose d m : ℕ) : ℝ) by
            push_cast; rfl, Nat.sum_range_choose]; push_cast; rfl
      _ = (2 * B_Z) ^ d * B_δ ^ 2 := by rw [mul_pow]; ring
  calc ‖∑ m ∈ (Finset.range (F.natDegree + 1)).filter (2 ≤ ·), F.coeff m‖
      ≤ ∑ m ∈ (Finset.range (F.natDegree + 1)).filter (2 ≤ ·), ‖F.coeff m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (Finset.range (F.natDegree + 1)).filter (2 ≤ ·),
          ∑ μ ∈ R.support, ‖R.coeff μ‖ *
            ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ (μ.sum fun _ k ↦ k)).coeff m :=
        Finset.sum_le_sum fun m hm ↦ hdom_F m (Finset.mem_filter.mp hm).2
    _ = ∑ μ ∈ R.support, ‖R.coeff μ‖ *
          ∑ m ∈ (Finset.range (F.natDegree + 1)).filter (2 ≤ ·),
            ((Polynomial.C B_Z + Polynomial.C B_δ * Polynomial.X) ^ (μ.sum fun _ k ↦ k)).coeff m := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro μ _; rw [← Finset.mul_sum]
    _ ≤ ∑ μ ∈ R.support, ‖R.coeff μ‖ * ((2 * B_Z) ^ (μ.sum fun _ k ↦ k) * B_δ ^ 2) :=
        Finset.sum_le_sum fun μ _ ↦ mul_le_mul_of_nonneg_left (hbinom_tail _ _) (norm_nonneg _)
    _ ≤ ∑ μ ∈ R.support, ‖R.coeff μ‖ * ((2 * B_Z) ^ R.totalDegree * B_δ ^ 2) :=
        Finset.sum_le_sum fun μ hμ ↦ mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (MvPolynomial.le_totalDegree hμ)) (sq_nonneg _))
          (norm_nonneg _)
    _ = (∑ μ ∈ R.support, ‖R.coeff μ‖ * (2 * B_Z) ^ R.totalDegree) * B_δ ^ 2 := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro μ _; ring

/-- Exact parity-split polynomial mode vectors `W_n^{int}(x)` and `W_n^{half}(x)` (`main.tex:966`)
for weight vector `k : Fin s → ℂ`, cusp parameters `M, L`, and Fourier coefficients `c_g`! -/
noncomputable def mockModeW (isHalf : Bool) {s r : ℕ} (M L : ℕ) (k : Fin s → ℂ)
    (c_g : Fin s → ℕ → ℂ) (n : ℕ) : Fin s × Fin (r + 1) → Polynomial ℂ :=
  fun p ↦
    if nonBolIsHalf (k p.1) = isHalf then
      let ω_n : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ)
      let phase : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))
      Polynomial.C (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) *
          starRingEnd ℂ (c_g p.1 n) * phase * (ω_n : ℂ) ^ (k p.1 - 1)) *
        (Polynomial.X ^ nonBolShift (k p.1) * mockJetP (k p.1) r p.2.val (ω_n : ℂ))
    else 0

/-- Helper: uniform bound on gradient entries of `evalAtConv x R`! -/
private lemma evalAtConv_grad_le {ι : Type*} [DecidableEq ι] {ρ M_R B_Z : ℝ}
    (hMR : 0 ≤ M_R) (hBZ : 1 ≤ B_Z)
    (R : MvPolynomial ι convergentSubring)
    (hR_conv : ∀ m : ι →₀ ℕ, IsConvergentOn ρ M_R (R.coeff m).val)
    {x : ℂ} (hx_lt_ρ : ‖x‖ < ρ)
    (hcoeff_bd : ∀ m : ι →₀ ℕ, ‖psEval (R.coeff m).val x‖ ≤ 2 * M_R)
    {Z : ι → ℂ} (hZ : ∀ i, ‖Z i‖ ≤ B_Z) (p : ι) :
    ‖MvPolynomial.aeval Z (MvPolynomial.pderiv p (evalAtConv x R))‖ ≤
      ∑ μ ∈ (MvPolynomial.pderiv p R).support, (2 * M_R * ((μ p + 1 : ℕ) : ℝ)) * B_Z ^ R.totalDegree := by
  rw [evalAtConv_pderiv, aeval_evalAtConv]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ hμ ↦ ?_)
  rw [norm_mul, norm_prod]
  simp_rw [norm_pow]
  have h1 : ‖psEval ((MvPolynomial.pderiv p R).coeff μ).val x‖ ≤ 2 * M_R * ((μ p + 1 : ℕ) : ℝ) := by
    rw [MvPolynomial.coeff_pderiv]
    have hval : (R.coeff (μ + Finsupp.single p 1) * ((μ p : convergentSubring) + 1)).val =
        (Polynomial.C ((μ p + 1 : ℕ) : ℂ) : PowerSeries ℂ) * (R.coeff (μ + Finsupp.single p 1)).val := by
      rw [Polynomial.coe_C, map_natCast PowerSeries.C, mul_comm]; simp
    rw [hval, psEval_poly_mul (hR_conv _) _ hx_lt_ρ, Polynomial.eval_C, norm_mul, Complex.norm_natCast]
    calc ((μ p + 1 : ℕ) : ℝ) * ‖psEval (R.coeff (μ + Finsupp.single p 1)).val x‖
        ≤ ((μ p + 1 : ℕ) : ℝ) * (2 * M_R) :=
          mul_le_mul_of_nonneg_left (hcoeff_bd _) (Nat.cast_nonneg _)
      _ = 2 * M_R * ((μ p + 1 : ℕ) : ℝ) := by ring
  have h2 : ∏ i ∈ μ.support, ‖Z i‖ ^ (μ i) ≤ B_Z ^ R.totalDegree := by
    have hle1 : ∏ i ∈ μ.support, ‖Z i‖ ^ (μ i) ≤ ∏ i ∈ μ.support, B_Z ^ (μ i) := by
      gcongr with i _
      exact hZ i
    rw [Finset.prod_pow_eq_pow_sum] at hle1
    have hdeg_le : (∑ i ∈ μ.support, μ i) ≤ R.totalDegree := by
      have hle_pd : (μ.sum fun _ c ↦ c) ≤ (MvPolynomial.pderiv p R).totalDegree :=
        MvPolynomial.le_totalDegree hμ
      have hpd_le : (MvPolynomial.pderiv p R).totalDegree ≤ R.totalDegree := by
        rw [MvPolynomial.totalDegree]
        refine Finset.sup_le fun ν hν ↦ ?_
        have hne := MvPolynomial.mem_support_iff.mp hν
        rw [MvPolynomial.coeff_pderiv] at hne
        have hs := MvPolynomial.le_totalDegree
          (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne))
        have hsub_le : (ν.sum fun _ c ↦ c) ≤ ((ν + Finsupp.single p 1).sum fun _ c ↦ c) := by
          rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
          exact Nat.le_add_right _ _
        exact hsub_le.trans hs
      exact hle_pd.trans hpd_le
    exact hle1.trans (pow_le_pow_right₀ hBZ hdeg_le)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ ↦ by positivity) (by positivity)

/-- Helper: uniform bound on the degree-`≥ 2` Taylor remainder of `evalAtConv x R`! -/
private lemma evalAtConv_taylor_rem_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M_R B_Z B_δ : ℝ} (hMR : 0 ≤ M_R) (hBZ : 1 ≤ B_Z) (hBδ0 : 0 ≤ B_δ) (hBδ1 : B_δ ≤ 1)
    (R : MvPolynomial ι convergentSubring) (x : ℂ)
    (hcoeff_bd : ∀ m : ι →₀ ℕ, ‖psEval (R.coeff m).val x‖ ≤ 2 * M_R)
    (Z δ : ι → ℂ) (hZ : ∀ j, ‖Z j‖ ≤ B_Z) (hδ : ∀ j, ‖δ j‖ ≤ B_δ) :
    let F : Polynomial ℂ :=
      MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap ℂ ℂ))
        (fun j ↦ Polynomial.C (Z j) + Polynomial.C (δ j) * Polynomial.X) (evalAtConv x R)
    ‖∑ m ∈ (Finset.range (F.natDegree + 1)).filter (2 ≤ ·), F.coeff m‖ ≤
      ((R.support.card : ℝ) * (2 * M_R) * (2 * B_Z) ^ R.totalDegree) * B_δ ^ 2 := by
  intro F
  have hRem := norm_taylor_rem_le (evalAtConv x R) Z δ hBZ hBδ0 hBδ1 hZ hδ
  have hsub_supp : (evalAtConv x R).support ⊆ R.support := by
    intro μ hμ; by_contra hnot
    have h0 := MvPolynomial.notMem_support_iff.mp hnot
    have hne := MvPolynomial.mem_support_iff.mp hμ
    rw [coeff_evalAtConv, h0] at hne; exact hne (by simp [psEval])
  have hdeg_le : (evalAtConv x R).totalDegree ≤ R.totalDegree := by
    rw [MvPolynomial.totalDegree]
    exact Finset.sup_le fun μ hμ ↦ MvPolynomial.le_totalDegree (hsub_supp hμ)
  have hcoef_sum : ∑ μ ∈ (evalAtConv x R).support,
        ‖(evalAtConv x R).coeff μ‖ * (2 * B_Z) ^ (evalAtConv x R).totalDegree ≤
      (R.support.card : ℝ) * (2 * M_R) * (2 * B_Z) ^ R.totalDegree := by
    calc ∑ μ ∈ (evalAtConv x R).support,
            ‖(evalAtConv x R).coeff μ‖ * (2 * B_Z) ^ (evalAtConv x R).totalDegree
        ≤ ∑ μ ∈ (evalAtConv x R).support, (2 * M_R) * (2 * B_Z) ^ R.totalDegree := by
          apply Finset.sum_le_sum; intro μ _
          rw [coeff_evalAtConv]
          exact mul_le_mul (hcoeff_bd μ) (pow_le_pow_right₀ (by linarith) hdeg_le) (by positivity) (by positivity)
      _ ≤ ∑ _μ ∈ R.support, (2 * M_R) * (2 * B_Z) ^ R.totalDegree :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_supp fun _ _ _ ↦ by positivity
      _ = (R.support.card : ℝ) * (2 * M_R) * (2 * B_Z) ^ R.totalDegree := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  exact hRem.trans (mul_le_mul_of_nonneg_right hcoef_sum (sq_nonneg _))

/-- **Proposition 5.3 — Collision-Free Translation-Invariance Induction & `x^{1/2}`-Parity Decoupling**:
Let `R ∈ MvPolynomial (Fin s × Fin (r + 1)) convergentSubring` be a minimal-total-degree
nonzero annihilator of the formal Eichler jet `Yhat(x)` for non-Bol weights
`k_i ∈ {1} ∪ (1/2 + ℤ)_{≤ 3/2}` and shadow Fourier coefficients `c_g i n` (`‖c_g i n‖ ≤ C₀ exp(a ω_n)`,
`a < 1`).
Then for EVERY mode `n : ℕ`, **BOTH** parity-split directional derivatives vanish identically in `ℂ{x}[Z]`:
`dirDeriv (convPolyEmb ∘ mockModeW false M L k c_g n) R = 0` AND
`dirDeriv (convPolyEmb ∘ mockModeW true M L k c_g n) R = 0`! -/
theorem mockModular_translation_invariance_induction {s r M L : ℕ} (_hM : 1 ≤ M) (hL : 1 ≤ L)
    (k : Fin s → ℂ) (hk : ∀ i, NonBolWeight (k i))
    (c_g : Fin s → ℕ → ℂ) {C₀ a : ℝ} (hC₀ : 0 ≤ C₀) (ha : a < 1)
    (hc_bd : ∀ i n, ‖c_g i n‖ ≤ C₀ * Real.exp (a * (2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ))))
    (b : Fin s → ℂ → ℂ) (C_b c_b : Fin s → ℝ)
    (hb : ∀ i, ExpDecayKernel (b i) (C_b i) (c_b i))
    (hb_ser : ∀ i y, b i y = ∑' n : ℕ,
      (starRingEnd ℂ (c_g i n) * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))) *
        Complex.exp (-((2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ) : ℝ) : ℂ) * y))
    (R : MvPolynomial (Fin s × Fin (r + 1)) convergentSubring)
    (_hR_ne : R ≠ 0) (hR_deg : 0 < R.totalDegree)
    (hR_ann : MvPolynomial.aeval
      (fun p : Fin s × Fin (r + 1) ↦
        PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n))
      (MvPolynomial.map convergentSubring.subtype R) = 0)
    (hR_min : ∀ Q : MvPolynomial (Fin s × Fin (r + 1)) convergentSubring,
      Q ≠ 0 →
      MvPolynomial.aeval
        (fun p : Fin s × Fin (r + 1) ↦
          PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n))
        (MvPolynomial.map convergentSubring.subtype Q) = 0 →
      R.totalDegree ≤ Q.totalDegree) :
    ∀ n : ℕ,
      dirDeriv (fun p ↦ convPolyEmb (mockModeW false M L k c_g n p)) R = 0 ∧
      dirDeriv (fun p ↦ convPolyEmb (mockModeW true M L k c_g n p)) R = 0 := by
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
  let δ_freq : ℝ := 2 * Real.pi / (L : ℝ)
  have hδ_pos : 0 < δ_freq := div_pos (mul_pos two_pos Real.pi_pos) hL_pos
  let ω : ℕ → ℝ := fun n ↦ δ_freq * ((n + 1 : ℕ) : ℝ)
  have hω_eq : ∀ n : ℕ, ω n = 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ) := fun n ↦ by
    dsimp [ω, δ_freq]; ring
  have hω_pos : ∀ n : ℕ, 0 < ω n := fun n ↦ by dsimp [ω]; positivity
  let c_mode : Fin s → ℕ → ℂ := fun i n ↦
    starRingEnd ℂ (c_g i n) * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))
  have hc_mode_bd : ∀ i n, ‖c_mode i n‖ ≤ C₀ * Real.exp (a * ω n) := fun i n ↦ by
    dsimp [c_mode]
    rw [norm_mul, RCLike.norm_conj]
    have hunit : ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))‖ = 1 := by
      have harg : -2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)) =
          (((-2 * Real.pi * ((n + 1 : ℕ) : ℝ) / ((M : ℝ) * (L : ℝ)) : ℝ) : ℂ)) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    rw [hunit, mul_one, hω_eq n]; exact hc_bd i n
  -- Extract common convergence radius `ρ > 0` for `R` and invoke lateral simultaneous annihilation!
  obtain ⟨ρ, M_R, hρ_pos, hMR_nn, hR_conv⟩ := mvPoly_conv_common_radius R
  let x₀ : ℝ := min (ρ / 2) (1 / 4)
  have hx₀_pos : 0 < x₀ := lt_min (by linarith) (by norm_num)
  have hx₀_le_quarter : x₀ ≤ 1 / 4 := min_le_right _ _
  have hx₀_le_half : x₀ ≤ ρ / 2 := min_le_left _ _
  have hx₀_lt_ρ : x₀ < ρ := lt_of_le_of_lt hx₀_le_half (by linarith)
  let YPlus : ℝ → Fin s × Fin (r + 1) → ℂ := fun x p ↦
    iteratedDeriv p.2.val (fun t : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(t : ℂ))) x
  let YMinus : ℝ → Fin s × Fin (r + 1) → ℂ := fun x p ↦
    iteratedDeriv p.2.val (fun t : ℝ ↦ PhiMinus (k p.1) (b p.1) (-(t : ℂ))) x
  let Yhat : Fin s × Fin (r + 1) → PowerSeries ℂ := fun p ↦
    PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n)
  have hlat := mvPoly_conv_lateral_simultaneous_annihilation k b C_b c_b hb R hρ_pos hR_conv hR_ann
  -- Uniform boundedness of `YMinus x` on `(0, x₀)` (from `HasRealAsymp` at `N = 0`)!
  have hYMinus_asymp : ∀ p : Fin s × Fin (r + 1),
      HasRealAsymp x₀ (fun x ↦ YMinus x p) (fun n ↦ (Yhat p).coeff n) := fun p ↦ by
    have h := (PhiPlus_PhiMinus_neg_iteratedDeriv_hasRealAsymp (hb p.1) hx₀_pos hx₀_le_quarter (k p.1) p.2.val).2
    intro N; obtain ⟨C, hC, hbN⟩ := h N
    refine ⟨C, hC, fun x hx ↦ ?_⟩
    simpa [YMinus, Yhat] using hbN x hx
  have hYMinus_bdd : ∃ B_Z : ℝ, 1 ≤ B_Z ∧ ∀ x ∈ Set.Ioo (0 : ℝ) x₀, ∀ p, ‖YMinus x p‖ ≤ B_Z := by
    have h0 : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ioo (0 : ℝ) x₀, ‖YMinus x p‖ ≤ C := fun p ↦ by
      obtain ⟨C, hC, hb0⟩ := hYMinus_asymp p 0
      exact ⟨C, hC, fun x hx ↦ by simpa using hb0 x hx⟩
    choose C_p hCp_nn hCp_bd using h0
    refine ⟨1 + ∑ p : Fin s × Fin (r + 1), C_p p,
      by linarith [Finset.sum_nonneg (s := Finset.univ) fun p _ ↦ hCp_nn p], fun x hx p ↦ ?_⟩
    have h1 := hCp_bd p x hx
    have h2 : C_p p ≤ ∑ q : Fin s × Fin (r + 1), C_p q :=
      Finset.single_le_sum (fun q _ ↦ hCp_nn q) (Finset.mem_univ p)
    linarith
  obtain ⟨B_Z, hBZ_ge1, hYMinus_le⟩ := hYMinus_bdd
  -- Exact mode vectors `v_m(x)` from `hankel_series_jump_iteratedDeriv` (`Lemma 5.2`):
  let v_mode : ℕ → ℝ → Fin s × Fin (r + 1) → ℂ := fun m x p ↦
    -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) *
      c_mode p.1 m * (ω m : ℂ) ^ (k p.1 - 1) *
      ((x : ℂ) ^ (-k p.1 - 2 * (p.2.val : ℂ)) * (mockJetQAt (k p.1) p.2.val (ω m : ℂ)).eval (x : ℂ))
  -- Exact parity split identity: `x^{3 + 2r} v_m(x) = W_m^{int}(x) + √x W_m^{half}(x)`!
  have hv_parity : ∀ (m : ℕ) (x : ℝ), 0 < x → ∀ p : Fin s × Fin (r + 1),
      (x : ℂ) ^ (3 + 2 * r) * v_mode m x p =
        (mockModeW false M L k c_g m p).eval (x : ℂ) +
        ((Real.sqrt x : ℝ) : ℂ) * (mockModeW true M L k c_g m p).eval (x : ℂ) := by
    intro m x hx p
    dsimp [v_mode, mockModeW]
    have hxp := nonBolWeight_x_power_eq (hk p.1) r (Nat.lt_succ_iff.mp p.2.isLt) (ω m : ℂ) hx
    cases hpar : nonBolIsHalf (k p.1)
    · simp only [Bool.false_eq_true, ↓reduceIte, Polynomial.eval_zero, mul_zero, add_zero,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      simp only [hpar, Bool.false_eq_true, ↓reduceIte, one_mul,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hxp
      rw [← hω_eq m]
      have hcm_eq : -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * starRingEnd ℂ (c_g p.1 m) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ))) =
          -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * c_mode p.1 m := by
        dsimp [c_mode]; ring
      rw [hcm_eq, ← hxp]; ring
    · simp only [Bool.true_eq_false, ↓reduceIte, Polynomial.eval_zero, zero_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      simp only [hpar, ↓reduceIte,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hxp
      rw [← hω_eq m]
      have hcm_eq : -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * starRingEnd ℂ (c_g p.1 m) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ))) =
          -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * c_mode p.1 m := by
        dsimp [c_mode]; ring
      rw [hcm_eq]
      linear_combination
        (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * c_mode p.1 m * (ω m : ℂ) ^ (k p.1 - 1)) * hxp
  -- Exact Hankel jump difference `YPlus x p - YMinus x p = ∑' m, exp(-ω m / x) * v_mode m x p`!
  have hjump : ∀ x ∈ Set.Ioo (0 : ℝ) x₀, ∀ p : Fin s × Fin (r + 1),
      YPlus x p - YMinus x p = ∑' m : ℕ, ((Real.exp (-ω m / x) : ℝ) : ℂ) * v_mode m x p := by
    intro x hx p
    have hx_half : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := ⟨hx.1, lt_of_lt_of_le hx.2 (hx₀_le_quarter.trans (by norm_num))⟩
    have hdiff_iter : YPlus x p - YMinus x p =
        iteratedDeriv p.2.val (fun t : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(t : ℂ)) -
          PhiMinus (k p.1) (b p.1) (-(t : ℂ))) x := by
      -- Linearity of `iteratedDeriv` on `(0, x₀)` (both `PhiPlus(-t)` and `PhiMinus(-t)` are smooth on `(0, x₀)`)!
      have hsub_smooth : ∀ m : ℕ, ∀ t ∈ Set.Ioo (0 : ℝ) x₀,
          iteratedDeriv m (fun u : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(u : ℂ)) -
            PhiMinus (k p.1) (b p.1) (-(u : ℂ))) t =
          iteratedDeriv m (fun u : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(u : ℂ))) t -
          iteratedDeriv m (fun u : ℝ ↦ PhiMinus (k p.1) (b p.1) (-(u : ℂ))) t := by
        intro m
        induction m with
        | zero => intro t _; simp [iteratedDeriv_zero]
        | succ m ih =>
          intro t ht
          rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ]
          have hev : iteratedDeriv m (fun u : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(u : ℂ)) -
                PhiMinus (k p.1) (b p.1) (-(u : ℂ))) =ᶠ[𝓝 t]
              fun u : ℝ ↦ iteratedDeriv m (fun u : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(u : ℂ))) u -
                iteratedDeriv m (fun u : ℝ ↦ PhiMinus (k p.1) (b p.1) (-(u : ℂ))) u := by
            filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu; exact ih u hu
          rw [hev.deriv_eq]
          have hdP : DifferentiableAt ℝ (iteratedDeriv m (fun u : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(u : ℂ)))) t := by
            have hevP : iteratedDeriv m (fun u : ℝ ↦ PhiPlus (k p.1) (b p.1) (-(u : ℂ))) =ᶠ[𝓝 t]
                fun u : ℝ ↦ (-1 : ℂ) ^ m * iteratedDeriv m (PhiPlus (k p.1) (b p.1)) (-(u : ℂ)) := by
              filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
              exact iteratedDeriv_comp_neg_ofReal (isOpen_UPlus x₀)
                (PhiPlus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) 0).1 m u (neg_ofReal_mem_UPlus hu.1 hu.2)
            refine DifferentiableAt.congr_of_eventuallyEq ?_ hevP
            have hmem := neg_ofReal_mem_UPlus ht.1 ht.2
            have hd := ((PhiPlus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) m).1 _ hmem).differentiableAt
              ((isOpen_UPlus x₀).mem_nhds hmem)
            have hneg : HasDerivAt (fun u : ℝ ↦ -(u : ℂ)) (-1 : ℂ) t := Complex.ofRealCLM.hasDerivAt.neg
            exact ((hd.hasDerivAt.scomp t hneg).const_mul _).differentiableAt
          have hdM : DifferentiableAt ℝ (iteratedDeriv m (fun u : ℝ ↦ PhiMinus (k p.1) (b p.1) (-(u : ℂ)))) t := by
            have hevM : iteratedDeriv m (fun u : ℝ ↦ PhiMinus (k p.1) (b p.1) (-(u : ℂ))) =ᶠ[𝓝 t]
                fun u : ℝ ↦ (-1 : ℂ) ^ m * iteratedDeriv m (PhiMinus (k p.1) (b p.1)) (-(u : ℂ)) := by
              filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
              exact iteratedDeriv_comp_neg_ofReal (isOpen_UMinus x₀)
                (PhiMinus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) 0).1 m u (neg_ofReal_mem_UMinus hu.1 hu.2)
            refine DifferentiableAt.congr_of_eventuallyEq ?_ hevM
            have hmem := neg_ofReal_mem_UMinus ht.1 ht.2
            have hd := ((PhiMinus_iteratedDeriv (hb p.1) hx₀_le_quarter (k p.1) m).1 _ hmem).differentiableAt
              ((isOpen_UMinus x₀).mem_nhds hmem)
            have hneg : HasDerivAt (fun u : ℝ ↦ -(u : ℂ)) (-1 : ℂ) t := Complex.ofRealCLM.hasDerivAt.neg
            exact ((hd.hasDerivAt.scomp t hneg).const_mul _).differentiableAt
          exact (hdP.hasDerivAt.sub hdM.hasDerivAt).deriv
      exact (hsub_smooth p.2.val x hx).symm
    rw [hdiff_iter]
    have hb_fn : b p.1 = fun y ↦ ∑' n : ℕ, c_mode p.1 n * Complex.exp (-(ω n : ℂ) * y) := by
      ext y
      have h := hb_ser p.1 y
      dsimp [c_mode]
      simpa only [← hω_eq] using h
    rw [hb_fn, hankel_series_jump_iteratedDeriv (k p.1) (c_mode p.1) ω hδ_pos hC₀ ha
      (fun n ↦ le_rfl) (hc_mode_bd p.1) p.2.val x hx_half, ← tsum_mul_left]
    apply tsum_congr; intro m
    have hexp : Complex.exp (-(ω m : ℂ) / (x : ℂ)) = ((Real.exp (-ω m / x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_exp]
    dsimp [v_mode]; rw [hexp]; ring
  -- Uniform polynomial-exponential bound on `‖v_mode m x p‖` for `x ∈ (0, x₀)`!
  have hv_bound : ∃ C_v : ℝ, ∃ A_v : ℕ, 0 ≤ C_v ∧
      ∀ (m : ℕ) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) x₀ → ∀ p : Fin s × Fin (r + 1),
        ‖v_mode m x p‖ ≤ C_v * x ^ (-(3 + 2 * r : ℤ)) * ((m + 1 : ℕ) : ℝ) ^ A_v * Real.exp (a * ω m) := by
    have hQ : ∀ p : Fin s × Fin (r + 1), ∃ M_p : ℝ, 0 ≤ M_p ∧
        ∀ (ω_v x : ℝ), 0 ≤ ω_v → 0 ≤ x → x ≤ 1 →
          ‖(mockJetQAt (k p.1) p.2.val (ω_v : ℂ)).eval (x : ℂ)‖ ≤ M_p * (1 + ω_v) ^ p.2.val :=
      fun p ↦ norm_eval_mockJetQAt_le (k p.1) p.2.val
    choose M_Q hMQ_nn hMQ_bd using hQ
    let A_v : ℕ := r + (Finset.univ.sup fun i : Fin s ↦ Nat.ceil (max ((k i).re - 1) 0))
    let K_p : Fin s × Fin (r + 1) → ℝ := fun p ↦
      ‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * C₀ *
        (max (δ_freq ^ ((k p.1).re - 1)) 1 * max (1 + δ_freq) 1 ^ p.2.val) *
        Real.exp (|(k p.1).im| * Real.pi) * M_Q p
    let C_v : ℝ := ∑ p : Fin s × Fin (r + 1), K_p p
    have hKp_nn : ∀ q : Fin s × Fin (r + 1), 0 ≤ K_p q := fun q ↦ by
      have hm1 : 0 ≤ max (δ_freq ^ ((k q.1).re - 1)) 1 := le_trans zero_le_one (le_max_right _ _)
      have hm2 : 0 ≤ max (1 + δ_freq) 1 := le_trans zero_le_one (le_max_right _ _)
      have hmq : 0 ≤ M_Q q := hMQ_nn q
      dsimp [K_p]; positivity
    refine ⟨C_v, A_v, Finset.sum_nonneg fun p _ ↦ hKp_nn p, fun m x hx p ↦ ?_⟩
    have hx_pos : 0 < x := hx.1
    have hx_le1 : x ≤ 1 := hx.2.le.trans (hx₀_le_quarter.trans (by norm_num))
    -- Note `‖(x : ℂ)^{-k - 2j}‖ = x^{-k.re - 2j} ≤ x^{-(3 + 2r)}` since `x ∈ (0, 1]` and `k.re ≤ 3/2`, `j ≤ r`!
    have hk_re_le : (k p.1).re ≤ 3 / 2 := by
      rcases hk p.1 with h1 | ⟨m', hm', hle⟩
      · rw [h1]; norm_num
      · rw [hm']; simp only [Complex.add_re, Complex.intCast_re, Complex.div_ofNat_re, Complex.one_re]
        have : (m' : ℝ) ≤ 1 := by exact_mod_cast hle
        linarith
    have hx_cpow : ‖(x : ℂ) ^ (-k p.1 - 2 * (p.2.val : ℂ))‖ ≤ x ^ (-(3 + 2 * r : ℤ)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      have hre : (-k p.1 - 2 * (p.2.val : ℂ)).re = -(k p.1).re - 2 * (p.2.val : ℝ) := by simp
      rw [hre, ← Real.rpow_intCast x (-(3 + 2 * r : ℤ))]
      apply Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le1
      have hj_le : (p.2.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp p.2.isLt
      push_cast; linarith
    have hω_cpow : ‖(ω m : ℂ) ^ (k p.1 - 1)‖ ≤
        max (δ_freq ^ ((k p.1).re - 1)) 1 * ((m + 1 : ℕ) : ℝ) ^ (Nat.ceil (max ((k p.1).re - 1) 0)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hω_pos m)]
      have hre : (k p.1 - 1).re = (k p.1).re - 1 := by simp
      rw [hre]; dsimp [ω]
      rw [Real.mul_rpow hδ_pos.le (by positivity)]
      have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
      have h1 : δ_freq ^ ((k p.1).re - 1) ≤ max (δ_freq ^ ((k p.1).re - 1)) 1 := le_max_left _ _
      have h2 : ((m + 1 : ℕ) : ℝ) ^ ((k p.1).re - 1) ≤
          ((m + 1 : ℕ) : ℝ) ^ (Nat.ceil (max ((k p.1).re - 1) 0)) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hm1 ((le_max_left _ _).trans (Nat.le_ceil _))
      exact mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) (by positivity)
    have hQ_m : ‖(mockJetQAt (k p.1) p.2.val (ω m : ℂ)).eval (x : ℂ)‖ ≤
        M_Q p * (max (1 + δ_freq) 1) ^ p.2.val * ((m + 1 : ℕ) : ℝ) ^ p.2.val := by
      have h1 := hMQ_bd p (ω m) x (hω_pos m).le hx_pos.le hx_le1
      have h2 : 1 + ω m ≤ max (1 + δ_freq) 1 * ((m + 1 : ℕ) : ℝ) := by
        have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
        have hle1 : 1 + δ_freq ≤ max (1 + δ_freq) 1 := le_max_left _ _
        dsimp [ω]; nlinarith
      calc ‖(mockJetQAt (k p.1) p.2.val (ω m : ℂ)).eval (x : ℂ)‖
          ≤ M_Q p * (1 + ω m) ^ p.2.val := h1
        _ ≤ M_Q p * (max (1 + δ_freq) 1 * ((m + 1 : ℕ) : ℝ)) ^ p.2.val :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 _) (hMQ_nn p)
        _ = M_Q p * (max (1 + δ_freq) 1) ^ p.2.val * ((m + 1 : ℕ) : ℝ) ^ p.2.val := by rw [mul_pow]; ring
    have hpow_Av : ((m + 1 : ℕ) : ℝ) ^ (Nat.ceil (max ((k p.1).re - 1) 0)) * ((m + 1 : ℕ) : ℝ) ^ p.2.val ≤
        ((m + 1 : ℕ) : ℝ) ^ A_v := by
      rw [← pow_add]
      apply pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos m)
      have h1 : Nat.ceil (max ((k p.1).re - 1) 0) ≤ Finset.univ.sup fun i : Fin s ↦ Nat.ceil (max ((k i).re - 1) 0) :=
        Finset.le_sup (f := fun i : Fin s ↦ Nat.ceil (max ((k i).re - 1) 0)) (Finset.mem_univ p.1)
      have h2 : p.2.val ≤ r := Nat.lt_succ_iff.mp p.2.isLt
      dsimp [A_v]; omega
    have hKp_le : K_p p ≤ C_v := Finset.single_le_sum (fun q _ ↦ hKp_nn q) (Finset.mem_univ p)
    have hexp_ge1 : (1 : ℝ) ≤ Real.exp (|(k p.1).im| * Real.pi) := Real.one_le_exp (by positivity)
    have hm1_nn : 0 ≤ max (δ_freq ^ ((k p.1).re - 1)) 1 := le_trans zero_le_one (le_max_right _ _)
    have hm2_nn : 0 ≤ max (1 + δ_freq) 1 := le_trans zero_le_one (le_max_right _ _)
    have hmq_nn : 0 ≤ M_Q p := hMQ_nn p
    have hx_zpow_nn : 0 ≤ x ^ (-(3 + 2 * r : ℤ)) := zpow_nonneg hx_pos.le _
    have hv_norm : ‖v_mode m x p‖ =
        (‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * ‖c_mode p.1 m‖ *
          ‖(ω m : ℂ) ^ (k p.1 - 1)‖) *
        (‖(x : ℂ) ^ (-k p.1 - 2 * (p.2.val : ℂ))‖ *
          ‖(mockJetQAt (k p.1) p.2.val (ω m : ℂ)).eval (x : ℂ)‖) := by
      dsimp only [v_mode]
      rw [norm_mul]
      congr 1
      · rw [norm_mul, norm_mul]
      · exact norm_mul _ _
    have h1_le : ‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * ‖c_mode p.1 m‖ *
        ‖(ω m : ℂ) ^ (k p.1 - 1)‖ ≤
        ‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * (C₀ * Real.exp (a * ω m)) *
          (max (δ_freq ^ ((k p.1).re - 1)) 1 * ((m + 1 : ℕ) : ℝ) ^ (Nat.ceil (max ((k p.1).re - 1) 0))) := by
      have ha_le := mul_le_mul_of_nonneg_left (hc_mode_bd p.1 m)
        (norm_nonneg (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))))
      exact mul_le_mul ha_le hω_cpow (norm_nonneg _) (by positivity)
    have h2_le : ‖(x : ℂ) ^ (-k p.1 - 2 * (p.2.val : ℂ))‖ *
        ‖(mockJetQAt (k p.1) p.2.val (ω m : ℂ)).eval (x : ℂ)‖ ≤
        x ^ (-(3 + 2 * r : ℤ)) * (M_Q p * (max (1 + δ_freq) 1) ^ p.2.val * ((m + 1 : ℕ) : ℝ) ^ p.2.val) :=
      mul_le_mul hx_cpow hQ_m (norm_nonneg _) hx_zpow_nn
    rw [hv_norm]
    calc (‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * ‖c_mode p.1 m‖ *
            ‖(ω m : ℂ) ^ (k p.1 - 1)‖) *
          (‖(x : ℂ) ^ (-k p.1 - 2 * (p.2.val : ℂ))‖ *
            ‖(mockJetQAt (k p.1) p.2.val (ω m : ℂ)).eval (x : ℂ)‖)
        ≤ (‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * (C₀ * Real.exp (a * ω m)) *
            (max (δ_freq ^ ((k p.1).re - 1)) 1 * ((m + 1 : ℕ) : ℝ) ^ (Nat.ceil (max ((k p.1).re - 1) 0)))) *
          (x ^ (-(3 + 2 * r : ℤ)) * (M_Q p * (max (1 + δ_freq) 1) ^ p.2.val * ((m + 1 : ℕ) : ℝ) ^ p.2.val)) :=
            mul_le_mul h1_le h2_le (by positivity) (by positivity)
      _ = (‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * C₀ *
            (max (δ_freq ^ ((k p.1).re - 1)) 1 * max (1 + δ_freq) 1 ^ p.2.val) * M_Q p) *
            (x ^ (-(3 + 2 * r : ℤ)) *
              (((m + 1 : ℕ) : ℝ) ^ (Nat.ceil (max ((k p.1).re - 1) 0)) * ((m + 1 : ℕ) : ℝ) ^ p.2.val)) *
            Real.exp (a * ω m) := by ring
      _ ≤ K_p p * (x ^ (-(3 + 2 * r : ℤ)) * ((m + 1 : ℕ) : ℝ) ^ A_v) * Real.exp (a * ω m) := by
          have hnn : 0 ≤ ‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * C₀ *
              (max (δ_freq ^ ((k p.1).re - 1)) 1 * max (1 + δ_freq) 1 ^ p.2.val) * M_Q p := by positivity
          have h1 : ‖-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1))‖ * C₀ *
              (max (δ_freq ^ ((k p.1).re - 1)) 1 * max (1 + δ_freq) 1 ^ p.2.val) * M_Q p ≤ K_p p := by
            dsimp [K_p]
            nlinarith [mul_le_mul_of_nonneg_left hexp_ge1 hnn]
          have h2 := mul_le_mul h1 (mul_le_mul_of_nonneg_left hpow_Av hx_zpow_nn)
            (by positivity) (hKp_nn p)
          exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = K_p p * x ^ (-(3 + 2 * r : ℤ)) * ((m + 1 : ℕ) : ℝ) ^ A_v * Real.exp (a * ω m) := by ring
      _ ≤ C_v * x ^ (-(3 + 2 * r : ℤ)) * ((m + 1 : ℕ) : ℝ) ^ A_v * Real.exp (a * ω m) := by
          have hnn_rest : 0 ≤ x ^ (-(3 + 2 * r : ℤ)) * ((m + 1 : ℕ) : ℝ) ^ A_v * Real.exp (a * ω m) := by
            have := hx_zpow_nn; positivity
          have hmul := mul_le_mul_of_nonneg_right hKp_le hnn_rest
          linarith
  obtain ⟨C_v, A_v, hCv_nn, hv_bd⟩ := hv_bound
  -- Helper: tail bound `∑' t, exp(-ω (n + t) / x) * v_mode (n + t) x p` for ANY `n : ℕ`!
  have htail_bd : ∀ n : ℕ, ∃ x_n C_n : ℝ, 0 < x_n ∧ x_n ≤ x₀ ∧ 0 ≤ C_n ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) x_n, ∀ p : Fin s × Fin (r + 1),
        Summable (fun t : ℕ ↦ ((Real.exp (-ω (n + t) / x) : ℝ) : ℂ) * v_mode (n + t) x p) ∧
        ‖∑' t : ℕ, ((Real.exp (-ω (n + t) / x) : ℝ) : ℂ) * v_mode (n + t) x p‖ ≤
          C_n * x ^ (-(3 + 2 * r : ℤ)) * Real.exp (-ω n / x) := by
    intro n
    let a_pos : ℝ := max a 0
    have ha_pos_lt1 : a_pos < 1 := max_lt ha zero_lt_one
    -- Choose `x_n` small enough so `a_pos * ω (n + t) ≤ (1 / 2) * ω t / x` for `t ≥ 1` AND `a_pos * ω n ≤ ...`!
    -- Even simpler: pick `x_n = min (x₀ / 2) (1 / (2 * (a_pos + 1)))`!
    -- Then for `x < x_n`: `1 / x > 2 * (a_pos + 1)` → `ω (n + t) / x - a * ω (n + t) = ω (n + t) * (1 / x - a)`:
    -- Wait: we need `exp(-(ω (n + t) / x - a * ω (n + t))) ≤ exp(a_pos * ω n) * exp(-ω n / x) * exp(-(δ_freq / (2 * x)) * t)`!
    -- Indeed: `-(ω (n + t) / x) + a * ω (n + t) = -ω n / x + a * ω n - (δ_freq * (1 / x - a)) * t`!
    -- For `x ≤ min (x₀ / 2) (1 / (2 * (a_pos + 1)))`: `1 / x - a ≥ 1 / x - a_pos ≥ 1 / (2 * x) ≥ 1`, so
    -- `-(δ_freq * (1 / x - a)) * t ≤ -δ_freq * t`!!
    let x_n : ℝ := min (x₀ / 2) (1 / (2 * (a_pos + 1)))
    have hxn_pos : 0 < x_n := lt_min (by linarith) (by dsimp [a_pos]; positivity)
    have hxn_le : x_n ≤ x₀ := (min_le_left _ _).trans (by linarith)
    have hr_lt1 : Real.exp (-δ_freq) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ_pos)
    have hsum_dom : Summable (fun t : ℕ ↦ ((t : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ A_v * (Real.exp (-δ_freq)) ^ t) :=
      summable_poly_mul_geom (by positivity) (Real.exp_pos _).le hr_lt1 A_v
    let S_n : ℝ := ∑' t : ℕ, ((t : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ A_v * (Real.exp (-δ_freq)) ^ t
    have hSn_nn : 0 ≤ S_n := tsum_nonneg fun _ ↦ by positivity
    refine ⟨x_n, C_v * Real.exp (a * ω n) * S_n, hxn_pos, hxn_le, by positivity, fun x hx p ↦ ?_⟩
    have hx_in : x ∈ Set.Ioo (0 : ℝ) x₀ := ⟨hx.1, lt_of_lt_of_le hx.2 hxn_le⟩
    have h1x_ge : 1 ≤ 1 / x - a := by
      have h1 : x ≤ 1 / (2 * (a_pos + 1)) := hx.2.le.trans (min_le_right _ _)
      have h2 : 2 * (a_pos + 1) ≤ 1 / x := (le_div_iff₀ hx.1).mpr (by
        have := (le_div_iff₀ (show 0 < 2 * (a_pos + 1) by dsimp [a_pos]; positivity)).mp h1; linarith)
      have ha_le : a ≤ a_pos := le_max_left _ _
      have ha0 : 0 ≤ a_pos := le_max_right _ _
      linarith
    have hterm_le : ∀ t : ℕ,
        ‖((Real.exp (-ω (n + t) / x) : ℝ) : ℂ) * v_mode (n + t) x p‖ ≤
          (C_v * x ^ (-(3 + 2 * r : ℤ)) * Real.exp (-ω n / x) * Real.exp (a * ω n)) *
            (((t : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ A_v * (Real.exp (-δ_freq)) ^ t) := by
      intro t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h1 := hv_bd (n + t) x hx_in p
      have hω_split : ω (n + t) = ω n + δ_freq * (t : ℝ) := by dsimp [ω]; push_cast; ring
      have hexp_split : Real.exp (-ω (n + t) / x) * Real.exp (a * ω (n + t)) ≤
          Real.exp (-ω n / x) * Real.exp (a * ω n) * (Real.exp (-δ_freq)) ^ t := by
        rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [hω_split]
        have hdiff : -(ω n + δ_freq * (t : ℝ)) / x + a * (ω n + δ_freq * (t : ℝ)) -
            (-ω n / x + a * ω n + (t : ℝ) * (-δ_freq)) =
            -(δ_freq * (t : ℝ) * (1 / x - a - 1)) := by ring
        have hnn : 0 ≤ δ_freq * (t : ℝ) * (1 / x - a - 1) := by
          exact mul_nonneg (mul_nonneg hδ_pos.le (Nat.cast_nonneg t)) (by linarith)
        linarith
      have hcast : ((n + t + 1 : ℕ) : ℝ) = (t : ℝ) + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      have hx_zpow_nn : 0 ≤ x ^ (-(3 + 2 * r : ℤ)) := zpow_nonneg hx.1.le _
      calc Real.exp (-ω (n + t) / x) * ‖v_mode (n + t) x p‖
          ≤ Real.exp (-ω (n + t) / x) * (C_v * x ^ (-(3 + 2 * r : ℤ)) * ((n + t + 1 : ℕ) : ℝ) ^ A_v * Real.exp (a * ω (n + t))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = C_v * x ^ (-(3 + 2 * r : ℤ)) * (((t : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ A_v) *
              (Real.exp (-ω (n + t) / x) * Real.exp (a * ω (n + t))) := by rw [hcast]; ring
        _ ≤ C_v * x ^ (-(3 + 2 * r : ℤ)) * (((t : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ A_v) *
              (Real.exp (-ω n / x) * Real.exp (a * ω n) * (Real.exp (-δ_freq)) ^ t) :=
            mul_le_mul_of_nonneg_left hexp_split (by positivity)
        _ = (C_v * x ^ (-(3 + 2 * r : ℤ)) * Real.exp (-ω n / x) * Real.exp (a * ω n)) *
              (((t : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ A_v * (Real.exp (-δ_freq)) ^ t) := by ring
    have hsum_t : Summable (fun t : ℕ ↦ ((Real.exp (-ω (n + t) / x) : ℝ) : ℂ) * v_mode (n + t) x p) :=
      Summable.of_norm_bounded (hsum_dom.mul_left _) hterm_le
    refine ⟨hsum_t, ?_⟩
    have h1 := norm_tsum_le_tsum_norm hsum_t.norm
    have h2 := Summable.tsum_le_tsum hterm_le hsum_t.norm (hsum_dom.mul_left _)
    rw [tsum_mul_left] at h2
    exact (h1.trans h2).trans_eq (by dsimp [S_n]; ring)
  -- Strong induction on `n : ℕ`!
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    -- Define the two candidate lower-degree directional derivatives in `MvPolynomial _ convergentSubring`:
    let F_int : MvPolynomial (Fin s × Fin (r + 1)) convergentSubring :=
      dirDeriv (fun p ↦ convPolyEmb (mockModeW false M L k c_g n p)) R
    let F_half : MvPolynomial (Fin s × Fin (r + 1)) convergentSubring :=
      dirDeriv (fun p ↦ convPolyEmb (mockModeW true M L k c_g n p)) R
    -- Obtain tail bounds for `δ_n` and `δ_{n+1}`!
    obtain ⟨x_n, C_n, hxn_pos, hxn_le, hCn_nn, hδn_bd⟩ := htail_bd n
    obtain ⟨x_n1, C_n1, hxn1_pos, hxn1_le, hCn1_nn, hδn1_bd⟩ := htail_bd (n + 1)
    -- Choose `u₁ ≤ min x_n x_n1` small enough that `‖δ_n(x)‖ ≤ 1` on `(0, u₁)`!
    -- Since `C_n * x^{-(3+2r)} * exp(-ω n / x) → 0` as `x → 0⁺`, take explicit `u₁` using `exp(ω n / x) ≥ (ω n / x)^{3+2r+1} / (3+2r+1)!`!
    let K_deg : ℕ := 3 + 2 * r
    let u₁ : ℝ := min (min x_n x_n1)
      ((ω n) ^ (K_deg + 1) / ((C_n + 1) * ((K_deg + 1).factorial : ℝ)))
    have hu₁_pos : 0 < u₁ := lt_min (lt_min hxn_pos hxn1_pos) (by positivity)
    have hu₁_le_x₀ : u₁ ≤ x₀ := ((min_le_left _ _).trans (min_le_left _ _)).trans hxn_le
    -- Uniform bound on `R.coeff μ` over `(0, x₀)`:
    have hcoeff_bd : ∀ x ∈ Set.Ioo (0 : ℝ) x₀, ∀ μ, ‖psEval (R.coeff μ).val (x : ℂ)‖ ≤ 2 * M_R := by
      intro x hx μ
      have hsum := isConvergentOn_summable (hR_conv μ) (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]; exact lt_trans hx.2 hx₀_lt_ρ)
      have hgeom : Summable (fun m : ℕ ↦ M_R * (1 / 2 : ℝ) ^ m) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M_R
      have hterm : ∀ m : ℕ, ‖(R.coeff μ).val.coeff m * (x : ℂ) ^ m‖ ≤ M_R * (1 / 2 : ℝ) ^ m := by
        intro m
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
        have h1 := (hR_conv μ).2.2 m
        have h2 : x ^ m ≤ (ρ / 2) ^ m := pow_le_pow_left₀ hx.1.le (hx.2.le.trans hx₀_le_half) m
        calc ‖(R.coeff μ).val.coeff m‖ * x ^ m ≤ ‖(R.coeff μ).val.coeff m‖ * (ρ / 2) ^ m :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = (‖(R.coeff μ).val.coeff m‖ * ρ ^ m) * (1 / 2 : ℝ) ^ m := by rw [div_pow, one_div, inv_pow]; ring
          _ ≤ M_R * (1 / 2 : ℝ) ^ m := mul_le_mul_of_nonneg_right h1 (by positivity)
      calc ‖psEval (R.coeff μ).val (x : ℂ)‖
          ≤ ∑' m : ℕ, ‖(R.coeff μ).val.coeff m * (x : ℂ) ^ m‖ := norm_tsum_le_tsum_norm hsum.norm
        _ ≤ ∑' m : ℕ, M_R * (1 / 2 : ℝ) ^ m := Summable.tsum_le_tsum hterm hsum.norm hgeom
        _ = M_R * (1 - 1 / 2)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        _ = 2 * M_R := by ring
    -- Uniform bound on `‖aeval (YMinus x) (pderiv p (evalAtConv x R))‖ ≤ B_grad` on `(0, x₀)`:
    let B_grad : ℝ := ∑ p : Fin s × Fin (r + 1),
      ∑ μ ∈ (MvPolynomial.pderiv p R).support, (2 * M_R * ((μ p + 1 : ℕ) : ℝ)) * B_Z ^ R.totalDegree
    have hBgrad_nn : 0 ≤ B_grad := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity
    -- Bound `‖evalAtConv x F_int (YMinus x) + √x * evalAtConv x F_half (YMinus x)‖ ≤ K_err * exp(-(δ_freq / 2) / x)`!
    -- Wait: absorb `x^{-K_deg} * exp(-(δ_freq / 2) / x)` into a constant `K_abs` so total RHS is `K_tot * exp(-(δ_freq / 2) / x)`!
    let K_rem_c : ℝ := (R.support.card : ℝ) * (2 * M_R * (2 * B_Z) ^ R.totalDegree)
    have hKrem_nn : 0 ≤ K_rem_c := by positivity
    -- Elementary polynomial-in-`1/x` times `exp(-(δ_freq / 2) / x)` bound:
    have hpow_exp_abs : ∀ d : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x →
        x ^ (-(d : ℤ)) * Real.exp (-(δ_freq / 2) / x) ≤ K := fun d ↦ by
      refine ⟨(d.factorial : ℝ) / (δ_freq / 2) ^ d, by positivity, fun x hx ↦ ?_⟩
      have hge := Real.pow_div_factorial_le_exp ((δ_freq / 2) / x) (by positivity) d
      have hle : Real.exp (-(δ_freq / 2) / x) ≤ (d.factorial : ℝ) * x ^ d / (δ_freq / 2) ^ d := by
        rw [neg_div, Real.exp_neg]
        calc (Real.exp ((δ_freq / 2) / x))⁻¹ ≤ (((δ_freq / 2) / x) ^ d / (d.factorial : ℝ))⁻¹ :=
              inv_anti₀ (by positivity) hge
          _ = (d.factorial : ℝ) * x ^ d / (δ_freq / 2) ^ d := by rw [inv_div, div_pow, div_div_eq_mul_div]
      calc x ^ (-(d : ℤ)) * Real.exp (-(δ_freq / 2) / x)
          ≤ x ^ (-(d : ℤ)) * ((d.factorial : ℝ) * x ^ d / (δ_freq / 2) ^ d) :=
            mul_le_mul_of_nonneg_left hle (zpow_nonneg hx.le _)
        _ = (d.factorial : ℝ) / (δ_freq / 2) ^ d := by
            rw [zpow_neg, zpow_natCast]; field_simp [(pow_pos hx d).ne', (pow_pos (show 0 < δ_freq / 2 by positivity) d).ne']
    obtain ⟨K_abs1, hKabs1_nn, hKabs1_bd⟩ := hpow_exp_abs 0
    obtain ⟨K_abs2, hKabs2_nn, hKabs2_bd⟩ := hpow_exp_abs K_deg
    let K_tot : ℝ := B_grad * C_n1 * K_abs1 + K_rem_c * C_n ^ 2 * K_abs2
    have hKtot_nn : 0 ≤ K_tot := by positivity
    -- Pointwise exponential bound on `x ∈ (0, u₁)`!
    have hparity_bd : ∀ x ∈ Set.Ioo (0 : ℝ) u₁,
        ‖MvPolynomial.aeval (YMinus x) (evalAtConv (x : ℂ) F_int) +
          ((Real.sqrt x : ℝ) : ℂ) * MvPolynomial.aeval (YMinus x) (evalAtConv (x : ℂ) F_half)‖ ≤
          K_tot * Real.exp (-(δ_freq / 2) / x) := by
      intro x hx
      have hx_x₀ : x ∈ Set.Ioo (0 : ℝ) x₀ := ⟨hx.1, lt_of_lt_of_le hx.2 hu₁_le_x₀⟩
      have hx_lt_ρ : ‖(x : ℂ)‖ < ρ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]; exact lt_trans hx_x₀.2 hx₀_lt_ρ
      have hx_xn : x ∈ Set.Ioo (0 : ℝ) x_n := ⟨hx.1, lt_of_lt_of_le hx.2 ((min_le_left _ _).trans (min_le_left _ _))⟩
      have hx_xn1 : x ∈ Set.Ioo (0 : ℝ) x_n1 := ⟨hx.1, lt_of_lt_of_le hx.2 ((min_le_left _ _).trans (min_le_right _ _))⟩
      -- 1. Split `YPlus x = YMinus x + ∑_{ℓ < n} e^{-ω_ℓ/x} v_ℓ(x) + δ_n(x)`!
      let δ_n : Fin s × Fin (r + 1) → ℂ := fun p ↦
        ∑' t : ℕ, ((Real.exp (-ω (n + t) / x) : ℝ) : ℂ) * v_mode (n + t) x p
      let δ_n1 : Fin s × Fin (r + 1) → ℂ := fun p ↦
        ∑' t : ℕ, ((Real.exp (-ω (n + 1 + t) / x) : ℝ) : ℂ) * v_mode (n + 1 + t) x p
      have hY_split : YPlus x = fun p ↦
          YMinus x p + (∑ ℓ ∈ Finset.range n, ((Real.exp (-ω ℓ / x) : ℝ) : ℂ) * v_mode ℓ x p) + δ_n p := by
        ext p
        have hsum_all : Summable (fun m : ℕ ↦ ((Real.exp (-ω m / x) : ℝ) : ℂ) * v_mode m x p) := by
          refine (summable_nat_add_iff n).mp ?_
          have h := (hδn_bd x hx_xn p).1
          simpa [add_comm n] using h
        have hsp := hsum_all.sum_add_tsum_nat_add n
        have hj := hjump x hx_x₀ p
        rw [← hsp] at hj
        have hshift_eq : (∑' t : ℕ, ((Real.exp (-ω (t + n) / x) : ℝ) : ℂ) * v_mode (t + n) x p) = δ_n p := by
          dsimp [δ_n]; apply tsum_congr; intro t; rw [add_comm t n]
        rw [hshift_eq] at hj
        linear_combination hj
      -- 2. Apply `mockModular_translation_invariance_kills_linear_collisions` to remove ALL modes `ℓ < n` EXACTLY!
      have hdir_v : ∀ ℓ ∈ Finset.range n, dirDeriv (v_mode ℓ x) (evalAtConv (x : ℂ) R) = 0 := by
        intro ℓ hℓ
        have hℓ_lt : ℓ < n := Finset.mem_range.mp hℓ
        have ⟨hI0, hH0⟩ := ih ℓ hℓ_lt
        have hI_eval : dirDeriv (fun p ↦ (mockModeW false M L k c_g ℓ p).eval (x : ℂ)) (evalAtConv (x : ℂ) R) = 0 := by
          rw [evalAtConv_dirDeriv_poly R hR_conv _ hx_lt_ρ, hI0]; simp [evalAtConv]
        have hH_eval : dirDeriv (fun p ↦ (mockModeW true M L k c_g ℓ p).eval (x : ℂ)) (evalAtConv (x : ℂ) R) = 0 := by
          rw [evalAtConv_dirDeriv_poly R hR_conv _ hx_lt_ρ, hH0]; simp [evalAtConv]
        have hxK_ne : ((x : ℂ) ^ (3 + 2 * r)) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hx.1.ne')
        have hmul0 : MvPolynomial.C ((x : ℂ) ^ (3 + 2 * r)) * dirDeriv (v_mode ℓ x) (evalAtConv (x : ℂ) R) = 0 := by
          have hlhs : MvPolynomial.C ((x : ℂ) ^ (3 + 2 * r)) * dirDeriv (v_mode ℓ x) (evalAtConv (x : ℂ) R) =
              dirDeriv (fun p ↦ (mockModeW false M L k c_g ℓ p).eval (x : ℂ)) (evalAtConv (x : ℂ) R) +
              MvPolynomial.C ((Real.sqrt x : ℝ) : ℂ) *
                dirDeriv (fun p ↦ (mockModeW true M L k c_g ℓ p).eval (x : ℂ)) (evalAtConv (x : ℂ) R) := by
            simp only [dirDeriv, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro p _
            rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← add_mul, ← map_add, hv_parity ℓ x hx.1 p]
          rw [hlhs, hI_eval, hH_eval, mul_zero, add_zero]
        exact (mul_eq_zero.mp hmul0).resolve_left (fun h ↦ hxK_ne (MvPolynomial.C_eq_zero.mp h))
      have htrans := mockModular_translation_invariance_kills_linear_collisions
        (A := ℂ) (B := ℂ) (Finset.range n) (fun ℓ ↦ v_mode ℓ x) (evalAtConv (x : ℂ) R) hdir_v
        (YMinus x) (fun ℓ ↦ ((Real.exp (-ω ℓ / x) : ℝ) : ℂ)) δ_n
      have hR_shifted : MvPolynomial.aeval (fun p ↦ YMinus x p + δ_n p) (evalAtConv (x : ℂ) R) = 0 := by
        rw [← htrans]
        have heq : (fun p ↦ YMinus x p + (∑ ℓ ∈ Finset.range n, ((Real.exp (-ω ℓ / x) : ℝ) : ℂ) * v_mode ℓ x p) + δ_n p) =
            YPlus x := hY_split.symm
        simp only [Algebra.algebraMap_self, RingHom.id_apply]
        rw [heq]; exact (hlat x hx_x₀).1
      -- 3. Taylor expand `R_x(YMinus x + δ_n) = 0` using `mockModular_taylor_expansion`!
      have htay := mockModular_taylor_expansion (A := ℂ) (B := ℂ) (evalAtConv (x : ℂ) R) (YMinus x) δ_n
      dsimp only at htay
      rw [hR_shifted, (hlat x hx_x₀).2, zero_add] at htay
      -- Split `δ_n p = exp(-ω n / x) * v_mode n x p + δ_n1 p`!
      have hδn_split : ∀ p, δ_n p = ((Real.exp (-ω n / x) : ℝ) : ℂ) * v_mode n x p + δ_n1 p := fun p ↦ by
        dsimp [δ_n, δ_n1]
        have hsum := (hδn_bd x hx_xn p).1
        rw [hsum.tsum_eq_zero_add, add_zero]
        congr 1; apply tsum_congr; intro t; rw [show n + (t + 1) = n + 1 + t by omega]
      -- Multiply `htay` by `x^{3 + 2r} * exp(ω n / x)`!
      let Rem2 : ℂ := ∑ m ∈ (Finset.range ((MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap ℂ ℂ))
          (fun p ↦ Polynomial.C (YMinus x p) + Polynomial.C (δ_n p) * Polynomial.X)
          (evalAtConv (x : ℂ) R)).natDegree + 1)).filter (2 ≤ ·),
        (MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap ℂ ℂ))
          (fun p ↦ Polynomial.C (YMinus x p) + Polynomial.C (δ_n p) * Polynomial.X)
          (evalAtConv (x : ℂ) R)).coeff m
      have hlin_id :
          MvPolynomial.aeval (YMinus x) (evalAtConv (x : ℂ) F_int) +
          ((Real.sqrt x : ℝ) : ℂ) * MvPolynomial.aeval (YMinus x) (evalAtConv (x : ℂ) F_half) =
          -(x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) *
            ((∑ p : Fin s × Fin (r + 1), δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))) +
              Rem2) := by
        have hF_sum :
            MvPolynomial.aeval (YMinus x) (evalAtConv (x : ℂ) F_int) +
            ((Real.sqrt x : ℝ) : ℂ) * MvPolynomial.aeval (YMinus x) (evalAtConv (x : ℂ) F_half) =
            (x : ℂ) ^ (3 + 2 * r) *
              ∑ p : Fin s × Fin (r + 1), v_mode n x p *
                MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R)) := by
          dsimp [F_int, F_half]
          rw [← evalAtConv_dirDeriv_poly R hR_conv _ hx_lt_ρ, ← evalAtConv_dirDeriv_poly R hR_conv _ hx_lt_ρ]
          simp only [dirDeriv, map_sum, map_mul, MvPolynomial.eval_C, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p _
          have hp := hv_parity n x hx.1 p
          linear_combination MvPolynomial.eval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R)) * hp.symm
        rw [hF_sum]
        have hsplit_sum :
            ∑ p : Fin s × Fin (r + 1), δ_n p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R)) =
            ((Real.exp (-ω n / x) : ℝ) : ℂ) *
              (∑ p : Fin s × Fin (r + 1), v_mode n x p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))) +
            ∑ p : Fin s × Fin (r + 1), δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p _
          rw [hδn_split p]; ring
        have hexp_cancel : ((Real.exp (ω n / x) : ℝ) : ℂ) * ((Real.exp (-ω n / x) : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, ← Real.exp_add, show ω n / x + -ω n / x = 0 by ring, Real.exp_zero, Complex.ofReal_one]
        have htay' : (∑ p : Fin s × Fin (r + 1), δ_n p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))) + Rem2 = 0 :=
          htay.symm
        rw [hsplit_sum] at htay'
        linear_combination
          (x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) * htay' -
          (x : ℂ) ^ (3 + 2 * r) *
            (∑ p : Fin s × Fin (r + 1), v_mode n x p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))) *
            hexp_cancel
      rw [hlin_id]
      -- 4. Bound both pieces cleanly using `evalAtConv_grad_le` and `evalAtConv_taylor_rem_le`!
      have hx_pos : 0 < x := hx.1
      have hK_int : (-(3 + 2 * r : ℤ)) = -((3 + 2 * r : ℕ) : ℤ) := by push_cast; ring
      have hx_zpow_nn : 0 ≤ x ^ (-(3 + 2 * r : ℤ)) := zpow_nonneg hx_pos.le _
      have hterm1 :
          ‖(x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) *
            ∑ p : Fin s × Fin (r + 1), δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))‖ ≤
          B_grad * C_n1 * K_abs1 * Real.exp (-(δ_freq / 2) / x) := by
        have hsum_δ1 : ‖∑ p : Fin s × Fin (r + 1),
              δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))‖ ≤
            B_grad * (C_n1 * x ^ (-(3 + 2 * r : ℤ)) * Real.exp (-ω (n + 1) / x)) := by
          dsimp [B_grad]; rw [Finset.sum_mul]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
          rw [norm_mul, mul_comm (∑ μ ∈ _, _)]
          exact mul_le_mul (hδn1_bd x hx_xn1 p).2
            (evalAtConv_grad_le hMR_nn hBZ_ge1 R hR_conv hx_lt_ρ (hcoeff_bd x hx_x₀) (hYMinus_le x hx_x₀) p)
            (norm_nonneg _) (by positivity)
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hx_pos, abs_of_pos (Real.exp_pos _)]
        have hx_cancel : x ^ (3 + 2 * r) * x ^ (-(3 + 2 * r : ℤ)) = 1 := by
          rw [hK_int, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_pos hx_pos _).ne']
        have hexp_diff : Real.exp (ω n / x) * Real.exp (-ω (n + 1) / x) =
            Real.exp (-(δ_freq / 2) / x) * Real.exp (-(δ_freq / 2) / x) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1
          dsimp [ω]; push_cast; ring
        have hK1_ge : Real.exp (-(δ_freq / 2) / x) ≤ K_abs1 := by
          simpa using hKabs1_bd x hx_pos
        calc x ^ (3 + 2 * r) * Real.exp (ω n / x) *
              ‖∑ p, δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))‖
            ≤ x ^ (3 + 2 * r) * Real.exp (ω n / x) *
                (B_grad * (C_n1 * x ^ (-(3 + 2 * r : ℤ)) * Real.exp (-ω (n + 1) / x))) :=
              mul_le_mul_of_nonneg_left hsum_δ1 (by positivity)
          _ = B_grad * C_n1 * (x ^ (3 + 2 * r) * x ^ (-(3 + 2 * r : ℤ))) *
                (Real.exp (ω n / x) * Real.exp (-ω (n + 1) / x)) := by ring
          _ = B_grad * C_n1 * Real.exp (-(δ_freq / 2) / x) * Real.exp (-(δ_freq / 2) / x) := by
              rw [hx_cancel, mul_one, hexp_diff]; ring
          _ ≤ B_grad * C_n1 * K_abs1 * Real.exp (-(δ_freq / 2) / x) := by
              have hnn : 0 ≤ B_grad * C_n1 := mul_nonneg hBgrad_nn hCn1_nn
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK1_ge hnn) (Real.exp_pos _).le
      have hterm2 :
          ‖(x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) * Rem2‖ ≤
          K_rem_c * C_n ^ 2 * K_abs2 * Real.exp (-(δ_freq / 2) / x) := by
        let B_δ : ℝ := C_n * x ^ (-(3 + 2 * r : ℤ)) * Real.exp (-ω n / x)
        have hBδ_nn : 0 ≤ B_δ := by dsimp [B_δ]; positivity
        have hωn_pos : 0 < ω n := hω_pos n
        have hBδ_le1 : B_δ ≤ 1 := by
          have hexp_ge := Real.pow_div_factorial_le_exp (ω n / x) (by positivity) (K_deg + 1)
          have hexp_le : Real.exp (-ω n / x) ≤ ((K_deg + 1).factorial : ℝ) * x ^ (K_deg + 1) / (ω n) ^ (K_deg + 1) := by
            rw [neg_div, Real.exp_neg]
            calc (Real.exp (ω n / x))⁻¹ ≤ ((ω n / x) ^ (K_deg + 1) / ((K_deg + 1).factorial : ℝ))⁻¹ :=
                  inv_anti₀ (by positivity) hexp_ge
              _ = ((K_deg + 1).factorial : ℝ) * x ^ (K_deg + 1) / (ω n) ^ (K_deg + 1) := by
                  rw [inv_div, div_pow, div_div_eq_mul_div]
          have hxu : x ≤ (ω n) ^ (K_deg + 1) / ((C_n + 1) * ((K_deg + 1).factorial : ℝ)) :=
            hx.2.le.trans (min_le_right _ _)
          have hK_eq : (-(3 + 2 * r : ℤ)) = -(K_deg : ℤ) := by dsimp [K_deg]
          dsimp [B_δ]; rw [hK_eq]
          calc C_n * x ^ (-(K_deg : ℤ)) * Real.exp (-ω n / x)
              ≤ (C_n + 1) * x ^ (-(K_deg : ℤ)) * (((K_deg + 1).factorial : ℝ) * x ^ (K_deg + 1) / (ω n) ^ (K_deg + 1)) := by
                have h1 : C_n * x ^ (-(K_deg : ℤ)) ≤ (C_n + 1) * x ^ (-(K_deg : ℤ)) :=
                  mul_le_mul_of_nonneg_right (by linarith) (zpow_nonneg hx_pos.le _)
                exact mul_le_mul h1 hexp_le (Real.exp_pos _).le (mul_nonneg (by linarith) (zpow_nonneg hx_pos.le _))
            _ = (C_n + 1) * ((K_deg + 1).factorial : ℝ) / (ω n) ^ (K_deg + 1) * x := by
                rw [zpow_neg, zpow_natCast, pow_succ]
                field_simp [(pow_pos hx_pos K_deg).ne', (pow_pos hωn_pos _).ne']
            _ ≤ (C_n + 1) * ((K_deg + 1).factorial : ℝ) / (ω n) ^ (K_deg + 1) *
                  ((ω n) ^ (K_deg + 1) / ((C_n + 1) * ((K_deg + 1).factorial : ℝ))) :=
                mul_le_mul_of_nonneg_left hxu (by positivity)
            _ = 1 := by
                have h1 : C_n + 1 ≠ 0 := by linarith
                have h2 : ((K_deg + 1).factorial : ℝ) ≠ 0 := by positivity
                have h3 : (ω n) ^ (K_deg + 1) ≠ 0 := (pow_pos hωn_pos _).ne'
                field_simp [h1, h2, h3]
        have hRem_le' : ‖Rem2‖ ≤ K_rem_c * B_δ ^ 2 := by
          simpa only [Rem2, K_rem_c, mul_assoc] using
            evalAtConv_taylor_rem_le hMR_nn hBZ_ge1 hBδ_nn hBδ_le1 R (x : ℂ) (hcoeff_bd x hx_x₀)
              (YMinus x) δ_n (hYMinus_le x hx_x₀) (fun p ↦ (hδn_bd x hx_xn p).2)
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hx_pos, abs_of_pos (Real.exp_pos _)]
        have hexp_2 : Real.exp (ω n / x) * (Real.exp (-ω n / x)) ^ 2 ≤
            Real.exp (-(δ_freq / 2) / x) * Real.exp (-(δ_freq / 2) / x) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hω_ge : δ_freq ≤ ω n := by
            dsimp [ω]; exact le_mul_of_one_le_right hδ_pos.le (by exact_mod_cast Nat.succ_pos n)
          have hdiv : δ_freq / x ≤ ω n / x := div_le_div_of_nonneg_right hω_ge hx_pos.le
          push_cast; linarith [show -(δ_freq / 2) / x + -(δ_freq / 2) / x = -(δ_freq / x) by ring,
            show ω n / x + 2 * (-ω n / x) = -(ω n / x) by ring]
        have hx_zpow : x ^ (3 + 2 * r) * (x ^ (-(3 + 2 * r : ℤ))) ^ 2 = x ^ (-(K_deg : ℤ)) := by
          rw [hK_int, zpow_neg, zpow_natCast, sq]
          field_simp [(pow_pos hx_pos (3 + 2 * r)).ne']
        have hKrem_c2_nn : 0 ≤ K_rem_c * C_n ^ 2 := mul_nonneg hKrem_nn (sq_nonneg _)
        calc x ^ (3 + 2 * r) * Real.exp (ω n / x) * ‖Rem2‖
            ≤ x ^ (3 + 2 * r) * Real.exp (ω n / x) * (K_rem_c * B_δ ^ 2) :=
              mul_le_mul_of_nonneg_left hRem_le' (by positivity)
          _ = K_rem_c * C_n ^ 2 * (x ^ (3 + 2 * r) * (x ^ (-(3 + 2 * r : ℤ))) ^ 2) *
                (Real.exp (ω n / x) * (Real.exp (-ω n / x)) ^ 2) := by dsimp [B_δ]; ring
          _ ≤ K_rem_c * C_n ^ 2 * x ^ (-(K_deg : ℤ)) *
                (Real.exp (-(δ_freq / 2) / x) * Real.exp (-(δ_freq / 2) / x)) := by
              rw [hx_zpow]
              exact mul_le_mul_of_nonneg_left hexp_2 (mul_nonneg hKrem_c2_nn (zpow_nonneg hx_pos.le _))
          _ = K_rem_c * C_n ^ 2 * (x ^ (-(K_deg : ℤ)) * Real.exp (-(δ_freq / 2) / x)) *
                Real.exp (-(δ_freq / 2) / x) := by ring
          _ ≤ K_rem_c * C_n ^ 2 * K_abs2 * Real.exp (-(δ_freq / 2) / x) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hKabs2_bd x hx_pos) hKrem_c2_nn) (Real.exp_pos _).le
      have hneg_add :
          -(x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) *
            ((∑ p : Fin s × Fin (r + 1), δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))) +
              Rem2) =
          -((x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) *
              (∑ p : Fin s × Fin (r + 1), δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))) +
            (x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) * Rem2) := by ring
      rw [hneg_add, norm_neg]
      calc ‖(x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) *
              (∑ p, δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R))) +
            (x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) * Rem2‖
          ≤ ‖(x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) *
              (∑ p, δ_n1 p * MvPolynomial.aeval (YMinus x) (MvPolynomial.pderiv p (evalAtConv (x : ℂ) R)))‖ +
            ‖(x : ℂ) ^ (3 + 2 * r) * ((Real.exp (ω n / x) : ℝ) : ℂ) * Rem2‖ := norm_add_le _ _
        _ ≤ B_grad * C_n1 * K_abs1 * Real.exp (-(δ_freq / 2) / x) +
              K_rem_c * C_n ^ 2 * K_abs2 * Real.exp (-(δ_freq / 2) / x) := add_le_add hterm1 hterm2
        _ = K_tot * Real.exp (-(δ_freq / 2) / x) := by dsimp [K_tot]; ring
    -- 5. Apply `half_parity_scale_separation` + `evalAtConv_hasRealAsymp`!
    obtain ⟨ρ_I, M_I, hρI_pos, _, hFI_conv⟩ := mvPoly_conv_common_radius F_int
    obtain ⟨ρ_H, M_H, hρH_pos, _, hFH_conv⟩ := mvPoly_conv_common_radius F_half
    let u₂ : ℝ := min u₁ (min (ρ_I / 2) (ρ_H / 2))
    have hu₂_pos : 0 < u₂ := lt_min hu₁_pos (lt_min (by linarith) (by linarith))
    have hY_u₂ : ∀ p, HasRealAsymp u₂ (fun x ↦ YMinus x p) (fun m ↦ (Yhat p).coeff m) := fun p N ↦ by
      obtain ⟨C, hC, hbN⟩ := hYMinus_asymp p N
      exact ⟨C, hC, fun x hx ↦ hbN x ⟨hx.1, lt_of_lt_of_le hx.2 ((min_le_left _ _).trans hu₁_le_x₀)⟩⟩
    have hFI_asymp := evalAtConv_hasRealAsymp hu₂_pos ((min_le_right _ _).trans (min_le_left _ _)) F_int hFI_conv hY_u₂
    have hFH_asymp := evalAtConv_hasRealAsymp hu₂_pos ((min_le_right _ _).trans (min_le_right _ _)) F_half hFH_conv hY_u₂
    have ⟨hFI_hat0, hFH_hat0⟩ := half_parity_scale_separation hu₂_pos (show 0 < δ_freq / 2 by positivity)
      hKtot_nn hFI_asymp hFH_asymp (fun x hx ↦ hparity_bd x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩)
    have hFI_ann : MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype F_int) = 0 := by
      ext m; rw [hFI_hat0 m, map_zero]
    have hFH_ann : MvPolynomial.aeval Yhat (MvPolynomial.map convergentSubring.subtype F_half) = 0 := by
      ext m; rw [hFH_hat0 m, map_zero]
    -- 6. By `dirDeriv_totalDegree_lt` + minimality of `R`, BOTH `F_int = 0` and `F_half = 0`!
    refine ⟨?_, ?_⟩
    · by_contra hne
      have hle := hR_min F_int hne hFI_ann
      have hlt := dirDeriv_totalDegree_lt (fun p ↦ convPolyEmb (mockModeW false M L k c_g n p)) hR_deg
      dsimp [F_int] at hle; omega
    · by_contra hne
      have hle := hR_min F_half hne hFH_ann
      have hlt := dirDeriv_totalDegree_lt (fun p ↦ convPolyEmb (mockModeW true M L k c_g n p)) hR_deg
      dsimp [F_half] at hle; omega

/-- Helper: `MvPolynomial.rename e (MvPolynomial.pderiv p R) = MvPolynomial.pderiv (e p) (MvPolynomial.rename e R)`
for any equivalence `e : ι₁ ≃ ι₂`. -/
theorem rename_pderiv_equiv {ι₁ ι₂ A : Type*} [CommRing A] (e : ι₁ ≃ ι₂) (p : ι₁)
    (R : MvPolynomial ι₁ A) :
    MvPolynomial.rename e (MvPolynomial.pderiv p R) = MvPolynomial.pderiv (e p) (MvPolynomial.rename e R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f q hf =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.rename_X, hf]
    by_cases h : q = p
    · subst h; simp
    · have he : e q ≠ e p := fun h0 ↦ h (e.injective h0)
      simp [h, he]

/-- **End-to-End Paper #10 Theorem A (Scalar Differential Transcendence from Single-Cusp Split)**:
Suppose a single scalar mock modular form `h` of non-Bol weight `k ∈ {1} ∪ (1/2 + ℤ)_{≤ 3/2}`
has shadow with infinitely many nonzero Fourier coefficients `c_g n` (`‖c_g n‖ ≤ C₀ exp(a ω_n)`,
`a < 1`) and obeys the single-cusp `y = 1` Eichler split + Cauchy `q₁`-expansion for a putative
constant-coefficient ADE `P ∈ ℂ[X₀, …, X_r]` of degree `D = P.totalDegree ≥ 1`.
Then **`False`**! (Wires `q1_induction_kill` → `top_degree_survival` → `minimal_degree_descent`
→ `mockModular_translation_invariance_induction` → `one_div_Gamma_ne_zero_nonBol`
→ `mockModular_minimal_annihilator_contradiction`!) -/
theorem mockModular_scalar_diff_trans_of_cuspSplit {r M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (k : ℂ) (hk : NonBolWeight k)
    (c_g : ℕ → ℂ) {C₀ a : ℝ} (hC₀ : 0 ≤ C₀) (ha : a < 1)
    (hc_bd : ∀ n : ℕ, ‖c_g n‖ ≤ C₀ * Real.exp (a * (2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ))))
    (hc_inf : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c_g n ≠ 0)
    (b : ℂ → ℂ) {C_b c_b : ℝ} (hb : ExpDecayKernel b C_b c_b)
    (hb_ser : ∀ y : ℂ, b y = ∑' n : ℕ,
      (starRingEnd ℂ (c_g n) * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))) *
        Complex.exp (-((2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ) : ℝ) : ℂ) * y))
    (Rtilde : MvPolynomial (Fin 1 × Fin (r + 1)) convergentSubring) (hRtilde_ne : Rtilde ≠ 0)
    (hRtilde_ann : MvPolynomial.aeval
      (fun p : Fin 1 × Fin (r + 1) ↦
        PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff k b p.2.val n))
      (MvPolynomial.map convergentSubring.subtype Rtilde) = 0) :
    False := by
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
  -- Step 1: Minimal-degree descent into `ℂ{x}[Z]`!
  let Yhat : Fin 1 × Fin (r + 1) → PowerSeries ℂ := fun p ↦
    PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff k b p.2.val n)
  obtain ⟨R, hR_ne, hR_deg, hR_ann, hR_min⟩ := minimal_degree_descent Yhat Rtilde hRtilde_ne hRtilde_ann
  -- Step 2: Proposition 5.3 kills EVERY mode directional derivative `W_n^{int}` and `W_n^{half}`!
  have hvan_all := mockModular_translation_invariance_induction (s := 1) (r := r) hM hL
    (fun _ ↦ k) (fun _ ↦ hk) (fun _ ↦ c_g) hC₀ ha (fun _ n ↦ hc_bd n)
    (fun _ ↦ b) (fun _ ↦ C_b) (fun _ ↦ c_b) (fun _ ↦ hb) (fun _ y ↦ hb_ser y)
    R hR_ne hR_deg hR_ann hR_min
  -- Step 3: Pick `r + 1` strictly increasing indices `idx 0 < idx 1 < … < idx r` with `c_g (idx s) ≠ 0`!
  have hex_seq : ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ s : ℕ, c_g (idx s) ≠ 0 := by
    let step : ℕ → ℕ := fun prev ↦ Classical.choose (hc_inf (prev + 1))
    let idx : ℕ → ℕ := Nat.rec (Classical.choose (hc_inf 0)) (fun _ prev ↦ step prev)
    refine ⟨idx, strictMono_nat_of_lt_succ fun s ↦ ?_, fun s ↦ ?_⟩
    · have h := (Classical.choose_spec (hc_inf (idx s + 1))).1
      change idx s < step (idx s); dsimp [step]; omega
    · cases s with
      | zero => exact (Classical.choose_spec (hc_inf 0)).2
      | succ s => exact (Classical.choose_spec (hc_inf (idx s + 1))).2
  obtain ⟨idx, hidx_mono, hidx_ne⟩ := hex_seq
  -- Reindex `R` from `Fin 1 × Fin (r + 1)` to `Fin (r + 1)` via `e : Fin 1 × Fin (r + 1) ≃ Fin (r + 1)`!
  let e : Fin 1 × Fin (r + 1) ≃ Fin (r + 1) :=
    { toFun := fun p ↦ p.2
      invFun := fun j ↦ (0, j)
      left_inv := fun ⟨i, j⟩ ↦ Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl }
  let R' : MvPolynomial (Fin (r + 1)) convergentSubring := MvPolynomial.rename e R
  have hR'_deg : 0 < R'.totalDegree := by
    have hdeg_eq : R'.totalDegree = R.totalDegree := by
      apply le_antisymm
      · exact MvPolynomial.totalDegree_rename_le e R
      · have hback : MvPolynomial.rename e.symm R' = R := by
          dsimp [R']; rw [MvPolynomial.rename_rename]; simp
        rw [← hback]; exact MvPolynomial.totalDegree_rename_le e.symm R'
    rw [hdeg_eq]; exact hR_deg
  let ω_sub : Fin (r + 1) → ℂ := fun s ↦ ((2 * Real.pi * ((idx s.val + 1 : ℕ) : ℝ) / (L : ℝ) : ℝ) : ℂ)
  have hω_inj : Function.Injective ω_sub := by
    intro s₁ s₂ heq
    have hR := Complex.ofReal_injective heq
    have hmul : 2 * Real.pi * ((idx s₁.val + 1 : ℕ) : ℝ) = 2 * Real.pi * ((idx s₂.val + 1 : ℕ) : ℝ) := by
      have := congrArg (· * (L : ℝ)) hR
      rwa [div_mul_cancel₀ _ hL_pos.ne', div_mul_cancel₀ _ hL_pos.ne'] at this
    have hcast : ((idx s₁.val + 1 : ℕ) : ℝ) = ((idx s₂.val + 1 : ℕ) : ℝ) :=
      mul_left_cancel₀ (mul_pos two_pos Real.pi_pos).ne' hmul
    have hnat : idx s₁.val = idx s₂.val := by
      have : idx s₁.val + 1 = idx s₂.val + 1 := by exact_mod_cast hcast
      omega
    exact Fin.ext (hidx_mono.injective hnat)
  let α_sub : Fin (r + 1) → convergentSubring := fun s ↦
    let n := idx s.val
    let phase : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))
    convPolyEmb (Polynomial.C (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma k) *
      starRingEnd ℂ (c_g n) * phase * (ω_sub s) ^ (k - 1)) * Polynomial.X ^ nonBolShift k)
  have hα_ne : ∀ s : Fin (r + 1), α_sub s ≠ 0 := fun s h0 ↦ by
    have hp0 : Polynomial.C (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma k) *
        starRingEnd ℂ (c_g (idx s.val)) *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((idx s.val + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ))) *
        (ω_sub s) ^ (k - 1)) * Polynomial.X ^ nonBolShift k = 0 :=
      convPolyEmb_injective (h0.trans (map_zero convPolyEmb).symm)
    have hC0 := (mul_eq_zero.mp hp0).resolve_right (pow_ne_zero _ Polynomial.X_ne_zero)
    rw [Polynomial.C_eq_zero] at hC0
    have h1 : -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma k) ≠ 0 := by
      rw [neg_ne_zero, div_eq_mul_inv]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
        Complex.I_ne_zero) (nonBolWeight_inv_Gamma_ne_zero hk)
    have h2 : starRingEnd ℂ (c_g (idx s.val)) ≠ 0 := by
      intro h; exact hidx_ne s.val (by simpa using congrArg (starRingEnd ℂ) h)
    have h3 : Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((idx s.val + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ))) ≠ 0 :=
      Complex.exp_ne_zero _
    have h4 : (ω_sub s) ^ (k - 1) ≠ 0 := by
      have hω_pos : (0 : ℝ) < 2 * Real.pi * ((idx s.val + 1 : ℕ) : ℝ) / (L : ℝ) := by positivity
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hω_pos.ne')]
      exact Complex.exp_ne_zero _
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4 hC0
  have hvan' : ∀ s : Fin (r + 1),
      dirDeriv (fun j : Fin (r + 1) ↦ α_sub s * convPolyEmb (mockJetP k r j.val (ω_sub s))) R' = 0 := by
    intro s
    have hvan_s : dirDeriv (fun p ↦ convPolyEmb (mockModeW (nonBolIsHalf k) M L (fun _ ↦ k) (fun _ ↦ c_g) (idx s.val) p)) R = 0 := by
      cases hpar : nonBolIsHalf k
      · exact (hvan_all (idx s.val)).1
      · exact (hvan_all (idx s.val)).2
    have hren := congrArg (MvPolynomial.rename e) hvan_s
    rw [map_zero] at hren
    have hdir_ren : MvPolynomial.rename e
        (dirDeriv (fun p ↦ convPolyEmb (mockModeW (nonBolIsHalf k) M L (fun _ ↦ k) (fun _ ↦ c_g) (idx s.val) p)) R) =
        dirDeriv (fun j : Fin (r + 1) ↦ α_sub s * convPolyEmb (mockJetP k r j.val (ω_sub s))) R' := by
      simp only [dirDeriv, map_sum, map_mul, MvPolynomial.rename_C]
      refine Fintype.sum_equiv e _ _ fun p ↦ ?_
      have hW_eq : convPolyEmb (mockModeW (nonBolIsHalf k) M L (fun _ ↦ k) (fun _ ↦ c_g) (idx s.val) p) =
          α_sub s * convPolyEmb (mockJetP k r (e p).val (ω_sub s)) := by
        dsimp [mockModeW, α_sub, e, ω_sub]
        simp only [↓reduceIte, ← map_mul, mul_assoc]
      have hpd : MvPolynomial.rename e (MvPolynomial.pderiv p R) = MvPolynomial.pderiv (e p) R' :=
        rename_pderiv_equiv e p R
      rw [hW_eq, hpd, map_mul]
    rw [← hdir_ren]; exact hren
  -- Step 4: Immediate contradiction via `mockModular_minimal_annihilator_contradiction`!
  exact mockModular_minimal_annihilator_contradiction convPolyEmb convPolyEmb_injective k ω_sub hω_inj
    α_sub hα_ne R' hR'_deg hvan'

/-- **End-to-End Paper #10 Theorem B (Joint Shadow-Rank Independence from Single-Cusp Split)**:
Let `g₁, …, g_s` be `ℂ`-linearly independent positive-weight holomorphic modular forms on `ℍ`
of weights `w_i = 2 - k_i ∈ (1/2) ℤ_{> 0}` (`k_i ∈ {1} ∪ (1/2 + ℤ)_{≤ 3/2}`), obeying common
`γ_n`-modularity (`M ≥ 1`) and `T^L`-periodicity (`L ≥ 1`), with Fourier expansions
`g_i(τ) = c₀ i + ∑' n, c_g i n * exp(2π i (n + 1) τ / L)` (`‖c_g i n‖ ≤ C₀ exp(a ω_n)`, `a < 1`).
Then there exists **NO** nonzero convergent polynomial `Rtilde ∈ ℂ{x}[(Z_{i,j})]` annihilating
the joint formal Eichler jet `Yhat(x)` (and hence **NO** nonzero constant-coefficient polynomial
differential relation among the mock modular forms `h₁, …, h_s`!)!
(Wires `minimal_degree_descent` → `mockModular_translation_invariance_induction` →
exact `[Z^α]` and `[x^{ν_min}]` extraction → `one_div_Gamma_ne_zero_nonBol` →
**`positiveWeight_modular_thetaQ_diff_indep`** from `MockModularAlgebraCore`!) -/
theorem mockModular_joint_shadow_rank_of_cuspSplit {s r M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (k : Fin s → ℂ) (hk : ∀ i, NonBolWeight (k i))
    (w_twice : Fin s → ℕ) (hw_pos : ∀ i, 1 ≤ w_twice i)
    (_hw_eq : ∀ i, (w_twice i : ℂ) / 2 = 2 - k i)
    (g : Fin s → ℂ → ℂ) (hg_diff : ∀ i, DifferentiableOn ℂ (g i) upperHalfPlane)
    (hg_mod : ∀ i n, 1 ≤ n → ∀ τ ∈ upperHalfPlane,
      g i (τ / (((n * M : ℕ) : ℂ) * τ + 1)) =
        ((((n * M : ℕ) : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ (w_twice i) * g i τ)
    (hg_per : ∀ i (n : ℤ), ∀ τ ∈ upperHalfPlane,
      g i (τ + ((n * (L : ℤ) : ℤ) : ℂ)) = g i τ)
    (hg_lin : ∀ c : Fin s → ℂ, (∀ τ ∈ upperHalfPlane, ∑ i : Fin s, c i * g i τ = 0) → c = 0)
    (c₀ : Fin s → ℂ) (c_g : Fin s → ℕ → ℂ) {C₀ a : ℝ} (hC₀ : 0 ≤ C₀) (ha : a < 1)
    (hc_bd : ∀ i n, ‖c_g i n‖ ≤ C₀ * Real.exp (a * (2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ))))
    (hg_fourier : ∀ i, ∀ τ ∈ upperHalfPlane,
      g i τ - c₀ i = ∑' n : ℕ, c_g i n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) * τ / (L : ℂ)))
    (b : Fin s → ℂ → ℂ) (C_b c_b : Fin s → ℝ)
    (hb : ∀ i, ExpDecayKernel (b i) (C_b i) (c_b i))
    (hb_ser : ∀ i y, b i y = ∑' n : ℕ,
      (starRingEnd ℂ (c_g i n) * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))) *
        Complex.exp (-((2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ) : ℝ) : ℂ) * y))
    (Rtilde : MvPolynomial (Fin s × Fin (r + 1)) convergentSubring) (hRtilde_ne : Rtilde ≠ 0)
    (hRtilde_ann : MvPolynomial.aeval
      (fun p : Fin s × Fin (r + 1) ↦
        PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n))
      (MvPolynomial.map convergentSubring.subtype Rtilde) = 0) :
    False := by
  classical
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
  -- Step 1: Minimal-degree descent into `ℂ{x}[Z]`!
  let Yhat : Fin s × Fin (r + 1) → PowerSeries ℂ := fun p ↦
    PowerSeries.mk (fun n ↦ (-1 : ℂ) ^ (n + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val n)
  obtain ⟨R, hR_ne, hR_deg, hR_ann, hR_min⟩ := minimal_degree_descent Yhat Rtilde hRtilde_ne hRtilde_ann
  -- Step 2: Proposition 5.3 kills EVERY parity-split directional derivative!
  have hvan_all := mockModular_translation_invariance_induction hM hL k hk c_g hC₀ ha hc_bd
    b C_b c_b hb hb_ser R hR_ne hR_deg hR_ann hR_min
  -- Step 3: Pick a nonzero partial derivative `p₀` and a monomial `α` appearing in `pderiv p₀ R`!
  have hex_pd : ∃ p₀ : Fin s × Fin (r + 1), MvPolynomial.pderiv p₀ R ≠ 0 := by
    by_contra hall; push Not at hall
    have hR_const : R = MvPolynomial.C (R.coeff 0) := by
      apply MvPolynomial.ext; intro (m : (Fin s × Fin (r + 1)) →₀ ℕ)
      rw [MvPolynomial.coeff_C]
      by_cases hm : m = 0
      · subst hm; simp
      · simp only [Ne.symm hm, ↓reduceIte]
        obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
          by_contra h0; push Not at h0; exact hm (Finsupp.ext h0)
        let m' : (Fin s × Fin (r + 1)) →₀ ℕ := m - Finsupp.single j 1
        have h0 := congrArg (fun f : MvPolynomial _ convergentSubring ↦ f.coeff m') (hall j)
        simp only [MvPolynomial.coeff_pderiv, m', Finsupp.sub_add_single_one_cancel hj, AddMonoidAlgebra.coeff_zero] at h0
        have hnat : ((m' j : convergentSubring) + 1) ≠ 0 := by
          intro h; have := congrArg (fun x : convergentSubring ↦ x.val.coeff 0) h
          simp at this; exact Nat.cast_add_one_ne_zero _ this
        exact (mul_eq_zero.mp h0).resolve_right hnat
    rw [hR_const, MvPolynomial.totalDegree_C] at hR_deg
    exact lt_irrefl 0 hR_deg
  obtain ⟨p₀, hp₀_ne⟩ := hex_pd
  obtain ⟨α, hα_mem⟩ := MvPolynomial.support_nonempty.mpr hp₀_ne
  let A : Fin s × Fin (r + 1) → PowerSeries ℂ := fun p ↦ ((MvPolynomial.pderiv p R).coeff α).val
  have hAp₀_ne : A p₀ ≠ 0 := fun h0 ↦
    MvPolynomial.mem_support_iff.mp hα_mem (Subtype.ext h0)
  -- Pick the parity block `par := nonBolIsHalf (k p₀.1)` containing `p₀`!
  let par : Bool := nonBolIsHalf (k p₀.1)
  let I_idx : Finset (Fin s × Fin (r + 1)) :=
    Finset.univ.filter fun p ↦ nonBolIsHalf (k p.1) = par ∧ A p ≠ 0
  have hI_non : I_idx.Nonempty := ⟨p₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hAp₀_ne⟩⟩
  -- For each `p ∈ I_idx`, let `v p := Nat.find (∃ d, (A p).coeff d ≠ 0)` be its exact `x`-valuation!
  have hex_val : ∀ p ∈ I_idx, ∃ d : ℕ, (A p).coeff d ≠ 0 := fun p hp ↦ by
    by_contra hall; push Not at hall
    exact (Finset.mem_filter.mp hp).2.2 (PowerSeries.ext fun d ↦ by simp [hall d])
  let valA : Fin s × Fin (r + 1) → ℕ := fun p ↦
    if h : p ∈ I_idx then Nat.find (hex_val p h) else 0
  have hvalA_ne : ∀ p ∈ I_idx, (A p).coeff (valA p) ≠ 0 := fun p hp ↦ by
    simp only [valA, hp, ↓reduceDIte]; exact Nat.find_spec (hex_val p hp)
  have hvalA_min : ∀ p ∈ I_idx, ∀ d < valA p, (A p).coeff d = 0 := fun p hp d hd ↦ by
    simp only [valA, hp, ↓reduceDIte] at hd
    by_contra hne; exact Nat.find_min (hex_val p hp) hd hne
  let ν : Fin s × Fin (r + 1) → ℕ := fun p ↦ nonBolShift (k p.1) + 2 * (r - p.2.val) + valA p
  let ν_min : ℕ := I_idx.inf' hI_non ν
  let S_min : Finset (Fin s × Fin (r + 1)) := I_idx.filter fun p ↦ ν p = ν_min
  have hSmin_non : S_min.Nonempty := by
    obtain ⟨p₁, hp₁, hmin⟩ := Finset.exists_mem_eq_inf' hI_non ν
    exact ⟨p₁, Finset.mem_filter.mpr ⟨hp₁, hmin.symm⟩⟩
  -- Extract `[Z^α]` and `[x^{ν_min}]` from `dirDeriv (mockModeW par ... n) R = 0` for EVERY `n : ℕ`!
  have hcoeff_rel : ∀ n : ℕ,
      let ω_n : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ)
      ∑ p ∈ S_min,
        (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * (A p).coeff (valA p)) *
          starRingEnd ℂ (c_g p.1 n) * (ω_n : ℂ) ^ (k p.1 - 1) * (ω_n : ℂ) ^ p.2.val = 0 := by
    intro n
    dsimp only
    let ω_n : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ)
    let phase : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))
    have hvan_n : dirDeriv (fun p ↦ convPolyEmb (mockModeW par M L k c_g n p)) R = 0 := by
      cases hpar : par
      · exact (hvan_all n).1
      · exact (hvan_all n).2
    have hZα := congrArg (fun F : MvPolynomial _ convergentSubring ↦ (F.coeff α).val.coeff ν_min) hvan_n
    simp only [dirDeriv, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, AddMonoidAlgebra.coeff_zero] at hZα
    rw [show (∑ x : Fin s × Fin (r + 1), convPolyEmb (mockModeW par M L k c_g n x) *
          (MvPolynomial.pderiv x R).coeff α).val =
        convergentSubring.subtype (∑ x : Fin s × Fin (r + 1),
          convPolyEmb (mockModeW par M L k c_g n x) * (MvPolynomial.pderiv x R).coeff α) from rfl,
        map_sum, map_sum] at hZα
    -- Compute the `ν_min`-th `x`-coefficient of each term `p`!
    have hterm_eq : ∀ p : Fin s × Fin (r + 1),
        ((convPolyEmb (mockModeW par M L k c_g n p) * (MvPolynomial.pderiv p R).coeff α).val).coeff ν_min =
        if p ∈ S_min then
          phase * ((-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * (A p).coeff (valA p)) *
            starRingEnd ℂ (c_g p.1 n) * (ω_n : ℂ) ^ (k p.1 - 1) * (ω_n : ℂ) ^ p.2.val)
        else 0 := by
      intro p
      by_cases hpI : p ∈ I_idx
      · have hpar_p : nonBolIsHalf (k p.1) = par := (Finset.mem_filter.mp hpI).2.1
        have hν_le : ν_min ≤ ν p := Finset.inf'_le ν hpI
        let c_pref : ℂ := -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) *
          starRingEnd ℂ (c_g p.1 n) * phase * (ω_n : ℂ) ^ (k p.1 - 1)
        have hW_p : ((convPolyEmb (mockModeW par M L k c_g n p) * (MvPolynomial.pderiv p R).coeff α).val) =
            PowerSeries.C c_pref * (PowerSeries.X ^ nonBolShift (k p.1) * ((mockJetP (k p.1) r p.2.val (ω_n : ℂ) : PowerSeries ℂ) * A p)) := by
          change ((mockModeW par M L k c_g n p : PowerSeries ℂ)) * A p = _
          dsimp [mockModeW]; simp only [hpar_p, ↓reduceIte]
          simp [c_pref, ω_n, phase, mul_assoc]
        rw [hW_p, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
        by_cases hS : p ∈ S_min
        · have hν_eq : ν p = ν_min := (Finset.mem_filter.mp hS).2
          have hsh_le : nonBolShift (k p.1) ≤ ν_min := by dsimp [ν] at hν_eq; omega
          simp only [hS, hsh_le, ↓reduceIte]
          rw [PowerSeries.coeff_mul]
          -- Only `(2 * (r - p.2.val), valA p)` contributes in the antidiagonal!
          have hpair_mem : (2 * (r - p.2.val), valA p) ∈ Finset.antidiagonal (ν_min - nonBolShift (k p.1)) := by
            rw [Finset.mem_antidiagonal]; dsimp [ν] at hν_eq; omega
          rw [Finset.sum_eq_single (2 * (r - p.2.val), valA p)]
          · simp only [Polynomial.coeff_coe, mockJetP_coeff_le, lt_irrefl, ↓reduceIte]
            dsimp [c_pref]; ring
          · intro x hx hne
            have hsum_x : x.1 + x.2 = ν_min - nonBolShift (k p.1) := Finset.mem_antidiagonal.mp hx
            by_cases h1 : x.1 < 2 * (r - p.2.val)
            · simp only [Polynomial.coeff_coe, mockJetP_coeff_le, h1, ↓reduceIte, zero_mul]
            · have h2 : x.2 < valA p := by
                have : x.1 ≠ 2 * (r - p.2.val) ∨ x.2 ≠ valA p := by
                  by_contra h; push Not at h; exact hne (Prod.ext h.1 h.2)
                dsimp [ν] at hν_eq; omega
              rw [hvalA_min p hpI x.2 h2, mul_zero]
          · intro hnot; exact absurd hpair_mem hnot
        · have hν_gt : ν_min < ν p := lt_of_le_of_ne hν_le (fun h ↦ hS (Finset.mem_filter.mpr ⟨hpI, h.symm⟩))
          simp only [hS, ↓reduceIte]
          split_ifs with hsh
          · rw [PowerSeries.coeff_mul]
            suffices ∑ x ∈ Finset.antidiagonal (ν_min - nonBolShift (k p.1)),
                (mockJetP (k p.1) r p.2.val (ω_n : ℂ)).coeff x.1 * (A p).coeff x.2 = 0 by
              simpa [Polynomial.coeff_coe] using congrArg (c_pref * ·) this
            apply Finset.sum_eq_zero; intro x hx
            have hsum_x := Finset.mem_antidiagonal.mp hx
            by_cases h1 : x.1 < 2 * (r - p.2.val)
            · simp only [mockJetP_coeff_le, h1, ↓reduceIte, zero_mul]
            · have h2 : x.2 < valA p := by dsimp [ν] at hν_gt; omega
              rw [hvalA_min p hpI x.2 h2, mul_zero]
          · rw [mul_zero]
      · have hnotS : p ∉ S_min := fun h ↦ hpI (Finset.mem_filter.mp h).1
        simp only [hnotS, ↓reduceIte]
        by_cases hpar_p : nonBolIsHalf (k p.1) = par
        · have hAp0 : A p = 0 := by
            by_contra hne; exact hpI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpar_p, hne⟩)
          have : (MvPolynomial.pderiv p R).coeff α = 0 := Subtype.ext hAp0
          rw [this, mul_zero]; simp
        · have hW0 : mockModeW par M L k c_g n p = 0 := by dsimp [mockModeW]; simp [hpar_p]
          rw [hW0, map_zero, zero_mul, ZeroMemClass.coe_zero, map_zero]
    have hsum_eq : ∑ p : Fin s × Fin (r + 1),
        ((convPolyEmb (mockModeW par M L k c_g n p) * (MvPolynomial.pderiv p R).coeff α).val).coeff ν_min = 0 := hZα
    simp_rw [hterm_eq] at hsum_eq
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum] at hsum_eq
    exact (mul_eq_zero.mp hsum_eq).resolve_left (Complex.exp_ne_zero _)
  -- Step 4: Multiply by `ω_n^{1 - k_min}` and conjugate to build a NONZERO polynomial vector `Q : Fin s → Polynomial ℂ`
  -- satisfying `∑_i c_g i n * Q_i((n + 1) / L) = 0` for ALL `n : ℕ`!
  let I_forms : Finset (Fin s) := S_min.image Prod.fst
  have hIf_non : I_forms.Nonempty := hSmin_non.image Prod.fst
  -- Every `i ∈ I_forms` has the same parity `par`, so `k i` differs from `k_min` by a natural number `d_i`!
  let k_re_floor : Fin s → ℤ := fun i ↦ Int.floor (k i).re
  let m_min : ℤ := I_forms.inf' hIf_non k_re_floor
  have hk_diff_nat : ∀ i ∈ I_forms, ∃ d : ℕ, k i - (m_min : ℂ) - (if par then (1 / 2 : ℂ) else 0) = (d : ℂ) := by
    intro i hi
    obtain ⟨p, hpS, hpi⟩ := Finset.mem_image.mp hi
    have hpar_i : nonBolIsHalf (k i) = par := by rw [← hpi]; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hpS).1).2.1
    have hle : m_min ≤ k_re_floor i := Finset.inf'_le k_re_floor hi
    rcases hk i with hk1 | ⟨m, hkm, _⟩
    · have hpar_f : par = false := by rw [← hpar_i, hk1]; simp [nonBolIsHalf]
      have hfl : k_re_floor i = 1 := by dsimp [k_re_floor]; rw [hk1]; simp
      refine ⟨(1 - m_min).toNat, ?_⟩
      simp only [hpar_f, Bool.false_eq_true, ↓reduceIte, hk1, sub_zero]
      have : (((1 - m_min).toNat : ℕ) : ℤ) = 1 - m_min := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this.symm
    · have hne1 : (m : ℂ) + 1 / 2 ≠ 1 := by
        intro h0; have hre := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.intCast_re, Complex.div_ofNat_re, Complex.one_re] at hre
        have h2m : 2 * m = 1 := by exact_mod_cast (by linarith : (2 * m : ℝ) = 1)
        omega
      have hpar_t : par = true := by
        rw [← hpar_i, hkm]; unfold nonBolIsHalf; simp only [ne_eq, hne1, not_false_eq_true, decide_true]
      have hfl : k_re_floor i = m := by
        dsimp [k_re_floor]; rw [hkm]
        have hre : ((m : ℂ) + 1 / 2).re = (m : ℝ) + 1 / 2 := by simp
        rw [hre, Int.floor_eq_iff]; constructor <;> linarith
      refine ⟨(m - m_min).toNat, ?_⟩
      simp only [hpar_t, ↓reduceIte, hkm]
      have : (((m - m_min).toNat : ℕ) : ℤ) = m - m_min := Int.toNat_of_nonneg (by omega)
      have hC : (((m - m_min).toNat : ℕ) : ℂ) = (m : ℂ) - (m_min : ℂ) := by exact_mod_cast this
      rw [hC]; ring
  let k_min : ℂ := (m_min : ℂ) + (if par then (1 / 2 : ℂ) else 0)
  let shiftK : Fin s → ℕ := fun i ↦ if h : i ∈ I_forms then Classical.choose (hk_diff_nat i h) else 0
  have hshiftK_eq : ∀ i ∈ I_forms, k i - k_min = (shiftK i : ℂ) := fun i hi ↦ by
    simp only [shiftK, hi, ↓reduceDIte, k_min]
    have h := Classical.choose_spec (hk_diff_nat i hi)
    linear_combination h
  let Q : Fin s → Polynomial ℂ := fun i ↦
    ∑ p ∈ S_min.filter (fun p ↦ p.1 = i),
      Polynomial.C (starRingEnd ℂ (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k i)) * (A p).coeff (valA p)) *
        ((2 * (Real.pi : ℂ)) ^ (shiftK i + p.2.val))) * Polynomial.X ^ (shiftK i + p.2.val)
  -- At least one `Q i ≠ 0`!
  have hQ_nonzero : ∃ i : Fin s, Q i ≠ 0 := by
    obtain ⟨p₁, hp₁S⟩ := hSmin_non
    refine ⟨p₁.1, fun h0 ↦ ?_⟩
    have hc := congrArg (fun P : Polynomial ℂ ↦ P.coeff (shiftK p₁.1 + p₁.2.val)) h0
    rw [Polynomial.coeff_zero] at hc
    dsimp [Q] at hc
    change (Polynomial.lcoeff ℂ (shiftK p₁.1 + p₁.2.val)) _ = 0 at hc
    rw [map_sum] at hc
    have hp₁_filt : p₁ ∈ S_min.filter (fun p ↦ p.1 = p₁.1) := Finset.mem_filter.mpr ⟨hp₁S, rfl⟩
    rw [Finset.sum_eq_single p₁] at hc
    · rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one] at hc
      have h1 : starRingEnd ℂ (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p₁.1)) * (A p₁).coeff (valA p₁)) ≠ 0 := by
        intro h; have h' := congrArg (starRingEnd ℂ) h; simp only [Complex.conj_conj, map_zero] at h'
        have hG : -(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p₁.1)) ≠ 0 := by
          rw [neg_ne_zero, div_eq_mul_inv]
          exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
            Complex.I_ne_zero) (nonBolWeight_inv_Gamma_ne_zero (hk p₁.1))
        exact mul_ne_zero hG (hvalA_ne p₁ (Finset.mem_filter.mp hp₁S).1) h'
      have h2 : (2 * (Real.pi : ℂ)) ^ (shiftK p₁.1 + p₁.2.val) ≠ 0 :=
        pow_ne_zero _ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
      exact mul_ne_zero h1 h2 hc
    · intro p hp hne
      have hp1 : p.1 = p₁.1 := (Finset.mem_filter.mp hp).2
      have hp2 : p.2.val ≠ p₁.2.val := fun h ↦ hne (Prod.ext hp1 (Fin.ext h))
      have hne_deg : shiftK p₁.1 + p₁.2.val ≠ shiftK p₁.1 + p.2.val := by omega
      simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        hne_deg, ↓reduceIte, mul_zero]
    · intro hnot; exact absurd hp₁_filt hnot
  -- Verify `∑ i : Fin s, c_g i n * (Q i).eval (((n + 1 : ℕ) : ℂ) / (L : ℂ)) = 0` for EVERY `n : ℕ`!
  have hQ_coeff_rel : ∀ n : ℕ,
      ∑ i : Fin s, c_g i n * (Q i).eval (((n + 1 : ℕ) : ℂ) / (L : ℂ)) = 0 := by
    intro n
    let ω_n : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ)
    have hω_pos : 0 < ω_n := by dsimp [ω_n]; positivity
    have hωC_ne : (ω_n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω_pos.ne'
    have h1 := congrArg (fun z : ℂ ↦ starRingEnd ℂ ((ω_n : ℂ) ^ (1 - k_min) * z)) (hcoeff_rel n)
    rw [mul_zero, map_zero, Finset.mul_sum, map_sum] at h1
    rw [← h1]
    -- Group `S_min` by `p.1 : Fin s`!
    have hgroup : (∑ i : Fin s, c_g i n * (Q i).eval (((n + 1 : ℕ) : ℂ) / (L : ℂ))) =
        ∑ i : Fin s, ∑ p ∈ S_min.filter (fun p ↦ p.1 = i),
          starRingEnd ℂ ((ω_n : ℂ) ^ (1 - k_min) *
            ((-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * (A p).coeff (valA p)) *
              starRingEnd ℂ (c_g p.1 n) * (ω_n : ℂ) ^ (k p.1 - 1) * (ω_n : ℂ) ^ p.2.val)) := by
      apply Finset.sum_congr rfl; intro i _
      dsimp [Q]
      change c_g i n * (Polynomial.evalRingHom (((n + 1 : ℕ) : ℂ) / (L : ℂ))) _ = _
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p hp
      have hpi : p.1 = i := (Finset.mem_filter.mp hp).2
      have hpS : p ∈ S_min := (Finset.mem_filter.mp hp).1
      have hi_mem : i ∈ I_forms := Finset.mem_image.mpr ⟨p, hpS, hpi⟩
      subst hpi
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hpow_combine : (ω_n : ℂ) ^ (1 - k_min) * (ω_n : ℂ) ^ (k p.1 - 1) * (ω_n : ℂ) ^ p.2.val =
          ((ω_n ^ (shiftK p.1 + p.2.val) : ℝ) : ℂ) := by
        rw [← Complex.cpow_add _ _ hωC_ne, show (1 - k_min) + (k p.1 - 1) = k p.1 - k_min by ring,
            hshiftK_eq p.1 hi_mem, Complex.cpow_natCast, ← pow_add]; push_cast; rfl
      have hω_fac : (2 * (Real.pi : ℂ)) ^ (shiftK p.1 + p.2.val) *
          (((n + 1 : ℕ) : ℂ) / (L : ℂ)) ^ (shiftK p.1 + p.2.val) = ((ω_n ^ (shiftK p.1 + p.2.val) : ℝ) : ℂ) := by
        rw [← mul_pow]; dsimp [ω_n]; push_cast; congr 1; ring
      have hconj : starRingEnd ℂ ((ω_n : ℂ) ^ (1 - k_min) *
            ((-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * (A p).coeff (valA p)) *
              starRingEnd ℂ (c_g p.1 n) * (ω_n : ℂ) ^ (k p.1 - 1) * (ω_n : ℂ) ^ p.2.val)) =
          c_g p.1 n *
            starRingEnd ℂ (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * (A p).coeff (valA p)) *
            ((ω_n ^ (shiftK p.1 + p.2.val) : ℝ) : ℂ) := by
        have hreord : (ω_n : ℂ) ^ (1 - k_min) *
            ((-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * (A p).coeff (valA p)) *
              starRingEnd ℂ (c_g p.1 n) * (ω_n : ℂ) ^ (k p.1 - 1) * (ω_n : ℂ) ^ p.2.val) =
            starRingEnd ℂ (c_g p.1 n) *
              (-(2 * (Real.pi : ℂ) * Complex.I / Complex.Gamma (k p.1)) * (A p).coeff (valA p)) *
              ((ω_n : ℂ) ^ (1 - k_min) * (ω_n : ℂ) ^ (k p.1 - 1) * (ω_n : ℂ) ^ p.2.val) := by ring
        rw [hreord, hpow_combine, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      rw [hconj, ← hω_fac]; ring
    rw [hgroup]
    rw [Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (fun _ _ ↦ Finset.mem_univ _)]
  -- Step 5: Compute `iteratedDeriv j (g_i - c₀ i) τ` termwise on `{τ : ℂ | 1 < τ.im}` (`⊆ ℍ`),
  -- deduce `∑_i Q_i(θ_q) g_{i,cusp} = 0` on `{1 < τ.im}`, extend to ALL of `ℍ` by the Identity Theorem,
  -- and contradict `positiveWeight_modular_thetaQ_diff_indep`!
  let U_hi : Set ℂ := {τ : ℂ | 1 < τ.im}
  have hUhi_open : IsOpen U_hi := isOpen_lt continuous_const Complex.continuous_im
  have hUhi_sub : U_hi ⊆ upperHalfPlane := fun τ hτ ↦ show 0 < τ.im from lt_trans zero_lt_one hτ
  have hUhi_conv : Convex ℝ U_hi := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    have h1 : 1 < z₁.im := hz₁
    have h2 : 1 < z₂.im := hz₂
    change 1 < (a • z₁ + b • z₂).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      rw [hb1, zero_mul, zero_add, one_mul]; exact h2
    · nlinarith
  have hUHP_conv : Convex ℝ upperHalfPlane := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    have h1 : 0 < z₁.im := hz₁
    have h2 : 0 < z₂.im := hz₂
    change 0 < (a • z₁ + b • z₂).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      rw [hb1, zero_mul, zero_add, one_mul]; exact h2
    · nlinarith
  let δ_freq : ℝ := 2 * Real.pi / (L : ℝ)
  have hδ_pos : 0 < δ_freq := div_pos (mul_pos two_pos Real.pi_pos) hL_pos
  have h1a : 0 < 1 - a := sub_pos.mpr ha
  let α_n : ℕ → ℂ := fun n ↦ 2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / (L : ℂ)
  have hterm_bd : ∀ (i : Fin s) (m : ℕ),
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ z ∈ U_hi,
        ‖c_g i n * (α_n n) ^ m * Complex.exp (α_n n * z)‖ ≤ u n := by
    intro i m
    have hr_lt1 : Real.exp (-(1 - a) * δ_freq) < 1 :=
      Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr h1a) hδ_pos)
    have hsum_dom := (summable_poly_mul_geom (c := 1) zero_le_one (Real.exp_pos _).le hr_lt1 m).mul_left
      (C₀ * δ_freq ^ m * Real.exp (-(1 - a) * δ_freq))
    refine ⟨_, hsum_dom, fun n z hz ↦ ?_⟩
    let ω_n : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ)
    have hω_eq : ω_n = δ_freq * ((n + 1 : ℕ) : ℝ) := by dsimp [ω_n, δ_freq]; ring
    have hα_norm : ‖α_n n‖ = ω_n := by
      dsimp [α_n, ω_n]
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_natCast,
          Complex.norm_natCast]
    have hexp_re : (α_n n * z).re = -ω_n * z.im := by
      have hα_eq : α_n n = ((ω_n : ℝ) : ℂ) * Complex.I := by dsimp [α_n, ω_n]; push_cast; ring
      rw [hα_eq, Complex.mul_re, Complex.mul_re, Complex.mul_im]
      simp
    have hexp_comb : Real.exp (a * ω_n) * Real.exp (-ω_n * z.im) ≤
        Real.exp (-(1 - a) * δ_freq) * (Real.exp (-(1 - a) * δ_freq)) ^ n := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hz1 : 1 < z.im := hz
      have hω_pos : 0 < ω_n := by dsimp [ω_n]; positivity
      have h1 : a * ω_n + -ω_n * z.im ≤ -(1 - a) * ω_n := by nlinarith
      have h2 : -(1 - a) * ω_n = -(1 - a) * δ_freq + (n : ℝ) * (-(1 - a) * δ_freq) := by
        rw [hω_eq]; push_cast; ring
      linarith
    rw [norm_mul, norm_mul, norm_pow, hα_norm, Complex.norm_exp, hexp_re]
    calc ‖c_g i n‖ * ω_n ^ m * Real.exp (-ω_n * z.im)
        ≤ (C₀ * Real.exp (a * ω_n)) * ω_n ^ m * Real.exp (-ω_n * z.im) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc_bd i n) (by positivity)) (Real.exp_pos _).le
      _ = C₀ * ω_n ^ m * (Real.exp (a * ω_n) * Real.exp (-ω_n * z.im)) := by ring
      _ ≤ C₀ * ω_n ^ m * (Real.exp (-(1 - a) * δ_freq) * (Real.exp (-(1 - a) * δ_freq)) ^ n) :=
          mul_le_mul_of_nonneg_left hexp_comb (by positivity)
      _ = C₀ * δ_freq ^ m * Real.exp (-(1 - a) * δ_freq) *
            (((n : ℝ) + 1) ^ m * (Real.exp (-(1 - a) * δ_freq)) ^ n) := by
          rw [hω_eq, mul_pow]; push_cast; ring
  have hiter_series : ∀ (i : Fin s) (m : ℕ), ∀ τ ∈ U_hi,
      iteratedDeriv m (fun z ↦ g i z - c₀ i) τ =
      ∑' n : ℕ, c_g i n * (α_n n) ^ m * Complex.exp (α_n n * τ) := by
    intro i m
    induction m with
    | zero =>
      intro τ hτ
      rw [iteratedDeriv_zero, hg_fourier i τ (hUhi_sub hτ)]
      apply tsum_congr; intro n; dsimp [α_n]; rw [pow_zero, mul_one]
      congr 1; congr 1; ring
    | succ m ih =>
      intro τ hτ
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv m (fun z ↦ g i z - c₀ i) =ᶠ[𝓝 τ]
          fun z ↦ ∑' n : ℕ, c_g i n * (α_n n) ^ m * Complex.exp (α_n n * z) := by
        filter_upwards [hUhi_open.mem_nhds hτ] with z hz; exact ih z hz
      rw [hev.deriv_eq]
      obtain ⟨u_m, hum_sum, hbd_m⟩ := hterm_bd i m
      obtain ⟨u_s, hus_sum, hbd_s⟩ := hterm_bd i (m + 1)
      have hderiv_n : ∀ n : ℕ, ∀ z ∈ U_hi,
          HasDerivAt (fun w ↦ c_g i n * (α_n n) ^ m * Complex.exp (α_n n * w))
            (c_g i n * (α_n n) ^ (m + 1) * Complex.exp (α_n n * z)) z := fun n z _ ↦ by
        have h1 : HasDerivAt (fun w : ℂ ↦ Complex.exp (α_n n * w)) (Complex.exp (α_n n * z) * α_n n) z := by
          simpa using ((hasDerivAt_id z).const_mul (α_n n)).cexp
        have h2 := h1.const_mul (c_g i n * (α_n n) ^ m)
        convert h2 using 1; rw [pow_succ]; ring
      have hsum_τ : Summable (fun n : ℕ ↦ c_g i n * (α_n n) ^ m * Complex.exp (α_n n * τ)) :=
        Summable.of_norm_bounded hum_sum (fun n ↦ hbd_m n τ hτ)
      exact (hasDerivAt_tsum_of_isPreconnected hus_sum hUhi_open hUhi_conv.isPreconnected
        hderiv_n hbd_s hτ hsum_τ hτ).deriv
  -- Evaluate the linear differential combination `F(τ) = ∑ i, Q_i(θ_q) g_{i,cusp}(τ)`!
  let F_rel : ℂ → ℂ := fun τ ↦
    ∑ i : Fin s, ∑ j ∈ Finset.range ((Q i).natDegree + 1),
      (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
        iteratedDeriv j (fun z ↦ g i z - c₀ i) τ
  have hF_zero_Uhi : ∀ τ ∈ U_hi, F_rel τ = 0 := by
    intro τ hτ
    dsimp [F_rel]
    have h2piI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
    have hα_div : ∀ n : ℕ, (1 / (2 * (Real.pi : ℂ) * Complex.I)) * α_n n = ((n + 1 : ℕ) : ℂ) / (L : ℂ) := fun n ↦ by
      dsimp [α_n]; field_simp [h2piI]
    have hterm_i : ∀ i : Fin s,
        ∑ j ∈ Finset.range ((Q i).natDegree + 1),
          (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
            iteratedDeriv j (fun z ↦ g i z - c₀ i) τ =
        ∑' n : ℕ, c_g i n * (Q i).eval (((n + 1 : ℕ) : ℂ) / (L : ℂ)) * Complex.exp (α_n n * τ) := by
      intro i
      have hsum_j : ∀ j ∈ Finset.range ((Q i).natDegree + 1),
          Summable (fun n : ℕ ↦ (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
            (c_g i n * (α_n n) ^ j * Complex.exp (α_n n * τ))) := fun j _ ↦ by
        obtain ⟨u_j, huj_sum, hbd_j⟩ := hterm_bd i j
        exact (Summable.of_norm_bounded huj_sum (fun n ↦ hbd_j n τ hτ)).mul_left _
      have hlhs : ∑ j ∈ Finset.range ((Q i).natDegree + 1),
            (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
              iteratedDeriv j (fun z ↦ g i z - c₀ i) τ =
          ∑ j ∈ Finset.range ((Q i).natDegree + 1), ∑' n : ℕ,
            (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
              (c_g i n * (α_n n) ^ j * Complex.exp (α_n n * τ)) := by
        apply Finset.sum_congr rfl; intro j _
        rw [hiter_series i j τ hτ, ← tsum_mul_left]
      rw [hlhs, ← Summable.tsum_finsetSum hsum_j]
      apply tsum_congr; intro n
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self (Q i).natDegree), Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      have hp : (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j * (α_n n) ^ j = (((n + 1 : ℕ) : ℂ) / (L : ℂ)) ^ j := by
        rw [← mul_pow, hα_div n]
      linear_combination (Q i).coeff j * c_g i n * Complex.exp (α_n n * τ) * hp
    have hsum_i : ∀ i : Fin s,
        Summable (fun n : ℕ ↦ c_g i n * (Q i).eval (((n + 1 : ℕ) : ℂ) / (L : ℂ)) * Complex.exp (α_n n * τ)) := by
      intro i
      have hsum_j : ∀ j ∈ Finset.range ((Q i).natDegree + 1),
          Summable (fun n : ℕ ↦ (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
            (c_g i n * (α_n n) ^ j * Complex.exp (α_n n * τ))) := fun j _ ↦ by
        obtain ⟨u_j, huj_sum, hbd_j⟩ := hterm_bd i j
        exact (Summable.of_norm_bounded huj_sum (fun n ↦ hbd_j n τ hτ)).mul_left _
      have heq : (fun n : ℕ ↦ c_g i n * (Q i).eval (((n + 1 : ℕ) : ℂ) / (L : ℂ)) * Complex.exp (α_n n * τ)) =
          fun n ↦ ∑ j ∈ Finset.range ((Q i).natDegree + 1),
            (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
              (c_g i n * (α_n n) ^ j * Complex.exp (α_n n * τ)) := by
        ext n
        rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self (Q i).natDegree), Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        have hp : (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j * (α_n n) ^ j = (((n + 1 : ℕ) : ℂ) / (L : ℂ)) ^ j := by
          rw [← mul_pow, hα_div n]
        linear_combination -(Q i).coeff j * c_g i n * Complex.exp (α_n n * τ) * hp
      rw [heq]; exact summable_sum hsum_j
    rw [Finset.sum_congr rfl (fun i _ ↦ hterm_i i), ← Summable.tsum_finsetSum (fun i _ ↦ hsum_i i)]
    have hzero_n : ∀ n : ℕ, ∑ i : Fin s, c_g i n * (Q i).eval (((n + 1 : ℕ) : ℂ) / (L : ℂ)) *
        Complex.exp (α_n n * τ) = 0 := fun n ↦ by
      rw [← Finset.sum_mul, hQ_coeff_rel n, zero_mul]
    simp_rw [hzero_n]
    exact tsum_zero
  -- Extend `F_rel τ = 0` from `U_hi` to ALL of `upperHalfPlane` by the Identity Theorem!
  have hF_diff : DifferentiableOn ℂ F_rel upperHalfPlane := by
    refine DifferentiableOn.fun_sum fun i _ ↦ DifferentiableOn.fun_sum fun j _ ↦ ?_
    have hdiff_sub : DifferentiableOn ℂ (fun z ↦ g i z - c₀ i) upperHalfPlane :=
      (hg_diff i).sub (differentiableOn_const _)
    have hdiff_iter : ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m (fun z ↦ g i z - c₀ i)) upperHalfPlane := by
      intro m
      induction m with
      | zero => simpa [iteratedDeriv_zero] using hdiff_sub
      | succ m ih => simpa [iteratedDeriv_succ] using ih.deriv isOpen_upperHalfPlane
    exact (hdiff_iter j).const_mul _
  have hF_an : AnalyticOnNhd ℂ F_rel upperHalfPlane := hF_diff.analyticOnNhd isOpen_upperHalfPlane
  have h2I_mem : (2 * Complex.I : ℂ) ∈ upperHalfPlane := by simp [upperHalfPlane]
  have hfreq : ∃ᶠ τ in 𝓝[≠] (2 * Complex.I : ℂ), F_rel τ = 0 := by
    have h2I_Uhi : (2 * Complex.I : ℂ) ∈ U_hi := by simp [U_hi]
    have hev : ∀ᶠ τ in 𝓝 (2 * Complex.I : ℂ), F_rel τ = 0 :=
      Filter.eventually_of_mem (hUhi_open.mem_nhds h2I_Uhi) hF_zero_Uhi
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  have hF_zero_UHP : ∀ τ ∈ upperHalfPlane, F_rel τ = 0 :=
    hF_an.eqOn_zero_of_preconnected_of_frequently_eq_zero hUHP_conv.isPreconnected h2I_mem hfreq
  -- Step 6: Contradict `positiveWeight_modular_thetaQ_diff_indep` from `MockModularAlgebraCore`!
  have hQ_all_zero := positiveWeight_modular_thetaQ_diff_indep w_twice hw_pos g hg_diff hM hL
    hg_mod hg_per hg_lin c₀ Q hF_zero_UHP
  obtain ⟨i₀, hi₀_ne⟩ := hQ_nonzero
  exact hi₀_ne (hQ_all_zero i₀)

/-- **Complete End-to-End Paper #10 Master Theorem (`q₁`-Expansion → Top-Degree Survival → Stokes Contradiction)**:
Wires **ALL FOUR STAGES** of Paper #10's unconditional proof into a single master theorem:
1. Uniform Cauchy `q₁`-tail bound (`Lemma 4.1`) + Logarithmic/Puiseux scale separation + Watson uniqueness
   (`q1_induction_kill`) kills the `m = 0, ε = 0, a = 0` formal series `f_hat 0 0 0 ≡ 0`;
2. Exact top-degree survival (`top_degree_survival`) guarantees the resulting convergent relation
   `Q_{0,0,0} ∈ ℂ{x}[Z]` is NONZERO with `P.totalDegree ≤ Q_{0,0,0}.totalDegree`;
3. Minimal-total-degree descent + Rotated-ray simultaneous lateral annihilation (`Lemma 5.1`) +
   Exact Hankel keyhole jump (`Lemma 5.2`) + Collision-free translation-invariance induction (`Prop. 5.3`) +
   Positive-weight modular form differential independence (`positiveWeight_modular_thetaQ_diff_indep`)
   derive **`False`**! -/
theorem mockModular_joint_diff_indep_of_q1Expansion {s r M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (k : Fin s → ℂ) (hk : ∀ i, NonBolWeight (k i))
    (w_twice : Fin s → ℕ) (hw_pos : ∀ i, 1 ≤ w_twice i)
    (hw_eq : ∀ i, (w_twice i : ℂ) / 2 = 2 - k i)
    (g : Fin s → ℂ → ℂ) (hg_diff : ∀ i, DifferentiableOn ℂ (g i) upperHalfPlane)
    (hg_mod : ∀ i n, 1 ≤ n → ∀ τ ∈ upperHalfPlane,
      g i (τ / (((n * M : ℕ) : ℂ) * τ + 1)) =
        ((((n * M : ℕ) : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ (w_twice i) * g i τ)
    (hg_per : ∀ i (n : ℤ), ∀ τ ∈ upperHalfPlane,
      g i (τ + ((n * (L : ℤ) : ℤ) : ℂ)) = g i τ)
    (hg_lin : ∀ c : Fin s → ℂ, (∀ τ ∈ upperHalfPlane, ∑ i : Fin s, c i * g i τ = 0) → c = 0)
    (c₀ : Fin s → ℂ) (c_g : Fin s → ℕ → ℂ) {C₀ a : ℝ} (hC₀ : 0 ≤ C₀) (ha : a < 1)
    (hc_bd : ∀ i n, ‖c_g i n‖ ≤ C₀ * Real.exp (a * (2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ))))
    (hg_fourier : ∀ i, ∀ τ ∈ upperHalfPlane,
      g i τ - c₀ i = ∑' n : ℕ, c_g i n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) * τ / (L : ℂ)))
    (b : Fin s → ℂ → ℂ) (C_b c_b : Fin s → ℝ)
    (hb : ∀ i, ExpDecayKernel (b i) (C_b i) (c_b i))
    (hb_ser : ∀ i y, b i y = ∑' n : ℕ,
      (starRingEnd ℂ (c_g i n) * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) / ((M : ℂ) * (L : ℂ)))) *
        Complex.exp (-((2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (L : ℝ) : ℝ) : ℂ) * y))
    -- Putative constant-coefficient ADE `P` of positive degree + top-degree multipliers `γ` + `q₁`-expansion data:
    (P : MvPolynomial (Fin s × Fin (r + 1)) ℂ) (hP_deg : 1 ≤ P.totalDegree)
    (γ : Fin s × Fin (r + 1) → ℂ) (hγ : ∀ p, γ p ≠ 0) (N₁ : ℕ)
    (Q000 : MvPolynomial (Fin s × Fin (r + 1)) convergentSubring)
    (htop : ∀ α : (Fin s × Fin (r + 1)) →₀ ℕ, α.sum (fun _ e ↦ e) = P.totalDegree →
      (Q000.coeff α).val = PowerSeries.X ^ N₁ * PowerSeries.C (P.coeff α * ∏ p ∈ α.support, (γ p) ^ (α p)))
    {u₀ ρ₀ : ℝ} (hu₀_pos : 0 < u₀) (hu₀_le : u₀ ≤ 1 / 2) (huρ : u₀ < ρ₀)
    {N_shift : ℤ} (hN_le : N_shift ≤ 0) {K₂ : ℝ} (hK₂ : 0 ≤ K₂) (A_deg D : ℕ)
    (F : ℤ → Fin 2 → Fin (D + 1) → ℂ → ℂ)
    (f_hat : ℤ → Fin 2 → Fin (D + 1) → ℕ → ℂ)
    (hF_holo : ∀ m : ℤ, N_shift ≤ m → m ≤ 0 → ∀ ε a, DifferentiableOn ℂ (F m ε a) (slitDisk ρ₀))
    (hF_gev : ∀ m : ℤ, N_shift ≤ m → m ≤ 0 → ∀ ε a, HasGevrey1Asymp (sector34 u₀) (F m ε a) (f_hat m ε a))
    (C : ℤ → ℝ → ℂ)
    (hC_eq : ∀ m : ℤ, N_shift ≤ m → m ≤ 0 → ∀ u ∈ Set.Ioo (0 : ℝ) (u₀ / 2),
      C m u = ∑ ε : Fin 2, ∑ a : Fin (D + 1),
        (((u : ℝ) ^ ((ε.val : ℝ) / 2) : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) ^ a.val * F m ε a (u : ℂ))
    (hC_bd : ∀ m : ℤ, N_shift ≤ m → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      ‖C m u‖ ≤ K₂ * (((m - N_shift).toNat + 1 : ℕ) : ℝ) ^ A_deg * (1 + |Real.log u|) ^ D *
        (Real.exp (-Real.pi / ((L : ℝ) * u₀))) ^ (-m))
    (hzero : ∀ u ∈ Set.Ioo (0 : ℝ) (u₀ / 2),
      ∑' t : ℕ, C (N_shift + (t : ℤ)) u *
        (((Real.exp (-2 * Real.pi / ((L : ℝ) * u))) ^ (N_shift + (t : ℤ)) : ℝ) : ℂ) = 0)
    (hf000_eq : ∀ n : ℕ,
      f_hat 0 0 0 n = (-1 : ℂ) ^ n *
        (MvPolynomial.aeval
          (fun p : Fin s × Fin (r + 1) ↦
            PowerSeries.mk (fun m ↦ (-1 : ℂ) ^ (m + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val m))
          (MvPolynomial.map convergentSubring.subtype Q000)).coeff n) :
    False := by
  have hL_ge1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  -- Stage 1: `q1_induction_kill` kills `f_hat 0 0 0 n = 0` for ALL `n : ℕ`!
  have hkill := q1_induction_kill hu₀_pos hu₀_le huρ hL_ge1 hN_le hK₂ A_deg D
    F f_hat hF_holo hF_gev C hC_eq hC_bd hzero
  have hf000_zero : ∀ n : ℕ, f_hat 0 0 0 n = 0 := (hkill 0 hN_le le_rfl 0 0).2
  have hQ000_ann :
      MvPolynomial.aeval
        (fun p : Fin s × Fin (r + 1) ↦
          PowerSeries.mk (fun m ↦ (-1 : ℂ) ^ (m + p.2.val) * phiFormalCoeff (k p.1) (b p.1) p.2.val m))
        (MvPolynomial.map convergentSubring.subtype Q000) = 0 := by
    ext n
    have h0 := hf000_zero n
    rw [hf000_eq n] at h0
    rw [map_zero]
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero n (by norm_num))
  -- Stage 2: `top_degree_survival` proves `Q000 ≠ 0`!
  have hQ000_ne : Q000 ≠ 0 := (top_degree_survival P hP_deg γ hγ N₁ Q000 htop).1
  -- Stages 3–4: `mockModular_joint_shadow_rank_of_cuspSplit` derives `False`!
  exact mockModular_joint_shadow_rank_of_cuspSplit hM hL k hk w_twice hw_pos hw_eq
    g hg_diff hg_mod hg_per hg_lin c₀ c_g hC₀ ha hc_bd hg_fourier
    b C_b c_b hb hb_ser Q000 hQ000_ne hQ000_ann

end
end
end CubicTheta.AllD
