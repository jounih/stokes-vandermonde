module

public import Mathlib.Analysis.Complex.Polynomial.GaussLucas
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic

/-! # A shifted polynomial derivative on the closed lower half-plane

For a polynomial with all zeros in the closed upper half-plane,
the logarithmic derivative has nonnegative imaginary part below the real
axis. Adding a strictly positive imaginary constant gives a uniform lower
bound, which can be applied repeatedly.
-/

public section
open Complex Polynomial
open scoped Polynomial

namespace PakPrimes.PrimePencil

/-- Every zero of the polynomial is in the closed upper half-plane. -/
@[expose] def UpperRoots (P : ℂ[X]) : Prop := ∀ z : ℂ, P.IsRoot z → 0 ≤ z.im

/-- The polynomial operator `D + i b`. -/
noncomputable def imagShift (b : ℝ) (P : ℂ[X]) : ℂ[X] :=
  P.derivative + C (Complex.I * (b:ℂ)) * P

theorem logDerivative_im_nonneg {P : ℂ[X]} (hP : UpperRoots P) {z : ℂ}
    (hz : z.im ≤ 0) (hp : P.eval z ≠ 0) :
    0 ≤ (P.derivative.eval z / P.eval z).im := by
  rw [(IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hp]
  suffices H : ∀ M : Multiset ℂ, (∀ r ∈ M, z.im ≤ r.im) →
      0 ≤ (M.map (fun r => 1 / (z-r))).sum.im by
    exact H P.roots fun r hr => hz.trans (hP r (Polynomial.isRoot_of_mem_roots hr))
  intro M
  induction M using Multiset.induction_on with
  | empty => simp
  | cons r M ih =>
    intro h
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
    apply add_nonneg _ (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))
    have hr := h r (Multiset.mem_cons_self ..)
    rw [one_div, Complex.inv_im, Complex.sub_im]
    have hn : 0 ≤ -(z.im - r.im) := by linarith
    exact mul_nonneg hn (inv_nonneg.mpr (Complex.normSq_nonneg _))

private theorem eval_imagShift_factor (b : ℝ) (P : ℂ[X]) {z : ℂ} (hp : P.eval z ≠ 0) :
    (imagShift b P).eval z =
      (P.derivative.eval z / P.eval z + Complex.I * (b:ℂ)) * P.eval z := by
  simp [imagShift, add_mul, div_mul_cancel₀ _ hp]

/-- The bound includes the boundary and all points below it. -/
theorem imagShift_lower_bound (b : ℝ) {P : ℂ[X]} (hP : UpperRoots P) {z : ℂ}
    (hz : z.im ≤ 0) : b * ‖P.eval z‖ ≤ ‖(imagShift b P).eval z‖ := by
  by_cases hp : P.eval z = 0
  · simp [hp]
  rw [eval_imagShift_factor _ _ hp, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply le_trans _ (Complex.im_le_norm _)
  simpa [Complex.add_im, Complex.mul_im] using add_le_add_right
    (logDerivative_im_nonneg hP hz hp) b

theorem upperRoots_imagShift {b : ℝ} (hb : 0 < b) {P : ℂ[X]} (hP : UpperRoots P) :
    UpperRoots (imagShift b P) := by
  intro z hroot
  by_contra! hz
  have hp : P.eval z ≠ 0 := fun h => hz.not_ge (hP z h)
  have h := imagShift_lower_bound b hP hz.le
  change (imagShift b P).eval z = 0 at hroot
  rw [hroot, norm_zero] at h
  exact (mul_pos hb (norm_pos_iff.mpr hp)).not_ge h

/-- After any number of iterations, root stability and a quantitative
nonvanishing estimate persist. The case `z=x:ℝ` gives the real-axis bound. -/
theorem iterate_imagShift {b : ℝ} (hb : 0 < b) {P : ℂ[X]} (hP : UpperRoots P)
    (n : ℕ) : UpperRoots ((imagShift b)^[n] P) ∧ ∀ z : ℂ, z.im ≤ 0 →
      b^n * ‖P.eval z‖ ≤ ‖((imagShift b)^[n] P).eval z‖ := by
  induction n with
  | zero => exact ⟨hP, by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨upperRoots_imagShift hb ih.1, ?_⟩
    intro z hz
    calc
      b^(n+1) * ‖P.eval z‖ = b * (b^n * ‖P.eval z‖) := by ring
      _ ≤ b * ‖((imagShift b)^[n] P).eval z‖ :=
        mul_le_mul_of_nonneg_left (ih.2 z hz) hb.le
      _ ≤ _ := imagShift_lower_bound b ih.1 hz

/-- A double zero gives the exact base of the iteration. -/
theorem second_imagShift_at_double_zero (b : ℝ) (P : ℂ[X]) {z : ℂ}
    (h₀ : P.eval z = 0) (h₁ : P.derivative.eval z = 0) :
    ((imagShift b)^[2] P).eval z = P.derivative.derivative.eval z := by
  simp [Function.iterate_succ_apply', imagShift, Polynomial.derivative_mul, h₀, h₁]

section Approximants

variable {ι : Type*} [DecidableEq ι]

/-- The pole-cleared finite approximant with positive inverse poles `a j`
and masses `w j`. For `a j = 1/j` this is the sine-product truncation. -/
noncomputable def massApproximant (b : ℝ) (s : Finset ι) (a w : ι → ℝ) : ℂ[X] :=
  X^2 * (C (b:ℂ) * (∏ j ∈ s, (1 + C (a j:ℂ)*X)) *
    ∑ i ∈ s, C (w i:ℂ) * ∏ j ∈ s.erase i, (1 - C (a j:ℂ)*X))

/-- Clearing the poles recovers the original finite rational expression
at every point away from those poles. -/
theorem eval_massApproximant (b : ℝ) (s : Finset ι) (a w : ι → ℝ) (z : ℂ)
    (hz : ∀ i ∈ s, 1 - (a i:ℂ)*z ≠ 0) :
    (massApproximant b s a w).eval z =
      z^2 * ((b:ℂ) * (∏ j ∈ s, (1 + (a j:ℂ)*z)) *
        ((∏ j ∈ s, (1 - (a j:ℂ)*z)) * ∑ i ∈ s, (w i:ℂ)/(1 - (a i:ℂ)*z))) := by
  simp only [massApproximant, eval_mul, eval_pow, eval_X, eval_C, eval_prod,
    eval_finsetSum, eval_add, eval_one, eval_sub]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← s.prod_erase_mul (fun j => 1 - (a j:ℂ)*z) hi]
  generalize (∏ j ∈ s.erase i, (1 - (a j:ℂ)*z)) = A
  rw [mul_assoc, mul_comm (1 - (a i:ℂ)*z) ((w i:ℂ)/_), div_mul_cancel₀ _ (hz i hi), mul_comm]

/-- The imaginary part of the weighted resolvent sum is strictly negative
below the real axis. Thus every zero of the cleared polynomial lies on
or above the axis. -/
theorem upperRoots_massApproximant {b : ℝ} (hb : 0 < b) {s : Finset ι}
    (hs : s.Nonempty) {a w : ι → ℝ} (ha : ∀ i ∈ s, 0 < a i) (hw : ∀ i ∈ s, 0 < w i) :
    UpperRoots (massApproximant b s a w) := by
  intro z hroot
  by_contra! hz
  have hz₀ : z ≠ 0 := fun h => by simp [h] at hz
  have hz' (i) (hi : i ∈ s) : ((a i:ℂ)*z).im < 0 := by
    simpa [Complex.mul_im] using mul_neg_of_pos_of_neg (ha i hi) hz
  have hD (i) (hi : i ∈ s) : 0 < (1 - (a i:ℂ)*z).im := by
    simpa [Complex.sub_im] using hz' i hi
  have hD₀ (i) (hi : i ∈ s) : 1 - (a i:ℂ)*z ≠ 0 := fun h => by simpa [h] using hD i hi
  have hF₀ (i) (hi : i ∈ s) : 1 + (a i:ℂ)*z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.add_im, Complex.one_im, zero_add, Complex.zero_im] at this
    exact (hz' i hi).ne this
  have hS : (∑ i ∈ s, (w i:ℂ)/(1 - (a i:ℂ)*z)).im < 0 := by
    rw [Complex.im_sum]
    apply Finset.sum_neg _ hs
    intro i hi
    rw [div_eq_mul_inv, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.inv_im]
    exact mul_neg_of_pos_of_neg (hw i hi)
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr (hD i hi))
        (inv_pos.mpr (Complex.normSq_pos.mpr (hD₀ i hi))))
  have hS₀ : (∑ i ∈ s, (w i:ℂ)/(1 - (a i:ℂ)*z)) ≠ 0 := fun h => by simp [h] at hS
  change (massApproximant b s a w).eval z = 0 at hroot
  rw [eval_massApproximant b s a w z hD₀] at hroot
  exact mul_ne_zero (pow_ne_zero _ hz₀) (mul_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') (Finset.prod_ne_zero_iff.mpr hF₀))
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr hD₀) hS₀)) hroot

theorem massApproximant_jets (b : ℝ) (s : Finset ι) (a w : ι → ℝ) :
    (massApproximant b s a w).eval 0 = 0 ∧
    (massApproximant b s a w).derivative.eval 0 = 0 ∧
    (massApproximant b s a w).derivative.derivative.eval 0 =
      (2*b:ℂ) * ∑ i ∈ s, (w i:ℂ) := by
  let A : ℂ[X] := C (b:ℂ) * (∏ j ∈ s, (1 + C (a j:ℂ)*X)) *
    ∑ i ∈ s, C (w i:ℂ) * ∏ j ∈ s.erase i, (1 - C (a j:ℂ)*X)
  change (X^2*A).eval 0 = 0 ∧ _ ∧ _
  have hA : A.eval 0 = (b:ℂ) * ∑ i ∈ s, (w i:ℂ) := by
    simp [A, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  change (X^2*A).eval 0 = 0 ∧ (X^2*A).derivative.eval 0 = 0 ∧
    (X^2*A).derivative.derivative.eval 0 = _
  simp [Polynomial.derivative_mul, Polynomial.derivative_pow, hA, mul_assoc]

end Approximants

open Filter
open scoped Topology

/-- The analytic counterpart of the shifted polynomial derivative. -/
noncomputable def functionShift (b : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv f z + Complex.I * (b:ℂ) * f z

/-- Local uniform convergence of the original polynomials on an open set
already implies convergence of every shifted derivative on that set. -/
theorem locallyUniform_imagShift (b : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (P : ℕ → ℂ[X]) {f : ℂ → ℂ}
    (hf : TendstoLocallyUniformlyOn (fun N z => (P N).eval z) f atTop U)
    (k : ℕ) : TendstoLocallyUniformlyOn
      (fun N z => ((imagShift b)^[k] (P N)).eval z) ((functionShift b)^[k] f) atTop U := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    have hd := ih.deriv (Eventually.of_forall fun N =>
      ((imagShift b)^[k] (P N)).differentiable.differentiableOn) hU
    have hc := (uniformContinuous_mul_left' (Complex.I * (b:ℂ))).comp_tendstoLocallyUniformlyOn ih
    have ha := hd.add hc
    rw [Function.iterate_succ_apply']
    apply ha.congr
    intro N z _
    simp [Function.iterate_succ_apply', imagShift, Function.comp_def, Polynomial.deriv]

/-- Exponential conjugation turns the shifted jets into the ordinary
derivatives used to read Taylor coefficients. -/
theorem exp_mul_iteratedDeriv (b : ℝ) (c : ℂ) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    Set.EqOn (iteratedDeriv k (fun z => c * Complex.exp (Complex.I * (b:ℂ) * z) * f z))
      (fun z => c * Complex.exp (Complex.I * (b:ℂ) * z) * ((functionShift b)^[k] f) z) U := by
  let d : ℂ := Complex.I * (b:ℂ)
  have hdiff (n : ℕ) : DifferentiableOn ℂ ((functionShift b)^[n] f) U := by
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (ih.deriv hU).add (ih.const_mul d)
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    have heq' : iteratedDeriv k (fun t => c * Complex.exp (Complex.I * (b:ℂ) * t) * f t) =ᶠ[𝓝 z]
        (fun t => c * Complex.exp (Complex.I * (b:ℂ) * t) * ((functionShift b)^[k] f) t) :=
      Filter.mem_of_superset (hU.mem_nhds hz) fun t ht => ih ht
    have heq := heq'.deriv_eq
    rw [iteratedDeriv_succ, heq, Function.iterate_succ_apply']
    have hexp : HasDerivAt (fun t : ℂ => Complex.exp (d*t)) (Complex.exp (d*z) * d) z := by
      simpa using (((hasDerivAt_id z).const_mul d).cexp)
    have hfun := ((hdiff k).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    change deriv (fun t => c * Complex.exp (d*t) * ((functionShift b)^[k] f) t) z = _
    refine ((hexp.const_mul c).mul hfun).deriv.trans ?_
    dsimp [functionShift, d]
    ring

/-- Limit form for the Taylor coefficients of the affine displacement.
The approximating polynomials have a double zero at the origin and
second derivative tending to `2b`. For each higher order only the limit
of the corresponding shifted jet is required. In the prime application
`b=π`, and the displacement is `-2i exp(iπt)L(t)`. -/
theorem affineCoefficient_lower_bound_of_limits (b : ℝ) (hb : 0 < b)
    (P : ℕ → ℂ[X]) (hP : ∀ N, UpperRoots (P N))
    (h₀ : ∀ N, (P N).eval 0 = 0) (h₁ : ∀ N, (P N).derivative.eval 0 = 0)
    (h₂ : Tendsto (fun N => (P N).derivative.derivative.eval 0) atTop (𝓝 ((2*b:ℝ):ℂ)))
    (k : ℕ) (v : ℂ)
    (hv : Tendsto (fun N => ((imagShift b)^[k+2] (P N)).eval 0) atTop (𝓝 v)) :
    4 * b^(k+1) / ((k+2).factorial : ℝ) ≤
      ‖-2 * Complex.I * v / ((k+2).factorial : ℂ)‖ := by
  have hi (N : ℕ) : b^k * ‖(P N).derivative.derivative.eval 0‖ ≤
      ‖((imagShift b)^[k+2] (P N)).eval 0‖ := by
    rw [Function.iterate_add_apply, ← second_imagShift_at_double_zero b (P N) (h₀ N) (h₁ N)]
    exact (iterate_imagShift hb (iterate_imagShift hb (hP N) 2).1 k).2 0 (by simp)
  have hlim : b^k * ‖((2*b:ℝ):ℂ)‖ ≤ ‖v‖ :=
    le_of_tendsto_of_tendsto' (tendsto_const_nhds.mul h₂.norm) hv.norm hi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hlim
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_two, Complex.norm_I,
    mul_one, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    4 * b^(k+1) = 2 * (b^k * (2*b)) := by ring
    _ ≤ 2 * ‖v‖ := by linarith

/-- For literal pole-cleared positive-mass polynomials, it suffices to
know convergence of the total mass and local uniform convergence of the
polynomials on a neighborhood of the origin. -/
theorem massApproximant_affine_bound {ι : Type*} [DecidableEq ι]
    {b : ℝ} (hb : 0 < b) (s : ℕ → Finset ι) (hs : ∀ N, (s N).Nonempty)
    (a w : ι → ℝ) (ha : ∀ N i, i ∈ s N → 0 < a i) (hw : ∀ N i, i ∈ s N → 0 < w i)
    (hm : Tendsto (fun N => ∑ i ∈ s N, w i) atTop (𝓝 1))
    {U : Set ℂ} (hU : IsOpen U) (h0 : 0 ∈ U) {f : ℂ → ℂ}
    (hf : TendstoLocallyUniformlyOn (fun N z => (massApproximant b (s N) a w).eval z) f atTop U)
    (k : ℕ) : 4 * b^(k+1) / ((k+2).factorial : ℝ) ≤
      ‖iteratedDeriv (k+2) (fun z => -2 * Complex.I * Complex.exp (Complex.I * (b:ℂ) * z) * f z)
        0 / ((k+2).factorial : ℂ)‖ := by
  let P := fun N => massApproximant b (s N) a w
  have hdiff := hf.differentiableOn (Eventually.of_forall fun N => (P N).differentiableOn) hU
  rw [exp_mul_iteratedDeriv b (-2 * Complex.I) hU hdiff (k+2) h0]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  apply affineCoefficient_lower_bound_of_limits b hb P
    (fun N => upperRoots_massApproximant hb (hs N) (ha N) (hw N))
    (fun N => (massApproximant_jets b (s N) a w).1)
    (fun N => (massApproximant_jets b (s N) a w).2.1)
  · have hmass := (Complex.continuous_ofReal.tendsto 1).comp hm
    have h₂ := hmass.const_mul ((2*b):ℂ)
    simpa [P, (fun N => (massApproximant_jets b (s N) a w).2.2), Function.comp_def] using h₂
  · exact (locallyUniform_imagShift b hU P hf (k+2)).tendsto_at h0

private theorem imagShift_add (b : ℝ) (P Q : ℂ[X]) :
    imagShift b (P+Q) = imagShift b P + imagShift b Q := by
  simp [imagShift, mul_add]; ring

private theorem imagShift_C_mul (b : ℝ) (c : ℂ) (P : ℂ[X]) :
    imagShift b (C c * P) = C c * imagShift b P := by
  simp [imagShift, Polynomial.derivative_mul]; ring

private theorem imagShift_X_mul (b : ℝ) (P : ℂ[X]) :
    imagShift b (X*P) = X * imagShift b P + P := by
  simp [imagShift, Polynomial.derivative_mul]; ring

/-- The commutator with multiplication by X yields the gain from
removing the two zeros *before* estimating the shifted jets. -/
theorem iterate_imagShift_X_mul (b : ℝ) (k : ℕ) (P : ℂ[X]) :
    (imagShift b)^[k+1] (X*P) =
      X * (imagShift b)^[k+1] P + C ((k+1:ℕ):ℂ) * (imagShift b)^[k] P := by
  induction k with
  | zero => simp [imagShift_X_mul]
  | succ k ih =>
    calc
      (imagShift b)^[k+2] (X*P) = imagShift b ((imagShift b)^[k+1] (X*P)) :=
        Function.iterate_succ_apply' ..
      _ = X * imagShift b ((imagShift b)^[k+1] P) + (imagShift b)^[k+1] P +
          C ((k+1:ℕ):ℂ) * imagShift b ((imagShift b)^[k] P) := by
        rw [ih, imagShift_add, imagShift_X_mul, imagShift_C_mul]
      _ = _ := by
        rw [← Function.iterate_succ_apply' (imagShift b) (k+1) P,
          ← Function.iterate_succ_apply' (imagShift b) k P]
        let Y := (imagShift b)^[k+1] P
        let Z := (imagShift b)^[k+2] P
        change X*Z + Y + C ((k+1:ℕ):ℂ)*Y = X*Z + C ((k+2:ℕ):ℂ)*Y
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_one, map_ofNat]
        ring

theorem eval_iterate_imagShift_X_sq (b : ℝ) (k : ℕ) (P : ℂ[X]) :
    ((imagShift b)^[k+2] (X^2*P)).eval 0 =
      ((k+2:ℕ):ℂ) * ((k+1:ℕ):ℂ) * ((imagShift b)^[k] P).eval 0 := by
  rw [pow_two, mul_assoc, iterate_imagShift_X_mul b (k+1) (X*P)]
  simp only [eval_add, eval_mul, eval_X, zero_mul, zero_add, eval_C]
  rw [iterate_imagShift_X_mul b k P]
  simp only [eval_add, eval_mul, eval_X, zero_mul, zero_add, eval_C, mul_assoc]

/-- Coefficient bound retaining the entire contribution of the double
zero. The finite polynomials have the form `X² * A N`. Only the mass at
zero and local uniform convergence of the original polynomials enter. -/
theorem factored_affine_bound {b : ℝ} (hb : 0 < b) (A : ℕ → ℂ[X])
    (hA : ∀ N, UpperRoots (A N))
    (hm : Tendsto (fun N => (A N).eval 0) atTop (𝓝 (b:ℂ)))
    {U : Set ℂ} (hU : IsOpen U) (h0 : 0 ∈ U) {f : ℂ → ℂ}
    (hf : TendstoLocallyUniformlyOn (fun N z => (X^2*A N).eval z) f atTop U)
    (k : ℕ) : 2 * b^(k+1) / (k.factorial : ℝ) ≤
      ‖iteratedDeriv (k+2) (fun z => -2 * Complex.I * Complex.exp (Complex.I * (b:ℂ) * z) * f z)
        0 / ((k+2).factorial : ℂ)‖ := by
  let P := fun N => X^2 * A N
  have hi (N : ℕ) : ((k+2:ℕ):ℝ) * ((k+1:ℕ):ℝ) * b^k * ‖(A N).eval 0‖ ≤
      ‖((imagShift b)^[k+2] (P N)).eval 0‖ := by
    change _ ≤ ‖((imagShift b)^[k+2] (X^2*A N)).eval 0‖
    rw [eval_iterate_imagShift_X_sq]
    simp only [norm_mul, Complex.norm_natCast, mul_assoc]
    gcongr
    exact (iterate_imagShift hb (hA N) k).2 0 (by simp)
  have hd := (locallyUniform_imagShift b hU P hf (k+2)).tendsto_at h0
  have hlim := le_of_tendsto_of_tendsto' (tendsto_const_nhds.mul hm.norm) hd.norm hi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hlim
  have hdiff := hf.differentiableOn (Eventually.of_forall fun N => (P N).differentiableOn) hU
  rw [exp_mul_iteratedDeriv b (-2 * Complex.I) hU hdiff (k+2) h0]
  simp only [mul_zero, Complex.exp_zero, mul_one, norm_div, norm_mul, norm_neg,
    Complex.norm_two, Complex.norm_I, Complex.norm_natCast]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast at *
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hlim (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num)
    (show (0:ℝ) ≤ (k.factorial:ℝ) by positivity))]


/-- Every Taylor coefficient from degree two on obeys the stronger bound
obtained by peeling off the double zero. For inverse poles `1/j` and
`b = π`, this reads `|cₘ| ≥ 2 π^(m−1)/(m−2)!`. -/
theorem massApproximant_factored_affine_bound {ι : Type*} [DecidableEq ι]
    {b : ℝ} (hb : 0 < b) (s : ℕ → Finset ι) (hs : ∀ N, (s N).Nonempty)
    (a w : ι → ℝ) (ha : ∀ N i, i ∈ s N → 0 < a i) (hw : ∀ N i, i ∈ s N → 0 < w i)
    (hm : Tendsto (fun N => ∑ i ∈ s N, w i) atTop (𝓝 1))
    {U : Set ℂ} (hU : IsOpen U) (h0 : 0 ∈ U) {f : ℂ → ℂ}
    (hf : TendstoLocallyUniformlyOn (fun N z => (massApproximant b (s N) a w).eval z) f atTop U)
    (k : ℕ) : 2 * b^(k+1) / (k.factorial : ℝ) ≤
      ‖iteratedDeriv (k+2) (fun z => -2 * Complex.I * Complex.exp (Complex.I * (b:ℂ) * z) * f z)
        0 / ((k+2).factorial : ℂ)‖ := by
  let A (N : ℕ) : ℂ[X] := C (b:ℂ) * (∏ j ∈ s N, (1 + C (a j:ℂ)*X)) *
    ∑ i ∈ s N, C (w i:ℂ) * ∏ j ∈ (s N).erase i, (1 - C (a j:ℂ)*X)
  apply factored_affine_bound hb A _ _ hU h0 hf k
  · intro N z hz
    apply upperRoots_massApproximant hb (hs N) (ha N) (hw N) z
    change (X^2 * A N).eval z = 0
    change (A N).eval z = 0 at hz
    simp [hz]
  · have hmul := ((Complex.continuous_ofReal.tendsto 1).comp hm).const_mul (b:ℂ)
    simpa [A, Polynomial.eval_prod, Polynomial.eval_finsetSum, Function.comp_def] using hmul

end PakPrimes.PrimePencil
