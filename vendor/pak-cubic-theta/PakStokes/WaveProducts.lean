module

public import ActionSeparation
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Absolute expansions along a fixed frequency ray. A single reserved unit of
inverse temperature buys summability before, during and after multiplication. -/
public section
namespace CubicTheta
open Complex Filter Set
open scoped Topology
noncomputable section

structure WaveExpansion (ι : Type*) where
  rate : ι → ℂ
  amplitude : ι → ℝ → ℂ
  budget : ι → ℝ
  loss : ℕ
  re_nonneg : ∀ i, 0 ≤ (rate i).re
  budget_nonneg : ∀ i, 0 ≤ budget i
  summable_budget : Summable budget
  bound : ∀ᶠ x : ℝ in atTop, ∀ i,
    ‖amplitude i x‖ ≤ budget i * Real.exp (rate i).re * x^loss

namespace WaveExpansion
variable {ι κ : Type*}

def term (a : WaveExpansion ι) (x : ℝ) (i : ι) := exp (-a.rate i*x)*a.amplitude i x
def value (a : WaveExpansion ι) (x : ℝ) := ∑' i, a.term x i

theorem norm_term_bound (a : WaveExpansion ι) :
    ∀ᶠ x : ℝ in atTop, ∀ i, ‖a.term x i‖ ≤ a.budget i*x^a.loss := by
  filter_upwards [a.bound,eventually_ge_atTop (1:ℝ)] with x hb hx i
  simp only [term,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.neg_re,
    ofReal_re,ofReal_im,mul_zero,sub_zero]
  calc _ ≤ Real.exp (-(a.rate i).re*x)*(a.budget i*Real.exp (a.rate i).re*x^a.loss) :=
      mul_le_mul_of_nonneg_left (hb i) (Real.exp_pos _).le
       _ = (Real.exp (-(a.rate i).re*x)*Real.exp (a.rate i).re)*(a.budget i*x^a.loss) := by ring
       _ ≤ 1*(a.budget i*x^a.loss) := by
         rw [← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (a.budget_nonneg i) (by positivity))
         apply Real.exp_le_one_iff.mpr; nlinarith [mul_nonneg (a.re_nonneg i) (sub_nonneg.mpr hx)]
       _ = _ := one_mul _

theorem norm_summable (a : WaveExpansion ι) :
    ∀ᶠ x : ℝ in atTop, Summable (fun i ↦ ‖a.term x i‖) := by
  filter_upwards [a.norm_term_bound] with x hb
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb (a.summable_budget.mul_right _)

/-- A common tail for the individual derivative identities and the two
expansion budgets suffice to differentiate the entire series on a tail.
Polynomial growth in x is handled on a bounded interval about each point. -/
theorem hasDerivAt_value (a d : WaveExpansion ι)
    (jets : ∀ᶠ x : ℝ in atTop, ∀ i, HasDerivAt (fun y ↦ a.term y i) (d.term x i) x) :
    ∀ᶠ x : ℝ in atTop, HasDerivAt a.value (d.value x) x := by
  obtain ⟨L,hL⟩ := eventually_atTop.1 (jets.and d.norm_term_bound)
  filter_upwards [eventually_gt_atTop (max L 0),a.norm_summable] with x hx hs
  let R := x+1
  have inside : x ∈ Ioo (max L 0) R := ⟨hx,by dsimp [R]; linarith⟩
  apply hasDerivAt_tsum_of_isPreconnected (d.summable_budget.mul_right (R^d.loss))
    isOpen_Ioo isPreconnected_Ioo (t := Ioo (max L 0) R) _ _ inside hs.of_norm inside
  · exact fun i y hy ↦ (hL y ((le_max_left ..).trans hy.1.le)).1 i
  · intro i y hy
    exact ((hL y ((le_max_left ..).trans hy.1.le)).2 i).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ((le_max_right ..).trans hy.1.le) hy.2.le _)
        (d.budget_nonneg i))

/-- Iteration only intersects finitely many tail conditions for a given jet. -/
theorem iteratedDeriv_value (a : ℕ → WaveExpansion ι)
    (jets : ∀ j, ∀ᶠ x : ℝ in atTop, ∀ i, HasDerivAt
      (fun y ↦ (a j).term y i) ((a (j+1)).term x i) x) (j : ℕ) :
    iteratedDeriv j (a 0).value =ᶠ[atTop] (a j).value := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    obtain ⟨L,hL⟩ := eventually_atTop.1 ih
    filter_upwards [eventually_gt_atTop L,hasDerivAt_value _ _ (jets j)] with x hx hd
    have near : iteratedDeriv j (a 0).value =ᶠ[𝓝 x] (a j).value :=
      (lt_mem_nhds hx).mono fun y hy ↦ hL y hy.le
    exact near.deriv_eq.trans hd.deriv

def add (a : WaveExpansion ι) (b : WaveExpansion κ) : WaveExpansion (ι ⊕ κ) where
  rate := Sum.elim a.rate b.rate
  amplitude := Sum.elim a.amplitude b.amplitude
  budget := Sum.elim a.budget b.budget
  loss := max a.loss b.loss
  re_nonneg := by rintro (i|j); exacts [a.re_nonneg i,b.re_nonneg j]
  budget_nonneg := by rintro (i|j); exacts [a.budget_nonneg i,b.budget_nonneg j]
  summable_budget := (HasSum.sum (f := Sum.elim a.budget b.budget)
    a.summable_budget.hasSum b.summable_budget.hasSum).summable
  bound := by
    filter_upwards [a.bound,b.bound,eventually_ge_atTop (1:ℝ)] with x ha hb hx
    rintro (i|j)
    · exact (ha i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (le_max_left ..))
        (mul_nonneg (a.budget_nonneg i) (Real.exp_pos _).le))
    · exact (hb j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (le_max_right ..))
        (mul_nonneg (b.budget_nonneg j) (Real.exp_pos _).le))

def mul (a : WaveExpansion ι) (b : WaveExpansion κ) : WaveExpansion (ι × κ) where
  rate := fun (i,j) ↦ a.rate i + b.rate j
  amplitude := fun (i,j) x ↦ a.amplitude i x * b.amplitude j x
  budget := fun (i,j) ↦ a.budget i * b.budget j
  loss := a.loss+b.loss
  re_nonneg := fun (i,j) ↦ add_nonneg (a.re_nonneg i) (b.re_nonneg j)
  budget_nonneg := fun (i,j) ↦ mul_nonneg (a.budget_nonneg i) (b.budget_nonneg j)
  summable_budget := a.summable_budget.mul_of_nonneg b.summable_budget a.budget_nonneg b.budget_nonneg
  bound := by
    filter_upwards [a.bound,b.bound,eventually_ge_atTop (0:ℝ)] with x ha hb hx
    rintro ⟨i,j⟩
    rw [norm_mul,Complex.add_re,Real.exp_add,pow_add]
    calc _ ≤ _ := mul_le_mul (ha i) (hb j) (norm_nonneg _) ((norm_nonneg _).trans (ha i))
         _ = _ := by ring

theorem value_add (a : WaveExpansion ι) (b : WaveExpansion κ) :
    ∀ᶠ x : ℝ in atTop, (a.add b).value x = a.value x + b.value x := by
  filter_upwards [a.norm_summable,b.norm_summable] with x ha hb
  exact (HasSum.sum (f := (a.add b).term x) ha.of_norm.hasSum hb.of_norm.hasSum).tsum_eq

theorem value_mul (a : WaveExpansion ι) (b : WaveExpansion κ) :
    ∀ᶠ x : ℝ in atTop, (a.mul b).value x = a.value x * b.value x := by
  filter_upwards [a.norm_summable,b.norm_summable] with x ha hb
  have h := ha.of_norm.hasSum.mul hb.of_norm.hasSum (summable_mul_of_summable_norm ha hb)
  apply HasSum.tsum_eq (h.congr_fun ?_)
  rintro ⟨i,j⟩
  simp only [term,mul,neg_add_rev,add_mul,Complex.exp_add]; ring

/-- Push the unweighted summable budget forward on the very same fibers as the
amplitudes. Equal complex rates are essential for factoring out one phase. -/
def groupAmplitude (a : WaveExpansion ι) (g : ι → κ) (k : κ) (x : ℝ) :=
  ∑' i : g ⁻¹' {k}, a.amplitude i x

def groupBudget (a : WaveExpansion ι) (g : ι → κ) (k : κ) :=
  ∑' i : g ⁻¹' {k}, a.budget i

theorem grouped_budget (a : WaveExpansion ι) (g : ι → κ) :
    Summable (a.groupBudget g) := (a.summable_budget.hasSum.tsum_fiberwise g).summable

theorem grouped_bound (a : WaveExpansion ι) (g : ι → κ) (r : κ → ℂ)
    (hr : ∀ i, a.rate i = r (g i)) :
    ∀ᶠ x : ℝ in atTop, ∀ k, ‖a.groupAmplitude g k x‖ ≤
      a.groupBudget g k * Real.exp (r k).re * x^a.loss := by
  filter_upwards [a.bound] with x hb k
  have hs := (a.summable_budget.subtype (fun i ↦ g i = k)).mul_right (Real.exp (r k).re * x^a.loss)
  have le (i : g ⁻¹' {k}) : ‖a.amplitude i x‖ ≤ a.budget i * (Real.exp (r k).re*x^a.loss) := by
    have he : g i = k := i.property
    simpa only [hr,he,mul_assoc] using hb i
  have hnorm := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) le hs
  exact (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum le hs).trans_eq (by
    rw [tsum_mul_right]; simp [groupBudget,mul_assoc]))

theorem grouped_hasSum (a : WaveExpansion ι) (g : ι → κ) (r : κ → ℂ)
    (hr : ∀ i, a.rate i = r (g i)) :
    ∀ᶠ x : ℝ in atTop, HasSum (fun k ↦ exp (-r k*x)*a.groupAmplitude g k x) (a.value x) := by
  filter_upwards [a.norm_summable] with x ha
  apply (ha.of_norm.hasSum.tsum_fiberwise g).congr_fun
  intro k
  unfold groupAmplitude
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  have he : g i = k := i.property
  simp only [term,hr,he]

end WaveExpansion
end
end CubicTheta
