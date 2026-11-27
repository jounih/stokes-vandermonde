module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Uniqueness of a normally convergent exponential expansion with variable amplitudes.
The real parameter x tends to infinity (reciprocal small parameter in the manuscript).
All zero statements are equalities of germs, allowing a different threshold per action. -/
set_option maxHeartbeats 1200000

public section
namespace CubicTheta
open Filter Real Finset
open scoped Topology

/-- A power renormalization detects a nonzero amplitude. Fractional and negative
exponents are allowed, including every first nonzero Laurent–Puiseux term. -/
@[expose] def Detectable (a : ℝ → ℂ) : Prop :=
  ∃ v c : ℝ, 0 < c ∧ ∀ᶠ x in atTop, c ≤ x ^ v * ‖a x‖

theorem detectable_of_leading {a : ℝ → ℂ} {v : ℝ} {z : ℂ} (hz : z ≠ 0)
    (h : Tendsto (fun x : ℝ ↦ x ^ v • a x) atTop (𝓝 z)) : Detectable a := by
  refine ⟨v, ‖z‖ / 2, half_pos (norm_pos_iff.mpr hz), ?_⟩
  filter_upwards [h.norm.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hz))),
    eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  simpa [norm_smul, Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hxpos v)] using hx.le

/-- Once earlier coefficients vanish, the exponential gap makes the next
coefficient smaller than every real power, even if it contains oscillations. -/
theorem flat_of_earlier_zero (w : ℕ → ℝ) (hw : StrictMono w) (a : ℕ → ℝ → ℂ)
    (b : ℕ → ℝ) (hb : Summable b) (K reserve : ℝ)
    (major : ∀ᶠ x : ℝ in atTop, ∀ n, ‖a n x‖ ≤ b n * exp (w n*reserve) * x ^ K)
    (zeroSum : ∀ᶠ x : ℝ in atTop, HasSum (fun n ↦ exp (-w n * x) • a n x) 0)
    (n : ℕ) (previous : ∀ i < n, ∀ᶠ x : ℝ in atTop, a i x = 0) (v : ℝ) :
    Tendsto (fun x : ℝ ↦ x^v • a n x) atTop (𝓝 0) := by
  have earlier := (eventually_all_finset (range n)).2
    (fun i hi ↦ previous i (mem_range.mp hi))
  let gap := w (n+1) - w n
  have hgap : 0 < gap := sub_pos.mpr (hw (Nat.lt_succ_self n))
  let B := ∑' j : ℕ, b (j + (n+1))
  have hb' : Summable (fun j : ℕ ↦ b (j + (n+1))) := (summable_nat_add_iff _).2 hb
  have small : Tendsto (fun x : ℝ ↦ (B * exp (w (n+1)*reserve)) * (x ^ (v+K) * exp (-gap*x))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (v+K) gap hgap).const_mul (B * exp (w (n+1)*reserve))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ small
  filter_upwards [major,zeroSum,earlier,eventually_gt_atTop (0:ℝ),eventually_ge_atTop reserve] with x hmaj hsum hprev hx hreserve
  let term (i : ℕ) : ℂ := exp ((w n - w i)*x) • a i x
  have scaled : HasSum term 0 := by
    have h := hsum.const_smul (exp (w n*x))
    simpa only [term, smul_smul, ← exp_add, sub_mul, neg_mul, sub_eq_add_neg, add_mul, smul_zero] using h
  have first : ∑ i ∈ range (n+1), term i = a n x := by
    rw [sum_range_succ, sum_eq_zero (fun i hi ↦ by simp [term, hprev i hi])]
    simp [term]
  have tail : (∑' j : ℕ, term (j+(n+1))) = -a n x := by
    have h := scaled.summable.sum_add_tsum_nat_add (n+1)
    rw [scaled.tsum_eq, first] at h
    exact eq_neg_of_add_eq_zero_right h
  let M := x ^ K * (exp (w (n+1)*reserve) * exp (-gap*x))
  have bound (j : ℕ) : ‖term (j+(n+1))‖ ≤ b (j+(n+1)) * M := by
    let i := j+(n+1)
    have hi : w (n+1) ≤ w i := hw.monotone (by dsimp [i]; omega)
    have he : exp ((w n-w i)*x) * exp (w i*reserve) ≤ exp (w (n+1)*reserve) * exp (-gap*x) := by
      rw [← exp_add, ← exp_add, exp_le_exp]; dsimp [gap]
      nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr hreserve)]
    have hbi : 0 ≤ b i := by
      have h := (norm_nonneg _).trans (hmaj i)
      exact nonneg_of_mul_nonneg_left (nonneg_of_mul_nonneg_left h (rpow_pos_of_pos hx K)) (exp_pos _)
    calc
      _ = exp ((w n-w i)*x) * ‖a i x‖ := by
        change ‖exp ((w n-w i)*x) • a i x‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmaj i) (exp_pos _).le
      _ = (b i * x^K) * (exp ((w n-w i)*x) * exp (w i*reserve)) := by ring
      _ ≤ (b i * x^K) * (exp (w (n+1)*reserve) * exp (-gap*x)) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hbi (rpow_pos_of_pos hx K).le)
      _ = _ := by dsimp [M, i]; ring
  have hs := hb'.mul_right M
  have hn := Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) bound hs
  have hu := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum bound hs)
  rw [tail, norm_neg, hb'.tsum_mul_right] at hu
  have hfinal := mul_le_mul_of_nonneg_left hu (rpow_pos_of_pos hx v).le
  have ident : x ^ v * (B * M) = (B * exp (w (n+1)*reserve)) * (x ^ (v+K) * exp (-gap*x)) := by
    rw [rpow_add hx]; dsimp [M]; ring
  simpa [norm_smul,Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos hx v)] using hfinal.trans_eq ident

/-- With an absolutely summable coefficient majorant and a common polynomial loss,
a zero sum forces each detectable-or-zero coefficient to be the zero germ. -/
theorem separate_actions (w : ℕ → ℝ) (hw : StrictMono w) (a : ℕ → ℝ → ℂ)
    (b : ℕ → ℝ) (hb : Summable b) (K reserve : ℝ)
    (major : ∀ᶠ x : ℝ in atTop, ∀ n, ‖a n x‖ ≤ b n * exp (w n*reserve) * x ^ K)
    (zeroSum : ∀ᶠ x : ℝ in atTop, HasSum (fun n ↦ exp (-w n * x) • a n x) 0)
    (detect : ∀ n, (∀ᶠ x : ℝ in atTop, a n x = 0) ∨ Detectable (a n)) :
    ∀ n, ∀ᶠ x : ℝ in atTop, a n x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases detect n with done | ⟨v,c,hc,lower⟩
    · exact done
    have flat := (flat_of_earlier_zero w hw a b hb K reserve major zeroSum n ih v).norm
    have small := flat.eventually (gt_mem_nhds (by simpa using hc : ‖(0:ℂ)‖ < c))
    filter_upwards [small,lower,eventually_gt_atTop (0:ℝ)] with x hs hl hx
    simp [Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos hx v)] at hs
    exact False.elim (hs.not_ge hl)

end CubicTheta
