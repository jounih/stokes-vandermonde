module

public import PakPrimes.NthPrimeAsymptotics
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-! Flatness of the nth-prime approximation after power-weighted Abel smoothing. -/
public section
noncomputable section
namespace PakPrimes.NthPrime
open Filter Real Finset

/-- Zero-based sequence error, with O(n/log(n)^M) precision at every order. -/
def IndexLogError (e : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    |e n| ≤ C * (n+1 : ℝ) / (log (n+1 : ℝ))^M

private theorem indexLinear {e : ℕ → ℝ} (herr : IndexLogError e) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, |e n| ≤ A * (n+1 : ℝ) := by
  obtain ⟨C,hC,h⟩ := herr 0
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let B := ∑ i ∈ range N, |e i|
  let A := max B C
  have hA : 0 < A := hC.trans_le (le_max_right _ _)
  refine ⟨A,hA,fun n => ?_⟩
  by_cases hn : N ≤ n
  · simpa using (show |e n| ≤ C * (n+1 : ℝ) by simpa using hN n hn).trans
      (mul_le_mul_of_nonneg_right (le_max_right B C) (by positivity))
  · have hsmall : |e n| ≤ B := single_le_sum (fun i _ => abs_nonneg (e i))
        (mem_range.mpr (by omega))
    apply (hsmall.trans (le_max_left _ _)).trans
    change A ≤ A * (n+1 : ℝ)
    nlinarith [mul_nonneg hA.le (Nat.cast_nonneg (α := ℝ) n)]

private theorem expMoment_bound (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y^j * exp (-y) ≤ ((2 : ℝ)^j * j.factorial) * exp (-y/2) := by
  have h := Real.pow_div_factorial_le_exp (y/2) (by positivity) j
  have hn : (0 : ℝ) < j.factorial := by positivity
  have hp := (div_le_iff₀ hn).mp h
  have hpow : y^j = (2 : ℝ)^j * (y/2)^j := by rw [← mul_pow]; congr 1; ring
  have hh : y^j ≤ (2 : ℝ)^j * j.factorial * exp (y/2) := by
    rw [hpow]
    calc _ ≤ (2 : ℝ)^j * (exp (y/2) * j.factorial) := by gcongr
         _ = _ := by ring
  calc
    _ ≤ ((2 : ℝ)^j * j.factorial * exp (y/2)) * exp (-y) := by gcongr
    _ = _ := by rw [mul_assoc, ← exp_add]; congr 2; ring

private theorem geometricMass {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => t * exp (-(t * (n+1 : ℝ))/2)) ∧
      (∑' n : ℕ, t * exp (-(t * (n+1 : ℝ))/2)) ≤ 2 := by
  let r := exp (-t/2)
  have hr : 0 < r := exp_pos _
  have hlt : r < 1 := exp_lt_one_iff.mpr (by linarith)
  have he (n : ℕ) : t * exp (-(t*(n+1 : ℝ))/2) = (t*r)*r^n := by
    change _ = (t*exp (-t/2))*exp (-t/2)^n
    rw [← exp_nat_mul, mul_assoc, ← exp_add]; congr 2; ring
  simp_rw [he]
  have hs := summable_geometric_of_lt_one hr.le hlt
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr.le hlt, ← div_eq_mul_inv,
      div_le_iff₀ (sub_pos.mpr hlt)]
  have hex : r * exp (t/2) = 1 := by
    dsimp [r]; rw [← exp_add, show -t/2+t/2 = 0 by ring, exp_zero]
  have hend := mul_le_mul_of_nonneg_left (add_one_le_exp (t/2)) hr.le
  rw [hex] at hend
  nlinarith

/-- After multiplication by any fixed power of u, the logarithmic coefficient
error at scale n exp(-u) is uniformly bounded by an affine function of that scale. -/
private theorem error_at_scale {e : ℕ → ℝ} (herr : IndexLogError e) (M : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ u : ℝ in atTop, ∀ n : ℕ,
      u^M * exp (-u) * |e n| ≤ L * (1 + exp (-u) * (n+1 : ℝ)) := by
  obtain ⟨A,hA,ha⟩ := indexLinear herr
  obtain ⟨C,hC,h⟩ := herr M
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let B := (M.factorial : ℝ) / (1/2 : ℝ)^M
  let L := A*B + C * (2 : ℝ)^M
  have hB : 0 < B := by dsimp [B]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L,hL, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (2*(N:ℝ)))] with u hu
  intro n
  have hu1 := (le_max_left 1 (2*(N:ℝ))).trans hu
  have huN := (le_max_right 1 (2*(N:ℝ))).trans hu
  have hu0 : 0 < u := by linarith
  let y := exp (-u) * (n+1 : ℝ)
  have hy : 0 < y := by dsimp [y]; positivity
  change _ ≤ L * (1+y)
  by_cases hcut : log (n+1 : ℝ) < u/2
  · have hyb : y ≤ exp (-(1/2 : ℝ)*u) := by
      rw [show -(1/2 : ℝ)*u = -u+u/2 by ring, exp_add]
      exact mul_le_mul_of_nonneg_left
        ((Real.log_lt_iff_lt_exp (by positivity : 0 < (n+1 : ℝ))).mp hcut).le
        (exp_pos _).le
    have hbound := Main.exp_neg_mul_le_inv_pow (1/2) (by norm_num) M hu0
    have hup : u^M * y ≤ B := by
      have hby : y ≤ B / u^M := hyb.trans hbound
      rw [mul_comm]
      exact (le_div_iff₀ (pow_pos hu0 M)).mp hby
    calc
      _ ≤ u^M * exp (-u) * (A * (n+1 : ℝ)) := by gcongr; exact ha n
      _ = A * (u^M * y) := by dsimp [y]; ring
      _ ≤ A*B := by gcongr
      _ ≤ L := le_add_of_nonneg_right (by positivity)
      _ ≤ L * (1+y) := by nlinarith [mul_nonneg hL.le hy.le]
  · have hlog := le_of_not_gt hcut
    have hg : 0 < log (n+1 : ℝ) := by linarith
    have hlogn := log_le_sub_one_of_pos (by positivity : 0 < (n+1 : ℝ))
    have hn : N ≤ n := by exact_mod_cast (show (N : ℝ) ≤ n by linarith)
    have hpow : u^M ≤ (2:ℝ)^M * (log (n+1:ℝ))^M := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hu0.le (by linarith) M
    have he := (le_div_iff₀ (pow_pos hg M)).mp (hN n hn)
    have hprod : u^M * |e n| ≤ (C * (2:ℝ)^M) * (n+1 : ℝ) := by
      calc _ ≤ (2:ℝ)^M * (log (n+1:ℝ))^M * |e n| := by gcongr
           _ = (2:ℝ)^M * (|e n| * (log (n+1:ℝ))^M) := by ring
           _ ≤ (2:ℝ)^M * (C * (n+1:ℝ)) := by gcongr
           _ = _ := by ring
    calc
      _ = (u^M * |e n|) * exp (-u) := by ring
      _ ≤ ((C * (2:ℝ)^M) * (n+1 : ℝ)) * exp (-u) := by gcongr
      _ = C*(2:ℝ)^M*y := by dsimp [y]; ring
      _ ≤ L*y := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hA.le hB.le)) hy.le
      _ ≤ L*(1+y) := by linarith

/-- Absolute coefficient error with the degree-j normalized Boltzmann weight. -/
@[expose] def abelErrorTerm (e : ℕ → ℝ) (j : ℕ) (u : ℝ) (n : ℕ) : ℝ :=
  let t := exp (-u)
  let y := t * (n+1 : ℝ)
  t^2 * |e n| * y^j * exp (-y)

private theorem abelErrorTerm_nonneg (e : ℕ → ℝ) (j : ℕ) (u : ℝ) (n : ℕ) :
    0 ≤ abelErrorTerm e j u n := by unfold abelErrorTerm; positivity

/-- Each fixed monomial-weighted infinite error sum is flat to every
inverse-logarithmic order. The estimate controls the sum of absolute errors. -/
theorem abelError_allOrders {e : ℕ → ℝ} (herr : IndexLogError e) (j M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop,
      Summable (abelErrorTerm e j u) ∧ (∑' n, abelErrorTerm e j u n) ≤ C / u^M := by
  obtain ⟨L,hL,h⟩ := error_at_scale herr M
  let W := (2:ℝ)^j * j.factorial + 2^(j+1) * (j+1).factorial
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨L*W*2, by positivity, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with u hu hu1
  let t := exp (-u)
  have ht : 0 < t := exp_pos _
  have hup : 0 < u^M := pow_pos (by linarith : 0 < u) M
  have hmono (n : ℕ) : u^M * abelErrorTerm e j u n ≤
      (L*W) * (t * exp (-(t * (n+1 : ℝ))/2)) := by
    let y := t * (n+1 : ℝ)
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have h1 := expMoment_bound j hy
    have h2 := expMoment_bound (j+1) hy
    have hh : (1+y) * (y^j * exp (-y)) ≤ W * exp (-y/2) := by
      dsimp [W]
      rw [add_mul]
      convert add_le_add h1 h2 using 1 <;> ring
    change u^M * (t^2 * |e n| * y^j * exp (-y)) ≤ (L*W)*(t*exp (-y/2))
    calc _ = t * ((u^M*t*|e n|) * (y^j*exp (-y))) := by ring
         _ ≤ t * ((L*(1+y)) * (y^j*exp (-y))) := by
           exact mul_le_mul_of_nonneg_left
             (mul_le_mul_of_nonneg_right (hu n) (mul_nonneg (pow_nonneg hy j) (exp_pos _).le))
             ht.le
         _ = (t*L) * ((1+y) * (y^j * exp (-y))) := by ring
         _ ≤ (t*L) * (W * exp (-y/2)) := by gcongr
         _ = _ := by ring
  obtain ⟨hgeom,hmass⟩ := geometricMass ht
  have hmajor := hgeom.mul_left (L*W)
  have hs := hmajor.of_nonneg_of_le
    (fun n => mul_nonneg hup.le (abelErrorTerm_nonneg e j u n)) hmono
  have hs0 := hs.mul_left (u^M)⁻¹
  constructor
  · simpa only [← mul_assoc, inv_mul_cancel₀ hup.ne', one_mul] using hs0
  · apply (le_div_iff₀ hup).2
    rw [mul_comm, ← tsum_mul_left]
    apply (hs.tsum_le_tsum hmono hmajor).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hmass (mul_nonneg hL.le hW.le)

/-- Application to the actual nth primes and the inverse of the normalized
logarithmic integral. The only arithmetic input is the all-orders PNT. -/
theorem prime_inverseLi_abelError (hpnt : Main.PNTAllOrders) (j M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop,
      let e := fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) - inverseLi (n+1 : ℝ)
      Summable (abelErrorTerm e j u) ∧ (∑' n, abelErrorTerm e j u n) ≤ C / u^M :=
  abelError_allOrders (nth_prime_inverseLi_allOrders hpnt) j M

/-- Signed normalized Abel summand with an arbitrary polynomial in t(n+1). -/
@[expose] def abelPolyTerm (e : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  let t := exp (-u)
  let y := t * (n+1 : ℝ)
  t^2 * e n * P.eval y * exp (-y)

theorem abelPolyError_allOrders {e : ℕ → ℝ} (herr : IndexLogError e) (P : Polynomial ℝ)
    (M : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop,
      Summable (fun n => |abelPolyTerm e P n u|) ∧
        (∑' n, |abelPolyTerm e P n u|) ≤ C / u^M := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨A,hA,hp⟩ := hP
    obtain ⟨B,hB,hq⟩ := hQ
    refine ⟨A+B,add_pos hA hB,?_⟩
    filter_upwards [hp,hq] with u hu hv
    have hadd (n : ℕ) : |abelPolyTerm e (P+Q) n u| ≤
        |abelPolyTerm e P n u| + |abelPolyTerm e Q n u| := by
      have he : abelPolyTerm e (P+Q) n u = abelPolyTerm e P n u + abelPolyTerm e Q n u := by
        simp only [abelPolyTerm, Polynomial.eval_add]; ring
      rw [he]; exact abs_add_le _ _
    have hs := hu.1.add hv.1
    have hsum := hs.of_nonneg_of_le (fun n => abs_nonneg _) hadd
    refine ⟨hsum, (hsum.tsum_le_tsum hadd hs).trans ?_⟩
    rw [hu.1.tsum_add hv.1, add_div]
    exact add_le_add hu.2 hv.2
  | monomial j a =>
    obtain ⟨C,hC,h⟩ := abelError_allOrders herr j M
    refine ⟨(|a|+1)*C,by positivity,?_⟩
    filter_upwards [h,eventually_ge_atTop (1:ℝ)] with u hu hu1
    have hmono (n : ℕ) : |abelPolyTerm e (Polynomial.monomial j a) n u| =
        |a| * abelErrorTerm e j u n := by
      simp only [abelPolyTerm, abelErrorTerm, Polynomial.eval_monomial,
        abs_mul, abs_pow, abs_of_nonneg (exp_pos _).le,
        abs_of_nonneg (show 0 ≤ (n:ℝ)+1 by positivity)]
      ring
    simp_rw [hmono]
    refine ⟨hu.1.mul_left _, ?_⟩
    rw [tsum_mul_left]
    calc _ ≤ |a| * (C/u^M) := mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)
         _ ≤ (|a|+1) * (C/u^M) := by gcongr; linarith
         _ = _ := by ring

/-- Polynomial induced by one derivative in u = -log t. -/
@[expose] def abelJetStep (P : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.X - 2) * P - Polynomial.X * P.derivative

theorem abelPolyTerm_hasDerivAt (e : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (abelPolyTerm e P n) (abelPolyTerm e (abelJetStep P) n u) u := by
  let t := fun v : ℝ => exp (-v)
  let y := fun v : ℝ => t v * (n+1 : ℝ)
  have ht : HasDerivAt t (-t u) u := by simpa [t] using (hasDerivAt_id u).neg.exp
  have hy : HasDerivAt y (-y u) u := by simpa [y] using ht.mul_const (n+1 : ℝ)
  have he := ((((ht.pow 2).mul_const (e n)).mul ((P.hasDerivAt (y u)).comp u hy)).mul
    hy.neg.exp)
  convert he using 1
  · rfl
  · simp [abelPolyTerm, abelJetStep, t, y]; ring

/-- Every logarithmic derivative of the actual nth-prime error summands
has absolutely summable errors bounded by C/u^M, at every order M. -/
theorem prime_inverseLi_abelJetError (hpnt : Main.PNTAllOrders) (r M : ℕ) :
    let e := fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) - inverseLi (n+1 : ℝ)
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop,
      Summable (fun n => |iteratedDeriv r (abelPolyTerm e 1 n) u|) ∧
        (∑' n, |iteratedDeriv r (abelPolyTerm e 1 n) u|) ≤ C / u^M := by
  let e := fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) - inverseLi (n+1 : ℝ)
  have hjet (k : ℕ) (n : ℕ) : iteratedDeriv k (abelPolyTerm e 1 n) =
      abelPolyTerm e (abelJetStep^[k] 1) n := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact funext fun u => (abelPolyTerm_hasDerivAt _ _ _ _).deriv
  change ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop,
    Summable (fun n => |iteratedDeriv r (abelPolyTerm e 1 n) u|) ∧
      (∑' n, |iteratedDeriv r (abelPolyTerm e 1 n) u|) ≤ C / u^M
  simp only [hjet]
  exact abelPolyError_allOrders (e := e) (nth_prime_inverseLi_allOrders hpnt)
    (abelJetStep^[r] 1) M

private theorem abelPoly_localBound {e : ℕ → ℝ} (herr : IndexLogError e)
    (P : Polynomial ℝ) (x : ℝ) : ∃ B : ℕ → ℝ, Summable B ∧
      ∀ n u, u ∈ Set.Ioo (x-1) (x+1) → |abelPolyTerm e P n u| ≤ B n := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨B,hB,hp⟩ := hP
    obtain ⟨C,hC,hq⟩ := hQ
    refine ⟨_,hB.add hC,fun n u hu => ?_⟩
    have he : abelPolyTerm e (P+Q) n u = abelPolyTerm e P n u + abelPolyTerm e Q n u := by
      simp only [abelPolyTerm, Polynomial.eval_add]; ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (hp n u hu) (hq n u hu))
  | monomial j a =>
    obtain ⟨A,hA,he⟩ := indexLinear herr
    let T := exp (-(x-1))
    let τ := exp (-(x+1))
    let r := exp (-τ)
    have hτ : 0 < τ := exp_pos _
    have hr : 0 < r := exp_pos _
    have hlt : r < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hτ)
    let C := T^2 * (A * (|a| * T^j))
    have hs := (summable_pow_mul_geometric_of_norm_lt_one (j+1) (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_pos hr])).comp_injective Nat.succ_injective
    refine ⟨_,hs.mul_left C,fun n u hu => ?_⟩
    have hT : exp (-u) ≤ T := exp_le_exp.mpr (neg_le_neg hu.1.le)
    have hlow : τ ≤ exp (-u) := exp_le_exp.mpr (neg_le_neg hu.2.le)
    have harg : 0 ≤ (n:ℝ)+1 := by positivity
    have hkernel : exp (-(exp (-u)*((n:ℝ)+1))) ≤ r^(n+1) := by
      dsimp [r]; rw [← exp_nat_mul]; apply exp_le_exp.mpr
      push_cast; nlinarith [mul_le_mul_of_nonneg_right hlow harg]
    change _ ≤ C * (((n+1 : ℕ) : ℝ)^(j+1) * r^(n+1))
    simp only [abelPolyTerm, Polynomial.eval_monomial, abs_mul, abs_pow,
      abs_of_pos (exp_pos _), abs_of_nonneg harg, Nat.cast_add, Nat.cast_one]
    calc _ ≤ T^2 * (A*((n:ℝ)+1)) * (|a| * (T*((n:ℝ)+1))^j) * r^(n+1) := by
            gcongr
            exact he n
         _ = _ := by dsimp [C]; rw [mul_pow]; ring

/-- Termwise logarithmic differentiation of the full Abel sum. -/
theorem hasDerivAt_abelPolySum {e : ℕ → ℝ} (herr : IndexLogError e) (P : Polynomial ℝ)
    (x : ℝ) : HasDerivAt (fun u => ∑' n, abelPolyTerm e P n u)
      (∑' n, abelPolyTerm e (abelJetStep P) n x) x := by
  have hx : x ∈ Set.Ioo (x-1) (x+1) := ⟨by linarith,by linarith⟩
  obtain ⟨B,hB,hbound⟩ := abelPoly_localBound herr (abelJetStep P) x
  obtain ⟨C,hC,hbase⟩ := abelPoly_localBound herr P x
  exact hasDerivAt_tsum_of_isPreconnected hB isOpen_Ioo isPreconnected_Ioo
    (fun n u _ => abelPolyTerm_hasDerivAt _ _ n u)
    (fun n u hu => by simpa only [Real.norm_eq_abs] using hbound n u hu) hx
    (hC.of_norm_bounded fun n => hbase n x hx) hx

set_option maxHeartbeats 1200000 in
/-- The actual r-th derivative of the entire smoothed prime-minus-inverse-li
series is O(u^(-M)) for every r and M, with t = exp(-u). -/
theorem prime_inverseLi_abelSumJetError (hpnt : Main.PNTAllOrders) (r M : ℕ) :
    let e := fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) - inverseLi (n+1 : ℝ)
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop,
      |iteratedDeriv r (fun v => ∑' n, abelPolyTerm e 1 n v) u| ≤ C / u^M := by
  let e := fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) - inverseLi (n+1 : ℝ)
  have he : IndexLogError e := nth_prime_inverseLi_allOrders hpnt
  have hjet (k : ℕ) : iteratedDeriv k (fun v => ∑' n, abelPolyTerm e 1 n v) =
      fun u => ∑' n, abelPolyTerm e (abelJetStep^[k] 1) n u := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact funext fun u => (hasDerivAt_abelPolySum he _ u).deriv
  change ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop,
    |iteratedDeriv r (fun v => ∑' n, abelPolyTerm e 1 n v) u| ≤ C / u^M
  rw [hjet]
  obtain ⟨C,hC,h⟩ := abelPolyError_allOrders he (abelJetStep^[r] 1) M
  refine ⟨C,hC,h.mono fun u hu => ?_⟩
  have hs : Summable (fun n => ‖abelPolyTerm e (abelJetStep^[r] 1) n u‖) := hu.1
  have hle := norm_tsum_le_tsum_norm (f := fun n => abelPolyTerm e (abelJetStep^[r] 1) n u)
    hs
  exact hle.trans hu.2

end PakPrimes.NthPrime
end
