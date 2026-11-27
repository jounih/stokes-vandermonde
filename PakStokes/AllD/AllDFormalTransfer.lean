module

public import PakStokes.AllD.ExtremeRayProjection
public import PakStokes.PolynomialFlow
public import PakStokes.OrdinaryPoint
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import all PakStokes.AllD.ExtremeRayProjection
import all PakStokes.PolynomialFlow
import all PakStokes.OrdinaryPoint
import all PakStokes.RayAlgebra
import all PakStokes.PhysicalExpression

/-! 100% Unconditional all-`d` formal-to-analytic transfer machinery (`d ≥ 3`):
1. Formal power series `Θ_d(q) = ∑ q^{n^d}`, Waring powers `Θ_d(q)^k`, and
   dilations `Θ_d(q^a) = ∑ q^{a n^d}`, with unit-disk convergence & derivatives.
2. Unconditional `allD_formal_transfer`: any formal ADE over `ℂ(q)` for `Θ_d(q)`
   transfers to a nonzero autonomous polynomial relation in `iteratedDeriv j (regularThetaD d)`
   on `p > 0`.
3. Unconditional `waring_algebraicIndependent_of_base`: for ANY formal power series
   `H ∈ ℂ[[q]]` and ANY `k ≥ 1`, differential transcendence of `H` over `ℂ(q)`
   implies differential transcendence of `H^k` over `ℂ(q)`.
4. Unconditional `QCoeff` chain-rule expansion converting `(d/dq)^j` into a
   `PowerClass 0`-linear combination of `(d/dp)^ℓ` (`0 ≤ ℓ ≤ j`) with exact
   leading Vandermonde asymptotic `(p^d / (d - 1))^j`. -/
public section
namespace CubicTheta.AllD
open Set Filter Complex Metric PowerSeries Flow MvPolynomial
open scoped Topology
noncomputable section

/-! ### 1. Formal Power Series `Θ_d(q)`, Dilations `Θ_d(q^a)`, and Disk Evaluation -/

/-- Formal power series `Θ_d(q^a) = ∑_{n ≥ 0} q^{a n^d} ∈ ℂ[[q]]`. -/
def thetaDDilated (d a : ℕ) : PowerSeries ℂ := by
  classical exact PowerSeries.mk fun k ↦ if ∃ n : ℕ, a * n ^ d = k then 1 else 0

/-- Formal power series `Θ_d(q) = ∑_{n ≥ 0} q^{n^d} ∈ ℂ[[q]]`. -/
def thetaD (d : ℕ) : PowerSeries ℂ := thetaDDilated d 1

/-- The `j`-th ordinary formal derivative of `S ∈ ℂ[[q]]`. -/
def formalJet (S : PowerSeries ℂ) (j : ℕ) : PowerSeries ℂ :=
  (PowerSeries.derivative (R := ℂ))^[j] S

/-- Formal coordinate family `(q, S, S', S'', ...)` in `ℂ[[q]]`. -/
def seriesCoordinates (S : PowerSeries ℂ) : ℕ → PowerSeries ℂ
  | 0 => PowerSeries.X
  | j + 1 => formalJet S j

/-- Formal coordinates for `Θ_d(q)` over `ℂ(q)`. -/
def thetaDCoordinates (d : ℕ) : ℕ → PowerSeries ℂ := seriesCoordinates (thetaD d)

/-- Formal coordinates for the Waring power `Θ_d(q)^k` over `ℂ(q)`. -/
def waringCoordinates (d k : ℕ) : ℕ → PowerSeries ℂ := seriesCoordinates ((thetaD d) ^ k)

/-- Joint formal coordinates `(q, {Θ_d(q^{a_i})^{(j)}})` for same-degree dilations. -/
def dilationCoordinates (d : ℕ) {s : ℕ} (a : Fin s → ℕ+) : Option (Fin s × ℕ) → PowerSeries ℂ
  | none => PowerSeries.X
  | some (i, j) => formalJet (thetaDDilated d (a i).val) j

def psTerm (S : PowerSeries ℂ) (q : ℂ) (n : ℕ) : ℂ := PowerSeries.coeff n S * q ^ n
def psValue (S : PowerSeries ℂ) (q : ℂ) : ℂ := ∑' n, psTerm S q n
def PSAbsAt (S : PowerSeries ℂ) (q : ℂ) : Prop := Summable (fun n ↦ ‖psTerm S q n‖)

private theorem shifted_geom_allD (j : ℕ) {r : ℝ} (hr : 0 < r) (h1 : r < 1) :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ j * r ^ n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one j
    (show ‖r‖ < 1 by simpa [abs_of_pos hr] using h1)
  have h := (hs.comp_injective (show Function.Injective (fun n : ℕ ↦ n + 1) by
    intro i k hh; exact Nat.add_right_cancel hh)).mul_right r⁻¹
  simpa [Function.comp_def, pow_succ, mul_assoc, hr.ne'] using h

private theorem dilated_coeff_bound (d a j n : ℕ) :
    ‖PowerSeries.coeff n (formalJet (thetaDDilated d a) j)‖ ≤ j.factorial * (n + 1 : ℝ) ^ j := by
  rw [formalJet, PowerSeries.coeff_iterate_derivative, thetaDDilated, PowerSeries.coeff_mk]
  split_ifs
  · simpa using (show (↑((n + 1).ascFactorial j) : ℝ) ≤ j.factorial * (n + 1 : ℝ) ^ j by
      exact_mod_cast Nat.ascFactorial_le_factorial_mul_pow (n + 1) j)
  · simp; positivity

private theorem dilated_bound_on (d a j : ℕ) {q : ℂ} {r : ℝ} (h : ‖q‖ ≤ r) (n : ℕ) :
    ‖psTerm (formalJet (thetaDDilated d a) j) q n‖ ≤ j.factorial * ((n + 1 : ℝ) ^ j * r ^ n) := by
  rw [psTerm, norm_mul, norm_pow, ← mul_assoc]
  exact mul_le_mul (dilated_coeff_bound d a j n)
    (pow_le_pow_left₀ (norm_nonneg _) h _) (by positivity) (by positivity)

theorem dilated_jet_abs (d a j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    PSAbsAt (formalJet (thetaDDilated d a) j) q := by
  obtain ⟨r, hr, h1⟩ := exists_between hq
  exact ((shifted_geom_allD j ((norm_nonneg _).trans_lt hr) h1).mul_left _).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (dilated_bound_on d a j hr.le)

theorem dilated_jet_deriv (d a j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt (psValue (formalJet (thetaDDilated d a) j))
      (psValue (formalJet (thetaDDilated d a) (j + 1)) q) q := by
  obtain ⟨r, hr, h1⟩ := exists_between hq
  have rp := (norm_nonneg _).trans_lt hr
  let f (n : ℕ) (z : ℂ) := psTerm (formalJet (thetaDDilated d a) j) z (n + 1)
  let g (n : ℕ) (z : ℂ) := psTerm (formalJet (thetaDDilated d a) (j + 1)) z n
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (f n) (g n z) z := by
    have he : PowerSeries.coeff n (formalJet (thetaDDilated d a) (j + 1)) =
        PowerSeries.coeff (n + 1) (formalJet (thetaDDilated d a) j) * (n + 1) := by
      rw [formalJet, Function.iterate_succ_apply', PowerSeries.coeff_derivative]; rfl
    simpa [f, g, psTerm, he, mul_assoc] using
      ((hasDerivAt_pow (n + 1) z).const_mul (PowerSeries.coeff (n + 1) (formalJet (thetaDDilated d a) j)))
  have hs := hasDerivAt_tsum_of_isPreconnected
    ((shifted_geom_allD (j + 1) rp h1).mul_left (↑(j + 1).factorial))
    (t := ball (0 : ℂ) r) isOpen_ball (convex_ball (0 : ℂ) _).isPreconnected
    (fun n z _ ↦ hd n z) (fun n z hz ↦ dilated_bound_on d a _ (by simpa using (mem_ball.mp hz).le) n)
    (y₀ := q) (by simpa using hr)
    ((dilated_jet_abs d a j hq).of_norm.comp_injective
      (show Function.Injective (fun n : ℕ ↦ n + 1) by intro i k hh; exact Nat.add_right_cancel hh))
    (by simpa using hr)
  have near : psValue (formalJet (thetaDDilated d a) j) =ᶠ[𝓝 q]
      fun z ↦ PowerSeries.coeff 0 (formalJet (thetaDDilated d a) j) + ∑' n, f n z := by
    filter_upwards [isOpen_ball.mem_nhds (show q ∈ ball (0 : ℂ) 1 by simpa using hq)] with z hz
    have h := (dilated_jet_abs d a j (by simpa using hz : ‖z‖ < 1)).of_norm.sum_add_tsum_nat_add 1
    simpa [psValue, f, psTerm] using h.symm
  exact (hs.const_add _).congr_of_eventuallyEq near

theorem dilated_jet_analytic (d a j : ℕ) :
    AnalyticOnNhd ℂ (psValue (formalJet (thetaDDilated d a) j)) (ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro q hq
  exact (dilated_jet_deriv d a j (by simpa using hq)).differentiableAt.differentiableWithinAt

theorem dilated_value_eq {d a : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (q : ℂ) :
    psValue (thetaDDilated d a) q = ∑' n : ℕ, q ^ (a * n ^ d) := by
  classical
  let f (n : ℕ) := a * n ^ d
  have inj : Function.Injective f := by
    intro m n hmn
    exact Nat.pow_left_injective (by omega : d ≠ 0) (Nat.eq_of_mul_eq_mul_left (by omega : 0 < a) hmn)
  have eqn := inj.tsum_eq (f := psTerm (thetaDDilated d a) q) (fun k hk ↦ by
    by_contra no
    change ¬ ∃ n : ℕ, a * n ^ d = k at no
    exact hk (by simp [psTerm, thetaDDilated, no]))
  simpa [psValue, psTerm, thetaDDilated, f, show a ≠ 0 by omega] using eqn.symm

private theorem ps_conv_term (S T : PowerSeries ℂ) (q : ℂ) (n : ℕ) :
    psTerm (S * T) q n = ∑ kl ∈ Finset.antidiagonal n, psTerm S q kl.1 * psTerm T q kl.2 := by
  rw [psTerm, PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro kl h
  rw [← Finset.mem_antidiagonal.mp h, pow_add]; unfold psTerm; ring

private theorem ps_eval_add {S T : PowerSeries ℂ} {q : ℂ} (h : PSAbsAt S q) (k : PSAbsAt T q) :
    PSAbsAt (S + T) q ∧ psValue (S + T) q = psValue S q + psValue T q := by
  have he : psTerm (S + T) q = fun n ↦ psTerm S q n + psTerm T q n := by
    funext n; simp [psTerm, add_mul]
  exact ⟨by unfold PSAbsAt; rw [he]; exact (h.add k).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_add_le ..),
    by simp only [psValue, he, h.of_norm.tsum_add k.of_norm]⟩

private theorem ps_eval_mul {S T : PowerSeries ℂ} {q : ℂ} (h : PSAbsAt S q) (k : PSAbsAt T q) :
    PSAbsAt (S * T) q ∧ psValue (S * T) q = psValue S q * psValue T q := by
  constructor
  · simpa only [PSAbsAt, ps_conv_term] using summable_norm_sum_mul_antidiagonal_of_summable_norm h k
  · simpa only [psValue, ps_conv_term] using (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h k).symm

private theorem ps_eval_const (c q : ℂ) : PSAbsAt (PowerSeries.C c) q ∧ psValue (PowerSeries.C c) q = c := by
  classical
  have he : psTerm (PowerSeries.C c) q = Pi.single 0 c := by
    funext n; by_cases hn : n = 0 <;> simp [psTerm, PowerSeries.coeff_C, hn]
  simp [PSAbsAt, psValue, he, Pi.single_apply, apply_ite (fun z : ℂ ↦ ‖z‖)]
  exact summable_of_ne_finset_zero (s := {0}) (by simp_all)

theorem ps_polynomial_value {ι : Type*} (P : MvPolynomial ι ℂ) {S : ι → PowerSeries ℂ}
    {q : ℂ} (hs : ∀ i, PSAbsAt (S i) q) :
    PSAbsAt (MvPolynomial.aeval S P) q ∧
      psValue (MvPolynomial.aeval S P) q = MvPolynomial.eval (fun i ↦ psValue (S i) q) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa [PowerSeries.algebraMap_apply] using ps_eval_const c q
  | add p t hp ht => simpa [hp.2, ht.2] using ps_eval_add hp.1 ht.1
  | mul_X p i hp => simpa [hp.2] using ps_eval_mul hp.1 (hs i)

theorem ps_nome_abs (q : ℂ) : PSAbsAt PowerSeries.X q ∧ psValue PowerSeries.X q = q := by
  classical
  have he : psTerm PowerSeries.X q = Pi.single 1 q := by
    funext n; by_cases hn : n = 1 <;> simp [psTerm, PowerSeries.coeff_X, hn]
  simp [PSAbsAt, psValue, he, Pi.single_apply, apply_ite (fun z : ℂ ↦ ‖z‖)]
  exact summable_of_ne_finset_zero (s := {1}) (by simp_all)

/-! ### 2. Unconditional All-`d` Formal-to-Autonomous Transfer (`d ≥ 3`) -/

/-- The positive real nome ray `q(p) = exp(-p^{-(d-1)})`. -/
def qRayD (d : ℕ) (p : ℝ) : ℂ := (Real.exp (-(1 / p ^ (d - 1))) : ℝ)
def recipD (p : ℝ) : ℂ := (p : ℂ)⁻¹
def poleD (d : ℕ) (p : ℝ) : ℂ := ((p ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) : ℝ) : ℂ)
def speedD (d : ℕ) (p : ℝ) : ℂ := ((d - 1 : ℕ) : ℂ) * (recipD p) ^ d * qRayD d p

/-- The regularized `d`-th power theta function `Y_d(p)` on the positive action ray `p > 0`. -/
def regularThetaD (d : ℕ) (p : ℝ) : ℂ :=
  (∑' n : ℕ, (Real.exp (-(1 / p ^ (d - 1)) * (n : ℝ) ^ d) : ℂ)) -
    (1 / 2 + (((1 / p ^ (d - 1)) ^ (-(1 : ℝ) / (d : ℝ)) * Real.Gamma (1 + 1 / (d : ℝ)) : ℝ) : ℂ))

theorem qRayD_disk {d : ℕ} {p : ℝ} (hp : 0 < p) : ‖qRayD d p‖ < 1 := by
  rw [qRayD, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr (by positivity)

theorem qRayD_deriv {d : ℕ} (hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (qRayD d) (speedD d p) p := by
  have h := (((hasDerivAt_const p (1 : ℝ)).div (hasDerivAt_pow (d - 1) p) (by positivity)).neg.exp).ofReal_comp
  convert h using 1
  · rfl
  · simp only [speedD, recipD, qRayD, Pi.neg_apply, Pi.div_apply, zero_mul, one_mul, zero_sub,
      neg_div, neg_neg]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hpow : (p : ℂ) ^ (d - 1 - 1) / ((p : ℂ) ^ (d - 1)) ^ 2 = ((p : ℂ)⁻¹) ^ d := by
      rw [inv_pow, div_eq_iff (pow_ne_zero 2 (pow_ne_zero _ hp0))]
      calc (p : ℂ) ^ (d - 1 - 1)
          = (p : ℂ) ^ (d - 1 - 1) * ((p : ℂ) ^ d * ((p : ℂ) ^ d)⁻¹) := by
              rw [mul_inv_cancel₀ (pow_ne_zero d hp0), mul_one]
        _ = ((p : ℂ) ^ d)⁻¹ * ((p : ℂ) ^ (d - 1 - 1) * (p : ℂ) ^ d) := by ring
        _ = ((p : ℂ) ^ d)⁻¹ * ((p : ℂ) ^ (d - 1)) ^ 2 := by
              congr 1; rw [← pow_add, ← pow_mul]; congr 1; omega
    push_cast
    rw [← hpow]
    ring

theorem qRayD_analytic {d : ℕ} {p : ℝ} (hp : 0 < p) : AnalyticAt ℝ (qRayD d) p := by
  apply (Complex.ofRealCLM.analyticAt _).comp
  exact ((analyticAt_const.div (analyticAt_id.pow (d - 1)) (pow_ne_zero _ hp.ne')).neg).rexp

theorem recipD_deriv {p : ℝ} (hp : 0 < p) : HasDerivAt recipD (-recipD p ^ 2) p := by
  simpa [recipD, div_eq_mul_inv] using!
    Complex.ofRealCLM.hasDerivAt.inv (show (p : ℂ) ≠ 0 by exact_mod_cast hp.ne')

theorem poleD_deriv {d : ℕ} (_hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (poleD d) ((((d - 1 : ℕ) : ℂ) / (d : ℂ)) * recipD p * poleD d p) p := by
  have h := (Real.hasDerivAt_rpow_const (x := p) (p := ((d - 1 : ℕ) : ℝ) / (d : ℝ))
    (Or.inl hp.ne')).ofReal_comp
  convert h using 1
  · rfl
  · rw [Real.rpow_sub hp, Real.rpow_one]
    unfold poleD recipD
    push_cast
    ring

theorem poleD_analytic {d : ℕ} {p : ℝ} (hp : 0 < p) : AnalyticAt ℝ (poleD d) p := by
  have he : poleD d =ᶠ[𝓝 p] fun x : ℝ ↦ (Real.exp (Real.log x * (((d - 1 : ℕ) : ℝ) / (d : ℝ))) : ℂ) :=
    (lt_mem_nhds hp).mono fun x hx ↦ by simp [poleD, Real.rpow_def_of_pos hx]
  apply AnalyticAt.congr _ he.symm
  exact (Complex.ofRealCLM.analyticAt _).comp ((analyticAt_log hp).mul analyticAt_const).rexp

def sourceD (d : ℕ) : ℕ → ℝ → ℂ
  | 0 => qRayD d
  | j + 1 => fun p ↦ psValue (formalJet (thetaD d) j) (qRayD d p)

private theorem sourceD_deriv {d : ℕ} (hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) (j : ℕ) :
    HasDerivAt (sourceD d (j + 1)) (speedD d p * sourceD d (j + 2) p) p := by
  simpa [sourceD, thetaD, Function.comp_def, mul_comm] using!
    ((dilated_jet_deriv d 1 j (qRayD_disk hp)).scomp p (qRayD_deriv hd hp))

private theorem sourceD_analytic {d : ℕ} {p : ℝ} (hp : 0 < p) (j : ℕ) :
    AnalyticAt ℝ (sourceD d j) p := by
  cases j with
  | zero => exact qRayD_analytic hp
  | succ j =>
    exact (((dilated_jet_analytic d 1 j) _ (by simpa using qRayD_disk hp)).restrictScalars
      (𝕜 := ℝ)).comp (qRayD_analytic hp)

theorem regularThetaD_at {d : ℕ} (hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) :
    regularThetaD d p =
      sourceD d 1 p - (1 / 2 + ((Real.Gamma (1 + 1 / (d : ℝ)) : ℝ) : ℂ) * poleD d p) := by
  change _ = psValue (thetaDDilated d 1) (qRayD d p) - _
  rw [dilated_value_eq (d := d) (a := 1) (by omega) le_rfl (qRayD d p)]
  unfold regularThetaD
  congr 1
  · apply tsum_congr; intro n
    simp only [one_mul, qRayD, ← Complex.ofReal_pow, ← Real.exp_nat_mul, Nat.cast_pow]
    congr 2; ring
  · have h : (1 / p ^ (d - 1)) ^ (-(1 : ℝ) / (d : ℝ)) = p ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by
      rw [one_div, Real.inv_rpow (pow_nonneg hp.le _), ← Real.rpow_natCast_mul hp.le,
          ← Real.rpow_neg hp.le]
      congr 1; ring
    rw [h]; simp [poleD, mul_comm]

theorem regularThetaD_analytic {d : ℕ} (hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) :
    AnalyticAt ℝ (regularThetaD d) p := by
  apply ((sourceD_analytic hp 1).sub
    (analyticAt_const.add (analyticAt_const.mul (poleD_analytic hp)))).congr
  exact (lt_mem_nhds hp).mono fun _ h ↦ (regularThetaD_at hd h).symm

theorem local_to_tail_allD {d J : ℕ} (hd : 3 ≤ d) (P : MvPolynomial (Fin J) ℂ) {x : ℝ} (hx : 0 < x)
    (h : ∀ᶠ p in 𝓝 x, eval (fun i : Fin J ↦ iteratedDeriv i.val (regularThetaD d) p) P = 0) :
    ∀ᶠ p : ℝ in atTop, eval (fun i : Fin J ↦ iteratedDeriv i.val (regularThetaD d) p) P = 0 := by
  have an (p : ℝ) (hp : 0 < p) (k : ℕ) : AnalyticAt ℝ (iteratedDeriv k (regularThetaD d)) p := by
    induction k with
    | zero => simpa using regularThetaD_analytic hd hp
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have all : AnalyticOnNhd ℝ
      (fun p ↦ eval (fun i : Fin J ↦ iteratedDeriv i.val (regularThetaD d) p) P) (Ioi 0) := by
    clear h; intro p hp
    induction P using MvPolynomial.induction_on with
    | C => simpa using analyticAt_const
    | add a b ha hb => simpa only [map_add] using! ha.add hb
    | mul_X a i ha => simpa only [map_mul, eval_X] using! ha.mul (an p hp i.val)
  exact (eventually_gt_atTop (0 : ℝ)).mono fun p hp ↦
    all.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_Ioi _).isPreconnected hx h hp

/-- **100% Unconditional All-`d` Formal-to-Autonomous Transfer (`d ≥ 3`)**:
any nontrivial formal algebraic differential equation over `ℂ(q)` satisfied by
`Θ_d(q)` yields a nontrivial autonomous polynomial ODE for `regularThetaD d`
eventually on the positive action ray `p > 0`. -/
theorem allD_formal_transfer {d : ℕ} (hd : 3 ≤ d) (Q : MvPolynomial ℕ ℂ) (hQ : Q ≠ 0)
    (zero : MvPolynomial.aeval (thetaDCoordinates d) Q = 0) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ p : ℝ in atTop, eval (fun j : Fin J ↦ iteratedDeriv j.val (regularThetaD d) p) P = 0 := by
  classical
  have relation (p : ℝ) (hp : 0 < p) : eval (fun i ↦ sourceD d i p) Q = 0 := by
    have ha (j : ℕ) : PSAbsAt (thetaDCoordinates d j) (qRayD d p) := by
      cases j with
      | zero => exact (ps_nome_abs _).1
      | succ j => exact dilated_jet_abs d 1 j (qRayD_disk hp)
    have he : (fun i ↦ psValue (thetaDCoordinates d i) (qRayD d p)) = fun i ↦ sourceD d i p := by
      funext i; cases i with
      | zero => exact (ps_nome_abs _).2
      | succ j => rfl
    have hh := (ps_polynomial_value Q ha).2
    rw [zero, he] at hh
    simpa [psValue, psTerm] using hh.symm
  obtain ⟨n, A, x, hx, ordinary, ident⟩ :=
    ordinary_relation (Ioi (0 : ℝ)) ⟨1, zero_lt_one⟩ (sourceD d) ⟨Q, hQ, relation⟩
  let v (i : Fin (n + 1)) := sourceD d i.val
  let g (i : Fin (n + 1)) (p : ℝ) := eval (fun j ↦ v j p) (pderiv i A)
  let top := Fin.last n
  let S := g top
  have hd_v {p : ℝ} (hp : 0 < p) (i : Fin (n + 1)) : DifferentiableAt ℝ (v i) p :=
    (sourceD_analytic hp i.val).differentiableAt
  have chain (B : MvPolynomial (Fin (n + 1)) ℂ) {p : ℝ} (hp : 0 < p) :=
    polynomial_chain B v (fun i ↦ deriv (v i)) p (fun i ↦ (hd_v hp i).hasDerivAt)
  have vanish {p : ℝ} (hp : 0 < p) : ∑ i, g i p * deriv (v i) p = 0 := by
    have near : (fun z ↦ eval (fun i ↦ v i z) A) =ᶠ[𝓝 p] (fun _ ↦ 0) :=
      (lt_mem_nhds hp).mono fun z hz ↦ ident z hz
    exact (chain A hp).deriv.symm.trans (near.deriv_eq.trans (deriv_const ..))
  have hn : n ≠ 0 := by
    rintro rfl
    have he := vanish hx
    change ∑ i : Fin 1, g i x * deriv (v i) x = 0 at he
    rw [Fin.sum_univ_one] at he
    have ds : deriv (v 0) x = speedD d x := (qRayD_deriv hd hx).deriv
    rw [ds] at he
    have hs : speedD d x ≠ 0 := by
      unfold speedD recipD qRayD
      have hr0 : ((d - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      exact mul_ne_zero (mul_ne_zero hr0 (pow_ne_zero d (inv_ne_zero hx0)))
        (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    exact mul_ne_zero ordinary hs he
  let invS (p : ℝ) := (S p)⁻¹
  let u : Fin (n + 1) ⊕ Fin 3 → ℝ → ℂ := Sum.elim v ![recipD, poleD d, invS]
  let G := Generated u x
  have gv (i : Fin (n + 1)) : G (v i) := Generated.coord (u := u) (.inl i)
  have gr : G recipD := Generated.coord (u := u) (.inr 0)
  have gp : G (poleD d) := Generated.coord (u := u) (.inr 1)
  have gw : G invS := Generated.coord (u := u) (.inr 2)
  have gc (c : ℂ) : G (fun _ ↦ c) := Generated.const _
  have gs : G (speedD d) := ((gc ((d - 1 : ℕ) : ℂ)).mul (gr.pow d)).mul (gv 0)
  have gg (i : Fin (n + 1)) : G (g i) := Generated.evalPoly v gv _
  have pos : ∀ᶠ p in 𝓝 x, 0 < p := lt_mem_nhds hx
  have Snz : ∀ᶠ p in 𝓝 x, S p ≠ 0 := (chain (pderiv top A) hx).continuousAt.eventually_ne ordinary
  have low (i : Fin (n + 1)) (hi : i ≠ top) : G (deriv (v i)) := by
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact gs.congr (pos.mono fun p hp ↦ (qRayD_deriv hd hp).deriv.symm)
    | succ k =>
      have lt : k + 2 < n + 1 := by
        have h : k + 1 ≠ n := fun eqn ↦ hi (Fin.ext eqn); omega
      apply (gs.mul (gv ⟨k + 2, lt⟩)).congr
      exact pos.mono fun p hp ↦ (sourceD_deriv hd hp k).deriv.symm
  let lowSum := ∑ i ∈ Finset.univ.erase top, g i * deriv (v i)
  have gl : G lowSum := Generated.finsetSum _ _ (fun i hi ↦ (gg i).mul (low i (Finset.mem_erase.mp hi).1))
  have dv (i : Fin (n + 1)) : G (deriv (v i)) := by
    by_cases hi : i = top
    · subst i
      apply (((gc (-1)).mul gl).mul gw).congr
      filter_upwards [pos, Snz] with p hp nz
      have he := vanish hp
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at he
      change (-1) * lowSum p * (S p)⁻¹ = deriv (v top) p
      have hh : S p * deriv (v top) p + lowSum p = 0 := by simpa [S, lowSum, Finset.sum_apply] using he
      field_simp [nz]; linear_combination -hh
    · exact low i hi
  have dS : G (deriv S) := by
    let D (i : Fin (n + 1)) (p : ℝ) := eval (fun k ↦ v k p) (pderiv i (pderiv top A))
    have gen (i) : G (D i) := Generated.evalPoly v gv _
    apply (Generated.finsetSum Finset.univ _ (fun i _ ↦ (gen i).mul (dv i))).congr
    filter_upwards [pos] with p hp
    simpa [D, Finset.sum_apply] using (chain (pderiv top A) hp).deriv.symm
  have smooth : ∀ᶠ p in 𝓝 x, ∀ i, DifferentiableAt ℝ (u i) p := by
    filter_upwards [pos, Snz] with p hp nz i
    rcases i with i | i
    · exact hd_v hp i
    · fin_cases i
      · exact (recipD_deriv hp).differentiableAt
      · exact (poleD_deriv hd hp).differentiableAt
      · exact (chain (pderiv top A) hp).differentiableAt.inv nz
  have closed (i) : G (deriv (u i)) := by
    rcases i with i | i
    · exact dv i
    · fin_cases i
      · change G (deriv recipD)
        exact ((gc (-1)).mul (gr.pow 2)).congr (pos.mono fun p hp ↦ by simpa using (recipD_deriv hp).deriv.symm)
      · exact (((gc (((d - 1 : ℕ) : ℂ) / (d : ℂ))).mul gr).mul gp).congr
          (pos.mono fun p hp ↦ (poleD_deriv hd hp).deriv.symm)
      · apply (((gc (-1)).mul dS).mul (gw.pow 2)).congr
        filter_upwards [pos, Snz] with p hp nz
        have hi := ((chain (pderiv top A) hp).differentiableAt.hasDerivAt.inv nz).deriv
        change (-1) * deriv S p * ((S p)⁻¹) ^ 2 = deriv invS p
        change deriv invS p = -deriv S p / (S p) ^ 2 at hi
        rw [hi]; simp [inv_pow, div_eq_mul_inv]
  have readout : G (regularThetaD d) := by
    apply ((gv ⟨1, by omega⟩).sub
      ((gc (1 / 2)).add ((gc ((Real.Gamma (1 + 1 / (d : ℝ)) : ℝ) : ℂ)).mul gp))).congr
    exact pos.mono fun p hp ↦ (regularThetaD_at hd hp).symm
  obtain ⟨P, hp, hz⟩ := autonomous_readout u x _ readout smooth closed
  exact ⟨_, P, hp, local_to_tail_allD hd P hx hz⟩

/-! ### 3. 100% Unconditional Waring Algebraic Differential Independence Transfer -/

/-- Formal jet derivation `D` on `ℂ[X_0, X_1, ...]` sending `X_0 ↦ 1`, `X_{j+1} ↦ X_{j+2}`. -/
private def jetDerivMap : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | j + 1 => MvPolynomial.X (j + 2)

private def jetDeriv (A : MvPolynomial ℕ ℂ) : MvPolynomial ℕ ℂ :=
  ∑ i ∈ A.vars, MvPolynomial.pderiv i A * jetDerivMap i

private theorem jetDeriv_add (A B : MvPolynomial ℕ ℂ) :
    jetDeriv (A + B) = jetDeriv A + jetDeriv B := by
  classical
  have hsub (P : MvPolynomial ℕ ℂ) (S : Finset ℕ) (hS : P.vars ⊆ S) :
      jetDeriv P = ∑ i ∈ S, MvPolynomial.pderiv i P * jetDerivMap i := by
    unfold jetDeriv
    apply Finset.sum_subset hS
    intro i _ hi
    have hp0 : MvPolynomial.pderiv i P = 0 := by
      ext m
      rw [MvPolynomial.coeff_pderiv]
      have h0 : P.coeff (m + Finsupp.single i 1) = 0 := by
        by_contra hne
        have hm : m + Finsupp.single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
        have hi' : i ∈ P.vars := (MvPolynomial.mem_vars_iff_mem_support i).mpr
          ⟨m + Finsupp.single i 1, hm, by simp⟩
        exact hi hi'
      simp [h0]
    simp [hp0]
  let S := A.vars ∪ B.vars
  rw [hsub (A + B) S (MvPolynomial.vars_add_subset A B),
      hsub A S Finset.subset_union_left,
      hsub B S Finset.subset_union_right,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [map_add, add_mul]

private theorem jetDeriv_mul (A B : MvPolynomial ℕ ℂ) :
    jetDeriv (A * B) = jetDeriv A * B + A * jetDeriv B := by
  classical
  have hsub (P : MvPolynomial ℕ ℂ) (S : Finset ℕ) (hS : P.vars ⊆ S) :
      jetDeriv P = ∑ i ∈ S, MvPolynomial.pderiv i P * jetDerivMap i := by
    unfold jetDeriv
    apply Finset.sum_subset hS
    intro i _ hi
    have hp0 : MvPolynomial.pderiv i P = 0 := by
      ext m
      rw [MvPolynomial.coeff_pderiv]
      have h0 : P.coeff (m + Finsupp.single i 1) = 0 := by
        by_contra hne
        have hi' : i ∈ P.vars := (MvPolynomial.mem_vars_iff_mem_support i).mpr
          ⟨m + Finsupp.single i 1, MvPolynomial.mem_support_iff.mpr hne, by simp⟩
        exact hi hi'
      simp [h0]
    simp [hp0]
  let S := A.vars ∪ B.vars
  rw [hsub (A * B) S (MvPolynomial.vars_mul A B),
      hsub A S Finset.subset_union_left,
      hsub B S Finset.subset_union_right,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [MvPolynomial.pderiv_mul]
  ring

private theorem jetDeriv_C (c : ℂ) : jetDeriv (MvPolynomial.C c) = 0 := by
  simp [jetDeriv]

private theorem jetDeriv_X (i : ℕ) : jetDeriv (MvPolynomial.X i) = jetDerivMap i := by
  classical
  unfold jetDeriv
  rw [MvPolynomial.vars_X, Finset.sum_singleton, MvPolynomial.pderiv_X_self, one_mul]

private theorem powerSeries_deriv_aeval (H : PowerSeries ℂ) (A : MvPolynomial ℕ ℂ) :
    PowerSeries.derivative (R := ℂ) (MvPolynomial.aeval (seriesCoordinates H) A) =
      MvPolynomial.aeval (seriesCoordinates H) (jetDeriv A) := by
  induction A using MvPolynomial.induction_on with
  | C c =>
    rw [jetDeriv_C, map_zero, MvPolynomial.aeval_C, PowerSeries.algebraMap_apply,
        PowerSeries.derivative_C]
  | add A B hA hB =>
    rw [jetDeriv_add, map_add, map_add, map_add, hA, hB]
  | mul_X A i hA =>
    rw [jetDeriv_mul, jetDeriv_X, map_mul (MvPolynomial.aeval (seriesCoordinates H)),
        Derivation.leibniz, map_add, map_mul, map_mul, smul_eq_mul, smul_eq_mul,
        hA, MvPolynomial.aeval_X]
    have hstep : PowerSeries.derivative (R := ℂ) (seriesCoordinates H i) =
        MvPolynomial.aeval (seriesCoordinates H) (jetDerivMap i) := by
      cases i with
      | zero =>
        simp [seriesCoordinates, jetDerivMap, PowerSeries.derivative_X]
      | succ j =>
        simp only [seriesCoordinates, jetDerivMap, MvPolynomial.aeval_X]
        rw [formalJet, formalJet, Function.iterate_succ_apply']
    rw [hstep]; ring

private def waringSub (k : ℕ) : ℕ → MvPolynomial ℕ ℂ
  | 0 => MvPolynomial.X 0
  | 1 => (MvPolynomial.X 1) ^ k
  | j + 2 => jetDeriv (waringSub k (j + 1))

private theorem aeval_waringSub (H : PowerSeries ℂ) (k : ℕ) (i : ℕ) :
    MvPolynomial.aeval (seriesCoordinates H) (waringSub k i) =
      seriesCoordinates (H ^ k) i := by
  match i with
  | 0 => simp [waringSub, seriesCoordinates]
  | 1 => simp [waringSub, seriesCoordinates, formalJet]
  | j + 2 =>
    rw [waringSub, ← powerSeries_deriv_aeval, aeval_waringSub H k (j + 1)]
    simp only [seriesCoordinates, formalJet, Function.iterate_succ_apply']

private theorem waringSub_pderiv_props (k : ℕ) :
    ∀ i : ℕ,
      (∀ r > i, MvPolynomial.pderiv r (waringSub k i) = 0) ∧
      (i = 0 → MvPolynomial.pderiv 0 (waringSub k 0) = 1) ∧
      (1 ≤ i → MvPolynomial.pderiv i (waringSub k i) =
        MvPolynomial.C (k : ℂ) * (MvPolynomial.X 1) ^ (k - 1)) := by
  intro i
  induction i with
  | zero =>
    refine ⟨fun r hr ↦ ?_, fun _ ↦ MvPolynomial.pderiv_X_self 0, fun h ↦ by omega⟩
    rw [waringSub, MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by omega)]
  | succ i ih =>
    cases i with
    | zero =>
      refine ⟨fun r hr ↦ ?_, fun h ↦ by omega, fun _ ↦ ?_⟩
      · rw [waringSub, Derivation.leibniz_pow, MvPolynomial.pderiv_X,
            Pi.single_eq_of_ne (by omega : 1 ≠ r), smul_zero, smul_zero]
      · rw [waringSub, Derivation.leibniz_pow, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one]
        cases k with
        | zero => simp
        | succ k => simp [Nat.cast_add, mul_comm]
    | succ j =>
      obtain ⟨hvan, _, htop⟩ := ih
      have htop_j := htop (by omega)
      have hvars_le : ∀ v ∈ (waringSub k (j + 1)).vars, v ≤ j + 1 := by
        intro v hv
        by_contra hgt
        exact partial_ne hv (hvan v (by omega))
      have hexpand : waringSub k (j + 2) =
          (∑ u ∈ (waringSub k (j + 1)).vars.erase (j + 1),
            MvPolynomial.pderiv u (waringSub k (j + 1)) * jetDerivMap u) +
          (MvPolynomial.C (k : ℂ) * (MvPolynomial.X 1) ^ (k - 1)) * MvPolynomial.X (j + 2) := by
        classical
        change jetDeriv (waringSub k (j + 1)) = _
        unfold jetDeriv
        by_cases hm : j + 1 ∈ (waringSub k (j + 1)).vars
        · rw [← Finset.add_sum_erase _ _ hm, htop_j, add_comm]
          rfl
        · have h0 : MvPolynomial.pderiv (j + 1) (waringSub k (j + 1)) = 0 := by
            ext m; rw [MvPolynomial.coeff_pderiv]
            have hc0 : (waringSub k (j + 1)).coeff (m + Finsupp.single (j + 1) 1) = 0 := by
              by_contra hne
              exact hm ((MvPolynomial.mem_vars_iff_mem_support _).mpr
                ⟨_, MvPolynomial.mem_support_iff.mpr hne, by simp⟩)
            simp [hc0]
          rw [htop_j] at h0
          rw [Finset.erase_eq_of_notMem hm, h0, zero_mul, add_zero]
      have hterm_van (r : ℕ) (hr : j + 2 ≤ r) :
          MvPolynomial.pderiv r
            (∑ u ∈ (waringSub k (j + 1)).vars.erase (j + 1),
              MvPolynomial.pderiv u (waringSub k (j + 1)) * jetDerivMap u) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro u hu
        have hu_mem : u ∈ (waringSub k (j + 1)).vars := Finset.mem_of_mem_erase hu
        have hu_ne : u ≠ j + 1 := Finset.ne_of_mem_erase hu
        have hu_lt : u < j + 1 := lt_of_le_of_ne (hvars_le u hu_mem) hu_ne
        rw [MvPolynomial.pderiv_mul]
        have hp1 : MvPolynomial.pderiv r (MvPolynomial.pderiv u (waringSub k (j + 1))) = 0 := by
          rw [MvPolynomial.pderiv_comm, hvan r (by omega), map_zero]
        have hp2 : MvPolynomial.pderiv r (jetDerivMap u) = 0 := by
          cases u with
          | zero => simp [jetDerivMap]
          | succ u' =>
            simp only [jetDerivMap, MvPolynomial.pderiv_X]
            rw [Pi.single_eq_of_ne (by omega : u' + 2 ≠ r)]
        simp [hp1, hp2]
      have hcoef_van (r : ℕ) (hr : j + 2 ≤ r) :
          MvPolynomial.pderiv r (MvPolynomial.C (k : ℂ) * (MvPolynomial.X 1) ^ (k - 1)) = 0 := by
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, Derivation.leibniz_pow,
            MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by omega : 1 ≠ r)]
        simp
      refine ⟨fun r hr ↦ ?_, fun h ↦ by omega, fun _ ↦ ?_⟩
      · rw [hexpand, map_add, hterm_van r (by omega), zero_add, MvPolynomial.pderiv_mul,
            hcoef_van r (by omega), MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by omega : j + 2 ≠ r)]
        simp
      · rw [hexpand, map_add, hterm_van (j + 2) le_rfl, zero_add, MvPolynomial.pderiv_mul,
            hcoef_van (j + 2) le_rfl, MvPolynomial.pderiv_X_self]
        simp

private theorem pderiv_bind₁_chain (P : MvPolynomial ℕ ℂ) (f : ℕ → MvPolynomial ℕ ℂ) (r : ℕ) :
    MvPolynomial.pderiv r (MvPolynomial.bind₁ f P) =
      ∑ i ∈ P.vars, MvPolynomial.bind₁ f (MvPolynomial.pderiv i P) * MvPolynomial.pderiv r (f i) := by
  classical
  have hsub (Q : MvPolynomial ℕ ℂ) (S : Finset ℕ) (hS : Q.vars ⊆ S) :
      ∑ i ∈ Q.vars, MvPolynomial.bind₁ f (MvPolynomial.pderiv i Q) * MvPolynomial.pderiv r (f i) =
      ∑ i ∈ S, MvPolynomial.bind₁ f (MvPolynomial.pderiv i Q) * MvPolynomial.pderiv r (f i) := by
    apply Finset.sum_subset hS
    intro i _ hi
    have hp0 : MvPolynomial.pderiv i Q = 0 := by
      ext m; rw [MvPolynomial.coeff_pderiv]
      have hc0 : Q.coeff (m + Finsupp.single i 1) = 0 := by
        by_contra hne
        exact hi ((MvPolynomial.mem_vars_iff_mem_support i).mpr
          ⟨_, MvPolynomial.mem_support_iff.mpr hne, by simp⟩)
      simp [hc0]
    simp [hp0]
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add A B hA hB =>
    let S := A.vars ∪ B.vars
    rw [map_add, map_add, hA, hB, hsub (A + B) S (MvPolynomial.vars_add_subset A B),
        hsub A S Finset.subset_union_left, hsub B S Finset.subset_union_right,
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [map_add, map_add, add_mul]
  | mul_X A j hA =>
    let S := insert j A.vars
    have hvars_sub : (A * MvPolynomial.X j).vars ⊆ S := by
      refine (MvPolynomial.vars_mul A (MvPolynomial.X j)).trans ?_
      rw [MvPolynomial.vars_X, Finset.union_comm]
      exact Finset.Subset.rfl
    rw [map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.pderiv_mul, hA,
        hsub (A * MvPolynomial.X j) S hvars_sub, hsub A S (Finset.subset_insert j A.vars)]
    rw [Finset.sum_mul]
    have hX : MvPolynomial.bind₁ f A * MvPolynomial.pderiv r (f j) =
        ∑ i ∈ S, MvPolynomial.bind₁ f (A * MvPolynomial.pderiv i (MvPolynomial.X j)) *
          MvPolynomial.pderiv r (f i) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        rw [MvPolynomial.pderiv_X, Pi.single_eq_of_ne hij.symm, mul_zero, map_zero, zero_mul]
      · intro hnot; exact (hnot (Finset.mem_insert_self j A.vars)).elim
    rw [hX, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.bind₁_X_right]
    ring

private theorem bind₁_waringSub_injective {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (MvPolynomial.bind₁ (waringSub k)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro Q
  induction Q using (measure fun Q : MvPolynomial ℕ ℂ ↦ Q.totalDegree).wf.induction with
  | h Q ih =>
    intro hQ
    by_contra hne
    by_cases hv : Q.vars.Nonempty
    · let m := Q.vars.max' hv
      have hm : m ∈ Q.vars := Finset.max'_mem Q.vars hv
      have hderiv := congrArg (MvPolynomial.pderiv m) hQ
      rw [map_zero, pderiv_bind₁_chain] at hderiv
      have honly : ∀ i ∈ Q.vars, i ≠ m →
          MvPolynomial.bind₁ (waringSub k) (MvPolynomial.pderiv i Q) *
            MvPolynomial.pderiv m (waringSub k i) = 0 := by
        intro i hi him
        have hlt : i < m := lt_of_le_of_ne (Finset.le_max' Q.vars i hi) him
        rw [(waringSub_pderiv_props k i).1 m hlt, mul_zero]
      rw [Finset.sum_eq_single m honly (fun hnot ↦ (hnot hm).elim)] at hderiv
      have htop_nz : MvPolynomial.pderiv m (waringSub k m) ≠ 0 := by
        cases m with
        | zero =>
          rw [(waringSub_pderiv_props k 0).2.1 rfl]
          exact one_ne_zero
        | succ m' =>
          rw [(waringSub_pderiv_props k (m' + 1)).2.2 (by omega)]
          have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
          exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hk0) (pow_ne_zero _ (MvPolynomial.X_ne_zero 1))
      have hbind0 : MvPolynomial.bind₁ (waringSub k) (MvPolynomial.pderiv m Q) = 0 :=
        (mul_eq_zero.mp hderiv).resolve_right htop_nz
      have hdeg_pos : 0 < Q.totalDegree := by
        by_contra h0
        have hc := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (not_lt.mp h0))
        rw [hc, vars_C] at hm
        exact Finset.notMem_empty m hm
      have hp0 : MvPolynomial.pderiv m Q = 0 :=
        ih (MvPolynomial.pderiv m Q) (CubicTheta.lower_degree m Q hdeg_pos) hbind0
      exact partial_ne hm hp0
    · rw [Finset.not_nonempty_iff_eq_empty] at hv
      have hc := MvPolynomial.vars_eq_empty_iff_eq_C.mp hv
      rw [hc, MvPolynomial.bind₁_C_right] at hQ
      have hc0 : Q.coeff 0 = 0 := MvPolynomial.C_injective _ _ (hQ.trans (map_zero _).symm)
      exact hne (hc.trans (by rw [hc0, MvPolynomial.C_0]))

/-- **100% Unconditional Waring Algebraic Transfer**: for ANY formal power series
`H ∈ ℂ[[q]]` and ANY exponent `k ≥ 1`, differential transcendence of `H` over `ℂ(q)`
implies differential transcendence of `H^k` over `ℂ(q)`. -/
theorem waring_algebraicIndependent_of_base (H : PowerSeries ℂ) {k : ℕ} (hk : 1 ≤ k)
    (hH : AlgebraicIndependent ℂ (seriesCoordinates H)) :
    AlgebraicIndependent ℂ (seriesCoordinates (H ^ k)) := by
  rw [algebraicIndependent_iff] at hH ⊢
  intro Q hQ
  have hcomp : MvPolynomial.aeval (seriesCoordinates H) (MvPolynomial.bind₁ (waringSub k) Q) = 0 := by
    rw [MvPolynomial.aeval_bind₁]
    have hfun : (fun i ↦ MvPolynomial.aeval (seriesCoordinates H) (waringSub k i)) =
        seriesCoordinates (H ^ k) := funext (aeval_waringSub H k)
    rw [hfun]
    exact hQ
  exact bind₁_waringSub_injective hk ((hH _ hcomp).trans (map_zero _).symm)

/-! ### 4. `QCoeff` Chain-Rule Expansion (`(d/dq)^j` in terms of `(d/dp)^ℓ`) -/

/-- Inverse speed `1 / (dq/dp) = (d - 1)⁻¹ p^d exp(1 / p^{d-1})`. -/
def invSpeedD (d : ℕ) (p : ℝ) : ℂ :=
  (((d - 1 : ℕ) : ℂ)⁻¹) * ((p : ℂ) ^ d) * (Real.exp (1 / p ^ (d - 1)) : ℝ)

theorem invSpeedD_mul_speedD {d : ℕ} (hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) :
    invSpeedD d p * speedD d p = 1 := by
  unfold invSpeedD speedD recipD qRayD
  have hr0 : ((d - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hexp : ((Real.exp (1 / p ^ (d - 1)) : ℝ) : ℂ) *
      ((Real.exp (-(1 / p ^ (d - 1))) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  calc (((d - 1 : ℕ) : ℂ)⁻¹ * (p : ℂ) ^ d * ↑(Real.exp (1 / p ^ (d - 1)))) *
        (((d - 1 : ℕ) : ℂ) * (p : ℂ)⁻¹ ^ d * ↑(Real.exp (-(1 / p ^ (d - 1)))))
      = ((((d - 1 : ℕ) : ℂ)⁻¹ * ((d - 1 : ℕ) : ℂ)) * ((p : ℂ) ^ d * ((p : ℂ) ^ d)⁻¹)) *
          (↑(Real.exp (1 / p ^ (d - 1))) * ↑(Real.exp (-(1 / p ^ (d - 1))))) := by
            rw [inv_pow]; ring
    _ = 1 := by
            rw [inv_mul_cancel₀ hr0, mul_inv_cancel₀ (pow_ne_zero d hp0), hexp]; ring

/-- The `d/dq` differential operator pulled back to the positive action ray `p > 0`. -/
def qDeriv (d : ℕ) (f : ℝ → ℂ) (p : ℝ) : ℂ := invSpeedD d p * deriv f p

/-- Iterated `d/dq` operator on functions of `p > 0`. -/
def iterQDeriv (d : ℕ) : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, f => f
  | j + 1, f => qDeriv d (iterQDeriv d j f)

theorem dilated_jet_eq_iterQDeriv {d a : ℕ} (hd : 3 ≤ d) (j : ℕ) {p : ℝ} (hp : 0 < p) :
    psValue (formalJet (thetaDDilated d a) j) (qRayD d p) =
      iterQDeriv d j (fun x ↦ psValue (thetaDDilated d a) (qRayD d x)) p := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    change psValue (formalJet (thetaDDilated d a) (j + 1)) (qRayD d p) =
      invSpeedD d p * deriv (iterQDeriv d j (fun x ↦ psValue (thetaDDilated d a) (qRayD d x))) p
    have hnear : iterQDeriv d j (fun x ↦ psValue (thetaDDilated d a) (qRayD d x)) =ᶠ[𝓝 p]
        fun x ↦ psValue (formalJet (thetaDDilated d a) j) (qRayD d x) :=
      (lt_mem_nhds hp).mono fun x hx ↦ (ih hx).symm
    have hcomp : HasDerivAt (fun x ↦ psValue (formalJet (thetaDDilated d a) j) (qRayD d x))
        (speedD d p * psValue (formalJet (thetaDDilated d a) (j + 1)) (qRayD d p)) p := by
      simpa [Function.comp_def, mul_comm] using!
        ((dilated_jet_deriv d a j (qRayD_disk hp)).scomp p (qRayD_deriv hd hp))
    rw [hnear.deriv_eq, hcomp.deriv, ← mul_assoc, invSpeedD_mul_speedD hd hp, one_mul]

/-- Closed inductive class of `q`-to-`p` chain-rule coefficients of degree `≤ deg`:
finite sums of `c * p^k * exp(m / p^{d-1})` (`k ≤ deg`, `m : ℕ`). -/
inductive QCoeff (d : ℕ) : ℤ → (ℝ → ℂ) → Prop
  | mono (c : ℂ) (k deg : ℤ) (m : ℕ) (hle : k ≤ deg) :
      QCoeff d deg (fun p : ℝ ↦ c * ((p ^ (k : ℝ) : ℝ) : ℂ) * (Real.exp ((m : ℝ) / p ^ (d - 1)) : ℝ))
  | add {deg : ℤ} {f g : ℝ → ℂ} (hf : QCoeff d deg f) (hg : QCoeff d deg g) :
      QCoeff d deg (fun p ↦ f p + g p)
  | congr {deg : ℤ} {f g : ℝ → ℂ} (hf : QCoeff d deg f) (he : ∀ p > 0, f p = g p) :
      QCoeff d deg g

namespace QCoeff

theorem zero (d : ℕ) (deg : ℤ) : QCoeff d deg (fun _ ↦ 0) :=
  (mono 0 deg deg 0 le_rfl).congr (fun _ _ ↦ by simp)

theorem raise {d : ℕ} {deg₁ deg₂ : ℤ} {f : ℝ → ℂ} (h : QCoeff d deg₁ f) (hle : deg₁ ≤ deg₂) :
    QCoeff d deg₂ f := by
  induction h with
  | mono c k _ m hk => exact mono c k deg₂ m (hk.trans hle)
  | add _ _ ih1 ih2 => exact add (ih1 hle) (ih2 hle)
  | congr _ he ih => exact congr (ih hle) he

theorem mul {d : ℕ} {deg₁ deg₂ : ℤ} {f g : ℝ → ℂ}
    (hf : QCoeff d deg₁ f) (hg : QCoeff d deg₂ g) :
    QCoeff d (deg₁ + deg₂) (fun p ↦ f p * g p) := by
  induction hf generalizing deg₂ g with
  | mono c₁ k₁ d₁ m₁ hk₁ =>
    induction hg with
    | mono c₂ k₂ d₂ m₂ hk₂ =>
      refine (mono (c₁ * c₂) (k₁ + k₂) (d₁ + d₂) (m₁ + m₂) (add_le_add hk₁ hk₂)).congr ?_
      intro p hp
      push_cast
      rw [Real.rpow_add hp, add_div, Complex.exp_add]
      push_cast; ring
    | add _ _ ih1 ih2 =>
      exact (add ih1 ih2).congr (fun p _ ↦ by ring)
    | congr _ he ih =>
      exact ih.congr (fun p hp ↦ by rw [he p hp])
  | add _ _ ih1 ih2 =>
    exact (add (ih1 hg) (ih2 hg)).congr (fun p _ ↦ by ring)
  | congr _ he ih =>
    exact (ih hg).congr (fun p hp ↦ by rw [he p hp])

theorem invSpeed {d : ℕ} : QCoeff d (d : ℤ) (invSpeedD d) := by
  refine (mono (((d - 1 : ℕ) : ℂ)⁻¹) (d : ℤ) (d : ℤ) 1 le_rfl).congr ?_
  intro p hp
  unfold invSpeedD
  simp [Real.rpow_natCast]

theorem smooth {d : ℕ} {deg : ℤ} {f : ℝ → ℂ} (hf : QCoeff d deg f)
    {p : ℝ} (hp : 0 < p) : DifferentiableAt ℝ f p := by
  induction hf with
  | mono c k _ m _ =>
    have h1 : DifferentiableAt ℝ (fun x : ℝ ↦ ((x ^ (k : ℝ) : ℝ) : ℂ)) p :=
      ((Real.hasDerivAt_rpow_const (x := p) (p := (k : ℝ)) (Or.inl hp.ne')).ofReal_comp).differentiableAt
    have h2 : DifferentiableAt ℝ (fun x : ℝ ↦ (Real.exp ((m : ℝ) / x ^ (d - 1)) : ℂ)) p := by
      have hd_exp := (((hasDerivAt_const p (m : ℝ)).div (hasDerivAt_pow (d - 1) p)
        (by positivity)).exp).ofReal_comp
      exact hd_exp.differentiableAt
    exact (h1.const_mul c).mul h2
  | add _ _ ih1 ih2 => exact ih1.add ih2
  | congr _ he ih =>
    exact ih.congr_of_eventuallyEq ((lt_mem_nhds hp).mono fun x hx ↦ (he x hx).symm)

theorem deriv_drop {d : ℕ} (hd : 3 ≤ d) {deg : ℤ} {f : ℝ → ℂ} (hf : QCoeff d deg f) :
    QCoeff d (deg - 1) (deriv f) := by
  induction hf with
  | mono c k d₀ m hk =>
    have h1 : QCoeff d (d₀ - 1)
        (fun p : ℝ ↦ (c * (k : ℂ)) * ((p ^ ((k - 1 : ℤ) : ℝ) : ℝ) : ℂ) *
          (Real.exp ((m : ℝ) / p ^ (d - 1)) : ℝ)) :=
      mono _ (k - 1) (d₀ - 1) m (by omega)
    have h2 : QCoeff d (d₀ - 1)
        (fun p : ℝ ↦ (-c * (m : ℂ) * ((d - 1 : ℕ) : ℂ)) * ((p ^ ((k - d : ℤ) : ℝ) : ℝ) : ℂ) *
          (Real.exp ((m : ℝ) / p ^ (d - 1)) : ℝ)) :=
      mono _ (k - d) (d₀ - 1) m (by omega)
    refine (h1.add h2).congr ?_
    intro p hp
    have hd1 : HasDerivAt (fun x : ℝ ↦ c * ((x ^ (k : ℝ) : ℝ) : ℂ))
        (c * ((k : ℝ) * p ^ ((k : ℝ) - 1) : ℝ)) p :=
      ((Real.hasDerivAt_rpow_const (x := p) (p := (k : ℝ)) (Or.inl hp.ne')).ofReal_comp).const_mul c
    have hd2 : HasDerivAt (fun x : ℝ ↦ (Real.exp ((m : ℝ) / x ^ (d - 1)) : ℂ))
        ((Real.exp ((m : ℝ) / p ^ (d - 1)) * (-(m : ℝ) * ((d - 1 : ℕ) : ℝ) * p ^ (-(d : ℝ))) : ℝ) : ℂ) p := by
      have hdiv := ((hasDerivAt_const p (m : ℝ)).div (hasDerivAt_pow (d - 1) p) (by positivity)).exp.ofReal_comp
      convert hdiv using 1
      congr 1
      simp only [zero_mul, zero_sub, Pi.div_apply]
      have hp0 : p ≠ 0 := hp.ne'
      have hpow_eq : p ^ (d - 1 - 1) / (p ^ (d - 1)) ^ 2 = p ^ (-(d : ℝ)) := by
        rw [Real.rpow_neg hp.le, Real.rpow_natCast, div_eq_iff (pow_ne_zero 2 (pow_ne_zero _ hp0))]
        calc p ^ (d - 1 - 1)
            = p ^ (d - 1 - 1) * (p ^ d * (p ^ d)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero d hp0), mul_one]
          _ = (p ^ d)⁻¹ * (p ^ (d - 1 - 1) * p ^ d) := by ring
          _ = (p ^ d)⁻¹ * (p ^ (d - 1)) ^ 2 := by congr 1; rw [← pow_add, ← pow_mul]; congr 1; omega
      rw [← hpow_eq]; ring
    have hprod : HasDerivAt (fun x : ℝ ↦ c * ((x ^ (k : ℝ) : ℝ) : ℂ) * (Real.exp ((m : ℝ) / x ^ (d - 1)) : ℂ))
        ((c * ((k : ℝ) * p ^ ((k : ℝ) - 1) : ℝ)) * (Real.exp ((m : ℝ) / p ^ (d - 1)) : ℂ) +
          (c * ((p ^ (k : ℝ) : ℝ) : ℂ)) *
            ((Real.exp ((m : ℝ) / p ^ (d - 1)) * (-(m : ℝ) * ((d - 1 : ℕ) : ℝ) * p ^ (-(d : ℝ))) : ℝ) : ℂ)) p :=
      hd1.mul hd2
    rw [hprod.deriv]
    have hsub1 : ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by push_cast; ring
    have hsubd : p ^ ((k - d : ℤ) : ℝ) = p ^ (k : ℝ) * p ^ (-(d : ℝ)) := by
      rw [show ((k - d : ℤ) : ℝ) = (k : ℝ) + -(d : ℝ) by push_cast; ring, Real.rpow_add hp]
    rw [hsub1, hsubd]
    push_cast; ring
  | add h₁ h₂ ih1 ih2 =>
    refine (ih1.add ih2).congr ?_
    intro p hp
    exact ((h₁.smooth hp).hasDerivAt.add (h₂.smooth hp).hasDerivAt).deriv.symm
  | congr h₁ he ih =>
    refine ih.congr ?_
    intro p hp
    have hnear : _ =ᶠ[𝓝 p] _ := (lt_mem_nhds hp).mono fun x hx ↦ he x hx
    exact hnear.deriv_eq

theorem powerClass_zero {d : ℕ} (hd : 3 ≤ d) {deg : ℤ} {f : ℝ → ℂ} (hf : QCoeff d deg f) :
    PowerClass 0 f := by
  induction hf with
  | mono c k _ m _ =>
    have h1 : PowerClass 0 (fun p : ℝ ↦ ((p ^ (k : ℝ) : ℝ) : ℂ)) :=
      (powerClass_rpow (k : ℝ)).reindex k (by simp)
    have h2 : PowerClass 0 (fun p : ℝ ↦ (Real.exp ((m : ℝ) / p ^ (d - 1)) : ℂ)) :=
      exp_inv_pow_powerClass (r := d - 1) (by omega) (m : ℝ)
    simpa [mul_assoc] using ((PowerClass.const c).mul h1).mul h2
  | add _ _ ih1 ih2 => exact ih1.add ih2
  | congr _ he ih => exact ih.congr ((eventually_gt_atTop (0 : ℝ)).mono he)

theorem poly_bound {d : ℕ} {deg : ℤ} {f : ℝ → ℂ} (hf : QCoeff d deg f) :
    ∃ (B : ℝ) (L : ℕ), 0 ≤ B ∧ ∀ᶠ p : ℝ in atTop, ‖f p‖ ≤ B * p ^ L := by
  induction hf with
  | mono c k _ m _ =>
    refine ⟨‖c‖ * Real.exp (m : ℝ), k.toNat, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with p hp
    have hp_pos : 0 < p := zero_lt_one.trans_le hp
    have hexp : Real.exp ((m : ℝ) / p ^ (d - 1)) ≤ Real.exp (m : ℝ) := by
      apply Real.exp_le_exp.mpr
      have h1 : (1 : ℝ) ≤ p ^ (d - 1) := one_le_pow₀ hp
      exact div_le_self (Nat.cast_nonneg m) h1
    have hpow : p ^ (k : ℝ) ≤ p ^ (k.toNat : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hp (by exact_mod_cast Int.self_le_toNat k)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hp_pos _), abs_of_pos (Real.exp_pos _)]
    calc ‖c‖ * p ^ (k : ℝ) * Real.exp ((m : ℝ) / p ^ (d - 1))
        ≤ ‖c‖ * p ^ k.toNat * Real.exp (m : ℝ) := by gcongr
      _ = ‖c‖ * Real.exp (m : ℝ) * p ^ k.toNat := by ring
  | add _ _ ih1 ih2 =>
    obtain ⟨B₁, L₁, hB₁, hb₁⟩ := ih1
    obtain ⟨B₂, L₂, hB₂, hb₂⟩ := ih2
    refine ⟨B₁ + B₂, max L₁ L₂, add_nonneg hB₁ hB₂, ?_⟩
    filter_upwards [hb₁, hb₂, eventually_ge_atTop (1 : ℝ)] with p h1 h2 hp
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le ..
      _ ≤ B₁ * p ^ L₁ + B₂ * p ^ L₂ := add_le_add h1 h2
      _ ≤ B₁ * p ^ max L₁ L₂ + B₂ * p ^ max L₁ L₂ :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (le_max_left ..)) hB₁)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (le_max_right ..)) hB₂)
      _ = (B₁ + B₂) * p ^ max L₁ L₂ := by ring
  | congr _ he ih =>
    obtain ⟨B, L, hB, hb⟩ := ih
    refine ⟨B, L, hB, ?_⟩
    filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with p hp hpos
    rwa [← he p hpos]

theorem tendsto_zero_of_lt {d : ℕ} (hd : 3 ≤ d) {deg M : ℤ} {f : ℝ → ℂ}
    (hf : QCoeff d deg f) (hlt : deg < M) :
    Tendsto (fun p : ℝ ↦ ((p ^ (-(M : ℝ)) : ℝ) : ℂ) * f p) atTop (𝓝 0) := by
  induction hf with
  | mono c k d₀ m hk =>
    have hlt_k : (k : ℝ) - (M : ℝ) < 0 := by
      have : k < M := lt_of_le_of_lt hk hlt
      have hcast : (k : ℝ) < (M : ℝ) := by exact_mod_cast this
      linarith
    have hpow : Tendsto (fun p : ℝ ↦ ((p ^ ((k : ℝ) - (M : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp
        (by simpa [neg_sub] using tendsto_rpow_neg_atTop (show 0 < (M : ℝ) - (k : ℝ) by linarith))
    have hexp : Tendsto (fun p : ℝ ↦ (Real.exp ((m : ℝ) / p ^ (d - 1)) : ℂ)) atTop (𝓝 1) := by
      have hdiv : Tendsto (fun p : ℝ ↦ (m : ℝ) / p ^ (d - 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega : d - 1 ≠ 0))
      have hexpR : Tendsto (fun p : ℝ ↦ Real.exp ((m : ℝ) / p ^ (d - 1))) atTop (𝓝 1) :=
        Real.exp_zero ▸ (Real.continuous_exp.tendsto 0).comp hdiv
      simpa only [Function.comp_def, Complex.ofReal_one] using
        (Complex.continuous_ofReal.tendsto 1).comp hexpR
    have hprod := ((hpow.const_mul c).mul hexp)
    rw [mul_zero, zero_mul] at hprod
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
    rw [show (k : ℝ) - (M : ℝ) = -(M : ℝ) + (k : ℝ) by ring, Real.rpow_add hp, Complex.ofReal_mul]
    ring
  | add _ _ ih1 ih2 =>
    have h := (ih1 hlt).add (ih2 hlt)
    rw [add_zero] at h
    exact h.congr (fun p ↦ by ring)
  | congr _ he ih =>
    apply (ih hlt).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
    rw [he p hp]

end QCoeff

/-- Explicit recursive coefficients expanding `iterQDeriv d j f` as
`∑ ℓ ∈ Finset.range (j + 1), qPolyCoeff d j ℓ p * iteratedDeriv ℓ f p`. -/
def qPolyCoeff (d : ℕ) : ℕ → ℕ → ℝ → ℂ
  | 0, 0, _ => 1
  | 0, _ + 1, _ => 0
  | j + 1, ℓ, p =>
      invSpeedD d p * deriv (qPolyCoeff d j ℓ) p +
        if ℓ = 0 then 0 else invSpeedD d p * qPolyCoeff d j (ℓ - 1) p

theorem qPolyCoeff_gt {d : ℕ} : ∀ j ℓ, j < ℓ → ∀ p, qPolyCoeff d j ℓ p = 0 := by
  intro j
  induction j with
  | zero =>
    intro ℓ hℓ p
    cases ℓ with
    | zero => omega
    | succ ℓ' => rfl
  | succ j ih =>
    intro ℓ hℓ p
    cases ℓ with
    | zero => omega
    | succ ℓ' =>
      have h1 : qPolyCoeff d j (ℓ' + 1) = fun _ ↦ 0 := funext (ih (ℓ' + 1) (by omega))
      have h2 : qPolyCoeff d j ℓ' p = 0 := ih ℓ' (by omega) p
      simp [qPolyCoeff, h1, h2]

theorem qPolyCoeff_diag {d : ℕ} : ∀ j p, qPolyCoeff d j j p = (invSpeedD d p) ^ j := by
  intro j
  induction j with
  | zero => intro p; simp [qPolyCoeff]
  | succ j ih =>
    intro p
    have h0 : qPolyCoeff d j (j + 1) = fun _ ↦ 0 := funext (qPolyCoeff_gt j (j + 1) (by omega))
    simp [qPolyCoeff, h0, ih p, pow_succ']

theorem qPolyCoeff_QCoeff {d : ℕ} (hd : 3 ≤ d) :
    ∀ (j ℓ : ℕ), ℓ ≤ j → QCoeff d (((d : ℤ) * (j : ℤ)) - ((j - ℓ : ℕ) : ℤ)) (qPolyCoeff d j ℓ) := by
  intro j
  induction j with
  | zero =>
    intro ℓ hℓ
    have h0 : ℓ = 0 := by omega
    subst h0
    refine (QCoeff.mono 1 0 0 0 le_rfl).congr ?_
    intro p hp; simp [qPolyCoeff]
  | succ j ih =>
    intro ℓ hℓ
    have hterm1 : QCoeff d (((d : ℤ) * ((j + 1 : ℕ) : ℤ)) - (((j + 1) - ℓ : ℕ) : ℤ))
        (fun p ↦ invSpeedD d p * deriv (qPolyCoeff d j ℓ) p) := by
      by_cases hlt : ℓ ≤ j
      · have hder := (ih ℓ hlt).deriv_drop hd
        have hmul := QCoeff.invSpeed.mul hder
        refine hmul.raise ?_
        have hsub1 : ((j - ℓ : ℕ) : ℤ) = (j : ℤ) - (ℓ : ℤ) := by omega
        have hsub2 : ((j + 1 - ℓ : ℕ) : ℤ) = (j : ℤ) + 1 - (ℓ : ℤ) := by omega
        rw [hsub1, hsub2]; push_cast; linarith
      · have hgt : j < ℓ := by omega
        have hz : qPolyCoeff d j ℓ = fun _ ↦ 0 := funext (qPolyCoeff_gt j ℓ hgt)
        exact (QCoeff.zero d _).congr (fun p _ ↦ by simp [hz])
    have hterm2 : QCoeff d (((d : ℤ) * ((j + 1 : ℕ) : ℤ)) - (((j + 1) - ℓ : ℕ) : ℤ))
        (fun p ↦ if ℓ = 0 then 0 else invSpeedD d p * qPolyCoeff d j (ℓ - 1) p) := by
      cases ℓ with
      | zero => exact (QCoeff.zero d _).congr (fun _ _ ↦ by simp)
      | succ ℓ' =>
        have hmul := QCoeff.invSpeed.mul (ih ℓ' (by omega))
        refine (hmul.raise ?_).congr (fun p _ ↦ by simp)
        have hsub1 : ((j - ℓ' : ℕ) : ℤ) = (j : ℤ) - (ℓ' : ℤ) := by omega
        have hsub2 : ((j + 1 - (ℓ' + 1) : ℕ) : ℤ) = (j : ℤ) - (ℓ' : ℤ) := by omega
        rw [hsub1, hsub2]; push_cast; linarith
    exact hterm1.add hterm2

theorem qPolyCoeff_diag_limit {d : ℕ} (hd : 3 ≤ d) (j : ℕ) :
    Tendsto (fun p : ℝ ↦ ((p ^ (-((d * j : ℕ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff d j j p)
      atTop (𝓝 ((((d - 1 : ℕ) : ℂ)⁻¹) ^ j)) := by
  have h1 : Tendsto (fun p : ℝ ↦ (Real.exp (1 / p ^ (d - 1)) : ℂ)) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun p : ℝ ↦ (1 : ℝ) / p ^ (d - 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega : d - 1 ≠ 0))
    have hexpR : Tendsto (fun p : ℝ ↦ Real.exp (1 / p ^ (d - 1))) atTop (𝓝 1) := by
      have hc := (Real.continuous_exp.tendsto 0).comp hdiv
      rwa [Real.exp_zero] at hc
    simpa only [Function.comp_def, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto 1).comp hexpR
  have hpow := (h1.const_mul (((d - 1 : ℕ) : ℂ)⁻¹)).pow j
  rw [mul_one] at hpow
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [qPolyCoeff_diag, invSpeedD, Real.rpow_neg hp.le, Real.rpow_natCast,
      Complex.ofReal_inv, Complex.ofReal_pow]
  have hpow_rhs : (((d - 1 : ℕ) : ℂ)⁻¹ * (p : ℂ) ^ d * ↑(Real.exp (1 / p ^ (d - 1)))) ^ j =
      (((d - 1 : ℕ) : ℂ)⁻¹) ^ j * (p : ℂ) ^ (d * j) * (↑(Real.exp (1 / p ^ (d - 1)))) ^ j := by
    rw [mul_pow, mul_pow, ← pow_mul]
  rw [hpow_rhs, mul_pow]
  calc (((d - 1 : ℕ) : ℂ)⁻¹) ^ j * (↑(Real.exp (1 / p ^ (d - 1)))) ^ j
      = (((d - 1 : ℕ) : ℂ)⁻¹) ^ j * (((p : ℂ) ^ (d * j))⁻¹ * (p : ℂ) ^ (d * j)) *
          (↑(Real.exp (1 / p ^ (d - 1)))) ^ j := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hp0), mul_one]
    _ = ((p : ℂ) ^ (d * j))⁻¹ * ((((d - 1 : ℕ) : ℂ)⁻¹) ^ j * (p : ℂ) ^ (d * j) *
          (↑(Real.exp (1 / p ^ (d - 1)))) ^ j) := by ring

/-- Exact chain-rule identity expanding `iterQDeriv d j f` into ordinary `p`-derivatives
for any smooth function `f` on a tail `p > L`. -/
theorem iterQDeriv_eq_sum {d : ℕ} (hd : 3 ≤ d) (f : ℝ → ℂ) (j : ℕ)
    (hsmooth : ∀ ℓ ≤ j, ∀ᶠ p : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv ℓ f) p) :
    ∀ᶠ p : ℝ in atTop,
      iterQDeriv d j f p =
        ∑ ℓ ∈ Finset.range (j + 1), qPolyCoeff d j ℓ p * iteratedDeriv ℓ f p := by
  induction j with
  | zero =>
    filter_upwards with p
    simp [iterQDeriv, qPolyCoeff]
  | succ j ih =>
    have hprev := ih (fun ℓ hℓ ↦ hsmooth ℓ (by omega))
    obtain ⟨L, hL⟩ := eventually_atTop.1 hprev
    have hall_diff : ∀ᶠ p : ℝ in atTop, ∀ ℓ ∈ Finset.range (j + 1),
        DifferentiableAt ℝ (iteratedDeriv ℓ f) p :=
      Filter.eventually_all_finset (Finset.range (j + 1)) |>.mpr fun ℓ hℓ ↦
        hsmooth ℓ (by have := Finset.mem_range.mp hℓ; omega)
    filter_upwards [eventually_gt_atTop (max L 0), hall_diff] with p hp hdiff
    have hp_pos : 0 < p := lt_of_le_of_lt (le_max_right L 0) hp
    have hL_lt : L < p := lt_of_le_of_lt (le_max_left L 0) hp
    have hnear : iterQDeriv d j f =ᶠ[𝓝 p]
        fun x ↦ ∑ ℓ ∈ Finset.range (j + 1), qPolyCoeff d j ℓ x * iteratedDeriv ℓ f x :=
      (lt_mem_nhds hL_lt).mono fun x hx ↦ hL x hx.le
    change invSpeedD d p * deriv (iterQDeriv d j f) p = _
    rw [hnear.deriv_eq]
    have hterm_deriv (ℓ : ℕ) (hℓ : ℓ ∈ Finset.range (j + 1)) :
        HasDerivAt (fun x ↦ qPolyCoeff d j ℓ x * iteratedDeriv ℓ f x)
          (deriv (qPolyCoeff d j ℓ) p * iteratedDeriv ℓ f p +
            qPolyCoeff d j ℓ p * iteratedDeriv (ℓ + 1) f p) p := by
      have hdq : DifferentiableAt ℝ (qPolyCoeff d j ℓ) p :=
        (qPolyCoeff_QCoeff hd j ℓ (by have := Finset.mem_range.mp hℓ; omega)).smooth hp_pos
      have hdf : DifferentiableAt ℝ (iteratedDeriv ℓ f) p := hdiff ℓ hℓ
      have hm := hdq.hasDerivAt.mul hdf.hasDerivAt
      rw [← iteratedDeriv_succ] at hm
      exact hm
    have hsum_d := HasDerivAt.fun_sum (u := Finset.range (j + 1)) hterm_deriv
    rw [hsum_d.deriv, Finset.mul_sum]
    have hsplit : (∑ ℓ ∈ Finset.range (j + 1),
        invSpeedD d p * (deriv (qPolyCoeff d j ℓ) p * iteratedDeriv ℓ f p +
          qPolyCoeff d j ℓ p * iteratedDeriv (ℓ + 1) f p)) =
      (∑ ℓ ∈ Finset.range (j + 1),
        invSpeedD d p * deriv (qPolyCoeff d j ℓ) p * iteratedDeriv ℓ f p) +
      (∑ ℓ ∈ Finset.range (j + 1),
        invSpeedD d p * qPolyCoeff d j ℓ p * iteratedDeriv (ℓ + 1) f p) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro ℓ _; ring
    rw [hsplit]
    have hpart1 : (∑ ℓ ∈ Finset.range (j + 1),
        invSpeedD d p * deriv (qPolyCoeff d j ℓ) p * iteratedDeriv ℓ f p) =
      ∑ ℓ ∈ Finset.range (j + 2),
        invSpeedD d p * deriv (qPolyCoeff d j ℓ) p * iteratedDeriv ℓ f p := by
      symm
      rw [Finset.sum_range_succ]
      have hz : qPolyCoeff d j (j + 1) = fun _ ↦ 0 := funext (qPolyCoeff_gt j (j + 1) (by omega))
      rw [hz, deriv_const']
      simp
    have hpart2 : (∑ ℓ ∈ Finset.range (j + 1),
        invSpeedD d p * qPolyCoeff d j ℓ p * iteratedDeriv (ℓ + 1) f p) =
      ∑ ℓ ∈ Finset.range (j + 2),
        (if ℓ = 0 then 0 else invSpeedD d p * qPolyCoeff d j (ℓ - 1) p) * iteratedDeriv ℓ f p := by
      symm
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      simp
    rw [hpart1, hpart2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro ℓ _
    rw [qPolyCoeff, add_mul]

end
end CubicTheta.AllD
