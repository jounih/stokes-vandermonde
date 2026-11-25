module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Pak Conjecture 2.5a (`∑ p_n q^n`) — Unconditional `D₁ / τ / L_M`-Vandermonde Engine

This module formalizes the complete algebraic and analytic descent engine that bypasses
Écalle's global endless-continuability hypothesis `(H1)` for Pak's ICM 2018 Conjecture 2.5a:

1. **Algebraic derivations** `D1Op` and `LmOp m` on `MvPolynomial (Fin (r + 1)) ℂ`:
   commutativity `LmOp_comm` and strict total-degree drop `LmOp_totalDegree_lt`.
2. **Exact `τ`-differentiation identity**: for any smooth `H : ℝ → ℂ` and
   `Y H τ u := exp (τ * exp (-u)) * H u`, the function
   `F_eval P H u τ := eval (fun j => iteratedDeriv j (Y H τ) u) P` is entire in `τ` and satisfies
   `iteratedDeriv k (F_eval P H u) 0 = exp (-k * u) * eval (fun j => iteratedDeriv j H u) (D1Op^[k] P)`.
3. **Step 2 (`tau_invariance`)**: if `eval (iteratedDeriv · H u) (D1Op^[k] P) = 0` for all `k`,
   then `F_eval P H u (2 * π * I) = 0`, i.e., `P` vanishes on `H̃(u) = exp (2πi e^{-u}) H(u)`.
4. **Steps 1, 3, and 4 (`D1_invariance`, `strong_induction_Lm_eq_zero`,
   `vandermonde_collapse_eq_const`, `pak_nth_prime_engine_eq_zero`)**: from `H_- = H̃ + η`
   with geometric-bound series `η(u) = ∑' m, c (m + 2) * exp (-(m + 2) u)`, infinitely many
   `c m ≠ 0`, polynomial-order jet bounds on `H_+`, and the Log-Borel Bridge hypothesis,
   deduce `P = 0`.
5. **Unconditional non-polynomiality (`infinitely_many_cm_ne_zero`, `R_integral_neg_ne_zero`)**:
   for any `R : ℂ → ℂ` continuous at `-1` with `R (-1) ≠ 0` (and in particular for the literal
   integral `R_integral t = t * ∫_{x>0} exp(-x + t E₁(x)) dx` at `t = -s`, `s > 0`), the Stokes
   perturbation `η(t) = -(exp (2πi t) - 1) * R t` cannot be a polynomial, hence
   `{m : ℕ | 2 ≤ m ∧ c m ≠ 0}.Infinite`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.PakNthPrimeEngine

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open scoped Topology BigOperators

noncomputable section

/-! ### 1. Algebraic Derivations `D1Op` and `LmOp` -/

/-- The `D₁` linear differential operator on `MvPolynomial (Fin (r + 1)) ℂ`:
`(D₁ Q)(X) = ∑ j, (∑ s ≤ j, C(j, s) (-1)^(j-s) X_s) * ∂_j Q`. -/
@[expose] def D1Op {r : ℕ} :
    MvPolynomial (Fin (r + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin (r + 1)) ℂ where
  toFun P :=
    ∑ j : Fin (r + 1),
      (∑ s : Fin (r + 1),
        if (s : ℕ) ≤ (j : ℕ) then
          (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) •
            MvPolynomial.X s
        else 0) * MvPolynomial.pderiv j P
  map_add' P Q := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, mul_smul_comm]

theorem D1Op_apply {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) :
    D1Op P =
      ∑ j : Fin (r + 1),
        (∑ s : Fin (r + 1),
          if (s : ℕ) ≤ (j : ℕ) then
            (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) •
              MvPolynomial.X s
          else 0) * MvPolynomial.pderiv j P := rfl

/-- Constant-coefficient frequency derivation `L_m P = ∑ j, (-m)^j • ∂_j P`. -/
@[expose] def LmOp {r : ℕ} (m : ℕ) :
    MvPolynomial (Fin (r + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin (r + 1)) ℂ where
  toFun P := ∑ j : Fin (r + 1), (-(m : ℂ)) ^ (j : ℕ) • MvPolynomial.pderiv j P
  map_add' P Q := by
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, smul_comm]

theorem LmOp_apply {r : ℕ} (m : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    LmOp m P = ∑ j : Fin (r + 1), (-(m : ℂ)) ^ (j : ℕ) • MvPolynomial.pderiv j P := rfl

/-- Helper: `eval x (c • P) = c * eval x P`. -/
lemma eval_smul_eq {ι : Type*} (x : ι → ℂ) (c : ℂ) (P : MvPolynomial ι ℂ) :
    MvPolynomial.eval x (c • P) = c * MvPolynomial.eval x P := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]

/-- Partial derivatives on `MvPolynomial` commute. -/
lemma pderiv_comm_apply {ι : Type*} (i j : ι) (P : MvPolynomial ι ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add,
      hp, Pi.single_apply]
    by_cases hkj : k = j <;> by_cases hki : k = i
    · subst hkj; subst hki; rfl
    · subst hkj; simp [hki]; ring
    · subst hki; simp [hkj]; ring
    · simp [hkj, hki]

/-- The operators `LmOp m` and `LmOp n` commute for all `m, n : ℕ`. -/
theorem LmOp_comm {r : ℕ} (m n : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    LmOp m (LmOp n P) = LmOp n (LmOp m P) := by
  simp only [LmOp_apply, map_sum, LinearMap.map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, pderiv_comm_apply]

lemma totalDegree_pderiv_lt {ι : Type*} (i : ι) (P : MvPolynomial ι ℂ)
    (h : 0 < P.totalDegree) : (MvPolynomial.pderiv i P).totalDegree < P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree_eq]
  apply lt_of_le_of_lt (Finset.sup_le fun m hm => ?_) (Nat.pred_lt h.ne')
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hn
  have hs := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
  change ((m + Finsupp.single i 1).sum fun _ => id) ≤ _ at hs
  rw [← Finsupp.card_toMultiset, Finsupp.toMultiset_add, Finsupp.toMultiset_single] at hs
  simp at hs
  rw [Finsupp.card_toMultiset, Nat.pred_eq_sub_one]
  omega

private lemma totalDegree_sum_lt {ι σ : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial σ ℂ) {d : ℕ} (hd : 0 < d)
    (hf : ∀ i ∈ s, (f i).totalDegree < d) :
    (∑ i ∈ s, f i).totalDegree < d := by
  induction s using Finset.induction_on with
  | empty => simpa using hd
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (MvPolynomial.totalDegree_add _ _).trans_lt ?_
    exact max_lt (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- `LmOp m` strictly drops total degree whenever `0 < P.totalDegree`. -/
theorem LmOp_totalDegree_lt {r : ℕ} (m : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (h : 0 < P.totalDegree) : (LmOp m P).totalDegree < P.totalDegree := by
  classical
  rw [LmOp_apply]
  refine totalDegree_sum_lt Finset.univ _ h fun j _ => ?_
  refine (MvPolynomial.totalDegree_smul_le _ _).trans_lt ?_
  exact totalDegree_pderiv_lt j P h

lemma all_partials_zero {ι : Type*} (P : MvPolynomial ι ℂ)
    (h : ∀ i, MvPolynomial.pderiv i P = 0) : P = MvPolynomial.C (P.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  · have hsupp : ∃ i, m i ≠ 0 := by
      by_contra! hall
      exact hm (Finsupp.ext hall)
    obtain ⟨i, hi⟩ := hsupp
    let m' : ι →₀ ℕ := m - Finsupp.single i 1
    have hcoeff : (MvPolynomial.pderiv i P).coeff m' = 0 := by
      rw [h i]; simp
    rw [MvPolynomial.coeff_pderiv] at hcoeff
    have hadd : m' + Finsupp.single i 1 = m := by
      ext j
      simp only [m', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
      by_cases hji : j = i
      · subst hji; rw [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_apply, ite_eq_right_iff.mpr (fun h => absurd h.symm hji)]; omega
    rw [hadd] at hcoeff
    have hne : (m' i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' i)
    have hp0 : P.coeff m = 0 := (mul_eq_zero.mp hcoeff).resolve_right hne
    rw [hp0, MvPolynomial.coeff_C]
    simp [Ne.symm hm]

/-! ### 2. Exact `τ`-Differentiation Identity & Touchard Polynomials -/

/-- Touchard-type polynomials satisfying
`iteratedDeriv n (fun x => exp (τ * exp (-x))) u = exp (τ * exp (-u)) * (touchard n).eval (τ * exp (-u))`. -/
@[expose] def touchard : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => -(Polynomial.X * (touchard n + Polynomial.derivative (touchard n)))

@[simp] lemma touchard_zero : touchard 0 = 1 := rfl

lemma touchard_succ (n : ℕ) :
    touchard (n + 1) = -(Polynomial.X * (touchard n + Polynomial.derivative (touchard n))) := rfl

/-- Key algebraic identity: `T_n + T_n' = ∑_{k=0}^n C(n, k) (-1)^{n-k} T_k`. -/
theorem touchard_add_deriv (n : ℕ) :
    touchard n + Polynomial.derivative (touchard n) =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard k := by
  induction n with
  | zero => simp [touchard]
  | succ n ih =>
    have hD : Polynomial.derivative (touchard (n + 1)) =
        -(touchard n + Polynomial.derivative (touchard n)) -
          Polynomial.X * Polynomial.derivative (touchard n + Polynomial.derivative (touchard n)) := by
      rw [touchard_succ, map_neg, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul]
      ring
    have hLHS : touchard (n + 1) + Polynomial.derivative (touchard (n + 1)) =
        -(touchard n + Polynomial.derivative (touchard n)) +
          -(Polynomial.X * ((touchard n + Polynomial.derivative (touchard n)) +
            Polynomial.derivative (touchard n + Polynomial.derivative (touchard n)))) := by
      rw [hD, touchard_succ]; ring
    rw [hLHS, ih]
    have hderiv_sum :
        Polynomial.derivative
          (∑ k ∈ Finset.range (n + 1),
            Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard k) =
        ∑ k ∈ Finset.range (n + 1),
          Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) *
            Polynomial.derivative (touchard k) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
    rw [hderiv_sum, ← Finset.sum_add_distrib]
    have hmul_sum :
        -(Polynomial.X *
          ∑ k ∈ Finset.range (n + 1),
            (Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard k +
              Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) *
                Polynomial.derivative (touchard k))) =
        ∑ k ∈ Finset.range (n + 1),
          Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard (k + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [touchard_succ]
      ring
    rw [hmul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_range_succ' (fun k =>
      -(Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard k))]
    rw [Finset.sum_range_succ (fun k =>
      Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard (k + 1))]
    rw [Finset.sum_range_succ' (fun k =>
      Polynomial.C (((n + 1).choose k : ℂ) * (-1 : ℂ) ^ (n + 1 - k)) * touchard k)]
    rw [Finset.sum_range_succ (fun k =>
      Polynomial.C (((n + 1).choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n + 1 - (k + 1))) *
        touchard (k + 1))]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.sub_self, pow_zero, Nat.sub_zero,
      Nat.cast_one, one_mul, Nat.succ_sub_succ_eq_sub]
    have hmid :
        (∑ k ∈ Finset.range n,
          -(Polynomial.C ((n.choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n - (k + 1))) * touchard (k + 1))) +
        (∑ k ∈ Finset.range n,
          Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard (k + 1)) =
        ∑ k ∈ Finset.range n,
          Polynomial.C (((n + 1).choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard (k + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n := Finset.mem_range.mp hk
      have hsub : n - k = (n - (k + 1)) + 1 := by omega
      have hpow : (-1 : ℂ) ^ (n - k) = -((-1 : ℂ) ^ (n - (k + 1))) := by
        rw [hsub, pow_succ]; ring
      have hcoeff :
          -(Polynomial.C ((n.choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n - (k + 1)))) +
            Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) =
          Polynomial.C (((n + 1).choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n - k)) := by
        rw [← map_neg, ← map_add]
        congr 1
        rw [Nat.choose_succ_succ, Nat.cast_add, hpow]
        ring
      calc
        -(Polynomial.C ((n.choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n - (k + 1))) * touchard (k + 1)) +
            Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard (k + 1)
          = (-(Polynomial.C ((n.choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n - (k + 1)))) +
              Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k))) * touchard (k + 1) := by ring
        _ = Polynomial.C (((n + 1).choose (k + 1) : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard (k + 1) := by
            rw [hcoeff]
    have hpow0 : Polynomial.C ((-1 : ℂ) ^ (n + 1)) = -(Polynomial.C ((-1 : ℂ) ^ n)) := by
      rw [pow_succ, ← map_neg]; congr 1; ring
    rw [hpow0, ← hmid]
    ring

/-- The exponential factor `exp (τ * exp (-u))`. -/
@[expose] def expTau (τ : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (τ * Complex.exp (-(u : ℂ)))

/-- The `τ`-deformed function `Y(τ, u) = exp (τ * exp (-u)) * H(u)`. -/
@[expose] def Y (H : ℝ → ℂ) (τ : ℂ) (u : ℝ) : ℂ :=
  expTau τ u * H u

/-- The entire function `F_u(τ) = P(Y(τ, u), ∂_u Y(τ, u), ..., ∂_u^r Y(τ, u))`. -/
@[expose] def F_eval {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) (H : ℝ → ℂ) (u : ℝ) (τ : ℂ) : ℂ :=
  MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (Y H τ) u) P

lemma hasDerivAt_ofReal_id (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) u := by
  simpa using (hasDerivAt_id u).ofReal_comp

lemma hasDerivAt_neg_exp_real (u : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-(x : ℂ))) (-Complex.exp (-(u : ℂ))) u := by
  have h1 : HasDerivAt (fun x : ℝ => -(x : ℂ)) (-1 : ℂ) u := (hasDerivAt_ofReal_id u).neg
  simpa using h1.cexp

lemma hasDerivAt_expTau_poly (τ : ℂ) (Q : Polynomial ℂ) (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => expTau τ x * Q.eval (τ * Complex.exp (-(x : ℂ))))
      (expTau τ u *
        (-(Polynomial.X * (Q + Polynomial.derivative Q))).eval (τ * Complex.exp (-(u : ℂ)))) u := by
  have hz : HasDerivAt (fun x : ℝ => τ * Complex.exp (-(x : ℂ)))
      (-(τ * Complex.exp (-(u : ℂ)))) u := by
    simpa [mul_neg] using (hasDerivAt_neg_exp_real u).const_mul τ
  have hE : HasDerivAt (expTau τ)
      (expTau τ u * (-(τ * Complex.exp (-(u : ℂ))))) u := by
    exact hz.cexp
  have hQ : HasDerivAt (fun x : ℝ => Q.eval (τ * Complex.exp (-(x : ℂ))))
      ((Polynomial.derivative Q).eval (τ * Complex.exp (-(u : ℂ))) *
        (-(τ * Complex.exp (-(u : ℂ))))) u := by
    exact (Polynomial.hasDerivAt Q (τ * Complex.exp (-(u : ℂ)))).comp u hz
  convert hE.mul hQ using 1
  simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add]
  ring

/-- Exact `n`-th `u`-derivative of `exp (τ * exp (-u))` via Touchard polynomials. -/
theorem iteratedDeriv_expTau (n : ℕ) (τ : ℂ) (u : ℝ) :
    iteratedDeriv n (expTau τ) u =
      expTau τ u * (touchard n).eval (τ * Complex.exp (-(u : ℂ))) := by
  induction n generalizing u with
  | zero => simp [expTau, touchard]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (expTau τ) =
        fun x : ℝ => expTau τ x * (touchard n).eval (τ * Complex.exp (-(x : ℂ))) :=
      funext ih
    rw [hfun]
    exact (hasDerivAt_expTau_poly τ (touchard n) u).deriv

lemma contDiff_expTau (τ : ℂ) : ContDiff ℝ ⊤ (expTau τ) := by
  unfold expTau
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => -(x : ℂ)) :=
    Complex.ofRealCLM.contDiff.neg
  exact (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.contDiff_exp.comp h1)))

/-- `τ`-derivative of `iteratedDeriv n (expTau τ) u`. -/
lemma hasDerivAt_tau_iteratedDeriv_expTau (n : ℕ) (u : ℝ) (τ : ℂ) :
    HasDerivAt (fun t : ℂ => iteratedDeriv n (expTau t) u)
      (Complex.exp (-(u : ℂ)) *
        ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * iteratedDeriv k (expTau τ) u) τ := by
  have hfun : (fun t : ℂ => iteratedDeriv n (expTau t) u) =
      fun t : ℂ => Complex.exp (t * Complex.exp (-(u : ℂ))) *
        (touchard n).eval (t * Complex.exp (-(u : ℂ))) :=
    funext fun t => iteratedDeriv_expTau n t u
  rw [hfun]
  have hz : HasDerivAt (fun t : ℂ => t * Complex.exp (-(u : ℂ))) (Complex.exp (-(u : ℂ))) τ := by
    simpa using (hasDerivAt_id τ).mul_const (Complex.exp (-(u : ℂ)))
  have hE : HasDerivAt (fun t : ℂ => Complex.exp (t * Complex.exp (-(u : ℂ))))
      (Complex.exp (τ * Complex.exp (-(u : ℂ))) * Complex.exp (-(u : ℂ))) τ := by
    simpa using hz.cexp
  have hQ : HasDerivAt (fun t : ℂ => (touchard n).eval (t * Complex.exp (-(u : ℂ))))
      ((Polynomial.derivative (touchard n)).eval (τ * Complex.exp (-(u : ℂ))) *
        Complex.exp (-(u : ℂ))) τ := by
    exact (Polynomial.hasDerivAt (touchard n) (τ * Complex.exp (-(u : ℂ)))).comp τ hz
  convert hE.mul hQ using 1
  have h1 :
      Complex.exp (τ * Complex.exp (-(u : ℂ))) * Complex.exp (-(u : ℂ)) *
          (touchard n).eval (τ * Complex.exp (-(u : ℂ))) +
        Complex.exp (τ * Complex.exp (-(u : ℂ))) *
          ((Polynomial.derivative (touchard n)).eval (τ * Complex.exp (-(u : ℂ))) *
            Complex.exp (-(u : ℂ))) =
      Complex.exp (-(u : ℂ)) * expTau τ u *
        (touchard n + Polynomial.derivative (touchard n)).eval (τ * Complex.exp (-(u : ℂ))) := by
    simp only [Polynomial.eval_add, expTau]; ring
  rw [h1, touchard_add_deriv]
  have heval_sum : ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℂ) (z : ℂ),
      Polynomial.eval z (∑ k ∈ s, f k) = ∑ k ∈ s, Polynomial.eval z (f k) := by
    intro s f z
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih => rw [Finset.sum_insert hk, Polynomial.eval_add, ih, Finset.sum_insert hk]
  rw [heval_sum (Finset.range (n + 1))
    (fun k => Polynomial.C ((n.choose k : ℂ) * (-1 : ℂ) ^ (n - k)) * touchard k)
    (τ * Complex.exp (-(u : ℂ)))]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, iteratedDeriv_expTau]
  ring

/-- Leibniz expansion of `iteratedDeriv j (Y H τ) u`. -/
lemma iteratedDeriv_Y_eq {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H) (j : ℕ) (τ : ℂ) (u : ℝ) :
    iteratedDeriv j (Y H τ) u =
      ∑ s ∈ Finset.range (j + 1),
        (j.choose s : ℂ) * iteratedDeriv (j - s) (expTau τ) u * iteratedDeriv s H u := by
  have hE : ContDiffAt ℝ j (expTau τ) u := (contDiff_expTau τ).contDiffAt.of_le le_top
  have hH' : ContDiffAt ℝ j H u := hH.contDiffAt.of_le le_top
  have hmul := iteratedDeriv_mul hE hH'
  have hYdef : Y H τ = expTau τ * H := rfl
  rw [hYdef, hmul]
  rw [← Finset.sum_range_reflect (fun s =>
    (j.choose s : ℂ) * iteratedDeriv (j - s) (expTau τ) u * iteratedDeriv s H u) (j + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkj : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : j + 1 - 1 - k = j - k := by omega
  have h2 : j - (j - k) = k := by omega
  rw [h1, h2, Nat.choose_symm hkj]

/-- Exact `τ`-derivative of `iteratedDeriv j (Y H τ) u`. -/
theorem hasDerivAt_tau_iteratedDeriv_Y {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H)
    (j : ℕ) (u : ℝ) (τ : ℂ) :
    HasDerivAt (fun t : ℂ => iteratedDeriv j (Y H t) u)
      (Complex.exp (-(u : ℂ)) *
        ∑ m ∈ Finset.range (j + 1),
          ((j.choose m : ℂ) * (-1 : ℂ) ^ (j - m)) * iteratedDeriv m (Y H τ) u) τ := by
  have hfun : (fun t : ℂ => iteratedDeriv j (Y H t) u) =
      fun t : ℂ => ∑ s ∈ Finset.range (j + 1),
        (j.choose s : ℂ) * iteratedDeriv (j - s) (expTau t) u * iteratedDeriv s H u :=
    funext fun t => iteratedDeriv_Y_eq hH j t u
  rw [hfun]
  have hsum : HasDerivAt
      (fun t : ℂ => ∑ s ∈ Finset.range (j + 1),
        (j.choose s : ℂ) * iteratedDeriv (j - s) (expTau t) u * iteratedDeriv s H u)
      (∑ s ∈ Finset.range (j + 1),
        (j.choose s : ℂ) *
          (Complex.exp (-(u : ℂ)) *
            ∑ k ∈ Finset.range (j - s + 1),
              (((j - s).choose k : ℂ) * (-1 : ℂ) ^ (j - s - k)) *
                iteratedDeriv k (expTau τ) u) *
          iteratedDeriv s H u) τ := by
    refine HasDerivAt.fun_sum fun s _ => ?_
    exact ((hasDerivAt_tau_iteratedDeriv_expTau (j - s) u τ).const_mul (j.choose s : ℂ)).mul_const
      (iteratedDeriv s H u)
  convert hsum using 1
  simp_rw [iteratedDeriv_Y_eq hH]
  have hLHS :
      Complex.exp (-(u : ℂ)) *
        ∑ m ∈ Finset.range (j + 1),
          ((j.choose m : ℂ) * (-1 : ℂ) ^ (j - m)) *
            ∑ s ∈ Finset.range (m + 1),
              (m.choose s : ℂ) * iteratedDeriv (m - s) (expTau τ) u * iteratedDeriv s H u =
      Complex.exp (-(u : ℂ)) *
        ∑ m ∈ Finset.range (j + 1), ∑ s ∈ Finset.range (j + 1),
          if s ≤ m then
            (j.choose m : ℂ) * (m.choose s : ℂ) * (-1 : ℂ) ^ (j - m) *
              iteratedDeriv (m - s) (expTau τ) u * iteratedDeriv s H u
          else 0 := by
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mul_sum]
    have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range (j + 1)).filter (fun s => s ≤ m) = Finset.range (m + 1) := by
      ext s; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hLHS, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsj : s ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hRHS_re :
      (∑ m ∈ Finset.range (j + 1),
        if s ≤ m then
          (j.choose m : ℂ) * (m.choose s : ℂ) * (-1 : ℂ) ^ (j - m) *
            iteratedDeriv (m - s) (expTau τ) u * iteratedDeriv s H u
        else 0) =
      ∑ k ∈ Finset.range (j - s + 1),
        (j.choose (s + k) : ℂ) * ((s + k).choose s : ℂ) * (-1 : ℂ) ^ (j - (s + k)) *
          iteratedDeriv k (expTau τ) u * iteratedDeriv s H u := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun m _ => m - s) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
      omega
    · intro m₁ hm₁ m₂ hm₂ h
      simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
      omega
    · intro k hk
      refine ⟨s + k, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      have hms : s + (m - s) = m := by omega
      rw [hms]
  rw [hRHS_re, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hks : k ≤ j - s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hbinom : (j.choose (s + k) : ℂ) * ((s + k).choose s : ℂ) =
      (j.choose s : ℂ) * ((j - s).choose k : ℂ) := by
    have hnat : j.choose (s + k) * (s + k).choose s = j.choose s * (j - s).choose k := by
      have h1 := Nat.choose_mul (n := j) (k := s + k) (s := s) (by omega)
      rw [show s + k - s = k by omega] at h1
      exact h1
    exact_mod_cast hnat
  have hsub : j - (s + k) = j - s - k := by omega
  rw [hsub]
  calc
    Complex.exp (-(u : ℂ)) *
        ((j.choose (s + k) : ℂ) * ((s + k).choose s : ℂ) * (-1 : ℂ) ^ (j - s - k) *
          iteratedDeriv k (expTau τ) u * iteratedDeriv s H u)
      = Complex.exp (-(u : ℂ)) *
        ((j.choose s : ℂ) * ((j - s).choose k : ℂ) * (-1 : ℂ) ^ (j - s - k) *
          iteratedDeriv k (expTau τ) u * iteratedDeriv s H u) := by rw [hbinom]
    _ = (j.choose s : ℂ) *
        (Complex.exp (-(u : ℂ)) *
          (((j - s).choose k : ℂ) * (-1 : ℂ) ^ (j - s - k) * iteratedDeriv k (expTau τ) u)) *
        iteratedDeriv s H u := by ring

/-- Chain rule for `MvPolynomial.eval` along differentiable curves `x : ℂ → Fin (r + 1) → ℂ`. -/
lemma hasDerivAt_mvPolynomial_eval {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (x x' : ℂ → Fin (r + 1) → ℂ) (τ : ℂ)
    (hx : ∀ j : Fin (r + 1), HasDerivAt (fun t => x t j) (x' τ j) τ) :
    HasDerivAt (fun t => MvPolynomial.eval (x t) P)
      (∑ j : Fin (r + 1), MvPolynomial.eval (x τ) (MvPolynomial.pderiv j P) * x' τ j) τ := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa using hasDerivAt_const τ c
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext t; simp
    · simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hmul := hp.mul (hx i)
    convert hmul using 1
    · ext t; simp
    · simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul,
        MvPolynomial.eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
      have hsingle : (∑ j : Fin (r + 1), (if i = j then (1 : ℂ) else 0) *
          MvPolynomial.eval (x τ) p * x' τ j) = MvPolynomial.eval (x τ) p * x' τ i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [Ne.symm hji]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [add_comm, ← hsingle]
      congr 1
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i = j <;> simp [hij]

/-- Exact `τ`-derivative of `F_eval P H u τ`:
`∂_τ F_u(τ) = exp (-u) * F_u(D₁ P, τ)`. -/
theorem hasDerivAt_F_eval {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H) (u : ℝ) (τ : ℂ) :
    HasDerivAt (F_eval P H u) (Complex.exp (-(u : ℂ)) * F_eval (D1Op P) H u τ) τ := by
  have hx : ∀ j : Fin (r + 1),
      HasDerivAt (fun t => iteratedDeriv (j : ℕ) (Y H t) u)
        (Complex.exp (-(u : ℂ)) *
          ∑ s : Fin (r + 1),
            if (s : ℕ) ≤ (j : ℕ) then
              (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) *
                iteratedDeriv (s : ℕ) (Y H τ) u
            else 0) τ := by
    intro j
    convert hasDerivAt_tau_iteratedDeriv_Y hH (j : ℕ) u τ using 2
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun s _ => (s : ℕ)) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hs)
    · intro s₁ _ s₂ _ h; exact Fin.ext h
    · intro m hm
      have hmj : m ≤ (j : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      refine ⟨⟨m, lt_of_le_of_lt hmj j.isLt⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmj
    · intro s _; rfl
  have hmain := hasDerivAt_mvPolynomial_eval P
    (fun t j => iteratedDeriv (j : ℕ) (Y H t) u)
    (fun t j => Complex.exp (-(u : ℂ)) *
      ∑ s : Fin (r + 1),
        if (s : ℕ) ≤ (j : ℕ) then
          (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) *
            iteratedDeriv (s : ℕ) (Y H t) u
        else 0)
    τ hx
  change HasDerivAt (fun t => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (Y H t) u) P) _ τ
  convert hmain using 1
  simp only [F_eval, D1Op_apply, map_sum, map_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hinner :
      (∑ x : Fin (r + 1),
        MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (Y H τ) u)
          (if (x : ℕ) ≤ (j : ℕ) then
            (((j : ℕ).choose (x : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (x : ℕ))) •
              MvPolynomial.X x
          else 0)) =
      ∑ s : Fin (r + 1),
        if (s : ℕ) ≤ (j : ℕ) then
          (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) *
            iteratedDeriv (s : ℕ) (Y H τ) u
        else 0 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with hsj
    · rw [eval_smul_eq, MvPolynomial.eval_X]
    · simp
  rw [hinner]
  ring

/-- `F_eval P H u` is entire in `τ`. -/
theorem differentiable_F_eval {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H) (u : ℝ) :
    Differentiable ℂ (F_eval P H u) :=
  fun τ => (hasDerivAt_F_eval P hH u τ).differentiableAt

/-- Exact `k`-th `τ`-derivative of `F_eval P H u`:
`∂_τ^k F_u(τ) = exp (-k * u) * F_u(D₁^[k] P, τ)`. -/
theorem iteratedDeriv_F_eval {r : ℕ} (k : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H) (u : ℝ) (τ : ℂ) :
    iteratedDeriv k (F_eval P H u) τ =
      Complex.exp (-((k : ℂ) * (u : ℂ))) * F_eval (D1Op^[k] P) H u τ := by
  induction k generalizing P τ with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (F_eval P H u) =
        fun t => Complex.exp (-(u : ℂ)) * F_eval (D1Op P) H u t :=
      funext fun t => (hasDerivAt_F_eval P hH u t).deriv
    rw [hderiv, iteratedDeriv_const_mul_field, ih (D1Op P) τ]
    rw [Function.iterate_succ_apply, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Evaluation at `τ = 0`:
`iteratedDeriv k (F_eval P H u) 0 = exp (-k * u) * eval (iteratedDeriv · H u) (D₁^[k] P)`. -/
theorem iteratedDeriv_F_eval_zero {r : ℕ} (k : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H) (u : ℝ) :
    iteratedDeriv k (F_eval P H u) 0 =
      Complex.exp (-((k : ℂ) * (u : ℂ))) *
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H u) (D1Op^[k] P) := by
  rw [iteratedDeriv_F_eval k P hH u 0]
  have hY0 : Y H 0 = H := by
    ext x; simp [Y, expTau]
  simp only [F_eval, hY0]

/-! ### 3. Step 2: Exact `τ`-Invariance (`tau_invariance`) -/

/-- An entire function `f : ℂ → ℂ` with `iteratedDeriv k f 0 = 0` for all `k` vanishes identically. -/
lemma entire_eq_zero_of_iteratedDeriv_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : ∀ k : ℕ, iteratedDeriv k f 0 = 0) (z : ℂ) : f z = 0 := by
  have han : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hev : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    by_contra hne
    obtain ⟨n, g, hg, hg0, hfac⟩ :=
      (han 0 (Set.mem_univ 0)).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
    have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun w => w ^ n * g w := by
      filter_upwards [hfac] with w hw
      simpa [smul_eq_mul] using hw
    have hdn : iteratedDeriv n f 0 = (n.factorial : ℂ) * g 0 := by
      rw [hloc.iteratedDeriv_eq n]
      have hmul := iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ))
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w ^ n) 0).contDiffAt hg.contDiffAt
      rw [hmul]
      have hterm : ∀ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) * iteratedDeriv i (fun w : ℂ => w ^ n) (0 : ℂ) *
            iteratedDeriv (n - i) g 0 =
            if i = n then (n.factorial : ℂ) * g 0 else 0 := by
        intro i _
        rw [iteratedDeriv_fun_pow_zero]
        split_ifs with hin
        · subst hin; simp [Nat.choose_self]
        · simp
      rw [Finset.sum_congr rfl hterm]
      simp
    have hfact_ne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    exact hg0 ((mul_eq_zero.mp (hdn.symm.trans (h0 n))).resolve_left hfact_ne)
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev
    (Set.mem_univ z)

/-- **Step 2 (`tau_invariance`)**: If `eval (iteratedDeriv · H u) (D1Op^[k] P) = 0` for all `k`,
then `F_eval P H u τ = 0` for all `τ : ℂ`, and in particular `P` vanishes on
`H̃(u) = exp (2πi e^{-u}) H(u)`. -/
theorem tau_invariance {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H) (u : ℝ)
    (hD1 : ∀ k : ℕ, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H u)
      (D1Op^[k] P) = 0) :
    ∀ τ : ℂ, F_eval P H u τ = 0 := by
  intro τ
  refine entire_eq_zero_of_iteratedDeriv_zero (differentiable_F_eval P hH u) (fun k => ?_) τ
  rw [iteratedDeriv_F_eval_zero k P hH u, hD1 k, mul_zero]

theorem tau_invariance_two_pi_I {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ⊤ H) (u : ℝ)
    (hD1 : ∀ k : ℕ, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H u)
      (D1Op^[k] P) = 0) :
    F_eval P H u (2 * Real.pi * I) = 0 :=
  tau_invariance P hH u hD1 (2 * Real.pi * I)

/-! ### 4. Steps 1, 3, and 4: `D₁`-Invariance, Strong Induction on `L_M`, and Vandermonde Collapse -/

/-- Elementary polynomial growth, Lipschitz, and Taylor-1 bounds for `MvPolynomial.eval`. -/
lemma mvPolynomial_bounds {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) :
    ∃ (C0 C1 C2 : ℝ) (D : ℕ), 0 < C0 ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (x δ : Fin (r + 1) → ℂ) (Mx Mδ : ℝ),
        1 ≤ Mx → 0 ≤ Mδ → Mδ ≤ 1 →
        (∀ j, ‖x j‖ ≤ Mx) → (∀ j, ‖δ j‖ ≤ Mδ) →
        ‖MvPolynomial.eval x P‖ ≤ C0 * Mx ^ D ∧
        ‖MvPolynomial.eval (x + δ) P - MvPolynomial.eval x P‖ ≤ C1 * Mx ^ D * Mδ ∧
        ‖MvPolynomial.eval (x + δ) P - MvPolynomial.eval x P -
          ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j P) * δ j‖ ≤
          C2 * Mx ^ D * Mδ ^ 2 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨‖c‖ + 1, 1, 1, 0, by positivity, by positivity, by positivity, ?_⟩
    intro x δ Mx Mδ hMx hMδ _ _ _
    simp only [MvPolynomial.eval_C, pow_zero, mul_one, sub_self, norm_zero, pderiv_C,
      map_zero, zero_mul, Finset.sum_const_zero]
    exact ⟨by linarith, by positivity, by positivity⟩
  | add p q hp hq =>
    obtain ⟨Cp0, Cp1, Cp2, Dp, hCp0, hCp1, hCp2, hpb⟩ := hp
    obtain ⟨Cq0, Cq1, Cq2, Dq, hCq0, hCq1, hCq2, hqb⟩ := hq
    refine ⟨Cp0 + Cq0, Cp1 + Cq1, Cp2 + Cq2, max Dp Dq,
      by positivity, by positivity, by positivity, ?_⟩
    intro x δ Mx Mδ hMx hMδ hMδ1 hx hδ
    obtain ⟨hp0, hp1, hp2⟩ := hpb x δ Mx Mδ hMx hMδ hMδ1 hx hδ
    obtain ⟨hq0, hq1, hq2⟩ := hqb x δ Mx Mδ hMx hMδ hMδ1 hx hδ
    have hpow_p : Mx ^ Dp ≤ Mx ^ max Dp Dq := pow_le_pow_right₀ hMx (le_max_left _ _)
    have hpow_q : Mx ^ Dq ≤ Mx ^ max Dp Dq := pow_le_pow_right₀ hMx (le_max_right _ _)
    refine ⟨?_, ?_, ?_⟩
    · calc
        ‖MvPolynomial.eval x (p + q)‖
          = ‖MvPolynomial.eval x p + MvPolynomial.eval x q‖ := by simp
        _ ≤ ‖MvPolynomial.eval x p‖ + ‖MvPolynomial.eval x q‖ := norm_add_le _ _
        _ ≤ Cp0 * Mx ^ Dp + Cq0 * Mx ^ Dq := add_le_add hp0 hq0
        _ ≤ Cp0 * Mx ^ max Dp Dq + Cq0 * Mx ^ max Dp Dq := by nlinarith
        _ = (Cp0 + Cq0) * Mx ^ max Dp Dq := by ring
    · have heq : MvPolynomial.eval (x + δ) (p + q) - MvPolynomial.eval x (p + q) =
          (MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) +
          (MvPolynomial.eval (x + δ) q - MvPolynomial.eval x q) := by simp; ring
      rw [heq]
      calc
        ‖(MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) +
            (MvPolynomial.eval (x + δ) q - MvPolynomial.eval x q)‖
          ≤ ‖MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p‖ +
            ‖MvPolynomial.eval (x + δ) q - MvPolynomial.eval x q‖ := norm_add_le _ _
        _ ≤ Cp1 * Mx ^ Dp * Mδ + Cq1 * Mx ^ Dq * Mδ := add_le_add hp1 hq1
        _ ≤ Cp1 * Mx ^ max Dp Dq * Mδ + Cq1 * Mx ^ max Dp Dq * Mδ := by
            have h1 : Cp1 * Mx ^ Dp ≤ Cp1 * Mx ^ max Dp Dq := by nlinarith
            have h2 : Cq1 * Mx ^ Dq ≤ Cq1 * Mx ^ max Dp Dq := by nlinarith
            nlinarith
        _ = (Cp1 + Cq1) * Mx ^ max Dp Dq * Mδ := by ring
    · have heq :
          MvPolynomial.eval (x + δ) (p + q) - MvPolynomial.eval x (p + q) -
            ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (p + q)) * δ j =
          (MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p -
            ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j p) * δ j) +
          (MvPolynomial.eval (x + δ) q - MvPolynomial.eval x q -
            ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j q) * δ j) := by
        simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
      rw [heq]
      have hMδ2 : 0 ≤ Mδ ^ 2 := sq_nonneg Mδ
      calc
        ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
        _ ≤ Cp2 * Mx ^ Dp * Mδ ^ 2 + Cq2 * Mx ^ Dq * Mδ ^ 2 := add_le_add hp2 hq2
        _ ≤ Cp2 * Mx ^ max Dp Dq * Mδ ^ 2 + Cq2 * Mx ^ max Dp Dq * Mδ ^ 2 := by
            have h1 : Cp2 * Mx ^ Dp ≤ Cp2 * Mx ^ max Dp Dq := by nlinarith
            have h2 : Cq2 * Mx ^ Dq ≤ Cq2 * Mx ^ max Dp Dq := by nlinarith
            nlinarith
        _ = (Cp2 + Cq2) * Mx ^ max Dp Dq * Mδ ^ 2 := by ring
  | mul_X p i hp =>
    obtain ⟨Cp0, Cp1, Cp2, Dp, hCp0, hCp1, hCp2, hpb⟩ := hp
    refine ⟨Cp0, 2 * Cp1 + Cp0, 2 * Cp2 + Cp1, Dp + 1,
      by positivity, by positivity, by positivity, ?_⟩
    intro x δ Mx Mδ hMx hMδ hMδ1 hx hδ
    obtain ⟨hp0, hp1, hp2⟩ := hpb x δ Mx Mδ hMx hMδ hMδ1 hx hδ
    have hxi : ‖x i‖ ≤ Mx := hx i
    have hδi : ‖δ i‖ ≤ Mδ := hδ i
    have hxd : ‖x i + δ i‖ ≤ 2 * Mx := by
      calc ‖x i + δ i‖ ≤ ‖x i‖ + ‖δ i‖ := norm_add_le _ _
        _ ≤ Mx + Mδ := add_le_add hxi hδi
        _ ≤ Mx + 1 := by linarith
        _ ≤ 2 * Mx := by linarith
    have hMx_pos : 0 < Mx := lt_of_lt_of_le zero_lt_one hMx
    have hpow_le : Mx ^ Dp ≤ Mx ^ (Dp + 1) := pow_le_pow_right₀ hMx (Nat.le_succ Dp)
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ]
      calc ‖MvPolynomial.eval x p‖ * ‖x i‖
          ≤ (Cp0 * Mx ^ Dp) * Mx := mul_le_mul hp0 hxi (norm_nonneg _) (by positivity)
        _ = Cp0 * (Mx ^ Dp * Mx) := by ring
    · have heq : MvPolynomial.eval (x + δ) (p * MvPolynomial.X i) -
            MvPolynomial.eval x (p * MvPolynomial.X i) =
          (MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) * (x i + δ i) +
            MvPolynomial.eval x p * δ i := by
        simp only [map_mul, MvPolynomial.eval_X, Pi.add_apply]; ring
      rw [heq]
      calc
        ‖(MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) * (x i + δ i) +
            MvPolynomial.eval x p * δ i‖
          ≤ ‖MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p‖ * ‖x i + δ i‖ +
            ‖MvPolynomial.eval x p‖ * ‖δ i‖ := by
              have hna := norm_add_le
                ((MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) * (x i + δ i))
                (MvPolynomial.eval x p * δ i)
              simpa only [norm_mul] using hna
        _ ≤ (Cp1 * Mx ^ Dp * Mδ) * (2 * Mx) + (Cp0 * Mx ^ Dp) * Mδ := by
              exact add_le_add
                (mul_le_mul hp1 hxd (norm_nonneg _) (by positivity))
                (mul_le_mul hp0 hδi (norm_nonneg _) (by positivity))
        _ = 2 * Cp1 * Mx ^ (Dp + 1) * Mδ + Cp0 * Mx ^ Dp * Mδ := by rw [pow_succ]; ring
        _ ≤ 2 * Cp1 * Mx ^ (Dp + 1) * Mδ + Cp0 * Mx ^ (Dp + 1) * Mδ := by
              have : Cp0 * Mx ^ Dp ≤ Cp0 * Mx ^ (Dp + 1) := by nlinarith
              nlinarith
        _ = (2 * Cp1 + Cp0) * Mx ^ (Dp + 1) * Mδ := by ring
    · have hsum_pderiv :
          ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X i)) * δ j =
          (∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j p) * δ j) * x i +
            MvPolynomial.eval x p * δ i := by
        simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul,
          MvPolynomial.eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
        have h1 : (∑ j : Fin (r + 1),
            MvPolynomial.eval x p * (if i = j then (1 : ℂ) else 0) * δ j) =
            MvPolynomial.eval x p * δ i := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [Ne.symm hji]
          · intro hi; exact absurd (Finset.mem_univ i) hi
        rw [add_comm, ← h1]
        congr 1
        · rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : i = j <;> simp [hij]
      have heq' :
          MvPolynomial.eval (x + δ) (p * MvPolynomial.X i) -
            MvPolynomial.eval x (p * MvPolynomial.X i) -
            ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X i)) * δ j =
          (MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p -
            ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j p) * δ j) * x i +
          (MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) * δ i := by
        rw [hsum_pderiv]
        simp only [map_mul, MvPolynomial.eval_X, Pi.add_apply]
        ring
      rw [heq']
      have hMδ2 : 0 ≤ Mδ ^ 2 := sq_nonneg Mδ
      calc
        ‖(MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p -
              ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j p) * δ j) * x i +
            (MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) * δ i‖
          ≤ ‖MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p -
              ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j p) * δ j‖ * ‖x i‖ +
            ‖MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p‖ * ‖δ i‖ := by
              have hna := norm_add_le
                ((MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p -
                  ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j p) * δ j) * x i)
                ((MvPolynomial.eval (x + δ) p - MvPolynomial.eval x p) * δ i)
              simpa only [norm_mul] using hna
        _ ≤ (Cp2 * Mx ^ Dp * Mδ ^ 2) * Mx + (Cp1 * Mx ^ Dp * Mδ) * Mδ := by
              exact add_le_add
                (mul_le_mul hp2 hxi (norm_nonneg _) (by positivity))
                (mul_le_mul hp1 hδi (norm_nonneg _) (by positivity))
        _ = Cp2 * Mx ^ (Dp + 1) * Mδ ^ 2 + Cp1 * Mx ^ Dp * Mδ ^ 2 := by rw [pow_succ]; ring
        _ ≤ 2 * Cp2 * Mx ^ (Dp + 1) * Mδ ^ 2 + Cp1 * Mx ^ (Dp + 1) * Mδ ^ 2 := by
              have h1 : Cp2 * Mx ^ (Dp + 1) ≤ 2 * Cp2 * Mx ^ (Dp + 1) := by nlinarith [pow_pos hMx_pos (Dp + 1)]
              have h2 : Cp1 * Mx ^ Dp ≤ Cp1 * Mx ^ (Dp + 1) := by nlinarith
              nlinarith
        _ = (2 * Cp2 + Cp1) * Mx ^ (Dp + 1) * Mδ ^ 2 := by ring

/-- Shift invariance of `MvPolynomial.eval` when `LmOp m P = 0`. -/
theorem eval_add_smul_eq_of_LmOp_eq_zero {r : ℕ} (m : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hLm : LmOp m P = 0) (x : Fin (r + 1) → ℂ) (c : ℂ) :
    MvPolynomial.eval (fun j : Fin (r + 1) => x j + c * (-(m : ℂ)) ^ (j : ℕ)) P =
      MvPolynomial.eval x P := by
  let g : ℂ → ℂ := fun t => MvPolynomial.eval (fun j : Fin (r + 1) => x j + t * (-(m : ℂ)) ^ (j : ℕ)) P
  have hg : ∀ t : ℂ, HasDerivAt g 0 t := by
    intro t
    have hx : ∀ j : Fin (r + 1),
        HasDerivAt (fun s : ℂ => x j + s * (-(m : ℂ)) ^ (j : ℕ)) ((-(m : ℂ)) ^ (j : ℕ)) t := by
      intro j
      have h1 : HasDerivAt (fun s : ℂ => s * (-(m : ℂ)) ^ (j : ℕ)) ((-(m : ℂ)) ^ (j : ℕ)) t := by
        simpa using (hasDerivAt_id t).mul_const ((-(m : ℂ)) ^ (j : ℕ))
      simpa using (hasDerivAt_const t (x j)).fun_add h1
    have hd := hasDerivAt_mvPolynomial_eval P
      (fun s j => x j + s * (-(m : ℂ)) ^ (j : ℕ))
      (fun _ j => (-(m : ℂ)) ^ (j : ℕ)) t hx
    convert hd using 1
    have h0 : MvPolynomial.eval (fun j : Fin (r + 1) => x j + t * (-(m : ℂ)) ^ (j : ℕ)) (LmOp m P) = 0 := by
      rw [hLm, map_zero]
    rw [LmOp_apply, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_smul_eq, mul_comm]
  have hconst : g c = g 0 :=
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) c 0
  simpa [g] using hconst

/-- Exponential decay `u^A * exp (-u)` beats every inverse power `u^(-N)`. -/
lemma exists_bound_pow_mul_exp_neg (C : ℝ) (hC : 0 < C) (A N : ℕ) :
    ∃ C' > 0, ∃ U : ℝ, 1 ≤ U ∧ ∀ u ≥ U, C * u ^ A * Real.exp (-u) ≤ C' / u ^ N := by
  refine ⟨C * ((A + N).factorial : ℝ), by positivity, 1, le_rfl, fun u hu => ?_⟩
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hexp : u ^ (A + N) / ((A + N).factorial : ℝ) ≤ Real.exp u :=
    Real.pow_div_factorial_le_exp u (by linarith) (A + N)
  have hfact_pos : (0 : ℝ) < ((A + N).factorial : ℝ) := by positivity
  have h1 : u ^ (A + N) ≤ Real.exp u * ((A + N).factorial : ℝ) := by
    rw [div_le_iff₀ hfact_pos] at hexp
    linarith
  have h2 : u ^ A * Real.exp (-u) * u ^ N ≤ ((A + N).factorial : ℝ) := by
    have heq : u ^ A * Real.exp (-u) * u ^ N = u ^ (A + N) * (Real.exp u)⁻¹ := by
      rw [pow_add, Real.exp_neg]; ring
    rw [heq, mul_inv_le_iff₀ (Real.exp_pos u)]
    linarith
  rw [le_div_iff₀ (pow_pos hu_pos N)]
  nlinarith

/-- Helper for real part of `-(k * (u : ℂ))`. -/
lemma re_neg_nat_mul_ofReal (k : ℕ) (u : ℝ) :
    (-((k : ℂ) * (u : ℂ))).re = -((k : ℝ) * u) := by
  simp [Complex.mul_re]

/-- Geometric series bound for tail `∑_{m ≥ 0} ‖c (m + 2)‖ * (m + 2)^j * exp (-(m + 2) * u)`. -/
lemma summable_tail_exp {c : ℕ → ℂ} {Cc ρ : ℝ} (hCc : 0 < Cc) (hρ : 0 < ρ)
    (hc : ∀ m, 2 ≤ m → ‖c m‖ ≤ Cc * ρ ^ m) (j : ℕ) (u : ℝ)
    (hu : Real.log (2 * ρ) + 1 ≤ u) :
    Summable (fun m : ℕ => ‖c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ j *
      Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ)))‖) := by
  have hρu' : ρ * Real.exp (-u) ≤ (2 * Real.exp 1)⁻¹ := by
    have h2 : 2 * ρ * Real.exp 1 ≤ Real.exp u := by
      calc 2 * ρ * Real.exp 1 = Real.exp (Real.log (2 * ρ) + 1) := by
            rw [Real.exp_add, Real.exp_log (by positivity)]
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hu
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos u)]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  have hpoly_exp : ∀ k : ℕ, (k : ℝ) ^ j ≤ ((j.factorial : ℝ) * (3 : ℝ) ^ j) * (Real.exp (1 / 3)) ^ k := by
    intro k
    have h1 := Real.pow_div_factorial_le_exp ((k : ℝ) / 3) (by positivity) j
    have hfact_pos : (0 : ℝ) < (j.factorial : ℝ) := by positivity
    rw [div_pow, div_le_iff₀ hfact_pos] at h1
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have h2 : (k : ℝ) ^ j ≤ Real.exp ((k : ℝ) / 3) * ((j.factorial : ℝ) * (3 : ℝ) ^ j) := by
      have := mul_le_mul_of_nonneg_right h1 h3.le
      rw [div_mul_cancel₀ _ h3.ne'] at this
      linarith
    have hexp_k : Real.exp ((k : ℝ) / 3) = (Real.exp (1 / 3)) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hexp_k] at h2
    linarith
  have hr_lt : (Real.exp (1 / 3)) * (2 * Real.exp 1)⁻¹ < 1 := by
    rw [mul_inv_lt_iff₀ (by positivity), one_mul]
    have h1 : Real.exp (1 / 3) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith [Real.exp_pos 1]
  have hbase_nn : 0 ≤ Real.exp (1 / 3) * (2 * Real.exp 1)⁻¹ := by positivity
  have hgeom : Summable (fun m : ℕ =>
      (Cc * ((j.factorial : ℝ) * (3 : ℝ) ^ j)) *
        (Real.exp (1 / 3) * (2 * Real.exp 1)⁻¹) ^ (m + 2)) := by
    have h1 := (summable_geometric_of_lt_one hbase_nn hr_lt).comp_injective
      (fun a b (h : a + 2 = b + 2) => by omega)
    exact h1.mul_left _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hgeom
  have hnorm_exp : ‖Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ)))‖ = (Real.exp (-u)) ^ (m + 2) := by
    rw [Complex.norm_exp, re_neg_nat_mul_ofReal, show -(((m + 2 : ℕ) : ℝ) * u) = ((m + 2 : ℕ) : ℝ) * (-u) by ring,
      Real.exp_nat_mul]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_natCast, hnorm_exp]
  have hcm := hc (m + 2) (by omega)
  have hpow_le : ρ ^ (m + 2) * (Real.exp (-u)) ^ (m + 2) ≤ ((2 * Real.exp 1)⁻¹) ^ (m + 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hρu' (m + 2)
  have hp := hpoly_exp (m + 2)
  calc
    ‖c (m + 2)‖ * (((m + 2 : ℕ) : ℝ) ^ j) * (Real.exp (-u)) ^ (m + 2)
      ≤ (Cc * ρ ^ (m + 2)) * (((j.factorial : ℝ) * (3 : ℝ) ^ j) * (Real.exp (1 / 3)) ^ (m + 2)) *
          (Real.exp (-u)) ^ (m + 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hcm hp (by positivity) (by positivity)
    _ = (Cc * ((j.factorial : ℝ) * (3 : ℝ) ^ j)) *
          ((Real.exp (1 / 3)) ^ (m + 2) * (ρ ^ (m + 2) * (Real.exp (-u)) ^ (m + 2))) := by ring
    _ ≤ (Cc * ((j.factorial : ℝ) * (3 : ℝ) ^ j)) *
          ((Real.exp (1 / 3)) ^ (m + 2) * ((2 * Real.exp 1)⁻¹) ^ (m + 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = (Cc * ((j.factorial : ℝ) * (3 : ℝ) ^ j)) *
          (Real.exp (1 / 3) * (2 * Real.exp 1)⁻¹) ^ (m + 2) := by rw [mul_pow]

/-- Exact `n`-th derivative of `f + η` on `u > Real.log (2 * ρ) + 1` for smooth `f`. -/
lemma iteratedDeriv_add_eta {f : ℝ → ℂ} (hf : ContDiff ℝ ⊤ f)
    {c : ℕ → ℂ} {Cc ρ : ℝ} (hCc : 0 < Cc) (hρ : 0 < ρ)
    (hc : ∀ m, 2 ≤ m → ‖c m‖ ≤ Cc * ρ ^ m) (n : ℕ) :
    ∀ x : ℝ, Real.log (2 * ρ) + 1 < x →
      iteratedDeriv n (fun y : ℝ => f y +
          ∑' m : ℕ, c (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (y : ℂ)))) x =
        iteratedDeriv n f x +
          ∑' m : ℕ, c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ n *
            Complex.exp (-(((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
  let u0 : ℝ := Real.log (2 * ρ) + 1
  induction n with
  | zero => intro x _; simp
  | succ n ihn =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hl : iteratedDeriv n (fun y : ℝ => f y +
          ∑' m : ℕ, c (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (y : ℂ)))) =ᶠ[𝓝 x]
        fun y => iteratedDeriv n f y +
          ∑' m : ℕ, c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ n *
            Complex.exp (-(((m + 2 : ℕ) : ℂ) * (y : ℂ))) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ihn y hy
    rw [hl.deriv_eq]
    have hdf : DifferentiableAt ℝ (iteratedDeriv n f) x :=
      (hf.differentiable_iteratedDeriv n (by simp)) x
    have hsum0 : Summable (fun m : ℕ => c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ n *
        Complex.exp (-(((m + 2 : ℕ) : ℂ) * ((u0 + 1 : ℝ) : ℂ)))) :=
      (summable_tail_exp hCc hρ hc n (u0 + 1) (by linarith)).of_norm
    have hdη : HasDerivAt
        (fun y : ℝ => ∑' m : ℕ, c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ n *
          Complex.exp (-(((m + 2 : ℕ) : ℂ) * (y : ℂ))))
        (∑' m : ℕ, c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ (n + 1) *
          Complex.exp (-(((m + 2 : ℕ) : ℂ) * (x : ℂ)))) x := by
      refine hasDerivAt_tsum_of_isPreconnected (t := Set.Ioi u0)
        (g := fun m (y : ℝ) => c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ n *
          Complex.exp (-(((m + 2 : ℕ) : ℂ) * (y : ℂ))))
        (g' := fun m (y : ℝ) => c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ (n + 1) *
          Complex.exp (-(((m + 2 : ℕ) : ℂ) * (y : ℂ))))
        (summable_tail_exp hCc hρ hc (n + 1) u0 le_rfl) isOpen_Ioi isPreconnected_Ioi
        (fun m y _ => ?_) (fun m y hy => ?_)
        (by simp [u0] : u0 + 1 ∈ Set.Ioi u0) hsum0 hx
      · have h1 : HasDerivAt (fun z : ℝ => -(((m + 2 : ℕ) : ℂ) * (z : ℂ))) (-(((m + 2 : ℕ) : ℂ))) y := by
          simpa using ((hasDerivAt_ofReal_id y).const_mul ((m + 2 : ℕ) : ℂ)).fun_neg
        convert (h1.cexp).const_mul (c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ n) using 1
        rw [pow_succ]; ring
      · have hy' : u0 ≤ y := le_of_lt hy
        simp only [norm_mul, norm_pow, norm_neg, Complex.norm_natCast, Complex.norm_exp,
          re_neg_nat_mul_ofReal]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    rw [deriv_fun_add hdf hdη.differentiableAt, hdη.deriv, ← iteratedDeriv_succ]

/-- Tail norm bound for `∑_{m ≥ 0} c (m + M) * (-(m + M))^j * exp (-(m + M) * u)`. -/
lemma norm_tsum_tail_le {c : ℕ → ℂ} {Cc ρ : ℝ} (hCc : 0 < Cc) (hρ : 0 < ρ)
    (hc : ∀ m, 2 ≤ m → ‖c m‖ ≤ Cc * ρ ^ m) (j M : ℕ) (hM : 2 ≤ M) :
    ∃ K > 0, ∀ u : ℝ, Real.log (2 * ρ) + 1 ≤ u →
      ‖∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j *
        Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))‖ ≤
        K * Real.exp (-(M : ℝ) * u) := by
  let u0 : ℝ := Real.log (2 * ρ) + 1
  have hsum_all := summable_tail_exp hCc hρ hc j u0 le_rfl
  let K0 : ℝ := ∑' m : ℕ, ‖c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j *
    Complex.exp (-(((m + M : ℕ) : ℂ) * (u0 : ℂ)))‖
  have hsum_shift : Summable (fun m : ℕ =>
      ‖c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j * Complex.exp (-(((m + M : ℕ) : ℂ) * (u0 : ℂ)))‖) := by
    have hinj : Function.Injective (fun m : ℕ => m + (M - 2)) := fun _ _ h => Nat.add_right_cancel h
    have h1 := hsum_all.comp_injective hinj
    refine h1.congr fun m => ?_
    have hadd : m + (M - 2) + 2 = m + M := by omega
    simp only [Function.comp_apply, hadd]
  have hK0_nn : 0 ≤ K0 := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨(K0 + 1) * Real.exp ((M : ℝ) * u0), by positivity, fun u hu => ?_⟩
  have hterm : ∀ m : ℕ,
      ‖c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))‖ ≤
      Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) *
        ‖c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j * Complex.exp (-(((m + M : ℕ) : ℂ) * (u0 : ℂ)))‖ := by
    intro m
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_natCast, Complex.norm_exp,
      re_neg_nat_mul_ofReal]
    have hexp_le : Real.exp (-(((m + M : ℕ) : ℝ) * u)) ≤
        Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) * Real.exp (-(((m + M : ℕ) : ℝ) * u0)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      push_cast
      have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have hnonneg : 0 ≤ ‖c (m + M)‖ * ((m + M : ℕ) : ℝ) ^ j := by positivity
    calc
      ‖c (m + M)‖ * ((m + M : ℕ) : ℝ) ^ j * Real.exp (-(((m + M : ℕ) : ℝ) * u))
        ≤ ‖c (m + M)‖ * ((m + M : ℕ) : ℝ) ^ j *
            (Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) *
              Real.exp (-(((m + M : ℕ) : ℝ) * u0))) :=
          mul_le_mul_of_nonneg_left hexp_le hnonneg
      _ = Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) *
            (‖c (m + M)‖ * ((m + M : ℕ) : ℝ) ^ j * Real.exp (-(((m + M : ℕ) : ℝ) * u0))) := by ring
  have hsum_u : Summable (fun m : ℕ =>
      ‖c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsum_shift.mul_left _)
  calc
    ‖∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))‖
      ≤ ∑' m : ℕ, ‖c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j * Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hsum_u
    _ ≤ ∑' m : ℕ, Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) *
          ‖c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ j * Complex.exp (-(((m + M : ℕ) : ℂ) * (u0 : ℂ)))‖ :=
        hsum_u.tsum_le_tsum hterm (hsum_shift.mul_left _)
    _ = Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) * K0 := by
        rw [tsum_mul_left]
    _ ≤ (K0 + 1) * Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) := by
        have : 0 ≤ Real.exp ((M : ℝ) * u0) * Real.exp (-(M : ℝ) * u) := by positivity
        nlinarith

/-- Uniform bound on `iteratedDeriv n (expTau τ) u` minus its linear part for `u ≥ 1`. -/
lemma norm_iteratedDeriv_expTau_sub_le (n : ℕ) (τ : ℂ) :
    ∃ K > 0, ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv n (expTau τ) u -
        (if n = 0 then (1 : ℂ) + τ * Complex.exp (-(u : ℂ))
         else τ * (-1 : ℂ) ^ n * Complex.exp (-(u : ℂ)))‖ ≤
        K * Real.exp (-2 * u) := by
  have hT_const : ∀ n : ℕ, (touchard n).eval 0 = if n = 0 then 1 else 0 := by
    intro n; cases n with
    | zero => simp [touchard]
    | succ n => simp [touchard]
  have hT_deriv0 : ∀ n : ℕ, (Polynomial.derivative (touchard n)).eval 0 =
      if n = 0 then 0 else (-1 : ℂ) ^ n := by
    intro n
    induction n with
    | zero => simp [touchard]
    | succ n ih =>
      rw [touchard_succ, map_neg, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul]
      simp only [Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        zero_mul, add_zero, Nat.succ_ne_zero, ↓reduceIte]
      rw [hT_const n, ih]
      cases n with
      | zero => simp
      | succ n => simp [pow_succ]
  let φ : ℂ → ℂ := fun z => Complex.exp z * (touchard n).eval z
  have hφ0 : φ 0 = if n = 0 then 1 else 0 := by simp [φ, hT_const]
  have hφ'0 : deriv φ 0 = (-1 : ℂ) ^ n := by
    have hd : HasDerivAt φ
        (Complex.exp 0 * (touchard n).eval 0 +
          Complex.exp 0 * (Polynomial.derivative (touchard n)).eval 0) 0 := by
      simpa using (Complex.hasDerivAt_exp 0).fun_mul (Polynomial.hasDerivAt (touchard n) 0)
    rw [hd.deriv, Complex.exp_zero, one_mul, one_mul, hT_const n, hT_deriv0 n]
    cases n with
    | zero => simp
    | succ n => simp
  have hpoly_q : ∀ Q : Polynomial ℂ, ∃ Cq > 0, ∀ z : ℂ, ‖z‖ ≤ ‖τ‖ + 1 →
      ‖Q.eval z - Q.eval 0 - (Polynomial.derivative Q).eval 0 * z‖ ≤ Cq * ‖z‖ ^ 2 ∧
      ‖Q.eval z - Q.eval 0‖ ≤ Cq * ‖z‖ := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨Cp, hCp, hpb⟩ := hp
      obtain ⟨Cq, hCq, hqb⟩ := hq
      refine ⟨Cp + Cq, by positivity, fun z hz => ?_⟩
      obtain ⟨hp2, hp1⟩ := hpb z hz
      obtain ⟨hq2, hq1⟩ := hqb z hz
      refine ⟨?_, ?_⟩
      · have heq : (p + q).eval z - (p + q).eval 0 - (Polynomial.derivative (p + q)).eval 0 * z =
            (p.eval z - p.eval 0 - (Polynomial.derivative p).eval 0 * z) +
            (q.eval z - q.eval 0 - (Polynomial.derivative q).eval 0 * z) := by
          simp only [Polynomial.eval_add, map_add]; ring
        rw [heq]
        calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
          _ ≤ Cp * ‖z‖ ^ 2 + Cq * ‖z‖ ^ 2 := add_le_add hp2 hq2
          _ = (Cp + Cq) * ‖z‖ ^ 2 := by ring
      · have heq : (p + q).eval z - (p + q).eval 0 =
            (p.eval z - p.eval 0) + (q.eval z - q.eval 0) := by
          simp only [Polynomial.eval_add]; ring
        rw [heq]
        calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
          _ ≤ Cp * ‖z‖ + Cq * ‖z‖ := add_le_add hp1 hq1
          _ = (Cp + Cq) * ‖z‖ := by ring
    | monomial k a =>
      cases k with
      | zero =>
        refine ⟨1, one_pos, fun z _ => ?_⟩
        simp
      | succ k =>
        cases k with
        | zero =>
          refine ⟨‖a‖ + 1, by positivity, fun z _ => ?_⟩
          have he0 : (Polynomial.monomial 1 a).eval 0 = 0 := by simp
          have hd0 : (Polynomial.derivative (Polynomial.monomial 1 a)).eval 0 = a := by
            rw [Polynomial.derivative_monomial]; simp
          have hez : (Polynomial.monomial 1 a).eval z = a * z := by simp
          rw [he0, hd0, hez]
          simp only [sub_zero, sub_self, norm_zero, norm_mul]
          exact ⟨by positivity, by nlinarith [norm_nonneg z]⟩
        | succ k =>
          refine ⟨(‖a‖ + 1) * (‖τ‖ + 1) ^ (k + 1) + (‖a‖ + 1) * (‖τ‖ + 1) ^ k, by positivity,
            fun z hz => ?_⟩
          have heval0 : (Polynomial.monomial (k + 2) a).eval 0 = 0 := by
            simp [Polynomial.eval_monomial]
          have hderiv0 : (Polynomial.derivative (Polynomial.monomial (k + 2) a)).eval 0 = 0 := by
            rw [Polynomial.derivative_monomial]
            simp [Polynomial.eval_monomial]
          rw [heval0, hderiv0, sub_zero, zero_mul, sub_zero]
          simp only [Polynomial.eval_monomial, norm_mul, norm_pow]
          have h1 : ‖a‖ * ‖z‖ ^ (k + 2) ≤ (‖a‖ + 1) * (‖τ‖ + 1) ^ k * ‖z‖ ^ 2 := by
            have hz_pow : ‖z‖ ^ k ≤ (‖τ‖ + 1) ^ k := pow_le_pow_left₀ (norm_nonneg z) hz k
            calc ‖a‖ * ‖z‖ ^ (k + 2) = ‖a‖ * ‖z‖ ^ k * ‖z‖ ^ 2 := by rw [pow_add]; ring
              _ ≤ (‖a‖ + 1) * (‖τ‖ + 1) ^ k * ‖z‖ ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
                exact mul_le_mul (by linarith) hz_pow (by positivity) (by positivity)
          have h2 : ‖a‖ * ‖z‖ ^ (k + 2) ≤ (‖a‖ + 1) * (‖τ‖ + 1) ^ (k + 1) * ‖z‖ := by
            have hz_pow : ‖z‖ ^ (k + 1) ≤ (‖τ‖ + 1) ^ (k + 1) :=
              pow_le_pow_left₀ (norm_nonneg z) hz (k + 1)
            calc ‖a‖ * ‖z‖ ^ (k + 2) = ‖a‖ * ‖z‖ ^ (k + 1) * ‖z‖ := by rw [pow_succ]; ring
              _ ≤ (‖a‖ + 1) * (‖τ‖ + 1) ^ (k + 1) * ‖z‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
                exact mul_le_mul (by linarith) hz_pow (by positivity) (by positivity)
          have hpos1 : 0 ≤ (‖a‖ + 1) * (‖τ‖ + 1) ^ (k + 1) * ‖z‖ ^ 2 := by positivity
          have hpos2 : 0 ≤ (‖a‖ + 1) * (‖τ‖ + 1) ^ k * ‖z‖ := by positivity
          exact ⟨by linarith, by linarith⟩
  obtain ⟨Cq, hCq, hqb⟩ := hpoly_q (touchard n)
  have hexp1 : ∀ z : ℂ, ‖z‖ ≤ ‖τ‖ + 1 → ‖Complex.exp z - 1‖ ≤ Real.exp (‖τ‖ + 1) * ‖z‖ := by
    intro z hz
    have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_one] at h1
    calc ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by simpa using h1
      _ ≤ ‖z‖ * Real.exp (‖τ‖ + 1) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz) (norm_nonneg z)
      _ = Real.exp (‖τ‖ + 1) * ‖z‖ := by ring
  have hexp2 : ∀ z : ℂ, ‖z‖ ≤ ‖τ‖ + 1 → ‖Complex.exp z - 1 - z‖ ≤ Real.exp (‖τ‖ + 1) * ‖z‖ ^ 2 := by
    intro z hz
    have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
    have hsum : (∑ m ∈ Finset.range 2, z ^ m / (m.factorial : ℂ)) = 1 + z := by
      simp [Finset.sum_range_succ]
    rw [hsum, show Complex.exp z - (1 + z) = Complex.exp z - 1 - z by ring] at h1
    have h2 : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
      have hle : ‖z‖ ^ 2 / (2 : ℝ) * Real.exp ‖z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
        nlinarith [sq_nonneg ‖z‖, Real.exp_pos ‖z‖]
      simpa [Nat.factorial, div_mul_eq_mul_div] using h1.trans (by
        have : ‖z‖ ^ 2 * (Real.exp ‖z‖ / 2) = ‖z‖ ^ 2 / 2 * Real.exp ‖z‖ := by ring
        linarith)
    calc ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := h2
      _ ≤ ‖z‖ ^ 2 * Real.exp (‖τ‖ + 1) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz) (sq_nonneg _)
      _ = Real.exp (‖τ‖ + 1) * ‖z‖ ^ 2 := by ring
  let Cφ : ℝ := Real.exp (‖τ‖ + 1) + Real.exp (‖τ‖ + 1) * Cq + Cq
  refine ⟨Cφ * (‖τ‖ + 1) ^ 2, by positivity, fun u hu => ?_⟩
  rw [iteratedDeriv_expTau]
  set z : ℂ := τ * Complex.exp (-(u : ℂ))
  have hz_norm : ‖z‖ ≤ ‖τ‖ * Real.exp (-u) := by
    simp only [z, norm_mul, Complex.norm_exp]
    have hre : (-(u : ℂ)).re = -u := by simp
    rw [hre]
  have hz_le : ‖z‖ ≤ ‖τ‖ + 1 := by
    have hexp_le : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc ‖z‖ ≤ ‖τ‖ * Real.exp (-u) := hz_norm
      _ ≤ ‖τ‖ * 1 := mul_le_mul_of_nonneg_left hexp_le (norm_nonneg τ)
      _ ≤ ‖τ‖ + 1 := by linarith
  obtain ⟨hq2, hq1⟩ := hqb z hz_le
  have hmatch :
      (if n = 0 then (1 : ℂ) + τ * Complex.exp (-(u : ℂ))
       else τ * (-1 : ℂ) ^ n * Complex.exp (-(u : ℂ))) =
      φ 0 + deriv φ 0 * z := by
    rw [hφ0, hφ'0]
    cases n with
    | zero => simp [z]
    | succ n => simp [z]; ring
  rw [hmatch]
  have hdecomp :
      expTau τ u * (touchard n).eval z - (φ 0 + deriv φ 0 * z) =
      (Complex.exp z - 1 - z) * (touchard n).eval 0 +
      (Complex.exp z - 1) * ((touchard n).eval z - (touchard n).eval 0) +
      ((touchard n).eval z - (touchard n).eval 0 - (Polynomial.derivative (touchard n)).eval 0 * z) := by
    have h0 : φ 0 = (touchard n).eval 0 := by simp [φ]
    have h1 : deriv φ 0 = (touchard n).eval 0 + (Polynomial.derivative (touchard n)).eval 0 := by
      rw [hφ'0, hT_const n, hT_deriv0 n]; cases n <;> simp
    rw [h0, h1]
    change Complex.exp z * (touchard n).eval z - _ = _
    ring
  rw [hdecomp]
  have hT0_le : ‖(touchard n).eval 0‖ ≤ 1 := by
    rw [hT_const n]; split_ifs <;> simp
  have hstep : ‖(Complex.exp z - 1 - z) * (touchard n).eval 0 +
        (Complex.exp z - 1) * ((touchard n).eval z - (touchard n).eval 0) +
        ((touchard n).eval z - (touchard n).eval 0 - (Polynomial.derivative (touchard n)).eval 0 * z)‖ ≤
      Cφ * ‖z‖ ^ 2 := by
    calc
      ‖_ + _ + _‖
        ≤ ‖(Complex.exp z - 1 - z) * (touchard n).eval 0‖ +
          ‖(Complex.exp z - 1) * ((touchard n).eval z - (touchard n).eval 0)‖ +
          ‖(touchard n).eval z - (touchard n).eval 0 - (Polynomial.derivative (touchard n)).eval 0 * z‖ := by
            exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (Real.exp (‖τ‖ + 1) * ‖z‖ ^ 2) * 1 +
          (Real.exp (‖τ‖ + 1) * ‖z‖) * (Cq * ‖z‖) + Cq * ‖z‖ ^ 2 := by
            simp only [norm_mul]
            refine add_le_add (add_le_add ?_ ?_) hq2
            · exact mul_le_mul (hexp2 z hz_le) hT0_le (norm_nonneg _) (by positivity)
            · exact mul_le_mul (hexp1 z hz_le) hq1 (norm_nonneg _) (by positivity)
      _ = Cφ * ‖z‖ ^ 2 := by simp only [Cφ]; ring
  have hz2 : ‖z‖ ^ 2 ≤ (‖τ‖ + 1) ^ 2 * Real.exp (-2 * u) := by
    have h1 : ‖z‖ ^ 2 ≤ (‖τ‖ * Real.exp (-u)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg z) hz_norm 2
    have h2 : Real.exp (-u) ^ 2 = Real.exp (-2 * u) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [mul_pow, h2] at h1
    have hτ : ‖τ‖ ^ 2 ≤ (‖τ‖ + 1) ^ 2 := by nlinarith [norm_nonneg τ]
    nlinarith [Real.exp_pos (-2 * u)]
  calc
    ‖_‖ ≤ Cφ * ‖z‖ ^ 2 := hstep
    _ ≤ Cφ * ((‖τ‖ + 1) ^ 2 * Real.exp (-2 * u)) := by
        exact mul_le_mul_of_nonneg_left hz2 (by positivity)
    _ = Cφ * (‖τ‖ + 1) ^ 2 * Real.exp (-2 * u) := by ring

/-- **Step 1 (`D1_invariance`)**: Under the Stokes relation `H_- = exp(2πi e^{-u}) H_+ + η`,
polynomial jet bounds on `H_+`, and the Log-Borel Bridge hypothesis, if `Q` vanishes on
`H_+` and `H_-`, then `D1Op Q` also vanishes on `H_+` and `H_-`. -/
theorem D1_invariance {r : ℕ}
    {H_plus H_minus : ℝ → ℂ} (hHp : ContDiff ℝ ⊤ H_plus)
    {c : ℕ → ℂ} {Cc ρ : ℝ} (hCc : 0 < Cc) (hρ : 0 < ρ)
    (hc : ∀ m, 2 ≤ m → ‖c m‖ ≤ Cc * ρ ^ m)
    {u_stokes : ℝ}
    (hstokes : ∀ u ≥ u_stokes,
      H_minus u = Y H_plus (2 * Real.pi * I) u +
        ∑' m : ℕ, c (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))))
    {CH : ℝ} {A : ℕ} (hCH : 0 < CH)
    (hHbound : ∀ j : Fin (r + 1), ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv (j : ℕ) H_plus u‖ ≤ CH * u ^ A)
    (hbridge : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) Q = 0))
    (Q : MvPolynomial (Fin (r + 1)) ℂ)
    (hQ : ∀ u : ℝ,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q = 0 ∧
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) Q = 0) :
    ∀ u : ℝ,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) (D1Op Q) = 0 ∧
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) (D1Op Q) = 0 := by
  apply hbridge
  let τ0 : ℂ := 2 * Real.pi * I
  let u1 : ℝ := max (max u_stokes (Real.log (2 * ρ) + 1)) 1 + 1
  have hη_bound : ∀ j : Fin (r + 1), ∃ Kη > 0, ∀ u : ℝ, Real.log (2 * ρ) + 1 ≤ u →
      ‖∑' m : ℕ, c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ (j : ℕ) *
        Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ)))‖ ≤ Kη * Real.exp (-2 * u) := by
    intro j
    obtain ⟨K, hK, hKb⟩ := norm_tsum_tail_le hCc hρ hc (j : ℕ) 2 le_rfl
    exact ⟨K, hK, fun u hu => by simpa using hKb u hu⟩
  choose Kη hKη_pos hKη using hη_bound
  have hexp_b : ∀ n : ℕ, ∃ Ke > 0, ∀ u : ℝ, 1 ≤ u →
      ‖iteratedDeriv n (expTau τ0) u -
        (if n = 0 then (1 : ℂ) + τ0 * Complex.exp (-(u : ℂ))
         else τ0 * (-1 : ℂ) ^ n * Complex.exp (-(u : ℂ)))‖ ≤ Ke * Real.exp (-2 * u) :=
    fun n => norm_iteratedDeriv_expTau_sub_le n τ0
  choose Ke hKe_pos hKe using hexp_b
  let Ljet : ℝ → Fin (r + 1) → ℂ := fun u j =>
    ∑ s : Fin (r + 1),
      if (s : ℕ) ≤ (j : ℕ) then
        (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) *
          iteratedDeriv (s : ℕ) H_plus u
      else 0
  let C_err : ℝ := (∑ j : Fin (r + 1), Kη j) +
    (∑ j : Fin (r + 1), ∑ s ∈ Finset.range ((j : ℕ) + 1),
      ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) + 1
  have hC_err_pos : 0 < C_err := by
    have h1 : 0 ≤ ∑ j : Fin (r + 1), Kη j := Finset.sum_nonneg fun j _ => (hKη_pos j).le
    have h2 : 0 ≤ ∑ j : Fin (r + 1), ∑ s ∈ Finset.range ((j : ℕ) + 1),
        ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKe_pos _).le) hCH.le
    linarith
  let C_L : ℝ := (∑ j : Fin (r + 1), ∑ s : Fin (r + 1), ((j : ℕ).choose (s : ℕ) : ℝ) * CH) + 1
  have hC_L_pos : 0 < C_L := by
    have h1 : 0 ≤ ∑ j : Fin (r + 1), ∑ s : Fin (r + 1), ((j : ℕ).choose (s : ℕ) : ℝ) * CH :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => by positivity
    linarith
  have hL_bound : ∀ u : ℝ, 1 ≤ u → ∀ j : Fin (r + 1), ‖Ljet u j‖ ≤ C_L * u ^ A := by
    intro u hu j
    have hu_nn : 0 ≤ u ^ A := pow_nonneg (by linarith) A
    calc
      ‖Ljet u j‖ ≤ ∑ s : Fin (r + 1),
          ‖if (s : ℕ) ≤ (j : ℕ) then
            (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) *
              iteratedDeriv (s : ℕ) H_plus u
          else 0‖ := norm_sum_le _ _
      _ ≤ ∑ s : Fin (r + 1), ((j : ℕ).choose (s : ℕ) : ℝ) * (CH * u ^ A) := by
          refine Finset.sum_le_sum fun s _ => ?_
          split_ifs
          · rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_neg, norm_one, one_pow,
              mul_one]
            exact mul_le_mul_of_nonneg_left (hHbound s u hu) (by positivity)
          · simp; positivity
      _ = (∑ s : Fin (r + 1), ((j : ℕ).choose (s : ℕ) : ℝ) * CH) * u ^ A := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun s _ => by ring
      _ ≤ C_L * u ^ A := by
          have hle : (∑ s : Fin (r + 1), ((j : ℕ).choose (s : ℕ) : ℝ) * CH) ≤ C_L := by
            have hsingle := Finset.single_le_sum
              (f := fun j' : Fin (r + 1) => ∑ s : Fin (r + 1), ((j' : ℕ).choose (s : ℕ) : ℝ) * CH)
              (fun j' _ => Finset.sum_nonneg fun s _ => by positivity) (Finset.mem_univ j)
            linarith
          exact mul_le_mul_of_nonneg_right hle hu_nn
  have hdiff_bound : ∀ u : ℝ, u1 ≤ u → ∀ j : Fin (r + 1),
      ‖iteratedDeriv (j : ℕ) H_minus u - iteratedDeriv (j : ℕ) H_plus u -
        τ0 * Complex.exp (-(u : ℂ)) * Ljet u j‖ ≤ C_err * u ^ A * Real.exp (-2 * u) := by
    intro u hu j
    have hu_st : u_stokes < u := by
      have : u_stokes ≤ max (max u_stokes (Real.log (2 * ρ) + 1)) 1 :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      linarith
    have hu_log : Real.log (2 * ρ) + 1 < u := by
      have : Real.log (2 * ρ) + 1 ≤ max (max u_stokes (Real.log (2 * ρ) + 1)) 1 :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    have hu1 : 1 ≤ u := by
      have : (1 : ℝ) ≤ max (max u_stokes (Real.log (2 * ρ) + 1)) 1 := le_max_right _ _
      linarith
    have hloc : H_minus =ᶠ[𝓝 u] fun x => Y H_plus τ0 x +
        ∑' m : ℕ, c (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
      filter_upwards [Ioi_mem_nhds hu_st] with x hx
      exact hstokes x (le_of_lt hx)
    rw [hloc.iteratedDeriv_eq (j : ℕ)]
    have hYsmooth : ContDiff ℝ ⊤ (Y H_plus τ0) := (contDiff_expTau τ0).mul hHp
    rw [iteratedDeriv_add_eta hYsmooth hCc hρ hc (j : ℕ) u hu_log, iteratedDeriv_Y_eq hHp (j : ℕ) τ0 u]
    have hlin :
        iteratedDeriv (j : ℕ) H_plus u + τ0 * Complex.exp (-(u : ℂ)) * Ljet u j =
        ∑ s ∈ Finset.range ((j : ℕ) + 1),
          ((j : ℕ).choose s : ℂ) *
            (if (j : ℕ) - s = 0 then (1 : ℂ) + τ0 * Complex.exp (-(u : ℂ))
             else τ0 * (-1 : ℂ) ^ ((j : ℕ) - s) * Complex.exp (-(u : ℂ))) *
            iteratedDeriv s H_plus u := by
      have hL_range : Ljet u j = ∑ s ∈ Finset.range ((j : ℕ) + 1),
          (((j : ℕ).choose s : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - s)) * iteratedDeriv s H_plus u := by
        simp only [Ljet, ← Finset.sum_filter]
        refine Finset.sum_bij (fun s _ => (s : ℕ)) ?_ ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hs)
        · intro s₁ _ s₂ _ h; exact Fin.ext h
        · intro s hs
          have hsj : s ≤ (j : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
          refine ⟨⟨s, lt_of_le_of_lt hsj j.isLt⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hsj
        · intro s _; rfl
      rw [hL_range, Finset.mul_sum, Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, mul_one, ↓reduceIte]
      have hmid :
          (∑ x ∈ Finset.range (j : ℕ),
            τ0 * Complex.exp (-(u : ℂ)) *
              (((j : ℕ).choose x : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - x) * iteratedDeriv x H_plus u)) =
          ∑ x ∈ Finset.range (j : ℕ),
            ((j : ℕ).choose x : ℂ) *
              (if (j : ℕ) - x = 0 then (1 : ℂ) + τ0 * Complex.exp (-(u : ℂ))
               else τ0 * (-1 : ℂ) ^ ((j : ℕ) - x) * Complex.exp (-(u : ℂ))) *
              iteratedDeriv x H_plus u := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxj : x < (j : ℕ) := Finset.mem_range.mp hx
        have hne : (j : ℕ) - x ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        ring
      rw [hmid]; ring
    have heq :
        (∑ s ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose s : ℂ) * iteratedDeriv ((j : ℕ) - s) (expTau τ0) u *
              iteratedDeriv s H_plus u) +
          (∑' m : ℕ, c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ (j : ℕ) *
            Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ)))) -
          iteratedDeriv (j : ℕ) H_plus u - τ0 * Complex.exp (-(u : ℂ)) * Ljet u j =
        (∑ s ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose s : ℂ) *
              (iteratedDeriv ((j : ℕ) - s) (expTau τ0) u -
                (if (j : ℕ) - s = 0 then (1 : ℂ) + τ0 * Complex.exp (-(u : ℂ))
                 else τ0 * (-1 : ℂ) ^ ((j : ℕ) - s) * Complex.exp (-(u : ℂ)))) *
              iteratedDeriv s H_plus u) +
        (∑' m : ℕ, c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ (j : ℕ) *
          Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ)))) := by
      have hsub :
          (∑ s ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose s : ℂ) * iteratedDeriv ((j : ℕ) - s) (expTau τ0) u *
              iteratedDeriv s H_plus u) -
          (iteratedDeriv (j : ℕ) H_plus u + τ0 * Complex.exp (-(u : ℂ)) * Ljet u j) =
          ∑ s ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose s : ℂ) *
              (iteratedDeriv ((j : ℕ) - s) (expTau τ0) u -
                (if (j : ℕ) - s = 0 then (1 : ℂ) + τ0 * Complex.exp (-(u : ℂ))
                 else τ0 * (-1 : ℂ) ^ ((j : ℕ) - s) * Complex.exp (-(u : ℂ)))) *
              iteratedDeriv s H_plus u := by
        rw [hlin, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s _ => by ring
      linear_combination hsub
    rw [heq]
    have hsum_le :
        ‖∑ s ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose s : ℂ) *
              (iteratedDeriv ((j : ℕ) - s) (expTau τ0) u -
                (if (j : ℕ) - s = 0 then (1 : ℂ) + τ0 * Complex.exp (-(u : ℂ))
                 else τ0 * (-1 : ℂ) ^ ((j : ℕ) - s) * Complex.exp (-(u : ℂ)))) *
              iteratedDeriv s H_plus u‖ ≤
        (∑ s ∈ Finset.range ((j : ℕ) + 1),
          ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) * u ^ A * Real.exp (-2 * u) := by
      calc
        ‖∑ s ∈ Finset.range ((j : ℕ) + 1), _‖
          ≤ ∑ s ∈ Finset.range ((j : ℕ) + 1),
              ‖((j : ℕ).choose s : ℂ) *
                (iteratedDeriv ((j : ℕ) - s) (expTau τ0) u -
                  (if (j : ℕ) - s = 0 then (1 : ℂ) + τ0 * Complex.exp (-(u : ℂ))
                   else τ0 * (-1 : ℂ) ^ ((j : ℕ) - s) * Complex.exp (-(u : ℂ)))) *
                iteratedDeriv s H_plus u‖ := norm_sum_le _ _
        _ ≤ ∑ s ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose s : ℝ) * (Ke ((j : ℕ) - s) * Real.exp (-2 * u)) * (CH * u ^ A) := by
            refine Finset.sum_le_sum fun s hs => ?_
            have hsj : s ≤ (j : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
            let sFin : Fin (r + 1) := ⟨s, lt_of_le_of_lt hsj j.isLt⟩
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            have hKe_nn : 0 ≤ ((j : ℕ).choose s : ℝ) * (Ke ((j : ℕ) - s) * Real.exp (-2 * u)) :=
              mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKe_pos _).le (Real.exp_pos _).le)
            refine mul_le_mul ?_ (hHbound sFin u hu1) (norm_nonneg _) hKe_nn
            exact mul_le_mul_of_nonneg_left (hKe ((j : ℕ) - s) u hu1) (Nat.cast_nonneg _)
        _ = (∑ s ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) * u ^ A * Real.exp (-2 * u) := by
            rw [Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => by ring
    have hη_le := hKη j u (le_of_lt hu_log)
    have huA_ge1 : 1 ≤ u ^ A := one_le_pow₀ hu1
    have hKη_le : Kη j ≤ ∑ j' : Fin (r + 1), Kη j' :=
      Finset.single_le_sum (fun j' _ => (hKη_pos j').le) (Finset.mem_univ j)
    have hKe_le : (∑ s ∈ Finset.range ((j : ℕ) + 1), ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) ≤
        ∑ j' : Fin (r + 1), ∑ s ∈ Finset.range ((j' : ℕ) + 1),
          ((j' : ℕ).choose s : ℝ) * Ke ((j' : ℕ) - s) * CH :=
      Finset.single_le_sum
        (f := fun j' : Fin (r + 1) => ∑ s ∈ Finset.range ((j' : ℕ) + 1),
          ((j' : ℕ).choose s : ℝ) * Ke ((j' : ℕ) - s) * CH)
        (fun j' _ => Finset.sum_nonneg fun s _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKe_pos _).le) hCH.le)
        (Finset.mem_univ j)
    calc
      ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ (∑ s ∈ Finset.range ((j : ℕ) + 1), ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) *
            u ^ A * Real.exp (-2 * u) + Kη j * Real.exp (-2 * u) := add_le_add hsum_le hη_le
      _ ≤ (∑ s ∈ Finset.range ((j : ℕ) + 1), ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) *
            u ^ A * Real.exp (-2 * u) + Kη j * u ^ A * Real.exp (-2 * u) := by
          have : Kη j ≤ Kη j * u ^ A := by nlinarith [hKη_pos j]
          nlinarith [Real.exp_pos (-2 * u)]
      _ ≤ C_err * u ^ A * Real.exp (-2 * u) := by
          have hle : (∑ s ∈ Finset.range ((j : ℕ) + 1), ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) +
              Kη j ≤ C_err := by linarith
          have hnn : 0 ≤ u ^ A * Real.exp (-2 * u) := by positivity
          calc
            _ = ((∑ s ∈ Finset.range ((j : ℕ) + 1), ((j : ℕ).choose s : ℝ) * Ke ((j : ℕ) - s) * CH) +
                  Kη j) * (u ^ A * Real.exp (-2 * u)) := by ring
            _ ≤ C_err * (u ^ A * Real.exp (-2 * u)) := mul_le_mul_of_nonneg_right hle hnn
            _ = C_err * u ^ A * Real.exp (-2 * u) := by ring
  obtain ⟨C0, C1, C2, D, hC0, hC1, hC2, hQb⟩ := mvPolynomial_bounds Q
  have hpd_b : ∀ j : Fin (r + 1), ∃ Cp > 0, ∃ Dp : ℕ, ∀ (x : Fin (r + 1) → ℂ) (Mx : ℝ),
      1 ≤ Mx → (∀ k, ‖x k‖ ≤ Mx) → ‖MvPolynomial.eval x (MvPolynomial.pderiv j Q)‖ ≤ Cp * Mx ^ Dp := by
    intro j
    obtain ⟨c0, _, _, d0, hc0, _, _, hb⟩ := mvPolynomial_bounds (MvPolynomial.pderiv j Q)
    exact ⟨c0, hc0, d0, fun x Mx hMx hx => (hb x 0 Mx 0 hMx le_rfl zero_le_one hx (fun _ => by simp)).1⟩
  choose Cp hCp_pos Dp hCp using hpd_b
  let Dmax : ℕ := max D ((Finset.univ : Finset (Fin (r + 1))).sup Dp)
  let Cp_sum : ℝ := (∑ j : Fin (r + 1), Cp j) + 1
  have hCp_sum_pos : 0 < Cp_sum := by
    have : 0 ≤ ∑ j : Fin (r + 1), Cp j := Finset.sum_nonneg fun j _ => (hCp_pos j).le
    linarith
  let Kδ : ℝ := (‖τ0‖ + 1) * C_L + C_err
  have hKδ_pos : 0 < Kδ := by positivity
  obtain ⟨C_small, hC_small, U_small, hU_small1, hsmall⟩ := exists_bound_pow_mul_exp_neg Kδ hKδ_pos A 1
  let U0 : ℝ := max (max u1 U_small) (C_small + 1)
  have hU0_ge1 : 1 ≤ U0 := le_trans hU_small1 (le_trans (le_max_right _ _) (le_max_left _ _))
  let Mx_coeff : ℝ := CH + 1
  have hMx_coeff_ge1 : 1 ≤ Mx_coeff := by linarith
  let C_fin : ℝ := (C2 * Mx_coeff ^ D * Kδ ^ 2 + Cp_sum * Mx_coeff ^ Dmax * C_err) / (2 * Real.pi)
  have hC_fin_pos : 0 < C_fin := by positivity
  let B_fin : ℕ := A * Dmax + 2 * A
  have hmain_exp : ∀ u ≥ U0,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) (D1Op Q)‖ ≤
        C_fin * u ^ B_fin * Real.exp (-u) := by
    intro u hu
    have hu1 : 1 ≤ u := le_trans hU0_ge1 hu
    have hu_u1 : u1 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
    have hu_Us : U_small ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
    have hu_Cs : C_small + 1 ≤ u := le_trans (le_max_right _ _) hu
    let x : Fin (r + 1) → ℂ := fun j => iteratedDeriv (j : ℕ) H_plus u
    let δ : Fin (r + 1) → ℂ := fun j => iteratedDeriv (j : ℕ) H_minus u - iteratedDeriv (j : ℕ) H_plus u
    have hx_add_δ : x + δ = fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u := by
      ext j; simp [x, δ]
    let Mx : ℝ := Mx_coeff * u ^ A
    have hMx_ge1 : 1 ≤ Mx := by
      have : 1 ≤ u ^ A := one_le_pow₀ hu1
      nlinarith
    have hx_b : ∀ j : Fin (r + 1), ‖x j‖ ≤ Mx := fun j => by
      have := hHbound j u hu1
      have : 0 ≤ u ^ A := pow_nonneg (by linarith) A
      dsimp only [x, Mx, Mx_coeff]; nlinarith
    let Mδ : ℝ := Kδ * u ^ A * Real.exp (-u)
    have hMδ_nn : 0 ≤ Mδ := by positivity
    have hMδ_le1 : Mδ ≤ 1 := by
      have h1 := hsmall u hu_Us
      rw [pow_one] at h1
      have h2 : C_small / u ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith
    have hδ_b : ∀ j : Fin (r + 1), ‖δ j‖ ≤ Mδ := fun j => by
      have hd1 := hdiff_bound u hu_u1 j
      have hL1 := hL_bound u hu1 j
      have hexp_le : Real.exp (-2 * u) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
      have hnorm_e : ‖Complex.exp (-(u : ℂ))‖ = Real.exp (-u) := by
        rw [Complex.norm_exp]; simp
      have hsplit : δ j = (δ j - τ0 * Complex.exp (-(u : ℂ)) * Ljet u j) +
          τ0 * Complex.exp (-(u : ℂ)) * Ljet u j := by ring
      rw [hsplit]
      calc
        ‖_ + _‖ ≤ ‖δ j - τ0 * Complex.exp (-(u : ℂ)) * Ljet u j‖ +
            ‖τ0 * Complex.exp (-(u : ℂ)) * Ljet u j‖ := norm_add_le _ _
        _ ≤ C_err * u ^ A * Real.exp (-2 * u) + ‖τ0‖ * Real.exp (-u) * (C_L * u ^ A) := by
            refine add_le_add hd1 ?_
            rw [norm_mul, norm_mul, hnorm_e]
            exact mul_le_mul_of_nonneg_left hL1 (by positivity)
        _ ≤ C_err * u ^ A * Real.exp (-u) + (‖τ0‖ + 1) * C_L * u ^ A * Real.exp (-u) := by
            have h1 : C_err * u ^ A * Real.exp (-2 * u) ≤ C_err * u ^ A * Real.exp (-u) :=
              mul_le_mul_of_nonneg_left hexp_le (by positivity)
            have h2 : ‖τ0‖ * Real.exp (-u) * (C_L * u ^ A) ≤ (‖τ0‖ + 1) * C_L * u ^ A * Real.exp (-u) := by
              nlinarith [Real.exp_pos (-u), pow_nonneg (by linarith : (0 : ℝ) ≤ u) A]
            linarith
        _ = Mδ := by simp only [Mδ, Kδ]; ring
    have hT2 := (hQb x δ Mx Mδ hMx_ge1 hMδ_nn hMδ_le1 hx_b hδ_b).2.2
    rw [hx_add_δ, (hQ u).2, (hQ u).1, sub_zero, zero_sub, norm_neg] at hT2
    have hD1_eq : τ0 * Complex.exp (-(u : ℂ)) * MvPolynomial.eval x (D1Op Q) =
        ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j Q) *
          (τ0 * Complex.exp (-(u : ℂ)) * Ljet u j) := by
      rw [D1Op_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      have hinner :
          MvPolynomial.eval x
            (∑ s : Fin (r + 1),
              if (s : ℕ) ≤ (j : ℕ) then
                (((j : ℕ).choose (s : ℕ) : ℂ) * (-1 : ℂ) ^ ((j : ℕ) - (s : ℕ))) •
                  MvPolynomial.X s
              else 0) = Ljet u j := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs
        · rw [eval_smul_eq, MvPolynomial.eval_X]
        · simp
      rw [hinner]; ring
    have hdiff_sum :
        ‖τ0 * Complex.exp (-(u : ℂ)) * MvPolynomial.eval x (D1Op Q)‖ ≤
        C2 * Mx ^ D * Mδ ^ 2 + Cp_sum * Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u)) := by
      have hrew : τ0 * Complex.exp (-(u : ℂ)) * MvPolynomial.eval x (D1Op Q) =
          (∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j Q) * δ j) -
          (∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j Q) *
            (δ j - τ0 * Complex.exp (-(u : ℂ)) * Ljet u j)) := by
        rw [hD1_eq, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrew]
      refine (norm_sub_le _ _).trans (add_le_add hT2 ?_)
      calc
        ‖∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j Q) *
            (δ j - τ0 * Complex.exp (-(u : ℂ)) * Ljet u j)‖
          ≤ ∑ j : Fin (r + 1), ‖MvPolynomial.eval x (MvPolynomial.pderiv j Q)‖ *
              ‖δ j - τ0 * Complex.exp (-(u : ℂ)) * Ljet u j‖ := by
            have hns := norm_sum_le Finset.univ (fun j : Fin (r + 1) =>
              MvPolynomial.eval x (MvPolynomial.pderiv j Q) *
                (δ j - τ0 * Complex.exp (-(u : ℂ)) * Ljet u j))
            simpa only [norm_mul] using hns
        _ ≤ ∑ j : Fin (r + 1), (Cp j * Mx ^ Dmax) * (C_err * u ^ A * Real.exp (-2 * u)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := hCp j x Mx hMx_ge1 hx_b
            have hDp_le : Dp j ≤ Dmax := le_trans (Finset.le_sup (Finset.mem_univ j)) (le_max_right _ _)
            have h1' : ‖MvPolynomial.eval x (MvPolynomial.pderiv j Q)‖ ≤ Cp j * Mx ^ Dmax :=
              h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hMx_ge1 hDp_le) (hCp_pos j).le)
            have h1'_nn : 0 ≤ Cp j * Mx ^ Dmax := mul_nonneg (hCp_pos j).le (by positivity)
            exact mul_le_mul h1' (hdiff_bound u hu_u1 j) (norm_nonneg _) h1'_nn
        _ = (∑ j : Fin (r + 1), Cp j) * Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u)) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
        _ ≤ Cp_sum * Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u)) := by
            have hle : ∑ j : Fin (r + 1), Cp j ≤ Cp_sum := by linarith
            have hnn : 0 ≤ Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u)) := by positivity
            calc
              _ = (∑ j : Fin (r + 1), Cp j) *
                    (Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u))) := by ring
              _ ≤ Cp_sum * (Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u))) :=
                  mul_le_mul_of_nonneg_right hle hnn
              _ = Cp_sum * Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u)) := by ring
    have hnorm_τ0 : ‖τ0‖ = 2 * Real.pi := by
      simp only [τ0, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    have hnorm_e : ‖Complex.exp (-(u : ℂ))‖ = Real.exp (-u) := by
      rw [Complex.norm_exp]; simp
    rw [norm_mul, norm_mul, hnorm_τ0, hnorm_e] at hdiff_sum
    have hMδ2 : Mδ ^ 2 = Kδ ^ 2 * u ^ (2 * A) * Real.exp (-2 * u) := by
      have hexp2 : Real.exp (-u) ^ 2 = Real.exp (-2 * u) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      simp only [Mδ]; rw [mul_pow, mul_pow, hexp2, ← pow_mul]; ring
    have hD_le : D ≤ Dmax := le_max_left _ _
    have hMxD : Mx ^ D = Mx_coeff ^ D * u ^ (A * D) := by
      simp only [Mx]; rw [mul_pow, ← pow_mul]
    have hMxDmax : Mx ^ Dmax = Mx_coeff ^ Dmax * u ^ (A * Dmax) := by
      simp only [Mx]; rw [mul_pow, ← pow_mul]
    have hu_pow1 : u ^ (A * D) * u ^ (2 * A) ≤ u ^ B_fin := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hu1 (by dsimp [B_fin]; nlinarith)
    have hu_pow2 : u ^ (A * Dmax) * u ^ A ≤ u ^ B_fin := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hu1 (by dsimp [B_fin]; omega)
    have hRHS_le :
        C2 * Mx ^ D * Mδ ^ 2 + Cp_sum * Mx ^ Dmax * (C_err * u ^ A * Real.exp (-2 * u)) ≤
        (2 * Real.pi * Real.exp (-u)) * (C_fin * u ^ B_fin * Real.exp (-u)) := by
      have hexp_sq : Real.exp (-u) * Real.exp (-u) = Real.exp (-2 * u) := by
        rw [← Real.exp_add]; congr 1; ring
      have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      rw [hMδ2, hMxD, hMxDmax]
      have hterm1 : C2 * (Mx_coeff ^ D * u ^ (A * D)) * (Kδ ^ 2 * u ^ (2 * A) * Real.exp (-2 * u)) ≤
          C2 * Mx_coeff ^ D * Kδ ^ 2 * u ^ B_fin * Real.exp (-2 * u) := by
        have : C2 * (Mx_coeff ^ D * u ^ (A * D)) * (Kδ ^ 2 * u ^ (2 * A) * Real.exp (-2 * u)) =
            (C2 * Mx_coeff ^ D * Kδ ^ 2 * Real.exp (-2 * u)) * (u ^ (A * D) * u ^ (2 * A)) := by ring
        rw [this]
        calc _ ≤ (C2 * Mx_coeff ^ D * Kδ ^ 2 * Real.exp (-2 * u)) * u ^ B_fin :=
              mul_le_mul_of_nonneg_left hu_pow1 (by positivity)
          _ = C2 * Mx_coeff ^ D * Kδ ^ 2 * u ^ B_fin * Real.exp (-2 * u) := by ring
      have hterm2 : Cp_sum * (Mx_coeff ^ Dmax * u ^ (A * Dmax)) * (C_err * u ^ A * Real.exp (-2 * u)) ≤
          Cp_sum * Mx_coeff ^ Dmax * C_err * u ^ B_fin * Real.exp (-2 * u) := by
        have : Cp_sum * (Mx_coeff ^ Dmax * u ^ (A * Dmax)) * (C_err * u ^ A * Real.exp (-2 * u)) =
            (Cp_sum * Mx_coeff ^ Dmax * C_err * Real.exp (-2 * u)) * (u ^ (A * Dmax) * u ^ A) := by ring
        rw [this]
        calc _ ≤ (Cp_sum * Mx_coeff ^ Dmax * C_err * Real.exp (-2 * u)) * u ^ B_fin :=
              mul_le_mul_of_nonneg_left hu_pow2 (by positivity)
          _ = Cp_sum * Mx_coeff ^ Dmax * C_err * u ^ B_fin * Real.exp (-2 * u) := by ring
      have hcomb :
          (2 * Real.pi * Real.exp (-u)) * (C_fin * u ^ B_fin * Real.exp (-u)) =
          (C2 * Mx_coeff ^ D * Kδ ^ 2 + Cp_sum * Mx_coeff ^ Dmax * C_err) *
            u ^ B_fin * Real.exp (-2 * u) := by
        dsimp only [C_fin]
        calc
          2 * Real.pi * Real.exp (-u) *
              ((C2 * Mx_coeff ^ D * Kδ ^ 2 + Cp_sum * Mx_coeff ^ Dmax * C_err) / (2 * Real.pi) *
                u ^ B_fin * Real.exp (-u))
            = (2 * Real.pi * ((C2 * Mx_coeff ^ D * Kδ ^ 2 + Cp_sum * Mx_coeff ^ Dmax * C_err) /
                (2 * Real.pi))) * u ^ B_fin * (Real.exp (-u) * Real.exp (-u)) := by ring
          _ = (C2 * Mx_coeff ^ D * Kδ ^ 2 + Cp_sum * Mx_coeff ^ Dmax * C_err) *
                u ^ B_fin * Real.exp (-2 * u) := by rw [mul_div_cancel₀ _ hpi_ne, hexp_sq]
      linarith
    exact le_of_mul_le_mul_left (hdiff_sum.trans hRHS_le) (by positivity)
  intro N
  obtain ⟨C', hC', U', _, hU'⟩ := exists_bound_pow_mul_exp_neg C_fin hC_fin_pos B_fin N
  refine ⟨C', hC', max U0 U', fun u hu => ?_⟩
  exact (hmain_exp u (le_trans (le_max_left _ _) hu)).trans (hU' u (le_trans (le_max_right _ _) hu))

/-- **Step 3 (`strong_induction_Lm_eq_zero`)**: If `P` is a minimal-degree nonzero annihilator
vanishing on `H_+`, `H_-`, and `H̃`, then for every `M ≥ 2` with `c M ≠ 0`, `LmOp M P = 0`. -/
theorem strong_induction_Lm_eq_zero {r : ℕ}
    {H_plus H_minus : ℝ → ℂ} (hHp : ContDiff ℝ ⊤ H_plus)
    {c : ℕ → ℂ} {Cc ρ : ℝ} (hCc : 0 < Cc) (hρ : 0 < ρ)
    (hc : ∀ m, 2 ≤ m → ‖c m‖ ≤ Cc * ρ ^ m)
    {u_stokes : ℝ}
    (hstokes : ∀ u ≥ u_stokes,
      H_minus u = Y H_plus (2 * Real.pi * I) u +
        ∑' m : ℕ, c (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))))
    {CH : ℝ} {A : ℕ} (hCH : 0 < CH)
    (hHbound : ∀ j : Fin (r + 1), ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv (j : ℕ) H_plus u‖ ≤ CH * u ^ A)
    (hbridge : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) Q = 0))
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP_deg : 0 < P.totalDegree)
    (hP_min : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ, Q.totalDegree < P.totalDegree →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) Q = 0) →
      Q = 0)
    (hP_vanish : ∀ u : ℝ,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) P = 0 ∧
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) P = 0)
    (hP_tilde : ∀ u : ℝ, F_eval P H_plus u (2 * Real.pi * I) = 0) :
    ∀ M : ℕ, 2 ≤ M → c M ≠ 0 → LmOp M P = 0 := by
  let τ0 : ℂ := 2 * Real.pi * I
  intro M
  induction M using Nat.strong_induction_on with
  | ind M ih =>
    intro hM2 hcM
    apply hP_min (LmOp M P) (LmOp_totalDegree_lt M P hP_deg)
    apply hbridge
    let u1 : ℝ := max (max u_stokes (Real.log (2 * ρ) + 1)) 1 + 1
    have hshift_zero : ∀ u ≥ u1,
        MvPolynomial.eval (fun j : Fin (r + 1) =>
          iteratedDeriv (j : ℕ) (Y H_plus τ0) u +
          ∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
            Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))) P = 0 := by
      intro u hu
      have hu_st : u_stokes < u := by
        have : u_stokes ≤ max (max u_stokes (Real.log (2 * ρ) + 1)) 1 :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        linarith
      have hu_log : Real.log (2 * ρ) + 1 < u := by
        have : Real.log (2 * ρ) + 1 ≤ max (max u_stokes (Real.log (2 * ρ) + 1)) 1 :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        linarith
      have hHminus_eq : ∀ j : Fin (r + 1),
          iteratedDeriv (j : ℕ) H_minus u =
            (iteratedDeriv (j : ℕ) (Y H_plus τ0) u +
              ∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
                Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))) +
            ∑ k ∈ Finset.range (M - 2),
              c (k + 2) * Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ))) *
                (-(((k + 2 : ℕ) : ℂ))) ^ (j : ℕ) := by
        intro j
        have hloc : H_minus =ᶠ[𝓝 u] fun x => Y H_plus τ0 x +
            ∑' m : ℕ, c (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (x : ℂ))) := by
          filter_upwards [Ioi_mem_nhds hu_st] with x hx
          exact hstokes x (le_of_lt hx)
        rw [hloc.iteratedDeriv_eq (j : ℕ)]
        have hYsmooth : ContDiff ℝ ⊤ (Y H_plus τ0) := (contDiff_expTau τ0).mul hHp
        rw [iteratedDeriv_add_eta hYsmooth hCc hρ hc (j : ℕ) u hu_log]
        have hsum_j : Summable (fun m : ℕ => c (m + 2) * (-(((m + 2 : ℕ) : ℂ))) ^ (j : ℕ) *
            Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ)))) :=
          (summable_tail_exp hCc hρ hc (j : ℕ) u (le_of_lt hu_log)).of_norm
        rw [← hsum_j.sum_add_tsum_nat_add (M - 2)]
        have htail_eq :
            (∑' m : ℕ, c (m + (M - 2) + 2) * (-(((m + (M - 2) + 2 : ℕ) : ℂ))) ^ (j : ℕ) *
              Complex.exp (-(((m + (M - 2) + 2 : ℕ) : ℂ) * (u : ℂ)))) =
            ∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
              Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ))) := by
          congr 1; ext m
          have hm : m + (M - 2) + 2 = m + M := by omega
          simp only [hm]
        rw [htail_eq]
        have hfin_eq :
            (∑ k ∈ Finset.range (M - 2),
              c (k + 2) * (-(((k + 2 : ℕ) : ℂ))) ^ (j : ℕ) *
                Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ)))) =
            ∑ k ∈ Finset.range (M - 2),
              c (k + 2) * Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ))) *
                (-(((k + 2 : ℕ) : ℂ))) ^ (j : ℕ) :=
          Finset.sum_congr rfl fun k _ => by ring
        rw [hfin_eq]; ring
      have hpeel : ∀ K : ℕ, K ≤ M - 2 →
          ∀ x0 : Fin (r + 1) → ℂ,
            MvPolynomial.eval (fun j : Fin (r + 1) =>
              x0 j + ∑ k ∈ Finset.range K,
                c (k + 2) * Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ))) *
                  (-(((k + 2 : ℕ) : ℂ))) ^ (j : ℕ)) P =
            MvPolynomial.eval x0 P := by
        intro K
        induction K with
        | zero => intro _ x0; simp
        | succ K ihK =>
          intro hK x0
          have hK_lt : K + 2 < M := by omega
          have hstep :
              (fun j : Fin (r + 1) =>
                x0 j + ∑ k ∈ Finset.range (K + 1),
                  c (k + 2) * Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ))) *
                    (-(((k + 2 : ℕ) : ℂ))) ^ (j : ℕ)) =
              fun j : Fin (r + 1) =>
                (x0 j + ∑ k ∈ Finset.range K,
                  c (k + 2) * Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ))) *
                    (-(((k + 2 : ℕ) : ℂ))) ^ (j : ℕ)) +
                (c (K + 2) * Complex.exp (-(((K + 2 : ℕ) : ℂ) * (u : ℂ)))) *
                  (-(((K + 2 : ℕ) : ℂ))) ^ (j : ℕ) := by
            ext j; rw [Finset.sum_range_succ]; ring
          rw [hstep]
          by_cases hcK : c (K + 2) = 0
          · simp only [hcK, zero_mul, add_zero]
            exact ihK (by omega) x0
          · have hLmK : LmOp (K + 2) P = 0 := ih (K + 2) hK_lt (by omega) hcK
            rw [eval_add_smul_eq_of_LmOp_eq_zero (K + 2) P hLmK]
            exact ihK (by omega) x0
      have h0 := (hP_vanish u).2
      have hfun : (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) =
          fun j : Fin (r + 1) =>
            (iteratedDeriv (j : ℕ) (Y H_plus τ0) u +
              ∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
                Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))) +
            ∑ k ∈ Finset.range (M - 2),
              c (k + 2) * Complex.exp (-(((k + 2 : ℕ) : ℂ) * (u : ℂ))) *
                (-(((k + 2 : ℕ) : ℂ))) ^ (j : ℕ) :=
        funext hHminus_eq
      rw [hfun, hpeel (M - 2) le_rfl] at h0
      exact h0
    have hexp_b : ∀ n : ℕ, ∃ Ke > 0, ∀ u : ℝ, 1 ≤ u →
        ‖iteratedDeriv n (expTau τ0) u - (if n = 0 then (1 : ℂ) else 0)‖ ≤ Ke * Real.exp (-u) := by
      intro n
      obtain ⟨Ke0, hKe0, hKe0b⟩ := norm_iteratedDeriv_expTau_sub_le n τ0
      refine ⟨Ke0 + ‖τ0‖, by positivity, fun u hu => ?_⟩
      have h1 := hKe0b u hu
      have hexp_le : Real.exp (-2 * u) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
      have hne : ‖Complex.exp (-(u : ℂ))‖ = Real.exp (-u) := by rw [Complex.norm_exp]; simp
      cases n with
      | zero =>
        simp only [↓reduceIte] at h1 ⊢
        have hrew : iteratedDeriv 0 (expTau τ0) u - 1 =
            (iteratedDeriv 0 (expTau τ0) u - (1 + τ0 * Complex.exp (-(u : ℂ)))) +
              τ0 * Complex.exp (-(u : ℂ)) := by ring
        rw [hrew]
        calc ‖_ + _‖ ≤ ‖_‖ + ‖τ0 * Complex.exp (-(u : ℂ))‖ := norm_add_le _ _
          _ ≤ Ke0 * Real.exp (-2 * u) + ‖τ0‖ * Real.exp (-u) := by
              rw [norm_mul, hne]; exact add_le_add h1 le_rfl
          _ ≤ (Ke0 + ‖τ0‖) * Real.exp (-u) := by nlinarith
      | succ n =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, sub_zero] at h1 ⊢
        have hrew : iteratedDeriv (n + 1) (expTau τ0) u =
            (iteratedDeriv (n + 1) (expTau τ0) u - τ0 * (-1 : ℂ) ^ (n + 1) * Complex.exp (-(u : ℂ))) +
              τ0 * (-1 : ℂ) ^ (n + 1) * Complex.exp (-(u : ℂ)) := by ring
        rw [hrew]
        calc ‖_ + _‖ ≤ ‖_‖ + ‖τ0 * (-1 : ℂ) ^ (n + 1) * Complex.exp (-(u : ℂ))‖ := norm_add_le _ _
          _ ≤ Ke0 * Real.exp (-2 * u) + ‖τ0‖ * Real.exp (-u) := by
              rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, hne]
              exact add_le_add h1 le_rfl
          _ ≤ (Ke0 + ‖τ0‖) * Real.exp (-u) := by nlinarith
    choose Ke1 hKe1_pos hKe1 using hexp_b
    let C_td : ℝ := (∑ j : Fin (r + 1), ∑ s ∈ Finset.range ((j : ℕ) + 1),
      ((j : ℕ).choose s : ℝ) * Ke1 ((j : ℕ) - s) * CH) + 1
    have hC_td_pos : 0 < C_td := by
      have : 0 ≤ ∑ j : Fin (r + 1), ∑ s ∈ Finset.range ((j : ℕ) + 1),
          ((j : ℕ).choose s : ℝ) * Ke1 ((j : ℕ) - s) * CH :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKe1_pos _).le) hCH.le
      linarith
    have htilde_diff : ∀ u : ℝ, 1 ≤ u → ∀ j : Fin (r + 1),
        ‖iteratedDeriv (j : ℕ) (Y H_plus τ0) u - iteratedDeriv (j : ℕ) H_plus u‖ ≤
          C_td * u ^ A * Real.exp (-u) := by
      intro u hu j
      rw [iteratedDeriv_Y_eq hHp (j : ℕ) τ0 u]
      have hsub :
          (∑ s ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose s : ℂ) * iteratedDeriv ((j : ℕ) - s) (expTau τ0) u *
              iteratedDeriv s H_plus u) - iteratedDeriv (j : ℕ) H_plus u =
          ∑ s ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose s : ℂ) *
              (iteratedDeriv ((j : ℕ) - s) (expTau τ0) u -
                (if (j : ℕ) - s = 0 then (1 : ℂ) else 0)) *
              iteratedDeriv s H_plus u := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul, ↓reduceIte]
        have hmid :
            (∑ x ∈ Finset.range (j : ℕ),
              ((j : ℕ).choose x : ℂ) * iteratedDeriv ((j : ℕ) - x) (expTau τ0) u *
                iteratedDeriv x H_plus u) =
            ∑ x ∈ Finset.range (j : ℕ),
              ((j : ℕ).choose x : ℂ) *
                (iteratedDeriv ((j : ℕ) - x) (expTau τ0) u -
                  (if (j : ℕ) - x = 0 then (1 : ℂ) else 0)) *
                iteratedDeriv x H_plus u := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxj : x < (j : ℕ) := Finset.mem_range.mp hx
          have hne : (j : ℕ) - x ≠ 0 := by omega
          simp [hne]
        rw [hmid]; ring
      rw [hsub]
      calc
        ‖∑ s ∈ Finset.range ((j : ℕ) + 1), _‖
          ≤ ∑ s ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose s : ℝ) * (Ke1 ((j : ℕ) - s) * Real.exp (-u)) * (CH * u ^ A) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
            have hsj : s ≤ (j : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
            let sFin : Fin (r + 1) := ⟨s, lt_of_le_of_lt hsj j.isLt⟩
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            have hnn : 0 ≤ ((j : ℕ).choose s : ℝ) * (Ke1 ((j : ℕ) - s) * Real.exp (-u)) :=
              mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKe1_pos _).le (Real.exp_pos _).le)
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hKe1 ((j : ℕ) - s) u hu) (Nat.cast_nonneg _))
              (hHbound sFin u hu) (norm_nonneg _) hnn
        _ = (∑ s ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose s : ℝ) * Ke1 ((j : ℕ) - s) * CH) * u ^ A * Real.exp (-u) := by
            rw [Finset.sum_mul, Finset.sum_mul]; refine Finset.sum_congr rfl fun s _ => by ring
        _ ≤ C_td * u ^ A * Real.exp (-u) := by
            have hle : (∑ s ∈ Finset.range ((j : ℕ) + 1),
                ((j : ℕ).choose s : ℝ) * Ke1 ((j : ℕ) - s) * CH) ≤ C_td := by
              have h1 := Finset.single_le_sum
                (f := fun j' : Fin (r + 1) => ∑ s ∈ Finset.range ((j' : ℕ) + 1),
                  ((j' : ℕ).choose s : ℝ) * Ke1 ((j' : ℕ) - s) * CH)
                (fun j' _ => Finset.sum_nonneg fun s _ =>
                  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKe1_pos _).le) hCH.le)
                (Finset.mem_univ j)
              linarith
            have hnn : 0 ≤ u ^ A * Real.exp (-u) := by positivity
            calc
              _ = (∑ s ∈ Finset.range ((j : ℕ) + 1),
                    ((j : ℕ).choose s : ℝ) * Ke1 ((j : ℕ) - s) * CH) * (u ^ A * Real.exp (-u)) := by ring
              _ ≤ C_td * (u ^ A * Real.exp (-u)) := mul_le_mul_of_nonneg_right hle hnn
              _ = C_td * u ^ A * Real.exp (-u) := by ring
    have htail_M : ∀ j : Fin (r + 1), ∃ KM > 0, ∀ u : ℝ, Real.log (2 * ρ) + 1 ≤ u →
        ‖∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
          Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))‖ ≤ KM * Real.exp (-(M : ℝ) * u) :=
      fun j => norm_tsum_tail_le hCc hρ hc (j : ℕ) M hM2
    choose KM hKM_pos hKM using htail_M
    have htail_M1 : ∀ j : Fin (r + 1), ∃ KM1 > 0, ∀ u : ℝ, Real.log (2 * ρ) + 1 ≤ u →
        ‖∑' m : ℕ, c (m + (M + 1)) * (-(((m + (M + 1) : ℕ) : ℂ))) ^ (j : ℕ) *
          Complex.exp (-(((m + (M + 1) : ℕ) : ℂ) * (u : ℂ)))‖ ≤
          KM1 * Real.exp (-((M + 1 : ℕ) : ℝ) * u) :=
      fun j => norm_tsum_tail_le hCc hρ hc (j : ℕ) (M + 1) (by omega)
    choose KM1 hKM1_pos hKM1 using htail_M1
    let KM_tot : ℝ := (∑ j : Fin (r + 1), KM j) + 1
    let KM1_tot : ℝ := (∑ j : Fin (r + 1), KM1 j) + 1
    have hKM_tot_pos : 0 < KM_tot := by
      have : 0 ≤ ∑ j : Fin (r + 1), KM j := Finset.sum_nonneg fun j _ => (hKM_pos j).le
      linarith
    have hKM1_tot_pos : 0 < KM1_tot := by
      have : 0 ≤ ∑ j : Fin (r + 1), KM1 j := Finset.sum_nonneg fun j _ => (hKM1_pos j).le
      linarith
    obtain ⟨C0, C1, C2, D, hC0, hC1, hC2, hPb⟩ := mvPolynomial_bounds P
    obtain ⟨CL0, CL1, CL2, DL, hCL0, hCL1, hCL2, hLb⟩ := mvPolynomial_bounds (LmOp M P)
    have hpd_b : ∀ j : Fin (r + 1), ∃ Cp > 0, ∃ Dp : ℕ, ∀ (x : Fin (r + 1) → ℂ) (Mx : ℝ),
        1 ≤ Mx → (∀ k, ‖x k‖ ≤ Mx) → ‖MvPolynomial.eval x (MvPolynomial.pderiv j P)‖ ≤ Cp * Mx ^ Dp := by
      intro j
      obtain ⟨c0, _, _, d0, hc0, _, _, hb⟩ := mvPolynomial_bounds (MvPolynomial.pderiv j P)
      exact ⟨c0, hc0, d0, fun x Mx hMx hx => (hb x 0 Mx 0 hMx le_rfl zero_le_one hx (fun _ => by simp)).1⟩
    choose Cp hCp_pos Dp hCp using hpd_b
    let Dmax : ℕ := max (max D DL) ((Finset.univ : Finset (Fin (r + 1))).sup Dp)
    let Cp_sum : ℝ := (∑ j : Fin (r + 1), Cp j) + 1
    have hCp_sum_pos : 0 < Cp_sum := by
      have : 0 ≤ ∑ j : Fin (r + 1), Cp j := Finset.sum_nonneg fun j _ => (hCp_pos j).le
      linarith
    obtain ⟨C_td_s, hC_td_s, U_td, hU_td1, htd_small⟩ :=
      exists_bound_pow_mul_exp_neg C_td hC_td_pos A 1
    let U0 : ℝ := max (max (max u1 U_td) (C_td_s + 1)) (Real.log KM_tot + 1)
    have hU0_ge1 : 1 ≤ U0 :=
      le_trans hU_td1 (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
    let Mx_coeff : ℝ := CH + 2
    have hMx_coeff_ge1 : 1 ≤ Mx_coeff := by linarith
    let C_Lm : ℝ :=
      (C2 * Mx_coeff ^ D * KM_tot ^ 2 + Cp_sum * Mx_coeff ^ Dmax * KM1_tot) / ‖c M‖ +
        CL1 * Mx_coeff ^ DL * C_td
    have hcM_pos : 0 < ‖c M‖ := norm_pos_iff.mpr hcM
    have hC_Lm_pos : 0 < C_Lm := by positivity
    let B_Lm : ℕ := A * Dmax + A
    have hmain_Lm : ∀ u ≥ U0,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) (LmOp M P)‖ ≤
          C_Lm * u ^ B_Lm * Real.exp (-u) := by
      intro u hu
      have hu1 : 1 ≤ u := le_trans hU0_ge1 hu
      have hu_u1 : u1 ≤ u :=
        le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hu))
      have hu_Utd : U_td ≤ u :=
        le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hu))
      have hu_Ctd : C_td_s + 1 ≤ u :=
        le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hu)
      have hu_KM : Real.log KM_tot + 1 ≤ u := le_trans (le_max_right _ _) hu
      have hu_log : Real.log (2 * ρ) + 1 ≤ u := by
        have : Real.log (2 * ρ) + 1 ≤ max (max u_stokes (Real.log (2 * ρ) + 1)) 1 :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        linarith
      let xH : Fin (r + 1) → ℂ := fun j => iteratedDeriv (j : ℕ) H_plus u
      let xT : Fin (r + 1) → ℂ := fun j => iteratedDeriv (j : ℕ) (Y H_plus τ0) u
      let vM : Fin (r + 1) → ℂ := fun j =>
        ∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
          Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))
      let Mx : ℝ := Mx_coeff * u ^ A
      have hMx_ge1 : 1 ≤ Mx := by
        have : 1 ≤ u ^ A := one_le_pow₀ hu1
        nlinarith
      have htd_le1 : C_td * u ^ A * Real.exp (-u) ≤ 1 := by
        have h1 := htd_small u hu_Utd
        rw [pow_one] at h1
        have h2 : C_td_s / u ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      have hxH_b : ∀ j : Fin (r + 1), ‖xH j‖ ≤ Mx := fun j => by
        have := hHbound j u hu1
        have : 0 ≤ u ^ A := pow_nonneg (by linarith) A
        dsimp only [xH, Mx, Mx_coeff]; nlinarith
      have hxT_b : ∀ j : Fin (r + 1), ‖xT j‖ ≤ Mx := fun j => by
        have h1 := htilde_diff u hu1 j
        have h2 := hHbound j u hu1
        have hrew : xT j = (xT j - xH j) + xH j := by ring
        rw [hrew]
        have huA1 : 1 ≤ u ^ A := one_le_pow₀ hu1
        calc ‖(xT j - xH j) + xH j‖ ≤ ‖xT j - xH j‖ + ‖xH j‖ := norm_add_le _ _
          _ ≤ 1 + CH * u ^ A := add_le_add (h1.trans htd_le1) h2
          _ ≤ (CH + 2) * u ^ A := by nlinarith
      let Mv : ℝ := KM_tot * Real.exp (-(M : ℝ) * u)
      have hMv_nn : 0 ≤ Mv := by positivity
      have hMv_le1 : Mv ≤ 1 := by
        have h1 : KM_tot ≤ Real.exp u := by
          calc KM_tot = Real.exp (Real.log KM_tot) := (Real.exp_log hKM_tot_pos).symm
            _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
        have h2 : Real.exp (-(M : ℝ) * u) ≤ Real.exp (-u) := by
          refine Real.exp_le_exp.mpr ?_
          have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
          nlinarith
        calc Mv ≤ Real.exp u * Real.exp (-u) := mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; simp
      have hvM_b : ∀ j : Fin (r + 1), ‖vM j‖ ≤ Mv := fun j => by
        have h1 := hKM j u hu_log
        have hle : KM j ≤ KM_tot := by
          have := Finset.single_le_sum (fun j' _ => (hKM_pos j').le) (Finset.mem_univ j)
          linarith
        exact h1.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)
      have hT2 := (hPb xT vM Mx Mv hMx_ge1 hMv_nn hMv_le1 hxT_b hvM_b).2.2
      have hP_xTvM : MvPolynomial.eval (xT + vM) P = 0 := hshift_zero u hu_u1
      have hP_xT : MvPolynomial.eval xT P = 0 := hP_tilde u
      rw [hP_xTvM, hP_xT, sub_zero, zero_sub, norm_neg] at hT2
      have hvM_split : ∀ j : Fin (r + 1),
          vM j - c M * (-((M : ℂ))) ^ (j : ℕ) * Complex.exp (-((M : ℂ) * (u : ℂ))) =
          ∑' m : ℕ, c (m + (M + 1)) * (-(((m + (M + 1) : ℕ) : ℂ))) ^ (j : ℕ) *
            Complex.exp (-(((m + (M + 1) : ℕ) : ℂ) * (u : ℂ))) := by
        intro j
        have hsum_v : Summable (fun m : ℕ => c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
            Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))) := by
          have hinj : Function.Injective (fun m : ℕ => m + (M - 2)) := fun _ _ h => Nat.add_right_cancel h
          have h1 := ((summable_tail_exp hCc hρ hc (j : ℕ) u hu_log).of_norm).comp_injective hinj
          refine h1.congr fun m => ?_
          have hm : m + (M - 2) + 2 = m + M := by omega
          simp only [Function.comp_apply, hm]
        change (∑' m : ℕ, c (m + M) * (-(((m + M : ℕ) : ℂ))) ^ (j : ℕ) *
            Complex.exp (-(((m + M : ℕ) : ℂ) * (u : ℂ)))) - _ = _
        rw [← hsum_v.sum_add_tsum_nat_add 1]
        simp only [Finset.sum_range_one, zero_add, add_sub_cancel_left]
        congr 1; ext m
        have hm : m + 1 + M = m + (M + 1) := by omega
        simp only [hm]
      have hLm_eq : c M * Complex.exp (-((M : ℂ) * (u : ℂ))) * MvPolynomial.eval xT (LmOp M P) =
          ∑ j : Fin (r + 1), MvPolynomial.eval xT (MvPolynomial.pderiv j P) *
            (c M * (-((M : ℂ))) ^ (j : ℕ) * Complex.exp (-((M : ℂ) * (u : ℂ)))) := by
        rw [LmOp_apply, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [eval_smul_eq]; ring
      have hLm_xT_bound :
          ‖c M * Complex.exp (-((M : ℂ) * (u : ℂ))) * MvPolynomial.eval xT (LmOp M P)‖ ≤
          C2 * Mx ^ D * Mv ^ 2 + Cp_sum * Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by
        have hrew : c M * Complex.exp (-((M : ℂ) * (u : ℂ))) * MvPolynomial.eval xT (LmOp M P) =
            (∑ j : Fin (r + 1), MvPolynomial.eval xT (MvPolynomial.pderiv j P) * vM j) -
            (∑ j : Fin (r + 1), MvPolynomial.eval xT (MvPolynomial.pderiv j P) *
              (vM j - c M * (-((M : ℂ))) ^ (j : ℕ) * Complex.exp (-((M : ℂ) * (u : ℂ))))) := by
          rw [hLm_eq, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hrew]
        refine (norm_sub_le _ _).trans (add_le_add hT2 ?_)
        calc
          ‖∑ j : Fin (r + 1), MvPolynomial.eval xT (MvPolynomial.pderiv j P) *
              (vM j - c M * (-((M : ℂ))) ^ (j : ℕ) * Complex.exp (-((M : ℂ) * (u : ℂ))))‖
            ≤ ∑ j : Fin (r + 1), ‖MvPolynomial.eval xT (MvPolynomial.pderiv j P)‖ *
                ‖vM j - c M * (-((M : ℂ))) ^ (j : ℕ) * Complex.exp (-((M : ℂ) * (u : ℂ)))‖ := by
              have hns := norm_sum_le Finset.univ (fun j : Fin (r + 1) =>
                MvPolynomial.eval xT (MvPolynomial.pderiv j P) *
                  (vM j - c M * (-((M : ℂ))) ^ (j : ℕ) * Complex.exp (-((M : ℂ) * (u : ℂ)))))
              simpa only [norm_mul] using hns
          _ ≤ ∑ j : Fin (r + 1), (Cp j * Mx ^ Dmax) * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have h1 := hCp j xT Mx hMx_ge1 hxT_b
              have hDp_le : Dp j ≤ Dmax :=
                le_trans (Finset.le_sup (Finset.mem_univ j)) (le_max_right _ _)
              have h1' := h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hMx_ge1 hDp_le) (hCp_pos j).le)
              have h1'_nn : 0 ≤ Cp j * Mx ^ Dmax := mul_nonneg (hCp_pos j).le (by positivity)
              rw [hvM_split j]
              have h2 := hKM1 j u hu_log
              have hle : KM1 j ≤ KM1_tot := by
                have := Finset.single_le_sum (fun j' _ => (hKM1_pos j').le) (Finset.mem_univ j)
                linarith
              exact mul_le_mul h1' (h2.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le))
                (norm_nonneg _) h1'_nn
          _ = (∑ j : Fin (r + 1), Cp j) * Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]
          _ ≤ Cp_sum * Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by
              have hle : ∑ j : Fin (r + 1), Cp j ≤ Cp_sum := by linarith
              have hnn : 0 ≤ Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by positivity
              calc
                _ = (∑ j : Fin (r + 1), Cp j) *
                      (Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u))) := by ring
                _ ≤ Cp_sum * (Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u))) :=
                    mul_le_mul_of_nonneg_right hle hnn
                _ = Cp_sum * Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) := by ring
      have hnorm_eM : ‖Complex.exp (-((M : ℂ) * (u : ℂ)))‖ = Real.exp (-(M : ℝ) * u) := by
        rw [Complex.norm_exp, re_neg_nat_mul_ofReal]; ring_nf
      rw [norm_mul, norm_mul, hnorm_eM] at hLm_xT_bound
      have hexp_M2 : Mv ^ 2 ≤ KM_tot ^ 2 * Real.exp (-(M : ℝ) * u) * Real.exp (-u) := by
        have h1 : Real.exp (-(M : ℝ) * u) ^ 2 = Real.exp (-(M : ℝ) * u) * Real.exp (-(M : ℝ) * u) := sq _
        have h2 : Real.exp (-(M : ℝ) * u) ≤ Real.exp (-u) := by
          refine Real.exp_le_exp.mpr ?_
          have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
          nlinarith
        simp only [Mv]; rw [mul_pow, h1]
        have : Real.exp (-(M : ℝ) * u) * Real.exp (-(M : ℝ) * u) ≤ Real.exp (-(M : ℝ) * u) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        nlinarith [sq_nonneg KM_tot]
      have hexp_M1 : Real.exp (-((M + 1 : ℕ) : ℝ) * u) = Real.exp (-(M : ℝ) * u) * Real.exp (-u) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hLm_xT_le :
          ‖MvPolynomial.eval xT (LmOp M P)‖ ≤
          ((C2 * Mx_coeff ^ D * KM_tot ^ 2 + Cp_sum * Mx_coeff ^ Dmax * KM1_tot) / ‖c M‖) *
            u ^ B_Lm * Real.exp (-u) := by
        have hMxD : Mx ^ D = Mx_coeff ^ D * u ^ (A * D) := by simp only [Mx]; rw [mul_pow, ← pow_mul]
        have hMxDmax : Mx ^ Dmax = Mx_coeff ^ Dmax * u ^ (A * Dmax) := by simp only [Mx]; rw [mul_pow, ← pow_mul]
        have hD_le : D ≤ Dmax := le_trans (le_max_left _ _) (le_max_left _ _)
        have hu1' : u ^ (A * D) ≤ u ^ B_Lm := pow_le_pow_right₀ hu1 (by dsimp [B_Lm]; nlinarith)
        have hu2' : u ^ (A * Dmax) ≤ u ^ B_Lm := pow_le_pow_right₀ hu1 (by dsimp [B_Lm]; omega)
        have hcomb :
            C2 * Mx ^ D * Mv ^ 2 + Cp_sum * Mx ^ Dmax * (KM1_tot * Real.exp (-((M + 1 : ℕ) : ℝ) * u)) ≤
            (‖c M‖ * Real.exp (-(M : ℝ) * u)) *
              (((C2 * Mx_coeff ^ D * KM_tot ^ 2 + Cp_sum * Mx_coeff ^ Dmax * KM1_tot) / ‖c M‖) *
                u ^ B_Lm * Real.exp (-u)) := by
          rw [hexp_M1, hMxD, hMxDmax]
          have hterm1 : C2 * (Mx_coeff ^ D * u ^ (A * D)) * Mv ^ 2 ≤
              C2 * Mx_coeff ^ D * KM_tot ^ 2 * u ^ B_Lm * (Real.exp (-(M : ℝ) * u) * Real.exp (-u)) := by
            calc C2 * (Mx_coeff ^ D * u ^ (A * D)) * Mv ^ 2
                ≤ C2 * (Mx_coeff ^ D * u ^ (A * D)) *
                    (KM_tot ^ 2 * Real.exp (-(M : ℝ) * u) * Real.exp (-u)) :=
                  mul_le_mul_of_nonneg_left hexp_M2 (by positivity)
              _ = (C2 * Mx_coeff ^ D * KM_tot ^ 2 * (Real.exp (-(M : ℝ) * u) * Real.exp (-u))) *
                    u ^ (A * D) := by ring
              _ ≤ (C2 * Mx_coeff ^ D * KM_tot ^ 2 * (Real.exp (-(M : ℝ) * u) * Real.exp (-u))) *
                    u ^ B_Lm := mul_le_mul_of_nonneg_left hu1' (by positivity)
              _ = _ := by ring
          have hterm2 : Cp_sum * (Mx_coeff ^ Dmax * u ^ (A * Dmax)) *
                (KM1_tot * (Real.exp (-(M : ℝ) * u) * Real.exp (-u))) ≤
              Cp_sum * Mx_coeff ^ Dmax * KM1_tot * u ^ B_Lm *
                (Real.exp (-(M : ℝ) * u) * Real.exp (-u)) := by
            have : Cp_sum * (Mx_coeff ^ Dmax * u ^ (A * Dmax)) *
                (KM1_tot * (Real.exp (-(M : ℝ) * u) * Real.exp (-u))) =
                (Cp_sum * Mx_coeff ^ Dmax * KM1_tot * (Real.exp (-(M : ℝ) * u) * Real.exp (-u))) *
                  u ^ (A * Dmax) := by ring
            rw [this]
            calc _ ≤ (Cp_sum * Mx_coeff ^ Dmax * KM1_tot *
                    (Real.exp (-(M : ℝ) * u) * Real.exp (-u))) * u ^ B_Lm :=
                  mul_le_mul_of_nonneg_left hu2' (by positivity)
              _ = _ := by ring
          have hcancel :
              ‖c M‖ * Real.exp (-(M : ℝ) * u) *
                ((C2 * Mx_coeff ^ D * KM_tot ^ 2 + Cp_sum * Mx_coeff ^ Dmax * KM1_tot) / ‖c M‖ *
                  u ^ B_Lm * Real.exp (-u)) =
              (C2 * Mx_coeff ^ D * KM_tot ^ 2 + Cp_sum * Mx_coeff ^ Dmax * KM1_tot) *
                u ^ B_Lm * (Real.exp (-(M : ℝ) * u) * Real.exp (-u)) := by
            calc
              _ = (‖c M‖ * ((C2 * Mx_coeff ^ D * KM_tot ^ 2 + Cp_sum * Mx_coeff ^ Dmax * KM1_tot) / ‖c M‖)) *
                    u ^ B_Lm * (Real.exp (-(M : ℝ) * u) * Real.exp (-u)) := by ring
              _ = _ := by rw [mul_div_cancel₀ _ hcM_pos.ne']
          linarith
        exact le_of_mul_le_mul_left (hLm_xT_bound.trans hcomb) (by positivity)
      have hLip := (hLb xH (xT - xH) Mx (C_td * u ^ A * Real.exp (-u))
        hMx_ge1 (by positivity) htd_le1 hxH_b (fun j => htilde_diff u hu1 j)).2.1
      have hadd_eq : xH + (xT - xH) = xT := by ext j; simp
      rw [hadd_eq] at hLip
      have hDL_le : DL ≤ Dmax := le_trans (le_max_right _ _) (le_max_left _ _)
      have hLip_le :
          ‖MvPolynomial.eval xT (LmOp M P) - MvPolynomial.eval xH (LmOp M P)‖ ≤
          CL1 * Mx_coeff ^ DL * C_td * u ^ B_Lm * Real.exp (-u) := by
        have hMxDL : Mx ^ DL = Mx_coeff ^ DL * u ^ (A * DL) := by simp only [Mx]; rw [mul_pow, ← pow_mul]
        have hu_dl : u ^ (A * DL) * u ^ A ≤ u ^ B_Lm := by
          rw [← pow_add]; exact pow_le_pow_right₀ hu1 (by dsimp [B_Lm]; nlinarith)
        calc
          ‖_‖ ≤ CL1 * (Mx_coeff ^ DL * u ^ (A * DL)) * (C_td * u ^ A * Real.exp (-u)) := by
            rwa [← hMxDL]
          _ = (CL1 * Mx_coeff ^ DL * C_td * Real.exp (-u)) * (u ^ (A * DL) * u ^ A) := by ring
          _ ≤ (CL1 * Mx_coeff ^ DL * C_td * Real.exp (-u)) * u ^ B_Lm :=
            mul_le_mul_of_nonneg_left hu_dl (by positivity)
          _ = CL1 * Mx_coeff ^ DL * C_td * u ^ B_Lm * Real.exp (-u) := by ring
      have hrew : MvPolynomial.eval xH (LmOp M P) =
          MvPolynomial.eval xT (LmOp M P) -
            (MvPolynomial.eval xT (LmOp M P) - MvPolynomial.eval xH (LmOp M P)) := by ring
      rw [hrew]
      calc
        ‖_‖ ≤ ‖MvPolynomial.eval xT (LmOp M P)‖ +
            ‖MvPolynomial.eval xT (LmOp M P) - MvPolynomial.eval xH (LmOp M P)‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add hLm_xT_le hLip_le
        _ = C_Lm * u ^ B_Lm * Real.exp (-u) := by simp only [C_Lm]; ring
    intro N
    obtain ⟨C', hC', U', _, hU'⟩ := exists_bound_pow_mul_exp_neg C_Lm hC_Lm_pos B_Lm N
    refine ⟨C', hC', max U0 U', fun u hu => ?_⟩
    exact (hmain_Lm u (le_trans (le_max_left _ _) hu)).trans (hU' u (le_trans (le_max_right _ _) hu))

/-- **Step 4 (`vandermonde_collapse_eq_const`)**: If `LmOp m P = 0` for infinitely many `m ≥ 2`,
then `P` is a constant polynomial (`P = C (P.coeff 0)`). -/
theorem vandermonde_collapse_eq_const {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hinf : {m : ℕ | 2 ≤ m ∧ LmOp m P = 0}.Infinite) :
    P = MvPolynomial.C (P.coeff 0) := by
  classical
  obtain ⟨S, hS_sub, hS_card⟩ := hinf.exists_subset_card_eq (r + 1)
  let e : Fin (r + 1) ≃ S := (Fintype.equivFinOfCardEq (by simp [hS_card])).symm
  let M : Fin (r + 1) → ℕ := fun i => (e i).val
  have hM_inj : Function.Injective M := fun i j h => e.injective (Subtype.ext h)
  let nodes : Fin (r + 1) → ℂ := fun i => -((M i : ℂ))
  have hnodes_inj : Function.Injective nodes := fun i j h => by
    apply hM_inj
    have h1 : (M i : ℂ) = (M j : ℂ) := neg_inj.mp h
    exact_mod_cast h1
  let V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.vandermonde nodes
  have hdet_ne : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    exact hnodes_inj
  have hsys : ∀ i : Fin (r + 1), ∑ j : Fin (r + 1), V i j • MvPolynomial.pderiv j P = 0 := by
    intro i
    have hmem : M i ∈ {m : ℕ | 2 ≤ m ∧ LmOp m P = 0} := hS_sub (e i).property
    have hLm : LmOp (M i) P = 0 := hmem.2
    rw [LmOp_apply] at hLm
    simpa [V, Matrix.vandermonde, nodes] using hLm
  have hpd0 : ∀ k : Fin (r + 1), MvPolynomial.pderiv k P = 0 := by
    intro k
    have hmul : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hdet_ne)
    have hsum : ∑ i : Fin (r + 1), (V⁻¹) k i • (∑ j : Fin (r + 1), V i j • MvPolynomial.pderiv j P) = 0 := by
      simp [hsys]
    simp_rw [Finset.smul_sum, smul_smul] at hsum
    rw [Finset.sum_comm] at hsum
    have hcollapse :
        (∑ j : Fin (r + 1), ∑ i : Fin (r + 1), ((V⁻¹) k i * V i j) • MvPolynomial.pderiv j P) =
        MvPolynomial.pderiv k P := by
      have hinner : ∀ j : Fin (r + 1),
          (∑ i : Fin (r + 1), ((V⁻¹) k i * V i j) • MvPolynomial.pderiv j P) =
          (if k = j then (1 : ℂ) else 0) • MvPolynomial.pderiv j P := by
        intro j
        rw [← Finset.sum_smul]
        congr 1
        have hkj := congr_fun (congr_fun hmul k) j
        simpa [Matrix.mul_apply, Matrix.one_apply] using hkj
      simp_rw [hinner]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [Ne.symm hjk]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [hcollapse] at hsum
    exact hsum
  exact all_partials_zero P hpd0

/-- **Master Theorem (`pak_nth_prime_engine_eq_zero`)**: Complete 4-step `D₁ / τ / L_M`-Vandermonde
engine! Under the exact Stokes relation `H_- = exp(2πi e^{-u}) H_+ + η`, geometric coefficient
bounds on `η`, infinitely many nonzero `c_m`, polynomial jet bounds on `H_+`, and the Log-Borel
Bridge hypothesis, any polynomial `P` vanishing on `H_+` and `H_-` must be `P = 0`. -/
theorem pak_nth_prime_engine_eq_zero {r : ℕ}
    {H_plus H_minus : ℝ → ℂ} (hHp : ContDiff ℝ ⊤ H_plus)
    {c : ℕ → ℂ} {Cc ρ : ℝ} (hCc : 0 < Cc) (hρ : 0 < ρ)
    (hc : ∀ m, 2 ≤ m → ‖c m‖ ≤ Cc * ρ ^ m)
    (hinf : {m : ℕ | 2 ≤ m ∧ c m ≠ 0}.Infinite)
    {u_stokes : ℝ}
    (hstokes : ∀ u ≥ u_stokes,
      H_minus u = Y H_plus (2 * Real.pi * I) u +
        ∑' m : ℕ, c (m + 2) * Complex.exp (-(((m + 2 : ℕ) : ℂ) * (u : ℂ))))
    {CH : ℝ} {A : ℕ} (hCH : 0 < CH)
    (hHbound : ∀ j : Fin (r + 1), ∀ u : ℝ, 1 ≤ u → ‖iteratedDeriv (j : ℕ) H_plus u‖ ≤ CH * u ^ A)
    (hbridge : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q‖ ≤ C / u ^ N) →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) Q = 0))
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ u : ℝ,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) P = 0 ∧
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) P = 0) :
    P = 0 := by
  suffices ∀ d : ℕ, ∀ Q : MvPolynomial (Fin (r + 1)) ℂ, Q.totalDegree = d →
      (∀ u : ℝ,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) Q = 0 ∧
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) Q = 0) →
      Q = 0 from this P.totalDegree P rfl hP
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro Q hdeg hQ
    by_cases hd0 : d = 0
    · have hC : Q = MvPolynomial.C (Q.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (hdeg.trans hd0)
      have h0 := (hQ 0).1
      rw [hC, MvPolynomial.eval_C] at h0
      simpa [h0] using hC
    · have hQ_deg : 0 < Q.totalDegree := by omega
      have hD1_all : ∀ k : ℕ, ∀ u : ℝ,
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_plus u) (D1Op^[k] Q) = 0 ∧
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) H_minus u) (D1Op^[k] Q) = 0 := by
        intro k
        induction k with
        | zero => exact hQ
        | succ k ihk =>
          rw [Function.iterate_succ_apply']
          exact D1_invariance hHp hCc hρ hc hstokes hCH hHbound hbridge (D1Op^[k] Q) ihk
      have hQ_tilde : ∀ u : ℝ, F_eval Q H_plus u (2 * Real.pi * I) = 0 :=
        fun u => tau_invariance_two_pi_I Q hHp u (fun k => (hD1_all k u).1)
      have hLm_all : ∀ M : ℕ, 2 ≤ M → c M ≠ 0 → LmOp M Q = 0 :=
        strong_induction_Lm_eq_zero hHp hCc hρ hc hstokes hCH hHbound hbridge Q hQ_deg
          (fun R hRdeg hR => ih R.totalDegree (hdeg ▸ hRdeg) R rfl hR) hQ hQ_tilde
      have hsub_inf : {m : ℕ | 2 ≤ m ∧ c m ≠ 0} ⊆ {m : ℕ | 2 ≤ m ∧ LmOp m Q = 0} :=
        fun m hm => ⟨hm.1, hLm_all m hm.1 hm.2⟩
      have hinf_Lm : {m : ℕ | 2 ≤ m ∧ LmOp m Q = 0}.Infinite := hinf.mono hsub_inf
      have hC : Q = MvPolynomial.C (Q.coeff 0) := vandermonde_collapse_eq_const Q hinf_Lm
      have h0 := (hQ 0).1
      rw [hC, MvPolynomial.eval_C] at h0
      simpa [h0] using hC

/-! ### 5. Unconditional Non-Polynomiality of `η(t)` & Non-Vanishing of `R(-s)` -/

/-- **Unconditional Non-Polynomiality**: If `R : ℂ → ℂ` is continuous at `-1` with `R (-1) ≠ 0`,
and `-(exp (2πi t) - 1) * R t = ∑' m, c (m + 2) * t^(m + 2)` on `{t | t.re < 1}`, then
infinitely many coefficients `c m` (`m ≥ 2`) are nonzero. -/
theorem infinitely_many_cm_ne_zero {R : ℂ → ℂ} (hcont : ContinuousAt R (-1))
    (hR : R (-1) ≠ 0) {c : ℕ → ℂ}
    (hseries : ∀ t : ℂ, t.re < 1 →
      -(Complex.exp (2 * Real.pi * I * t) - 1) * R t = ∑' m : ℕ, c (m + 2) * t ^ (m + 2)) :
    {m : ℕ | 2 ≤ m ∧ c m ≠ 0}.Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  let S : Finset ℕ := hfin.toFinset
  let Q : Polynomial ℂ := ∑ m ∈ S, Polynomial.C (c m) * Polynomial.X ^ m
  have hQ_eval : ∀ t : ℂ, t.re < 1 → -(Complex.exp (2 * Real.pi * I * t) - 1) * R t = Q.eval t := by
    intro t ht
    rw [hseries t ht]
    have hsupp : Function.support (fun m : ℕ => c (m + 2) * t ^ (m + 2)) ⊆
        (S.image (fun m => m - 2) : Set ℕ) := by
      intro m hm
      have hcm : c (m + 2) ≠ 0 := left_ne_zero_of_mul hm
      have hmem : m + 2 ∈ S := hfin.mem_toFinset.mpr ⟨by omega, hcm⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m + 2, hmem, by omega⟩)
    rw [tsum_eq_sum (s := S.image (fun m => m - 2)) (fun m hm => by
      by_contra hne
      exact hm (hsupp hne))]
    change _ = Polynomial.evalRingHom t (∑ m ∈ S, Polynomial.C (c m) * Polynomial.X ^ m)
    rw [map_sum]
    refine Finset.sum_bij (fun m _ => m + 2) ?_ ?_ ?_ ?_
    · intro m hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      have hk2 : 2 ≤ k := (hfin.mem_toFinset.mp hk).1
      rwa [Nat.sub_add_cancel hk2]
    · intro m₁ _ m₂ _ h; omega
    · intro k hk
      have hk2 : 2 ≤ k := (hfin.mem_toFinset.mp hk).1
      exact ⟨k - 2, Finset.mem_image.mpr ⟨k, hk, rfl⟩, Nat.sub_add_cancel hk2⟩
    · intro m _
      change c (m + 2) * t ^ (m + 2) =
        Polynomial.eval t (Polynomial.C (c (m + 2)) * Polynomial.X ^ (m + 2))
      simp
  have hroots : ∀ k : ℕ, Q.eval (-((k + 1 : ℕ) : ℂ)) = 0 := by
    intro k
    have hre : (-((k + 1 : ℕ) : ℂ)).re < 1 := by
      simp only [Complex.neg_re, Complex.natCast_re]; linarith
    rw [← hQ_eval _ hre]
    have hexp : Complex.exp (2 * Real.pi * I * -((k + 1 : ℕ) : ℂ)) = 1 := by
      have h1 : 2 * Real.pi * I * -((k + 1 : ℕ) : ℂ) = ((-(k + 1 : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
        push_cast; ring
      rw [h1]
      exact Complex.exp_int_mul_two_pi_mul_I (-(k + 1 : ℤ))
    rw [hexp, sub_self, neg_zero, zero_mul]
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hinf_roots : {z : ℂ | Q.IsRoot z}.Infinite := by
      refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => -((k + 1 : ℕ) : ℂ))
        (fun a b h => by
          have h1 : ((a + 1 : ℕ) : ℂ) = ((b + 1 : ℕ) : ℂ) := neg_inj.mp h
          have h2 : a + 1 = b + 1 := by exact_mod_cast h1
          omega)
        (fun k => hroots k)
    have hfin_roots : {z : ℂ | Q.IsRoot z}.Finite :=
      (Q.roots.toFinset.finite_toSet).subset fun z hz => by
        simpa [Polynomial.mem_roots hQne] using hz
    exact hinf_roots hfin_roots
  let rn : ℕ → ℝ := fun n => 1 / ((n + 2 : ℕ) : ℝ)
  let tn : ℕ → ℂ := fun n => -1 - ((rn n : ℝ) : ℂ)
  have hR_tn : ∀ n : ℕ, R (tn n) = 0 := by
    intro n
    have hrn_pos : 0 < rn n := by dsimp [rn]; positivity
    have hre : (tn n).re < 1 := by
      simp only [tn, Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.ofReal_re]
      linarith
    have h0 := hQ_eval (tn n) hre
    rw [hQ0, Polynomial.eval_zero] at h0
    have hexp_ne : Complex.exp (2 * Real.pi * I * tn n) - 1 ≠ 0 := by
      intro heq
      have h1 : Complex.exp (2 * Real.pi * I * tn n) = 1 := sub_eq_zero.mp heq
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have htn_eq : tn n = (k : ℂ) := by
        have h2 : 2 * Real.pi * I * tn n = 2 * Real.pi * I * (k : ℂ) := by
          rw [hk]; ring
        exact mul_left_cancel₀ hpi h2
      have hre_eq := congr_arg Complex.re htn_eq
      simp only [tn, Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.ofReal_re,
        Complex.intCast_re] at hre_eq
      have hlt2 : rn n < 1 := by
        dsimp [rn]; rw [div_lt_one (by positivity)]; exact_mod_cast (show 1 < n + 2 by omega)
      have hk_gt : (-2 : ℝ) < (k : ℝ) := by linarith
      have hk_lt : (k : ℝ) < (-1 : ℝ) := by linarith
      have hk1 : (-2 : ℤ) < k := by exact_mod_cast hk_gt
      have hk2 : k < (-1 : ℤ) := by exact_mod_cast hk_lt
      omega
    exact (mul_eq_zero.mp h0).resolve_left (neg_ne_zero.mpr hexp_ne)
  have htend : Tendsto tn atTop (𝓝 (-1 : ℂ)) := by
    have hr : Tendsto rn atTop (𝓝 (0 : ℝ)) := by
      have h0 : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
      simpa only [rn, one_div] using h0
    have hc : Tendsto (fun n : ℕ => ((rn n : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp hr
    simpa [tn] using tendsto_const_nhds.sub hc
  have hR0 : Tendsto (fun n => R (tn n)) atTop (𝓝 (R (-1))) := hcont.tendsto.comp htend
  have hR0' : Tendsto (fun n => R (tn n)) atTop (𝓝 (0 : ℂ)) := by
    simp [hR_tn]
  exact hR (tendsto_nhds_unique hR0 hR0')

/-- The exponential integral `E₁(x) = ∫_{u > x} exp(-u) / u du`. -/
@[expose] def E1 (x : ℝ) : ℝ :=
  ∫ u in Set.Ioi x, Real.exp (-u) / u

/-- The literal Stokes integral `R(t) = t * ∫_{x > 0} exp(-x + t * E₁(x)) dx`. -/
@[expose] def R_integral (t : ℂ) : ℂ :=
  t * ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(x : ℂ) + t * (E1 x : ℂ))

lemma integrableOn_exp_neg_div_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Set.Ioi a) := by
  have hexp0 : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi a) :=
    (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) a).congr_fun
      (fun u _ => by simp) measurableSet_Ioi
  have hexp : IntegrableOn (fun u : ℝ => (1 / a) * Real.exp (-u)) (Set.Ioi a) :=
    hexp0.smul (1 / a)
  refine hexp.mono' ?_ ?_
  · have hcont : ContinuousOn (fun u : ℝ => Real.exp (-u) / u) (Set.Ioi a) :=
      (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
        (fun u hu => (lt_trans ha hu).ne')
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := lt_trans ha hu
    rw [Real.norm_of_nonneg (by positivity), one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le ha (le_of_lt hu)

lemma E1_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ E1 x := by
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hu_pos : 0 < u := lt_trans hx hu
  positivity

lemma continuousOn_E1 : ContinuousOn E1 (Set.Ioi 0) := by
  intro a ha
  have ha2 : 0 < a / 2 := half_pos ha
  have hint := integrableOn_exp_neg_div_Ioi ha2
  have heq : E1 =ᶠ[𝓝 a] fun x => E1 (a / 2) - ∫ u in (a / 2)..x, Real.exp (-u) / u := by
    filter_upwards [Ioi_mem_nhds (show a / 2 < a by linarith)] with x hx
    have hsplit : (∫ u in (a / 2)..x, Real.exp (-u) / u) + ∫ u in Set.Ioi x, Real.exp (-u) / u =
        ∫ u in Set.Ioi (a / 2), Real.exp (-u) / u := by
      rw [intervalIntegral.integral_of_le (le_of_lt hx)]
      have hunion : Set.Ioc (a / 2) x ∪ Set.Ioi x = Set.Ioi (a / 2) :=
        Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hx)
      rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint.mono_set Set.Ioc_subset_Ioi_self)
        (hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hx))), hunion]
    dsimp only [E1]
    linarith
  have hcont_int : ContinuousAt (fun x => ∫ u in (a / 2)..x, Real.exp (-u) / u) a := by
    have hint4 := integrableOn_exp_neg_div_Ioi (show 0 < a / 4 by linarith)
    have hint_ab : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Set.uIcc (a / 2) (a + 1)) volume := by
      refine hint4.mono_set ?_
      rw [Set.uIcc_of_le (by linarith)]
      intro u hu
      exact lt_of_lt_of_le (show a / 4 < a / 2 by linarith) hu.1
    have hc : ContinuousOn (fun x => ∫ u in (a / 2)..x, Real.exp (-u) / u) (Set.uIcc (a / 2) (a + 1)) :=
      intervalIntegral.continuousOn_primitive_interval hint_ab
    rw [Set.uIcc_of_le (by linarith)] at hc
    exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  exact (continuousAt_const.sub hcont_int).congr heq.symm |>.continuousWithinAt

/-- **Unconditional Non-Vanishing of `R(-s)`**: For every real `s > 0`, `R_integral (-s) ≠ 0`
(in fact its real part is strictly negative). In particular, `R_integral (-1) ≠ 0`. -/
theorem R_integral_neg_ne_zero (s : ℝ) (hs : 0 < s) : R_integral (-(s : ℂ)) ≠ 0 := by
  let f : ℝ → ℝ := fun x => Real.exp (-x - s * E1 x)
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn f (Set.Ioi 0) :=
      Real.continuous_exp.comp_continuousOn
        ((continuousOn_id.neg).sub (continuousOn_const.mul continuousOn_E1))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hf_int : IntegrableOn f (Set.Ioi 0) := by
    have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0).congr_fun
        (fun x _ => by simp) measurableSet_Ioi
    refine hexp.mono' hf_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by nlinarith [E1_nonneg hx])
  have hf_pos : 0 < ∫ x in Set.Ioi (0 : ℝ), f x := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun x => (Real.exp_pos _).le) hf_int]
    have hsupp : Function.support f = Set.univ := by
      ext x; simp [f, (Real.exp_pos _).ne']
    rw [hsupp, Set.univ_inter]
    simp
  have hre_eq : (R_integral (-(s : ℂ))).re = -s * ∫ x in Set.Ioi (0 : ℝ), f x := by
    have hfun : (fun x : ℝ => Complex.exp (-(x : ℂ) + -(s : ℂ) * (E1 x : ℂ))) =
        fun x : ℝ => ((f x : ℝ) : ℂ) := by
      ext x
      have harg : -(x : ℂ) + -(s : ℂ) * (E1 x : ℂ) = (((-x - s * E1 x : ℝ) : ℂ)) := by
        push_cast; ring
      rw [harg, ← Complex.ofReal_exp]
    dsimp only [R_integral]
    rw [hfun]
    have hint_ofReal : (∫ x in Set.Ioi (0 : ℝ), ((f x : ℝ) : ℂ)) =
        (((∫ x in Set.Ioi (0 : ℝ), f x) : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hf_int
    rw [hint_ofReal]
    simp [Complex.mul_re]
  intro h0
  have hre0 : (R_integral (-(s : ℂ))).re = 0 := by rw [h0]; simp
  rw [hre_eq] at hre0
  nlinarith

theorem R_integral_neg_one_ne_zero : R_integral (-1) ≠ 0 := by
  simpa using R_integral_neg_ne_zero 1 one_pos

end
end PakPrimes.PakNthPrimeEngine
