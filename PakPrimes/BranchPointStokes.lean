module

public import PakPrimes.HigherOrderStokes
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # General `α`-Branch-Point Non-Autonomous Stokes–Vandermonde Engine

This module formalizes the **General `α`-Branch-Point Non-Autonomous Stokes–Vandermonde Engine**
underlying unconditional differential transcendence over `ℂ(q)` (and `ℂ(q, E₂, E₄, E₆)`) of
Ramanujan's mock theta `q`-series `f(q), ω(q)`, Zagier's Hurwitz class-number series `H(q)`,
Rogers's false theta series `Ψ(q)`, and all half-integer-weight harmonic Maass forms with
non-constant holomorphic shadows:

1. **Exact Branch-Point Jet Polynomials (`P_branch`, `Q_branch`, `iteratedDeriv_rpow_mul_exp`)**:
   For any real exponent `α : ℝ` (including `α = 1/2, 3/2, -1/2, ...`) and frequency `ω : ℂ`,
   proves the exact derivative identity on `(0, ∞)`:
   `(d/du)^j (u^{-α} e^{-ω u}) = u^{-α} e^{-ω u} · (P_branch α ω j).eval u⁻¹`,
   with `deg(P_branch α ω j) ≤ j` and `(P_branch α ω j).coeff 0 = (-ω)^j`.
   Reversing by `r` gives `Q_branch α r ω j ∈ ℂ[u]` of degree `≤ r` with exact top coefficient
   `(Q_branch α r ω j).coeff r = (-ω)^j`.
2. **Branch-Point Non-Autonomous Operator & Vandermonde Descent (`L_branch`,
   `degree_L_branch_lt`, `D_freq_top_of_L_branch_eq_zero`, `L_branch_vandermonde_eq_zero`)**:
   Defines the `ℂ[u]`-linear derivation `L_branch α r ω P = ∑ j, Q_branch α r ω j • ∂_j P`,
   proves strict `Y`-total-degree drop, exact shift invariance of `evalU P u` along the exact
   branch-point Stokes jet `c_m · (d/du)^j (u^{-α} e^{-ω_m u})` (killing all nonlinear
   frequency collisions `ω_{ℓ_1} + ... + ω_{ℓ_t} ≤ ω_n` identically), and top-`u`-degree
   Vandermonde descent.
3. **End-to-End Branch-Point Stokes–Vandermonde Theorems (`BranchPointStokesData`,
   `branchPoint_stokes_vandermonde_no_ade`, `branchPoint_stokes_vandermonde_no_rat_ade`,
   `branchPoint_stokes_vandermonde_no_ade_of_asymp`,
   `branchPoint_stokes_vandermonde_no_rat_ade_of_asymp`)**:
   Proves that any formal series `S ∈ ℂ[[1/u]]` (and any function `M : ℝ → ℂ` sharing its
   all-orders `1/u` asymptotic expansion) admitting an `α`-branch-point Stokes comb
   `∑ c_m (d/du)^j (u^{-α} e^{-ω_m u})` satisfies NO nonzero `ℂ[u]`- or `ℂ(u)`-ADE.
4. **Exponentially Small Modular-Companion Absorption (`HasAsympExp.add_exp_small`,
   `branchPoint_no_rat_ade_of_exp_companion`, `half_integer_no_rat_ade_of_exp_companion`)**:
   Proves that adding any exponentially decaying modular companion `T(u)` (such as
   `2√(2u) e^{-4πu/3} ω(e^{-2πu})` in Watson–Zwegers for `f(q)`) preserves all-orders
   asymptotics and therefore unconditional `ℂ(u)` differential transcendence.
5. **Exact Closed-Form Abel Integral Identity (`abel_inv_linear_eq_inv_sqrt`)**:
   Proves via elementary FTC (`u = tan θ`) that for all `ω > 0` and `ξ > -ω`,
   `(1 / π) ∫_0^{π/2} (ξ sin²θ + ω)⁻¹ dθ = (2 √(ω (ξ + ω)))⁻¹`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.BranchPointStokes

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Exact Branch-Point Jet Polynomials (`P_branch`, `Q_branch`) & Leibniz Formula -/

/-- Jet polynomial in `w = 1/u` for `(d/du)^j (u^{-α} e^{-ω u})`:
`(d/du)^j (u^{-α} e^{-ω u}) = u^{-α} e^{-ω u} · (P_branch α ω j).eval u⁻¹`. -/
@[expose] def P_branch (α : ℝ) (ω : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | j + 1 =>
      Polynomial.C (-ω) * P_branch α ω j
        - Polynomial.C (α : ℂ) * Polynomial.X * P_branch α ω j
        - Polynomial.X ^ 2 * Polynomial.derivative (P_branch α ω j)

theorem P_branch_coeff_zero (α : ℝ) (ω : ℂ) (j : ℕ) :
    (P_branch α ω j).coeff 0 = (-ω) ^ j := by
  induction j with
  | zero => simp [P_branch]
  | succ j ih =>
    simp only [P_branch, Polynomial.coeff_sub, Polynomial.coeff_C_mul, ih,
      mul_assoc, Polynomial.coeff_X_mul_zero, mul_zero, sub_zero, pow_succ']

theorem P_branch_natDegree_le (α : ℝ) (ω : ℂ) (j : ℕ) :
    (P_branch α ω j).natDegree ≤ j := by
  induction j with
  | zero => simp [P_branch]
  | succ j ih =>
    unfold P_branch
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (ih.trans (Nat.le_succ j))
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have h1 : (Polynomial.C (α : ℂ) * Polynomial.X).natDegree ≤ 1 :=
          (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
        omega
    · by_cases hder : Polynomial.derivative (P_branch α ω j) = 0
      · simp [hder]
      · have hdeg : (P_branch α ω j).natDegree ≥ 1 := by
          by_contra hlt
          push Not at hlt
          have h0 : (P_branch α ω j).natDegree = 0 := Nat.lt_one_iff.mp hlt
          have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
          rw [hC, Polynomial.derivative_C] at hder
          exact hder rfl
        refine (Polynomial.natDegree_mul_le).trans ?_
        have hX2 : (Polynomial.X ^ 2 : Polynomial ℂ).natDegree ≤ 2 := by
          simp
        have hd : (Polynomial.derivative (P_branch α ω j)).natDegree ≤ (P_branch α ω j).natDegree - 1 :=
          Polynomial.natDegree_derivative_le _
        omega

/-- Branch-point basis function `u ↦ u^{-α} e^{-ω u}` on `ℝ`. -/
@[expose] def branchMode (α : ℝ) (ω : ℂ) (u : ℝ) : ℂ :=
  ((Real.rpow u (-α) : ℝ) : ℂ) * Complex.exp (-ω * (u : ℂ))

private lemma hasDerivAt_poly_eval_inv (q : Polynomial ℂ) {u : ℝ} (hu : (u : ℂ) ≠ 0) :
    HasDerivAt (fun t : ℝ => q.eval (t : ℂ)⁻¹)
      ((Polynomial.derivative q).eval (u : ℂ)⁻¹ * (-((u : ℂ) ^ 2)⁻¹)) u := by
  have hinv : HasDerivAt (fun t : ℝ => (t : ℂ)⁻¹) (-((u : ℂ) ^ 2)⁻¹) u := by
    have hofReal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := by
      have h := (hasDerivAt_id u).ofReal_comp
      exact h.congr_deriv (by simp)
    have h1 := hofReal.inv hu
    exact h1.congr_deriv (by simp [neg_div, one_div])
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    have hadd := hp.add hq
    refine (hadd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp [Polynomial.eval_add]
    · simp only [Polynomial.derivative_add, Polynomial.eval_add]; ring
  | monomial n a =>
    have hpow := (hinv.pow n).const_mul a
    refine (hpow.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp [Polynomial.eval_monomial]
    · simp only [Polynomial.derivative_monomial, Polynomial.eval_monomial]; ring

private lemma hasDerivAt_branchMode_mul_poly (α : ℝ) (ω : ℂ) (q : Polynomial ℂ)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => branchMode α ω t * q.eval (t : ℂ)⁻¹)
      (branchMode α ω u *
        (Polynomial.C (-ω) * q - Polynomial.C (α : ℂ) * Polynomial.X * q
          - Polynomial.X ^ 2 * Polynomial.derivative q).eval (u : ℂ)⁻¹) u := by
  have hu_ne : u ≠ 0 := hu.ne'
  have huC_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_ne
  have hrpow : HasDerivAt (fun t : ℝ => Real.rpow t (-α)) ((-α) * Real.rpow u (-α - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu_ne)
  have hrpowC : HasDerivAt (fun t : ℝ => ((Real.rpow t (-α) : ℝ) : ℂ))
      ((((-α) * Real.rpow u (-α - 1) : ℝ) : ℂ)) u :=
    hrpow.ofReal_comp
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-ω * (t : ℂ)))
      (Complex.exp (-ω * (u : ℂ)) * (-ω)) u := by
    have h1 : HasDerivAt (fun t : ℝ => -ω * (t : ℂ)) (-ω * 1) u :=
      (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-ω)
    simpa [mul_one] using h1.cexp
  have hmode : HasDerivAt (branchMode α ω)
      (((((-α) * Real.rpow u (-α - 1) : ℝ) : ℂ)) * Complex.exp (-ω * (u : ℂ)) +
        ((Real.rpow u (-α) : ℝ) : ℂ) * (Complex.exp (-ω * (u : ℂ)) * (-ω))) u :=
    hrpowC.mul hexp
  have hpoly : HasDerivAt (fun t : ℝ => q.eval (t : ℂ)⁻¹)
      ((Polynomial.derivative q).eval (u : ℂ)⁻¹ * (-((u : ℂ) ^ 2)⁻¹)) u :=
    hasDerivAt_poly_eval_inv q huC_ne
  have hmul := hmode.mul hpoly
  have hrpow_split : Real.rpow u (-α - 1) = Real.rpow u (-α) * u⁻¹ := by
    change u ^ (-α - 1) = u ^ (-α) * u⁻¹
    rw [sub_eq_add_neg, Real.rpow_add hu, Real.rpow_neg_one]
  convert hmul using 1
  simp only [branchMode, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, hrpow_split, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_inv]
  rw [inv_pow]
  ring

/-- Exact `j`-th derivative of `u ↦ u^{-α} e^{-ω u}` for `u > 0`. -/
theorem iteratedDeriv_branchMode (α : ℝ) (ω : ℂ) (j : ℕ) :
    ∀ u : ℝ, 0 < u →
      iteratedDeriv j (branchMode α ω) u =
        branchMode α ω u * (P_branch α ω j).eval (u : ℂ)⁻¹ := by
  induction j with
  | zero =>
    intro u _
    simp [P_branch]
  | succ j ih =>
    intro u hu
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (branchMode α ω) =ᶠ[𝓝 u]
        fun t : ℝ => branchMode α ω t * (P_branch α ω j).eval (t : ℂ)⁻¹ := by
      filter_upwards [eventually_gt_nhds hu] with t ht
      exact ih t ht
    rw [hev.deriv_eq]
    exact (hasDerivAt_branchMode_mul_poly α ω (P_branch α ω j) hu).deriv

/-- Reversed branch-point jet polynomial `Q_branch α r ω j ∈ ℂ[u]` satisfying
`(Q_branch α r ω j).eval u = u^r · (P_branch α ω j).eval u⁻¹`. -/
@[expose] def Q_branch (α : ℝ) (r : ℕ) (ω : ℂ) (j : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (r + 1),
    Polynomial.C ((P_branch α ω j).coeff k) * Polynomial.X ^ (r - k)

private lemma poly_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff ℂ m) f s

theorem Q_branch_natDegree_le (α : ℝ) (r : ℕ) (ω : ℂ) (j : ℕ) :
    (Q_branch α r ω j).natDegree ≤ r := by
  unfold Q_branch
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  exact (Polynomial.natDegree_X_pow_le (r - k)).trans (Nat.sub_le r k)

theorem Q_branch_coeff_top (α : ℝ) (r : ℕ) (ω : ℂ) (j : ℕ) :
    (Q_branch α r ω j).coeff r = (-ω) ^ j := by
  unfold Q_branch
  rw [poly_sum_coeff, Finset.sum_eq_single 0]
  · rw [Nat.sub_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one,
      P_branch_coeff_zero]
  · intro k hk hk0
    have hlt : r - k < r := by
      have := Finset.mem_range.mp hk
      omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right_iff.mpr (fun h => absurd h (ne_of_gt hlt)),
      mul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos r)) h0

theorem Q_branch_eval (α : ℝ) (r : ℕ) (ω : ℂ) {j : ℕ} (hj : j ≤ r) {u : ℂ} (hu : u ≠ 0) :
    (Q_branch α r ω j).eval u = u ^ r * (P_branch α ω j).eval u⁻¹ := by
  have hdeg : (P_branch α ω j).natDegree ≤ r := (P_branch_natDegree_le α ω j).trans hj
  have hsum : P_branch α ω j =
      ∑ k ∈ Finset.range (r + 1), Polynomial.C ((P_branch α ω j).coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow' _ (Nat.lt_succ_of_le hdeg)
  conv_rhs => rw [hsum]
  change Polynomial.evalRingHom u (Q_branch α r ω j) = u ^ r * Polynomial.evalRingHom u⁻¹ _
  simp only [Q_branch, map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have heq : u ^ (r - k) = u ^ r * u⁻¹ ^ k := by
    calc u ^ (r - k) = u ^ (r - k) * (u ^ k * u⁻¹ ^ k) := by
          rw [← mul_pow, mul_inv_cancel₀ hu, one_pow, mul_one]
      _ = (u ^ (r - k) * u ^ k) * u⁻¹ ^ k := by ring
      _ = u ^ r * u⁻¹ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_le]
  rw [heq]; ring

/-- Exact `j`-th derivative in terms of `Q_branch`:
`iteratedDeriv j (branchMode α ω) u = branchMode α ω u * (u⁻¹ ^ r * (Q_branch α r ω j).eval u)`. -/
theorem iteratedDeriv_branchMode_eq_Q_branch (α : ℝ) (r : ℕ) (ω : ℂ) {j : ℕ} (hj : j ≤ r)
    {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (branchMode α ω) u =
      branchMode α ω u * ((u : ℂ)⁻¹ ^ r * (Q_branch α r ω j).eval (u : ℂ)) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [iteratedDeriv_branchMode α ω j u hu, Q_branch_eval α r ω hj huC]
  have hcancel : (u : ℂ)⁻¹ ^ r * (u : ℂ) ^ r = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ huC, one_pow]
  rw [← mul_assoc ((u : ℂ)⁻¹ ^ r), hcancel, one_mul]

/-! ### 2. Branch-Point Differential Operator `L_branch` & Vandermonde Descent -/

/-- Non-autonomous `ℂ[u]`-linear branch-point derivation
`L_branch α r ω P = ∑ j, Q_branch α r ω j • ∂_j P`. -/
@[expose] def L_branch (α : ℝ) (r : ℕ) (ω : ℂ) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) →ₗ[Polynomial ℂ]
      MvPolynomial (Fin (r + 1)) (Polynomial ℂ) where
  toFun P := ∑ j : Fin (r + 1), Q_branch α r ω j.val • MvPolynomial.pderiv j P
  map_add' P Q := by
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, smul_comm]

private lemma degree_pderiv_poly_lt' {ι : Type*} (i : ι) (P : MvPolynomial ι (Polynomial ℂ))
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

private lemma totalDegree_poly_sum_lt' {ι σ : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial σ (Polynomial ℂ)) {d : ℕ} (hd : 0 < d)
    (hf : ∀ i ∈ s, (f i).totalDegree < d) :
    (∑ i ∈ s, f i).totalDegree < d := by
  induction s using Finset.induction_on with
  | empty => simpa using hd
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (MvPolynomial.totalDegree_add _ _).trans_lt ?_
    exact max_lt (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem degree_L_branch_lt (α : ℝ) {r : ℕ} (ω : ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (h : 0 < P.totalDegree) :
    (L_branch α r ω P).totalDegree < P.totalDegree := by
  unfold L_branch
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine totalDegree_poly_sum_lt' Finset.univ _ h fun j _ => ?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans_lt (degree_pderiv_poly_lt' j P h)

lemma evalU_L_branch (α : ℝ) {r : ℕ} (ω : ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    evalU (L_branch α r ω P) u =
      ∑ j : Fin (r + 1), (Q_branch α r ω j.val).eval u • MvPolynomial.pderiv j (evalU P u) := by
  unfold L_branch evalU
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
    ← MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_map]

/-- Coefficient of `u^k` in `P ∈ ℂ[u][Y_0,...,Y_r]` as an element of `ℂ[Y_0,...,Y_r]`. -/
private def coeffU {r : ℕ} (k : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ α ∈ P.support, MvPolynomial.monomial α ((P.coeff α).coeff k)

private lemma coeffU_coeff {r : ℕ} (k : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (m : Fin (r + 1) →₀ ℕ) : (coeffU k P).coeff m = (P.coeff m).coeff k := by
  classical
  unfold coeffU
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ P.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hbm; simp [hbm]
    · intro hnot; exact absurd hm hnot
  · have hP0 : P.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    rw [hP0, Polynomial.coeff_zero, Finset.sum_eq_zero]
    intro b hb
    rw [ite_eq_right_iff]
    intro hbm; subst hbm; exact absurd hb hm

private def maxUDeg {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) : ℕ :=
  P.support.sup fun α => (P.coeff α).natDegree

private lemma natDegree_le_maxUDeg {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (α : Fin (r + 1) →₀ ℕ) : (P.coeff α).natDegree ≤ maxUDeg P := by
  by_cases hα : α ∈ P.support
  · exact Finset.le_sup (f := fun β => (P.coeff β).natDegree) hα
  · have h0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    simp [h0]

private lemma evalU_eq_sum_coeffU {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    evalU P u = ∑ k ∈ Finset.range (maxUDeg P + 1), u ^ k • coeffU k P := by
  ext m
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_smul, coeffU_coeff, smul_eq_mul, mul_comm (u ^ _)]
  have hle : (P.coeff m).natDegree < maxUDeg P + 1 := Nat.lt_succ_of_le (natDegree_le_maxUDeg P m)
  rw [Polynomial.eval_eq_sum_range' hle]

/-- Maximum `u`-degree among the non-constant (`m ≠ 0`) `Y`-monomials of `P`. -/
@[expose] def maxNonConstUDeg {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) : ℕ :=
  (P.support.erase 0).sup fun m => (P.coeff m).natDegree

/-- Top `u`-degree `Y`-nonconstant component of `P`. -/
@[expose] def topNonConstU {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ m ∈ P.support.erase 0, MvPolynomial.monomial m ((P.coeff m).coeff (maxNonConstUDeg P))

private lemma topNonConstU_coeff {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (m : Fin (r + 1) →₀ ℕ) :
    (topNonConstU P).coeff m = if m = 0 then 0 else (P.coeff m).coeff (maxNonConstUDeg P) := by
  classical
  unfold topNonConstU
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    simp [hb0]
  · simp only [hm0, ↓reduceIte]
    by_cases hmem : m ∈ P.support.erase 0
    · rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hbm; simp [hbm]
      · intro hnot; exact absurd hmem hnot
    · have hnot : m ∉ P.support := fun h => hmem (Finset.mem_erase.mpr ⟨hm0, h⟩)
      have hP0 : P.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hnot
      rw [hP0, Polynomial.coeff_zero, Finset.sum_eq_zero]
      intro b hb
      rw [ite_eq_right_iff]
      intro hbm; subst hbm; exact absurd hb hmem

private lemma topNonConstU_pos_deg {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hpos : 0 < P.totalDegree) : 0 < (topNonConstU P).totalDegree := by
  classical
  have hne : (P.support.erase 0).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hle : P.totalDegree ≤ 0 := by
      rw [MvPolynomial.totalDegree_eq]
      refine Finset.sup_le fun m hm => ?_
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have : m ∈ P.support.erase 0 := Finset.mem_erase.mpr ⟨hm0, hm⟩
        rw [hempty] at this; exact absurd this (Finset.notMem_empty m)
    omega
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image (P.support.erase 0)
    (fun m => (P.coeff m).natDegree) hne
  have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm_mem).1
  have hm_supp : m ∈ P.support := (Finset.mem_erase.mp hm_mem).2
  have hPm_ne : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm_supp
  have hdeg_eq : (P.coeff m).natDegree = maxNonConstUDeg P := by
    apply le_antisymm
    · exact Finset.le_sup (f := fun b => (P.coeff b).natDegree) hm_mem
    · exact Finset.sup_le fun b hb => hm_max b hb
  have hcoeff_ne : (topNonConstU P).coeff m ≠ 0 := by
    rw [topNonConstU_coeff, ite_eq_right_iff.mpr (fun h => absurd h hm0), ← hdeg_eq]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPm_ne
  have hm_supp' : m ∈ (topNonConstU P).support := MvPolynomial.mem_support_iff.mpr hcoeff_ne
  have hsum_pos : 0 < m.sum fun _ e => e := by
    by_contra h0
    push Not at h0
    have hz : m.sum (fun _ e => e) = 0 := Nat.eq_zero_of_le_zero h0
    have hall : ∀ i, m i = 0 := by
      intro i
      by_cases hi : i ∈ m.support
      · have hle := Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _) hi
        change m i ≤ m.sum (fun _ e => e) at hle
        omega
      · exact Finsupp.notMem_support_iff.mp hi
    exact hm0 (Finsupp.ext hall)
  exact lt_of_lt_of_le hsum_pos (MvPolynomial.le_totalDegree hm_supp')

/-- Top-`u`-degree extraction: `L_branch α r ω P = 0` forces `D_freq r ω (topNonConstU P) = 0`. -/
theorem D_freq_top_of_L_branch_eq_zero (α : ℝ) {r : ℕ} (ω : ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hL : L_branch α r ω P = 0) :
    D_freq r ω (topNonConstU P) = 0 := by
  classical
  ext m
  change (D_freq r ω (topNonConstU P)).coeff m = 0
  let D : ℕ := maxNonConstUDeg P
  have hL_coeff : ((L_branch α r ω P).coeff m).coeff (r + D) = 0 := by
    rw [hL]
    simp
  have h_expand : ((L_branch α r ω P).coeff m).coeff (r + D) =
      (D_freq r ω (topNonConstU P)).coeff m := by
    unfold L_branch D_freq
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum, poly_sum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, smul_eq_mul, smul_eq_mul,
      MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
    let m' : Fin (r + 1) →₀ ℕ := m + Finsupp.single j 1
    have hm'_ne : m' ≠ 0 := by
      intro h0
      have h1 : m' j = 0 := by rw [h0]; simp
      simp [m'] at h1
    have hPm'_deg : (P.coeff m').natDegree ≤ D := by
      by_cases hmem : m' ∈ P.support
      · exact Finset.le_sup (f := fun b => (P.coeff b).natDegree)
          (Finset.mem_erase.mpr ⟨hm'_ne, hmem⟩)
      · have h0 : P.coeff m' = 0 := MvPolynomial.notMem_support_iff.mp hmem
        simp [h0]
    have hQ_deg : (Q_branch α r ω j.val).natDegree ≤ r := Q_branch_natDegree_le α r ω j.val
    have hmul_poly : (Q_branch α r ω j.val * (P.coeff m' * ((m j : Polynomial ℂ) + 1))).coeff (r + D) =
        ((Q_branch α r ω j.val * P.coeff m') * Polynomial.C (((m j : ℂ) + 1))).coeff (r + D) := by
      congr 1
      have hcast : ((m j : Polynomial ℂ) + 1) = Polynomial.C ((m j : ℂ) + 1) := by
        simp [map_add, map_natCast, map_one]
      rw [hcast, mul_assoc]
    rw [hmul_poly, Polynomial.coeff_mul_C, Polynomial.coeff_mul]
    rw [Finset.sum_eq_single (r, D)]
    · rw [Q_branch_coeff_top α r ω j.val, topNonConstU_coeff,
        ite_eq_right_iff.mpr (fun h => absurd h hm'_ne)]
      ring
    · intro ab hab hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      by_cases ha : r < ab.1
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ_deg ha), zero_mul]
      · push Not at ha
        have hb : D < ab.2 := by
          by_contra hble
          push Not at hble
          have ha_eq : ab.1 = r := by omega
          have hb_eq : ab.2 = D := by omega
          exact hne (Prod.ext ha_eq hb_eq)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPm'_deg hb), mul_zero]
    · intro hnot
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal (a := (r, D)).mpr rfl) hnot
  rw [← h_expand, hL_coeff]

/-- Complex Vandermonde descent: if `L_branch α r (ω n) P = 0` for `r + 1` pairwise distinct
frequencies `ω : Fin (r + 1) → ℂ`, then `P` has `Y`-total-degree `0`. -/
theorem L_branch_vandermonde_contradiction (α : ℝ) {r : ℕ}
    (ω : Fin (r + 1) → ℂ) (hω_inj : Function.Injective ω)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hpos : 0 < P.totalDegree)
    (hL : ∀ n : Fin (r + 1), L_branch α r (ω n) P = 0) : False := by
  let Q : MvPolynomial (Fin (r + 1)) ℂ := topNonConstU P
  have hQ_pos : 0 < Q.totalDegree := topNonConstU_pos_deg P hpos
  have hD : ∀ n : Fin (r + 1), D_freq r (ω n) Q = 0 := fun n =>
    D_freq_top_of_L_branch_eq_zero α (ω n) P (hL n)
  let V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.vandermonde (fun n => -ω n)
  have hV_det : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    exact hω_inj (neg_inj.mp hab)
  have hpart : ∀ j : Fin (r + 1), MvPolynomial.pderiv j Q = 0 := by
    intro j
    ext m
    change (MvPolynomial.pderiv j Q).coeff m = 0
    let x : Fin (r + 1) → ℂ := fun k => (MvPolynomial.pderiv k Q).coeff m
    have hVx : V.mulVec x = 0 := by
      ext n
      simp only [Matrix.mulVec, dotProduct, V, Matrix.vandermonde_apply, Pi.zero_apply, x]
      have h0 : (D_freq r (ω n) Q).coeff m = 0 := by
        rw [hD n]; rfl
      unfold D_freq at h0
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at h0
      rw [MvPolynomial.coeff_sum] at h0
      simpa only [MvPolynomial.coeff_smul, smul_eq_mul] using h0
    have hx0 : x = 0 := by
      have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hV_det)
      calc x = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ).mulVec x := (Matrix.one_mulVec x).symm
        _ = (V⁻¹ * V).mulVec x := by rw [hinv]
        _ = V⁻¹.mulVec (V.mulVec x) := (Matrix.mulVec_mulVec x V⁻¹ V).symm
        _ = V⁻¹.mulVec 0 := by rw [hVx]
        _ = 0 := Matrix.mulVec_zero _
    exact congr_fun hx0 j
  have hQC : Q = MvPolynomial.C (Q.coeff 0) := all_partials_zero Q hpart
  have hQ0 : Q.totalDegree = 0 := by rw [hQC]; exact MvPolynomial.totalDegree_C _
  omega

/-! ### 3. General `α`-Branch-Point Stokes–Vandermonde Engine -/

/-- Minimal genuine analytic hypotheses for an `α`-branch-point Stokes comb on a formal
power series `S ∈ ℂ[[1/u]]`:
- Strictly increasing positive singularity radii `0 < ω 0 < ω 1 < ...` with nonzero Stokes
  constants `c m ≠ 0`,
- Two lateral Borel sums `g_pos, g_neg : ℝ → ℂ` sharing the all-orders `1/u` asymptotic expansion
  `d_u^[j] S` and satisfying Borel–Laplace transfer for `ℂ[u]`-ODEs,
- Exact `α`-branch-point Stokes jump `∑_{m=0}^n c_m (d/du)^j (u^{-α} e^{-ω_m u}) + O(e^{-R' u})`
  for every `n, j : ℕ`. -/
structure BranchPointStokesData (S : PowerSeries ℂ) (α : ℝ) (ω : ℕ → ℝ) (c : ℕ → ℂ) where
  ω_pos : 0 < ω 0
  ω_mono : StrictMono ω
  c_ne_zero : ∀ m : ℕ, c m ≠ 0
  g_pos : ℝ → ℂ
  g_neg : ℝ → ℂ
  g_pos_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j g_pos) (d_u^[j] S)
  g_neg_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j g_neg) (d_u^[j] S)
  borel_transfer : ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)),
    formalEvalPoly S P = 0 →
      (∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u) (evalU P (u : ℂ)) = 0) ∧
      (∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_neg u) (evalU P (u : ℂ)) = 0)
  stokes_jump : ∀ n j : ℕ, ∃ R' : ℝ, ω n < R' ∧ ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
    ‖iteratedDeriv j g_neg u - iteratedDeriv j g_pos u -
      ∑ m ∈ Finset.range (n + 1), c m * iteratedDeriv j (branchMode α (ω m : ℂ)) u‖ ≤
      C * Real.exp (-R' * u)

private lemma pow_mul_exp_neg_le_one' (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, u ^ k * Real.exp (-δ * u) ≤ 1 := by
  have h1 : ∀ u : ℝ, 0 < u → u ^ k * Real.exp (-δ * u) ≤
      ((k + 1).factorial : ℝ) / (δ ^ (k + 1) * u) := by
    intro u hu_pos
    have hterm := Real.pow_div_factorial_le_exp (δ * u) (mul_nonneg hδ.le hu_pos.le) (k + 1)
    have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hexp : 0 < Real.exp (δ * u) := Real.exp_pos _
    rw [mul_pow, div_le_iff₀ hfac] at hterm
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexp (by positivity)]
    calc u ^ k * (δ ^ (k + 1) * u) = δ ^ (k + 1) * u ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ Real.exp (δ * u) * ((k + 1).factorial : ℝ) := hterm
      _ = ((k + 1).factorial : ℝ) * Real.exp (δ * u) := mul_comm _ _
  let B : ℝ := ((k + 1).factorial : ℝ) / δ ^ (k + 1) + 1
  filter_upwards [eventually_ge_atTop B] with u hu
  have hB_pos : 0 < B := by positivity
  have hu_pos : 0 < u := lt_of_lt_of_le hB_pos hu
  refine (h1 u hu_pos).trans ?_
  rw [div_le_one (by positivity)]
  have hdiv : ((k + 1).factorial : ℝ) / δ ^ (k + 1) ≤ u := by linarith
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ (k + 1))).mp hdiv |>.trans_eq (mul_comm _ _)

private lemma rpow_le_pow_of_ge_one (β : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    Real.rpow u β ≤ u ^ (Nat.ceil (max β 0)) := by
  have hle : β ≤ (Nat.ceil (max β 0) : ℝ) := (le_max_left β 0).trans (Nat.le_ceil _)
  calc Real.rpow u β ≤ Real.rpow u (Nat.ceil (max β 0) : ℝ) := Real.rpow_le_rpow_of_exponent_le hu hle
    _ = u ^ (Nat.ceil (max β 0)) := Real.rpow_natCast u _

private lemma norm_branchMode (α : ℝ) (ω : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖branchMode α (ω : ℂ) u‖ = Real.rpow u (-α) * Real.exp (-ω * u) := by
  unfold branchMode
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hrp : 0 < Real.rpow u (-α) := Real.rpow_pos_of_pos hu (-α)
  rw [abs_of_pos hrp]
  congr 1
  simp [Complex.mul_re]

private lemma Q_branch_inv_pow_bdd (α : ℝ) (r : ℕ) (ω : ℂ) (j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    ‖(u : ℂ)⁻¹ ^ r * (Q_branch α r ω j).eval (u : ℂ)‖ ≤
      ∑ k ∈ Finset.range (r + 1), ‖(Q_branch α r ω j).coeff k‖ := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hdeg : (Q_branch α r ω j).natDegree < r + 1 := Nat.lt_succ_of_le (Q_branch_natDegree_le α r ω j)
  rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk_le : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [norm_mul, norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hu_pos]
  have hpow : u⁻¹ ^ r * u ^ k ≤ 1 := by
    rw [inv_pow]
    calc (u ^ r)⁻¹ * u ^ k ≤ (u ^ r)⁻¹ * u ^ r :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hk_le) (by positivity)
      _ = 1 := inv_mul_cancel₀ (pow_pos hu_pos r).ne'
  calc u⁻¹ ^ r * (‖(Q_branch α r ω j).coeff k‖ * u ^ k)
      = ‖(Q_branch α r ω j).coeff k‖ * (u⁻¹ ^ r * u ^ k) := by ring
    _ ≤ ‖(Q_branch α r ω j).coeff k‖ * 1 := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = ‖(Q_branch α r ω j).coeff k‖ := mul_one _

private lemma HasAsympExp.eventually_bdd {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp f S) : ∃ B : ℝ, ∀ᶠ u : ℝ in atTop, ‖f u‖ ≤ B := by
  obtain ⟨C, hC⟩ := hf 1
  refine ⟨‖PowerSeries.coeff 0 S‖ + max C 0, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with u hu hu1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one] at hu
  have h1 : ‖f u‖ ≤ ‖f u - PowerSeries.coeff 0 S‖ + ‖PowerSeries.coeff 0 S‖ := by
    have := norm_add_le (f u - PowerSeries.coeff 0 S) (PowerSeries.coeff 0 S)
    simpa [sub_add_cancel] using this
  have h2 : C / u ≤ max C 0 := by
    calc C / u ≤ max C 0 / u := div_le_div_of_nonneg_right (le_max_left C 0) (by linarith)
      _ ≤ max C 0 / 1 := div_le_div_of_nonneg_left (le_max_right C 0) zero_lt_one hu1
      _ = max C 0 := div_one _
  linarith

private lemma polyToLaurent_injective' : Function.Injective polyToLaurent := by
  intro p q hpq
  by_contra hne
  have hsub : polyToLaurent (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  have hne0 : p - q ≠ 0 := sub_ne_zero.mpr hne
  let N := (p - q).natDegree
  have hlead : (p - q).coeff N ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne0
  have hval : (polyToLaurent (p - q)).coeff (-(N : ℤ)) = (p - q).coeff N := by
    have hsum := Polynomial.as_sum_range_C_mul_X_pow' (p - q) (Nat.lt_succ_self N)
    conv_lhs => rw [hsum]
    simp only [polyToLaurent, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul,
      map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    have halg : ∀ c : ℂ, algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c :=
      HahnSeries.ofPowerSeries_C
    have hu_pow : ∀ k : ℕ, uLaurent ^ k = HahnSeries.single (-(k : ℤ)) (1 : ℂ) := by
      intro k
      induction k with
      | zero => simp [uLaurent]
      | succ k ih =>
        rw [pow_succ, ih, uLaurent, HahnSeries.single_mul_single, one_mul]
        have hidx : -(k : ℤ) + (-1 : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
        rw [hidx]
    have hCmul : ∀ (c : ℂ) (k : ℕ), HahnSeries.C c * HahnSeries.single (-(k : ℤ)) (1 : ℂ) =
        HahnSeries.single (-(k : ℤ)) c := fun c k => by
      rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
    simp_rw [halg, hu_pow, hCmul]
    rw [HahnSeries.coeff_sum, Finset.sum_eq_single N]
    · simp
    · intro k _ hkN
      rw [HahnSeries.coeff_single_of_ne]
      omega
    · intro hN; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) hN
  rw [hsub, HahnSeries.coeff_zero] at hval
  exact hlead hval.symm

private lemma formalEvalPoly_eq_zero_of_evalU_exp_small {S : PowerSeries ℂ} {f : ℝ → ℂ}
    (hf : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] S))
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    {δ : ℝ} (hδ : 0 < δ) {C : ℝ}
    (hbound : ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalU Q (u : ℂ))‖ ≤
        C * Real.exp (-δ * u)) :
    formalEvalPoly S Q = 0 := by
  let N := maxUDeg Q
  -- Reverse Q in u: R(w) = w^N * Q(1/w)
  let revP : Polynomial ℂ → Polynomial ℂ := fun p =>
    ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k)
  let R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ α ∈ Q.support, MvPolynomial.monomial α (revP (Q.coeff α))
  have hrev_eval : ∀ p : Polynomial ℂ, p.natDegree ≤ N → ∀ {u : ℂ}, u ≠ 0 →
      (revP p).eval u⁻¹ = u⁻¹ ^ N * p.eval u := by
    intro p hp u hu
    have hsum := Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
    conv_rhs => rw [hsum]
    change Polynomial.evalRingHom u⁻¹ (revP p) = u⁻¹ ^ N * Polynomial.evalRingHom u _
    simp only [revP, map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, Polynomial.eval_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have heq : u⁻¹ ^ (N - k) = u⁻¹ ^ N * u ^ k := by
      calc u⁻¹ ^ (N - k) = u⁻¹ ^ (N - k) * (u⁻¹ ^ k * u ^ k) := by
            rw [← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
        _ = (u⁻¹ ^ (N - k) * u⁻¹ ^ k) * u ^ k := by ring
        _ = u⁻¹ ^ N * u ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_le]
    rw [heq]; ring
  have hevalR : ∀ {u : ℂ}, u ≠ 0 → evalU R u⁻¹ = u⁻¹ ^ N • evalU Q u := by
    intro u hu
    classical
    ext α
    rw [evalU, evalU, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_map,
      Polynomial.coe_evalRingHom, Polynomial.coe_evalRingHom, smul_eq_mul]
    unfold R
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ Q.support
    · rw [Finset.sum_eq_single α]
      · simp only [↓reduceIte]
        exact hrev_eval (Q.coeff α) (natDegree_le_maxUDeg Q α) hu
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · have h0 : Q.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
      rw [h0, Polynomial.eval_zero, mul_zero]
      have hsum0 : (∑ x ∈ Q.support, if x = α then revP (Q.coeff x) else 0) = 0 := by
        refine Finset.sum_eq_zero fun β hβ => ?_
        rw [ite_eq_right_iff]
        intro hβα; subst hβα; exact absurd hβ hα
      rw [hsum0, Polynomial.eval_zero]
  have hexp : HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalU R (u : ℂ)⁻¹))
      (MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
        (fun j : Fin (r + 1) => d_u^[j.val] S) R) :=
    HasAsympExp.mvPolynomial_evalW (fun j => hf j.val) R
  have hflat : ∀ M : ℕ, ∃ K : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalU R (u : ℂ)⁻¹)‖ ≤
        K / u ^ M := by
    intro M
    refine ⟨max C 0, ?_⟩
    filter_upwards [hbound, pow_mul_exp_neg_le_one' M hδ, eventually_ge_atTop (1 : ℝ)]
      with u hu hexp1 hu1
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    rw [hevalR hu_ne, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, norm_mul,
      norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
    have hinvN : u⁻¹ ^ N ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu1)
    calc u⁻¹ ^ N * ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalU Q (u : ℂ))‖
        ≤ 1 * (C * Real.exp (-δ * u)) :=
          mul_le_mul hinvN hu (norm_nonneg _) zero_le_one
      _ ≤ max C 0 * Real.exp (-δ * u) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 / u ^ M := by
          rw [le_div_iff₀ (pow_pos hu_pos M)]
          calc max C 0 * Real.exp (-δ * u) * u ^ M
              = max C 0 * (u ^ M * Real.exp (-δ * u)) := by ring
            _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hexp1 (le_max_right C 0)
            _ = max C 0 := mul_one _
  have hR0 : MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
      (fun j : Fin (r + 1) => d_u^[j.val] S) R = 0 :=
    hexp.eq_zero_of_flat hflat
  -- Link R back to formalEvalPoly S Q via multiplication by single N 1 in LaurentSeries ℂ
  have hsingle_rev : ∀ p : Polynomial ℂ, p.natDegree ≤ N →
      HahnSeries.single (N : ℤ) (1 : ℂ) * polyToLaurent p =
        (((revP p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    intro p hp
    have hsum := Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
    conv_lhs => rw [hsum]
    have halg : ∀ c : ℂ, algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c :=
      HahnSeries.ofPowerSeries_C
    have hu_pow : ∀ k : ℕ, uLaurent ^ k = HahnSeries.single (-(k : ℤ)) (1 : ℂ) := by
      intro k
      induction k with
      | zero => simp [uLaurent]
      | succ k ih =>
        rw [pow_succ, ih, uLaurent, HahnSeries.single_mul_single, one_mul]
        have hidx : -(k : ℤ) + (-1 : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
        rw [hidx]
    have hL : HahnSeries.single (N : ℤ) (1 : ℂ) *
        polyToLaurent (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k) =
        ∑ k ∈ Finset.range (N + 1), HahnSeries.single (N : ℤ) (1 : ℂ) *
          (HahnSeries.C (p.coeff k) * uLaurent ^ k) := by
      simp only [polyToLaurent, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul,
        map_pow, Polynomial.aeval_C, Polynomial.aeval_X, halg, Finset.mul_sum]
    have hR' : (((revP p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ∑ k ∈ Finset.range (N + 1),
          HahnSeries.C (p.coeff k) *
            ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) := by
      dsimp only [revP]
      change HahnSeries.ofPowerSeries ℤ ℂ
        (Polynomial.coeToPowerSeries.ringHom
          (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k))) = _
      simp only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, HahnSeries.ofPowerSeries_C, Polynomial.coe_X]
    rw [hL, hR']
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hu_pow k]
    have hX : ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) =
        HahnSeries.single ((N - k : ℕ) : ℤ) (1 : ℂ) := by
      rw [← PowerSeries.coe_pow, HahnSeries.ofPowerSeries_X_pow]
    rw [hX, ← mul_assoc, mul_comm (HahnSeries.single (N : ℤ) 1) (HahnSeries.C (p.coeff k)),
      mul_assoc, HahnSeries.single_mul_single, one_mul]
    have hidx : (N : ℤ) + -(k : ℤ) = ((N - k : ℕ) : ℤ) := by omega
    rw [hidx, HahnSeries.C_apply, HahnSeries.single_mul_single]
  have hmul_eq : HahnSeries.single (N : ℤ) (1 : ℂ) * formalEvalPoly S Q =
      ((MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
        (fun j : Fin (r + 1) => d_u^[j.val] S) R : PowerSeries ℂ) : LaurentSeries ℂ) := by
    unfold formalEvalPoly
    rw [MvPolynomial.eval₂_eq', Finset.mul_sum]
    dsimp only [R]
    rw [MvPolynomial.eval₂_sum]
    simp_rw [MvPolynomial.eval₂_monomial]
    have hprod_eq : ∀ α : Fin (r + 1) →₀ ℕ,
        α.prod (fun j e => d_u^[j.val] S ^ e) = ∏ j : Fin (r + 1), d_u^[j.val] S ^ α j :=
      fun α => Finsupp.prod_of_support_subset α (Finset.subset_univ _) _ (fun _ _ => pow_zero _)
    simp_rw [hprod_eq]
    change ∑ α ∈ Q.support, HahnSeries.single (N : ℤ) (1 : ℂ) *
        (polyToLaurent (Q.coeff α) * ∏ j : Fin (r + 1), ((d_u^[j.val] S : PowerSeries ℂ) : LaurentSeries ℂ) ^ α j) =
      HahnSeries.ofPowerSeries ℤ ℂ (∑ α ∈ Q.support,
        (Polynomial.coeToPowerSeries.ringHom (revP (Q.coeff α)) *
          ∏ j : Fin (r + 1), (d_u^[j.val] S) ^ α j))
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← mul_assoc, hsingle_rev (Q.coeff α) (natDegree_le_maxUDeg Q α), map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow]
  rw [hR0] at hmul_eq
  have hzero_cast : ((0 : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := map_zero _
  rw [hzero_cast] at hmul_eq
  have hunit : HahnSeries.single (-(N : ℤ)) (1 : ℂ) * HahnSeries.single (N : ℤ) (1 : ℂ) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, one_mul]; rfl
  calc formalEvalPoly S Q = 1 * formalEvalPoly S Q := (one_mul _).symm
    _ = (HahnSeries.single (-(N : ℤ)) (1 : ℂ) * HahnSeries.single (N : ℤ) (1 : ℂ)) * formalEvalPoly S Q := by
          rw [hunit]
    _ = HahnSeries.single (-(N : ℤ)) (1 : ℂ) * (HahnSeries.single (N : ℤ) (1 : ℂ) * formalEvalPoly S Q) := by
          rw [mul_assoc]
    _ = 0 := by rw [hmul_eq, mul_zero]

/-- **Main Theorem (General `α`-Branch-Point Non-Autonomous Stokes–Vandermonde, `ℂ[u]`)**:
For any real exponent `α : ℝ` and any formal series `S ∈ ℂ[[1/u]]` admitting an `α`-branch-point
Stokes comb, `formalEvalPoly S P = 0` forces `P = 0`. -/
theorem branchPoint_stokes_vandermonde_no_ade
    {S : PowerSeries ℂ} {α : ℝ} {ω : ℕ → ℝ} {c : ℕ → ℂ}
    (h : BranchPointStokesData S α ω c)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly S P = 0) : P = 0 := by
  classical
  by_contra hP_ne
  have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      Q.totalDegree = d ∧ Q ≠ 0 ∧ formalEvalPoly S Q = 0 :=
    ⟨P.totalDegree, P, rfl, hP_ne, hP⟩
  let Pmin := Classical.choose (Nat.find_spec hex)
  have hPmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hPmin_deg : Pmin.totalDegree = Nat.find hex := hPmin_spec.1
  have hPmin_ne : Pmin ≠ 0 := hPmin_spec.2.1
  have hPmin_zero : formalEvalPoly S Pmin = 0 := hPmin_spec.2.2
  have hPmin_min : ∀ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      Q ≠ 0 → Q.totalDegree < Pmin.totalDegree → formalEvalPoly S Q ≠ 0 := by
    intro Q hQ_ne hQ_deg hQ_zero
    rw [hPmin_deg] at hQ_deg
    exact Nat.find_min hex hQ_deg ⟨Q, rfl, hQ_ne, hQ_zero⟩
  have hPmin_pos_deg : 0 < Pmin.totalDegree := by
    by_contra! hle
    have h0 : Pmin.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev0 : formalEvalPoly S
        (MvPolynomial.C (Pmin.coeff 0) : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) = 0 := by
      rw [← hC]; exact hPmin_zero
    have hp0 : polyToLaurent (Pmin.coeff 0) = 0 := by
      simpa [formalEvalPoly] using hev0
    have hcoeff0 : Pmin.coeff 0 = 0 := polyToLaurent_injective' (hp0.trans (map_zero _).symm)
    exact hPmin_ne (hC.trans (by rw [hcoeff0, map_zero]))
  have hω_pos : ∀ m : ℕ, 0 < ω m := fun m =>
    lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
  obtain ⟨hP_pos, hP_neg⟩ := h.borel_transfer Pmin hPmin_zero
  -- Strong induction: L_branch α r (ω n) Pmin = 0 for all n < r + 1
  have hL_zero : ∀ n : ℕ, n < r + 1 → L_branch α r (ω n : ℂ) Pmin = 0 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      have h_prev : ∀ m < n, L_branch α r (ω m : ℂ) Pmin = 0 := fun m hm =>
        ih m hm (lt_trans hm hn)
      -- Exact shift invariance eliminates all earlier Stokes modes m < n (and all nonlinear collisions!)
      have h_shift_sum : ∀ k ≤ n, ∀ (u : ℝ), 0 < u → ∀ (x : Fin (r + 1) → ℂ),
          MvPolynomial.eval
            (fun j : Fin (r + 1) => x j + ∑ m ∈ Finset.range k,
              c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u)
            (evalU Pmin (u : ℂ)) =
          MvPolynomial.eval x (evalU Pmin (u : ℂ)) := by
        intro k hk u hu x
        induction k with
        | zero => simp
        | succ k ihk =>
          have hkk : k < n := Nat.lt_of_succ_le hk
          have hL_u : ∑ j : Fin (r + 1),
              (Q_branch α r (ω k : ℂ) j.val).eval (u : ℂ) •
                MvPolynomial.pderiv j (evalU Pmin (u : ℂ)) = 0 := by
            rw [← evalU_L_branch, h_prev k hkk, evalU, map_zero]
          have h1 : (fun j : Fin (r + 1) =>
              x j + ∑ m ∈ Finset.range (k + 1),
                c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u) =
              (fun j : Fin (r + 1) =>
                (x j + ∑ m ∈ Finset.range k,
                  c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u) +
                  (c k * branchMode α (ω k : ℂ) u * (u : ℂ)⁻¹ ^ r) *
                    (Q_branch α r (ω k : ℂ) j.val).eval (u : ℂ)) := by
            funext j
            rw [Finset.sum_range_succ, add_assoc,
              iteratedDeriv_branchMode_eq_Q_branch α r (ω k : ℂ) (Nat.le_of_lt_succ j.isLt) hu]
            ring
          rw [h1, shift_invariant_of_pderiv_sum_eq_zero _ _ hL_u, ihk (Nat.le_of_lt hkk)]
      -- Gather uniform bounds on g_pos^(j), Q_branch, and Stokes remainder
      choose Bg hBg using fun j : Fin (r + 1) => HasAsympExp.eventually_bdd (h.g_pos_asymp j.val)
      have h_all_bg : ∀ᶠ u in atTop, ∀ j : Fin (r + 1), ‖iteratedDeriv j.val h.g_pos u‖ ≤ Bg j :=
        Filter.eventually_all.mpr hBg
      let M_q : ℝ := ∑ j : Fin (r + 1), ∑ k ∈ Finset.range (r + 1),
        ‖(Q_branch α r (ω n : ℂ) j.val).coeff k‖
      have hM_q_nonneg : 0 ≤ M_q := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      let M : ℝ := 2 + (∑ j : Fin (r + 1), |Bg j|) + M_q
      have hM_nonneg : 0 ≤ M := by
        have h1 : 0 ≤ ∑ j : Fin (r + 1), |Bg j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp only [M]; linarith
      have hBg_le : ∀ j : Fin (r + 1), |Bg j| + 2 ≤ M := fun j => by
        have hs : |Bg j| ≤ ∑ i : Fin (r + 1), |Bg i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (Bg i)) (Finset.mem_univ j)
        dsimp only [M]; linarith
      have hv_bdd : ∀ u : ℝ, 1 ≤ u → ∀ j : Fin (r + 1),
          ‖(u : ℂ)⁻¹ ^ r * (Q_branch α r (ω n : ℂ) j.val).eval (u : ℂ)‖ ≤ M := by
        intro u hu j
        have h1 := Q_branch_inv_pow_bdd α r (ω n : ℂ) j.val hu
        have h2 : ∑ k ∈ Finset.range (r + 1), ‖(Q_branch α r (ω n : ℂ) j.val).coeff k‖ ≤ M_q :=
          Finset.single_le_sum
            (f := fun j' : Fin (r + 1) => ∑ k ∈ Finset.range (r + 1),
              ‖(Q_branch α r (ω n : ℂ) j'.val).coeff k‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
        have h3 : 0 ≤ ∑ i : Fin (r + 1), |Bg i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp only [M]; linarith
      -- Stokes jump expansion for each j : Fin (r + 1)
      choose R_j hR_j_gt C_j h_jump_j using fun j : Fin (r + 1) => h.stokes_jump n j.val
      let R' : ℝ := Finset.univ.inf' Finset.univ_nonempty R_j
      have hR'_gt : ω n < R' := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun j _ => hR_j_gt j
      have hR'_le : ∀ j : Fin (r + 1), R' ≤ R_j j := fun j => Finset.inf'_le R_j (Finset.mem_univ j)
      have hR'_pos : 0 < R' := lt_trans (hω_pos n) hR'_gt
      let C_rem : ℝ := ∑ j : Fin (r + 1), max (C_j j) 0
      have hC_rem_nonneg : 0 ≤ C_rem := Finset.sum_nonneg fun _ _ => le_max_right _ _
      have h_all_jump : ∀ᶠ u in atTop, ∀ j : Fin (r + 1),
          ‖iteratedDeriv j.val h.g_neg u - iteratedDeriv j.val h.g_pos u -
            ∑ m ∈ Finset.range (n + 1), c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖ ≤
            C_rem * Real.exp (-R' * u) := by
        filter_upwards [Filter.eventually_all.mpr h_jump_j, eventually_ge_atTop (0 : ℝ)] with u hu hu0 j
        refine (hu j).trans ?_
        have hexp_le : Real.exp (-R_j j * u) ≤ Real.exp (-R' * u) :=
          Real.exp_le_exp.mpr (by nlinarith [hR'_le j])
        calc C_j j * Real.exp (-R_j j * u)
            ≤ max (C_j j) 0 * Real.exp (-R_j j * u) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ max (C_j j) 0 * Real.exp (-R' * u) :=
              mul_le_mul_of_nonneg_left hexp_le (le_max_right _ _)
          _ ≤ C_rem * Real.exp (-R' * u) :=
              mul_le_mul_of_nonneg_right
                (Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j))
                (Real.exp_pos _).le
      -- Bound the finite Stokes sum ∑_{m ≤ n} c_m (d/du)^j (branchMode α (ω m)) u ≤ 1 eventually
      have hS_le1 : ∀ᶠ u : ℝ in atTop, ∀ j : Fin (r + 1),
          ‖∑ m ∈ Finset.range (n + 1), c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖ ≤ 1 := by
        have hterm : ∀ j : Fin (r + 1), ∀ m ∈ Finset.range (n + 1),
            ∀ᶠ u : ℝ in atTop,
              ‖c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
          intro j m _
          let Bq : ℝ := ∑ k ∈ Finset.range (r + 1), ‖(Q_branch α r (ω m : ℂ) j.val).coeff k‖
          let K : ℝ := (‖c m‖ * Bq + 1) * ((n + 1 : ℕ) : ℝ)
          let p : ℕ := Nat.ceil (max (-α) 0)
          have hK_pos : 0 < K := by positivity
          filter_upwards [pow_mul_exp_neg_le_one' (p + 1) (hω_pos m),
            eventually_ge_atTop (max K 1)] with u hpe huK
          have hu1 : 1 ≤ u := (le_max_right K 1).trans huK
          have huK' : K ≤ u := (le_max_left K 1).trans huK
          have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          rw [iteratedDeriv_branchMode_eq_Q_branch α r (ω m : ℂ) (Nat.le_of_lt_succ j.isLt) hu_pos,
            norm_mul, norm_mul, norm_branchMode α (ω m) hu_pos]
          have hq := Q_branch_inv_pow_bdd α r (ω m : ℂ) j.val hu1
          have hrp := rpow_le_pow_of_ge_one (-α) hu1
          have h1 : ‖c m‖ * (Real.rpow u (-α) * Real.exp (-ω m * u)) *
              ‖(u : ℂ)⁻¹ ^ r * (Q_branch α r (ω m : ℂ) j.val).eval (u : ℂ)‖ ≤
              (‖c m‖ * Bq + 1) * (u ^ p * Real.exp (-ω m * u)) := by
            have hBq_nonneg : 0 ≤ Bq := Finset.sum_nonneg fun _ _ => norm_nonneg _
            calc ‖c m‖ * (Real.rpow u (-α) * Real.exp (-ω m * u)) *
                  ‖(u : ℂ)⁻¹ ^ r * (Q_branch α r (ω m : ℂ) j.val).eval (u : ℂ)‖
                ≤ ‖c m‖ * (u ^ p * Real.exp (-ω m * u)) * Bq := by
                  refine mul_le_mul ?_ hq (norm_nonneg _) (by positivity)
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hrp (Real.exp_pos _).le) (norm_nonneg _)
              _ = (‖c m‖ * Bq) * (u ^ p * Real.exp (-ω m * u)) := by ring
              _ ≤ (‖c m‖ * Bq + 1) * (u ^ p * Real.exp (-ω m * u)) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          rw [← mul_assoc]
          refine h1.trans ?_
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
          have h2 : (‖c m‖ * Bq + 1) * (u ^ p * Real.exp (-ω m * u)) * ((n + 1 : ℕ) : ℝ) =
              K * (u ^ p * Real.exp (-ω m * u)) := by dsimp only [K]; ring
          rw [h2]
          calc K * (u ^ p * Real.exp (-ω m * u))
              ≤ u * (u ^ p * Real.exp (-ω m * u)) :=
                mul_le_mul_of_nonneg_right huK' (by positivity)
            _ = u ^ (p + 1) * Real.exp (-ω m * u) := by rw [pow_succ']; ring
            _ ≤ 1 := hpe
        have hall := Filter.eventually_all.mpr fun j : Fin (r + 1) =>
          (Filter.eventually_all_finset (Finset.range (n + 1))).mpr fun m hm => hterm j m hm
        filter_upwards [hall] with u hu j
        refine (norm_sum_le _ _).trans ?_
        calc ∑ m ∈ Finset.range (n + 1),
              ‖c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u‖
            ≤ ∑ _m ∈ Finset.range (n + 1), (1 / ((n + 1 : ℕ) : ℝ)) :=
              Finset.sum_le_sum fun m hm => hu j m hm
          _ = 1 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div,
                mul_inv_cancel₀ (by positivity)]
      -- Assemble Lipschitz + Taylor bounds for Pmin
      let Du : ℕ := maxUDeg Pmin
      choose C_lip_k hC_lip_k h_lip_k using
        fun k : ℕ => eval_lipschitz_of_bounded (coeffU k Pmin) hM_nonneg
      choose C_tay_k hC_tay_k h_tay_k using
        fun k : ℕ => eval_shift_taylor_bound (coeffU k Pmin) hM_nonneg
      let C_L : ℝ := ∑ k ∈ Finset.range (Du + 1), C_lip_k k
      let C_T : ℝ := ∑ k ∈ Finset.range (Du + 1), C_tay_k k
      have hC_L_nonneg : 0 ≤ C_L := Finset.sum_nonneg fun k _ => hC_lip_k k
      have hC_T_nonneg : 0 ≤ C_T := Finset.sum_nonneg fun k _ => hC_tay_k k
      let δ₀ : ℝ := min (ω n) (R' - ω n)
      have hδ₀_pos : 0 < δ₀ := lt_min (hω_pos n) (sub_pos.mpr hR'_gt)
      let p_neg : ℕ := Nat.ceil (max (-α) 0)
      let p_pos : ℕ := Nat.ceil (max α 0)
      have hcn_pos : 0 < ‖c n‖ := norm_pos_iff.mpr (h.c_ne_zero n)
      -- Eventually ‖c n‖ * u^{-α} * e^{-ω_n u} ≤ 1
      have ha_small : ∀ᶠ u : ℝ in atTop, ‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u) ≤ 1 := by
        filter_upwards [pow_mul_exp_neg_le_one' (p_neg + 1) (hω_pos n),
          eventually_ge_atTop (max ‖c n‖ 1)] with u hpe huK
        have hu1 : 1 ≤ u := (le_max_right _ _).trans huK
        have huc : ‖c n‖ ≤ u := (le_max_left _ _).trans huK
        calc ‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u)
            ≤ u * u ^ p_neg * Real.exp (-ω n * u) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              exact mul_le_mul huc (rpow_le_pow_of_ge_one (-α) hu1)
                (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hu1) _).le (by linarith)
          _ = u ^ (p_neg + 1) * Real.exp (-ω n * u) := by rw [pow_succ']
          _ ≤ 1 := hpe
      have hrem_small : ∀ᶠ u : ℝ in atTop, C_rem * Real.exp (-R' * u) ≤ 1 := by
        filter_upwards [pow_mul_exp_neg_le_one' 1 hR'_pos,
          eventually_ge_atTop (max C_rem 1)] with u hpe huK
        have hu1 : 1 ≤ u := (le_max_right _ _).trans huK
        have huC : C_rem ≤ u := (le_max_left _ _).trans huK
        calc C_rem * Real.exp (-R' * u) ≤ u ^ 1 * Real.exp (-R' * u) := by
              rw [pow_one]; exact mul_le_mul_of_nonneg_right huC (Real.exp_pos _).le
          _ ≤ 1 := hpe
      have hu_poly_exp : ∀ᶠ u : ℝ in atTop,
          u ^ (Du + r + p_pos + p_neg) * Real.exp (-(δ₀ / 2) * u) ≤ 1 :=
        pow_mul_exp_neg_le_one' (Du + r + p_pos + p_neg) (half_pos hδ₀_pos)
      -- Key exponential decay bound on (L_branch α r (ω n) Pmin)(u, g_pos(u))
      let C_fin : ℝ := (C_L * C_rem) / ‖c n‖ + C_T * ‖c n‖
      have h_bridge_bound : ∀ᶠ u : ℝ in atTop,
          ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val h.g_pos u)
            (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ))‖ ≤
            C_fin * Real.exp (-(δ₀ / 2) * u) := by
        filter_upwards [h_all_bg, h_all_jump, hP_pos, hP_neg, hS_le1, ha_small, hrem_small,
          hu_poly_exp, eventually_ge_atTop (1 : ℝ)]
          with u hbg hjump hpos hneg hS1 ha1 hrem1 hpoly_u hu1
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
        have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
        let x : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val h.g_pos u
        let Svec : Fin (r + 1) → ℂ := fun j => ∑ m ∈ Finset.range (n + 1),
          c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u
        let y : Fin (r + 1) → ℂ := fun j => x j + Svec j
        let z : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val h.g_neg u
        let a : ℂ := c n * branchMode α (ω n : ℂ) u
        let v : Fin (r + 1) → ℂ := fun j =>
          (u : ℂ)⁻¹ ^ r * (Q_branch α r (ω n : ℂ) j.val).eval (u : ℂ)
        have hx_le : ∀ j, ‖x j‖ ≤ M := fun j =>
          (hbg j).trans ((le_abs_self _).trans (by linarith [hBg_le j]))
        have hy_le : ∀ j, ‖y j‖ ≤ M := fun j => by
          calc ‖y j‖ ≤ ‖x j‖ + ‖Svec j‖ := norm_add_le _ _
            _ ≤ |Bg j| + 1 := add_le_add ((hbg j).trans (le_abs_self _)) (hS1 j)
            _ ≤ M := by linarith [hBg_le j]
        have hzy_le : ∀ j, ‖z j - y j‖ ≤ C_rem * Real.exp (-R' * u) := fun j => by
          have hsub_eq : z j - y j = iteratedDeriv j.val h.g_neg u - iteratedDeriv j.val h.g_pos u - Svec j := by
            simp only [y, x, z]; ring
          rw [hsub_eq]; exact hjump j
        have hz_le : ∀ j, ‖z j‖ ≤ M := fun j => by
          have hid : z j = y j + (z j - y j) := by ring
          rw [hid]
          calc ‖y j + (z j - y j)‖ ≤ ‖y j‖ + ‖z j - y j‖ := norm_add_le _ _
            _ ≤ (|Bg j| + 1) + 1 :=
                add_le_add ((norm_add_le _ _).trans
                  (add_le_add ((hbg j).trans (le_abs_self _)) (hS1 j)))
                  ((hzy_le j).trans hrem1)
            _ ≤ M := by linarith [hBg_le j]
        have ha_norm : ‖a‖ = ‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u) := by
          simp only [a, norm_mul, norm_branchMode α (ω n) hu_pos]; ring
        have ha_le1 : ‖a‖ ≤ 1 := by rw [ha_norm]; exact ha1
        have ha_pos : 0 < ‖a‖ := by
          rw [ha_norm]
          exact mul_pos (mul_pos hcn_pos (Real.rpow_pos_of_pos hu_pos _)) (Real.exp_pos _)
        have hu_pow_le : ∀ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k‖ ≤ u ^ Du := fun k hk => by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
          exact pow_le_pow_right₀ hu1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        -- Step A: Lipschitz bound ‖Pmin(u, y)‖ ≤ C_L * C_rem * u^Du * e^{-R' u}
        have h_lip_y : ‖MvPolynomial.eval y (evalU Pmin (u : ℂ))‖ ≤
            (C_L * C_rem) * u ^ Du * Real.exp (-R' * u) := by
          have hyz : MvPolynomial.eval y (evalU Pmin (u : ℂ)) =
              ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                (MvPolynomial.eval y (coeffU k Pmin) - MvPolynomial.eval z (coeffU k Pmin)) := by
            have hneg' : MvPolynomial.eval z (evalU Pmin (u : ℂ)) = 0 := hneg
            rw [← sub_zero (MvPolynomial.eval y (evalU Pmin (u : ℂ))), ← hneg']
            dsimp only [Du]
            simp only [evalU_eq_sum_coeffU Pmin (u : ℂ), map_sum, MvPolynomial.smul_eq_C_mul,
              map_mul, MvPolynomial.eval_C, ← Finset.sum_sub_distrib, ← mul_sub]
          rw [hyz]
          calc ‖∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                  (MvPolynomial.eval y (coeffU k Pmin) - MvPolynomial.eval z (coeffU k Pmin))‖
              ≤ ∑ k ∈ Finset.range (Du + 1),
                  ‖(u : ℂ) ^ k * (MvPolynomial.eval y (coeffU k Pmin) - MvPolynomial.eval z (coeffU k Pmin))‖ :=
                norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.range (Du + 1),
                  u ^ Du * (C_lip_k k * (C_rem * Real.exp (-R' * u))) := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_mul]
                have hlk := h_lip_k k z y (C_rem * Real.exp (-R' * u))
                  (mul_nonneg hC_rem_nonneg (Real.exp_pos _).le) hz_le hy_le hzy_le
                rw [norm_sub_rev] at hlk
                exact mul_le_mul (hu_pow_le k hk) hlk (norm_nonneg _) (pow_nonneg hu_pos.le Du)
            _ = (C_L * C_rem) * u ^ Du * Real.exp (-R' * u) := by
                dsimp only [C_L]
                rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
        -- Step B: Exact shift invariance removes all modes m < n from Pmin(u, y)!
        have h_shift_y : MvPolynomial.eval y (evalU Pmin (u : ℂ)) =
            MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) := by
          have hy_split : y = fun j : Fin (r + 1) =>
              (x j + a * v j) + ∑ m ∈ Finset.range n,
                c m * iteratedDeriv j.val (branchMode α (ω m : ℂ)) u := by
            funext j
            simp only [y, Svec, a, v]
            rw [Finset.sum_range_succ,
              iteratedDeriv_branchMode_eq_Q_branch α r (ω n : ℂ) (Nat.le_of_lt_succ j.isLt) hu_pos]
            ring
          rw [hy_split]
          exact h_shift_sum n (le_refl n) u hu_pos (fun j => x j + a * v j)
        -- Step C: Multivariate Taylor bound on Pmin(u, x + a v) - Pmin(u, x) - a * (u^{-r} L_branch Pmin)(u, x)
        have h_lin_eq : ∑ j : Fin (r + 1),
            MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
            (u : ℂ)⁻¹ ^ r * MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ)) := by
          rw [evalU_L_branch, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
          dsimp only [v]; ring
        have h_tay_y : ‖MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) -
            a * ((u : ℂ)⁻¹ ^ r * MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ)))‖ ≤
            C_T * u ^ Du * ‖a‖ ^ 2 := by
          have hpos' : MvPolynomial.eval x (evalU Pmin (u : ℂ)) = 0 := hpos
          rw [← h_lin_eq]
          have hdecomp : MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) -
              a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
              ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                (MvPolynomial.eval (fun j => x j + a * v j) (coeffU k Pmin) -
                  MvPolynomial.eval x (coeffU k Pmin) -
                  a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (coeffU k Pmin)) * v j) := by
            have h1 : MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) -
                MvPolynomial.eval x (evalU Pmin (u : ℂ)) -
                a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
                MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) -
                  a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j := by
              rw [hpos', sub_zero]
            rw [← h1]
            dsimp only [Du]
            have hpd : ∀ j : Fin (r + 1),
                MvPolynomial.pderiv j (evalU Pmin (u : ℂ)) =
                ∑ k ∈ Finset.range (maxUDeg Pmin + 1), (u : ℂ) ^ k • MvPolynomial.pderiv j (coeffU k Pmin) := by
              intro j
              rw [evalU_eq_sum_coeffU Pmin (u : ℂ), map_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Derivation.map_smul_of_tower]
            have hsum_3 : a * ∑ j : Fin (r + 1),
                MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
                ∑ k ∈ Finset.range (maxUDeg Pmin + 1), (u : ℂ) ^ k *
                  (a * ∑ j : Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv j (coeffU k Pmin)) * v j) := by
              simp_rw [hpd, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
                Finset.sum_mul]
              rw [Finset.mul_sum]
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              refine Finset.sum_congr rfl fun j _ => by ring
            rw [hsum_3]
            simp only [evalU_eq_sum_coeffU Pmin (u : ℂ), map_sum, MvPolynomial.smul_eq_C_mul,
              map_mul, MvPolynomial.eval_C, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun k _ => by ring
          rw [hdecomp]
          calc ‖∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                  (MvPolynomial.eval (fun j => x j + a * v j) (coeffU k Pmin) -
                    MvPolynomial.eval x (coeffU k Pmin) -
                    a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (coeffU k Pmin)) * v j)‖
              ≤ ∑ k ∈ Finset.range (Du + 1),
                  ‖(u : ℂ) ^ k *
                    (MvPolynomial.eval (fun j => x j + a * v j) (coeffU k Pmin) -
                      MvPolynomial.eval x (coeffU k Pmin) -
                      a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (coeffU k Pmin)) * v j)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.range (Du + 1), u ^ Du * (C_tay_k k * ‖a‖ ^ 2) := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_mul]
                exact mul_le_mul (hu_pow_le k hk) (h_tay_k k x v a hx_le (hv_bdd u hu1) ha_le1)
                  (norm_nonneg _) (pow_nonneg hu_pos.le Du)
            _ = C_T * u ^ Du * ‖a‖ ^ 2 := by
                dsimp only [C_T]
                rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
        -- Step D: Triangle inequality & divide by ‖a‖ * u^{-r}
        have h_comb : ‖a‖ * u⁻¹ ^ r *
            ‖MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ))‖ ≤
            (C_L * C_rem) * u ^ Du * Real.exp (-R' * u) + C_T * u ^ Du * ‖a‖ ^ 2 := by
          have hlhs : ‖a‖ * u⁻¹ ^ r *
              ‖MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ))‖ =
              ‖a * ((u : ℂ)⁻¹ ^ r * MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ)))‖ := by
            symm
            rw [norm_mul a, norm_mul ((u : ℂ)⁻¹ ^ r), norm_pow, norm_inv, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hu_pos, mul_assoc]
          rw [hlhs]
          have htri : ‖a * ((u : ℂ)⁻¹ ^ r * MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ)))‖ ≤
              ‖MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ))‖ +
              ‖MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) -
                a * ((u : ℂ)⁻¹ ^ r * MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ)))‖ := by
            have := norm_sub_le (MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)))
              (MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) -
                a * ((u : ℂ)⁻¹ ^ r * MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ))))
            simpa [sub_sub_cancel] using this
          have h_lip_av : ‖MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ))‖ ≤
              (C_L * C_rem) * u ^ Du * Real.exp (-R' * u) := by
            rwa [← h_shift_y]
          exact htri.trans (add_le_add h_lip_av h_tay_y)
        -- Multiply by u^r / ‖a‖
        have h_div : ‖MvPolynomial.eval x (evalU (L_branch α r (ω n : ℂ) Pmin) (u : ℂ))‖ ≤
            ((C_L * C_rem) * u ^ (Du + r) * Real.exp (-R' * u)) / ‖a‖ +
              C_T * u ^ (Du + r) * ‖a‖ := by
          have hpos_au : 0 < ‖a‖ * u⁻¹ ^ r := mul_pos ha_pos (by positivity)
          have hstep := (le_div_iff₀' hpos_au).mpr h_comb
          refine hstep.trans_eq ?_
          rw [inv_pow]
          field_simp [ha_pos.ne', (pow_pos hu_pos r).ne']
          rw [pow_add]; ring
        refine h_div.trans ?_
        -- Bound both terms by C_fin * exp(-(δ₀/2) * u)
        have hrp_inv : (Real.rpow u (-α))⁻¹ = Real.rpow u α := by
          change (u ^ (-α))⁻¹ = u ^ α
          rw [← Real.rpow_neg hu_pos.le, neg_neg]
        have hrp_pos_le : Real.rpow u α ≤ u ^ p_pos := rpow_le_pow_of_ge_one α hu1
        have hrp_neg_le : Real.rpow u (-α) ≤ u ^ p_neg := rpow_le_pow_of_ge_one (-α) hu1
        have hterm1 : ((C_L * C_rem) * u ^ (Du + r) * Real.exp (-R' * u)) / ‖a‖ ≤
            ((C_L * C_rem) / ‖c n‖) * Real.exp (-(δ₀ / 2) * u) := by
          rw [ha_norm]
          have hrew : ((C_L * C_rem) * u ^ (Du + r) * Real.exp (-R' * u)) /
              (‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u)) =
              ((C_L * C_rem) / ‖c n‖) * (u ^ (Du + r) * Real.rpow u α * Real.exp (-(R' - ω n) * u)) := by
            have hrexp : Real.exp (-R' * u) / Real.exp (-ω n * u) = Real.exp (-(R' - ω n) * u) := by
              rw [← Real.exp_sub]; congr 1; ring
            rw [← hrp_inv]
            field_simp [hcn_pos.ne', (Real.rpow_pos_of_pos hu_pos _).ne', (Real.exp_pos _).ne']
            rw [mul_assoc (C_L * C_rem), ← Real.exp_add]
            congr 2
            ring
          rw [hrew]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpow_le : u ^ (Du + r) * Real.rpow u α ≤ u ^ (Du + r + p_pos + p_neg) := by
            calc u ^ (Du + r) * Real.rpow u α
                ≤ u ^ (Du + r) * u ^ p_pos := mul_le_mul_of_nonneg_left hrp_pos_le (by positivity)
              _ = u ^ (Du + r + p_pos) := (pow_add _ _ _).symm
              _ ≤ u ^ (Du + r + p_pos + p_neg) := pow_le_pow_right₀ hu1 (Nat.le_add_right _ _)
          have hexp_le : Real.exp (-(R' - ω n) * u) ≤ Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u) := by
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            have hδle : δ₀ ≤ R' - ω n := min_le_right _ _
            nlinarith
          calc u ^ (Du + r) * Real.rpow u α * Real.exp (-(R' - ω n) * u)
              ≤ u ^ (Du + r + p_pos + p_neg) * (Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u)) :=
                mul_le_mul hpow_le hexp_le (Real.exp_pos _).le (by positivity)
            _ = (u ^ (Du + r + p_pos + p_neg) * Real.exp (-(δ₀ / 2) * u)) * Real.exp (-(δ₀ / 2) * u) := by ring
            _ ≤ 1 * Real.exp (-(δ₀ / 2) * u) := mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le
            _ = Real.exp (-(δ₀ / 2) * u) := one_mul _
        have hterm2 : C_T * u ^ (Du + r) * ‖a‖ ≤ (C_T * ‖c n‖) * Real.exp (-(δ₀ / 2) * u) := by
          rw [ha_norm]
          have hrew : C_T * u ^ (Du + r) * (‖c n‖ * Real.rpow u (-α) * Real.exp (-ω n * u)) =
              (C_T * ‖c n‖) * (u ^ (Du + r) * Real.rpow u (-α) * Real.exp (-ω n * u)) := by ring
          rw [hrew]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpow_le : u ^ (Du + r) * Real.rpow u (-α) ≤ u ^ (Du + r + p_pos + p_neg) := by
            calc u ^ (Du + r) * Real.rpow u (-α)
                ≤ u ^ (Du + r) * u ^ p_neg := mul_le_mul_of_nonneg_left hrp_neg_le (by positivity)
              _ = u ^ (Du + r + p_neg) := (pow_add _ _ _).symm
              _ ≤ u ^ (Du + r + p_pos + p_neg) := pow_le_pow_right₀ hu1 (by omega)
          have hexp_le : Real.exp (-ω n * u) ≤ Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u) := by
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            have hδle : δ₀ ≤ ω n := min_le_left _ _
            nlinarith
          calc u ^ (Du + r) * Real.rpow u (-α) * Real.exp (-ω n * u)
              ≤ u ^ (Du + r + p_pos + p_neg) * (Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u)) :=
                mul_le_mul hpow_le hexp_le (Real.exp_pos _).le (by positivity)
            _ = (u ^ (Du + r + p_pos + p_neg) * Real.exp (-(δ₀ / 2) * u)) * Real.exp (-(δ₀ / 2) * u) := by ring
            _ ≤ 1 * Real.exp (-(δ₀ / 2) * u) := mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le
            _ = Real.exp (-(δ₀ / 2) * u) := one_mul _
        dsimp only [C_fin]
        linarith
      -- Therefore formalEvalPoly S (L_branch α r (ω n) Pmin) = 0!
      have hL_formal : formalEvalPoly S (L_branch α r (ω n : ℂ) Pmin) = 0 :=
        formalEvalPoly_eq_zero_of_evalU_exp_small h.g_pos_asymp (L_branch α r (ω n : ℂ) Pmin)
          (half_pos hδ₀_pos) h_bridge_bound
      by_contra hL_ne
      exact hPmin_min (L_branch α r (ω n : ℂ) Pmin) hL_ne
        (degree_L_branch_lt α (ω n : ℂ) Pmin hPmin_pos_deg) hL_formal
  -- Vandermonde contradiction on the r + 1 distinct frequencies ω 0, ..., ω r!
  have hω_inj : Function.Injective (fun n : Fin (r + 1) => (ω n.val : ℂ)) := by
    intro a b hab
    exact Fin.ext (h.ω_mono.injective (Complex.ofReal_injective hab))
  exact L_branch_vandermonde_contradiction α (fun n : Fin (r + 1) => (ω n.val : ℂ)) hω_inj
    Pmin hPmin_pos_deg (fun n => hL_zero n.val n.isLt)

/-- **Asymptotic-Transfer `ℂ[u]` Theorem**:
Any function `M : ℝ → ℂ` sharing the all-orders `1/u` asymptotic expansion `d_u^[j] S` of a
branch-point Stokes comb satisfies NO nonzero `ℂ[u]`-ADE. -/
theorem branchPoint_stokes_vandermonde_no_ade_of_asymp
    {S : PowerSeries ℂ} {α : ℝ} {ω : ℕ → ℝ} {c : ℕ → ℂ}
    (h : BranchPointStokesData S α ω c)
    {M : ℝ → ℂ}
    (hM_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j M) (d_u^[j] S))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val M u) (evalU P (u : ℂ)) = 0) :
    P = 0 := by
  have hbound : ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val M u) (evalU P (u : ℂ))‖ ≤
        (0 : ℝ) * Real.exp (-(1 : ℝ) * u) := by
    filter_upwards [hP] with u hu
    simp [hu]
  exact branchPoint_stokes_vandermonde_no_ade h P
    (formalEvalPoly_eq_zero_of_evalU_exp_small hM_asymp P zero_lt_one hbound)

private lemma poly_eval_eventually_ne_zero' {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∀ᶠ u : ℝ in atTop, q.eval (u : ℂ) ≠ 0 := by
  let B : ℝ := Finset.sum q.roots.toFinset fun z : ℂ => ‖z‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  filter_upwards [eventually_gt_atTop B] with u hu h0
  have hmem : (u : ℂ) ∈ q.roots := (Polynomial.mem_roots hq).mpr h0
  have hle : ‖(u : ℂ)‖ ≤ B :=
    Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _)
      (Multiset.mem_toFinset.mpr hmem)
  have hpos : 0 < u := lt_of_le_of_lt hB hu
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hle
  linarith

/-- **Asymptotic-Transfer `ℂ(u)` Theorem**:
Any function `M : ℝ → ℂ` sharing the all-orders `1/u` asymptotic expansion `d_u^[j] S` of a
branch-point Stokes comb satisfies NO nonzero rational-coefficient `ℂ(u)`-ADE. -/
theorem branchPoint_stokes_vandermonde_no_rat_ade_of_asymp
    {S : PowerSeries ℂ} {α : ℝ} {ω : ℕ → ℝ} {c : ℕ → ℂ}
    (h : BranchPointStokesData S α ω c)
    {M : ℝ → ℂ}
    (hM_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j M) (d_u^[j] S))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val M u) (evalRatU P (u : ℂ)) = 0) :
    P = 0 := by
  classical
  let D : Polynomial ℂ := ∏ β ∈ P.support, (P.coeff β).denom
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ α ∈ P.support, MvPolynomial.monomial α
      ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)
  have hden : ∀ᶠ u : ℝ in atTop, ∀ β ∈ P.support, (P.coeff β).denom.eval (u : ℂ) ≠ 0 :=
    (Filter.eventually_all_finset P.support).mpr fun β _ =>
      poly_eval_eventually_ne_zero' (RatFunc.denom_ne_zero _)
  have hQ_zero : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val M u) (evalU Q (u : ℂ)) = 0 := by
    filter_upwards [hP, hden] with u hu hdu
    have hclear : evalU Q (u : ℂ) = D.eval (u : ℂ) • evalRatU P (u : ℂ) := by
      ext α
      rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, MvPolynomial.coeff_smul,
        smul_eq_mul, evalRatU, MvPolynomial.coeff_sum]
      rw [MvPolynomial.coeff_sum]
      simp_rw [MvPolynomial.coeff_monomial]
      by_cases hα : α ∈ P.support
      · rw [Finset.sum_eq_single α, Finset.sum_eq_single α]
        · simp only [↓reduceIte, ratEval, D, Polynomial.eval_mul, Polynomial.eval_prod]
          rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval (u : ℂ)) hα]
          field_simp [hdu α hα]
        · intro β _ hβα; simp [hβα]
        · intro hnot; exact absurd hα hnot
        · intro β _ hβα; simp [hβα]
        · intro hnot; exact absurd hα hnot
      · have hsum1 : (∑ x ∈ P.support,
            if x = α then (P.coeff x).num * ∏ β ∈ P.support.erase x, (P.coeff β).denom else 0) = 0 :=
          Finset.sum_eq_zero fun β hβ => ite_eq_right_iff.mpr fun hβα => by subst hβα; exact absurd hβ hα
        have hsum2 : (∑ x ∈ P.support, if x = α then ratEval (P.coeff x) (u : ℂ) else 0) = 0 :=
          Finset.sum_eq_zero fun β hβ => ite_eq_right_iff.mpr fun hβα => by subst hβα; exact absurd hβ hα
        rw [hsum1, hsum2, Polynomial.eval_zero, mul_zero]
    rw [hclear, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hu, mul_zero]
  have hQ0 : Q = 0 := branchPoint_stokes_vandermonde_no_ade_of_asymp h hM_asymp Q hQ_zero
  ext α
  change P.coeff α = 0
  by_contra hα_ne
  have hα_mem : α ∈ P.support := MvPolynomial.mem_support_iff.mpr hα_ne
  have hQc : Q.coeff α = 0 := by rw [hQ0]; rfl
  dsimp only [Q] at hQc
  rw [MvPolynomial.coeff_sum] at hQc
  simp_rw [MvPolynomial.coeff_monomial] at hQc
  rw [Finset.sum_eq_single α] at hQc
  · simp only [↓reduceIte] at hQc
    have hprod_ne : (∏ β ∈ P.support.erase α, (P.coeff β).denom) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun β _ => RatFunc.denom_ne_zero _
    have hnum0 : (P.coeff α).num = 0 := (mul_eq_zero.mp hQc).resolve_right hprod_ne
    exact hα_ne (RatFunc.num_eq_zero_iff.mp hnum0)
  · intro β _ hβα; simp [hβα]
  · intro hnot; exact absurd hα_mem hnot

/-! ### 4. Exponentially Small Modular-Companion Absorption -/

/-- A function `T : ℝ → ℂ` whose `j`-th derivative decays exponentially (`O(u^A e^{-δ u})`)
has zero all-orders `1/u` asymptotic expansion. -/
theorem HasAsympExp.zero_of_exp_decay {T : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) {A : ℕ} {C : ℝ}
    (hT : ∀ᶠ u : ℝ in atTop, ‖T u‖ ≤ C * u ^ A * Real.exp (-δ * u)) :
    HasAsympExp T 0 := by
  intro M
  refine ⟨max C 0, ?_⟩
  filter_upwards [hT, pow_mul_exp_neg_le_one' (A + M) hδ, eventually_ge_atTop (1 : ℝ)]
    with u hu hpe hu1
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  simp only [map_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  refine hu.trans ?_
  rw [le_div_iff₀ (pow_pos hu_pos M)]
  calc C * u ^ A * Real.exp (-δ * u) * u ^ M
      ≤ max C 0 * u ^ A * Real.exp (-δ * u) * u ^ M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
            (Real.exp_pos _).le)
          (by positivity)
    _ = max C 0 * (u ^ (A + M) * Real.exp (-δ * u)) := by rw [pow_add]; ring
    _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hpe (le_max_right C 0)
    _ = max C 0 := mul_one _

private lemma eventually_nhds_of_eventually_atTop {p : ℝ → Prop}
    (h : ∀ᶠ t : ℝ in atTop, p t) : ∀ᶠ u : ℝ in atTop, ∀ᶠ t : ℝ in 𝓝 u, p t := by
  rw [Filter.eventually_atTop] at h
  obtain ⟨B, hB⟩ := h
  filter_upwards [eventually_gt_atTop B] with u hu
  filter_upwards [eventually_gt_nhds hu] with t ht
  exact hB t ht.le

/-- Adding an exponentially small modular companion `T` (with exponentially decaying derivatives)
preserves the all-orders `1/u` asymptotic expansion of every derivative `iteratedDeriv j`. -/
theorem HasAsympExp.add_exp_companion {I T : ℝ → ℂ} {S : PowerSeries ℂ}
    (hI_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j I) u)
    (hT_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j T) u)
    (hI : ∀ j : ℕ, HasAsympExp (iteratedDeriv j I) (d_u^[j] S))
    (hT : ∀ j : ℕ, ∃ δ > 0, ∃ A : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j T u‖ ≤ C * u ^ A * Real.exp (-δ * u)) :
    ∀ j : ℕ, HasAsympExp (iteratedDeriv j (fun u => I u + T u)) (d_u^[j] S) := by
  have hadd_deriv : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t => I t + T t) u = iteratedDeriv j I u + iteratedDeriv j T u := by
    intro j
    induction j with
    | zero => exact Filter.Eventually.of_forall fun _ => rfl
    | succ j ih =>
      have hev : ∀ᶠ u : ℝ in atTop,
          iteratedDeriv j (fun t => I t + T t) =ᶠ[𝓝 u]
            fun t => iteratedDeriv j I t + iteratedDeriv j T t :=
        eventually_nhds_of_eventually_atTop ih
      filter_upwards [hev, hI_diff j, hT_diff j] with u hu hIu hTu
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, hu.deriv_eq]
      exact deriv_add hIu hTu
  intro j M
  obtain ⟨δ, hδ, A, CT, hCT⟩ := hT j
  have hT0 : HasAsympExp (iteratedDeriv j T) 0 := HasAsympExp.zero_of_exp_decay hδ hCT
  obtain ⟨C1, hC1⟩ := (hI j).add hT0 M
  refine ⟨C1, ?_⟩
  filter_upwards [hC1, hadd_deriv j] with u hu hdu
  simpa [add_zero, hdu] using hu

/-- **Modular-Companion Absorption Corollary (`ℂ(u)`-D-Transcendence)**:
If `M(u) = I(u) + T(u)` where `I` matches an `α`-branch-point Stokes comb (e.g. Ramanujan's
Mordell integral for `f(q)` or `ω(q)`, or Zagier's Eichler integral for `H(q)`) and `T` is
exponentially small in every derivative (the modular partner `2√(2u) e^{-4πu/3} ω(e^{-2πu})`),
then `M` satisfies NO nonzero rational-coefficient differential equation over `ℂ(u)`. -/
theorem branchPoint_no_rat_ade_of_exp_companion
    {S : PowerSeries ℂ} {α : ℝ} {ω : ℕ → ℝ} {c : ℕ → ℂ}
    (h : BranchPointStokesData S α ω c)
    {M I T : ℝ → ℂ}
    (hMIT : ∀ᶠ u : ℝ in atTop, M u = I u + T u)
    (hI_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j I) u)
    (hT_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j T) u)
    (hI : ∀ j : ℕ, HasAsympExp (iteratedDeriv j I) (d_u^[j] S))
    (hT : ∀ j : ℕ, ∃ δ > 0, ∃ A : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j T u‖ ≤ C * u ^ A * Real.exp (-δ * u))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val M u) (evalRatU P (u : ℂ)) = 0) :
    P = 0 := by
  have hM_deriv : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j M u = iteratedDeriv j (fun t => I t + T t) u := by
    intro j
    induction j with
    | zero => exact hMIT
    | succ j ih =>
      filter_upwards [eventually_nhds_of_eventually_atTop ih] with u hu
      rw [iteratedDeriv_succ, iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hu]
  have hM_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j M) (d_u^[j] S) := by
    intro j M_ord
    obtain ⟨C, hC⟩ := HasAsympExp.add_exp_companion hI_diff hT_diff hI hT j M_ord
    refine ⟨C, ?_⟩
    filter_upwards [hC, hM_deriv j] with u hu hdu
    rwa [hdu]
  exact branchPoint_stokes_vandermonde_no_rat_ade_of_asymp h hM_asymp P hP

/-- Half-integer (`α = 1/2`) specialization for Ramanujan's mock theta functions `f(q), ω(q)`,
Zagier's Hurwitz series `H(q)`, Rogers's false theta `Ψ(q)`, and all half-integer-weight
harmonic Maass forms. -/
theorem half_integer_no_rat_ade_of_exp_companion
    {S : PowerSeries ℂ} {ω : ℕ → ℝ} {c : ℕ → ℂ}
    (h : BranchPointStokesData S (1 / 2 : ℝ) ω c)
    {M I T : ℝ → ℂ}
    (hMIT : ∀ᶠ u : ℝ in atTop, M u = I u + T u)
    (hI_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j I) u)
    (hT_diff : ∀ j : ℕ, ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j T) u)
    (hI : ∀ j : ℕ, HasAsympExp (iteratedDeriv j I) (d_u^[j] S))
    (hT : ∀ j : ℕ, ∃ δ > 0, ∃ A : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j T u‖ ≤ C * u ^ A * Real.exp (-δ * u))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val M u) (evalRatU P (u : ℂ)) = 0) :
    P = 0 :=
  branchPoint_no_rat_ade_of_exp_companion h hMIT hI_diff hT_diff hI hT P hP

/-! ### 5. Exact Closed-Form Abel Integral Identity (`1/(2√(ω(ξ+ω)))`) -/

/-- **Exact Closed-Form Abel Integral Identity**:
For every `ω > 0` and real `ξ` with `ξ + ω > 0`,
`(1 / π) ∫_0^{π/2} (ξ sin²θ + ω)⁻¹ dθ = (2 √(ω (ξ + ω)))⁻¹`.
This is the exact mechanism converting every simple pole `r_m / (z + ω_m)` of a meromorphic
Mordell/Eichler kernel into an exact inverse square-root branch point
`r_m / (2 √(ω_m (ξ + ω_m)))` in the Borel plane. -/
theorem abel_inv_linear_eq_inv_sqrt {ω ξ : ℝ} (hω : 0 < ω) (hξω : 0 < ξ + ω) :
    (1 / Real.pi) * (∫ θ in (0 : ℝ)..(Real.pi / 2), (ξ * Real.sin θ ^ 2 + ω)⁻¹) =
      (2 * Real.sqrt (ω * (ξ + ω)))⁻¹ := by
  let a : ℝ := Real.sqrt ((ξ + ω) / ω)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (div_pos hξω hω)
  have ha_sq : a ^ 2 = (ξ + ω) / ω := Real.sq_sqrt (div_pos hξω hω).le
  have hden_pos : ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2), 0 < ξ * Real.sin θ ^ 2 + ω := by
    intro θ _
    have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
    have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hrew : ξ * Real.sin θ ^ 2 + ω = (ξ + ω) * Real.sin θ ^ 2 + ω * (1 - Real.sin θ ^ 2) := by
      ring
    rw [hrew]
    by_cases h1 : Real.sin θ ^ 2 = 0
    · rw [h1]; linarith
    · have hpos1 : 0 < (ξ + ω) * Real.sin θ ^ 2 :=
        mul_pos hξω (lt_of_le_of_ne hs0 (Ne.symm h1))
      have hnn2 : 0 ≤ ω * (1 - Real.sin θ ^ 2) := mul_nonneg hω.le (by linarith)
      linarith
  -- Define continuous antiderivative F on [0, π/2] with F(π/2) = π/2
  let F : ℝ → ℝ := fun θ =>
    if θ < Real.pi / 2 then Real.arctan (a * Real.tan θ) else Real.pi / 2
  have hderiv_on : ∀ θ ∈ Ico (0 : ℝ) (Real.pi / 2),
      HasDerivAt F (Real.sqrt (ω * (ξ + ω)) * (ξ * Real.sin θ ^ 2 + ω)⁻¹) θ := by
    intro θ hθ
    have hcos_pos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hcos_ne : Real.cos θ ≠ 0 := hcos_pos.ne'
    have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos_ne
    have hmul : HasDerivAt (fun t => a * Real.tan t) (a * (1 / Real.cos θ ^ 2)) θ :=
      htan.const_mul a
    have harctan : HasDerivAt (fun t => Real.arctan (a * Real.tan t))
        ((1 + (a * Real.tan θ) ^ 2)⁻¹ * (a * (1 / Real.cos θ ^ 2))) θ := by
      simpa [div_eq_inv_mul] using hmul.arctan
    have hev : F =ᶠ[𝓝 θ] fun t => Real.arctan (a * Real.tan t) := by
      filter_upwards [eventually_lt_nhds hθ.2] with t ht
      simp [F, ht]
    have hF := harctan.congr_of_eventuallyEq hev
    convert hF using 1
    have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have htan_eq : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
    have hdenom_alg : (1 + (a * Real.tan θ) ^ 2) * Real.cos θ ^ 2 =
        (ξ * Real.sin θ ^ 2 + ω) / ω := by
      rw [mul_pow, ha_sq, htan_eq, div_pow]
      field_simp [hω.ne', hcos_ne]
      nlinarith [hsc]
    have hsqrt_rel : a / ω = Real.sqrt (ω * (ξ + ω)) / (ω ^ 2) := by
      rw [show a = Real.sqrt ((ξ + ω) / ω) from rfl, Real.sqrt_div hξω.le,
        Real.sqrt_mul hω.le]
      have hsq : Real.sqrt ω * Real.sqrt ω = ω := Real.mul_self_sqrt hω.le
      have hsω : Real.sqrt ω ≠ 0 := (Real.sqrt_pos.mpr hω).ne'
      field_simp [hω.ne', hsω]
      nlinarith [hsq]
    have hden_ne : ξ * Real.sin θ ^ 2 + ω ≠ 0 :=
      (hden_pos θ ⟨hθ.1, hθ.2.le⟩).ne'
    have h1_ne : 1 + (a * Real.tan θ) ^ 2 ≠ 0 := by positivity
    have hmul_inv : (1 + (a * Real.tan θ) ^ 2)⁻¹ * (a * (1 / Real.cos θ ^ 2)) =
        a / ((1 + (a * Real.tan θ) ^ 2) * Real.cos θ ^ 2) := by
      field_simp [h1_ne, hcos_ne]
    rw [hmul_inv, hdenom_alg]
    have ha_mul : a * ω = Real.sqrt (ω * (ξ + ω)) := by
      rw [show a = Real.sqrt ((ξ + ω) / ω) from rfl, Real.sqrt_div hξω.le,
        Real.sqrt_mul hω.le]
      have hsq : Real.sqrt ω * Real.sqrt ω = ω := Real.mul_self_sqrt hω.le
      have hsω : Real.sqrt ω ≠ 0 := (Real.sqrt_pos.mpr hω).ne'
      field_simp [hsω]
      nlinarith [hsq]
    field_simp [hω.ne', hden_ne]
    linarith [ha_mul]
  -- Continuity of F at π/2 from the left via tan θ → +∞ ⇒ arctan(a tan θ) → π/2
  have hF_lim_right : Tendsto F (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) := by
    have htan_top : Tendsto Real.tan (𝓝[<] (Real.pi / 2)) atTop := by
      have hsin : Tendsto Real.sin (𝓝[<] (Real.pi / 2)) (𝓝 1) := by
        have h := (Real.continuous_sin.continuousAt (x := Real.pi / 2)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Iio (Real.pi / 2)))
        rwa [Real.sin_pi_div_two] at h
      have hcos0 : Tendsto Real.cos (𝓝[<] (Real.pi / 2)) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have h := (Real.continuous_cos.continuousAt (x := Real.pi / 2)).tendsto.mono_left
            (nhdsWithin_le_nhds (s := Iio (Real.pi / 2)))
          rwa [Real.cos_pi_div_two] at h
        · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : -(Real.pi / 2) < Real.pi / 2)]
            with θ hθ
          exact Real.cos_pos_of_mem_Ioo hθ
      have hdiv : Tendsto (fun θ => Real.sin θ * (Real.cos θ)⁻¹) (𝓝[<] (Real.pi / 2)) atTop :=
        Tendsto.pos_mul_atTop zero_lt_one hsin (tendsto_inv_nhdsGT_zero.comp hcos0)
      refine hdiv.congr fun θ => ?_
      rw [Real.tan_eq_sin_div_cos, div_eq_mul_inv]
    have hatan : Tendsto (fun θ => Real.arctan (a * Real.tan θ)) (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
        (htan_top.const_mul_atTop ha_pos)
    refine hatan.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    simp [F, Set.mem_Iio.mp hθ]
  have hF_cont : ContinuousOn F (Icc 0 (Real.pi / 2)) := by
    intro θ hθ
    by_cases hlt : θ < Real.pi / 2
    · exact (hderiv_on θ ⟨hθ.1, hlt⟩).continuousAt.continuousWithinAt
    · have heq : θ = Real.pi / 2 := le_antisymm hθ.2 (not_lt.mp hlt)
      subst heq
      rw [ContinuousWithinAt, show F (Real.pi / 2) = Real.pi / 2 by simp [F],
        Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      rw [Metric.tendsto_nhdsWithin_nhds] at hF_lim_right
      obtain ⟨δ, hδ, hδ_spec⟩ := hF_lim_right ε hε
      refine ⟨δ, hδ, fun x hx hdist => ?_⟩
      by_cases hxlt : x < Real.pi / 2
      · exact hδ_spec hxlt hdist
      · have hxeq : x = Real.pi / 2 := le_antisymm hx.2 (not_lt.mp hxlt)
        subst hxeq
        simpa [F] using hε
  have hint : ContinuousOn (fun θ => Real.sqrt (ω * (ξ + ω)) * (ξ * Real.sin θ ^ 2 + ω)⁻¹)
      (Icc 0 (Real.pi / 2)) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ (fun θ hθ => (hden_pos θ hθ).ne')
    exact (continuousOn_const.mul (Real.continuous_sin.continuousOn.pow 2)).add continuousOn_const
  -- FTC on [0, π/2]
  have hftc : ∫ θ in (0 : ℝ)..(Real.pi / 2),
      Real.sqrt (ω * (ξ + ω)) * (ξ * Real.sin θ ^ 2 + ω)⁻¹ = F (Real.pi / 2) - F 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by positivity) hF_cont ?_
      (hint.intervalIntegrable_of_Icc (by positivity))
    intro θ hθ
    exact hderiv_on θ ⟨hθ.1.le, hθ.2⟩
  have hF0 : F 0 = 0 := by simp [F, Real.pi_pos]
  have hFpi : F (Real.pi / 2) = Real.pi / 2 := by simp [F]
  rw [intervalIntegral.integral_const_mul, hFpi, hF0, sub_zero] at hftc
  have hsq_pos : 0 < Real.sqrt (ω * (ξ + ω)) := Real.sqrt_pos.mpr (mul_pos hω hξω)
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hint_eq : ∫ θ in (0 : ℝ)..(Real.pi / 2), (ξ * Real.sin θ ^ 2 + ω)⁻¹ =
      (Real.pi / 2) / Real.sqrt (ω * (ξ + ω)) :=
    (eq_div_iff hsq_pos.ne').mpr (by linarith [hftc])
  rw [hint_eq]
  field_simp [hpi_ne, hsq_pos.ne']

end

end PakPrimes.BranchPointStokes
