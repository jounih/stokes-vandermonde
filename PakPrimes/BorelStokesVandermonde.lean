module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Borel–Stokes–Vandermonde Annihilator Descent

This module formalizes the unconditional Borel–Stokes–Vandermonde transcendence engine:
1. Constant-coefficient differential operators `D_m` on `MvPolynomial (Fin (r + 1)) ℂ`,
   strict total-degree drop `degree_D_m_lt`, shift invariance when `D_freq ω P = 0`,
   and the strong-induction + Vandermonde contradiction (`stokes_vandermonde_eq_zero` and
   `stokes_vandermonde_general_eq_zero`).
2. Lateral Laplace transforms `gPlus`, `gMinus` of `Γ(1 - ξ)` along `arg ξ = ±π/4`,
   super-exponential decay, Watson asymptotics to all orders, Borel–Laplace transfer
   from `P(gHat) = 0` to `P(gPlus) = P(gMinus) = 0`, and the exact Stokes jump via
   Cauchy's residue theorem.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.BorelStokesVandermonde

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open scoped Topology

noncomputable section

/-! ### 1. Constant-Coefficient Derivations & Vandermonde Descent -/

/-- General frequency constant-coefficient derivation `D_ω P = ∑ j, (-ω)^j • ∂_j P`. -/
@[expose] def D_freq (r : ℕ) (ω : ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin (r + 1)) ℂ where
  toFun P := ∑ j : Fin (r + 1), (-ω) ^ (j : ℕ) • MvPolynomial.pderiv j P
  map_add' P Q := by
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, smul_comm]

/-- Integer-frequency constant-coefficient derivation `D_m P = ∑ j, (-m)^j • ∂_j P`. -/
@[expose] def D_m {r : ℕ} (m : ℕ) :
    MvPolynomial (Fin (r + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin (r + 1)) ℂ :=
  D_freq r (m : ℂ)

theorem D_m_apply {r : ℕ} (m : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    D_m m P = ∑ j : Fin (r + 1), (-(m : ℂ)) ^ (j : ℕ) • MvPolynomial.pderiv j P :=
  rfl

lemma degree_pderiv_lt {ι : Type*} (i : ι) (P : MvPolynomial ι ℂ)
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

theorem degree_D_freq_lt {r : ℕ} (ω : ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (h : 0 < P.totalDegree) : (D_freq r ω P).totalDegree < P.totalDegree := by
  unfold D_freq
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine totalDegree_sum_lt Finset.univ _ h fun j _ => ?_
  refine (MvPolynomial.totalDegree_smul_le _ _).trans_lt ?_
  exact degree_pderiv_lt j P h

/-- Strict total-degree decrease under `D_m` for every non-constant polynomial `P`. -/
theorem degree_D_m_lt {r : ℕ} (m : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (h : 0 < P.totalDegree) : (D_m m P).totalDegree < P.totalDegree :=
  degree_D_freq_lt (m : ℂ) P h

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
    have hp : (MvPolynomial.pderiv i P).coeff (m - Finsupp.single i (1 : ℕ)) = 0 := by
      rw [h i]; simp
    rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hi] at hp
    have hmul : (((m - Finsupp.single i (1 : ℕ)) i : ℂ) + 1) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero ((m - Finsupp.single i (1 : ℕ)) i)
    have hcm : P.coeff m = 0 := (mul_eq_zero.mp hp).resolve_right hmul
    simp [hcm, MvPolynomial.coeff_C, Ne.symm hm]

private noncomputable def lineSlice {r : ℕ} (x v : Fin (r + 1) → ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun j => Polynomial.C (x j) + Polynomial.C (v j) * Polynomial.X

private lemma lineSlice_eval {r : ℕ} (x v : Fin (r + 1) → ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) (a : ℂ) :
    (lineSlice x v P).eval a = MvPolynomial.eval (fun j => x j + a * v j) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSlice]
  | add A B hA hB =>
    simp only [map_add, Polynomial.eval_add] at hA hB ⊢
    rw [hA, hB]
  | mul_X A j hA =>
    simp only [lineSlice, map_mul, MvPolynomial.aeval_X] at hA ⊢
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      hA, mul_comm a (v j)]

private lemma derivative_lineSlice {r : ℕ} (x v : Fin (r + 1) → ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) :
    Polynomial.derivative (lineSlice x v P) =
      ∑ j : Fin (r + 1), Polynomial.C (v j) * lineSlice x v (MvPolynomial.pderiv j P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSlice]
  | add A B hA hB =>
    simp only [map_add, hA, hB, mul_add, Finset.sum_add_distrib]
  | mul_X A k hA =>
    simp only [map_mul, Polynomial.derivative_mul, hA]
    have hk : Polynomial.derivative (lineSlice x v (MvPolynomial.X k)) = Polynomial.C (v k) := by
      simp [lineSlice]
    rw [hk]
    simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X, Pi.single_apply,
      mul_add, Finset.sum_add_distrib]
    have hsum1 : ∑ j : Fin (r + 1), Polynomial.C (v j) *
        lineSlice x v (MvPolynomial.pderiv j A * MvPolynomial.X k) =
        (∑ j : Fin (r + 1), Polynomial.C (v j) * lineSlice x v (MvPolynomial.pderiv j A)) *
          lineSlice x v (MvPolynomial.X k) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]; ring
    have hsum2 : ∑ j : Fin (r + 1), Polynomial.C (v j) *
        lineSlice x v (A * if k = j then 1 else 0) =
        lineSlice x v A * Polynomial.C (v k) := by
      trans ∑ j : Fin (r + 1), if k = j then Polynomial.C (v k) * lineSlice x v A else 0
      · refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hkj
        · subst hkj; simp
        · simp
      · simp [mul_comm]
    rw [hsum1, hsum2]

/-- If `D_freq ω P = 0`, then `P` is invariant under shifting in the `(-ω)^j` direction. -/
theorem shift_invariant_of_D_freq_eq_zero {r : ℕ} (ω : ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) (hP : D_freq r ω P = 0)
    (x : Fin (r + 1) → ℂ) (a : ℂ) :
    MvPolynomial.eval (fun j => x j + a * (-ω) ^ (j : ℕ)) P = MvPolynomial.eval x P := by
  let v : Fin (r + 1) → ℂ := fun j => (-ω) ^ (j : ℕ)
  have hd : Polynomial.derivative (lineSlice x v P) = 0 := by
    rw [derivative_lineSlice]
    have h0 : lineSlice x v (D_freq r ω P) = 0 := by rw [hP, map_zero]
    rw [D_freq] at h0
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at h0
    simp only [map_sum, Algebra.smul_def] at h0
    simpa [v] using h0
  have hc := Polynomial.eq_C_of_derivative_eq_zero hd
  have he : (lineSlice x v P).eval a = (lineSlice x v P).eval 0 := by
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  rw [lineSlice_eval, lineSlice_eval] at he
  simpa [v] using he

/-- Second-order Taylor bound for evaluating `P` at `x + a • v` when `x, v` are bounded and `‖a‖ ≤ 1`. -/
lemma eval_shift_taylor_bound {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x v : Fin (r + 1) → ℂ) (a : ℂ),
      (∀ j, ‖x j‖ ≤ M) → (∀ j, ‖v j‖ ≤ M) → ‖a‖ ≤ 1 →
      ‖MvPolynomial.eval (fun j => x j + a * v j) P - MvPolynomial.eval x P -
        a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j P) * v j‖ ≤
        C * ‖a‖ ^ 2 := by
  have eval_bdd : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Fin (r + 1) → ℂ, (∀ j, ‖y j‖ ≤ M) → ‖MvPolynomial.eval y Q‖ ≤ B := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => exact ⟨‖c‖, norm_nonneg _, fun _ _ => by simp⟩
    | add A B hA hB =>
      obtain ⟨BA, hBA, hbA⟩ := hA
      obtain ⟨BB, hBB, hbB⟩ := hB
      refine ⟨BA + BB, add_nonneg hBA hBB, fun y hy => ?_⟩
      simpa only [map_add] using (norm_add_le _ _).trans (add_le_add (hbA y hy) (hbB y hy))
    | mul_X A k hA =>
      obtain ⟨BA, hBA, hbA⟩ := hA
      refine ⟨BA * M, mul_nonneg hBA hM, fun y hy => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, norm_mul]
      exact mul_le_mul (hbA y hy) (hy k) (norm_nonneg _) hBA
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, le_rfl, fun x v a _ _ _ => ?_⟩
    simp
  | add A B hA hB =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨CB, hCB, hbB⟩ := hB
    refine ⟨CA + CB, add_nonneg hCA hCB, fun x v a hx hv ha => ?_⟩
    have hsplit : MvPolynomial.eval (fun j => x j + a * v j) (A + B) - MvPolynomial.eval x (A + B) -
        a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (A + B)) * v j =
        (MvPolynomial.eval (fun j => x j + a * v j) A - MvPolynomial.eval x A -
          a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j) +
        (MvPolynomial.eval (fun j => x j + a * v j) B - MvPolynomial.eval x B -
          a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j B) * v j) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [hsplit, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hbA x v a hx hv ha) (hbB x v a hx hv ha))
  | mul_X A k hA =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨BA, hBA, hAbdd⟩ := eval_bdd A
    have hderivBdd : ∃ BD : ℝ, 0 ≤ BD ∧ ∀ x v : Fin (r + 1) → ℂ,
        (∀ j, ‖x j‖ ≤ M) → (∀ j, ‖v j‖ ≤ M) →
        ‖∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j‖ ≤ BD := by
      choose B hB hBbdd using fun j => eval_bdd (MvPolynomial.pderiv j A)
      refine ⟨∑ j : Fin (r + 1), B j * M, Finset.sum_nonneg fun j _ => mul_nonneg (hB j) hM,
        fun x v hx hv => ?_⟩
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hBbdd j x hx) (hv j) (norm_nonneg _) (hB j)
    obtain ⟨BD, hBD, hDbdd⟩ := hderivBdd
    refine ⟨CA * (2 * M) + BD * M, by positivity, fun x v a hx hv ha => ?_⟩
    let S := ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j
    let RA := MvPolynomial.eval (fun j => x j + a * v j) A - MvPolynomial.eval x A - a * S
    have hsum : ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (A * MvPolynomial.X k)) * v j =
        S * x k + MvPolynomial.eval x A * v k := by
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply, map_add, map_mul,
        MvPolynomial.eval_X, add_mul, Finset.sum_add_distrib]
      have h1 : ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j A) * x k * v j = S * x k := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      have h2 : ∑ j : Fin (r + 1), MvPolynomial.eval x A *
          MvPolynomial.eval x (if k = j then 1 else 0) * v j =
          MvPolynomial.eval x A * v k := by
        trans ∑ j : Fin (r + 1), if k = j then MvPolynomial.eval x A * v k else 0
        · refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hkj
          · subst hkj; simp
          · simp
        · simp
      rw [h1, h2]
    have hid : MvPolynomial.eval (fun j => x j + a * v j) (A * MvPolynomial.X k) -
        MvPolynomial.eval x (A * MvPolynomial.X k) - a * (S * x k + MvPolynomial.eval x A * v k) =
        RA * (x k + a * v k) + a ^ 2 * (S * v k) := by
      simp only [map_mul, MvPolynomial.eval_X, RA]
      ring
    rw [hsum, hid]
    have hxk : ‖x k + a * v k‖ ≤ 2 * M := by
      calc ‖x k + a * v k‖ ≤ ‖x k‖ + ‖a‖ * ‖v k‖ := (norm_add_le _ _).trans (by rw [norm_mul])
        _ ≤ M + 1 * M := add_le_add (hx k) (mul_le_mul ha (hv k) (norm_nonneg _) zero_le_one)
        _ = 2 * M := by ring
    have hRA := hbA x v a hx hv ha
    have hSv : ‖S * v k‖ ≤ BD * M := by
      rw [norm_mul]
      exact mul_le_mul (hDbdd x v hx hv) (hv k) (norm_nonneg _) hBD
    calc ‖RA * (x k + a * v k) + a ^ 2 * (S * v k)‖
        ≤ ‖RA‖ * ‖x k + a * v k‖ + ‖a ^ 2‖ * ‖S * v k‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ (CA * ‖a‖ ^ 2) * (2 * M) + ‖a‖ ^ 2 * (BD * M) := by
          rw [norm_pow]
          exact add_le_add
            (mul_le_mul hRA hxk (norm_nonneg _) (mul_nonneg hCA (sq_nonneg _)))
            (mul_le_mul_of_nonneg_left hSv (sq_nonneg _))
      _ = (CA * (2 * M) + BD * M) * ‖a‖ ^ 2 := by ring

/-- Lipschitz bound for polynomial evaluation on bounded boxes. -/
lemma eval_lipschitz_of_bounded {ι : Type*} (P : MvPolynomial ι ℂ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ι → ℂ) (ε : ℝ), 0 ≤ ε →
      (∀ j, ‖x j‖ ≤ M) → (∀ j, ‖y j‖ ≤ M) → (∀ j, ‖x j - y j‖ ≤ ε) →
      ‖MvPolynomial.eval x P - MvPolynomial.eval y P‖ ≤ C * ε := by
  have eval_bdd : ∀ Q : MvPolynomial ι ℂ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ι → ℂ, (∀ j, ‖y j‖ ≤ M) → ‖MvPolynomial.eval y Q‖ ≤ B := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => exact ⟨‖c‖, norm_nonneg _, fun _ _ => by simp⟩
    | add A B hA hB =>
      obtain ⟨BA, hBA, hbA⟩ := hA
      obtain ⟨BB, hBB, hbB⟩ := hB
      refine ⟨BA + BB, add_nonneg hBA hBB, fun y hy => ?_⟩
      simpa only [map_add] using (norm_add_le _ _).trans (add_le_add (hbA y hy) (hbB y hy))
    | mul_X A k hA =>
      obtain ⟨BA, hBA, hbA⟩ := hA
      refine ⟨BA * M, mul_nonneg hBA hM, fun y hy => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, norm_mul]
      exact mul_le_mul (hbA y hy) (hy k) (norm_nonneg _) hBA
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, le_rfl, fun _ _ ε _ _ _ _ => ?_⟩
    simp
  | add A B hA hB =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨CB, hCB, hbB⟩ := hB
    refine ⟨CA + CB, add_nonneg hCA hCB, fun x y ε hε hx hy hxy => ?_⟩
    simp only [map_add]
    have hsplit : (MvPolynomial.eval x A + MvPolynomial.eval x B) -
        (MvPolynomial.eval y A + MvPolynomial.eval y B) =
        (MvPolynomial.eval x A - MvPolynomial.eval y A) +
        (MvPolynomial.eval x B - MvPolynomial.eval y B) := by ring
    rw [hsplit, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hbA x y ε hε hx hy hxy) (hbB x y ε hε hx hy hxy))
  | mul_X A k hA =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨BA, hBA, hAbdd⟩ := eval_bdd A
    refine ⟨CA * M + BA, by positivity, fun x y ε hε hx hy hxy => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X]
    have hsplit : MvPolynomial.eval x A * x k - MvPolynomial.eval y A * y k =
        (MvPolynomial.eval x A - MvPolynomial.eval y A) * x k +
        MvPolynomial.eval y A * (x k - y k) := by ring
    rw [hsplit]
    calc ‖(MvPolynomial.eval x A - MvPolynomial.eval y A) * x k + MvPolynomial.eval y A * (x k - y k)‖
        ≤ ‖MvPolynomial.eval x A - MvPolynomial.eval y A‖ * ‖x k‖ +
          ‖MvPolynomial.eval y A‖ * ‖x k - y k‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ (CA * ε) * M + BA * ε :=
          add_le_add
            (mul_le_mul (hbA x y ε hε hx hy hxy) (hx k) (norm_nonneg _) (mul_nonneg hCA hε))
            (mul_le_mul (hAbdd y hy) (hxy k) (norm_nonneg _) hBA)
      _ = (CA * M + BA) * ε := by ring

/-- Iterated derivative of a difference equals the difference of iterated derivatives
when both functions are smooth along the tail. -/
lemma eventually_iteratedDeriv_sub {f g : ℝ → ℂ} {k : ℕ}
    (hf : ∀ i < k, ∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv i f) u)
    (hg : ∀ i < k, ∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv i g) u) :
    ∀ᶠ u in atTop, iteratedDeriv k (fun t => f t - g t) u =
      iteratedDeriv k f u - iteratedDeriv k g u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hih := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
      (fun i hi => hg i (Nat.lt_succ_of_lt hi))
    have hloc : ∀ᶠ u in atTop,
        iteratedDeriv k (fun t => f t - g t) =ᶠ[𝓝 u] fun t => iteratedDeriv k f t - iteratedDeriv k g t := by
      obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hih
      filter_upwards [Filter.eventually_gt_atTop L] with u hu
      exact (lt_mem_nhds hu).mono fun v hv => hL v hv.le
    filter_upwards [hloc, hf k (Nat.lt_succ_self k), hg k (Nat.lt_succ_self k)] with u hu hfu hgu
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, hu.deriv_eq]
    exact (hfu.hasDerivAt.sub hgu.hasDerivAt).deriv

/-- Strong Induction + Vandermonde Contradiction for arbitrary strictly increasing positive frequencies. -/
theorem stokes_vandermonde_general_eq_zero {r : ℕ}
    (IsFormalZero : MvPolynomial (Fin (r + 1)) ℂ → Prop)
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP_min : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 → Q.totalDegree < P.totalDegree → ¬ IsFormalZero Q)
    (hP_const : MvPolynomial.eval 0 P = 0)
    (ω : ℕ → ℝ) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hω_low : ∀ m, δ₀ ≤ ω m) (hω_mono : StrictMono ω)
    (c : ℕ → ℂ) (hc_ne : ∀ m, m < r + 1 → c m ≠ 0)
    (g_pos g_neg : ℝ → ℂ)
    (h_diff : ∀ k < r, (∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv k g_pos) u) ∧
      (∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv k g_neg) u))
    (hP_pos : ∀ᶠ u in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u) P = 0)
    (hP_neg : ∀ᶠ u in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_neg u) P = 0)
    (hg_bdd : ∀ j : Fin (r + 1), ∃ C : ℝ, ∀ᶠ u in atTop, ‖iteratedDeriv j.val g_pos u‖ ≤ C)
    (h_exp : ∀ (n : ℕ) (j : Fin (r + 1)), n < r + 1 →
      ∃ C : ℝ, ∀ᶠ u in atTop,
        ‖iteratedDeriv j.val (fun t => g_neg t - g_pos t) u -
          ∑ m ∈ Finset.range (n + 1), c m * (-(ω m : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
          C * Real.exp (-(ω n + δ₀) * u))
    (h_bridge : ∀ (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∃ C : ℝ, ∀ᶠ u in atTop,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u) Q‖ ≤
          C * Real.exp (-δ₀ * u)) →
      IsFormalZero Q) :
    P = 0 := by
  have hω_pos : ∀ m, 0 < ω m := fun m => lt_of_lt_of_le hδ₀ (hω_low m)
  by_contra hP_ne
  have hP_pos_deg : 0 < P.totalDegree := by
    by_contra! hle
    have h0 : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev : P.coeff 0 = 0 := by
      have hh := hP_const
      rw [hC, MvPolynomial.eval_C] at hh
      exact hh
    exact hP_ne (hC.trans (by rw [hev, map_zero]))
  have h_sub_deriv : ∀ j : Fin (r + 1), ∀ᶠ u in atTop,
      iteratedDeriv j.val (fun t => g_neg t - g_pos t) u =
        iteratedDeriv j.val g_neg u - iteratedDeriv j.val g_pos u := by
    intro j
    exact eventually_iteratedDeriv_sub
      (fun i hi => (h_diff i (lt_of_lt_of_le hi (Nat.lt_succ_iff.mp j.isLt))).2)
      (fun i hi => (h_diff i (lt_of_lt_of_le hi (Nat.lt_succ_iff.mp j.isLt))).1)
  have hD_zero : ∀ n : ℕ, n < r + 1 → D_freq r (ω n) P = 0 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      have h_prev : ∀ m < n, D_freq r (ω m) P = 0 := fun m hm =>
        ih m hm (lt_trans hm hn)
      have h_shift_sum : ∀ k ≤ n, ∀ (x : Fin (r + 1) → ℂ) (a : ℕ → ℂ),
          MvPolynomial.eval (fun j => x j + ∑ m ∈ Finset.range k, a m * (-(ω m : ℂ)) ^ (j : ℕ)) P =
            MvPolynomial.eval x P := by
        intro k hk x a
        induction k with
        | zero => simp
        | succ k ihk =>
          have hkk : k < n := Nat.lt_of_succ_le hk
          have h1 : (fun j : Fin (r + 1) =>
              x j + ∑ m ∈ Finset.range (k + 1), a m * (-(ω m : ℂ)) ^ (j : ℕ)) =
              (fun j : Fin (r + 1) =>
                (x j + ∑ m ∈ Finset.range k, a m * (-(ω m : ℂ)) ^ (j : ℕ)) +
                  a k * (-(ω k : ℂ)) ^ (j : ℕ)) := by
            funext j; rw [Finset.sum_range_succ, add_assoc]
          rw [h1, shift_invariant_of_D_freq_eq_zero (ω k) P (h_prev k hkk),
            ihk (Nat.le_of_lt hkk)]
      choose Bg hBg using hg_bdd
      have h_all_bg : ∀ᶠ u in atTop, ∀ j : Fin (r + 1), ‖iteratedDeriv j.val g_pos u‖ ≤ Bg j :=
        Filter.eventually_all.mpr hBg
      let M₀ : ℝ := 1 + (∑ j : Fin (r + 1), |Bg j|) +
        (∑ j : Fin (r + 1), ∑ m ∈ Finset.range (n + 1), (1 + ‖c m‖) * (ω m) ^ (j : ℕ))
      let M : ℝ := 2 * M₀ + 1
      have hM₀_nonneg : 0 ≤ M₀ := by
        have h1 : 0 ≤ ∑ j : Fin (r + 1), |Bg j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have h2 : 0 ≤ ∑ j : Fin (r + 1), ∑ m ∈ Finset.range (n + 1),
            (1 + ‖c m‖) * (ω m) ^ (j : ℕ) :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun m _ =>
            mul_nonneg (add_nonneg zero_le_one (norm_nonneg _)) (pow_nonneg (hω_pos m).le _)
        dsimp only [M₀]
        linarith
      have hM_nonneg : 0 ≤ M := by positivity
      have hBg_le : ∀ j : Fin (r + 1), |Bg j| ≤ M₀ := fun j => by
        have hsum : |Bg j| ≤ ∑ i : Fin (r + 1), |Bg i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (Bg i)) (Finset.mem_univ j)
        have h3 : 0 ≤ ∑ j' : Fin (r + 1), ∑ m ∈ Finset.range (n + 1),
            (1 + ‖c m‖) * (ω m) ^ (j' : ℕ) :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun m _ =>
            mul_nonneg (add_nonneg zero_le_one (norm_nonneg _)) (pow_nonneg (hω_pos m).le _)
        dsimp only [M₀]
        linarith
      have hv_le : ∀ (m : ℕ) (hm : m ∈ Finset.range (n + 1)) (j : Fin (r + 1)),
          ‖(-(ω m : ℂ)) ^ (j : ℕ)‖ ≤ M := by
        intro m hm j
        have hnorm : ‖(-(ω m : ℂ)) ^ (j : ℕ)‖ = (ω m) ^ (j : ℕ) := by
          rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hω_pos m)]
        have h1 : (ω m) ^ (j : ℕ) ≤ (1 + ‖c m‖) * (ω m) ^ (j : ℕ) :=
          le_mul_of_one_le_left (pow_nonneg (hω_pos m).le _) (by linarith [norm_nonneg (c m)])
        have h2 : (1 + ‖c m‖) * (ω m) ^ (j : ℕ) ≤
            ∑ m' ∈ Finset.range (n + 1), (1 + ‖c m'‖) * (ω m') ^ (j : ℕ) :=
          Finset.single_le_sum (fun m' _ =>
            mul_nonneg (add_nonneg zero_le_one (norm_nonneg _)) (pow_nonneg (hω_pos m').le _)) hm
        have h3 : ∑ m' ∈ Finset.range (n + 1), (1 + ‖c m'‖) * (ω m') ^ (j : ℕ) ≤
            ∑ j' : Fin (r + 1), ∑ m' ∈ Finset.range (n + 1), (1 + ‖c m'‖) * (ω m') ^ (j' : ℕ) :=
          Finset.single_le_sum
            (f := fun j' : Fin (r + 1) => ∑ m' ∈ Finset.range (n + 1), (1 + ‖c m'‖) * (ω m') ^ (j' : ℕ))
            (fun j' _ => Finset.sum_nonneg fun m' _ =>
              mul_nonneg (add_nonneg zero_le_one (norm_nonneg _)) (pow_nonneg (hω_pos m').le _))
            (Finset.mem_univ j)
        have h4 : 0 ≤ ∑ j' : Fin (r + 1), |Bg j'| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        rw [hnorm]
        dsimp only [M, M₀]
        linarith
      choose Cexp h_exp_ev using fun j : Fin (r + 1) => h_exp n j hn
      have h_all_exp : ∀ᶠ u in atTop, ∀ j : Fin (r + 1),
          ‖iteratedDeriv j.val (fun t => g_neg t - g_pos t) u -
            ∑ m ∈ Finset.range (n + 1), c m * (-(ω m : ℂ)) ^ (j : ℕ) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
            Cexp j * Real.exp (-(ω n + δ₀) * u) :=
        Filter.eventually_all.mpr h_exp_ev
      have h_all_sub : ∀ᶠ u in atTop, ∀ j : Fin (r + 1),
          iteratedDeriv j.val (fun t => g_neg t - g_pos t) u =
            iteratedDeriv j.val g_neg u - iteratedDeriv j.val g_pos u :=
        Filter.eventually_all.mpr h_sub_deriv
      let C_rem : ℝ := ∑ j : Fin (r + 1), max (Cexp j) 0
      have hC_rem_nonneg : 0 ≤ C_rem := Finset.sum_nonneg fun j _ => le_max_right _ _
      obtain ⟨C_lip, hC_lip, h_lip⟩ := eval_lipschitz_of_bounded P hM_nonneg
      obtain ⟨C_tay, hC_tay, h_tay⟩ := eval_shift_taylor_bound P hM_nonneg
      have h_exp_neg_small : ∀ᶠ u : ℝ in atTop,
          (∀ m ∈ Finset.range (n + 1), Real.exp (-ω m * u) ≤ 1) ∧
          ‖c n‖ * Real.exp (-ω n * u) ≤ 1 ∧
          C_rem * Real.exp (-(ω n + δ₀) * u) ≤ 1 := by
        have hm : ∀ m ∈ Finset.range (n + 1), ∀ᶠ u : ℝ in atTop, Real.exp (-ω m * u) ≤ 1 := by
          intro m _
          filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
          rw [Real.exp_le_one_iff]
          have hmul : 0 ≤ ω m * u := mul_nonneg (hω_pos m).le hu
          linarith
        have ha : ∀ᶠ u : ℝ in atTop, ‖c n‖ * Real.exp (-ω n * u) ≤ 1 := by
          have ht : Filter.Tendsto (fun u : ℝ => ‖c n‖ * Real.exp (-ω n * u)) atTop (𝓝 0) := by
            simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
              (Filter.tendsto_id.const_mul_atTop (hω_pos n))).const_mul ‖c n‖
          exact (ht.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le
        have hb : ∀ᶠ u : ℝ in atTop, C_rem * Real.exp (-(ω n + δ₀) * u) ≤ 1 := by
          have hpos : 0 < ω n + δ₀ := add_pos (hω_pos n) hδ₀
          have ht : Filter.Tendsto (fun u : ℝ => C_rem * Real.exp (-(ω n + δ₀) * u)) atTop (𝓝 0) := by
            simpa [neg_add, add_mul] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
              (Filter.tendsto_id.const_mul_atTop hpos)).const_mul C_rem
          exact (ht.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le
        exact ((Filter.eventually_all_finset _).mpr hm).and (ha.and hb)
      have hcn_ne : c n ≠ 0 := hc_ne n hn
      have hcn_pos : 0 < ‖c n‖ := norm_pos_iff.mpr hcn_ne
      let C_final : ℝ := (C_lip * C_rem + C_tay * ‖c n‖ ^ 2) / ‖c n‖
      have h_bridge_bound : ∀ᶠ u : ℝ in atTop,
          ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u)
            (D_freq r (ω n) P)‖ ≤ C_final * Real.exp (-δ₀ * u) := by
        filter_upwards [h_all_bg, h_all_exp, h_all_sub, hP_pos, hP_neg, h_exp_neg_small,
          Filter.eventually_ge_atTop (0 : ℝ)] with u hbg hexp hsub hpos hneg ⟨hexp1, ha1, hrem1⟩ hu0
        let x : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val g_pos u
        let S : Fin (r + 1) → ℂ := fun j =>
          ∑ m ∈ Finset.range (n + 1), c m * (-(ω m : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ))
        let y : Fin (r + 1) → ℂ := fun j => x j + S j
        let z : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val g_neg u
        have h_exp_norm (m : ℕ) : ‖Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ = Real.exp (-ω m * u) := by
          rw [Complex.norm_exp]
          congr 1
          simp [Complex.mul_re]
        have hx_le : ∀ j, ‖x j‖ ≤ M := fun j =>
          (hbg j).trans ((le_abs_self _).trans ((hBg_le j).trans (by dsimp only [M]; linarith)))
        have hS_le : ∀ j, ‖S j‖ ≤ M₀ := fun j => by
          calc ‖S j‖ ≤ ∑ m ∈ Finset.range (n + 1),
                ‖c m * (-(ω m : ℂ)) ^ (j : ℕ) * Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ :=
                  norm_sum_le _ _
            _ ≤ ∑ m ∈ Finset.range (n + 1), (1 + ‖c m‖) * (ω m) ^ (j : ℕ) := by
                refine Finset.sum_le_sum fun m hm => ?_
                rw [norm_mul, norm_mul, h_exp_norm, norm_pow, norm_neg, Complex.norm_real,
                  Real.norm_eq_abs, abs_of_pos (hω_pos m)]
                calc ‖c m‖ * (ω m) ^ (j : ℕ) * Real.exp (-ω m * u)
                    ≤ ‖c m‖ * (ω m) ^ (j : ℕ) * 1 :=
                      mul_le_mul_of_nonneg_left (hexp1 m hm) (mul_nonneg (norm_nonneg _) (pow_nonneg (hω_pos m).le _))
                  _ = ‖c m‖ * (ω m) ^ (j : ℕ) := mul_one _
                  _ ≤ (1 + ‖c m‖) * (ω m) ^ (j : ℕ) :=
                      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (hω_pos m).le _)
            _ ≤ M₀ := by
                have h3 : ∑ m ∈ Finset.range (n + 1), (1 + ‖c m‖) * (ω m) ^ (j : ℕ) ≤
                    ∑ j' : Fin (r + 1), ∑ m ∈ Finset.range (n + 1),
                      (1 + ‖c m‖) * (ω m) ^ (j' : ℕ) :=
                  Finset.single_le_sum
                    (f := fun j' : Fin (r + 1) => ∑ m ∈ Finset.range (n + 1),
                      (1 + ‖c m‖) * (ω m) ^ (j' : ℕ))
                    (fun j' _ => Finset.sum_nonneg fun m' _ =>
                      mul_nonneg (add_nonneg zero_le_one (norm_nonneg _)) (pow_nonneg (hω_pos m').le _))
                    (Finset.mem_univ j)
                have h4 : 0 ≤ ∑ j' : Fin (r + 1), |Bg j'| :=
                  Finset.sum_nonneg fun _ _ => abs_nonneg _
                dsimp only [M₀]
                linarith
        have hy_le : ∀ j, ‖y j‖ ≤ M := fun j => by
          calc ‖y j‖ ≤ ‖x j‖ + ‖S j‖ := norm_add_le _ _
            _ ≤ M₀ + M₀ := add_le_add ((hbg j).trans ((le_abs_self _).trans (hBg_le j))) (hS_le j)
            _ ≤ M := by dsimp only [M]; linarith
        have hzy_le : ∀ j, ‖z j - y j‖ ≤ C_rem * Real.exp (-(ω n + δ₀) * u) := fun j => by
          have hsub_eq : z j - y j =
              iteratedDeriv j.val (fun t => g_neg t - g_pos t) u - S j := by
            rw [hsub j]
            simp only [y, x, z]
            ring
          rw [hsub_eq]
          refine (hexp j).trans ?_
          calc Cexp j * Real.exp (-(ω n + δ₀) * u)
              ≤ max (Cexp j) 0 * Real.exp (-(ω n + δ₀) * u) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
            _ ≤ C_rem * Real.exp (-(ω n + δ₀) * u) := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
                exact Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j)
        have hz_le : ∀ j, ‖z j‖ ≤ M := fun j => by
          have hid : z j = y j + (z j - y j) := by ring
          rw [hid]
          calc ‖y j + (z j - y j)‖ ≤ ‖y j‖ + ‖z j - y j‖ := norm_add_le _ _
            _ ≤ (M₀ + M₀) + 1 := by
                refine add_le_add ?_ ((hzy_le j).trans hrem1)
                exact (norm_add_le _ _).trans (add_le_add ((hbg j).trans ((le_abs_self _).trans (hBg_le j))) (hS_le j))
            _ = M := by ring
        have h_lip_y : ‖MvPolynomial.eval y P‖ ≤ C_lip * (C_rem * Real.exp (-(ω n + δ₀) * u)) := by
          have h0 := h_lip z y (C_rem * Real.exp (-(ω n + δ₀) * u))
            (mul_nonneg hC_rem_nonneg (Real.exp_pos _).le) hz_le hy_le hzy_le
          rw [show MvPolynomial.eval z P = 0 from hneg, zero_sub, norm_neg] at h0
          exact h0
        let a : ℂ := c n * Complex.exp (-(ω n : ℂ) * (u : ℂ))
        let v : Fin (r + 1) → ℂ := fun j => (-(ω n : ℂ)) ^ (j : ℕ)
        have hy_eq : MvPolynomial.eval y P = MvPolynomial.eval (fun j => x j + a * v j) P := by
          have hy_split : y = fun j => (x j + a * v j) +
              ∑ m ∈ Finset.range n, (c m * Complex.exp (-(ω m : ℂ) * (u : ℂ))) * (-(ω m : ℂ)) ^ (j : ℕ) := by
            funext j
            simp only [y, S, Finset.sum_range_succ, a, v]
            have hcomm : ∀ m, c m * (-(ω m : ℂ)) ^ (j : ℕ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
                (c m * Complex.exp (-(ω m : ℂ) * (u : ℂ))) * (-(ω m : ℂ)) ^ (j : ℕ) :=
              fun m => by ring
            simp_rw [hcomm]
            ring
          rw [hy_split]
          exact h_shift_sum n le_rfl (fun j => x j + a * v j)
            (fun m => c m * Complex.exp (-(ω m : ℂ) * (u : ℂ)))
        have ha_norm : ‖a‖ = ‖c n‖ * Real.exp (-ω n * u) := by
          simp only [a, norm_mul, h_exp_norm]
        have ha_le1 : ‖a‖ ≤ 1 := by rw [ha_norm]; exact ha1
        have h_tay_y := h_tay x v a hx_le (fun j => hv_le n (Finset.mem_range.mpr (Nat.lt_succ_self n)) j) ha_le1
        have hx0 : MvPolynomial.eval x P = 0 := hpos
        have hD_eval : ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j P) * v j =
            MvPolynomial.eval x (D_freq r (ω n) P) := by
          simp only [D_freq, LinearMap.coe_mk, AddHom.coe_mk, map_sum, Algebra.smul_def,
            MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.eval_C, v, mul_comm]
        rw [← hy_eq, hx0, sub_zero, hD_eval] at h_tay_y
        have h_main : ‖a * MvPolynomial.eval x (D_freq r (ω n) P)‖ ≤
            C_lip * (C_rem * Real.exp (-(ω n + δ₀) * u)) + C_tay * ‖a‖ ^ 2 := by
          have htri : ‖a * MvPolynomial.eval x (D_freq r (ω n) P)‖ ≤
              ‖MvPolynomial.eval y P‖ + ‖MvPolynomial.eval y P - a * MvPolynomial.eval x (D_freq r (ω n) P)‖ := by
            simpa using norm_sub_le (MvPolynomial.eval y P)
              (MvPolynomial.eval y P - a * MvPolynomial.eval x (D_freq r (ω n) P))
          exact htri.trans (add_le_add h_lip_y h_tay_y)
        rw [norm_mul, ha_norm] at h_main
        have hpos_den : 0 < ‖c n‖ * Real.exp (-ω n * u) := mul_pos hcn_pos (Real.exp_pos _)
        have h1_exp : Real.exp (-(ω n + δ₀) * u) = Real.exp (-ω n * u) * Real.exp (-δ₀ * u) := by
          rw [← Real.exp_add]; congr 1; ring
        have h2_exp : (‖c n‖ * Real.exp (-ω n * u)) ^ 2 =
            (‖c n‖ * Real.exp (-ω n * u)) * (‖c n‖ * Real.exp (-ω n * u)) := by ring
        rw [h1_exp, h2_exp] at h_main
        have h_δ2 : Real.exp (-ω n * u) ≤ Real.exp (-δ₀ * u) := by
          rw [Real.exp_le_exp]
          nlinarith [hω_low n]
        have h_rhs : C_lip * (C_rem * (Real.exp (-ω n * u) * Real.exp (-δ₀ * u))) +
            C_tay * (‖c n‖ * Real.exp (-ω n * u) * (‖c n‖ * Real.exp (-ω n * u))) ≤
            (‖c n‖ * Real.exp (-ω n * u)) * (C_final * Real.exp (-δ₀ * u)) := by
          have hB : C_tay * (‖c n‖ * Real.exp (-ω n * u) * (‖c n‖ * Real.exp (-ω n * u))) ≤
              C_tay * ‖c n‖ ^ 2 * Real.exp (-ω n * u) * Real.exp (-δ₀ * u) := by
            have hle := mul_le_mul_of_nonneg_left h_δ2
              (mul_nonneg (mul_nonneg hC_tay (sq_nonneg ‖c n‖)) (Real.exp_pos (-ω n * u)).le)
            linarith
          have hCeq : (‖c n‖ * Real.exp (-ω n * u)) * (C_final * Real.exp (-δ₀ * u)) =
              (C_lip * C_rem + C_tay * ‖c n‖ ^ 2) * Real.exp (-ω n * u) * Real.exp (-δ₀ * u) := by
            dsimp only [C_final]
            field_simp [hcn_pos.ne']
          rw [hCeq]
          linarith
        exact le_of_mul_le_mul_left (h_main.trans h_rhs) hpos_den
      have h_iso := h_bridge (D_freq r (ω n) P) ⟨C_final, h_bridge_bound⟩
      by_contra h_ne
      exact hP_min (D_freq r (ω n) P) h_ne (degree_D_freq_lt (ω n) P hP_pos_deg) h_iso
  let nodes : Fin (r + 1) → ℂ := fun i => -(ω i.val : ℂ)
  have h_inj : Function.Injective nodes := by
    intro i j hij
    have hre := congrArg Complex.re hij
    simp only [nodes, Complex.neg_re, Complex.ofReal_re, neg_inj] at hre
    exact Fin.ext (hω_mono.injective hre)
  let V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.vandermonde nodes
  have hV_det : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr h_inj
  let VC : Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1)) ℂ) :=
    V.map MvPolynomial.C
  have hVC_det : VC.det ∈ nonZeroDivisors (MvPolynomial (Fin (r + 1)) ℂ) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    change ((MvPolynomial.C : ℂ →+* MvPolynomial (Fin (r + 1)) ℂ).mapMatrix V).det ≠ 0
    rw [← RingHom.map_det]
    intro h0
    exact hV_det (MvPolynomial.C_eq_zero.mp h0)
  have hVC_mul : VC *ᵥ (fun j : Fin (r + 1) => MvPolynomial.pderiv j P) = 0 := by
    funext i
    simp only [VC, Matrix.mulVec, dotProduct, Matrix.map_apply, V, Matrix.vandermonde_apply,
      Pi.zero_apply]
    have hDi := hD_zero i.val i.isLt
    rw [D_freq] at hDi
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at hDi
    simpa only [nodes, Algebra.smul_def, MvPolynomial.algebraMap_eq] using hDi
  have hpderiv_zero : ∀ j : Fin (r + 1), MvPolynomial.pderiv j P = 0 :=
    congrFun (Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hVC_det hVC_mul)
  have hPC := all_partials_zero P hpderiv_zero
  have hcoeff : P.coeff 0 = 0 := by
    have hh := hP_const
    rw [hPC, MvPolynomial.eval_C] at hh
    exact hh
  exact hP_ne (hPC.trans (by rw [hcoeff, map_zero]))

/-- Strong Induction + Vandermonde Contradiction for integer frequencies `m = 1, ..., r + 1`. -/
theorem stokes_vandermonde_eq_zero {r : ℕ}
    (IsFormalZero : MvPolynomial (Fin (r + 1)) ℂ → Prop)
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP_min : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 → Q.totalDegree < P.totalDegree → ¬ IsFormalZero Q)
    (hP_const : MvPolynomial.eval 0 P = 0)
    (c : ℕ → ℂ) (hc_ne : ∀ m, 1 ≤ m → m ≤ r + 1 → c m ≠ 0)
    (g_pos g_neg : ℝ → ℂ)
    (h_diff : ∀ k < r, (∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv k g_pos) u) ∧
      (∀ᶠ u in atTop, DifferentiableAt ℝ (iteratedDeriv k g_neg) u))
    (hP_pos : ∀ᶠ u in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u) P = 0)
    (hP_neg : ∀ᶠ u in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_neg u) P = 0)
    (hg_bdd : ∀ j : Fin (r + 1), ∃ C : ℝ, ∀ᶠ u in atTop, ‖iteratedDeriv j.val g_pos u‖ ≤ C)
    (h_exp : ∀ (n : ℕ) (j : Fin (r + 1)), 1 ≤ n → n ≤ r + 1 →
      ∃ C : ℝ, ∀ᶠ u in atTop,
        ‖iteratedDeriv j.val (fun t => g_neg t - g_pos t) u -
          ∑ m ∈ Finset.Icc 1 n, c m * (-(m : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(m : ℂ) * (u : ℂ))‖ ≤
          C * Real.exp (-((n : ℝ) + 1) * u))
    (h_bridge : ∀ (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∃ C : ℝ, ∀ᶠ u in atTop,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u) Q‖ ≤
          C * Real.exp (-u)) →
      IsFormalZero Q) :
    P = 0 := by
  refine stokes_vandermonde_general_eq_zero IsFormalZero P hP_min hP_const
    (fun m => (m + 1 : ℝ)) 1 zero_lt_one (fun m => by linarith [show (0 : ℝ) ≤ m by positivity])
    (fun a b hab => by simp [hab])
    (fun m => c (m + 1)) (fun m hm => hc_ne (m + 1) (by omega) (by omega))
    g_pos g_neg h_diff hP_pos hP_neg hg_bdd ?_ ?_
  · intro n j hn
    obtain ⟨C, hC⟩ := h_exp (n + 1) j (by omega) (by omega)
    refine ⟨C, ?_⟩
    filter_upwards [hC] with u hu
    have hsum : ∑ m ∈ Finset.range (n + 1), c (m + 1) * (-((m + 1 : ℝ) : ℂ)) ^ (j : ℕ) *
        Complex.exp (-((m + 1 : ℝ) : ℂ) * (u : ℂ)) =
        ∑ m ∈ Finset.Icc 1 (n + 1), c m * (-(m : ℂ)) ^ (j : ℕ) *
          Complex.exp (-(m : ℂ) * (u : ℂ)) := by
      have hIcc : Finset.Icc 1 (n + 1) = (Finset.range (n + 1)).map
          ⟨fun m => m + 1, Nat.succ_injective⟩ := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨m, hm, rfl⟩; omega
      rw [hIcc, Finset.sum_map]
      refine Finset.sum_congr rfl fun m _ => by simp
    rw [hsum]
    simpa [show ((n : ℝ) + 1) + 1 = ((n + 1 : ℕ) : ℝ) + 1 by push_cast; ring] using hu
  · intro Q ⟨C, hQ⟩
    apply h_bridge Q
    refine ⟨C, ?_⟩
    simpa using hQ

/-! ### 2. Formal Laplace Series `gHat` in `w = 1/u` -/

/-- Formal differentiation operator `d/du = -w^2 d/dw` on `ℂ[[w]]` (`w = 1/u`). -/
@[expose] def d_u (S : PowerSeries ℂ) : PowerSeries ℂ :=
  -(PowerSeries.X ^ 2 * PowerSeries.derivative S)

/-- Formal evaluation of a differential polynomial `P(y, y', ..., y^(r))` at `S ∈ ℂ[[1/u]]`. -/
@[expose] def formalEval {r : ℕ} (S : PowerSeries ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) : PowerSeries ℂ :=
  MvPolynomial.aeval (fun j : Fin (r + 1) => d_u^[j.val] S) P

/-- The Borel kernel `φ(ξ) = Γ(1 - ξ)`. -/
@[expose] def phi (ξ : ℂ) : ℂ := Complex.Gamma (1 - ξ)

/-- The asymptotic formal power series `ĝ(u) = ∑_{k ≥ 0} (-1)^k Γ^(k)(1) u^{-k-1}`
represented in `w = 1/u` so `coeff (k + 1) gHat = iteratedDeriv k phi 0`. -/
@[expose] def gHat : PowerSeries ℂ :=
  PowerSeries.mk fun n => match n with
    | 0 => 0
    | k + 1 => iteratedDeriv k phi 0

theorem gHat_coeff_zero : PowerSeries.coeff 0 gHat = 0 := by
  simp [gHat]

theorem gHat_coeff_succ (k : ℕ) :
    PowerSeries.coeff (k + 1) gHat = iteratedDeriv k phi 0 := by
  simp [gHat]

theorem iteratedDeriv_phi_zero (k : ℕ) :
    iteratedDeriv k phi 0 = (-1 : ℂ) ^ k * iteratedDeriv k Complex.Gamma 1 := by
  unfold phi
  simpa using congrFun (iteratedDeriv_comp_const_sub k Complex.Gamma (1 : ℂ)) 0

/-! ### 3. Tilted Rays, Star Domains, Analyticity, and Elementary Decay of `Γ(1 - ξ)` -/

@[expose] def theta4 : ℝ := Real.pi / 4
@[expose] def dPlus : ℂ := Complex.exp (I * theta4)
@[expose] def dMinus : ℂ := Complex.exp (-I * theta4)

lemma theta4_pos : 0 < theta4 := by unfold theta4; positivity
lemma theta4_lt_pi : theta4 < Real.pi := by unfold theta4; linarith [Real.pi_pos]

lemma dPlus_eq : dPlus = (Real.sqrt 2 / 2 : ℂ) + (Real.sqrt 2 / 2 : ℂ) * I := by
  unfold dPlus theta4
  rw [mul_comm I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

lemma dMinus_eq : dMinus = (Real.sqrt 2 / 2 : ℂ) - (Real.sqrt 2 / 2 : ℂ) * I := by
  unfold dMinus theta4
  rw [neg_mul, mul_comm I, show -(↑(Real.pi / 4) * I) = (↑(-(Real.pi / 4)) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

lemma dPlus_re : dPlus.re = Real.sqrt 2 / 2 := by rw [dPlus_eq]; simp
lemma dPlus_im : dPlus.im = Real.sqrt 2 / 2 := by rw [dPlus_eq]; simp
lemma dMinus_re : dMinus.re = Real.sqrt 2 / 2 := by rw [dMinus_eq]; simp
lemma dMinus_im : dMinus.im = -(Real.sqrt 2 / 2) := by rw [dMinus_eq]; simp

lemma dPlus_re_pos : 0 < dPlus.re := by rw [dPlus_re]; positivity
lemma dMinus_re_pos : 0 < dMinus.re := by rw [dMinus_re]; positivity
lemma dPlus_im_pos : 0 < dPlus.im := by rw [dPlus_im]; positivity
lemma dMinus_im_neg : dMinus.im < 0 := by rw [dMinus_im]; exact neg_lt_zero.mpr (by positivity)

lemma norm_dPlus : ‖dPlus‖ = 1 := by
  unfold dPlus; rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]

lemma norm_dMinus : ‖dMinus‖ = 1 := by
  unfold dMinus
  rw [neg_mul, mul_comm I, show -(↑theta4 * I) = (↑(-theta4) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

@[expose] def UPlus : Set ℂ := {z : ℂ | ‖z‖ < 1 ∨ 0 < z.im}
@[expose] def UMinus : Set ℂ := {z : ℂ | ‖z‖ < 1 ∨ z.im < 0}

lemma isOpen_UPlus : IsOpen UPlus :=
  (isOpen_lt continuous_norm continuous_const).union (isOpen_lt continuous_const Complex.continuous_im)

lemma isOpen_UMinus : IsOpen UMinus :=
  (isOpen_lt continuous_norm continuous_const).union (isOpen_lt Complex.continuous_im continuous_const)

lemma isPreconnected_UPlus : IsPreconnected UPlus := by
  have h1 : IsPreconnected (Metric.ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
  have h2 : IsPreconnected {z : ℂ | 0 < z.im} := by
    refine Convex.isPreconnected ?_
    intro x hx y hy a b ha hb hab
    change 0 < (a • x + b • y).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb (le_of_lt hy))
  have hU : UPlus = Metric.ball (0 : ℂ) 1 ∪ {z : ℂ | 0 < z.im} := by
    ext z; simp [UPlus, Metric.mem_ball, dist_zero_right]
  rw [hU]
  refine h1.union' ?_ h2
  refine ⟨(1 / 2 : ℂ) * I, ?_, ?_⟩
  · simp [Metric.mem_ball, dist_zero_right]; norm_num
  · change 0 < ((1 / 2 : ℂ) * I).im; norm_num

lemma isPreconnected_UMinus : IsPreconnected UMinus := by
  have h1 : IsPreconnected (Metric.ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
  have h2 : IsPreconnected {z : ℂ | z.im < 0} := by
    refine Convex.isPreconnected ?_
    intro x hx y hy a b ha hb hab
    change (a • x + b • y).im < 0
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · nlinarith [mul_pos ha' (neg_pos.mpr hx), mul_nonneg hb (neg_nonneg.mpr hy.le)]
  have hU : UMinus = Metric.ball (0 : ℂ) 1 ∪ {z : ℂ | z.im < 0} := by
    ext z; simp [UMinus, Metric.mem_ball, dist_zero_right]
  rw [hU]
  refine h1.union' ?_ h2
  refine ⟨-(1 / 2 : ℂ) * I, ?_, ?_⟩
  · simp [Metric.mem_ball, dist_zero_right]; norm_num
  · change (-(1 / 2 : ℂ) * I).im < 0; norm_num

lemma star_UPlus : ∀ z ∈ UPlus, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ UPlus := by
  intro z hz t ht
  rcases hz with hz1 | hzim
  · left
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz1
  · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left; simp
    · right
      simp [Complex.mul_im, mul_pos ht_pos hzim]

lemma star_UMinus : ∀ z ∈ UMinus, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ UMinus := by
  intro z hz t ht
  rcases hz with hz1 | hzim
  · left
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz1
  · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left; simp
    · right
      simp [Complex.mul_im]
      exact mul_neg_of_pos_of_neg ht_pos hzim

lemma UPlus_contains_dPlus : ∀ v : ℝ, 0 ≤ v → dPlus * (v : ℂ) ∈ UPlus := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simp
  · right
    simp [Complex.mul_im]
    exact mul_pos dPlus_im_pos hv_pos

lemma UMinus_contains_dMinus : ∀ v : ℝ, 0 ≤ v → dMinus * (v : ℂ) ∈ UMinus := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simp
  · right
    simp [Complex.mul_im]
    exact mul_neg_of_neg_of_pos dMinus_im_neg hv_pos

lemma avoids_posNat_of_UPlus {z : ℂ} (hz : z ∈ UPlus) (n : ℕ) (hn : 1 ≤ n) : z ≠ (n : ℂ) := by
  intro h
  subst h
  rcases hz with h1 | h2
  · have hle : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast hn
    linarith
  · simp at h2

lemma avoids_posNat_of_UMinus {z : ℂ} (hz : z ∈ UMinus) (n : ℕ) (hn : 1 ≤ n) : z ≠ (n : ℂ) := by
  intro h
  subst h
  rcases hz with h1 | h2
  · have hle : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast hn
    linarith
  · simp at h2

lemma phi_analyticAt_of_avoids_posNat {z : ℂ} (hz : ∀ n : ℕ, 1 ≤ n → z ≠ (n : ℂ)) :
    AnalyticAt ℂ phi z := by
  let N : ℕ := Nat.ceil (‖z‖ + 1)
  have h_fin : ∀ᶠ w in 𝓝 z, ∀ n ∈ Finset.Icc 1 N, w ≠ (n : ℂ) :=
    (Filter.eventually_all_finset (Finset.Icc 1 N)).mpr fun n hn =>
      continuousAt_id.eventually_ne (hz n (Finset.mem_Icc.mp hn).1)
  have h_norm : ∀ᶠ w in 𝓝 z, ‖w‖ < ‖z‖ + 1 :=
    continuousAt_id.norm.eventually (gt_mem_nhds (by simp : ‖id z‖ < ‖z‖ + 1))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (h_fin.and h_norm)
  have hdiff : DifferentiableOn ℂ phi (Metric.ball z r) := by
    intro w hw
    obtain ⟨hw_fin, hw_norm⟩ := hball (Metric.mem_ball.mp hw)
    have hw_avoid : ∀ n : ℕ, 1 ≤ n → w ≠ (n : ℂ) := by
      intro n hn
      by_cases hnN : n ≤ N
      · exact hw_fin n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
      · intro hwn
        have hlt : N < n := Nat.lt_of_not_le hnN
        have hle : ‖z‖ + 1 ≤ (N : ℝ) := Nat.le_ceil _
        have hlt2 : (N : ℝ) < (n : ℝ) := by exact_mod_cast hlt
        have hnw : ‖w‖ = (n : ℝ) := by rw [hwn, Complex.norm_natCast]
        linarith
    have hg : DifferentiableAt ℂ Complex.Gamma (1 - w) := by
      refine Complex.differentiableAt_Gamma (1 - w) fun m hm => ?_
      apply hw_avoid (m + 1) (by omega)
      push_cast
      linear_combination -hm
    exact ((hg.comp w ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id))).differentiableWithinAt
  exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

lemma phi_analyticOn_UPlus : AnalyticOnNhd ℂ phi UPlus :=
  fun _ hz => phi_analyticAt_of_avoids_posNat (avoids_posNat_of_UPlus hz)

lemma phi_analyticOn_UMinus : AnalyticOnNhd ℂ phi UMinus :=
  fun _ hz => phi_analyticAt_of_avoids_posNat (avoids_posNat_of_UMinus hz)

lemma Gamma_strip_bound {w : ℂ} (hw1 : 1 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖Complex.Gamma w‖ ≤ 2 := by
  have hw0 : 0 < w.re := by linarith
  rw [Complex.Gamma_eq_integral hw0]
  unfold Complex.GammaIntegral
  have h_bound_fun : ∀ t ∈ Ioi (0 : ℝ),
      ‖(Real.exp (-t) : ℂ) * (t : ℂ) ^ (w - 1)‖ ≤ Real.exp (-t) * (1 + t) := by
    intro t ht
    change 0 < t at ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-t)),
      Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
    have hpow : t ^ (w.re - 1) ≤ 1 + t := by
      have hexp0 : 0 ≤ w.re - 1 := by linarith
      have hexp1 : w.re - 1 ≤ 1 := by linarith
      by_cases ht1 : t ≤ 1
      · exact (Real.rpow_le_one ht.le ht1 hexp0).trans (by linarith)
      · have h1t : 1 ≤ t := le_of_not_ge ht1
        exact ((Real.rpow_le_rpow_of_exponent_le h1t hexp1).trans_eq (Real.rpow_one t)).trans
          (by linarith)
    exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-t)).le
  have hi1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := integrableOn_exp_neg_Ioi 0
  have hi2 : IntegrableOn (fun t : ℝ => Real.exp (-t) * t) (Ioi 0) := by
    simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
      (Real.GammaIntegral_convergent (s := 2) (by norm_num))
  have hi_sum : IntegrableOn (fun t : ℝ => Real.exp (-t) * (1 + t)) (Ioi 0) := by
    have heq : (fun t : ℝ => Real.exp (-t) * (1 + t)) =
        fun t => Real.exp (-t) + Real.exp (-t) * t := by funext t; ring
    rw [heq]; exact hi1.add hi2
  have hnorm_le : ‖∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * (t : ℂ) ^ (w - 1)‖ ≤
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * (1 + t) := by
    calc ‖∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * (t : ℂ) ^ (w - 1)‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖(Real.exp (-t) : ℂ) * (t : ℂ) ^ (w - 1)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-t) * (1 + t) := by
          refine setIntegral_mono_on ?_ hi_sum measurableSet_Ioi h_bound_fun
          exact (Complex.GammaIntegral_convergent hw0).norm
  have hint_val : ∫ t in Ioi (0 : ℝ), Real.exp (-t) * (1 + t) = 2 := by
    have heq : (fun t : ℝ => Real.exp (-t) * (1 + t)) =
        fun t => Real.exp (-t) + Real.exp (-t) * t := by funext t; ring
    rw [heq, integral_add hi1 hi2]
    have hv1 : ∫ t in Ioi (0 : ℝ), Real.exp (-t) = 1 := by
      have hg1 := Real.Gamma_eq_integral (s := 1) one_pos
      rw [Real.Gamma_one] at hg1
      simpa using hg1.symm
    have hv2 : ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t = 1 := by
      have hg2 := Real.Gamma_eq_integral (s := 2) (by norm_num)
      have hval2 : Real.Gamma (2 : ℝ) = 1 := by simp
      rw [hval2] at hg2
      simp [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hg2
      exact hg2.symm
    linarith
  exact hnorm_le.trans_eq hint_val

lemma Gamma_one_sub_mul_falling {ξ : ℂ} (K : ℕ) (hξ : ∀ n : ℕ, 1 ≤ n → ξ ≠ (n : ℂ)) :
    (∏ k ∈ Finset.range (K + 1), ((k + 1 : ℂ) - ξ)) * Complex.Gamma (1 - ξ) =
      Complex.Gamma ((K + 2 : ℂ) - ξ) := by
  induction K with
  | zero =>
    have h1 : (1 : ℂ) - ξ ≠ 0 := sub_ne_zero.mpr (by simpa using (hξ 1 le_rfl).symm)
    simp [show (2 : ℂ) - ξ = (1 - ξ) + 1 by ring, (Complex.Gamma_add_one (1 - ξ) h1).symm]
  | succ K ih =>
    have hK2 : ((K + 2 : ℂ) - ξ) ≠ 0 := by
      intro h0
      apply hξ (K + 2) (by omega)
      push_cast
      linear_combination -h0
    rw [Finset.prod_range_succ]
    calc ((∏ k ∈ Finset.range (K + 1), ((k + 1 : ℂ) - ξ)) * (((K + 1 : ℕ) : ℂ) + 1 - ξ)) *
            Complex.Gamma (1 - ξ)
        = ((K + 2 : ℂ) - ξ) *
            ((∏ k ∈ Finset.range (K + 1), ((k + 1 : ℂ) - ξ)) * Complex.Gamma (1 - ξ)) := by
          push_cast; ring
      _ = ((K + 2 : ℂ) - ξ) * Complex.Gamma ((K + 2 : ℂ) - ξ) := by rw [ih]
      _ = Complex.Gamma ((K + 2 : ℂ) - ξ + 1) := (Complex.Gamma_add_one _ hK2).symm
      _ = Complex.Gamma (((K + 1 : ℕ) : ℂ) + 2 - ξ) := by congr 1; push_cast; ring

private lemma real_prod_le_prod {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact mul_le_mul (hfg i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfg j (Finset.mem_insert_of_mem hj)))
      (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj))
      ((hf i (Finset.mem_insert_self i s)).trans (hfg i (Finset.mem_insert_self i s)))

lemma phi_ray_superExp_decay {d : ℂ} (hre : 0 < d.re) (him : d.im ≠ 0)
    (havoid : ∀ v : ℝ, 0 ≤ v → ∀ n : ℕ, 1 ≤ n → d * (v : ℂ) ≠ (n : ℂ)) (D : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 ≤ v → ‖phi (d * (v : ℂ))‖ ≤ C * Real.exp (-D * v) := by
  let s : ℝ := |d.im|
  have hs : 0 < s := abs_pos.mpr him
  let V₀ : ℝ := Real.exp (max D 0 / d.re) / s
  have hV₀_nonneg : 0 ≤ V₀ := by positivity
  have hcont : ContinuousOn (fun v : ℝ => ‖phi (d * (v : ℂ))‖ * Real.exp (D * v)) (Icc 0 V₀) := by
    refine (ContinuousOn.norm ?_).mul ((continuous_const.mul continuous_id).rexp).continuousOn
    intro v hv
    have hmul : Continuous (fun x : ℝ => d * (x : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    exact ((phi_analyticAt_of_avoids_posNat (havoid v hv.1)).continuousAt.comp
      (f := fun x : ℝ => d * (x : ℂ)) hmul.continuousAt).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let C : ℝ := max 2 C₀
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, fun v hv => ?_⟩
  by_cases hv_small : v ≤ V₀
  · have hmem : v ∈ Icc 0 V₀ := ⟨hv, hv_small⟩
    have hb := hC₀ v hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)] at hb
    calc ‖phi (d * (v : ℂ))‖
        = (‖phi (d * (v : ℂ))‖ * Real.exp (D * v)) * Real.exp (-D * v) := by
          rw [mul_assoc, ← Real.exp_add, show D * v + -D * v = 0 by ring, Real.exp_zero, mul_one]
      _ ≤ C₀ * Real.exp (-D * v) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ ≤ C * Real.exp (-D * v) := mul_le_mul_of_nonneg_right (le_max_right 2 C₀) (Real.exp_pos _).le
  · have hv_gt : V₀ < v := lt_of_not_ge hv_small
    have hv_pos : 0 < v := lt_of_le_of_lt hV₀_nonneg hv_gt
    let ξ : ℂ := d * (v : ℂ)
    have hξre_nonneg : 0 ≤ ξ.re := by
      simp only [ξ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg hre.le hv
    let K : ℕ := Nat.floor ξ.re
    have hK_le : (K : ℝ) ≤ ξ.re := Nat.floor_le hξre_nonneg
    have hlt_K : ξ.re < (K : ℝ) + 1 := Nat.lt_floor_add_one ξ.re
    have hw1 : 1 ≤ ((K + 2 : ℂ) - ξ).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.re_ofNat]
      linarith
    have hw2 : ((K + 2 : ℂ) - ξ).re ≤ 2 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.re_ofNat]
      linarith
    have hGamma_w : ‖Complex.Gamma ((K + 2 : ℂ) - ξ)‖ ≤ 2 := Gamma_strip_bound hw1 hw2
    have h_fall := Gamma_one_sub_mul_falling K (havoid v hv)
    have h_each : ∀ k : ℕ, s * v ≤ ‖(k + 1 : ℂ) - ξ‖ := by
      intro k
      have him_eq : ((k + 1 : ℂ) - ξ).im = -(d.im * v) := by
        simp [ξ, Complex.mul_im]
      calc s * v = |d.im * v| := by rw [abs_mul, abs_of_nonneg hv]
        _ = |((k + 1 : ℂ) - ξ).im| := by rw [him_eq, abs_neg]
        _ ≤ ‖(k + 1 : ℂ) - ξ‖ := Complex.abs_im_le_norm _
    have hsv_ge_exp : Real.exp (max D 0 / d.re) ≤ s * v := by
      have := (div_lt_iff₀ hs).mp hv_gt
      linarith
    have hsv_ge_one : 1 ≤ s * v :=
      (Real.one_le_exp (div_nonneg (le_max_right D 0) hre.le)).trans hsv_ge_exp
    have hsv_pos : 0 < s * v := zero_lt_one.trans_le hsv_ge_one
    have hprod_ge : (s * v) ^ (K + 1) ≤ ∏ k ∈ Finset.range (K + 1), ‖(k + 1 : ℂ) - ξ‖ := by
      simpa using real_prod_le_prod (Finset.range (K + 1)) (fun _ => s * v)
        (fun k => ‖(k + 1 : ℂ) - ξ‖) (fun _ _ => hsv_pos.le) (fun k _ => h_each k)
    have hexp_Dv : Real.exp (D * v) ≤ (s * v) ^ (K + 1) := by
      have hlog : max D 0 / d.re ≤ Real.log (s * v) := by
        rw [← Real.log_exp (max D 0 / d.re)]
        exact Real.log_le_log (Real.exp_pos _) hsv_ge_exp
      have hK1_ge : d.re * v ≤ (K + 1 : ℝ) := by
        have hξeq : ξ.re = d.re * v := by
          simp [ξ, Complex.mul_re]
        linarith [hlt_K, hξeq]
      have hpow_exp : (s * v) ^ (K + 1) = Real.exp (((K + 1 : ℝ)) * Real.log (s * v)) := by
        rw [← Real.rpow_natCast (s * v) (K + 1), Real.rpow_def_of_pos hsv_pos]
        congr 1; push_cast; ring
      rw [hpow_exp, Real.exp_le_exp]
      have hlog_nonneg : 0 ≤ Real.log (s * v) := Real.log_nonneg hsv_ge_one
      calc D * v ≤ max D 0 * v := mul_le_mul_of_nonneg_right (le_max_left D 0) hv
        _ = (d.re * v) * (max D 0 / d.re) := by field_simp [hre.ne']
        _ ≤ (K + 1 : ℝ) * Real.log (s * v) :=
          mul_le_mul hK1_ge hlog (div_nonneg (le_max_right D 0) hre.le) (by positivity)
    have hnorm_eq : ‖∏ k ∈ Finset.range (K + 1), ((k + 1 : ℂ) - ξ)‖ * ‖phi ξ‖ =
        ‖Complex.Gamma ((K + 2 : ℂ) - ξ)‖ := by
      rw [← norm_mul]
      exact congrArg norm h_fall
    rw [norm_prod] at hnorm_eq
    have hphi_le : ‖phi ξ‖ ≤ 2 / Real.exp (D * v) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      calc ‖phi ξ‖ * Real.exp (D * v)
          ≤ ‖phi ξ‖ * (s * v) ^ (K + 1) := mul_le_mul_of_nonneg_left hexp_Dv (norm_nonneg _)
        _ ≤ ‖phi ξ‖ * ∏ k ∈ Finset.range (K + 1), ‖(k + 1 : ℂ) - ξ‖ :=
          mul_le_mul_of_nonneg_left hprod_ge (norm_nonneg _)
        _ = ‖Complex.Gamma ((K + 2 : ℂ) - ξ)‖ := by rw [mul_comm, hnorm_eq]
        _ ≤ 2 := hGamma_w
    calc ‖phi ξ‖ ≤ 2 / Real.exp (D * v) := hphi_le
      _ = 2 * Real.exp (-D * v) := by rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]
      _ ≤ C * Real.exp (-D * v) := mul_le_mul_of_nonneg_right (le_max_left 2 C₀) (Real.exp_pos _).le

lemma phi_dPlus_decay (D : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 ≤ v → ‖phi (dPlus * (v : ℂ))‖ ≤ C * Real.exp (-D * v) :=
  phi_ray_superExp_decay dPlus_re_pos dPlus_im_pos.ne'
    (fun v hv => avoids_posNat_of_UPlus (UPlus_contains_dPlus v hv)) D

lemma phi_dMinus_decay (D : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 ≤ v → ‖phi (dMinus * (v : ℂ))‖ ≤ C * Real.exp (-D * v) :=
  phi_ray_superExp_decay dMinus_re_pos dMinus_im_neg.ne
    (fun v hv => avoids_posNat_of_UMinus (UMinus_contains_dMinus v hv)) D

lemma Gamma_one_sub_arc_bound {N : ℕ} (hN : 2 ≤ N) {y : ℝ} (hy : |y| ≤ theta4) :
    ‖phi (((N : ℝ) + 1 / 2 : ℂ) * Complex.exp (I * (y : ℂ)))‖ ≤ 8 := by
  let R : ℝ := (N : ℝ) + 1 / 2
  let ξ : ℂ := (R : ℂ) * Complex.exp (I * (y : ℂ))
  suffices h : ‖phi ξ‖ ≤ 8 by
    simpa [ξ, R] using h
  have hnorm_ξ : ‖ξ‖ = R := by
    simp only [ξ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < R)]
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have havoid : ∀ n : ℕ, 1 ≤ n → ξ ≠ (n : ℂ) := by
    intro n hn h
    have hn_eq : R = (n : ℝ) := by
      have := congrArg norm h
      rw [hnorm_ξ, Complex.norm_natCast] at this
      exact this
    have h2 : 2 * R = 2 * (n : ℝ) := congrArg (2 * ·) hn_eq
    have h2' : ((2 * N + 1 : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by
      push_cast; linarith [h2, show R = (N : ℝ) + 1 / 2 from rfl]
    have hnat : 2 * N + 1 = 2 * n := by exact_mod_cast h2'
    omega
  have hcos_ge : Real.sqrt 2 / 2 ≤ Real.cos y := by
    have hcos_pos : Real.cos theta4 = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [← hcos_pos, ← Real.cos_abs y]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) theta4_lt_pi.le hy
  have hR_ge : (5 / 2 : ℝ) ≤ R := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith [show R = (N : ℝ) + 1 / 2 from rfl]
  have hξre_eq : ξ.re = R * Real.cos y := by
    simp only [ξ, mul_comm I (y : ℂ), Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.I_re, Complex.I_im, mul_zero, mul_one]
    ring
  have hξre_ge : 1 < ξ.re := by
    rw [hξre_eq]
    have hrt2 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    have hsq : 1 < (5 / 2 : ℝ) * (Real.sqrt 2 / 2) := by linarith
    calc (1 : ℝ) < (5 / 2 : ℝ) * (Real.sqrt 2 / 2) := hsq
      _ ≤ R * Real.cos y := mul_le_mul hR_ge hcos_ge (by positivity) (by positivity)
  let K : ℕ := Nat.floor ξ.re
  have hK_ge_1 : 1 ≤ K := Nat.le_floor (by simpa using hξre_ge.le)
  have hK_le : (K : ℝ) ≤ ξ.re := Nat.floor_le (by linarith)
  have hlt_K : ξ.re < (K : ℝ) + 1 := Nat.lt_floor_add_one ξ.re
  have hGamma_w : ‖Complex.Gamma ((K + 2 : ℂ) - ξ)‖ ≤ 2 :=
    Gamma_strip_bound
      (by simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.re_ofNat]; linarith)
      (by simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.re_ofNat]; linarith)
  have h_fall := Gamma_one_sub_mul_falling K havoid
  have hnorm_eq : (∏ k ∈ Finset.range (K + 1), ‖(k + 1 : ℂ) - ξ‖) * ‖phi ξ‖ =
      ‖Complex.Gamma ((K + 2 : ℂ) - ξ)‖ := by
    rw [← norm_prod, ← norm_mul]
    exact congrArg norm h_fall
  let lb : ℕ → ℝ := fun k => if k + 2 ≤ K then 1 else 1 / 2
  have h_lb : ∀ k ∈ Finset.range (K + 1), lb k ≤ ‖(k + 1 : ℂ) - ξ‖ := by
    intro k hk
    simp only [lb]
    split_ifs with hkle
    · have hle_re : (k + 1 : ℝ) + 1 ≤ ξ.re := by
        have hk' : (k : ℝ) + 2 ≤ (K : ℝ) := by exact_mod_cast hkle
        linarith
      calc (1 : ℝ) ≤ ξ.re - (k + 1 : ℝ) := by linarith
        _ = (ξ - (k + 1 : ℂ)).re := by simp
        _ ≤ ‖ξ - (k + 1 : ℂ)‖ := Complex.re_le_norm _
        _ = ‖(k + 1 : ℂ) - ξ‖ := norm_sub_rev _ _
    · have hdist : (1 / 2 : ℝ) ≤ |R - (k + 1 : ℝ)| := by
        rcases le_or_gt (k + 1 : ℕ) N with hkn | hnk
        · have : (k + 1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkn
          rw [abs_of_nonneg (by linarith [show R = (N : ℝ) + 1 / 2 from rfl])]
          linarith [show R = (N : ℝ) + 1 / 2 from rfl]
        · have : (N : ℝ) + 1 ≤ (k + 1 : ℝ) := by exact_mod_cast hnk
          rw [abs_of_nonpos (by linarith [show R = (N : ℝ) + 1 / 2 from rfl])]
          linarith [show R = (N : ℝ) + 1 / 2 from rfl]
      calc (1 / 2 : ℝ) ≤ |R - (k + 1 : ℝ)| := hdist
        _ = |‖(k + 1 : ℂ)‖ - ‖ξ‖| := by
          rw [hnorm_ξ, show (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
            Complex.norm_natCast, Nat.cast_add, Nat.cast_one, abs_sub_comm]
        _ ≤ ‖(k + 1 : ℂ) - ξ‖ := abs_norm_sub_norm_le _ _
  have h_lb_prod : (1 / 4 : ℝ) ≤ ∏ k ∈ Finset.range (K + 1), lb k := by
    have hsplit : Finset.range (K + 1) = (Finset.range (K - 1)) ∪ {K - 1, K} := by
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hdisj : Disjoint (Finset.range (K - 1)) {K - 1, K} := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      omega
    have hne : K - 1 ≠ K := by omega
    rw [hsplit, Finset.prod_union hdisj, Finset.prod_pair hne]
    have hleft : ∏ k ∈ Finset.range (K - 1), lb k = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      simp only [Finset.mem_range] at hk
      simp [lb, show k + 2 ≤ K by omega]
    have hright1 : lb (K - 1) = 1 / 2 := by
      simp [lb, show ¬((K - 1) + 2 ≤ K) by omega]
    have hright2 : lb K = 1 / 2 := by
      simp [lb, show ¬(K + 2 ≤ K) by omega]
    rw [hleft, hright1, hright2]
    norm_num
  have hprod_ge : (1 / 4 : ℝ) ≤ ∏ k ∈ Finset.range (K + 1), ‖(k + 1 : ℂ) - ξ‖ := by
    refine h_lb_prod.trans (real_prod_le_prod (Finset.range (K + 1)) _ _ (fun k hk => ?_) h_lb)
    simp only [lb]; split_ifs <;> positivity
  have h4 : (1 / 4 : ℝ) * ‖phi ξ‖ ≤ 2 :=
    (mul_le_mul_of_nonneg_right hprod_ge (norm_nonneg _)).trans (hnorm_eq.symm ▸ hGamma_w)
  linarith

/-! ### 4. Laplace Convolution, `Minor`, `BorelExpr`, Taylor Coefficients & Watson Asymptotics -/

@[expose] def complexConvolution (F G : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * ∫ t : ℝ in Ioc 0 1, F ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z)

@[expose] def borelProduct (F G : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..v, F t * G (v - t)

@[expose] def ExpType (F : ℝ → ℂ) : Prop :=
  ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ u ≥ 0, ‖F u‖ ≤ C * Real.exp (D * u)

@[expose] def damped (p : ℂ) (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-p * (u : ℂ)) * F u

@[expose] def complexLaplace (F : ℝ → ℂ) (p : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), damped p F u

lemma complexConvolution_analytic {U : Set ℂ} (hU : IsOpen U)
    (star : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ U)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (complexConvolution F G) U := by
  let f (z : ℂ) (t : ℝ) := F ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z)
  let Df (z : ℂ) (t : ℝ) := deriv F ((t : ℂ) * z) * (t : ℂ) * G (((1 - t : ℝ) : ℂ) * z) +
    F ((t : ℂ) * z) * (deriv G (((1 - t : ℝ) : ℂ) * z) * ((1 - t : ℝ) : ℂ))
  let S := U ×ˢ Icc (0 : ℝ) 1
  have refl (t : ℝ) (ht : t ∈ Icc 0 1) : 1 - t ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
  have m1 : MapsTo (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) S U := fun _ hp => star _ hp.1 _ hp.2
  have m2 : MapsTo (fun p : ℂ × ℝ => ((1 - p.2 : ℝ) : ℂ) * p.1) S U :=
    fun _ hp => star _ hp.1 _ (refl _ hp.2)
  have c1 : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) := by fun_prop
  have c2 : Continuous (fun p : ℂ × ℝ => ((1 - p.2 : ℝ) : ℂ) * p.1) := by fun_prop
  have cf : ContinuousOn f.uncurry S := (hF.continuousOn.comp c1.continuousOn m1).mul
    (hG.continuousOn.comp c2.continuousOn m2)
  have cd : ContinuousOn Df.uncurry S := by
    refine (((hF.deriv.continuousOn.comp c1.continuousOn m1).mul
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn).mul
      (hG.continuousOn.comp c2.continuousOn m2)).add
      ((hF.continuousOn.comp c1.continuousOn m1).mul
        ((hG.deriv.continuousOn.comp c2.continuousOn m2).mul
          (by fun_prop : Continuous (fun p : ℂ × ℝ => ((1 - p.2 : ℝ) : ℂ))).continuousOn))
  have derivAt (z : ℂ) (hz : z ∈ U) (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (f · t) (Df z t) z := by
    have h1 := (hF _ (star z hz t ht)).differentiableAt.hasDerivAt.comp z
      ((hasDerivAt_id z).const_mul (t : ℂ))
    have h2 := (hG _ (star z hz _ (refl t ht))).differentiableAt.hasDerivAt.comp z
      ((hasDerivAt_id z).const_mul ((1 - t : ℝ) : ℂ))
    simpa only [mul_one, Function.comp_def, id_eq, Df, f] using! h1.mul h2
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  apply DifferentiableWithinAt.mul differentiableWithinAt_id
  apply DifferentiableAt.differentiableWithinAt
  apply HasFDerivAt.differentiableAt
  apply hasFDerivAt_integral_of_continuousOn_fderiv (𝕜 := ℂ) (F := f)
    (hU.mem_nhds hz) isCompact_Icc measurableSet_Ioc (by simp) Ioc_subset_Icc_self cf
    (fun t ht y hy => (derivAt y hy t ht).differentiableAt.differentiableWithinAt)
  apply ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp_continuousOn cd).congr
  intro p hp
  apply ContinuousLinearMap.ext
  intro y
  rw [fderiv_eq_deriv_mul, (derivAt p.1 hp.1 p.2 hp.2).deriv]
  rfl

lemma complexConvolution_real (F G : ℂ → ℂ) (v : ℝ) :
    complexConvolution F G v = borelProduct (fun t : ℝ => F t) (fun t : ℝ => G t) v := by
  unfold complexConvolution borelProduct
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun t : ℝ => F t * G (v - t)) v
  rw [mul_zero, mul_one] at h
  simp only [Complex.ofReal_sub] at *
  rw [← h]
  change (v : ℂ) * _ = (v : ℂ) * _
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_one]
  congr 2 <;> ring

lemma borelProduct_bound {F G : ℝ → ℂ} {C E D : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hF : ∀ u ≥ 0, ‖F u‖ ≤ C * Real.exp (D * u)) (hG : ∀ u ≥ 0, ‖G u‖ ≤ E * Real.exp (D * u))
    {v : ℝ} (hv : 0 ≤ v) : ‖borelProduct F G v‖ ≤ C * E * Real.exp ((D + 1) * v) := by
  have hle (u : ℝ) (hu : u ∈ uIoc 0 v) : ‖F u * G (v - u)‖ ≤ C * E * Real.exp (D * v) := by
    rw [uIoc_of_le hv] at hu
    rw [norm_mul]
    calc _ ≤ (C * Real.exp (D * u)) * (E * Real.exp (D * (v - u))) :=
          mul_le_mul (hF u hu.1.le) (hG _ (sub_nonneg.mpr hu.2)) (norm_nonneg _) (by positivity)
      _ = C * E * (Real.exp (D * u) * Real.exp (D * (v - u))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
  rw [sub_zero, abs_of_nonneg hv] at h
  refine h.trans ?_
  rw [add_mul, one_mul, Real.exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (le_trans (by linarith : v ≤ v + 1) (Real.add_one_le_exp v))
    (by positivity)

lemma ExpType.common {F G : ℝ → ℂ} (hf : ExpType F) (hg : ExpType G) :
    ∃ C E D : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ 0 ≤ D ∧
      (∀ u ≥ 0, ‖F u‖ ≤ C * Real.exp (D * u)) ∧ (∀ u ≥ 0, ‖G u‖ ≤ E * Real.exp (D * u)) := by
  obtain ⟨C, D, hc, hd, hf⟩ := hf
  obtain ⟨E, T, he, ht, hg⟩ := hg
  refine ⟨C, E, max D T, hc, he, hd.trans (le_max_left ..), ?_, ?_⟩
  · intro u hu; exact (hf u hu).trans (by gcongr; exact le_max_left ..)
  · intro u hu; exact (hg u hu).trans (by gcongr; exact le_max_right ..)

lemma ExpType.zero : ExpType (fun _ : ℝ => (0 : ℂ)) :=
  ⟨0, 0, le_rfl, le_rfl, fun _ _ => by simp⟩

lemma ExpType.add {F G : ℝ → ℂ} (hf : ExpType F) (hg : ExpType G) :
    ExpType (fun u => F u + G u) := by
  obtain ⟨C, E, D, hc, he, hd, hf, hg⟩ := hf.common hg
  refine ⟨C + E, D, by positivity, hd, fun u hu => ?_⟩
  rw [add_mul]
  exact (norm_add_le ..).trans (add_le_add (hf u hu) (hg u hu))

lemma ExpType.scale {F : ℝ → ℂ} (hf : ExpType F) (a : ℂ) : ExpType (fun u => a * F u) := by
  obtain ⟨C, D, hc, hd, hf⟩ := hf
  refine ⟨‖a‖ * C, D, by positivity, hd, fun u hu => ?_⟩
  rw [norm_mul, mul_assoc]
  gcongr
  exact hf u hu

lemma ExpType.times_u {F : ℝ → ℂ} (hf : ExpType F) : ExpType (fun u => (u : ℂ) * F u) := by
  obtain ⟨C, D, hc, hd, hf⟩ := hf
  refine ⟨C, D + 1, hc, by positivity, fun u hu => ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, add_mul, one_mul, Real.exp_add]
  calc u * ‖F u‖ ≤ Real.exp u * (C * Real.exp (D * u)) :=
        mul_le_mul (by linarith [Real.add_one_le_exp u]) (hf u hu) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

lemma ExpType.convolution {F G : ℝ → ℂ} (hf : ExpType F) (hg : ExpType G) :
    ExpType (borelProduct F G) := by
  obtain ⟨C, E, D, hc, he, hd, hf, hg⟩ := hf.common hg
  exact ⟨C * E, D + 1, by positivity, by positivity, fun _ hu => borelProduct_bound hc he hf hg hu⟩

lemma damped_norm (p : ℂ) (F : ℝ → ℂ) (u : ℝ) :
    ‖damped p F u‖ = Real.exp (-p.re * u) * ‖F u‖ := by
  simp [damped, Complex.norm_exp]

lemma damped_integrable {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0)) {C D : ℝ}
    (hf : ∀ u ≥ 0, ‖F u‖ ≤ C * Real.exp (D * u)) {p : ℂ} (hp : D < p.re) :
    IntegrableOn (damped p F) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hp) 0).const_mul C).mono'
  · exact ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-p * (u : ℂ)))).continuousOn.mul
      hc).aestronglyMeasurable measurableSet_Ioi
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  rw [damped_norm]
  calc _ ≤ Real.exp (-p.re * u) * (C * Real.exp (D * u)) :=
        mul_le_mul_of_nonneg_left (hf u hu.le) (Real.exp_pos _).le
    _ = C * (Real.exp (-p.re * u) * Real.exp (D * u)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

lemma complexLaplace_product {F G : ℝ → ℂ} {p : ℂ}
    (hf : IntegrableOn (damped p F) (Ioi 0)) (hg : IntegrableOn (damped p G) (Ioi 0)) :
    complexLaplace (borelProduct F G) p = complexLaplace F p * complexLaplace G p := by
  have h := integral_posConvolution hf hg (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at h
  have inside (v : ℝ) : (∫ t in (0 : ℝ)..v, damped p F t * damped p G (v - t)) =
      damped p (borelProduct F G) v := by
    unfold damped borelProduct
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have he : Complex.exp (-p * (v : ℂ)) =
        Complex.exp (-p * (t : ℂ)) * Complex.exp (-p * ((v - t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, Complex.ofReal_sub]; congr 1; ring
    rw [he]; ring
  simpa only [inside, complexLaplace] using h

lemma complexLaplace_derivative {F : ℝ → ℂ} (hc : ContinuousOn F (Ioi 0)) {C D : ℝ}
    (hf : ∀ u ≥ 0, ‖F u‖ ≤ C * Real.exp (D * u)) {p : ℂ} (hp : D + 1 < p.re) :
    HasDerivAt (complexLaplace F) (-complexLaplace (fun u => (u : ℂ) * F u) p) p := by
  let G := fun u : ℝ => -(u : ℂ) * F u
  have meas (q : ℂ) {H : ℝ → ℂ} (hH : ContinuousOn H (Ioi 0)) :
      AEStronglyMeasurable (damped q H) (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-q * (u : ℂ)))).continuousOn.mul
      hH).aestronglyMeasurable measurableSet_Ioi
  have hi : IntegrableOn (fun u : ℝ => C * (Real.exp (-u) * u)) (Ioi 0) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, IntegrableOn] using!
      (Real.GammaIntegral_convergent (s := 2) (by norm_num)).const_mul C
  have hd (q : ℂ) (u : ℝ) : HasDerivAt (fun w => damped w F u) (damped q G u) q := by
    have h := (((hasDerivAt_id q).neg.mul_const (u : ℂ)).cexp).mul_const (F u)
    convert h using 1 <;> simp [damped, G]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun q u => damped q F u)
    (F' := fun q u => damped q G u) (bound := fun u : ℝ => C * (Real.exp (-u) * u))
    (s := {q : ℂ | D + 1 < q.re}) ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp)
    (.of_forall fun q => meas q hc) (damped_integrable hc hf (by linarith : D < p.re))
    (meas p (Complex.continuous_ofReal.neg.continuousOn.mul hc)) (bound_integrable := hi)
  have hb : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ q : ℂ, D + 1 < q.re →
      ‖damped q G u‖ ≤ C * (Real.exp (-u) * u) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    change 0 < u at hu
    intro q hq
    have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf u hu.le)) (Real.exp_pos _)
    rw [damped_norm]
    simp only [G, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    calc _ ≤ Real.exp (-q.re * u) * (u * (C * Real.exp (D * u))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf u hu.le) hu.le) (Real.exp_pos _).le
      _ = (C * u) * (Real.exp (-q.re * u) * Real.exp (D * u)) := by ring
      _ ≤ (C * u) * Real.exp (-u) := by
        rw [← Real.exp_add]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [mul_pos (sub_pos.mpr hq) hu]))
          (mul_nonneg hC hu.le)
      _ = _ := by ring
  have res := (h hb (ae_of_all _ fun u q _ => hd q u)).2
  have eqn (u : ℝ) : damped p G u = -damped p (fun v => (v : ℂ) * F v) u := by simp [damped, G]
  unfold complexLaplace
  simpa only [eqn, integral_neg] using! res

structure Minor where
  atom : ℂ
  density : ℂ → ℂ

structure Domain (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  star : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ U

@[expose] def ContainsRay (U : Set ℂ) (d : ℂ) : Prop :=
  ∀ v : ℝ, 0 ≤ v → d * (v : ℂ) ∈ U

@[expose] def far (d : ℂ) : Filter ℂ :=
  comap (fun p : ℂ => (p * d).re) atTop

lemma eventually_bound_far (d : ℂ) (R : ℝ) : ∀ᶠ p in far d, R < (p * d).re :=
  tendsto_comap.eventually (eventually_gt_atTop R)

namespace Minor

@[expose] def pull (d : ℂ) (F : ℂ → ℂ) (v : ℝ) : ℂ :=
  d * F (d * (v : ℂ))

@[expose] def value (a : Minor) (d p : ℂ) : ℂ :=
  a.atom + complexLaplace (pull d a.density) (p * d)

@[expose] def const (c : ℂ) : Minor :=
  ⟨c, fun _ => 0⟩

@[expose] def plus (a b : Minor) : Minor :=
  ⟨a.atom + b.atom, fun z => a.density z + b.density z⟩

@[expose] def times (a b : Minor) : Minor :=
  ⟨a.atom * b.atom, fun z => a.atom * b.density z + b.atom * a.density z +
    complexConvolution a.density b.density z⟩

/-- Derivative kernel: `d/du (∫ e^{-ξ u} F(ξ) dξ) = ∫ e^{-ξ u} (-ξ F(ξ)) dξ`. -/
@[expose] def jet (a : Minor) : Minor :=
  ⟨0, fun z => -z * a.density z⟩

@[expose] def Good (a : Minor) (U : Set ℂ) (d : ℂ) : Prop :=
  AnalyticOnNhd ℂ a.density U ∧ ExpType (pull d a.density)

@[expose] def toSeries (a : Minor) : PowerSeries ℂ :=
  PowerSeries.mk fun n => match n with
    | 0 => a.atom
    | k + 1 => iteratedDeriv k a.density 0

lemma pull_plus (a b : Minor) (d : ℂ) :
    pull d (plus a b).density = fun v => pull d a.density v + pull d b.density v := by
  funext v; simp [pull, plus, mul_add]

lemma pull_conv (d : ℂ) (F G : ℂ → ℂ) :
    pull d (complexConvolution F G) = borelProduct (pull d F) (pull d G) := by
  funext v
  unfold pull
  rw [← complexConvolution_real (fun z => d * F (d * z)) (fun z => d * G (d * z)) v]
  unfold complexConvolution
  have eqn (t : ℝ) : d * F (d * ((t : ℂ) * (v : ℂ))) * (d * G (d * (((1 - t : ℝ) : ℂ) * (v : ℂ)))) =
      (d * d) * (F ((t : ℂ) * (d * (v : ℂ))) * G (((1 - t : ℝ) : ℂ) * (d * (v : ℂ)))) := by
    rw [mul_left_comm d (t : ℂ), mul_left_comm d ((1 - t : ℝ) : ℂ)]; ring
  simp only [eqn, integral_const_mul]; ring

lemma pull_times (a b : Minor) (d : ℂ) :
    pull d (times a b).density = fun v => a.atom * pull d b.density v +
      b.atom * pull d a.density v + borelProduct (pull d a.density) (pull d b.density) v := by
  rw [← pull_conv]; funext v; simp only [pull, times]; ring

lemma pull_jet (a : Minor) (d : ℂ) :
    pull d a.jet.density = fun v : ℝ => -d * ((v : ℂ) * pull d a.density v) := by
  funext v; simp only [pull, jet]; ring

lemma Good.const {U d} (c : ℂ) : (Minor.const c).Good U d :=
  ⟨analyticOnNhd_const, by change ExpType (fun _ => d * 0); simp [ExpType.zero]⟩

lemma Good.plus {a b : Minor} {U d} (ha : a.Good U d) (hb : b.Good U d) :
    (a.plus b).Good U d :=
  ⟨ha.1.add hb.1, by rw [pull_plus]; exact ha.2.add hb.2⟩

lemma Good.times {a b : Minor} {U d} (hU : Domain U) (ha : a.Good U d) (hb : b.Good U d) :
    (a.times b).Good U d := by
  refine ⟨((analyticOnNhd_const.mul hb.1).add (analyticOnNhd_const.mul ha.1)).add
    (complexConvolution_analytic hU.isOpen hU.star ha.1 hb.1), ?_⟩
  rw [pull_times]
  exact ((hb.2.scale _).add (ha.2.scale _)).add (ha.2.convolution hb.2)

lemma Good.jet {a : Minor} {U d} (ha : a.Good U d) : a.jet.Good U d :=
  ⟨analyticOnNhd_id.neg.mul ha.1, by rw [pull_jet]; exact ha.2.times_u.scale (-d)⟩

lemma pull_cont {a : Minor} {U d} (ray : ContainsRay U d) (ha : a.Good U d) :
    ContinuousOn (pull d a.density) (Ioi 0) :=
  continuousOn_const.mul (ha.1.continuousOn.comp
    (by fun_prop : Continuous (fun v : ℝ => d * (v : ℂ))).continuousOn fun v hv => ray v hv.le)

lemma Good.integrable {a : Minor} {U d} (ray : ContainsRay U d) (ha : a.Good U d) :
    ∀ᶠ p in far d, IntegrableOn (damped (p * d) (pull d a.density)) (Ioi 0) := by
  obtain ⟨_, D, _, _, hg⟩ := ha.2
  filter_upwards [eventually_bound_far d D] with p hp
  exact damped_integrable (pull_cont ray ha) hg hp

private lemma lap_add {F G : ℝ → ℂ} {p : ℂ}
    (hf : IntegrableOn (damped p F) (Ioi 0)) (hg : IntegrableOn (damped p G) (Ioi 0)) :
    complexLaplace (fun u => F u + G u) p = complexLaplace F p + complexLaplace G p := by
  simpa only [complexLaplace, damped, mul_add] using! integral_add hf hg

private lemma lap_scale (F : ℝ → ℂ) (p c : ℂ) :
    complexLaplace (fun u => c * F u) p = c * complexLaplace F p := by
  simp only [complexLaplace, damped, mul_left_comm _ c, integral_const_mul]

lemma good_const_value (c d p : ℂ) : (Minor.const c).value d p = c := by
  simp [value, const, pull, complexLaplace, damped]

lemma good_plus_value {a b : Minor} {U d} (ray : ContainsRay U d)
    (ha : a.Good U d) (hb : b.Good U d) :
    ∀ᶠ p in far d, (a.plus b).value d p = a.value d p + b.value d p := by
  filter_upwards [ha.integrable ray, hb.integrable ray] with p hp hq
  unfold value
  rw [pull_plus, lap_add hp hq]
  change a.atom + b.atom + _ = _
  ring

lemma good_times_value {a b : Minor} {U d} (ray : ContainsRay U d)
    (hU : Domain U) (ha : a.Good U d) (hb : b.Good U d) :
    ∀ᶠ p in far d, (a.times b).value d p = a.value d p * b.value d p := by
  let l : Minor := ⟨0, fun z => a.atom * b.density z⟩
  let r : Minor := ⟨0, fun z => b.atom * a.density z⟩
  let k : Minor := ⟨0, complexConvolution a.density b.density⟩
  have eqL : pull d l.density = fun v => a.atom * pull d b.density v := by funext v; simp [l, pull]; ring
  have eqR : pull d r.density = fun v => b.atom * pull d a.density v := by funext v; simp [r, pull]; ring
  have hl : l.Good U d := ⟨analyticOnNhd_const.mul hb.1, by rw [eqL]; exact hb.2.scale _⟩
  have hr : r.Good U d := ⟨analyticOnNhd_const.mul ha.1, by rw [eqR]; exact ha.2.scale _⟩
  have hk : k.Good U d := ⟨complexConvolution_analytic hU.isOpen hU.star ha.1 hb.1, by
    change ExpType (pull d (complexConvolution _ _))
    rw [pull_conv]
    exact ha.2.convolution hb.2⟩
  filter_upwards [good_plus_value ray (hl.plus hr) hk, good_plus_value ray hl hr,
    ha.integrable ray, hb.integrable ray] with p hsum hparts hi hj
  have e : (a.times b).value d p = a.atom * b.atom + ((l.plus r).plus k).value d p := by
    simp [value, times, plus, l, r, k]
  rw [e, hsum, hparts]
  simp only [value, eqL, eqR, lap_scale, k, pull_conv, complexLaplace_product hi hj, l, r]
  ring

lemma good_jet_derivative {a : Minor} {U d} (ray : ContainsRay U d) (ha : a.Good U d) :
    ∀ᶠ p in far d, HasDerivAt (a.value d) (a.jet.value d p) p := by
  obtain ⟨_, D, _, _, hg⟩ := ha.2
  filter_upwards [eventually_bound_far d (D + 1)] with p hp
  have h := ((complexLaplace_derivative (pull_cont ray ha) hg hp).comp p
    ((hasDerivAt_id p).mul_const d)).const_add a.atom
  unfold value
  rw [pull_jet, lap_scale]
  simpa only [jet, zero_add, mul_comm d, Function.comp_def, id_eq, one_mul, mul_neg, neg_mul] using! h

lemma toSeries_const (c : ℂ) : (Minor.const c).toSeries = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp [toSeries, const]
  | succ k => simp [toSeries, const]

lemma toSeries_plus {a b : Minor} (ha : AnalyticAt ℂ a.density 0) (hb : AnalyticAt ℂ b.density 0) :
    (a.plus b).toSeries = a.toSeries + b.toSeries := by
  ext n
  cases n with
  | zero => simp [toSeries, plus]
  | succ k =>
    simp only [toSeries, plus, map_add, PowerSeries.coeff_mk]
    exact iteratedDeriv_fun_add ha.contDiffAt hb.contDiffAt

lemma toSeries_jet {a : Minor} (ha : AnalyticAt ℂ a.density 0) :
    a.jet.toSeries = d_u a.toSeries := by
  ext n
  cases n with
  | zero =>
    simp [toSeries, jet, d_u]
  | succ k =>
    cases k with
    | zero =>
      simp [toSeries, jet, d_u, sq, mul_assoc]
    | succ m =>
      have hl : iteratedDeriv (m + 1) (fun z : ℂ => -z * a.density z) 0 =
          -((m + 1 : ℂ) * iteratedDeriv m a.density 0) := by
        have hmul := iteratedDeriv_fun_mul (n := m + 1) (x := (0 : ℂ))
          (analyticAt_id.neg.contDiffAt) ha.contDiffAt
        change iteratedDeriv (m + 1) (fun z : ℂ => -z * a.density z) 0 = _ at hmul
        rw [hmul]
        have hterm : ∀ i ∈ Finset.range (m + 2),
            ((m + 1).choose i : ℂ) * iteratedDeriv i (-id) 0 *
              iteratedDeriv (m + 1 - i) a.density 0 =
              if i = 1 then -((m + 1 : ℂ) * iteratedDeriv m a.density 0) else 0 := by
          intro i _
          have hid : iteratedDeriv i (-id) (0 : ℂ) = if i = 1 then -1 else 0 := by
            have hneg : iteratedDeriv i (-id) 0 = -iteratedDeriv i id (0 : ℂ) := by
              rw [Pi.neg_def, iteratedDeriv_fun_neg]
            rw [hneg, iteratedDeriv_id]
            split_ifs with h0 h1 <;> simp_all
          rw [hid]
          split_ifs with h1
          · subst h1; simp [Nat.choose_one_right]; ring
          · simp
        rw [Finset.sum_congr rfl hterm]
        simp
      have hr : PowerSeries.coeff (m + 2) (d_u a.toSeries) =
          -((m + 1 : ℂ) * iteratedDeriv m a.density 0) := by
        rw [d_u, map_neg, show (m + 2 : ℕ) = 2 + m by omega,
          PowerSeries.coeff_X_pow_mul']
        simp [PowerSeries.coeff_derivative, toSeries]
        ring
      simp only [toSeries, jet, PowerSeries.coeff_mk]
      exact hl.trans hr.symm

private lemma beta_nat_integral (i j : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ j =
      ((i.factorial * j.factorial : ℕ) : ℝ) / ((i + j + 1).factorial : ℝ) := by
  induction i generalizing j with
  | zero =>
    simp only [pow_zero, one_mul]
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => -((1 - x) ^ (j + 1) / ((j : ℝ) + 1))) ((1 - t) ^ j) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      have h2 := (h1.pow (j + 1)).div_const ((j : ℝ) + 1) |>.neg
      convert h2 using 1
      have hne : (j : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp [hne]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous (fun t : ℝ => (1 - t) ^ j)).intervalIntegrable 0 1)]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero j), zero_div, neg_zero, sub_zero, zero_sub,
      neg_neg, one_pow]
    rw [zero_add, Nat.factorial_zero, one_mul, Nat.factorial_succ j]
    push_cast
    have hne : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hne2 : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hne, hne2]
  | succ i ih =>
    let f1 : ℝ → ℝ := fun t => t ^ i * (1 - t) ^ (j + 1)
    let f2 : ℝ → ℝ := fun t => t ^ (i + 1) * (1 - t) ^ j
    have hc1 : Continuous f1 := by fun_prop
    have hc2 : Continuous f2 := by fun_prop
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => x ^ (i + 1) * (1 - x) ^ (j + 1))
          ((i + 1 : ℝ) * f1 t - (j + 1 : ℝ) * f2 t) t := by
      intro t _
      have ha : HasDerivAt (fun x : ℝ => x ^ (i + 1)) ((i + 1 : ℝ) * t ^ i) t := by
        simpa using hasDerivAt_pow (i + 1) t
      have hb : HasDerivAt (fun x : ℝ => (1 - x) ^ (j + 1))
          (-((j + 1 : ℝ) * (1 - t) ^ j)) t := by
        have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
        convert hsub.pow (j + 1) using 1
        push_cast; ring
      convert ha.mul hb using 1
      dsimp only [f1, f2]; ring
    have hint0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (((continuous_const.mul hc1).sub (continuous_const.mul hc2)).intervalIntegrable 0 1)
    simp only [one_pow, sub_self, zero_pow (Nat.succ_ne_zero _), mul_zero, zero_mul, sub_zero] at hint0
    have hint_sub : ∫ y in (0 : ℝ)..1, ((i + 1 : ℝ) * f1 y - (j + 1 : ℝ) * f2 y) =
        (i + 1 : ℝ) * (∫ y in (0 : ℝ)..1, f1 y) - (j + 1 : ℝ) * (∫ y in (0 : ℝ)..1, f2 y) := by
      have h1 : IntervalIntegrable (fun y : ℝ => (i + 1 : ℝ) * f1 y) volume 0 1 :=
        (continuous_const.mul hc1).intervalIntegrable 0 1
      have h2 : IntervalIntegrable (fun y : ℝ => (j + 1 : ℝ) * f2 y) volume 0 1 :=
        (continuous_const.mul hc2).intervalIntegrable 0 1
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub h1 h2]
    rw [hint_sub] at hint0
    have hint2 : ∫ t in (0 : ℝ)..1, f2 t = ((i + 1 : ℝ) / ((j : ℝ) + 1)) * ∫ t in (0 : ℝ)..1, f1 t := by
      have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hj1]
      linear_combination -hint0
    rw [show (fun t : ℝ => t ^ (i + 1) * (1 - t) ^ j) = f2 from rfl, hint2, ih (j + 1)]
    rw [show i + (j + 1) + 1 = i + 1 + j + 1 by omega,
      Nat.factorial_succ i, Nat.factorial_succ j]
    push_cast
    have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have hfac : ((i + 1 + j + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp [hj1, hfac]

private lemma iteratedDeriv_eq_zero_of_isBigO_pow {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    {m : ℕ} (hO : ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ ≤ C * ‖z‖ ^ (m + 1))
    {n : ℕ} (hn : n ≤ m) : iteratedDeriv n H 0 = 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain ⟨Q, hQa, hQeq⟩ := hH.exists_eventuallyEq_sum_add_pow_mul (n + 1)
    obtain ⟨C, hC⟩ := hO
    have h_zero : ∀ i ∈ Finset.range (n + 1),
        (fun z : ℂ => (z ^ i / (i.factorial : ℂ)) * iteratedDeriv i H 0) =
          fun z => if i = n then (z ^ n / (n.factorial : ℂ)) * iteratedDeriv n H 0 else 0 := by
      intro i hi
      funext z
      rw [Finset.mem_range] at hi
      by_cases hin : i = n
      · subst hin; simp
      · have hilt : i < n := by omega
        have hz0 := ih i hilt (hilt.le.trans hn)
        simp [hin, hz0]
    have hsim : ∀ᶠ z in 𝓝 (0 : ℂ),
        H z = (z ^ n / (n.factorial : ℂ)) * iteratedDeriv n H 0 + z ^ (n + 1) * Q z := by
      filter_upwards [hQeq] with z hz
      rw [hz]
      congr 1
      trans ∑ i ∈ Finset.range (n + 1),
          (if i = n then (z ^ n / (n.factorial : ℂ)) * iteratedDeriv n H 0 else 0)
      · refine Finset.sum_congr rfl fun i hi => ?_
        have := congrFun (h_zero i hi) z
        simpa only [smul_eq_mul] using this
      · simp
    have ht_zero : Tendsto ((↑) : ℝ → ℂ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h_div : Tendsto (fun t : ℝ => H (t : ℂ) / (t : ℂ) ^ n) (𝓝[>] (0 : ℝ))
        (𝓝 (iteratedDeriv n H 0 / (n.factorial : ℂ))) := by
      have h_rhs : Tendsto (fun t : ℝ =>
          iteratedDeriv n H 0 / (n.factorial : ℂ) + (t : ℂ) * Q (t : ℂ)) (𝓝[>] (0 : ℝ))
          (𝓝 (iteratedDeriv n H 0 / (n.factorial : ℂ))) := by
        have hQlim : Tendsto (fun t : ℝ => (t : ℂ) * Q (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          simpa using ht_zero.mul (hQa.continuousAt.tendsto.comp ht_zero)
        simpa using tendsto_const_nhds.add hQlim
      refine h_rhs.congr' ?_
      filter_upwards [self_mem_nhdsWithin, ht_zero.eventually hsim] with t ht hHz
      have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      rw [hHz, pow_succ]
      field_simp [htne]
    have h_norm0 : Tendsto (fun t : ℝ => ‖H (t : ℂ) / (t : ℂ) ^ n‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t : ℝ => max C 0 * t) ?_ ?_
      · have hIoo : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 :=
          inter_mem_nhdsWithin _ (Iio_mem_nhds one_pos)
        filter_upwards [hIoo, ht_zero.eventually hC] with t ht hCt
        have htle1 : t ^ (m + 1 - n) ≤ t := by
          have hm1 : 1 ≤ m + 1 - n := by omega
          calc t ^ (m + 1 - n) ≤ t ^ 1 := pow_le_pow_of_le_one ht.1.le ht.2.le hm1
            _ = t := pow_one t
        rw [norm_norm, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        have hnorm_z : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht.1]
        rw [hnorm_z] at hCt
        rw [div_le_iff₀ (pow_pos ht.1 n)]
        calc ‖H (t : ℂ)‖ ≤ C * t ^ (m + 1) := hCt
          _ ≤ max C 0 * t ^ (m + 1) := mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg ht.1.le _)
          _ = max C 0 * (t ^ (m + 1 - n) * t ^ n) := by
            rw [← pow_add, show m + 1 - n + n = m + 1 by omega]
          _ ≤ max C 0 * (t * t ^ n) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htle1 (pow_nonneg ht.1.le _))
              (le_max_right C 0)
          _ = max C 0 * t * t ^ n := by ring
      · simpa using (tendsto_const_nhds (x := max C 0)).mul
          ((continuous_id.continuousAt (x := (0 : ℝ))).tendsto.mono_left
            (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    have h_norm_eq : Tendsto (fun t : ℝ => ‖H (t : ℂ) / (t : ℂ) ^ n‖) (𝓝[>] (0 : ℝ))
        (𝓝 ‖iteratedDeriv n H 0 / (n.factorial : ℂ)‖) := h_div.norm
    have h0' : ‖iteratedDeriv n H 0 / (n.factorial : ℂ)‖ = 0 :=
      tendsto_nhds_unique h_norm_eq h_norm0
    rw [norm_eq_zero, div_eq_zero_iff] at h0'
    exact h0'.resolve_right (by exact_mod_cast Nat.factorial_ne_zero n)

private lemma analyticAt_ball_cont_bound {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) :
    ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ContinuousOn H (Metric.ball 0 δ) ∧
      ∀ w ∈ Metric.ball (0 : ℂ) δ, ‖H w‖ ≤ K := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp
    (hH.eventually_analyticAt.and (hH.continuousAt.norm.eventually
      (gt_mem_nhds (by simp : ‖H 0‖ < ‖H 0‖ + 1))))
  exact ⟨δ, hδ, ‖H 0‖ + 1, by positivity,
    fun w hw => (h (Metric.mem_ball.mp hw)).1.continuousAt.continuousWithinAt,
    fun w hw => (h (Metric.mem_ball.mp hw)).2.le⟩

lemma iteratedDeriv_complexConvolution_zero {F G : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (m : ℕ) :
    iteratedDeriv m (complexConvolution F G) 0 =
      if m = 0 then 0 else
        ∑ ij ∈ Finset.antidiagonal (m - 1), iteratedDeriv ij.1 F 0 * iteratedDeriv ij.2 G 0 := by
  by_cases hm0 : m = 0
  · subst hm0; simp [complexConvolution]
  · simp only [hm0, ite_false]
    obtain ⟨r₁, hr₁, hFball⟩ := Metric.eventually_nhds_iff.mp hF.eventually_analyticAt
    obtain ⟨r₂, hr₂, hGball⟩ := Metric.eventually_nhds_iff.mp hG.eventually_analyticAt
    let r : ℝ := min r₁ r₂
    have hr : 0 < r := lt_min hr₁ hr₂
    have hF_on : AnalyticOnNhd ℂ F (Metric.ball 0 r) := fun z hz =>
      hFball (by simpa [Metric.mem_ball] using (Metric.mem_ball.mp hz).trans_le (min_le_left _ _))
    have hG_on : AnalyticOnNhd ℂ G (Metric.ball 0 r) := fun z hz =>
      hGball (by simpa [Metric.mem_ball] using (Metric.mem_ball.mp hz).trans_le (min_le_right _ _))
    have star_ball : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ t ∈ Icc (0 : ℝ) 1,
        (t : ℂ) * z ∈ Metric.ball (0 : ℂ) r := by
      intro z hz t ht
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
    have hconv_an : AnalyticAt ℂ (complexConvolution F G) 0 :=
      (complexConvolution_analytic Metric.isOpen_ball star_ball hF_on hG_on) 0 (Metric.mem_ball_self hr)
    obtain ⟨RF, hRFa, hRFeq⟩ := hF.exists_eq_sum_add_pow_mul m
    obtain ⟨RG, hRGa, hRGeq⟩ := hG.exists_eq_sum_add_pow_mul m
    let PF : ℂ → ℂ := fun z => ∑ i ∈ Finset.range m, (z ^ i / (i.factorial : ℂ)) * iteratedDeriv i F 0
    let PG : ℂ → ℂ := fun z => ∑ j ∈ Finset.range m, (z ^ j / (j.factorial : ℂ)) * iteratedDeriv j G 0
    let P : ℂ → ℂ := fun z => ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (iteratedDeriv i F 0 * iteratedDeriv j G 0 / ((i + j + 1).factorial : ℂ)) * z ^ (i + j + 1)
    have hP_an : AnalyticAt ℂ P 0 := by fun_prop
    have hH_an : AnalyticAt ℂ (fun z => complexConvolution F G z - P z) 0 := hconv_an.sub hP_an
    have hPF_an : AnalyticAt ℂ PF 0 := by fun_prop
    obtain ⟨δ₁, hδ₁, K_RF, hKRF, hRF_cont, hRF_bdd⟩ := analyticAt_ball_cont_bound hRFa
    obtain ⟨δ₂, hδ₂, K_RG, hKRG, hRG_cont, hRG_bdd⟩ := analyticAt_ball_cont_bound hRGa
    obtain ⟨δ₃, hδ₃, K_G, hKG, hG_cont, hG_bdd⟩ := analyticAt_ball_cont_bound hG
    obtain ⟨δ₄, hδ₄, K_PF, hKPF, hPF_cont, hPF_bdd⟩ := analyticAt_ball_cont_bound hPF_an
    let δ : ℝ := min (min δ₁ δ₂) (min δ₃ δ₄)
    have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄)
    let C : ℝ := K_RF * K_G + K_PF * K_RG
    have h_bigO : ∃ C₀ : ℝ, ∀ᶠ z in 𝓝 (0 : ℂ), ‖complexConvolution F G z - P z‖ ≤ C₀ * ‖z‖ ^ (m + 1) := by
      refine ⟨C, ?_⟩
      filter_upwards [Metric.ball_mem_nhds 0 hδ] with z hz
      have hsub : ∀ {w : ℂ} {d : ℝ}, w ∈ Metric.ball (0 : ℂ) δ → δ ≤ d → w ∈ Metric.ball (0 : ℂ) d :=
        fun hw hd => (Metric.mem_ball.mp hw).trans_le hd
      have hscale1 : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ Metric.ball (0 : ℂ) δ := by
        intro t ht
        rw [Metric.mem_ball, dist_zero_right] at hz ⊢
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
      have hscale2 : ∀ t ∈ Icc (0 : ℝ) 1, ((1 - t : ℝ) : ℂ) * z ∈ Metric.ball (0 : ℂ) δ := by
        intro t ht
        rw [Metric.mem_ball, dist_zero_right] at hz ⊢
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
        exact (mul_le_of_le_one_left (norm_nonneg z) (sub_le_self _ ht.1)).trans_lt hz
      let remIntegrand (t : ℝ) : ℂ :=
        ((t : ℂ) * z) ^ m * RF ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z) +
          PF ((t : ℂ) * z) * ((((1 - t : ℝ) : ℂ) * z) ^ m * RG (((1 - t : ℝ) : ℂ) * z))
      have hcont_rem_Icc : ContinuousOn remIntegrand (Icc 0 1) := by
        have hm1 : MapsTo (fun t : ℝ => (t : ℂ) * z) (Icc 0 1) (Metric.ball 0 δ₁) := fun t ht =>
          hsub (hscale1 t ht) ((min_le_left _ _).trans (min_le_left _ _))
        have hm2 : MapsTo (fun t : ℝ => ((1 - t : ℝ) : ℂ) * z) (Icc 0 1) (Metric.ball 0 δ₂) := fun t ht =>
          hsub (hscale2 t ht) ((min_le_left _ _).trans (min_le_right _ _))
        have hm3 : MapsTo (fun t : ℝ => ((1 - t : ℝ) : ℂ) * z) (Icc 0 1) (Metric.ball 0 δ₃) := fun t ht =>
          hsub (hscale2 t ht) ((min_le_right _ _).trans (min_le_left _ _))
        have hm4 : MapsTo (fun t : ℝ => (t : ℂ) * z) (Icc 0 1) (Metric.ball 0 δ₄) := fun t ht =>
          hsub (hscale1 t ht) ((min_le_right _ _).trans (min_le_right _ _))
        have hc1 : Continuous (fun t : ℝ => (t : ℂ) * z) := by fun_prop
        have hc2 : Continuous (fun t : ℝ => ((1 - t : ℝ) : ℂ) * z) := by fun_prop
        refine ((hc1.continuousOn.pow m).mul (hRF_cont.comp hc1.continuousOn hm1)).mul
            (hG_cont.comp hc2.continuousOn hm3) |>.add ?_
        exact (hPF_cont.comp hc1.continuousOn hm4).mul
          ((hc2.continuousOn.pow m).mul (hRG_cont.comp hc2.continuousOn hm2))
      have hconv_P : complexConvolution F G z - P z = z * ∫ t : ℝ in Ioc 0 1, remIntegrand t := by
        have hint_poly : z * ∫ t : ℝ in Ioc 0 1,
            PF ((t : ℂ) * z) * PG (((1 - t : ℝ) : ℂ) * z) = P z := by
          have hexp : (fun t : ℝ => PF ((t : ℂ) * z) * PG (((1 - t : ℝ) : ℂ) * z)) =
              fun t : ℝ => ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
                (((iteratedDeriv i F 0 / (i.factorial : ℂ)) *
                  (iteratedDeriv j G 0 / (j.factorial : ℂ)) * z ^ (i + j)) *
                  ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j)) := by
            funext t
            dsimp only [PF, PG]
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_pow, mul_pow, pow_add]
            ring
          rw [hexp]
          have hint_term : ∀ i j : ℕ,
              ∫ t : ℝ in Ioc 0 1,
                (((iteratedDeriv i F 0 / (i.factorial : ℂ)) *
                  (iteratedDeriv j G 0 / (j.factorial : ℂ)) * z ^ (i + j)) *
                  ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j)) =
                (iteratedDeriv i F 0 * iteratedDeriv j G 0 / ((i + j + 1).factorial : ℂ)) * z ^ (i + j) := by
            intro i j
            rw [integral_const_mul]
            have hreal : ∫ t : ℝ in Ioc 0 1, ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j) =
                ((∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ j : ℝ) : ℂ) := by
              rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
              have hcast : (fun t : ℝ => ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j)) =
                  fun t : ℝ => ((t ^ i * (1 - t) ^ j : ℝ) : ℂ) := by
                funext t; push_cast; rfl
              rw [hcast, intervalIntegral.integral_ofReal]
            rw [hreal, beta_nat_integral i j]
            push_cast
            have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
            have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
            have hij : ((i + j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
            field_simp [hi, hj, hij]
          have hi_term : ∀ i ∈ Finset.range m, IntegrableOn (fun t : ℝ => ∑ j ∈ Finset.range m,
              ((iteratedDeriv i F 0 / (i.factorial : ℂ)) *
                (iteratedDeriv j G 0 / (j.factorial : ℂ)) * z ^ (i + j)) *
                ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j)) (Ioc 0 1) := by
            intro i _
            have hcont : Continuous (fun t : ℝ => ∑ j ∈ Finset.range m,
                ((iteratedDeriv i F 0 / (i.factorial : ℂ)) *
                  (iteratedDeriv j G 0 / (j.factorial : ℂ)) * z ^ (i + j)) *
                  ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j)) := by fun_prop
            exact hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
          rw [integral_finsetSum (Finset.range m) hi_term]
          have h_inner : ∀ i ∈ Finset.range m,
              ∫ t : ℝ in Ioc 0 1, ∑ j ∈ Finset.range m,
                ((iteratedDeriv i F 0 / (i.factorial : ℂ)) *
                  (iteratedDeriv j G 0 / (j.factorial : ℂ)) * z ^ (i + j)) *
                  ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j) =
                ∑ j ∈ Finset.range m,
                  (iteratedDeriv i F 0 * iteratedDeriv j G 0 / ((i + j + 1).factorial : ℂ)) * z ^ (i + j) := by
            intro i _
            have hi2 : ∀ j ∈ Finset.range m, IntegrableOn (fun t : ℝ =>
                ((iteratedDeriv i F 0 / (i.factorial : ℂ)) *
                  (iteratedDeriv j G 0 / (j.factorial : ℂ)) * z ^ (i + j)) *
                  ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j)) (Ioc 0 1) := by
              intro j _
              have hc : Continuous (fun t : ℝ =>
                  ((iteratedDeriv i F 0 / (i.factorial : ℂ)) *
                    (iteratedDeriv j G 0 / (j.factorial : ℂ)) * z ^ (i + j)) *
                    ((t : ℂ) ^ i * ((1 - t : ℝ) : ℂ) ^ j)) := by fun_prop
              exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
            rw [integral_finsetSum (Finset.range m) hi2]
            exact Finset.sum_congr rfl fun j _ => hint_term i j
          rw [Finset.sum_congr rfl h_inner, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [pow_succ']
          ring
        have hsplit : (fun t : ℝ => F ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z)) =
            fun t : ℝ =>
              (PF ((t : ℂ) * z) * PG (((1 - t : ℝ) : ℂ) * z)) + remIntegrand t := by
          funext t
          have h1 := hRFeq ((t : ℂ) * z)
          have h2 := hRGeq (((1 - t : ℝ) : ℂ) * z)
          simp only [smul_eq_mul] at h1 h2
          change F ((t : ℂ) * z) = PF ((t : ℂ) * z) + ((t : ℂ) * z) ^ m * RF ((t : ℂ) * z) at h1
          change G (((1 - t : ℝ) : ℂ) * z) = PG (((1 - t : ℝ) : ℂ) * z) +
            (((1 - t : ℝ) : ℂ) * z) ^ m * RG (((1 - t : ℝ) : ℂ) * z) at h2
          calc F ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z)
              = (PF ((t : ℂ) * z) + ((t : ℂ) * z) ^ m * RF ((t : ℂ) * z)) *
                  G (((1 - t : ℝ) : ℂ) * z) := by rw [h1]
            _ = PF ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z) +
                  ((t : ℂ) * z) ^ m * RF ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z) := by ring
            _ = PF ((t : ℂ) * z) * (PG (((1 - t : ℝ) : ℂ) * z) +
                  (((1 - t : ℝ) : ℂ) * z) ^ m * RG (((1 - t : ℝ) : ℂ) * z)) +
                  ((t : ℂ) * z) ^ m * RF ((t : ℂ) * z) * G (((1 - t : ℝ) : ℂ) * z) := by rw [h2]
            _ = PF ((t : ℂ) * z) * PG (((1 - t : ℝ) : ℂ) * z) + remIntegrand t := by
                  dsimp only [remIntegrand]; ring
        have hcont_poly : IntegrableOn (fun t : ℝ => PF ((t : ℂ) * z) * PG (((1 - t : ℝ) : ℂ) * z)) (Ioc 0 1) := by
          have hc : Continuous (fun t : ℝ => PF ((t : ℂ) * z) * PG (((1 - t : ℝ) : ℂ) * z)) := by fun_prop
          exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        have hcont_rem : IntegrableOn remIntegrand (Ioc 0 1) :=
          hcont_rem_Icc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        rw [complexConvolution, hsplit, integral_add hcont_poly hcont_rem, mul_add, hint_poly]
        ring
      have hbound_rem : ∀ t ∈ Ioc (0 : ℝ) 1, ‖remIntegrand t‖ ≤ C * ‖z‖ ^ m := by
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
        have hw1 := hRF_bdd _ (hsub (hscale1 t ht') ((min_le_left _ _).trans (min_le_left _ _)))
        have hw2 := hRG_bdd _ (hsub (hscale2 t ht') ((min_le_left _ _).trans (min_le_right _ _)))
        have hw3 := hG_bdd _ (hsub (hscale2 t ht') ((min_le_right _ _).trans (min_le_left _ _)))
        have hw4 := hPF_bdd _ (hsub (hscale1 t ht') ((min_le_right _ _).trans (min_le_right _ _)))
        have htz : ‖((t : ℂ) * z) ^ m‖ ≤ ‖z‖ ^ m := by
          rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
          exact pow_le_pow_left₀ (mul_nonneg ht'.1 (norm_nonneg z))
            (mul_le_of_le_one_left (norm_nonneg z) ht'.2) m
        have h1tz : ‖(((1 - t : ℝ) : ℂ) * z) ^ m‖ ≤ ‖z‖ ^ m := by
          rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'.2)]
          exact pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr ht'.2) (norm_nonneg z))
            (mul_le_of_le_one_left (norm_nonneg z) (sub_le_self _ ht'.1)) m
        dsimp only [remIntegrand]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        calc ‖((t : ℂ) * z) ^ m‖ * ‖RF ((t : ℂ) * z)‖ * ‖G (((1 - t : ℝ) : ℂ) * z)‖ +
              ‖PF ((t : ℂ) * z)‖ * (‖(((1 - t : ℝ) : ℂ) * z) ^ m‖ * ‖RG (((1 - t : ℝ) : ℂ) * z)‖)
            ≤ (‖z‖ ^ m * K_RF) * K_G + K_PF * (‖z‖ ^ m * K_RG) := by
              apply add_le_add
              · exact mul_le_mul (mul_le_mul htz hw1 (norm_nonneg _) (by positivity)) hw3
                  (norm_nonneg _) (by positivity)
              · exact mul_le_mul hw4 (mul_le_mul h1tz hw2 (norm_nonneg _) (by positivity))
                  (by positivity) hKPF
          _ = C * ‖z‖ ^ m := by dsimp only [C]; ring
      rw [hconv_P, norm_mul]
      have hint_norm : ‖∫ t : ℝ in Ioc 0 1, remIntegrand t‖ ≤ C * ‖z‖ ^ m := by
        rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
        have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
          (f := remIntegrand) (C := C * ‖z‖ ^ m) (fun t ht => by
            rw [uIoc_of_le (by norm_num)] at ht
            exact hbound_rem t ht)
        simpa using hle
      calc ‖z‖ * ‖∫ t : ℝ in Ioc 0 1, remIntegrand t‖
          ≤ ‖z‖ * (C * ‖z‖ ^ m) := mul_le_mul_of_nonneg_left hint_norm (norm_nonneg z)
        _ = C * ‖z‖ ^ (m + 1) := by rw [pow_succ']; ring
    have hH_zero : iteratedDeriv m (fun z => complexConvolution F G z - P z) 0 = 0 :=
      iteratedDeriv_eq_zero_of_isBigO_pow hH_an h_bigO le_rfl
    have hdiff_id : iteratedDeriv m (fun z => complexConvolution F G z - P z) 0 =
        iteratedDeriv m (complexConvolution F G) 0 - iteratedDeriv m P 0 :=
      iteratedDeriv_fun_sub hconv_an.contDiffAt hP_an.contDiffAt
    have hconv_eq_P : iteratedDeriv m (complexConvolution F G) 0 = iteratedDeriv m P 0 :=
      eq_of_sub_eq_zero (hdiff_id.symm.trans hH_zero)
    rw [hconv_eq_P]
    have hP_eval : iteratedDeriv m P 0 =
        ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          if i + j + 1 = m then iteratedDeriv i F 0 * iteratedDeriv j G 0 else 0 := by
      have hc_diff : ∀ i ∈ Finset.range m,
          ContDiffAt ℂ m (fun z : ℂ => ∑ j ∈ Finset.range m,
            (iteratedDeriv i F 0 * iteratedDeriv j G 0 / ((i + j + 1).factorial : ℂ)) * z ^ (i + j + 1)) 0 :=
        fun _ _ => (Finset.analyticAt_fun_sum _ fun _ _ =>
          analyticAt_const.mul (analyticAt_id.pow _)).contDiffAt
      have hsum1 := iteratedDeriv_fun_sum (I := Finset.range m) hc_diff
      simp only [P] at hsum1 ⊢
      rw [hsum1]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc2_diff : ∀ j ∈ Finset.range m,
          ContDiffAt ℂ m (fun z : ℂ =>
            (iteratedDeriv i F 0 * iteratedDeriv j G 0 / ((i + j + 1).factorial : ℂ)) * z ^ (i + j + 1)) 0 :=
        fun _ _ => (analyticAt_const.mul (analyticAt_id.pow _)).contDiffAt
      rw [iteratedDeriv_fun_sum (I := Finset.range m) hc2_diff]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      split_ifs with h1 h2
      · subst h1
        have hij : ((i + j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        field_simp [hij]
      · omega
      · omega
      · simp
    rw [hP_eval]
    have hm_succ : m = (m - 1) + 1 := by omega
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => iteratedDeriv i F 0 * iteratedDeriv j G 0),
      Nat.succ_eq_add_one, ← hm_succ]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hite : ∀ j : ℕ, (if i + j + 1 = m then iteratedDeriv i F 0 * iteratedDeriv j G 0 else 0) =
        if j = m - 1 - i then iteratedDeriv i F 0 * iteratedDeriv j G 0 else 0 := by
      intro j
      split_ifs with h1 h2
      · rfl
      · omega
      · omega
      · rfl
    simp_rw [hite]
    rw [Finset.sum_ite_eq']
    simp [show m - 1 - i ∈ Finset.range m by rw [Finset.mem_range]; omega]

lemma toSeries_times {a b : Minor} (ha : AnalyticAt ℂ a.density 0) (hb : AnalyticAt ℂ b.density 0) :
    (a.times b).toSeries = a.toSeries * b.toSeries := by
  ext n
  rw [PowerSeries.coeff_mul]
  cases n with
  | zero => simp [toSeries, times]
  | succ k =>
    conv_lhs => simp only [toSeries, times, PowerSeries.coeff_mk]
    have h_lin : ContDiffAt ℂ k (fun z : ℂ => a.atom * b.density z + b.atom * a.density z) 0 := by
      refine AnalyticAt.contDiffAt ?_
      exact (analyticAt_const.mul hb).add (analyticAt_const.mul ha)
    have h_conv : ContDiffAt ℂ k (complexConvolution a.density b.density) 0 := by
      obtain ⟨r₁, hr₁, hFball⟩ := Metric.eventually_nhds_iff.mp ha.eventually_analyticAt
      obtain ⟨r₂, hr₂, hGball⟩ := Metric.eventually_nhds_iff.mp hb.eventually_analyticAt
      let r : ℝ := min r₁ r₂
      have hr : 0 < r := lt_min hr₁ hr₂
      have ha_on : AnalyticOnNhd ℂ a.density (Metric.ball 0 r) := fun z hz =>
        hFball (by simpa [Metric.mem_ball] using (Metric.mem_ball.mp hz).trans_le (min_le_left _ _))
      have hb_on : AnalyticOnNhd ℂ b.density (Metric.ball 0 r) := fun z hz =>
        hGball (by simpa [Metric.mem_ball] using (Metric.mem_ball.mp hz).trans_le (min_le_right _ _))
      have star_ball : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ t ∈ Icc (0 : ℝ) 1,
          (t : ℂ) * z ∈ Metric.ball (0 : ℂ) r := fun z hz t ht => by
        rw [Metric.mem_ball, dist_zero_right] at hz ⊢
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
      exact (complexConvolution_analytic Metric.isOpen_ball star_ball ha_on hb_on 0
        (Metric.mem_ball_self hr)).contDiffAt
    have hadd1 := iteratedDeriv_fun_add h_lin h_conv
    have h_part1 : ContDiffAt ℂ k (fun z : ℂ => a.atom * b.density z) 0 :=
      (analyticAt_const.mul hb).contDiffAt
    have h_part2 : ContDiffAt ℂ k (fun z : ℂ => b.atom * a.density z) 0 :=
      (analyticAt_const.mul ha).contDiffAt
    have hadd2 := iteratedDeriv_fun_add h_part1 h_part2
    rw [hadd1, hadd2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_complexConvolution_zero ha hb k]
    cases k with
    | zero =>
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i a.toSeries * PowerSeries.coeff j b.toSeries)]
      simp [Finset.sum_range_succ, toSeries]; ring
    | succ m =>
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i a.toSeries * PowerSeries.coeff j b.toSeries)]
      have hdrop : ∑ i ∈ Finset.range (m + 2 + 1),
          PowerSeries.coeff i a.toSeries * PowerSeries.coeff (m + 2 - i) b.toSeries =
          PowerSeries.coeff 0 a.toSeries * PowerSeries.coeff (m + 2) b.toSeries +
            (∑ i ∈ Finset.range (m + 1),
              PowerSeries.coeff (i + 1) a.toSeries * PowerSeries.coeff (m + 1 - i) b.toSeries) +
            PowerSeries.coeff (m + 2) a.toSeries * PowerSeries.coeff 0 b.toSeries := by
        rw [Finset.sum_range_succ, add_right_comm, Finset.sum_range_succ']
        simp [Nat.succ_sub_succ]
        ring
      rw [hdrop, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => iteratedDeriv i a.density 0 * iteratedDeriv j b.density 0)]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
        toSeries, PowerSeries.coeff_mk]
      have hcongr : ∑ i ∈ Finset.range (m + 1),
          iteratedDeriv i a.density 0 *
            (match m + 1 - i with | 0 => b.atom | k + 1 => iteratedDeriv k b.density 0) =
          ∑ x ∈ Finset.range (m + 1), iteratedDeriv x a.density 0 * iteratedDeriv (m - x) b.density 0 := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        have heq : m + 1 - i = (m - i) + 1 := by omega
        rw [heq]
      rw [hcongr]
      change _ = (a.atom * iteratedDeriv (m + 1) b.density 0 +
          (∑ x ∈ Finset.range (m + 1), iteratedDeriv x a.density 0 * iteratedDeriv (m - x) b.density 0) +
          iteratedDeriv (m + 1) a.density 0 * b.atom)
      ring

lemma complexLaplace_monomial (k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k =
      (k.factorial : ℂ) / w ^ (k + 1) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hint_exp : ∀ n : ℕ, IntegrableOn (fun v : ℝ => Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ n) (Ioi 0) := by
    intro n
    have hcont : Continuous (fun v : ℝ => Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ n) := by fun_prop
    have hexp_bound : ∃ C ≥ 0, ∀ v : ℝ, 0 ≤ v →
        ‖Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ n‖ ≤ C * Real.exp (-(w.re / 2) * v) := by
      refine ⟨(n.factorial : ℝ) / (w.re / 2) ^ n, by positivity, fun v hv => ?_⟩
      rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
      have hre : (-w * (v : ℂ)).re = -w.re * v := by
        simp [Complex.mul_re]
      rw [hre]
      have hpow : ((w.re / 2) * v) ^ n / (n.factorial : ℝ) ≤ Real.exp ((w.re / 2) * v) :=
        Real.pow_div_factorial_le_exp _ (by positivity) n
      have hvn : v ^ n ≤ ((n.factorial : ℝ) / (w.re / 2) ^ n) * Real.exp ((w.re / 2) * v) := by
        have hw2 : (0 : ℝ) < (w.re / 2) ^ n := pow_pos (by linarith) n
        have hfac : (0 : ℝ) < n.factorial := by positivity
        rw [mul_pow, mul_comm ((w.re / 2) ^ n), div_le_iff₀ hfac] at hpow
        have hvn' : v ^ n * (w.re / 2) ^ n ≤ Real.exp (w.re / 2 * v) * n.factorial := hpow
        calc v ^ n ≤ (Real.exp (w.re / 2 * v) * n.factorial) / (w.re / 2) ^ n :=
              (le_div_iff₀ hw2).mpr (by linarith)
          _ = ((n.factorial : ℝ) / (w.re / 2) ^ n) * Real.exp ((w.re / 2) * v) := by ring
      calc Real.exp (-w.re * v) * v ^ n
          ≤ Real.exp (-w.re * v) * (((n.factorial : ℝ) / (w.re / 2) ^ n) * Real.exp ((w.re / 2) * v)) :=
            mul_le_mul_of_nonneg_left hvn (Real.exp_pos _).le
        _ = ((n.factorial : ℝ) / (w.re / 2) ^ n) * (Real.exp (-w.re * v) * Real.exp ((w.re / 2) * v)) := by ring
        _ = ((n.factorial : ℝ) / (w.re / 2) ^ n) * Real.exp (-(w.re / 2) * v) := by
          rw [← Real.exp_add]; congr 2; ring
    obtain ⟨C, hC, hb⟩ := hexp_bound
    refine ((integrableOn_exp_mul_Ioi (show -(w.re / 2) < 0 by linarith) 0).const_mul C).mono'
      hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    exact hb v hv.le
  induction k with
  | zero =>
    let F : ℝ → ℂ := fun v => -(w⁻¹) * Complex.exp (-w * (v : ℂ))
    have hderiv : ∀ v ∈ Ici (0 : ℝ), HasDerivAt F (Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ 0) v := by
      intro v _
      have h1 : HasDerivAt (fun x : ℝ => -w * (x : ℂ)) (-w) v := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (-w)
      convert (h1.cexp.const_mul (-w⁻¹)) using 1
      simp [pow_zero]
      field_simp [hw0]
    have hlim : Tendsto F atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun v : ℝ => ‖w⁻¹‖ * Real.exp (-w.re * v)) ?_ ?_
      · filter_upwards with v
        simp only [F]
        rw [norm_mul, norm_neg, Complex.norm_exp]
        have hre : (-w * (v : ℂ)).re = -w.re * v := by simp [Complex.mul_re]
        rw [hre]
      · have h0 : Tendsto (fun v : ℝ => Real.exp (-w.re * v)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hw))
        simpa using (tendsto_const_nhds (x := ‖w⁻¹‖)).mul h0
    have hint_eq := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hint_exp 0) hlim
    simpa [F, zero_sub, pow_one, Nat.factorial_zero] using hint_eq
  | succ k ih =>
    let G : ℝ → ℂ := fun v => -((v : ℂ) ^ (k + 1)) * Complex.exp (-w * (v : ℂ))
    have hderiv : ∀ v ∈ Ici (0 : ℝ), HasDerivAt G
        (w * (Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ (k + 1)) -
          (k + 1 : ℂ) * (Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k)) v := by
      intro v _
      have ha : HasDerivAt (fun x : ℝ => -((x : ℂ) ^ (k + 1))) (-((k + 1 : ℂ) * (v : ℂ) ^ k)) v := by
        have hp := (hasDerivAt_pow (k + 1) (v : ℂ)).comp_ofReal
        convert hp.neg using 1
        push_cast; ring
      have hb : HasDerivAt (fun x : ℝ => Complex.exp (-w * (x : ℂ)))
          (-w * Complex.exp (-w * (v : ℂ))) v := by
        have h1 : HasDerivAt (fun x : ℝ => -w * (x : ℂ)) (-w) v := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (-w)
        convert h1.cexp using 1; ring
      convert ha.mul hb using 1
      ring
    have hGlim : Tendsto G atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun v : ℝ => v ^ (k + 1) * Real.exp (-w.re * v)) ?_ ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
        simp only [G]
        rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv,
          Complex.norm_exp]
        have hre : (-w * (v : ℂ)).re = -w.re * v := by simp [Complex.mul_re]
        rw [hre]
      · convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k + 1 : ℕ) : ℝ) w.re hw using 1
        funext v
        rw [Real.rpow_natCast]
    have hint_diff : IntegrableOn (fun v : ℝ =>
        w * (Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ (k + 1)) -
          (k + 1 : ℂ) * (Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k)) (Ioi 0) :=
      ((hint_exp (k + 1)).const_mul w).sub ((hint_exp k).const_mul (k + 1 : ℂ))
    have hG_int := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_diff hGlim
    have hG0 : G 0 = 0 := by simp [G]
    rw [hG0, zero_sub, neg_zero] at hG_int
    have hsplit_int : ∫ v in Ioi (0 : ℝ),
        (w * (Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ (k + 1)) -
          (k + 1 : ℂ) * (Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k)) =
        w * (∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ (k + 1)) -
          (k + 1 : ℂ) * (∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k) := by
      have hw_i := (hint_exp (k + 1)).const_mul w
      have hk_i := (hint_exp k).const_mul (k + 1 : ℂ)
      rw [← integral_const_mul, ← integral_const_mul, ← integral_sub hw_i hk_i]
    rw [hsplit_int, sub_eq_zero] at hG_int
    have hk1 : ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ (k + 1) =
        ((k + 1 : ℂ) / w) * ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k := by
      calc ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ (k + 1)
          = w⁻¹ * (w * ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ (k + 1)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
        _ = w⁻¹ * ((k + 1 : ℂ) * ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k) := by
            rw [hG_int]
        _ = ((k + 1 : ℂ) / w) * ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * (v : ℂ) ^ k := by
            ring
    rw [hk1, ih, Nat.factorial_succ]
    push_cast
    rw [pow_succ']
    field_simp [hw0]
    ring

theorem value_asymptotic (a : Minor) {U : Set ℂ} {d : ℂ}
    (_hU : Domain U) (ray : ContainsRay U d) (ha : a.Good U d) (hd : 0 < d.re) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ u : ℝ in atTop,
      ‖a.value d (u : ℂ) - (a.atom + ∑ k ∈ Finset.range M,
        iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1)))‖ ≤ C / u ^ (M + 1) := by
  have h0_mem : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
  have ha0 : AnalyticAt ℂ a.density 0 := ha.1 0 h0_mem
  obtain ⟨R, hRa, hReq⟩ := ha0.exists_eq_sum_add_pow_mul M
  obtain ⟨δ_r, hδr_pos, K_R, hKR, _, hR_bdd⟩ := analyticAt_ball_cont_bound hRa
  obtain ⟨C_exp, D_exp, hCexp, hDexp, hexp⟩ := ha.2
  have hd_ne : d ≠ 0 := fun h => by simp [h] at hd
  have hdn_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  let δ : ℝ := δ_r / (2 * ‖d‖)
  have hδ : 0 < δ := by positivity
  let P_trunc (z : ℂ) : ℂ := ∑ k ∈ Finset.range M, (z ^ k / (k.factorial : ℂ)) * iteratedDeriv k a.density 0
  have h_poly_bound : ∃ C_poly : ℝ, 0 ≤ C_poly ∧ ∀ v : ℝ, 0 ≤ v →
      ‖pull d P_trunc v‖ ≤ C_poly * Real.exp (v) := by
    refine ⟨∑ k ∈ Finset.range M, ‖d‖ ^ (k + 1) * ‖iteratedDeriv k a.density 0‖,
      Finset.sum_nonneg (fun _ _ => by positivity), fun v hv => ?_⟩
    unfold pull P_trunc
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hv, Complex.norm_natCast, mul_pow]
    have hpow : v ^ k / (k.factorial : ℝ) ≤ Real.exp v :=
      Real.pow_div_factorial_le_exp v hv k
    calc ‖d‖ * (‖d‖ ^ k * v ^ k / (k.factorial : ℝ) * ‖iteratedDeriv k a.density 0‖)
        = (‖d‖ ^ (k + 1) * ‖iteratedDeriv k a.density 0‖) * (v ^ k / (k.factorial : ℝ)) := by
          rw [pow_succ']; ring
      _ ≤ (‖d‖ ^ (k + 1) * ‖iteratedDeriv k a.density 0‖) * Real.exp v :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  obtain ⟨C_poly, hCpoly, hP_exp⟩ := h_poly_bound
  let D₀ : ℝ := max D_exp 1
  have hD₀_ge_1 : 1 ≤ D₀ := le_max_right _ _
  let C_tail : ℝ := C_exp + C_poly
  have hCtail : 0 ≤ C_tail := by positivity
  let u₀ : ℝ := max 1 (4 * D₀ / d.re)
  let K₁ : ℝ := ‖d‖ ^ (M + 1) * K_R * (M.factorial : ℝ) / d.re ^ (M + 1)
  let K₂ : ℝ := C_tail * (4 / d.re) * (((M + 1).factorial : ℝ) / ((d.re * δ / 4) ^ (M + 1)))
  refine ⟨K₁ + K₂, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop u₀] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le (by positivity : 0 < u₀) hu.le
  have hu_ge_1 : 1 ≤ u := le_trans (le_max_left _ _) hu.le
  have hu_d_gt : 2 * D₀ < u * d.re := by
    have hu4 : 4 * D₀ / d.re < u := lt_of_le_of_lt (le_max_right _ _) hu
    have h4' : 4 * D₀ < u * d.re := (div_lt_iff₀ hd).mp hu4
    linarith
  have h_lap_poly : complexLaplace (pull d P_trunc) ((u : ℂ) * d) =
      ∑ k ∈ Finset.range M, iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
    unfold complexLaplace
    have heq_sum : (fun v : ℝ => damped ((u : ℂ) * d) (pull d P_trunc) v) =
        fun v : ℝ => ∑ k ∈ Finset.range M,
          ((d ^ (k + 1) / (k.factorial : ℂ) * iteratedDeriv k a.density 0) *
            (Complex.exp (-((u : ℂ) * d) * (v : ℂ)) * (v : ℂ) ^ k)) := by
      funext v
      simp only [damped, pull, P_trunc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, pow_succ']
      ring
    rw [heq_sum]
    have hi_term : ∀ k ∈ Finset.range M,
        IntegrableOn (fun v : ℝ =>
          (d ^ (k + 1) / (k.factorial : ℂ) * iteratedDeriv k a.density 0) *
            (Complex.exp (-((u : ℂ) * d) * (v : ℂ)) * (v : ℂ) ^ k)) (Ioi 0) := by
      intro k _
      refine Integrable.const_mul ?_ _
      refine ((integrableOn_exp_mul_Ioi (show -(u * d.re / 2) < 0 by linarith [mul_pos hu_pos hd]) 0).const_mul
        ((k.factorial : ℝ) / (u * d.re / 2) ^ k)).mono'
        ((by fun_prop : Continuous (fun v : ℝ =>
          Complex.exp (-((u : ℂ) * d) * (v : ℂ)) * (v : ℂ) ^ k)).aestronglyMeasurable.restrict) ?_
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
      change 0 < v at hv
      rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.le]
      have hre2 : (-((u : ℂ) * d) * (v : ℂ)).re = -(u * d.re) * v := by
        simp [Complex.mul_re]
      rw [hre2]
      have hpow : (u * d.re / 2 * v) ^ k / (k.factorial : ℝ) ≤ Real.exp (u * d.re / 2 * v) :=
        Real.pow_div_factorial_le_exp _ (by positivity) k
      have hvk : v ^ k ≤ ((k.factorial : ℝ) / (u * d.re / 2) ^ k) * Real.exp (u * d.re / 2 * v) := by
        have h1 : 0 < (u * d.re / 2) ^ k := pow_pos (by positivity) k
        have h2 : 0 < (k.factorial : ℝ) := by positivity
        rw [mul_pow, div_le_iff₀ h2] at hpow
        calc v ^ k ≤ (Real.exp (u * d.re / 2 * v) * k.factorial) / (u * d.re / 2) ^ k :=
              (le_div_iff₀ h1).mpr (by linarith)
          _ = ((k.factorial : ℝ) / (u * d.re / 2) ^ k) * Real.exp (u * d.re / 2 * v) := by ring
      calc Real.exp (-(u * d.re) * v) * v ^ k
          ≤ Real.exp (-(u * d.re) * v) *
              (((k.factorial : ℝ) / (u * d.re / 2) ^ k) * Real.exp (u * d.re / 2 * v)) :=
            mul_le_mul_of_nonneg_left hvk (Real.exp_pos _).le
        _ = ((k.factorial : ℝ) / (u * d.re / 2) ^ k) * Real.exp (-(u * d.re / 2) * v) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    rw [MeasureTheory.integral_finsetSum _ hi_term]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, complexLaplace_monomial k (by simp [Complex.mul_re]; exact mul_pos hu_pos hd)]
    rw [mul_pow, inv_pow]
    have hk_ne : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    field_simp [hk_ne, hd_ne, hu_ne]
  have hP_exp' : ∀ v : ℝ, 0 ≤ v → ‖pull d P_trunc v‖ ≤ C_poly * Real.exp (1 * v) :=
    fun v hv => by simpa [one_mul] using hP_exp v hv
  have hval_diff : a.value d (u : ℂ) - (a.atom + ∑ k ∈ Finset.range M,
        iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1))) =
      ∫ v in Ioi (0 : ℝ), damped ((u : ℂ) * d) (fun w => pull d a.density w - pull d P_trunc w) v := by
    unfold value
    rw [← h_lap_poly]
    have hadd_sub : a.atom + complexLaplace (pull d a.density) ((u : ℂ) * d) -
        (a.atom + complexLaplace (pull d P_trunc) ((u : ℂ) * d)) =
        complexLaplace (pull d a.density) ((u : ℂ) * d) -
          complexLaplace (pull d P_trunc) ((u : ℂ) * d) := by ring
    rw [hadd_sub]
    unfold complexLaplace
    have hi_a : IntegrableOn (damped ((u : ℂ) * d) (pull d a.density)) (Ioi 0) :=
      damped_integrable (pull_cont ray ha) hexp
        (by simp [Complex.mul_re]; linarith [le_max_left D_exp 1, hD₀_ge_1, hu_d_gt])
    have hi_P : IntegrableOn (damped ((u : ℂ) * d) (pull d P_trunc)) (Ioi 0) :=
      damped_integrable (Continuous.continuousOn (by unfold pull P_trunc; fun_prop)) hP_exp'
        (by simp [Complex.mul_re]; linarith [hD₀_ge_1, hu_d_gt])
    rw [← integral_sub hi_a hi_P]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp [damped, mul_sub]
  rw [hval_diff]
  let diff_integrand (v : ℝ) : ℂ :=
    damped ((u : ℂ) * d) (fun w => pull d a.density w - pull d P_trunc w) v
  have hi_diff : IntegrableOn diff_integrand (Ioi 0) := by
    have hi_a : IntegrableOn (damped ((u : ℂ) * d) (pull d a.density)) (Ioi 0) :=
      damped_integrable (pull_cont ray ha) hexp
        (by simp [Complex.mul_re]; linarith [le_max_left D_exp 1, hD₀_ge_1, hu_d_gt])
    have hi_P : IntegrableOn (damped ((u : ℂ) * d) (pull d P_trunc)) (Ioi 0) :=
      damped_integrable (Continuous.continuousOn (by unfold pull P_trunc; fun_prop)) hP_exp'
        (by simp [Complex.mul_re]; linarith [hD₀_ge_1, hu_d_gt])
    refine (hi_a.sub hi_P).congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp [diff_integrand, damped, mul_sub]
  have hsplit_dom : Ioi (0 : ℝ) = Ioc 0 δ ∪ Ioi δ := (Ioc_union_Ioi_eq_Ioi hδ.le).symm
  have hdisj_dom : Disjoint (Ioc (0 : ℝ) δ) (Ioi δ) := Ioc_disjoint_Ioi_same
  have hint_split : ∫ v in Ioi (0 : ℝ), diff_integrand v =
      (∫ v in Ioc 0 δ, diff_integrand v) + ∫ v in Ioi δ, diff_integrand v := by
    conv_lhs => rw [hsplit_dom]
    exact setIntegral_union hdisj_dom measurableSet_Ioi
      (hi_diff.mono_set Ioc_subset_Ioi_self) (hi_diff.mono_set (Ioi_subset_Ioi hδ.le))
  rw [hint_split]
  have h_small : ‖∫ v in Ioc 0 δ, diff_integrand v‖ ≤ K₁ / u ^ (M + 1) := by
    let bound₁ (v : ℝ) : ℝ := ‖d‖ ^ (M + 1) * K_R * (v ^ M * Real.exp (-(u * d.re) * v))
    have hle₁ : ∀ v ∈ Ioc (0 : ℝ) δ, ‖diff_integrand v‖ ≤ bound₁ v := by
      intro v hv
      have hv0 : 0 ≤ v := hv.1.le
      have hdv_mem : d * (v : ℂ) ∈ Metric.ball (0 : ℂ) δ_r := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hv.1]
        have : ‖d‖ * v ≤ ‖d‖ * δ := mul_le_mul_of_nonneg_left hv.2 (norm_nonneg d)
        have hδeq : ‖d‖ * δ = δ_r / 2 := by dsimp only [δ]; field_simp [hdn_pos.ne']
        linarith
      have hR_le : ‖R (d * (v : ℂ))‖ ≤ K_R := hR_bdd _ hdv_mem
      have hsub_eq : pull d a.density v - pull d P_trunc v =
          d * ((d * (v : ℂ)) ^ M * R (d * (v : ℂ))) := by
        have h1 := hReq (d * (v : ℂ))
        simp only [smul_eq_mul] at h1
        change a.density (d * (v : ℂ)) = P_trunc (d * (v : ℂ)) + (d * (v : ℂ)) ^ M * R (d * (v : ℂ)) at h1
        simp only [pull, h1, mul_add]
        ring
      rw [show diff_integrand v = damped ((u : ℂ) * d) _ v from rfl, damped_norm,
        show (((u : ℂ) * d).re) = u * d.re by simp [Complex.mul_re], hsub_eq,
        norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv.1,
        mul_pow]
      calc Real.exp (-(u * d.re) * v) * (‖d‖ * (‖d‖ ^ M * v ^ M * ‖R (d * (v : ℂ))‖))
          ≤ Real.exp (-(u * d.re) * v) * (‖d‖ * (‖d‖ ^ M * v ^ M * K_R)) := by
            gcongr
        _ = bound₁ v := by dsimp only [bound₁]; rw [pow_succ']; ring
    have hi_b1_Ioi : IntegrableOn bound₁ (Ioi 0) := by
      have h_integrable : IntegrableOn (fun v : ℝ => v ^ M * Real.exp (-(u * d.re) * v)) (Ioi 0) := by
        refine ((integrableOn_exp_mul_Ioi (show -(u * d.re / 2) < 0 by linarith [mul_pos hu_pos hd]) 0).const_mul
          ((M.factorial : ℝ) / (u * d.re / 2) ^ M)).mono'
          ((by fun_prop : Continuous (fun v : ℝ => v ^ M * Real.exp (-(u * d.re) * v))).aestronglyMeasurable.restrict) ?_
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
        change 0 < v at hv
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le)]
        have hpow : (u * d.re / 2 * v) ^ M / (M.factorial : ℝ) ≤ Real.exp (u * d.re / 2 * v) :=
          Real.pow_div_factorial_le_exp _ (by positivity) M
        have hvM : v ^ M ≤ ((M.factorial : ℝ) / (u * d.re / 2) ^ M) * Real.exp (u * d.re / 2 * v) := by
          have h1 : 0 < (u * d.re / 2) ^ M := pow_pos (by positivity) M
          have h2 : 0 < (M.factorial : ℝ) := by positivity
          rw [mul_pow, div_le_iff₀ h2] at hpow
          calc v ^ M ≤ (Real.exp (u * d.re / 2 * v) * M.factorial) / (u * d.re / 2) ^ M :=
                (le_div_iff₀ h1).mpr (by linarith)
            _ = ((M.factorial : ℝ) / (u * d.re / 2) ^ M) * Real.exp (u * d.re / 2 * v) := by ring
        calc v ^ M * Real.exp (-(u * d.re) * v)
            ≤ (((M.factorial : ℝ) / (u * d.re / 2) ^ M) * Real.exp (u * d.re / 2 * v)) *
                Real.exp (-(u * d.re) * v) :=
              mul_le_mul_of_nonneg_right hvM (Real.exp_pos _).le
          _ = ((M.factorial : ℝ) / (u * d.re / 2) ^ M) * Real.exp (-(u * d.re / 2) * v) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      exact h_integrable.const_mul (‖d‖ ^ (M + 1) * K_R)
    have hle_norm : ‖∫ v in Ioc 0 δ, diff_integrand v‖ ≤ ∫ v in Ioi 0, bound₁ v := by
      calc ‖∫ v in Ioc 0 δ, diff_integrand v‖
          ≤ ∫ v in Ioc 0 δ, ‖diff_integrand v‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ v in Ioc 0 δ, bound₁ v :=
            setIntegral_mono_on (hi_diff.mono_set Ioc_subset_Ioi_self).norm
              (hi_b1_Ioi.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hle₁
        _ ≤ ∫ v in Ioi 0, bound₁ v :=
            setIntegral_mono_set hi_b1_Ioi
              ((ae_restrict_mem measurableSet_Ioi).mono fun v (hv : 0 < v) => by
                dsimp only [bound₁]
                exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le))
              (Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx)
    have hint_b1 : ∫ v in Ioi 0, bound₁ v = K₁ / u ^ (M + 1) := by
      dsimp only [bound₁]
      rw [integral_const_mul]
      have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (M : ℝ) + 1) (by positivity) (mul_pos hu_pos hd)
      have heq : (fun v : ℝ => v ^ M * Real.exp (-(u * d.re) * v)) =
          fun v : ℝ => v ^ (((M : ℝ) + 1) - 1) * Real.exp (-((u * d.re) * v)) := by
        funext v; rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
      rw [heq, hg, Real.Gamma_nat_eq_factorial,
        show (M : ℝ) + 1 = ((M + 1 : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_natCast, one_div, inv_pow, mul_pow]
      dsimp only [K₁]
      field_simp [hu_pos.ne', hd.ne']
    exact hle_norm.trans_eq hint_b1
  have h_large : ‖∫ v in Ioi δ, diff_integrand v‖ ≤ K₂ / u ^ (M + 1) := by
    let bound₂ (v : ℝ) : ℝ := (C_tail * Real.exp (-(u * d.re / 4) * δ)) * Real.exp (-(u * d.re / 4) * v)
    have hle₂ : ∀ v ∈ Ioi δ, ‖diff_integrand v‖ ≤ bound₂ v := by
      intro v hv
      change δ < v at hv
      have hv0 : 0 ≤ v := le_trans hδ.le hv.le
      have hsub_n : ‖pull d a.density v - pull d P_trunc v‖ ≤ C_tail * Real.exp (D₀ * v) := by
        calc ‖pull d a.density v - pull d P_trunc v‖
            ≤ ‖pull d a.density v‖ + ‖pull d P_trunc v‖ := norm_sub_le _ _
          _ ≤ C_exp * Real.exp (D_exp * v) + C_poly * Real.exp v := add_le_add (hexp v hv0) (hP_exp v hv0)
          _ ≤ C_exp * Real.exp (D₀ * v) + C_poly * Real.exp (D₀ * v) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
                (mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)) hCexp
            · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
                (le_mul_of_one_le_left hv0 hD₀_ge_1)) hCpoly
          _ = C_tail * Real.exp (D₀ * v) := by dsimp only [C_tail]; ring
      rw [show diff_integrand v = damped ((u : ℂ) * d) _ v from rfl, damped_norm,
        show (((u : ℂ) * d).re) = u * d.re by simp [Complex.mul_re]]
      calc Real.exp (-(u * d.re) * v) * ‖pull d a.density v - pull d P_trunc v‖
          ≤ Real.exp (-(u * d.re) * v) * (C_tail * Real.exp (D₀ * v)) :=
            mul_le_mul_of_nonneg_left hsub_n (Real.exp_pos _).le
        _ = C_tail * Real.exp ((D₀ - u * d.re) * v) := by
            rw [mul_left_comm _ C_tail, ← Real.exp_add]; congr 2; ring
        _ ≤ C_tail * Real.exp (-(u * d.re / 2) * v) := by
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hCtail
            nlinarith [hu_d_gt, hv0]
        _ = C_tail * (Real.exp (-(u * d.re / 4) * v) * Real.exp (-(u * d.re / 4) * v)) := by
            rw [← Real.exp_add]; congr 2; ring
        _ ≤ C_tail * (Real.exp (-(u * d.re / 4) * δ) * Real.exp (-(u * d.re / 4) * v)) := by
            apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _)
              (Real.exp_pos _).le) hCtail
            nlinarith [mul_pos hu_pos hd, hv]
        _ = bound₂ v := by dsimp only [bound₂]; ring
    have hi_b2_Ioi : IntegrableOn bound₂ (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (show -(u * d.re / 4) < 0 by linarith [mul_pos hu_pos hd]) 0).const_mul _
    have hle_norm : ‖∫ v in Ioi δ, diff_integrand v‖ ≤ ∫ v in Ioi 0, bound₂ v := by
      calc ‖∫ v in Ioi δ, diff_integrand v‖
          ≤ ∫ v in Ioi δ, ‖diff_integrand v‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ v in Ioi δ, bound₂ v :=
            setIntegral_mono_on (hi_diff.mono_set (Ioi_subset_Ioi hδ.le)).norm
              (hi_b2_Ioi.mono_set (Ioi_subset_Ioi hδ.le)) measurableSet_Ioi hle₂
        _ ≤ ∫ v in Ioi 0, bound₂ v :=
            integral_mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hδ.le) le_rfl)
              (ae_of_all _ fun v => by dsimp only [bound₂]; positivity) hi_b2_Ioi
    have hint_b2 : ∫ v in Ioi 0, bound₂ v =
        (C_tail * Real.exp (-(u * d.re / 4) * δ)) * (4 / (u * d.re)) := by
      dsimp only [bound₂]
      rw [integral_const_mul, integral_exp_mul_Ioi (show -(u * d.re / 4) < 0 by linarith [mul_pos hu_pos hd]) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp [hu_pos.ne', hd.ne']
    have hexp_decay : Real.exp (-(u * d.re / 4) * δ) ≤
        ((M + 1).factorial : ℝ) / ((d.re * δ / 4) ^ (M + 1) * u ^ (M + 1)) := by
      have harg : (u * (d.re * δ / 4)) ^ (M + 1) / ((M + 1).factorial : ℝ) ≤
          Real.exp ((u * d.re / 4) * δ) := by
        have := Real.pow_div_factorial_le_exp (u * (d.re * δ / 4)) (by positivity) (M + 1)
        simpa [show u * (d.re * δ / 4) = u * d.re / 4 * δ by ring] using this
      have h1 : 0 < (d.re * δ / 4) ^ (M + 1) := pow_pos (by positivity) (M + 1)
      have h2 : 0 < u ^ (M + 1) := pow_pos hu_pos (M + 1)
      have h3 : 0 < ((M + 1).factorial : ℝ) := by positivity
      calc Real.exp (-(u * d.re / 4) * δ) = (Real.exp ((u * d.re / 4) * δ))⁻¹ := by
            rw [← Real.exp_neg]; congr 1; ring
        _ ≤ ((u * (d.re * δ / 4)) ^ (M + 1) / ((M + 1).factorial : ℝ))⁻¹ := by
            refine inv_anti₀ (div_pos (pow_pos (by positivity) _) h3) harg
        _ = ((M + 1).factorial : ℝ) / ((d.re * δ / 4) ^ (M + 1) * u ^ (M + 1)) := by
            rw [inv_div, mul_pow]; ring
    calc ‖∫ v in Ioi δ, diff_integrand v‖
        ≤ ∫ v in Ioi 0, bound₂ v := hle_norm
      _ = (C_tail * Real.exp (-(u * d.re / 4) * δ)) * (4 / (u * d.re)) := hint_b2
      _ ≤ (C_tail * (((M + 1).factorial : ℝ) / ((d.re * δ / 4) ^ (M + 1) * u ^ (M + 1)))) *
            (4 / d.re) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hexp_decay hCtail) ?_ (by positivity) (by positivity)
          exact div_le_div_of_nonneg_left (by norm_num) hd (le_mul_of_one_le_left hd.le hu_ge_1)
      _ = K₂ / u ^ (M + 1) := by dsimp only [K₂]; ring
  calc ‖(∫ v in Ioc 0 δ, diff_integrand v) + ∫ v in Ioi δ, diff_integrand v‖
      ≤ ‖∫ v in Ioc 0 δ, diff_integrand v‖ + ‖∫ v in Ioi δ, diff_integrand v‖ := norm_add_le _ _
    _ ≤ K₁ / u ^ (M + 1) + K₂ / u ^ (M + 1) := add_le_add h_small h_large
    _ = (K₁ + K₂) / u ^ (M + 1) := by ring

theorem toSeries_eq_zero_of_flat (a : Minor) {U : Set ℂ} {d : ℂ}
    (hU : Domain U) (ray : ContainsRay U d) (ha : a.Good U d) (hd : 0 < d.re)
    (hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop, ‖a.value d (u : ℂ)‖ ≤ C / u ^ (M + 1)) :
    a.toSeries = 0 := by
  have hatom : a.atom = 0 := by
    obtain ⟨C₀, _, hC₀⟩ := value_asymptotic a hU ray ha hd 0
    obtain ⟨Cf, hCf⟩ := hflat 0
    have hlim : Tendsto (fun u : ℝ => a.value d (u : ℂ) - a.atom) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun u : ℝ => C₀ / u) ?_ ?_
      · filter_upwards [hC₀] with u hu
        simpa using hu
      · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := C₀)).mul tendsto_inv_atTop_zero
    have hlim0 : Tendsto (fun u : ℝ => a.value d (u : ℂ)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun u : ℝ => Cf / u) ?_ ?_
      · filter_upwards [hCf] with u hu
        simpa using hu
      · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := Cf)).mul tendsto_inv_atTop_zero
    have hconst := hlim0.sub hlim
    simp only [sub_sub_cancel, sub_zero] at hconst
    exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm
  have hderiv : ∀ k : ℕ, iteratedDeriv k a.density 0 = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      obtain ⟨Ck, _, hCk⟩ := value_asymptotic a hU ray ha hd (k + 1)
      obtain ⟨Cf, hCf⟩ := hflat (k + 1)
      have htrunc : ∀ᶠ u : ℝ in atTop,
          ‖iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖ ≤ (Cf + Ck) / u ^ (k + 2) := by
        filter_upwards [hCk, hCf] with u hu_asymp hu_flat
        have hsum_k : ∑ j ∈ Finset.range (k + 1),
            iteratedDeriv j a.density 0 * ((u : ℂ)⁻¹ ^ (j + 1)) =
            iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
          rw [Finset.sum_range_succ]
          have hlow : ∑ j ∈ Finset.range k, iteratedDeriv j a.density 0 * ((u : ℂ)⁻¹ ^ (j + 1)) = 0 := by
            refine Finset.sum_eq_zero fun j hj => ?_
            rw [ih j (Finset.mem_range.mp hj), zero_mul]
          rw [hlow, zero_add]
        rw [hatom, zero_add, hsum_k] at hu_asymp
        calc ‖iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖
            = ‖a.value d (u : ℂ) - (a.value d (u : ℂ) -
                iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1)))‖ := by
              congr 1; ring
          _ ≤ ‖a.value d (u : ℂ)‖ +
                ‖a.value d (u : ℂ) - iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖ :=
              norm_sub_le _ _
          _ ≤ Cf / u ^ (k + 2) + Ck / u ^ (k + 2) := add_le_add hu_flat hu_asymp
          _ = (Cf + Ck) / u ^ (k + 2) := by ring
      have hlim_const : Tendsto (fun u : ℝ =>
          u ^ (k + 1) * ‖iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖) atTop
          (𝓝 ‖iteratedDeriv k a.density 0‖) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu_pos
        rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos,
          inv_pow]
        field_simp [(pow_pos hu_pos (k + 1)).ne']
      have hlim_zero : Tendsto (fun u : ℝ =>
          u ^ (k + 1) * ‖iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖) atTop (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun u : ℝ => (Cf + Ck) / u) ?_ ?_
        · filter_upwards [htrunc, eventually_gt_atTop (0 : ℝ)] with u hu hu_pos
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hu_pos.le _) (norm_nonneg _))]
          calc u ^ (k + 1) * ‖iteratedDeriv k a.density 0 * ((u : ℂ)⁻¹ ^ (k + 1))‖
              ≤ u ^ (k + 1) * ((Cf + Ck) / u ^ (k + 2)) :=
                mul_le_mul_of_nonneg_left hu (pow_nonneg hu_pos.le _)
            _ = (Cf + Ck) / u := by
                rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
                field_simp [hu_pos.ne']
                ring
        · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := Cf + Ck)).mul tendsto_inv_atTop_zero
      have h0 : ‖iteratedDeriv k a.density 0‖ = 0 := tendsto_nhds_unique hlim_const hlim_zero
      exact norm_eq_zero.mp h0
  ext n
  cases n with
  | zero => simp [toSeries, hatom]
  | succ k => simp [toSeries, hderiv k]

end Minor

/-- Formal differential polynomial AST with one leaf representing the unknown asymptotic function `y`. -/
inductive BorelExpr where
  | const (c : ℂ)
  | leaf
  | add (e f : BorelExpr)
  | mul (e f : BorelExpr)
  | jet (e : BorelExpr)

namespace BorelExpr

@[expose] def residual (a : Minor) : BorelExpr → Minor
  | const c => Minor.const c
  | leaf => a
  | add e f => (e.residual a).plus (f.residual a)
  | mul e f => (e.residual a).times (f.residual a)
  | jet e => (e.residual a).jet

@[expose] def eval (a : Minor) (d : ℂ) : BorelExpr → ℂ → ℂ
  | const c => fun _ => c
  | leaf => a.value d
  | add e f => fun p => e.eval a d p + f.eval a d p
  | mul e f => fun p => e.eval a d p * f.eval a d p
  | jet e => fun p => deriv (e.eval a d) p

theorem represents (e : BorelExpr) {U : Set ℂ} {d : ℂ} (hU : Domain U) (ray : ContainsRay U d)
    {a : Minor} (ha : a.Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[far d] (e.residual a).value d := by
  induction e with
  | const c =>
    refine ⟨Minor.Good.const c, .of_forall fun p => (Minor.good_const_value c d p).symm⟩
  | leaf => exact ⟨ha, .rfl⟩
  | add e f he hf =>
    refine ⟨he.1.plus hf.1, ?_⟩
    filter_upwards [he.2, hf.2, Minor.good_plus_value ray he.1 hf.1] with p hp hq h
    simp only [residual, eval, h, hp, hq]
  | mul e f he hf =>
    refine ⟨he.1.times hU hf.1, ?_⟩
    filter_upwards [he.2, hf.2, Minor.good_times_value ray hU he.1 hf.1] with p hp hq h
    simp only [residual, eval, h, hp, hq]
  | jet e he =>
    refine ⟨he.1.jet, ?_⟩
    obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp he.2)
    filter_upwards [eventually_bound_far d R, Minor.good_jet_derivative ray he.1] with p hp h
    have loc : e.eval a d =ᶠ[𝓝 p] (e.residual a).value d := by
      filter_upwards [(isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_id.mul_const d))).mem_nhds hp] with q hq
      exact hR _ (le_of_lt hq) q rfl
    simp only [eval, residual, loc.deriv_eq, h.deriv]

lemma jetIter_eval_eq_iteratedDeriv (a : Minor) {U : Set ℂ} {d : ℂ}
    (hU : Domain U) (ray : ContainsRay U d) (ha : a.Good U d) (hd : 0 < d.re) (j : ℕ) :
    (∀ᶠ u : ℝ in atTop,
      (Nat.iterate jet j leaf).eval a d (u : ℂ) =
        iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ)) u) ∧
    (∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ))) u) := by
  induction j with
  | zero =>
    obtain ⟨good0, rep0⟩ := (leaf).represents hU ray ha
    obtain ⟨_, D, _, _, hg⟩ := good0.2
    obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp rep0)
    have hdiff0 : ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv 0 (fun t : ℝ => a.value d (t : ℂ))) u := by
      have ht : Tendsto (fun u : ℝ => ((u : ℂ) * d).re) atTop atTop := by
        have heq : (fun u : ℝ => ((u : ℂ) * d).re) = fun u : ℝ => u * d.re := by
          funext u; simp [Complex.mul_re]
        rw [heq]
        exact tendsto_id.atTop_mul_const hd
      filter_upwards [ht.eventually (eventually_comap.mp (Minor.good_jet_derivative ray ha))] with u hu
      exact (hu (u : ℂ) rfl).comp_ofReal.differentiableAt
    exact ⟨.of_forall fun u => rfl, hdiff0⟩
  | succ j ih =>
    let e := Nat.iterate jet j leaf
    obtain ⟨good_e, rep_e⟩ := e.represents hU ray ha
    obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (eventually_comap.mp rep_e)
    obtain ⟨R₂, hR₂⟩ := eventually_atTop.mp (eventually_comap.mp (Minor.good_jet_derivative ray good_e))
    let R : ℝ := max R₁ R₂
    have ht_large : ∀ᶠ u : ℝ in atTop, R < ((u : ℂ) * d).re := by
      rw [eventually_atTop]
      refine ⟨(R + 1) / d.re, fun u hu => ?_⟩
      have : R + 1 ≤ u * d.re := (div_le_iff₀ hd).mp hu
      simpa [Complex.mul_re] using by linarith
    have heval_succ : ∀ᶠ u : ℝ in atTop,
        (Nat.iterate jet (j + 1) leaf).eval a d (u : ℂ) =
          iteratedDeriv (j + 1) (fun t : ℝ => a.value d (t : ℂ)) u := by
      have ih_nhds : ∀ᶠ u : ℝ in atTop,
          (fun t : ℝ => e.eval a d (t : ℂ)) =ᶠ[𝓝 u]
            iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ)) := by
        obtain ⟨L, hL⟩ := eventually_atTop.mp ih.1
        filter_upwards [eventually_gt_atTop L] with u hu
        filter_upwards [eventually_gt_nhds hu] with t ht
        exact hL t ht.le
      filter_upwards [ht_large, ih_nhds] with u hu hloc
      have hp_open : ∀ᶠ p : ℂ in 𝓝 (u : ℂ), R < (p * d).re :=
        (isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_id.mul_const d))).mem_nhds hu
      have hloc_c : e.eval a d =ᶠ[𝓝 (u : ℂ)] (e.residual a).value d := by
        filter_upwards [hp_open] with p hp
        exact hR₁ _ ((le_max_left _ _).trans hp.le) p rfl
      have hd_val : HasDerivAt ((e.residual a).value d) ((e.residual a).jet.value d (u : ℂ)) (u : ℂ) :=
        hR₂ _ ((le_max_right _ _).trans hu.le) (u : ℂ) rfl
      have hd_eval : HasDerivAt (e.eval a d) ((e.residual a).jet.value d (u : ℂ)) (u : ℂ) :=
        hd_val.congr_of_eventuallyEq hloc_c
      have hd_real : HasDerivAt (fun t : ℝ => e.eval a d (t : ℂ))
          ((e.residual a).jet.value d (u : ℂ)) u := hd_eval.comp_ofReal
      have hd_it : HasDerivAt (iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ)))
          ((e.residual a).jet.value d (u : ℂ)) u := hd_real.congr_of_eventuallyEq hloc.symm
      rw [Function.iterate_succ_apply', iteratedDeriv_succ]
      change deriv (e.eval a d) (u : ℂ) = deriv (iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ))) u
      rw [hd_eval.deriv, hd_it.deriv]
    -- Also prove `DifferentiableAt` of `(j + 1)`-th iterated derivative!
    obtain ⟨good_succ, rep_succ⟩ := (Nat.iterate jet (j + 1) leaf).represents hU ray ha
    obtain ⟨R₃, hR₃⟩ := eventually_atTop.mp (eventually_comap.mp rep_succ)
    obtain ⟨R₄, hR₄⟩ := eventually_atTop.mp (eventually_comap.mp (Minor.good_jet_derivative ray good_succ))
    let R' : ℝ := max R₃ R₄
    have hdiff_succ : ∀ᶠ u : ℝ in atTop,
        DifferentiableAt ℝ (iteratedDeriv (j + 1) (fun t : ℝ => a.value d (t : ℂ))) u := by
      obtain ⟨L, hL⟩ := eventually_atTop.mp heval_succ
      filter_upwards [eventually_gt_atTop L, eventually_gt_atTop ((R' + 1) / d.re)] with u huL huR
      have hu_re : R' < ((u : ℂ) * d).re := by
        have : R' + 1 ≤ u * d.re := (div_le_iff₀ hd).mp huR.le
        simpa [Complex.mul_re] using by linarith
      have hp_open : ∀ᶠ p : ℂ in 𝓝 (u : ℂ), R' < (p * d).re :=
        (isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_id.mul_const d))).mem_nhds hu_re
      have hloc_c : (Nat.iterate jet (j + 1) leaf).eval a d =ᶠ[𝓝 (u : ℂ)]
          ((Nat.iterate jet (j + 1) leaf).residual a).value d := by
        filter_upwards [hp_open] with p hp
        exact hR₃ _ ((le_max_left _ _).trans hp.le) p rfl
      have hd_val : HasDerivAt (((Nat.iterate jet (j + 1) leaf).residual a).value d)
          (((Nat.iterate jet (j + 1) leaf).residual a).jet.value d (u : ℂ)) (u : ℂ) :=
        hR₄ _ ((le_max_right _ _).trans hu_re.le) (u : ℂ) rfl
      have hd_real : HasDerivAt (fun t : ℝ => (Nat.iterate jet (j + 1) leaf).eval a d (t : ℂ))
          (((Nat.iterate jet (j + 1) leaf).residual a).jet.value d (u : ℂ)) u :=
        (hd_val.congr_of_eventuallyEq hloc_c).comp_ofReal
      have hloc_r : (fun t : ℝ => (Nat.iterate jet (j + 1) leaf).eval a d (t : ℂ)) =ᶠ[𝓝 u]
          iteratedDeriv (j + 1) (fun t : ℝ => a.value d (t : ℂ)) := by
        filter_upwards [eventually_gt_nhds huL] with t ht
        exact hL t ht.le
      exact (hd_real.congr_of_eventuallyEq hloc_r.symm).differentiableAt
    exact ⟨heval_succ, hdiff_succ⟩

theorem exists_of_mvPolynomial {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) :
    ∃ e : BorelExpr,
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d →
        (e.residual a).toSeries = formalEval a.toSeries P) ∧
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor) (_hU : Domain U) (_ray : ContainsRay U d)
        (_ha : a.Good U d) (_hd : 0 < d.re),
        ∀ᶠ u : ℝ in atTop,
          e.eval a d (u : ℂ) =
            MvPolynomial.eval
              (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => a.value d (t : ℂ)) u) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨const c, ?_, ?_⟩
    · intro U d a _ _ _
      simp [residual, Minor.toSeries_const, formalEval]
    · intro U d a _ _ _ _
      simp [eval]
  | add P₁ P₂ h₁ h₂ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    obtain ⟨e₂, hs₂, he₂⟩ := h₂
    refine ⟨add e₁ e₂, ?_, ?_⟩
    · intro U d a hU ray ha
      have hg₁ := (e₁.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      have hg₂ := (e₂.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      rw [residual, Minor.toSeries_plus hg₁ hg₂, hs₁ U d a hU ray ha, hs₂ U d a hU ray ha]
      simp [formalEval]
    · intro U d a hU ray ha hd
      filter_upwards [he₁ U d a hU ray ha hd, he₂ U d a hU ray ha hd] with u hu₁ hu₂
      simp [eval, hu₁, hu₂]
  | mul_X P₁ j h₁ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    let ej : BorelExpr := Nat.iterate jet j.val leaf
    refine ⟨mul e₁ ej, ?_, ?_⟩
    · intro U d a hU ray ha
      have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
      have hg₁ := (e₁.represents hU ray ha).1.1 0 h0
      have hgj := (ej.represents hU ray ha).1.1 0 h0
      rw [residual, Minor.toSeries_times hg₁ hgj, hs₁ U d a hU ray ha]
      have hj_series : ∀ k : ℕ, ((Nat.iterate jet k leaf).residual a).toSeries = d_u^[k] a.toSeries := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          have hgk := ((Nat.iterate jet k leaf).represents hU ray ha).1.1 0 h0
          rw [Function.iterate_succ_apply' jet k leaf, Function.iterate_succ_apply' d_u k a.toSeries]
          exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
      rw [hj_series j.val]
      simp [formalEval]
    · intro U d a hU ray ha hd
      filter_upwards [he₁ U d a hU ray ha hd,
        (jetIter_eval_eq_iteratedDeriv a hU ray ha hd j.val).1] with u hu₁ huj
      simp [eval, ej, hu₁, huj]

end BorelExpr

/-- A real function `f : ℝ → ℂ` has all-orders `1/u` asymptotic expansion equal to `S ∈ ℂ[[1/u]]`. -/
@[expose] def HasAsympExp (f : ℝ → ℂ) (S : PowerSeries ℂ) : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
    ‖f u - ∑ k ∈ Finset.range M, PowerSeries.coeff k S * ((u : ℂ)⁻¹ ^ k)‖ ≤ C / u ^ M

lemma HasAsympExp.const (c : ℂ) : HasAsympExp (fun _ => c) (PowerSeries.C c) := by
  intro M
  refine ⟨‖c‖, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  cases M with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    simp [PowerSeries.coeff_C]
    positivity

lemma HasAsympExp.add {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hg : HasAsympExp g T) :
    HasAsympExp (fun u => f u + g u) (S + T) := by
  intro M
  obtain ⟨Cf, hCf⟩ := hf M
  obtain ⟨Cg, hCg⟩ := hg M
  refine ⟨Cf + Cg, ?_⟩
  filter_upwards [hCf, hCg] with u hfu hgu
  have hsum : ∑ k ∈ Finset.range M, PowerSeries.coeff k (S + T) * ((u : ℂ)⁻¹ ^ k) =
      (∑ k ∈ Finset.range M, PowerSeries.coeff k S * ((u : ℂ)⁻¹ ^ k)) +
        ∑ k ∈ Finset.range M, PowerSeries.coeff k T * ((u : ℂ)⁻¹ ^ k) := by
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  rw [hsum]
  calc ‖f u + g u - (_ + _)‖
      = ‖(f u - _) + (g u - _)‖ := by congr 1; ring
    _ ≤ ‖f u - _‖ + ‖g u - _‖ := norm_add_le _ _
    _ ≤ Cf / u ^ M + Cg / u ^ M := add_le_add hfu hgu
    _ = (Cf + Cg) / u ^ M := by ring

lemma HasAsympExp.mul {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hg : HasAsympExp g T) :
    HasAsympExp (fun u => f u * g u) (S * T) := by
  intro M
  obtain ⟨Cf, hCf⟩ := hf M
  obtain ⟨Cg, hCg⟩ := hg M
  let Pf (u : ℝ) : ℂ := ∑ k ∈ Finset.range M, PowerSeries.coeff k S * ((u : ℂ)⁻¹ ^ k)
  let Pg (u : ℝ) : ℂ := ∑ k ∈ Finset.range M, PowerSeries.coeff k T * ((u : ℂ)⁻¹ ^ k)
  let Pfg (u : ℝ) : ℂ := ∑ k ∈ Finset.range M, PowerSeries.coeff k (S * T) * ((u : ℂ)⁻¹ ^ k)
  let Bf : ℝ := ∑ k ∈ Finset.range M, ‖PowerSeries.coeff k S‖
  let Bg : ℝ := ∑ k ∈ Finset.range M, ‖PowerSeries.coeff k T‖
  let Bfg : ℝ := ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if M ≤ i + j then ‖PowerSeries.coeff i S * PowerSeries.coeff j T‖ else 0
  have hPf_bdd : ∀ u : ℝ, 1 ≤ u → ‖Pf u‖ ≤ Bf := fun u hu => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu))
  have hPg_bdd : ∀ u : ℝ, 1 ≤ u → ‖Pg u‖ ≤ Bg := fun u hu => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu))
  have hPdiff : ∀ u : ℝ, 1 ≤ u → ‖Pf u * Pg u - Pfg u‖ ≤ Bfg / u ^ M := fun u hu => by
    have hsplit : Pf u * Pg u - Pfg u = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (if M ≤ i + j then PowerSeries.coeff i S * PowerSeries.coeff j T * ((u : ℂ)⁻¹ ^ (i + j)) else 0) := by
      have hmul : Pf u * Pg u = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
          PowerSeries.coeff i S * PowerSeries.coeff j T * ((u : ℂ)⁻¹ ^ (i + j)) := by
        dsimp only [Pf, Pg]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_add]; ring
      have hpfg : Pfg u = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
          (if i + j < M then PowerSeries.coeff i S * PowerSeries.coeff j T * ((u : ℂ)⁻¹ ^ (i + j)) else 0) := by
        simp only [Pfg, PowerSeries.coeff_mul]
        have hanti : ∑ k ∈ Finset.range M,
            (∑ p ∈ Finset.antidiagonal k, PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T) *
              ((u : ℂ)⁻¹ ^ k) =
            ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
              (if i + j < M then PowerSeries.coeff i S * PowerSeries.coeff j T * ((u : ℂ)⁻¹ ^ (i + j)) else 0) := by
          simp_rw [Finset.sum_mul]
          trans ∑ k ∈ Finset.range M, ∑ p ∈ Finset.antidiagonal k,
              PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * ((u : ℂ)⁻¹ ^ (p.1 + p.2))
          · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p hp => ?_
            rw [Finset.mem_antidiagonal.mp hp]
          · let g : ℕ × ℕ → ℂ := fun p =>
              PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * ((u : ℂ)⁻¹ ^ (p.1 + p.2))
            have hL : (∑ k ∈ Finset.range M, ∑ p ∈ Finset.antidiagonal k, g p) =
                ∑ p ∈ (Finset.range M ×ˢ Finset.range M).filter (fun p : ℕ × ℕ => p.1 + p.2 < M), g p := by
              rw [← Finset.sum_sigma (f := fun x : Σ _ : ℕ, ℕ × ℕ => g x.2)]
              refine Finset.sum_bij (fun x _ => x.2) ?_ ?_ ?_ ?_
              · intro x hx
                simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx
                simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
                exact ⟨⟨by omega, by omega⟩, by omega⟩
              · intro x₁ hx₁ x₂ hx₂ he
                simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx₁ hx₂
                exact Sigma.ext (by rw [← hx₁.2, ← hx₂.2, he]) (heq_of_eq he)
              · intro p hp
                simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
                refine ⟨⟨p.1 + p.2, p⟩, ?_, rfl⟩
                simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
                exact ⟨hp.2, trivial⟩
              · intro _ _; rfl
            have hR : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, if i + j < M then g (i, j) else 0) =
                ∑ p ∈ (Finset.range M ×ˢ Finset.range M).filter (fun p : ℕ × ℕ => p.1 + p.2 < M), g p := by
              rw [← Finset.sum_product', Finset.sum_filter]
            dsimp only [g] at hL hR
            exact hL.trans hR.symm
        exact hanti
      rw [hmul, hpfg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h1 h2
      · omega
      · simp
      · simp
      · omega
    rw [hsplit]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with hij
    · rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have hpow : (u⁻¹) ^ (i + j) ≤ (u⁻¹) ^ M := by
        have huinv0 : 0 ≤ u⁻¹ := by positivity
        have huinv1 : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu
        have : (u⁻¹) ^ (i + j) = (u⁻¹) ^ M * (u⁻¹) ^ (i + j - M) := by
          rw [← pow_add, show M + (i + j - M) = i + j by omega]
        rw [this]
        exact mul_le_of_le_one_right (pow_nonneg huinv0 _) (pow_le_one₀ huinv0 huinv1)
      calc ‖PowerSeries.coeff i S * PowerSeries.coeff j T‖ * (u⁻¹) ^ (i + j)
          ≤ ‖PowerSeries.coeff i S * PowerSeries.coeff j T‖ * (u⁻¹) ^ M :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = ‖PowerSeries.coeff i S * PowerSeries.coeff j T‖ / u ^ M := by
            rw [inv_pow, div_eq_mul_inv]
    · simp
  refine ⟨max Cf 0 * Bg + max Cf 0 * max Cg 0 + Bf * max Cg 0 + Bfg, ?_⟩
  filter_upwards [hCf, hCg, eventually_ge_atTop (1 : ℝ)] with u hfu hgu hu
  have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
  have hfu' : ‖f u - Pf u‖ ≤ max Cf 0 / u ^ M :=
    hfu.trans (div_le_div_of_nonneg_right (le_max_left Cf 0) (by positivity))
  have hgu' : ‖g u - Pg u‖ ≤ max Cg 0 / u ^ M :=
    hgu.trans (div_le_div_of_nonneg_right (le_max_left Cg 0) (by positivity))
  have h_id : f u * g u - Pfg u =
      (f u - Pf u) * Pg u + (f u - Pf u) * (g u - Pg u) + Pf u * (g u - Pg u) + (Pf u * Pg u - Pfg u) := by
    ring
  rw [h_id]
  have h1 : ‖(f u - Pf u) * Pg u‖ ≤ max Cf 0 * Bg / u ^ M := by
    rw [norm_mul]
    calc ‖f u - Pf u‖ * ‖Pg u‖ ≤ (max Cf 0 / u ^ M) * Bg :=
          mul_le_mul hfu' (hPg_bdd u hu) (norm_nonneg _) (div_nonneg (le_max_right _ _) (by positivity))
      _ = max Cf 0 * Bg / u ^ M := by ring
  have h2 : ‖(f u - Pf u) * (g u - Pg u)‖ ≤ max Cf 0 * max Cg 0 / u ^ M := by
    rw [norm_mul]
    have hc2 : ‖g u - Pg u‖ ≤ max Cg 0 := by
      calc ‖g u - Pg u‖ ≤ max Cg 0 / u ^ M := hgu'
        _ ≤ max Cg 0 / 1 := div_le_div_of_nonneg_left (le_max_right _ _) one_pos (one_le_pow₀ hu)
        _ = max Cg 0 := div_one _
    calc ‖f u - Pf u‖ * ‖g u - Pg u‖ ≤ (max Cf 0 / u ^ M) * max Cg 0 :=
          mul_le_mul hfu' hc2 (norm_nonneg _) (div_nonneg (le_max_right _ _) (by positivity))
      _ = max Cf 0 * max Cg 0 / u ^ M := by ring
  have h3 : ‖Pf u * (g u - Pg u)‖ ≤ Bf * max Cg 0 / u ^ M := by
    rw [norm_mul]
    calc ‖Pf u‖ * ‖g u - Pg u‖ ≤ Bf * (max Cg 0 / u ^ M) :=
          mul_le_mul (hPf_bdd u hu) hgu' (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ = Bf * max Cg 0 / u ^ M := by ring
  calc ‖(f u - Pf u) * Pg u + (f u - Pf u) * (g u - Pg u) + Pf u * (g u - Pg u) + (Pf u * Pg u - Pfg u)‖
      ≤ ‖(f u - Pf u) * Pg u‖ + ‖(f u - Pf u) * (g u - Pg u)‖ + ‖Pf u * (g u - Pg u)‖ +
          ‖Pf u * Pg u - Pfg u‖ := by
        linarith [norm_add_le ((f u - Pf u) * Pg u + (f u - Pf u) * (g u - Pg u) + Pf u * (g u - Pg u)) (Pf u * Pg u - Pfg u),
          norm_add_le ((f u - Pf u) * Pg u + (f u - Pf u) * (g u - Pg u)) (Pf u * (g u - Pg u)),
          norm_add_le ((f u - Pf u) * Pg u) ((f u - Pf u) * (g u - Pg u))]
    _ ≤ max Cf 0 * Bg / u ^ M + max Cf 0 * max Cg 0 / u ^ M + Bf * max Cg 0 / u ^ M + Bfg / u ^ M := by
        linarith [h1, h2, h3, hPdiff u hu]
    _ = _ := by ring

lemma HasAsympExp.mvPolynomial {r : ℕ} {f : Fin (r + 1) → ℝ → ℂ} {S : Fin (r + 1) → PowerSeries ℂ}
    (hf : ∀ j, HasAsympExp (f j) (S j)) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    HasAsympExp (fun u => MvPolynomial.eval (fun j => f j u) P) (MvPolynomial.aeval S P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using HasAsympExp.const c
  | add P Q hP hQ => simpa only [map_add] using! hP.add hQ
  | mul_X P j hP => simpa only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X] using! hP.mul (hf j)

lemma HasAsympExp.eq_zero_of_flat {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop, ‖f u‖ ≤ C / u ^ M) :
    S = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain ⟨Ca, hCa⟩ := hf (n + 1)
    obtain ⟨Cf, hCf⟩ := hflat (n + 1)
    have htrunc : ∀ᶠ u : ℝ in atTop,
        ‖PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n)‖ ≤ (Cf + Ca) / u ^ (n + 1) := by
      filter_upwards [hCa, hCf] with u ha hfl
      have hsum : ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k S * ((u : ℂ)⁻¹ ^ k) =
          PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n) := by
        rw [Finset.sum_range_succ]
        have hlow : ∑ k ∈ Finset.range n, PowerSeries.coeff k S * ((u : ℂ)⁻¹ ^ k) = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          rw [ih k (Finset.mem_range.mp hk), zero_mul]
        rw [hlow, zero_add]
      rw [hsum] at ha
      calc ‖PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n)‖
          = ‖f u - (f u - PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n))‖ := by congr 1; ring
        _ ≤ ‖f u‖ + ‖f u - PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n)‖ := norm_sub_le _ _
        _ ≤ Cf / u ^ (n + 1) + Ca / u ^ (n + 1) := add_le_add hfl ha
        _ = (Cf + Ca) / u ^ (n + 1) := by ring
    have hlim_c : Tendsto (fun u : ℝ => u ^ n * ‖PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n)‖) atTop
        (𝓝 ‖PowerSeries.coeff n S‖) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu,
        inv_pow]
      field_simp [(pow_pos hu n).ne']
    have hlim_0 : Tendsto (fun u : ℝ => u ^ n * ‖PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n)‖) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun u : ℝ => (Cf + Ca) / u) ?_ ?_
      · filter_upwards [htrunc, eventually_gt_atTop (0 : ℝ)] with u hu hpos
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hpos.le _) (norm_nonneg _))]
        calc u ^ n * ‖PowerSeries.coeff n S * ((u : ℂ)⁻¹ ^ n)‖
            ≤ u ^ n * ((Cf + Ca) / u ^ (n + 1)) := mul_le_mul_of_nonneg_left hu (pow_nonneg hpos.le _)
          _ = (Cf + Ca) / u := by rw [pow_succ]; field_simp [hpos.ne']
      · simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := Cf + Ca)).mul tendsto_inv_atTop_zero
    exact norm_eq_zero.mp (tendsto_nhds_unique hlim_c hlim_0)

@[expose] def aGamma : Minor := ⟨0, phi⟩
@[expose] def gPlus (u : ℂ) : ℂ := aGamma.value dPlus u
@[expose] def gMinus (u : ℂ) : ℂ := aGamma.value dMinus u
@[expose] def gPlusR (u : ℝ) : ℂ := gPlus (u : ℂ)
@[expose] def gMinusR (u : ℝ) : ℂ := gMinus (u : ℂ)

lemma aGamma_toSeries : aGamma.toSeries = gHat := by
  ext n
  cases n <;> simp [aGamma, Minor.toSeries, gHat]

lemma aGamma_good_UPlus : aGamma.Good UPlus dPlus := by
  refine ⟨phi_analyticOn_UPlus, ?_⟩
  obtain ⟨C, hC, hdec⟩ := phi_dPlus_decay 0
  refine ⟨C, 0, hC, le_rfl, fun v hv => ?_⟩
  simp only [Minor.pull, aGamma, norm_mul, norm_dPlus, one_mul, zero_mul, Real.exp_zero, mul_one]
  simpa using hdec v hv

lemma aGamma_good_UMinus : aGamma.Good UMinus dMinus := by
  refine ⟨phi_analyticOn_UMinus, ?_⟩
  obtain ⟨C, hC, hdec⟩ := phi_dMinus_decay 0
  refine ⟨C, 0, hC, le_rfl, fun v hv => ?_⟩
  simp only [Minor.pull, aGamma, norm_mul, norm_dMinus, one_mul, zero_mul, Real.exp_zero, mul_one]
  simpa using hdec v hv

lemma UPlus_domain : Domain UPlus := ⟨isOpen_UPlus, star_UPlus⟩
lemma UMinus_domain : Domain UMinus := ⟨isOpen_UMinus, star_UMinus⟩

private lemma analyticAt_eqOn_zero_of_iteratedDeriv_zero {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) :
    EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz
    simpa [smul_eq_mul] using hz
  have hdn : iteratedDeriv n f 0 = (n.factorial : ℂ) * g 0 := by
    rw [hloc.iteratedDeriv_eq n]
    have hmul := iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ))
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0).contDiffAt hg.contDiffAt
    rw [hmul]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ n) (0 : ℂ) * iteratedDeriv (n - i) g 0 =
          if i = n then (n.factorial : ℂ) * g 0 else 0 := by
      intro i _
      rw [iteratedDeriv_fun_pow_zero]
      split_ifs with hin
      · subst hin; simp [Nat.choose_self]
      · simp
    rw [Finset.sum_congr rfl hterm]
    simp
  have hzero := hderiv n
  rw [hdn] at hzero
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) hzero

lemma tendsto_coe_far {d : ℂ} (hd : 0 < d.re) :
    Tendsto ((↑) : ℝ → ℂ) atTop (far d) := by
  rw [far, tendsto_comap_iff]
  have heq : (fun u : ℝ => ((u : ℂ) * d).re) = fun u : ℝ => u * d.re := by
    funext u; simp [Complex.mul_re]
  change Tendsto (fun u : ℝ => ((u : ℂ) * d).re) atTop atTop
  rw [heq]
  exact tendsto_id.atTop_mul_const hd

lemma formalEval_zero_implies_gPlus_gMinus_zero {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval gHat P = 0) :
    (∀ᶠ u : ℝ in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val gPlusR u) P = 0) ∧
    (∀ᶠ u : ℝ in atTop, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val gMinusR u) P = 0) := by
  obtain ⟨e, hs, he⟩ := BorelExpr.exists_of_mvPolynomial P
  have hres_series : (e.residual aGamma).toSeries = 0 := by
    rw [hs UPlus dPlus aGamma UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus, aGamma_toSeries, hP]
  have hatom : (e.residual aGamma).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series
    simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual aGamma).density 0 = 0 := by
    intro k
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series
    simpa [Minor.toSeries] using this
  have hplus_dens : EqOn (e.residual aGamma).density 0 UPlus :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zero isPreconnected_UPlus
      (by simpa using UPlus_contains_dPlus 0 le_rfl)
      (e.represents UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus).1.1 hderiv_zero
  have hminus_dens : EqOn (e.residual aGamma).density 0 UMinus :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zero isPreconnected_UMinus
      (by simpa using UMinus_contains_dMinus 0 le_rfl)
      (e.represents UMinus_domain UMinus_contains_dMinus aGamma_good_UMinus).1.1 hderiv_zero
  constructor
  · have hrep := (tendsto_coe_far dPlus_re_pos).eventually
      (e.represents UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus).2
    filter_upwards [hrep, he UPlus dPlus aGamma UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus
      dPlus_re_pos] with u hu_rep hu_ev
    change MvPolynomial.eval
      (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => aGamma.value dPlus (t : ℂ)) u) P = 0
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hplus_dens (UPlus_contains_dPlus v hv.le)]
  · have hrep := (tendsto_coe_far dMinus_re_pos).eventually
      (e.represents UMinus_domain UMinus_contains_dMinus aGamma_good_UMinus).2
    filter_upwards [hrep, he UMinus dMinus aGamma UMinus_domain UMinus_contains_dMinus aGamma_good_UMinus
      dMinus_re_pos] with u hu_rep hu_ev
    change MvPolynomial.eval
      (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => aGamma.value dMinus (t : ℂ)) u) P = 0
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hminus_dens (UMinus_contains_dMinus v hv.le)]

lemma eval_gPlus_flat_implies_formalEval_zero {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℂ)
    (hQ : ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val gPlusR u) Q‖ ≤
        C * Real.exp (-u)) :
    formalEval gHat Q = 0 := by
  obtain ⟨C, hC⟩ := hQ
  obtain ⟨e, hs, he⟩ := BorelExpr.exists_of_mvPolynomial Q
  have hrep := (tendsto_coe_far dPlus_re_pos).eventually
    (e.represents UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus).2
  have hflat : ∀ M : ℕ, ∃ C_M : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖(e.residual aGamma).value dPlus (u : ℂ)‖ ≤ C_M / u ^ (M + 1) := by
    intro M
    refine ⟨max C 0 * ((M + 1).factorial : ℝ), ?_⟩
    filter_upwards [hC, hrep, he UPlus dPlus aGamma UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus
      dPlus_re_pos, eventually_gt_atTop (0 : ℝ)] with u huC hurep huev hupos
    rw [← hurep, huev]
    have hexp : Real.exp (-u) ≤ ((M + 1).factorial : ℝ) / u ^ (M + 1) := by
      have harg := Real.pow_div_factorial_le_exp u hupos.le (M + 1)
      have hfac : 0 < ((M + 1).factorial : ℝ) := by positivity
      have hpow : 0 < u ^ (M + 1) := pow_pos hupos _
      rw [Real.exp_neg u]
      calc (Real.exp u)⁻¹ ≤ (u ^ (M + 1) / ((M + 1).factorial : ℝ))⁻¹ :=
            inv_anti₀ (div_pos hpow hfac) harg
        _ = ((M + 1).factorial : ℝ) / u ^ (M + 1) := inv_div _ _
    calc ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val gPlusR u) Q‖
        ≤ C * Real.exp (-u) := huC
      _ ≤ max C 0 * Real.exp (-u) := mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 * (((M + 1).factorial : ℝ) / u ^ (M + 1)) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right C 0)
      _ = (max C 0 * ((M + 1).factorial : ℝ)) / u ^ (M + 1) := by ring
  have hzero := Minor.toSeries_eq_zero_of_flat (e.residual aGamma) UPlus_domain UPlus_contains_dPlus
    (e.represents UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus).1 dPlus_re_pos hflat
  rwa [hs UPlus dPlus aGamma UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus,
    aGamma_toSeries] at hzero

lemma gPlusR_bounded_derivatives (j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop, ‖iteratedDeriv j gPlusR u‖ ≤ C := by
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have ha := (e.represents UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus).1
  obtain ⟨C₀, _, hC₀⟩ := Minor.value_asymptotic (e.residual aGamma) UPlus_domain UPlus_contains_dPlus
    ha dPlus_re_pos 0
  have hrep := (tendsto_coe_far dPlus_re_pos).eventually
    (e.represents UPlus_domain UPlus_contains_dPlus aGamma_good_UPlus).2
  have heq := (BorelExpr.jetIter_eval_eq_iteratedDeriv aGamma UPlus_domain UPlus_contains_dPlus
    aGamma_good_UPlus dPlus_re_pos j).1
  refine ⟨‖(e.residual aGamma).atom‖ + C₀, ?_⟩
  filter_upwards [hC₀, hrep, heq, eventually_ge_atTop (1 : ℝ)] with u hu0 hurep hueq hu1
  have heq' : iteratedDeriv j gPlusR u = (e.residual aGamma).value dPlus (u : ℂ) :=
    hueq.symm.trans hurep
  rw [heq']
  have hu0' : ‖(e.residual aGamma).value dPlus (u : ℂ) - (e.residual aGamma).atom‖ ≤ C₀ := by
    simpa using hu0.trans (div_le_self (by
      have h0 : 0 ≤ ‖(e.residual aGamma).value dPlus (u : ℂ) - (e.residual aGamma).atom‖ := norm_nonneg _
      have := h0.trans (by simpa using hu0 : _ ≤ C₀ / u)
      exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith)) (one_le_pow₀ hu1))
  calc ‖(e.residual aGamma).value dPlus (u : ℂ)‖
      = ‖((e.residual aGamma).value dPlus (u : ℂ) - (e.residual aGamma).atom) + (e.residual aGamma).atom‖ := by
        congr 1; ring
    _ ≤ ‖(e.residual aGamma).value dPlus (u : ℂ) - (e.residual aGamma).atom‖ + ‖(e.residual aGamma).atom‖ :=
        norm_add_le _ _
    _ ≤ ‖(e.residual aGamma).atom‖ + C₀ := by linarith

lemma gPlusR_gMinusR_eventually_differentiable (k : ℕ) :
    (∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv k gPlusR) u) ∧
    (∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ (iteratedDeriv k gMinusR) u) :=
  ⟨(BorelExpr.jetIter_eval_eq_iteratedDeriv aGamma UPlus_domain UPlus_contains_dPlus
      aGamma_good_UPlus dPlus_re_pos k).2,
   (BorelExpr.jetIter_eval_eq_iteratedDeriv aGamma UMinus_domain UMinus_contains_dMinus
      aGamma_good_UMinus dMinus_re_pos k).2⟩

/-! ### 5. Cauchy Residue Theorem & Exact Stokes Jump -/

/-- Counter-clockwise rectangle boundary integral `(bottom - top) + i (right - left)`. -/
@[expose] def rectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (z.im : ℂ) * I)) -
    (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (w.im : ℂ) * I)) +
    I * (∫ y : ℝ in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * I)) -
    I * (∫ y : ℝ in z.im..w.im, f ((z.re : ℂ) + (y : ℂ) * I))

lemma rectIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {z w : ℂ}
    (hf : DifferentiableOn ℂ f (uIcc z.re w.re ×ℂ uIcc z.im w.im)) :
    rectIntegral f z w = 0 := by
  simpa [rectIntegral, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf

lemma rectIntegral_sub_rectIntegral {f g : ℂ → ℂ} {z w : ℂ}
    (hb₁ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (hb₂ : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (ht₁ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (ht₂ : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (hr₁ : IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hr₂ : IntervalIntegrable (fun y : ℝ => g ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hl₁ : IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hl₂ : IntervalIntegrable (fun y : ℝ => g ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im) :
    rectIntegral (fun ζ => f ζ - g ζ) z w = rectIntegral f z w - rectIntegral g z w := by
  unfold rectIntegral
  rw [intervalIntegral.integral_sub hb₁ hb₂, intervalIntegral.integral_sub ht₁ ht₂,
    intervalIntegral.integral_sub hr₁ hr₂, intervalIntegral.integral_sub hl₁ hl₂]
  ring

lemma rectIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectIntegral (fun ζ => c * f ζ) z w = c * rectIntegral f z w := by
  unfold rectIntegral
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

lemma rectIntegral_hsplit {f : ℂ → ℂ} {x₁ x₀ x₂ y₁ y₂ : ℝ}
    (hb₁ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y₁ : ℂ) * I)) volume x₁ x₀)
    (hb₂ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y₁ : ℂ) * I)) volume x₀ x₂)
    (ht₁ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y₂ : ℂ) * I)) volume x₁ x₀)
    (ht₂ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y₂ : ℂ) * I)) volume x₀ x₂) :
    rectIntegral f ((x₁ : ℂ) + (y₁ : ℂ) * I) ((x₂ : ℂ) + (y₂ : ℂ) * I) =
      rectIntegral f ((x₁ : ℂ) + (y₁ : ℂ) * I) ((x₀ : ℂ) + (y₂ : ℂ) * I) +
      rectIntegral f ((x₀ : ℂ) + (y₁ : ℂ) * I) ((x₂ : ℂ) + (y₂ : ℂ) * I) := by
  unfold rectIntegral
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, Complex.ofReal_im, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rw [← intervalIntegral.integral_add_adjacent_intervals hb₁ hb₂,
    ← intervalIntegral.integral_add_adjacent_intervals ht₁ ht₂]
  ring

private lemma inv_real_add_mul_I {u v : ℝ} (huv : u ^ 2 + v ^ 2 ≠ 0) :
    ((u : ℂ) + (v : ℂ) * I)⁻¹ =
      ((u / (u ^ 2 + v ^ 2) : ℝ) : ℂ) - ((v / (u ^ 2 + v ^ 2) : ℝ) : ℂ) * I := by
  have huvc : ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) ≠ 0 := by exact_mod_cast huv
  symm
  apply eq_inv_of_mul_eq_one_left
  push_cast
  field_simp [huvc]
  rw [show ((u : ℂ) - (v : ℂ) * I) * ((u : ℂ) + (v : ℂ) * I) =
    (u : ℂ) ^ 2 - (v : ℂ) ^ 2 * I ^ 2 by ring, Complex.I_sq]
  ring

private lemma odd_intervalIntegral_zero {f : ℝ → ℝ} {b : ℝ}
    (hf : ∀ y : ℝ, f (-y) = -f y) :
    ∫ y in (-b)..b, f y = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg f (a := -b) (b := b)
  simp only [neg_neg, hf, intervalIntegral.integral_neg] at hcomp
  linarith

private lemma arctan_div_integral (a b d : ℝ) (hd : d ≠ 0) :
    ∫ t in a..b, d / (d ^ 2 + t ^ 2) = Real.arctan (b / d) - Real.arctan (a / d) := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun x : ℝ => Real.arctan (x / d)) (d / (d ^ 2 + t ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x / d) d⁻¹ t := by
      simpa using (hasDerivAt_id t).div_const d
    have h2 := h1.arctan
    convert h2 using 1
    have hden : d ^ 2 + t ^ 2 ≠ 0 := by positivity
    have hden1 : 1 + (t / d) ^ 2 ≠ 0 := by positivity
    field_simp [hd, hden, hden1]
  have hcont : Continuous (fun t : ℝ => d / (d ^ 2 + t ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_pow 2)) fun t => by positivity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)

private lemma arctan_shift_div_integral (a₁ a₂ c b : ℝ) (hb : b ≠ 0) :
    ∫ x in a₁..a₂, b / ((x - c) ^ 2 + b ^ 2) =
      Real.arctan ((a₂ - c) / b) - Real.arctan ((a₁ - c) / b) := by
  have hderiv : ∀ x ∈ uIcc a₁ a₂,
      HasDerivAt (fun t : ℝ => Real.arctan ((t - c) / b)) (b / ((x - c) ^ 2 + b ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t - c) / b) b⁻¹ x := by
      simpa using ((hasDerivAt_id x).sub_const c).div_const b
    have h2 := h1.arctan
    convert h2 using 1
    have hden : (x - c) ^ 2 + b ^ 2 ≠ 0 := by positivity
    have hden1 : 1 + ((x - c) / b) ^ 2 ≠ 0 := by positivity
    field_simp [hb, hden, hden1]
    ring
  have hcont : Continuous (fun x : ℝ => b / ((x - c) ^ 2 + b ^ 2)) :=
    continuous_const.div (((continuous_id.sub continuous_const).pow 2).add continuous_const)
      fun x => by positivity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a₁ a₂)

/-- Elementary `arctan` residue formula for `∫_∂R (ζ - c₀)⁻¹ dζ = 2πi`. -/
lemma rectIntegral_inv_sub {a₁ c₀ a₂ b : ℝ} (ha₁ : a₁ < c₀) (ha₂ : c₀ < a₂) (hb : 0 < b) :
    rectIntegral (fun ζ => (ζ - (c₀ : ℂ))⁻¹) ((a₁ : ℂ) - (b : ℂ) * I) ((a₂ : ℂ) + (b : ℂ) * I) =
      2 * (Real.pi : ℂ) * I := by
  unfold rectIntegral
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, Complex.ofReal_im, sub_zero, sub_self, Complex.add_re, add_zero,
    Complex.sub_im, Complex.mul_im, mul_one, zero_sub, Complex.add_im, zero_add]
  have hc1 : Continuous (fun x : ℝ => (((x : ℂ) + ((-b : ℝ) : ℂ) * I) - (c₀ : ℂ))⁻¹) :=
    Continuous.inv₀ (by fun_prop) fun x h0 => by
      have him := congrArg Complex.im h0; simp at him; linarith
  have hc2 : Continuous (fun x : ℝ => (((x : ℂ) + (b : ℂ) * I) - (c₀ : ℂ))⁻¹) :=
    Continuous.inv₀ (by fun_prop) fun x h0 => by
      have him := congrArg Complex.im h0; simp at him; linarith
  have hhoriz : (∫ x : ℝ in a₁..a₂, (((x : ℂ) + ((-b : ℝ) : ℂ) * I) - (c₀ : ℂ))⁻¹) -
      (∫ x : ℝ in a₁..a₂, (((x : ℂ) + (b : ℂ) * I) - (c₀ : ℂ))⁻¹) =
      ((2 * (Real.arctan ((a₂ - c₀) / b) + Real.arctan ((c₀ - a₁) / b)) : ℝ) : ℂ) * I := by
    rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable a₁ a₂) (hc2.intervalIntegrable a₁ a₂)]
    have hcongr : (fun x : ℝ => (((x : ℂ) + ((-b : ℝ) : ℂ) * I) - (c₀ : ℂ))⁻¹ -
          (((x : ℂ) + (b : ℂ) * I) - (c₀ : ℂ))⁻¹) =
        fun x : ℝ => ((2 * (b / ((x - c₀) ^ 2 + b ^ 2)) : ℝ) : ℂ) * I := by
      funext x
      have huv : (x - c₀) ^ 2 + b ^ 2 ≠ 0 := by positivity
      have huv' : (x - c₀) ^ 2 + (-b) ^ 2 ≠ 0 := by rw [neg_sq]; positivity
      have hL := inv_real_add_mul_I (u := x - c₀) (v := -b) huv'
      have hR := inv_real_add_mul_I (u := x - c₀) (v := b) huv
      have he1 : ((x : ℂ) + ((-b : ℝ) : ℂ) * I) - (c₀ : ℂ) = (((x - c₀ : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * I) := by
        push_cast; ring
      have he2 : ((x : ℂ) + (b : ℂ) * I) - (c₀ : ℂ) = (((x - c₀ : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) := by
        push_cast; ring
      rw [he1, he2, hL, hR]
      push_cast
      simp only [neg_sq]
      ring
    rw [hcongr, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul, arctan_shift_div_integral a₁ a₂ c₀ b hb.ne']
    have hneg : -Real.arctan ((a₁ - c₀) / b) = Real.arctan ((c₀ - a₁) / b) := by
      rw [← Real.arctan_neg]; congr 1; ring
    rw [sub_eq_add_neg, hneg]
  let d₂ : ℝ := a₂ - c₀
  let d₁ : ℝ := c₀ - a₁
  have hd₂ : 0 < d₂ := sub_pos.mpr ha₂
  have hd₁ : 0 < d₁ := sub_pos.mpr ha₁
  have hright : I * (∫ y : ℝ in (-b)..b, (((a₂ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹) =
      ((2 * Real.arctan (b / d₂) : ℝ) : ℂ) * I := by
    rw [← intervalIntegral.integral_const_mul]
    have hcongr : (fun y : ℝ => I * (((a₂ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹) =
        fun y : ℝ => ((y / (d₂ ^ 2 + y ^ 2) : ℝ) : ℂ) + ((d₂ / (d₂ ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
      funext y
      have he : ((a₂ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ) = ((d₂ : ℂ) + (y : ℂ) * I) := by
        dsimp only [d₂]; push_cast; ring
      rw [he, inv_real_add_mul_I (u := d₂) (v := y) (ne_of_gt (by linarith [sq_pos_of_pos hd₂, sq_nonneg y]))]
      push_cast
      rw [show I * ((d₂ / (d₂ ^ 2 + y ^ 2) : ℂ) - (y / (d₂ ^ 2 + y ^ 2) : ℂ) * I) =
        (d₂ / (d₂ ^ 2 + y ^ 2) : ℂ) * I - (y / (d₂ ^ 2 + y ^ 2) : ℂ) * I ^ 2 by ring,
        Complex.I_sq]
      ring
    rw [hcongr]
    have hiA : IntervalIntegrable (fun y : ℝ => ((y / (d₂ ^ 2 + y ^ 2) : ℝ) : ℂ)) volume (-b) b :=
      (Complex.continuous_ofReal.comp (continuous_id.div (continuous_const.add (continuous_pow 2))
        fun y => by dsimp; exact ne_of_gt (by positivity))).intervalIntegrable (-b) b
    have hiB : IntervalIntegrable (fun y : ℝ => ((d₂ / (d₂ ^ 2 + y ^ 2) : ℝ) : ℂ) * I) volume (-b) b :=
      ((Complex.continuous_ofReal.comp (continuous_const.div (continuous_const.add (continuous_pow 2))
        fun y => by dsimp; exact ne_of_gt (by positivity))).mul continuous_const).intervalIntegrable (-b) b
    rw [intervalIntegral.integral_add hiA hiB, intervalIntegral.integral_ofReal,
      odd_intervalIntegral_zero (fun y => by ring), Complex.ofReal_zero, zero_add,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      arctan_div_integral (-b) b d₂ hd₂.ne']
    have hneg : Real.arctan (-b / d₂) = -Real.arctan (b / d₂) := by
      rw [← Real.arctan_neg]; congr 1; ring
    rw [hneg, sub_neg_eq_add, ← two_mul]
  have hleft : -(I * (∫ y : ℝ in (-b)..b, (((a₁ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹)) =
      ((2 * Real.arctan (b / d₁) : ℝ) : ℂ) * I := by
    rw [← neg_mul, ← intervalIntegral.integral_const_mul]
    have hcongr : (fun y : ℝ => -I * (((a₁ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹) =
        fun y : ℝ => ((-y / (d₁ ^ 2 + y ^ 2) : ℝ) : ℂ) + ((d₁ / (d₁ ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
      funext y
      have he : ((a₁ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ) = (((-d₁ : ℝ) : ℂ) + (y : ℂ) * I) := by
        dsimp only [d₁]; push_cast; ring
      rw [he, inv_real_add_mul_I (u := -d₁) (v := y) (ne_of_gt (by rw [neg_sq]; linarith [sq_pos_of_pos hd₁, sq_nonneg y]))]
      push_cast
      rw [neg_sq, show -I * (((-(d₁ : ℂ) / (d₁ ^ 2 + y ^ 2)) - (y / (d₁ ^ 2 + y ^ 2)) * I)) =
        (y / (d₁ ^ 2 + y ^ 2)) * I ^ 2 + (d₁ / (d₁ ^ 2 + y ^ 2)) * I by ring, Complex.I_sq]
      ring
    rw [hcongr]
    have hiA : IntervalIntegrable (fun y : ℝ => ((-y / (d₁ ^ 2 + y ^ 2) : ℝ) : ℂ)) volume (-b) b :=
      (Complex.continuous_ofReal.comp (continuous_id.neg.div (continuous_const.add (continuous_pow 2))
        fun y => by dsimp; exact ne_of_gt (by positivity))).intervalIntegrable (-b) b
    have hiB : IntervalIntegrable (fun y : ℝ => ((d₁ / (d₁ ^ 2 + y ^ 2) : ℝ) : ℂ) * I) volume (-b) b :=
      ((Complex.continuous_ofReal.comp (continuous_const.div (continuous_const.add (continuous_pow 2))
        fun y => by dsimp; exact ne_of_gt (by positivity))).mul continuous_const).intervalIntegrable (-b) b
    rw [intervalIntegral.integral_add hiA hiB, intervalIntegral.integral_ofReal,
      odd_intervalIntegral_zero (fun y => by ring), Complex.ofReal_zero, zero_add,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      arctan_div_integral (-b) b d₁ hd₁.ne']
    have hneg : Real.arctan (-b / d₁) = -Real.arctan (b / d₁) := by
      rw [← Real.arctan_neg]; congr 1; ring
    rw [hneg, sub_neg_eq_add, ← two_mul]
  calc (∫ x in a₁..a₂, (((x : ℂ) + ((-b : ℝ) : ℂ) * I) - (c₀ : ℂ))⁻¹) -
          (∫ x in a₁..a₂, (((x : ℂ) + (b : ℂ) * I) - (c₀ : ℂ))⁻¹) +
          I * (∫ y in (-b)..b, (((a₂ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹) -
          I * (∫ y in (-b)..b, (((a₁ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹)
      = ((∫ x in a₁..a₂, (((x : ℂ) + ((-b : ℝ) : ℂ) * I) - (c₀ : ℂ))⁻¹) -
          (∫ x in a₁..a₂, (((x : ℂ) + (b : ℂ) * I) - (c₀ : ℂ))⁻¹)) +
          (I * (∫ y in (-b)..b, (((a₂ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹)) +
          (-(I * (∫ y in (-b)..b, (((a₁ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹))) := by ring
    _ = ((2 * (Real.arctan (d₂ / b) + Real.arctan (d₁ / b)) : ℝ) : ℂ) * I +
          ((2 * Real.arctan (b / d₂) : ℝ) : ℂ) * I +
          ((2 * Real.arctan (b / d₁) : ℝ) : ℂ) * I := by rw [hhoriz, hright, hleft]
    _ = ((2 * ((Real.arctan (d₂ / b) + Real.arctan (b / d₂)) +
            (Real.arctan (d₁ / b) + Real.arctan (b / d₁))) : ℝ) : ℂ) * I := by
          push_cast; ring
    _ = 2 * (Real.pi : ℂ) * I := by
          have ha2' : Real.arctan (b / d₂) = Real.pi / 2 - Real.arctan (d₂ / b) := by
            simpa [one_div, inv_div] using Real.arctan_inv_of_pos (div_pos hd₂ hb)
          have ha1' : Real.arctan (b / d₁) = Real.pi / 2 - Real.arctan (d₁ / b) := by
            simpa [one_div, inv_div] using Real.arctan_inv_of_pos (div_pos hd₁ hb)
          rw [ha2', ha1']
          push_cast; ring

/-- Exponential-ray Stokes coefficients `c_m = 2πi (-1)^m / (m - 1)!`. -/
@[expose] def cGamma (m : ℕ) : ℂ :=
  2 * (Real.pi : ℂ) * I * (-1 : ℂ) ^ m / ((m - 1).factorial : ℂ)

lemma cGamma_ne_zero {m : ℕ} : cGamma m ≠ 0 := by
  unfold cGamma
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (-1 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hfac : ((m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - 1)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hpow) hfac

/-- Log-polar rectangle integrand for `g_-(u) - g_+(u)`. -/
@[expose] def rectH (u z : ℂ) : ℂ :=
  Complex.exp (z - u * Complex.exp z) * phi (Complex.exp z)

private lemma exp_eq_natCast_iff_of_abs_im_lt_pi {z : ℂ} (hy : |z.im| < Real.pi)
    {n : ℕ} (hn : 1 ≤ n) :
    Complex.exp z = (n : ℂ) ↔ z = (Real.log n : ℂ) := by
  constructor
  · intro hz
    have hnorm : Real.exp z.re = (n : ℝ) := by
      have := congrArg norm hz
      rw [Complex.norm_exp, Complex.norm_natCast] at this
      exact this
    have hzre : z.re = Real.log n := by
      rw [← hnorm, Real.log_exp]
    have him : Real.exp z.re * Real.sin z.im = 0 := by
      have := congrArg Complex.im hz
      rw [Complex.exp_im] at this
      simpa using this
    have hsin : Real.sin z.im = 0 := (mul_eq_zero.mp him).resolve_left (Real.exp_pos _).ne'
    have hzim : z.im = 0 := by
      rcases lt_trichotomy z.im 0 with hlt | heq | hgt
      · exfalso
        have h1 : 0 < -z.im := neg_pos.mpr hlt
        have h2 : -z.im < Real.pi := by linarith [(abs_lt.mp hy).1]
        have hs : 0 < Real.sin (-z.im) := Real.sin_pos_of_pos_of_lt_pi h1 h2
        rw [Real.sin_neg, hsin, neg_zero] at hs
        exact lt_irrefl _ hs
      · exact heq
      · exfalso
        have h2 : z.im < Real.pi := (abs_lt.mp hy).2
        have hs : 0 < Real.sin z.im := Real.sin_pos_of_pos_of_lt_pi hgt h2
        linarith
    apply Complex.ext
    · rw [hzre]; exact (Complex.ofReal_re (Real.log n)).symm
    · rw [hzim]; exact (Complex.ofReal_im (Real.log n)).symm
  · rintro rfl
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Complex.ofReal_exp, Real.exp_log hn0]
    norm_cast

private lemma rectH_zero_cell (u : ℂ) {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2) :
    rectIntegral (rectH u) ((Real.log ε : ℂ) - (theta4 : ℂ) * I)
      ((Real.log (1 / 2) : ℂ) + (theta4 : ℂ) * I) = 0 := by
  refine rectIntegral_eq_zero_of_differentiableOn ?_
  intro z hz
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, Complex.ofReal_im, sub_zero, sub_self, Complex.add_re, add_zero,
    Complex.sub_im, Complex.mul_im, mul_one, zero_sub, Complex.add_im, zero_add] at hz
  have hre_le : z.re ≤ Real.log (1 / 2) := by
    have hle : Real.log ε ≤ Real.log (1 / 2) := Real.log_le_log hε hε_le
    rw [uIcc_of_le hle] at hz
    exact hz.1.2
  have hnorm_lt : ‖Complex.exp z‖ < 1 := by
    rw [Complex.norm_exp]
    calc Real.exp z.re ≤ Real.exp (Real.log (1 / 2)) := Real.exp_le_exp.mpr hre_le
      _ = 1 / 2 := Real.exp_log (by norm_num)
      _ < 1 := by norm_num
  have hphi : DifferentiableAt ℂ phi (Complex.exp z) := by
    refine (phi_analyticAt_of_avoids_posNat fun n hn => ?_).differentiableAt
    intro h
    have : ‖Complex.exp z‖ = (n : ℝ) := by rw [h, Complex.norm_natCast]
    have : (n : ℝ) < 1 := this ▸ hnorm_lt
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hd : DifferentiableAt ℂ (rectH u) z :=
    (Complex.differentiableAt_exp.comp z
      (differentiableAt_id.sub (differentiableAt_const u |>.mul Complex.differentiableAt_exp))).mul
      (hphi.comp z Complex.differentiableAt_exp)
  exact hd.differentiableWithinAt

private lemma prod_range_sub_nat (k : ℕ) :
    ∏ j ∈ Finset.range k, ((j + 1 : ℂ) - ((k + 1 : ℕ) : ℂ)) =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmem : ∀ j ∈ Finset.range (k + 1),
        ((j + 1 : ℂ) - ((k + 1 + 1 : ℕ) : ℂ)) = -(((k + 1 - j : ℕ) : ℂ)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have : k + 1 + 1 = (k + 1 - j) + (j + 1) := by omega
      push_cast [this]
      ring
    trans ∏ j ∈ Finset.range (k + 1), -(((k + 1 - j : ℕ) : ℂ))
    · exact Finset.prod_congr rfl fun j hj => by simpa using hmem j hj
    · rw [Finset.prod_neg, Finset.card_range]
      congr 1
      have hreflect := Finset.prod_range_reflect (fun m : ℕ => ((m + 1 : ℕ) : ℂ)) (k + 1)
      have hcongr : ∏ j ∈ Finset.range (k + 1), (((k + 1 - j : ℕ) : ℂ)) =
          ∏ j ∈ Finset.range (k + 1), (((k + 1 - 1 - j + 1 : ℕ) : ℂ)) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        congr 1
        omega
      rw [hcongr, hreflect]
      clear hcongr hreflect hmem ih
      induction (k + 1) with
      | zero => simp
      | succ m ihm =>
        rw [Finset.prod_range_succ, ihm, Nat.factorial_succ]
        push_cast; ring

private lemma rectH_pole_cell (u : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    rectIntegral (rectH u) ((Real.log ((k : ℝ) - 1 / 2) : ℂ) - (theta4 : ℂ) * I)
      ((Real.log ((k : ℝ) + 1 / 2) : ℂ) + (theta4 : ℂ) * I) =
      cGamma k * Complex.exp (-(k : ℂ) * u) := by
  let a₁ : ℝ := Real.log ((k : ℝ) - 1 / 2)
  let c₀ : ℝ := Real.log (k : ℝ)
  let a₂ : ℝ := Real.log ((k : ℝ) + 1 / 2)
  have hk_real : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_sub_pos : 0 < (k : ℝ) - 1 / 2 := by linarith
  have hk_pos : 0 < (k : ℝ) := by linarith
  have hk_add_pos : 0 < (k : ℝ) + 1 / 2 := by linarith
  have ha₁ : a₁ < c₀ := Real.log_lt_log hk_sub_pos (by linarith)
  have ha₂ : c₀ < a₂ := Real.log_lt_log hk_pos (by linarith)
  let rect : Set ℂ := uIcc a₁ a₂ ×ℂ uIcc (-theta4) theta4
  let O : Set ℂ :=
    {z : ℂ | (k : ℝ) - 3 / 4 < Real.exp z.re ∧ Real.exp z.re < (k : ℝ) + 3 / 4 ∧ |z.im| < Real.pi / 2}
  have hO_open : IsOpen O :=
    (isOpen_lt continuous_const (Real.continuous_exp.comp Complex.continuous_re)).inter
      ((isOpen_lt (Real.continuous_exp.comp Complex.continuous_re) continuous_const).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hc₀_mem : (c₀ : ℂ) ∈ O := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [c₀, Complex.ofReal_re, Real.exp_log hk_pos]; linarith
    · simp only [c₀, Complex.ofReal_re, Real.exp_log hk_pos]; linarith
    · simp [Real.pi_pos]
  have hrect_sub_O : rect ⊆ O := by
    intro z hz
    simp only [rect, uIcc_of_le (ha₁.trans ha₂).le, uIcc_of_le (by linarith [theta4_pos] : -(theta4) ≤ theta4),
      mem_reProdIm, mem_Icc] at hz
    have hre_lo : (k : ℝ) - 1 / 2 ≤ Real.exp z.re := by
      calc (k : ℝ) - 1 / 2 = Real.exp a₁ := (Real.exp_log hk_sub_pos).symm
        _ ≤ Real.exp z.re := Real.exp_le_exp.mpr hz.1.1
    have hre_hi : Real.exp z.re ≤ (k : ℝ) + 1 / 2 := by
      calc Real.exp z.re ≤ Real.exp a₂ := Real.exp_le_exp.mpr hz.1.2
        _ = (k : ℝ) + 1 / 2 := Real.exp_log hk_add_pos
    have him : |z.im| < Real.pi / 2 := by
      have : |z.im| ≤ theta4 := abs_le.mpr hz.2
      have hth : theta4 < Real.pi / 2 := by unfold theta4; linarith [Real.pi_pos]
      linarith
    exact ⟨by linarith, by linarith, him⟩
  let denomProd (ξ : ℂ) : ℂ := ∏ j ∈ Finset.range (k - 1), ((j + 1 : ℂ) - ξ)
  let G_cell (ξ : ℂ) : ℂ := -(Complex.Gamma ((k + 1 : ℂ) - ξ) / denomProd ξ)
  let D_exp (z : ℂ) : ℂ := dslope Complex.exp (c₀ : ℂ) z
  let M_cell (z : ℂ) : ℂ := Complex.exp (z - u * Complex.exp z) * G_cell (Complex.exp z) / D_exp z
  have hD_diff : Differentiable ℂ D_exp := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 (c₀ : ℂ))).mpr
      Complex.differentiable_exp.differentiableOn
  have hD_nz : ∀ z ∈ O, D_exp z ≠ 0 := by
    intro z hz h0
    by_cases hzc : z = (c₀ : ℂ)
    · subst hzc
      dsimp only [D_exp] at h0
      rw [dslope_same, (Complex.hasDerivAt_exp _).deriv] at h0
      exact Complex.exp_ne_zero _ h0
    · have hmul : Complex.exp z - Complex.exp (c₀ : ℂ) = 0 := by
        have hs := sub_smul_dslope Complex.exp (c₀ : ℂ) z
        rw [show dslope Complex.exp (c₀ : ℂ) z = D_exp z from rfl, h0, smul_zero] at hs
        exact hs.symm
      have hexp : Complex.exp z = (k : ℂ) := by
        have hc : Complex.exp (c₀ : ℂ) = (k : ℂ) := by
          rw [← Complex.ofReal_exp, Real.exp_log hk_pos]; norm_cast
        rw [sub_eq_zero] at hmul
        exact hmul.trans hc
      have hbad := (exp_eq_natCast_iff_of_abs_im_lt_pi (hz.2.2.trans (by linarith [Real.pi_pos])) hk).mp hexp
      exact hzc (by simpa [c₀] using hbad)
  have hdenom_nz : ∀ z ∈ O, denomProd (Complex.exp z) ≠ 0 := by
    intro z hz
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_range] at hj
    intro h0
    have hexp_eq : Complex.exp z = ((j + 1 : ℕ) : ℂ) := by
      push_cast; linear_combination -h0
    have hnorm : ‖Complex.exp z‖ = ((j + 1 : ℕ) : ℝ) := by
      rw [hexp_eq, Complex.norm_natCast]
    rw [Complex.norm_exp] at hnorm
    have hj_le : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
      have : j + 1 ≤ k - 1 := by omega
      exact_mod_cast this
    linarith [hz.1]
  have hGamma_diff : ∀ z ∈ O, DifferentiableAt ℂ (fun ζ => Complex.Gamma ((k + 1 : ℂ) - Complex.exp ζ)) z := by
    intro z hz
    have hre : 0 < ((k + 1 : ℂ) - Complex.exp z).re := by
      rw [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.exp_re]
      have hcos : Real.cos z.im ≤ 1 := Real.cos_le_one z.im
      have hmul : Real.exp z.re * Real.cos z.im ≤ Real.exp z.re :=
        mul_le_of_le_one_right (Real.exp_pos _).le hcos
      linarith [hz.2.1]
    have hg := Complex.differentiableAt_Gamma _ (fun m hm => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith)
    exact hg.comp z (differentiableAt_const _ |>.sub Complex.differentiableAt_exp)
  have hM_diffOn : DifferentiableOn ℂ M_cell O := by
    intro z hz
    refine (DifferentiableAt.differentiableWithinAt ?_)
    have hnum1 : DifferentiableAt ℂ (fun ζ => Complex.exp (ζ - u * Complex.exp ζ)) z :=
      Complex.differentiableAt_exp.comp z
        (differentiableAt_id.sub (differentiableAt_const u |>.mul Complex.differentiableAt_exp))
    have hdenom_diff : DifferentiableAt ℂ (fun ζ => denomProd (Complex.exp ζ)) z := by
      have h_all : ∀ n : ℕ, DifferentiableAt ℂ (fun ζ => ∏ j ∈ Finset.range n, ((j + 1 : ℂ) - Complex.exp ζ)) z := by
        intro n
        induction n with
        | zero => simp [differentiableAt_const]
        | succ n ihn =>
          simp_rw [Finset.prod_range_succ]
          exact ihn.mul ((differentiableAt_const _).sub Complex.differentiableAt_exp)
      exact h_all (k - 1)
    have hG_diff : DifferentiableAt ℂ (fun ζ => G_cell (Complex.exp ζ)) z :=
      ((hGamma_diff z hz).div hdenom_diff (hdenom_nz z hz)).neg
    exact (hnum1.mul hG_diff).div (hD_diff z) (hD_nz z hz)
  have hSlope_diff : DifferentiableOn ℂ (dslope M_cell (c₀ : ℂ)) rect :=
    ((differentiableOn_dslope (hO_open.mem_nhds hc₀_mem)).mpr hM_diffOn).mono hrect_sub_O
  have hRect0 : rectIntegral (dslope M_cell (c₀ : ℂ))
      ((a₁ : ℂ) - (theta4 : ℂ) * I) ((a₂ : ℂ) + (theta4 : ℂ) * I) = 0 := by
    apply rectIntegral_eq_zero_of_differentiableOn
    simpa [rect] using hSlope_diff
  have hD_eq : ∀ z : ℂ, z ≠ (c₀ : ℂ) → (z - (c₀ : ℂ)) * D_exp z = Complex.exp z - (k : ℂ) := by
    intro z _
    have hs := sub_smul_dslope Complex.exp (c₀ : ℂ) z
    have hc : Complex.exp (c₀ : ℂ) = (k : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hk_pos]; norm_cast
    simpa [D_exp, hc, smul_eq_mul] using hs
  have hH_on_ne : ∀ z ∈ O, z ≠ (c₀ : ℂ) →
      dslope M_cell (c₀ : ℂ) z =
        rectH u z - M_cell (c₀ : ℂ) * (z - (c₀ : ℂ))⁻¹ := by
    intro z hz hzne
    have hsub_ne : z - (c₀ : ℂ) ≠ 0 := sub_ne_zero.mpr hzne
    rw [dslope_of_ne M_cell hzne, slope_def_field]
    have hexp_ne_nat : ∀ n : ℕ, 1 ≤ n → Complex.exp z ≠ (n : ℂ) := by
      intro n hn hexp
      have hzn := (exp_eq_natCast_iff_of_abs_im_lt_pi (hz.2.2.trans (by linarith [Real.pi_pos])) hn).mp hexp
      by_cases hnk : n = k
      · subst hnk; exact hzne (by simpa [c₀] using hzn)
      · have hnorm : Real.exp z.re = (n : ℝ) := by
          have := congrArg norm hexp
          rw [Complex.norm_exp, Complex.norm_natCast] at this
          exact this
        have : (n : ℝ) ≤ (k : ℝ) - 1 ∨ (k : ℝ) + 1 ≤ n := by
          rcases Nat.lt_trichotomy n k with hlt | heq | hgt
          · left; exact_mod_cast (by omega : n ≤ k - 1)
          · exact False.elim (hnk heq)
          · right; exact_mod_cast (by omega : k + 1 ≤ n)
        rcases this with hlo | hhi <;> linarith [hz.1, hz.2.1]
    have hfall := Gamma_one_sub_mul_falling (k - 1) hexp_ne_nat
    have hprod_split : ∏ j ∈ Finset.range k, ((j + 1 : ℂ) - Complex.exp z) =
        denomProd (Complex.exp z) * ((k : ℂ) - Complex.exp z) := by
      have hk_eq : k = (k - 1) + 1 := by omega
      conv_lhs => rw [hk_eq, Finset.prod_range_succ]
      have : ((k - 1 : ℕ) : ℂ) + 1 = (k : ℂ) := by exact_mod_cast hk_eq.symm
      rw [this]
    have hphi_eq : phi (Complex.exp z) = G_cell (Complex.exp z) / (Complex.exp z - (k : ℂ)) := by
      have hk1_eq : (((k - 1 : ℕ) : ℂ) + 2 - Complex.exp z) = (k + 1 : ℂ) - Complex.exp z := by
        have : (k - 1 : ℕ) + 2 = k + 1 := by omega
        exact_mod_cast congrArg (fun m : ℕ => (m : ℂ) - Complex.exp z) this
      have hkeq2 : (k - 1) + 1 = k := by omega
      rw [hkeq2, hprod_split, hk1_eq] at hfall
      have hsubk : Complex.exp z - (k : ℂ) ≠ 0 := sub_ne_zero.mpr (hexp_ne_nat k hk)
      have hsubk' : (k : ℂ) - Complex.exp z ≠ 0 := fun h => hsubk (by linear_combination -h)
      have hdnz := hdenom_nz z hz
      dsimp only [G_cell, phi]
      calc Complex.Gamma (1 - Complex.exp z)
          = (denomProd (Complex.exp z) * ((k : ℂ) - Complex.exp z) *
              Complex.Gamma (1 - Complex.exp z)) /
              (denomProd (Complex.exp z) * ((k : ℂ) - Complex.exp z)) := by
            field_simp [hdnz, hsubk']
        _ = Complex.Gamma ((k + 1 : ℂ) - Complex.exp z) /
              (denomProd (Complex.exp z) * ((k : ℂ) - Complex.exp z)) := by rw [hfall]
        _ = -(Complex.Gamma ((k + 1 : ℂ) - Complex.exp z) / denomProd (Complex.exp z)) /
              (Complex.exp z - (k : ℂ)) := by
            rw [show (k : ℂ) - Complex.exp z = -(Complex.exp z - (k : ℂ)) by ring]
            field_simp [hdnz, hsubk]
    have hMz : M_cell z / (z - (c₀ : ℂ)) = rectH u z := by
      dsimp only [M_cell, rectH]
      rw [hphi_eq, ← hD_eq z hzne]
      have hDz := hD_nz z hz
      field_simp [hsub_ne, hDz]
    rw [sub_div, hMz]
    ring
  have h_bot_eq : ∫ x : ℝ in a₁..a₂, dslope M_cell (c₀ : ℂ) ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I) =
      ∫ x : ℝ in a₁..a₂, rectH u ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I) -
        M_cell (c₀ : ℂ) * (((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I) - (c₀ : ℂ))⁻¹ := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hz_mem : (x : ℂ) + ((-theta4 : ℝ) : ℂ) * I ∈ rect :=
      ⟨by simp [hx], by simp [left_mem_uIcc]⟩
    have hne : (x : ℂ) + ((-theta4 : ℝ) : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
      have him := congrArg Complex.im h
      simp at him
      linarith [theta4_pos]
    exact hH_on_ne _ (hrect_sub_O hz_mem) hne
  have h_top_eq : ∫ x : ℝ in a₁..a₂, dslope M_cell (c₀ : ℂ) ((x : ℂ) + (theta4 : ℂ) * I) =
      ∫ x : ℝ in a₁..a₂, rectH u ((x : ℂ) + (theta4 : ℂ) * I) -
        M_cell (c₀ : ℂ) * (((x : ℂ) + (theta4 : ℂ) * I) - (c₀ : ℂ))⁻¹ := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hz_mem : (x : ℂ) + (theta4 : ℂ) * I ∈ rect :=
      ⟨by simp [hx], by simp [right_mem_uIcc]⟩
    have hne : (x : ℂ) + (theta4 : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
      have him := congrArg Complex.im h
      simp at him
      linarith [theta4_pos]
    exact hH_on_ne _ (hrect_sub_O hz_mem) hne
  have h_right_eq : ∫ y : ℝ in (-theta4)..theta4, dslope M_cell (c₀ : ℂ) ((a₂ : ℂ) + (y : ℂ) * I) =
      ∫ y : ℝ in (-theta4)..theta4, rectH u ((a₂ : ℂ) + (y : ℂ) * I) -
        M_cell (c₀ : ℂ) * (((a₂ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹ := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hz_mem : (a₂ : ℂ) + (y : ℂ) * I ∈ rect :=
      ⟨by simp [right_mem_uIcc], by simp [hy]⟩
    have hne : (a₂ : ℂ) + (y : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
      have hre := congrArg Complex.re h
      simp at hre
      linarith [ha₂]
    exact hH_on_ne _ (hrect_sub_O hz_mem) hne
  have h_left_eq : ∫ y : ℝ in (-theta4)..theta4, dslope M_cell (c₀ : ℂ) ((a₁ : ℂ) + (y : ℂ) * I) =
      ∫ y : ℝ in (-theta4)..theta4, rectH u ((a₁ : ℂ) + (y : ℂ) * I) -
        M_cell (c₀ : ℂ) * (((a₁ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹ := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hz_mem : (a₁ : ℂ) + (y : ℂ) * I ∈ rect :=
      ⟨by simp [left_mem_uIcc], by simp [hy]⟩
    have hne : (a₁ : ℂ) + (y : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
      have hre := congrArg Complex.re h
      simp at hre
      linarith [ha₁]
    exact hH_on_ne _ (hrect_sub_O hz_mem) hne
  have hH_rect_eq : rectIntegral (rectH u) ((a₁ : ℂ) - (theta4 : ℂ) * I) ((a₂ : ℂ) + (theta4 : ℂ) * I) =
      M_cell (c₀ : ℂ) * rectIntegral (fun ζ => (ζ - (c₀ : ℂ))⁻¹)
        ((a₁ : ℂ) - (theta4 : ℂ) * I) ((a₂ : ℂ) + (theta4 : ℂ) * I) := by
    have hSlope_eq : rectIntegral (dslope M_cell (c₀ : ℂ))
          ((a₁ : ℂ) - (theta4 : ℂ) * I) ((a₂ : ℂ) + (theta4 : ℂ) * I) =
        rectIntegral (fun ζ => rectH u ζ - M_cell (c₀ : ℂ) * (ζ - (c₀ : ℂ))⁻¹)
          ((a₁ : ℂ) - (theta4 : ℂ) * I) ((a₂ : ℂ) + (theta4 : ℂ) * I) := by
      unfold rectIntegral
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, Complex.ofReal_im, sub_zero, sub_self, Complex.add_re, add_zero,
        Complex.sub_im, Complex.mul_im, mul_one, zero_sub, Complex.add_im, zero_add]
      rw [h_bot_eq, h_top_eq, h_right_eq, h_left_eq]
    have hinv_b : IntervalIntegrable (fun x : ℝ => M_cell (c₀ : ℂ) * (((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I) - (c₀ : ℂ))⁻¹)
        volume a₁ a₂ :=
      (Continuous.const_mul (Continuous.inv₀ (by fun_prop) fun x h0 => by
        have him := congrArg Complex.im h0; simp at him; linarith [theta4_pos]) _).intervalIntegrable a₁ a₂
    have hinv_t : IntervalIntegrable (fun x : ℝ => M_cell (c₀ : ℂ) * (((x : ℂ) + (theta4 : ℂ) * I) - (c₀ : ℂ))⁻¹)
        volume a₁ a₂ :=
      (Continuous.const_mul (Continuous.inv₀ (by fun_prop) fun x h0 => by
        have him := congrArg Complex.im h0; simp at him; linarith [theta4_pos]) _).intervalIntegrable a₁ a₂
    have hinv_r : IntervalIntegrable (fun y : ℝ => M_cell (c₀ : ℂ) * (((a₂ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹)
        volume (-theta4) theta4 :=
      (Continuous.const_mul (Continuous.inv₀ (by fun_prop) fun y h0 => by
        have hre := congrArg Complex.re h0; simp at hre; linarith [ha₂]) _).intervalIntegrable (-theta4) theta4
    have hinv_l : IntervalIntegrable (fun y : ℝ => M_cell (c₀ : ℂ) * (((a₁ : ℂ) + (y : ℂ) * I) - (c₀ : ℂ))⁻¹)
        volume (-theta4) theta4 :=
      (Continuous.const_mul (Continuous.inv₀ (by fun_prop) fun y h0 => by
        have hre := congrArg Complex.re h0; simp at hre; linarith [ha₁]) _).intervalIntegrable (-theta4) theta4
    have hs_b : IntervalIntegrable (fun x : ℝ => dslope M_cell (c₀ : ℂ) ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I))
        volume a₁ a₂ :=
      (hSlope_diff.continuousOn.comp (f := fun t : ℝ => (t : ℂ) + ((-theta4 : ℝ) : ℂ) * I)
        (Continuous.continuousOn (by fun_prop))
        (fun t ht => ⟨by simp [ht], by simp⟩)).intervalIntegrable
    have hs_t : IntervalIntegrable (fun x : ℝ => dslope M_cell (c₀ : ℂ) ((x : ℂ) + (theta4 : ℂ) * I))
        volume a₁ a₂ :=
      (hSlope_diff.continuousOn.comp (f := fun t : ℝ => (t : ℂ) + (theta4 : ℂ) * I)
        (Continuous.continuousOn (by fun_prop))
        (fun t ht => ⟨by simp [ht], by simp⟩)).intervalIntegrable
    have hs_r : IntervalIntegrable (fun y : ℝ => dslope M_cell (c₀ : ℂ) ((a₂ : ℂ) + (y : ℂ) * I))
        volume (-theta4) theta4 :=
      (hSlope_diff.continuousOn.comp (f := fun t : ℝ => (a₂ : ℂ) + (t : ℂ) * I)
        (Continuous.continuousOn (by fun_prop))
        (fun t ht => ⟨by simp [right_mem_uIcc], by simp [ht]⟩)).intervalIntegrable
    have hs_l : IntervalIntegrable (fun y : ℝ => dslope M_cell (c₀ : ℂ) ((a₁ : ℂ) + (y : ℂ) * I))
        volume (-theta4) theta4 :=
      (hSlope_diff.continuousOn.comp (f := fun t : ℝ => (a₁ : ℂ) + (t : ℂ) * I)
        (Continuous.continuousOn (by fun_prop))
        (fun t ht => ⟨by simp [left_mem_uIcc], by simp [ht]⟩)).intervalIntegrable
    have hh_b : IntervalIntegrable (fun x : ℝ => rectH u ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I)) volume a₁ a₂ :=
      (hs_b.add hinv_b).congr fun x hx => by
        have hmx : (x : ℂ) + ((-theta4 : ℝ) : ℂ) * I ∈ rect :=
          ⟨by simp [uIoc_subset_uIcc hx], by simp [left_mem_uIcc]⟩
        have hne : (x : ℂ) + ((-theta4 : ℝ) : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
          have him := congrArg Complex.im h; simp at him; linarith [theta4_pos]
        rw [hH_on_ne _ (hrect_sub_O hmx) hne]; ring
    have hh_t : IntervalIntegrable (fun x : ℝ => rectH u ((x : ℂ) + (theta4 : ℂ) * I)) volume a₁ a₂ :=
      (hs_t.add hinv_t).congr fun x hx => by
        have hmx : (x : ℂ) + (theta4 : ℂ) * I ∈ rect :=
          ⟨by simp [uIoc_subset_uIcc hx], by simp [right_mem_uIcc]⟩
        have hne : (x : ℂ) + (theta4 : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
          have him := congrArg Complex.im h; simp at him; linarith [theta4_pos]
        rw [hH_on_ne _ (hrect_sub_O hmx) hne]; ring
    have hh_r : IntervalIntegrable (fun y : ℝ => rectH u ((a₂ : ℂ) + (y : ℂ) * I)) volume (-theta4) theta4 :=
      (hs_r.add hinv_r).congr fun y hy => by
        have hmy : (a₂ : ℂ) + (y : ℂ) * I ∈ rect :=
          ⟨by simp [right_mem_uIcc], by simp [uIoc_subset_uIcc hy]⟩
        have hne : (a₂ : ℂ) + (y : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
          have hre := congrArg Complex.re h; simp at hre; linarith [ha₂]
        rw [hH_on_ne _ (hrect_sub_O hmy) hne]; ring
    have hh_l : IntervalIntegrable (fun y : ℝ => rectH u ((a₁ : ℂ) + (y : ℂ) * I)) volume (-theta4) theta4 :=
      (hs_l.add hinv_l).congr fun y hy => by
        have hmy : (a₁ : ℂ) + (y : ℂ) * I ∈ rect :=
          ⟨by simp [left_mem_uIcc], by simp [uIoc_subset_uIcc hy]⟩
        have hne : (a₁ : ℂ) + (y : ℂ) * I ≠ (c₀ : ℂ) := fun h => by
          have hre := congrArg Complex.re h; simp at hre; linarith [ha₁]
        rw [hH_on_ne _ (hrect_sub_O hmy) hne]; ring
    have hdiff_rect : rectIntegral (rectH u) ((a₁ : ℂ) - (theta4 : ℂ) * I) ((a₂ : ℂ) + (theta4 : ℂ) * I) -
        rectIntegral (fun ζ => M_cell (c₀ : ℂ) * (ζ - (c₀ : ℂ))⁻¹)
          ((a₁ : ℂ) - (theta4 : ℂ) * I) ((a₂ : ℂ) + (theta4 : ℂ) * I) = 0 := by
      rw [← rectIntegral_sub_rectIntegral
        (f := rectH u) (g := fun ζ => M_cell (c₀ : ℂ) * (ζ - (c₀ : ℂ))⁻¹)
        (z := (a₁ : ℂ) - (theta4 : ℂ) * I) (w := (a₂ : ℂ) + (theta4 : ℂ) * I)
        (by simpa using hh_b) (by simpa using hinv_b)
        (by simpa using hh_t) (by simpa using hinv_t)
        (by simpa using hh_r) (by simpa using hinv_r)
        (by simpa using hh_l) (by simpa using hinv_l), ← hSlope_eq, hRect0]
    rw [rectIntegral_const_mul] at hdiff_rect
    exact sub_eq_zero.mp hdiff_rect
  rw [hH_rect_eq, rectIntegral_inv_sub ha₁ ha₂ theta4_pos]
  have hM_val : M_cell (c₀ : ℂ) = (-1 : ℂ) ^ k / ((k - 1).factorial : ℂ) * Complex.exp (-(k : ℂ) * u) := by
    have hexp_c : Complex.exp (c₀ : ℂ) = (k : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hk_pos]; norm_cast
    have hD_c : D_exp (c₀ : ℂ) = (k : ℂ) := by
      dsimp only [D_exp]
      rw [dslope_same, (Complex.hasDerivAt_exp _).deriv, hexp_c]
    have hden_c : denomProd (k : ℂ) = (-1 : ℂ) ^ (k - 1) * ((k - 1).factorial : ℂ) := by
      have hkeq : (k - 1) + 1 = k := by omega
      simpa [denomProd, hkeq] using prod_range_sub_nat (k - 1)
    have hGam_c : Complex.Gamma ((k + 1 : ℂ) - (k : ℂ)) = 1 := by
      simp [show (k + 1 : ℂ) - (k : ℂ) = 1 by ring]
    dsimp only [M_cell, G_cell]
    rw [hexp_c, hD_c, hGam_c, hden_c]
    have hnum_c : Complex.exp ((c₀ : ℂ) - u * (k : ℂ)) = (k : ℂ) * Complex.exp (-(k : ℂ) * u) := by
      rw [sub_eq_add_neg, Complex.exp_add, hexp_c]
      congr 2; ring
    rw [hnum_c]
    have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk_pos.ne'
    have hfac : ((k - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - 1)
    have hpowk : (-1 : ℂ) ^ (k - 1) = -((-1 : ℂ) ^ k) := by
      have hkeq : k = (k - 1) + 1 := by omega
      conv_rhs => rw [hkeq, pow_succ]
      ring
    rw [hpowk]
    field_simp [hkne, hfac]
    have hpow2 : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hpow2]
  rw [hM_val]
  unfold cGamma
  ring

private lemma rectH_sum_cells (u : ℂ) {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2) (N : ℕ) :
    rectIntegral (rectH u) ((Real.log ε : ℂ) - (theta4 : ℂ) * I)
      ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (theta4 : ℂ) * I) =
      ∑ k ∈ Finset.Icc 1 N, cGamma k * Complex.exp (-(k : ℂ) * u) := by
  induction N with
  | zero =>
    simpa using rectH_zero_cell u hε hε_le
  | succ N ih =>
    let x₀ : ℝ := Real.log ((N : ℝ) + 1 / 2)
    let x₁ : ℝ := Real.log ε
    let x₂ : ℝ := Real.log (((N + 1 : ℕ) : ℝ) + 1 / 2)
    have hN0 : 0 < (N : ℝ) + 1 / 2 := by positivity
    have hx₁₀ : x₁ ≤ x₀ := Real.log_le_log hε (by linarith)
    have hx₀₂ : x₀ ≤ x₂ := Real.log_le_log hN0 (by push_cast; linarith)
    have h_line_cont : ∀ (y : ℝ) (hy : y = -theta4 ∨ y = theta4) {a b : ℝ} (_hab : a ≤ b),
        ContinuousOn (fun x : ℝ => rectH u ((x : ℂ) + (y : ℂ) * I)) (Icc a b) := by
      intro y hy a b _ x _
      have hexp_pt : DifferentiableAt ℂ Complex.exp ((x : ℂ) + (y : ℂ) * I) :=
        Complex.differentiableAt_exp
      have hphi_pt : DifferentiableAt ℂ (fun ζ => phi (Complex.exp ζ)) ((x : ℂ) + (y : ℂ) * I) := by
        refine (phi_analyticAt_of_avoids_posNat fun n hn hexp => ?_).differentiableAt.comp _ hexp_pt
        have him_eq : ((x : ℂ) + (y : ℂ) * I).im = y := by
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, mul_one, mul_zero, zero_add, add_zero, Complex.ofReal_re]
        have hy_lt : |((x : ℂ) + (y : ℂ) * I).im| < Real.pi := by
          rw [him_eq]
          rcases hy with rfl | rfl
          · rw [abs_neg, abs_of_pos theta4_pos]; exact theta4_lt_pi
          · rw [abs_of_pos theta4_pos]; exact theta4_lt_pi
        have hbad := (exp_eq_natCast_iff_of_abs_im_lt_pi hy_lt hn).mp hexp
        have him := congrArg Complex.im hbad
        rw [him_eq, Complex.ofReal_im] at him
        rcases hy with rfl | rfl <;> linarith [theta4_pos]
      have hd : DifferentiableAt ℂ (rectH u) ((x : ℂ) + (y : ℂ) * I) :=
        (Complex.differentiableAt_exp.comp _
          (differentiableAt_id.sub (differentiableAt_const u |>.mul Complex.differentiableAt_exp))).mul
          hphi_pt
      have hcomp : ContinuousAt (fun t : ℝ => rectH u ((t : ℂ) + (y : ℂ) * I)) x :=
        hd.continuousAt.comp (f := fun t : ℝ => (t : ℂ) + (y : ℂ) * I) (by fun_prop)
      exact hcomp.continuousWithinAt
    have hb₁ : IntervalIntegrable (fun x : ℝ => rectH u ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I)) volume x₁ x₀ :=
      (h_line_cont (-theta4) (Or.inl rfl) hx₁₀).intervalIntegrable_of_Icc hx₁₀
    have hb₂ : IntervalIntegrable (fun x : ℝ => rectH u ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I)) volume x₀ x₂ :=
      (h_line_cont (-theta4) (Or.inl rfl) hx₀₂).intervalIntegrable_of_Icc hx₀₂
    have ht₁ : IntervalIntegrable (fun x : ℝ => rectH u ((x : ℂ) + (theta4 : ℂ) * I)) volume x₁ x₀ :=
      (h_line_cont theta4 (Or.inr rfl) hx₁₀).intervalIntegrable_of_Icc hx₁₀
    have ht₂ : IntervalIntegrable (fun x : ℝ => rectH u ((x : ℂ) + (theta4 : ℂ) * I)) volume x₀ x₂ :=
      (h_line_cont theta4 (Or.inr rfl) hx₀₂).intervalIntegrable_of_Icc hx₀₂
    have hsplit := rectIntegral_hsplit hb₁ hb₂ ht₁ ht₂
    have h_cell := rectH_pole_cell u (k := N + 1) (by omega)
    have hx₀_eq : (((N + 1 : ℕ) : ℝ) - 1 / 2) = (N : ℝ) + 1 / 2 := by push_cast; ring
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h1 : ((x₁ : ℂ) + ((-theta4 : ℝ) : ℂ) * I) = (Real.log ε : ℂ) - (theta4 : ℂ) * I := by
      push_cast; ring
    have h2 : ((x₀ : ℂ) + ((-theta4 : ℝ) : ℂ) * I) =
        (Real.log (((N + 1 : ℕ) : ℝ) - 1 / 2) : ℂ) - (theta4 : ℂ) * I := by
      rw [hx₀_eq]; push_cast; ring
    rw [show (Real.log (((N + 1 : ℕ) : ℝ) + 1 / 2) : ℂ) + (theta4 : ℂ) * I =
        (x₂ : ℂ) + (theta4 : ℂ) * I from rfl,
      ← h1, hsplit, h1, ih, h2, h_cell, hIcc, Finset.sum_insert (by simp)]
    ring

private lemma dPlus_eq_exp_theta4 : Complex.exp ((theta4 : ℂ) * I) = dPlus := by
  unfold dPlus
  rw [mul_comm I]

private lemma dMinus_eq_exp_neg_theta4 : Complex.exp ((-theta4 : ℝ) * I) = dMinus := by
  unfold dMinus
  congr 1
  push_cast
  ring

theorem stokes_jump_gamma {u : ℝ} (hu : 0 < u) :
    gMinusR u - gPlusR u = -(2 * (Real.pi : ℂ) * I) * Complex.exp (-(u : ℂ)) *
      Complex.exp (-Complex.exp (-(u : ℂ))) := by
  let fPlus (r : ℝ) : ℂ := damped ((u : ℂ) * dPlus) (Minor.pull dPlus phi) r
  let fMinus (r : ℝ) : ℂ := damped ((u : ℂ) * dMinus) (Minor.pull dMinus phi) r
  have hfPlus_cont : ContinuousOn fPlus (Ici (0 : ℝ)) := by
    refine ContinuousOn.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn ?_
    refine continuousOn_const.mul (fun v hv => ?_)
    have han := (phi_analyticAt_of_avoids_posNat
      (avoids_posNat_of_UPlus (UPlus_contains_dPlus v hv))).continuousAt
    exact (han.comp (f := fun x : ℝ => dPlus * (x : ℂ))
      (continuous_const.mul Complex.continuous_ofReal).continuousAt).continuousWithinAt
  have hfMinus_cont : ContinuousOn fMinus (Ici (0 : ℝ)) := by
    refine ContinuousOn.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn ?_
    refine continuousOn_const.mul (fun v hv => ?_)
    have han := (phi_analyticAt_of_avoids_posNat
      (avoids_posNat_of_UMinus (UMinus_contains_dMinus v hv))).continuousAt
    exact (han.comp (f := fun x : ℝ => dMinus * (x : ℂ))
      (continuous_const.mul Complex.continuous_ofReal).continuousAt).continuousWithinAt
  have hi_Plus : IntegrableOn fPlus (Ioi 0) := by
    obtain ⟨C, _, hdec⟩ := phi_dPlus_decay 0
    have hexp : ∀ v : ℝ, 0 ≤ v → ‖Minor.pull dPlus phi v‖ ≤ C * Real.exp (0 * v) := fun v hv => by
      simpa [Minor.pull, norm_dPlus] using hdec v hv
    exact damped_integrable (Minor.pull_cont UPlus_contains_dPlus aGamma_good_UPlus) hexp
      (by simp [Complex.mul_re]; exact mul_pos hu dPlus_re_pos)
  have hi_Minus : IntegrableOn fMinus (Ioi 0) := by
    obtain ⟨C, _, hdec⟩ := phi_dMinus_decay 0
    have hexp : ∀ v : ℝ, 0 ≤ v → ‖Minor.pull dMinus phi v‖ ≤ C * Real.exp (0 * v) := fun v hv => by
      simpa [Minor.pull, norm_dMinus] using hdec v hv
    exact damped_integrable (Minor.pull_cont UMinus_contains_dMinus aGamma_good_UMinus) hexp
      (by simp [Complex.mul_re]; exact mul_pos hu dMinus_re_pos)
  have hgPlus_eq : gPlusR u = ∫ r in Ioi (0 : ℝ), fPlus r := by
    simp [gPlusR, gPlus, Minor.value, aGamma, complexLaplace, fPlus]
  have hgMinus_eq : gMinusR u = ∫ r in Ioi (0 : ℝ), fMinus r := by
    simp [gMinusR, gMinus, Minor.value, aGamma, complexLaplace, fMinus]
  have hH_plus : ∀ x : ℝ, rectH (u : ℂ) ((x : ℂ) + (theta4 : ℂ) * I) =
      Real.exp x • fPlus (Real.exp x) := by
    intro x
    have hexp_pt : Complex.exp ((x : ℂ) + (theta4 : ℂ) * I) = (Real.exp x : ℂ) * dPlus := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, dPlus_eq_exp_theta4]
    simp only [rectH, fPlus, damped, Minor.pull, Complex.real_smul]
    rw [hexp_pt, sub_eq_add_neg, Complex.exp_add, hexp_pt]
    have : Complex.exp (-((u : ℂ) * ((Real.exp x : ℂ) * dPlus))) =
        Complex.exp (-((u : ℂ) * dPlus) * (Real.exp x : ℂ)) := by congr 1; ring
    rw [this, mul_comm (Real.exp x : ℂ) dPlus]
    ring
  have hH_minus : ∀ x : ℝ, rectH (u : ℂ) ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I) =
      Real.exp x • fMinus (Real.exp x) := by
    intro x
    have hexp_pt : Complex.exp ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I) = (Real.exp x : ℂ) * dMinus := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, dMinus_eq_exp_neg_theta4]
    simp only [rectH, fMinus, damped, Minor.pull, Complex.real_smul]
    rw [hexp_pt, sub_eq_add_neg, Complex.exp_add, hexp_pt]
    have : Complex.exp (-((u : ℂ) * ((Real.exp x : ℂ) * dMinus))) =
        Complex.exp (-((u : ℂ) * dMinus) * (Real.exp x : ℂ)) := by congr 1; ring
    rw [this, mul_comm (Real.exp x : ℂ) dMinus]
    ring
  have h_sum_lim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, cGamma k * Complex.exp (-(k : ℂ) * (u : ℂ)))
      atTop (𝓝 (-(2 * (Real.pi : ℂ) * I) * Complex.exp (-(u : ℂ)) *
        Complex.exp (-Complex.exp (-(u : ℂ))))) := by
    let w : ℂ := Complex.exp (-(u : ℂ))
    have hsum_eq : ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, cGamma k * Complex.exp (-(k : ℂ) * (u : ℂ))) =
        -(2 * (Real.pi : ℂ) * I) * w * ∑ m ∈ Finset.range N, (-w) ^ m / (m.factorial : ℂ) := by
      intro N
      have hIcc : Finset.Icc 1 N = (Finset.range N).map ⟨fun m => m + 1, Nat.succ_injective⟩ := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
        exact ⟨fun h => ⟨k - 1, by omega, by omega⟩, fun ⟨m, hm, hmk⟩ => by omega⟩
      rw [hIcc, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only [Function.Embedding.coeFn_mk, cGamma]
      rw [Nat.add_sub_cancel, show -((m + 1 : ℕ) : ℂ) * (u : ℂ) = -(u : ℂ) + (m : ℕ) * (-(u : ℂ)) by
        push_cast; ring, Complex.exp_add, Complex.exp_nat_mul]
      change _ = -(2 * (Real.pi : ℂ) * I) * w * ((-w) ^ m / (m.factorial : ℂ))
      have hw_eq : Complex.exp (-(u : ℂ)) = w := rfl
      rw [hw_eq, pow_succ]
      rw [show (-w) ^ m = (-1 : ℂ) ^ m * w ^ m by rw [neg_eq_neg_one_mul, mul_pow]]
      ring
    simp_rw [hsum_eq]
    have hlim : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, (-w) ^ m / (m.factorial : ℂ))
        atTop (𝓝 (Complex.exp (-w))) := by
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
      exact (NormedSpace.expSeries_div_summable (-w)).hasSum.tendsto_sum_nat
    simpa [w] using (tendsto_const_nhds.mul hlim)
  have h_eps_eq : ∀ {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2),
      (∫ r in Ioi ε, fMinus r) - (∫ r in Ioi ε, fPlus r) -
        I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ε : ℂ) + (y : ℂ) * I)) =
      -(2 * (Real.pi : ℂ) * I) * Complex.exp (-(u : ℂ)) * Complex.exp (-Complex.exp (-(u : ℂ))) := by
    intro ε hε hε_le
    have h_N_eq : ∀ (N : ℕ), 2 ≤ N →
        (∫ r in ε..((N : ℝ) + 1 / 2), fMinus r) - (∫ r in ε..((N : ℝ) + 1 / 2), fPlus r) +
          I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I)) -
          I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ε : ℂ) + (y : ℂ) * I)) =
        ∑ k ∈ Finset.Icc 1 N, cGamma k * Complex.exp (-(k : ℂ) * (u : ℂ)) := by
      intro N _
      have hN_pos : 0 < (N : ℝ) + 1 / 2 := by positivity
      have hbot : ∫ x : ℝ in (Real.log ε)..(Real.log ((N : ℝ) + 1 / 2)),
          rectH (u : ℂ) ((x : ℂ) + ((-theta4 : ℝ) : ℂ) * I) =
          ∫ r in ε..((N : ℝ) + 1 / 2), fMinus r := by
        simp_rw [hH_minus]
        have him : (Real.exp '' uIcc (Real.log ε) (Real.log ((N : ℝ) + 1 / 2))) ⊆ Ici (0 : ℝ) := by
          rintro r ⟨x, _, rfl⟩; exact (Real.exp_pos x).le
        have hcomp := intervalIntegral.integral_deriv_smul_comp' (f := Real.exp) (f' := Real.exp)
          (g := fMinus) (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
          (hfMinus_cont.mono him)
        rw [Real.exp_log hε, Real.exp_log hN_pos] at hcomp
        exact hcomp
      have htop : ∫ x : ℝ in (Real.log ε)..(Real.log ((N : ℝ) + 1 / 2)),
          rectH (u : ℂ) ((x : ℂ) + (theta4 : ℂ) * I) =
          ∫ r in ε..((N : ℝ) + 1 / 2), fPlus r := by
        simp_rw [hH_plus]
        have him : (Real.exp '' uIcc (Real.log ε) (Real.log ((N : ℝ) + 1 / 2))) ⊆ Ici (0 : ℝ) := by
          rintro r ⟨x, _, rfl⟩; exact (Real.exp_pos x).le
        have hcomp := intervalIntegral.integral_deriv_smul_comp' (f := Real.exp) (f' := Real.exp)
          (g := fPlus) (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
          (hfPlus_cont.mono him)
        rw [Real.exp_log hε, Real.exp_log hN_pos] at hcomp
        exact hcomp
      have hrect := rectH_sum_cells (u : ℂ) hε hε_le N
      unfold rectIntegral at hrect
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, Complex.ofReal_im, sub_zero, sub_self, Complex.add_re, add_zero,
        Complex.sub_im, Complex.mul_im, mul_one, zero_sub, Complex.add_im, zero_add] at hrect
      rw [hbot, htop] at hrect
      exact hrect
    have hbot_lim : Tendsto (fun N : ℕ => ∫ r in ε..((N : ℝ) + 1 / 2), fMinus r)
        atTop (𝓝 (∫ r in Ioi ε, fMinus r)) :=
      intervalIntegral_tendsto_integral_Ioi ε (hi_Minus.mono_set (Ioi_subset_Ioi hε.le))
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have htop_lim : Tendsto (fun N : ℕ => ∫ r in ε..((N : ℝ) + 1 / 2), fPlus r)
        atTop (𝓝 (∫ r in Ioi ε, fPlus r)) :=
      intervalIntegral_tendsto_integral_Ioi ε (hi_Plus.mono_set (Ioi_subset_Ioi hε.le))
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hright_lim : Tendsto (fun N : ℕ =>
        I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I)))
        atTop (𝓝 0) := by
      let c_arc : ℝ := u * Real.sqrt 2 / 2
      have hca : 0 < c_arc := by positivity
      refine squeeze_zero_norm' (a := fun N : ℕ =>
          16 * theta4 * (((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2)))) ?_ ?_
      · filter_upwards [eventually_ge_atTop 2] with N hN
        rw [norm_mul, Complex.norm_I, one_mul]
        have hN_pos : 0 < (N : ℝ) + 1 / 2 := by positivity
        have hbd : ∀ y ∈ uIcc (-theta4) theta4,
            ‖rectH (u : ℂ) ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I)‖ ≤
              8 * ((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2)) := by
          intro y hy
          rw [uIcc_of_le (by linarith [theta4_pos] : -theta4 ≤ theta4)] at hy
          have hcos : Real.sqrt 2 / 2 ≤ Real.cos y := by
            rw [← Real.cos_pi_div_four, ← Real.cos_abs y]
            exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) theta4_lt_pi.le (abs_le.mpr hy)
          have hexp_pt : Complex.exp ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I) =
              ((N : ℂ) + 1 / 2) * Complex.exp (I * (y : ℂ)) := by
            rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hN_pos, mul_comm I (y : ℂ)]
            push_cast; ring
          have hphi_bd : ‖phi (Complex.exp ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I))‖ ≤ 8 := by
            rw [hexp_pt]
            exact Gamma_one_sub_arc_bound hN (abs_le.mpr hy)
          have hexp_norm : ‖Complex.exp (((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I) -
              (u : ℂ) * Complex.exp ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I))‖ ≤
              ((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2)) := by
            have hexp_pt' : Complex.exp ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I) =
                (((N : ℝ) + 1 / 2 : ℝ) : ℂ) * Complex.exp ((y : ℂ) * I) := by
              rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hN_pos]
            have hre_pt : (((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I) -
                (u : ℂ) * Complex.exp ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I)).re =
                Real.log ((N : ℝ) + 1 / 2) - u * (((N : ℝ) + 1 / 2) * Real.cos y) := by
              rw [hexp_pt']
              simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero,
                zero_mul, Complex.exp_ofReal_mul_I_re]
            rw [Complex.norm_exp, hre_pt, Real.exp_sub, Real.exp_log hN_pos,
              div_eq_mul_inv, ← Real.exp_neg]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN_pos.le
            have : c_arc * ((N : ℝ) + 1 / 2) ≤ u * (((N : ℝ) + 1 / 2) * Real.cos y) := by
              dsimp only [c_arc]
              calc u * Real.sqrt 2 / 2 * ((N : ℝ) + 1 / 2)
                  = u * (((N : ℝ) + 1 / 2) * (Real.sqrt 2 / 2)) := by ring
                _ ≤ u * (((N : ℝ) + 1 / 2) * Real.cos y) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos hN_pos.le) hu.le
            linarith
          rw [rectH, norm_mul]
          calc _ ≤ ((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2)) * 8 :=
                mul_le_mul hexp_norm hphi_bd (norm_nonneg _) (by positivity)
            _ = 8 * ((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2)) := by ring
        have hle := intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hbd y (uIoc_subset_uIcc hy)
        calc ‖∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I)‖
            ≤ 8 * ((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2)) * |theta4 - -theta4| := hle
          _ = 16 * theta4 * (((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2))) := by
              rw [show theta4 - -theta4 = 2 * theta4 by ring, abs_of_pos (by linarith [theta4_pos])]; ring
      · have ht0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 2) * Real.exp (-c_arc * ((N : ℝ) + 1 / 2)))
            atTop (𝓝 0) := by
          have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c_arc hca).comp
            (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 / 2 : ℝ))))
          simpa [Function.comp_def, Real.rpow_one] using h
        simpa using (tendsto_const_nhds (x := 16 * theta4)).mul ht0
    have hL : Tendsto (fun N : ℕ =>
        (∫ r in ε..((N : ℝ) + 1 / 2), fMinus r) - (∫ r in ε..((N : ℝ) + 1 / 2), fPlus r) +
          I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ((N : ℝ) + 1 / 2) : ℂ) + (y : ℂ) * I)) -
          I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ε : ℂ) + (y : ℂ) * I)))
        atTop (𝓝 ((∫ r in Ioi ε, fMinus r) - (∫ r in Ioi ε, fPlus r) -
          I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ε : ℂ) + (y : ℂ) * I)))) := by
      simpa [add_zero] using ((hbot_lim.sub htop_lim).add hright_lim).sub
        (tendsto_const_nhds (x := I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log ε : ℂ) + (y : ℂ) * I))))
    exact tendsto_nhds_unique (hL.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      exact h_N_eq N hN)) h_sum_lim
  let eps (m : ℕ) : ℝ := 1 / ((m : ℝ) + 3)
  have heps_pos : ∀ m : ℕ, 0 < eps m := fun m => by dsimp only [eps]; positivity
  have heps_le : ∀ m : ℕ, eps m ≤ 1 / 2 := fun m => by
    dsimp only [eps]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [show (0 : ℝ) ≤ m by positivity])
  have heps_lim : Tendsto eps atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hIoi_lim : ∀ (f : ℝ → ℂ), IntegrableOn f (Ioi 0) → ContinuousOn f (Icc 0 (1 / 2)) →
      Tendsto (fun m : ℕ => ∫ r in Ioi (eps m), f r) atTop (𝓝 (∫ r in Ioi 0, f r)) := by
    intro f hfi hfc
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
    have h_split : ∀ m : ℕ, ∫ r in Ioi (eps m), f r =
        (∫ r in Ioi 0, f r) - ∫ r in (0 : ℝ)..(eps m), f r := by
      intro m
      have hsub := intervalIntegral.integral_interval_add_Ioi (a := (0 : ℝ)) (b := eps m)
        (μ := volume) (f := f) hfi (hfi.mono_set (Ioi_subset_Ioi (heps_pos m).le))
      linear_combination hsub
    simp_rw [h_split]
    have h0_lim : Tendsto (fun m : ℕ => ∫ r in (0 : ℝ)..(eps m), f r) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun m : ℕ => K * eps m) ?_ ?_
      · refine .of_forall fun m => ?_
        have hbd : ∀ r ∈ uIoc (0 : ℝ) (eps m), ‖f r‖ ≤ K := fun r hr => by
          rw [uIoc_of_le (heps_pos m).le] at hr
          exact hK r ⟨hr.1.le, hr.2.trans (heps_le m)⟩
        simpa [abs_of_pos (heps_pos m)] using intervalIntegral.norm_integral_le_of_norm_le_const hbd
      · simpa using (tendsto_const_nhds (x := K)).mul heps_lim
    simpa using tendsto_const_nhds.sub h0_lim
  have hleft_lim : Tendsto (fun m : ℕ =>
      I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log (eps m) : ℂ) + (y : ℂ) * I)))
      atTop (𝓝 0) := by
    have hphi_cont_ball : ContinuousOn phi (Metric.closedBall (0 : ℂ) (1 / 2)) := fun z hz => by
      have hlt : ‖z‖ < 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz; linarith
      refine (phi_analyticAt_of_avoids_posNat fun n hn he => ?_).continuousAt.continuousWithinAt
      have : (n : ℝ) < 1 := by rw [he, Complex.norm_natCast] at hlt; exact hlt
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    obtain ⟨K_phi, hK_phi⟩ := isCompact_closedBall (0 : ℂ) (1 / 2) |>.exists_bound_of_continuousOn hphi_cont_ball
    refine squeeze_zero_norm' (a := fun m : ℕ => 2 * theta4 * K_phi * eps m) ?_ ?_
    · refine .of_forall fun m => ?_
      rw [norm_mul, Complex.norm_I, one_mul]
      have hbd : ∀ y ∈ uIcc (-theta4) theta4,
          ‖rectH (u : ℂ) ((Real.log (eps m) : ℂ) + (y : ℂ) * I)‖ ≤ K_phi * eps m := by
        intro y hy
        rw [uIcc_of_le (by linarith [theta4_pos] : -theta4 ≤ theta4)] at hy
        have hth2 : theta4 ≤ Real.pi / 2 := by unfold theta4; linarith [Real.pi_pos]
        have hcos : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have hexp_pt : Complex.exp ((Real.log (eps m) : ℂ) + (y : ℂ) * I) =
            ((eps m : ℝ) : ℂ) * Complex.exp (I * (y : ℂ)) := by
          rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (heps_pos m), mul_comm I (y : ℂ)]
        have hmem_ball : Complex.exp ((Real.log (eps m) : ℂ) + (y : ℂ) * I) ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
          rw [Metric.mem_closedBall, dist_zero_right, hexp_pt, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (heps_pos m), mul_comm I (y : ℂ),
            Complex.norm_exp_ofReal_mul_I, mul_one]
          exact heps_le m
        have hexp_le : ‖Complex.exp (((Real.log (eps m) : ℂ) + (y : ℂ) * I) -
            (u : ℂ) * Complex.exp ((Real.log (eps m) : ℂ) + (y : ℂ) * I))‖ ≤ eps m := by
          have hre_pt : (((Real.log (eps m) : ℂ) + (y : ℂ) * I) -
              (u : ℂ) * Complex.exp ((Real.log (eps m) : ℂ) + (y : ℂ) * I)).re =
              Real.log (eps m) - u * (eps m * Real.cos y) := by
            simp [Complex.exp_re, Real.exp_log (heps_pos m)]
          rw [Complex.norm_exp, hre_pt, Real.exp_sub, Real.exp_log (heps_pos m)]
          have : 0 ≤ u * (eps m * Real.cos y) := mul_nonneg hu.le (mul_nonneg (heps_pos m).le hcos)
          calc eps m / Real.exp (u * (eps m * Real.cos y)) ≤ eps m / 1 :=
                div_le_div_of_nonneg_left (heps_pos m).le zero_lt_one (Real.one_le_exp this)
            _ = eps m := div_one _
        rw [rectH, norm_mul]
        calc _ ≤ eps m * K_phi :=
              mul_le_mul hexp_le (hK_phi _ hmem_ball) (norm_nonneg _) (heps_pos m).le
          _ = K_phi * eps m := mul_comm _ _
      calc ‖∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log (eps m) : ℂ) + (y : ℂ) * I)‖
          ≤ K_phi * eps m * |theta4 - -theta4| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hbd y (uIoc_subset_uIcc hy)
        _ = 2 * theta4 * K_phi * eps m := by
            rw [show theta4 - -theta4 = 2 * theta4 by ring, abs_of_pos (by linarith [theta4_pos])]; ring
    · simpa using (tendsto_const_nhds (x := 2 * theta4 * K_phi)).mul heps_lim
  have h_lim_m := ((hIoi_lim fMinus hi_Minus (hfMinus_cont.mono Icc_subset_Ici_self)).sub
    (hIoi_lim fPlus hi_Plus (hfPlus_cont.mono Icc_subset_Ici_self))).sub hleft_lim
  have hconst_m : Tendsto (fun m : ℕ =>
      (∫ r in Ioi (eps m), fMinus r) - (∫ r in Ioi (eps m), fPlus r) -
        I * (∫ y in (-theta4)..theta4, rectH (u : ℂ) ((Real.log (eps m) : ℂ) + (y : ℂ) * I)))
      atTop (𝓝 (-(2 * (Real.pi : ℂ) * I) * Complex.exp (-(u : ℂ)) * Complex.exp (-Complex.exp (-(u : ℂ))))) := by
    simp [h_eps_eq (heps_pos _) (heps_le _)]
  rw [hgMinus_eq, hgPlus_eq]
  simpa using tendsto_nhds_unique h_lim_m hconst_m

private def expRem : ℕ → ℂ → ℂ
  | 0 => fun w => Complex.exp (-w)
  | k + 1 => dslope (expRem k) 0

/-- Exact Stokes exponential expansion for all derivatives of `g_- - g_+` via iterated `dslope`. -/
lemma stokes_jump_derivatives_expansion (n j : ℕ) (_hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => gMinusR t - gPlusR t) u -
        ∑ m ∈ Finset.Icc 1 n, cGamma m * (-(m : ℂ)) ^ j * Complex.exp (-(m : ℂ) * (u : ℂ))‖ ≤
        C * Real.exp (-((n : ℝ) + 1) * u) := by
  have hexpRem_diff : ∀ k : ℕ, Differentiable ℂ (expRem k) := by
    intro k
    induction k with
    | zero => exact Complex.differentiable_exp.comp differentiable_id.neg
    | succ k ih =>
      rw [← differentiableOn_univ]
      exact (differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 (0 : ℂ))).mpr ih.differentiableOn
  have hexpRem_id : ∀ (k : ℕ) (w : ℂ),
      Complex.exp (-w) =
        (∑ m ∈ Finset.range k, expRem m 0 * w ^ m) + w ^ k * expRem k w := by
    intro k w
    induction k with
    | zero => simp [expRem]
    | succ k ih =>
      have hstep : expRem k w = expRem k 0 + w * expRem (k + 1) w := by
        have := sub_smul_dslope (expRem k) (0 : ℂ) w
        simp only [sub_zero, smul_eq_mul] at this
        have h1 : w * expRem (k + 1) w = expRem k w - expRem k 0 := this
        linear_combination -h1
      rw [Finset.sum_range_succ, pow_succ]
      linear_combination ih + w ^ k * hstep
  have hexp_neg_deriv : ∀ (k : ℕ) (w : ℂ),
      iteratedDeriv k (fun ζ : ℂ => Complex.exp (-ζ)) w = (-1 : ℂ) ^ k * Complex.exp (-w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun ζ : ℂ => Complex.exp (-ζ)) =
          fun ζ : ℂ => (-1 : ℂ) ^ k * Complex.exp (-ζ) from funext ih]
      have hd : HasDerivAt (fun ζ : ℂ => (-1 : ℂ) ^ k * Complex.exp (-ζ))
          ((-1 : ℂ) ^ (k + 1) * Complex.exp (-w)) w := by
        simpa [pow_succ', mul_assoc, mul_left_comm] using
          (((hasDerivAt_id w).neg).cexp).const_mul ((-1 : ℂ) ^ k)
      exact hd.deriv
  have hexpRem_val : ∀ m : ℕ, expRem m 0 = (-1 : ℂ) ^ m / (m.factorial : ℂ) := by
    intro m
    have hpoly_an : AnalyticAt ℂ (fun w : ℂ => ∑ i ∈ Finset.range (m + 1), expRem i 0 * w ^ i) 0 :=
      Finset.analyticAt_fun_sum _ fun _ _ => analyticAt_const.mul (analyticAt_id.pow _)
    have hrem_an : AnalyticAt ℂ (fun w : ℂ => w ^ (m + 1) * expRem (m + 1) w) 0 :=
      (analyticAt_id.pow _).mul
        (((hexpRem_diff (m + 1)).differentiableOn.analyticOnNhd isOpen_univ) 0 (mem_univ 0))
    have h_bigO : ∃ C : ℝ, ∀ᶠ w in 𝓝 (0 : ℂ), ‖w ^ (m + 1) * expRem (m + 1) w‖ ≤ C * ‖w‖ ^ (m + 1) := by
      obtain ⟨r, hr, K, _, _, hbd⟩ := Minor.analyticAt_ball_cont_bound
        (((hexpRem_diff (m + 1)).differentiableOn.analyticOnNhd isOpen_univ) 0 (mem_univ 0))
      refine ⟨K, ?_⟩
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with w hw
      rw [norm_mul, norm_pow, mul_comm K]
      exact mul_le_mul_of_nonneg_left (hbd w hw) (pow_nonneg (norm_nonneg w) _)
    have hrem_d := Minor.iteratedDeriv_eq_zero_of_isBigO_pow hrem_an h_bigO le_rfl
    have heq_fn : (fun w : ℂ => Complex.exp (-w)) =
        fun w => (∑ i ∈ Finset.range (m + 1), expRem i 0 * w ^ i) + w ^ (m + 1) * expRem (m + 1) w :=
      funext (hexpRem_id (m + 1))
    have hL : iteratedDeriv m (fun w : ℂ => Complex.exp (-w)) 0 = (-1 : ℂ) ^ m := by
      simpa using hexp_neg_deriv m 0
    have hR : iteratedDeriv m (fun w : ℂ =>
        (∑ i ∈ Finset.range (m + 1), expRem i 0 * w ^ i) + w ^ (m + 1) * expRem (m + 1) w) 0 =
        (m.factorial : ℂ) * expRem m 0 := by
      rw [iteratedDeriv_fun_add hpoly_an.contDiffAt hrem_an.contDiffAt, hrem_d, add_zero]
      have hcd : ∀ i ∈ Finset.range (m + 1), ContDiffAt ℂ m (fun w : ℂ => expRem i 0 * w ^ i) 0 :=
        fun _ _ => (analyticAt_const.mul (analyticAt_id.pow _)).contDiffAt
      rw [iteratedDeriv_fun_sum (I := Finset.range (m + 1)) hcd]
      have hterm : ∀ i ∈ Finset.range (m + 1),
          iteratedDeriv m (fun w : ℂ => expRem i 0 * w ^ i) 0 =
            if i = m then (m.factorial : ℂ) * expRem m 0 else 0 := by
        intro i _
        rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
        by_cases him : i = m
        · subst him; simp [mul_comm]
        · simp [him, Ne.symm him]
      rw [Finset.sum_congr rfl hterm]
      simp
    rw [heq_fn] at hL
    have hm_ne : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    field_simp [hm_ne]
    linear_combination hL - hR
  let Φ₀ : ℂ → ℂ := fun w => -(2 * (Real.pi : ℂ) * I) * expRem n w
  have hΦ₀ : Differentiable ℂ Φ₀ := (hexpRem_diff n).const_mul _
  have h_rem_deriv : ∀ (k : ℕ), ∃ Φ : ℂ → ℂ, Differentiable ℂ Φ ∧ ∀ (t : ℝ),
      iteratedDeriv k (fun s : ℝ => (Complex.exp (-(s : ℂ))) ^ (n + 1) * Φ₀ (Complex.exp (-(s : ℂ)))) t =
        (Complex.exp (-(t : ℂ))) ^ (n + 1) * Φ (Complex.exp (-(t : ℂ))) := by
    intro k
    induction k with
    | zero => exact ⟨Φ₀, hΦ₀, fun _ => rfl⟩
    | succ k ih =>
      obtain ⟨Φ, hΦ_diff, hΦ_eq⟩ := ih
      let Φ' : ℂ → ℂ := fun w => -((n + 1 : ℂ) * Φ w + w * deriv Φ w)
      have hΦ_an : AnalyticOnNhd ℂ Φ univ := hΦ_diff.differentiableOn.analyticOnNhd isOpen_univ
      have hΦ'_diff : Differentiable ℂ Φ' := by
        refine (Differentiable.add (hΦ_diff.const_mul _) (differentiable_id.mul ?_)).neg
        exact fun w => (hΦ_an.deriv w (mem_univ w)).differentiableAt
      refine ⟨Φ', hΦ'_diff, fun t => ?_⟩
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun s : ℝ =>
          (Complex.exp (-(s : ℂ))) ^ (n + 1) * Φ₀ (Complex.exp (-(s : ℂ)))) =
          fun s : ℝ => (Complex.exp (-(s : ℂ))) ^ (n + 1) * Φ (Complex.exp (-(s : ℂ))) from funext hΦ_eq]
      have hw : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ))) (-Complex.exp (-(t : ℂ))) t := by
        have h1 : HasDerivAt (fun s : ℝ => -(s : ℂ)) (-1) t :=
          (Complex.ofRealCLM.hasDerivAt (x := t)).neg
        convert h1.cexp using 1; ring
      have ha : HasDerivAt (fun s : ℝ => (Complex.exp (-(s : ℂ))) ^ (n + 1))
          (-((n + 1 : ℂ) * (Complex.exp (-(t : ℂ))) ^ (n + 1))) t := by
        convert hw.pow (n + 1) using 1
        rw [pow_succ]; push_cast; ring
      have hb : HasDerivAt (fun s : ℝ => Φ (Complex.exp (-(s : ℂ))))
          (-Complex.exp (-(t : ℂ)) * deriv Φ (Complex.exp (-(t : ℂ)))) t := by
        simpa [Function.comp_def, mul_comm] using (hΦ_diff (Complex.exp (-(t : ℂ)))).hasDerivAt.comp t hw
      have hab : HasDerivAt (fun s : ℝ =>
          (Complex.exp (-(s : ℂ))) ^ (n + 1) * Φ (Complex.exp (-(s : ℂ))))
          (-((n + 1 : ℂ) * (Complex.exp (-(t : ℂ))) ^ (n + 1)) * Φ (Complex.exp (-(t : ℂ))) +
            (Complex.exp (-(t : ℂ))) ^ (n + 1) *
              (-Complex.exp (-(t : ℂ)) * deriv Φ (Complex.exp (-(t : ℂ))))) t := ha.mul hb
      rw [hab.deriv]
      dsimp only [Φ']
      ring
  obtain ⟨Φj, hΦj_diff, hΦj_eq⟩ := h_rem_deriv j
  obtain ⟨C, hC⟩ := isCompact_closedBall (0 : ℂ) 1 |>.exists_bound_of_continuousOn
    hΦj_diff.continuous.continuousOn
  refine ⟨max C 0, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hloc : (fun t : ℝ => gMinusR t - gPlusR t) =ᶠ[𝓝 u]
      fun t : ℝ => (∑ m ∈ Finset.Icc 1 n, cGamma m * (Complex.exp (-(t : ℂ))) ^ m) +
        (Complex.exp (-(t : ℂ))) ^ (n + 1) * Φ₀ (Complex.exp (-(t : ℂ))) := by
    filter_upwards [eventually_gt_nhds hu] with t ht
    rw [stokes_jump_gamma ht]
    let w : ℂ := Complex.exp (-(t : ℂ))
    have hid := congrArg (fun z => -(2 * (Real.pi : ℂ) * I) * w * z) (hexpRem_id n w)
    have hsum_w : -(2 * (Real.pi : ℂ) * I) * w * (∑ m ∈ Finset.range n, expRem m 0 * w ^ m) =
        ∑ m ∈ Finset.Icc 1 n, cGamma m * w ^ m := by
      have hIcc : Finset.Icc 1 n = (Finset.range n).map ⟨fun m => m + 1, Nat.succ_injective⟩ := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
        exact ⟨fun h => ⟨m - 1, by omega, by omega⟩, fun ⟨k, _, hkm⟩ => by omega⟩
      rw [hIcc, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only [Function.Embedding.coeFn_mk]
      rw [hexpRem_val m, cGamma, Nat.add_sub_cancel, pow_succ (-1 : ℂ), pow_succ w]
      ring
    dsimp only [Φ₀]
    rw [← hsum_w]
    change -(2 * (Real.pi : ℂ) * I) * w * Complex.exp (-w) = _
    rw [hid]
    ring
  rw [hloc.iteratedDeriv_eq j]
  have hcexp_cd : ∀ c : ℂ, ContDiff ℝ (j : WithTop ℕ∞) (fun t : ℝ => Complex.exp (c * (t : ℂ))) := fun c =>
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp).of_le le_top
  have hsum_eq : (fun t : ℝ => ∑ m ∈ Finset.Icc 1 n, cGamma m * (Complex.exp (-(t : ℂ))) ^ m) =
      fun t : ℝ => ∑ m ∈ Finset.Icc 1 n, cGamma m * Complex.exp (-(m : ℂ) * (t : ℂ)) := by
    funext t
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Complex.exp_nat_mul]
    congr 1; ring_nf
  have hsum_cd : ContDiffAt ℝ j (fun t : ℝ => ∑ m ∈ Finset.Icc 1 n, cGamma m * (Complex.exp (-(t : ℂ))) ^ m) u := by
    rw [hsum_eq]
    exact (ContDiff.sum (s := Finset.Icc 1 n) fun m _ =>
      contDiff_const.mul (hcexp_cd (-(m : ℂ)))).contDiffAt
  have hrem_cd : ContDiffAt ℝ j (fun t : ℝ => (Complex.exp (-(t : ℂ))) ^ (n + 1) * Φ₀ (Complex.exp (-(t : ℂ)))) u := by
    have hpow_eq : (fun t : ℝ => (Complex.exp (-(t : ℂ))) ^ (n + 1)) =
        fun t : ℝ => Complex.exp (-((n + 1 : ℕ) : ℂ) * (t : ℂ)) := by
      funext t
      rw [← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    have h1 : ContDiffAt ℝ j (fun t : ℝ => (Complex.exp (-(t : ℂ))) ^ (n + 1)) u := by
      rw [hpow_eq]
      exact (hcexp_cd (-((n + 1 : ℕ) : ℂ))).contDiffAt
    have hΦ₀_cd : ContDiff ℝ (j : WithTop ℕ∞) Φ₀ :=
      (((hΦ₀.differentiableOn.analyticOnNhd isOpen_univ).restrictScalars (𝕜 := ℝ)).contDiff).of_le le_top
    have h2 : ContDiffAt ℝ j (fun t : ℝ => Φ₀ (Complex.exp (-(t : ℂ)))) u :=
      hΦ₀_cd.contDiffAt.comp u (by
        have heq : (fun t : ℝ => Complex.exp (-(t : ℂ))) = fun t : ℝ => Complex.exp ((-1 : ℂ) * (t : ℂ)) := by
          funext t; ring_nf
        rw [heq]
        exact (hcexp_cd (-1)).contDiffAt)
    exact h1.mul h2
  rw [iteratedDeriv_fun_add hsum_cd hrem_cd]
  have h_sum_deriv : iteratedDeriv j (fun t : ℝ => ∑ m ∈ Finset.Icc 1 n, cGamma m * (Complex.exp (-(t : ℂ))) ^ m) u =
      ∑ m ∈ Finset.Icc 1 n, cGamma m * (-(m : ℂ)) ^ j * Complex.exp (-(m : ℂ) * (u : ℂ)) := by
    rw [hsum_eq]
    have hcd_m : ∀ m ∈ Finset.Icc 1 n, ContDiffAt ℝ j (fun t : ℝ => cGamma m * Complex.exp (-(m : ℂ) * (t : ℂ))) u :=
      fun m _ => (contDiff_const.mul (hcexp_cd (-(m : ℂ)))).contDiffAt
    rw [iteratedDeriv_fun_sum (I := Finset.Icc 1 n) hcd_m]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [iteratedDeriv_const_mul_field]
    have hcexp_d : ∀ (c : ℂ) (k : ℕ) (t : ℝ),
        iteratedDeriv k (fun s : ℝ => Complex.exp (c * (s : ℂ))) t = c ^ k * Complex.exp (c * (t : ℂ)) := by
      intro c k
      induction k with
      | zero => intro t; simp
      | succ k ih =>
        intro t
        rw [iteratedDeriv_succ, show iteratedDeriv k (fun s : ℝ => Complex.exp (c * (s : ℂ))) =
            fun s : ℝ => c ^ k * Complex.exp (c * (s : ℂ)) from funext ih]
        have hd : HasDerivAt (fun s : ℝ => c ^ k * Complex.exp (c * (s : ℂ)))
            (c ^ (k + 1) * Complex.exp (c * (t : ℂ))) t := by
          have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
          convert (h1.cexp.const_mul (c ^ k)) using 1
          rw [pow_succ']; ring
        exact hd.deriv
    rw [hcexp_d (-(m : ℂ)) j u]
    ring
  rw [h_sum_deriv, add_sub_cancel_left, hΦj_eq u]
  have hw_mem : Complex.exp (-(u : ℂ)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hΦ_le : ‖Φj (Complex.exp (-(u : ℂ)))‖ ≤ max C 0 :=
    (hC _ hw_mem).trans (le_max_left C 0)
  have hpow_norm : ‖(Complex.exp (-(u : ℂ))) ^ (n + 1)‖ = Real.exp (-((n : ℝ) + 1) * u) := by
    rw [norm_pow, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [norm_mul, hpow_norm, mul_comm (max C 0)]
  exact mul_le_mul_of_nonneg_left hΦ_le (Real.exp_pos _).le

/-! ### 6. Main Borel–Stokes–Vandermonde Theorem (`gHat` & General Asymptotic Transfer) -/

private lemma coeff_zero_d_u_iter (k : ℕ) :
    PowerSeries.coeff 0 (d_u^[k] gHat) = 0 := by
  cases k with
  | zero => simp [gHat]
  | succ k =>
    rw [Function.iterate_succ_apply']
    simp [d_u]

private lemma coeff_zero_formalEval {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) :
    PowerSeries.coeff 0 (formalEval gHat P) = MvPolynomial.eval 0 P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [formalEval]
  | add A B hA hB =>
    rw [formalEval, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hA hB
  | mul_X A j hA =>
    simp only [formalEval, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, Pi.zero_apply,
      mul_zero] at hA ⊢
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_d_u_iter j.val, mul_zero]

/-- **Borel–Stokes–Vandermonde Transcendence Theorem for `gHat`:**
    The formal Laplace series `gHat(u) = ∑_{k ≥ 0} (-1)^k Γ^{(k)}(1) u^{-k-1}`
    satisfies NO nonzero autonomous polynomial differential equation over `ℂ`. -/
theorem gHat_no_autonomous_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval gHat P = 0) : P = 0 := by
  classical
  by_contra hP_ne
  have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q.totalDegree = d ∧ Q ≠ 0 ∧ formalEval gHat Q = 0 :=
    ⟨P.totalDegree, P, rfl, hP_ne, hP⟩
  let Pmin := Classical.choose (Nat.find_spec hex)
  have hPmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hPmin_deg : Pmin.totalDegree = Nat.find hex := hPmin_spec.1
  have hPmin_ne : Pmin ≠ 0 := hPmin_spec.2.1
  have hPmin_zero : formalEval gHat Pmin = 0 := hPmin_spec.2.2
  have hPmin_min : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 → Q.totalDegree < Pmin.totalDegree → ¬ formalEval gHat Q = 0 := by
    intro Q hQ_ne hQ_deg hQ_zero
    rw [hPmin_deg] at hQ_deg
    exact Nat.find_min hex hQ_deg ⟨Q, rfl, hQ_ne, hQ_zero⟩
  have hPmin_const : MvPolynomial.eval 0 Pmin = 0 := by
    rw [← coeff_zero_formalEval, hPmin_zero, map_zero]
  obtain ⟨hpos, hneg⟩ := formalEval_zero_implies_gPlus_gMinus_zero Pmin hPmin_zero
  have h0 : Pmin = 0 := stokes_vandermonde_eq_zero
    (fun Q => formalEval gHat Q = 0) Pmin hPmin_min hPmin_const
    cGamma (fun _ _ _ => cGamma_ne_zero) gPlusR gMinusR
    (fun k _ => gPlusR_gMinusR_eventually_differentiable k)
    hpos hneg (fun j => gPlusR_bounded_derivatives j.val)
    (fun n j hn _ => stokes_jump_derivatives_expansion n j.val hn)
    (fun Q hQ => eval_gPlus_flat_implies_formalEval_zero Q hQ)
  exact hPmin_ne h0

/-- Any smooth/real function `f : ℝ → ℂ` sharing the all-orders `1/u` asymptotic expansion
    `d_u^[j] gHat` satisfies NO nonzero autonomous polynomial differential equation over `ℂ`. -/
theorem no_autonomous_ade_of_asymptotic {f : ℝ → ℂ}
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] gHat))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P = 0) :
    P = 0 := by
  have hexp : HasAsympExp
      (fun u => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P)
      (formalEval gHat P) :=
    HasAsympExp.mvPolynomial (fun j => hf_asymp j.val) P
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P‖ ≤ C / u ^ M := by
    intro M
    refine ⟨0, ?_⟩
    filter_upwards [hP] with u hu
    simp [hu]
  exact gHat_no_autonomous_ade P (hexp.eq_zero_of_flat hflat)

end
end PakPrimes.BorelStokesVandermonde
