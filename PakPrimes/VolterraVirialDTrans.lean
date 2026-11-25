module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Sibuya's Sub-Gevrey Convergence Theorem & Differential Transcendence of Volterra Functions and Quantum Gas Virial Coefficients

This module provides a completely self-contained, unconditional Lean 4 formalization of:

1. **Sibuya's Sub-Gevrey Convergence Theorem (`sibuya_subGevrey_convergent`,
   `sibuya_subGevrey_convergent_euler`)**:
   Every formal power series `f ∈ ℂ⟦X⟧` that is sub-Gevrey (`∀ s > 0, IsGevrey s f`) and satisfies
   a nonzero polynomial algebraic differential equation `P(X, f, f', ..., f^{(r)}) = 0` over `ℂ[X]`
   is convergent (`IsConvergentPS f`).
   Inspired by Gontsov–Goryuchkina (`arXiv:1311.6416`) and Malgrange–Sibuya, we prove BOTH the
   Fuchsian and irregular singular cases uniformly via a simultaneous weighted `ℓ¹` contraction
   on the tail `m ≥ M` in both the convergent (`s = 0`) and Gevrey (`s = ε`) norms.

2. **Sub-Gevrey Growth and Divergence of the Volterra Reciprocal-Gamma Asymptotic Series**:
   For every `α, β ∈ ℂ` with `-1 < β.re`, the formal series
   `volterraAsympSeries β α = ∑_{n ≥ 0} (Γ(n + β + 1) / Γ(β + 1)) * c_n X^n`,
   where `∑ c_n z^n = 1 / Γ(1 + α + z)`, is proved unconditionally to be sub-Gevrey
   (`volterraAsympSeries_isSubGevrey`) yet divergent (`volterraAsympSeries_not_convergent`).

3. **Volterra Functions `μ(t, β, α)` and `ν(t)`, Watson's Endpoint Expansion, Quantum Gas Virial
   Differential Transcendence, and the Exact Laplace Transform**:
   - `volterraMu_no_rat_ade`: for every `α : ℂ` and `β : ℂ` with `-1 < β.re`, `μ(t, β, α)`
     satisfies no nonzero polynomial ADE over `ℂ[t]`.
   - `volterraNu_no_rat_ade`, `volterraNu_temp_no_rat_ade`, `volterraNu_eulerDeriv_no_rat_ade`:
     Volterra's `ν(t)` (the interacting 2D two-component Fermi gas second virial shift
     `Δb_2^{(2D)}(t)`), its temperature form `T ↦ ν(E_B / T)`, and `t ν'(t)` are differentially
     transcendental.
   - `fermiGas1D_virial3_no_rat_ade`, `fermiGas1D_virial3_temp_no_rat_ade`: the interacting 1D
     three-species Fermi gas third virial shift `Δb_3^{(1D)}(t) = ν(t) / √3` is differentially
     transcendental in both inverse temperature `t` and temperature `T`.
   - `laplace_volterraNu`: for every real `s > 1`, `∫ t in Ioi 0, exp (-s t) * ν(t) = (s log s)⁻¹`.

## Non-Circular Parameter & Constant Schedule

All parameters and constants are chosen in strict topological order:

1. **Section 1 (Sibuya Sub-Gevrey Convergence):**
   - Inputs: `f : PowerSeries ℂ`, `IsSubGevrey f`, nonzero `P ∈ ℂ[X][Y_0, ..., Y_r]` with
     `evalDerivPS P f = 0`.
   - Step 1.1: Convert `d/dX` to Euler `δ = X d/dX` via `X^j f^{(j)} = ∏_{t < j} (δ - t) f` to get
     a nonzero `F_0` with `evalEulerPS F_0 f = 0`.
   - Step 1.2: Well-ordering minimization of order `n` and then `deg_{Y_n} F` yields a minimal
     nonzero `F ∈ ℂ[X][Y_0, ..., Y_n]` with `a_n := (∂F/∂Y_n)(X, Φ) ≠ 0`.
   - Step 1.3: Fix `l_n := (a_n.order).toNat`, `c_n := coeff l_n a_n ≠ 0`, and `k := l_n + 2`.
   - Step 1.4: Split `f = u_k + X^k ψ` with `u_k` a fixed polynomial of degree `≤ k` and
     `ψ(0) = 0`. Translate `F` by `Φ_k = (u_k, δ u_k, ..., δ^n u_k)` to obtain fixed polynomials
     `h`, `b_n`, `b_i` (`i < n`), irregular coefficients `c_{i,p}` (`1 ≤ p ≤ l_n`), and nonlinear
     polynomial `Q` (total `Y`-degree `≥ 2`, multiplied by `X^{k - l_n} = X^2`).
   - Step 1.5: Fix `ε := 1 / (4 * l_n + 2 : ℝ) > 0`. From `IsSubGevrey f`, obtain `C_0 ≥ 0`,
     `A_0 > 0` with `‖coeff m ψ‖ ≤ C_0 * A_0^m * (m!)^ε`.
   - Step 1.6: Choose `A ≥ 1` sufficiently large (explicitly depending only on `c_n`, `h`, `b_i`,
     `c_{i,p}`, `Q`, `C_0`, `A_0`, `k`, `n`, `l_n`) and set `M := Nat.ceil (A ^ (2 * l_n + 1))`.
     Then `M^{1/2} ≥ A^{l_n + 1/2}` makes every irregular term `O(A^{-1/2})`, while
     `M^ε / A = O(A^{-1/2})` makes `‖P_M‖_{n,0,A} → 0` and `‖φ‖_{n,ε,A} → 0`.
   - Step 1.7: The tail operator `Φ_M` is a `(1/2)`-contraction on the closed unit ball in BOTH
     `normN 0 A` and `normN ε A`. The convergent fixed point `vStar` coincides with the actual tail
     `φ` in `normN ε A`, hence `‖φ m‖ ≤ A^m` for all `m ≥ M` and `IsConvergentPS f`.

2. **Section 2 (Reciprocal Gamma & Volterra Formal Series):**
   - Harmonic bound `0 ≤ H_n - log n ≤ 1` and tail `∑_{j=N+1}^n 1/j^2 ≤ 1/N`.
   - Elementary complex inequality `‖1 + w‖ * exp (-w.re) ≤ exp (‖w‖^2 / 2)` applied to
     `Complex.GammaSeq_tendsto_Gamma` gives `‖(Gamma s)⁻¹‖ ≤ exp (6 * (‖s‖ + 1) * log (2 + ‖s‖))`.
   - Cauchy estimate at `R = n / log (n + 2)` + Pochhammer ratio bound gives `IsSubGevrey`.
   - Lower Pochhammer bound + entire Taylor series + Euler reflection at `-m - 1/2` gives
     `¬ IsConvergentPS`.

3. **Section 3 (Volterra Integrals, Watson Expansion, Transcendence Degree Transfer, Virial & Laplace):**
   - Super-exponential decay `‖recipGamma α v‖ ≤ C_α / ⌊v⌋!` on `[0, ∞)` ensures integrability
     and holomorphicity on `{z : ℂ | 0 < z.re}`.
   - General Watson expansion for `F(β, h)(x) = x^{-(β+1)} ∫_0^∞ e^{-v/x} v^β h(v) dv` plus exact
     Euler identity `x * deriv (F β h) x = -(β + 1) F β h x + F (β + 1) h x` yields all-orders
     asymptotics for `δ_x^[k] (volterraNorm β α (1/·))`.
   - Field of fractions of holomorphic functions on `{Re z > 0}` + `trdeg_le_cardinalMk` eliminates
     `(e^{-1/z}, e^{-α/z}, z^{β+1})` to produce a polynomial ADE over `ℂ[x]` for `volterraNorm`.
   - Real nonnegative Tonelli on `(0, ∞) × (0, ∞)` proves `laplace_volterraNu`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.VolterraVirialDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial
open scoped Topology Interval BigOperators

noncomputable section

/-! ## Section 1: Sub-Gevrey Formal Series & Sibuya's Convergence Theorem -/

/-- Geometric coefficient growth characterizing convergent formal power series at `0`:
`∃ C ≥ 0, R > 0, ∀ n, ‖[X^n] f‖ ≤ C * R^n`. -/
@[expose] def IsConvergentPS (f : PowerSeries ℂ) : Prop :=
  ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ n : ℕ, ‖PowerSeries.coeff n f‖ ≤ C * R ^ n

/-- Gevrey formal power series of order `s`:
`∃ C ≥ 0, A > 0, ∀ n, ‖[X^n] f‖ ≤ C * A^n * (n!)^s`. -/
@[expose] def IsGevrey (s : ℝ) (f : PowerSeries ℂ) : Prop :=
  ∃ C A : ℝ, 0 ≤ C ∧ 0 < A ∧
    ∀ n : ℕ, ‖PowerSeries.coeff n f‖ ≤ C * A ^ n * ((n.factorial : ℝ) ^ s)

/-- Sub-Gevrey formal power series: belongs to every positive Gevrey class `s > 0`. -/
@[expose] def IsSubGevrey (f : PowerSeries ℂ) : Prop :=
  ∀ s : ℝ, 0 < s → IsGevrey s f

/-- The Euler derivation `δ = X d/dX` on formal power series `ℂ⟦X⟧`. -/
@[expose] def eulerPS (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.derivative f

/-- Evaluation of a polynomial ADE `P ∈ ℂ[X][Y_0, ..., Y_r]` on a formal power series using
ordinary derivatives `d/dX`. -/
@[expose] def evalDerivPS {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (f : PowerSeries ℂ) : PowerSeries ℂ :=
  MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
    (fun i : Fin (r + 1) => PowerSeries.derivative^[i.1] f) P

/-- Evaluation of a polynomial ADE `P ∈ ℂ[X][Y_0, ..., Y_r]` on a formal power series using
the Euler derivation `δ = X d/dX`. -/
@[expose] def evalEulerPS {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (f : PowerSeries ℂ) : PowerSeries ℂ :=
  MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
    (fun i : Fin (r + 1) => eulerPS^[i.1] f) P

/-! ### 1.1 Basic Coefficient Identities for `eulerPS` and `eulerShift` -/

lemma coeff_eulerPS (f : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m (eulerPS f) = (m : ℂ) * PowerSeries.coeff m f := by
  unfold eulerPS
  cases m with
  | zero =>
    simp [PowerSeries.coeff_zero_X_mul]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

lemma coeff_eulerPS_iter (f : PowerSeries ℂ) (i m : ℕ) :
    PowerSeries.coeff m (eulerPS^[i] f) = (m : ℂ) ^ i * PowerSeries.coeff m f := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', coeff_eulerPS, ih]
    ring

lemma eulerPS_add (f g : PowerSeries ℂ) : eulerPS (f + g) = eulerPS f + eulerPS g := by
  ext m; simp [coeff_eulerPS, mul_add]

lemma eulerPS_sub (f g : PowerSeries ℂ) : eulerPS (f - g) = eulerPS f - eulerPS g := by
  ext m; simp [coeff_eulerPS, mul_sub]

lemma eulerPS_smul (c : ℂ) (f : PowerSeries ℂ) : eulerPS (c • f) = c • eulerPS f := by
  ext m; simp [coeff_eulerPS]; ring

lemma eulerPS_C (c : ℂ) : eulerPS (PowerSeries.C c) = 0 := by
  ext m
  rw [coeff_eulerPS, PowerSeries.coeff_C]
  split_ifs with hm <;> simp [hm]

lemma eulerPS_X : eulerPS (PowerSeries.X : PowerSeries ℂ) = PowerSeries.X := by
  ext m
  rw [coeff_eulerPS, PowerSeries.coeff_X]
  split_ifs with hm <;> simp [hm]

lemma eulerPS_mul (f g : PowerSeries ℂ) :
    eulerPS (f * g) = eulerPS f * g + f * eulerPS g := by
  unfold eulerPS
  rw [PowerSeries.derivative.leibniz]
  simp only [smul_eq_mul]
  ring

lemma eulerPS_iter_add (i : ℕ) (f g : PowerSeries ℂ) :
    eulerPS^[i] (f + g) = eulerPS^[i] f + eulerPS^[i] g := by
  ext m; simp [coeff_eulerPS_iter, mul_add]

/-- The shifted Euler operator `(δ + k)^i` on formal power series. -/
private def eulerShiftIter (k i : ℕ) (ψ : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => ((m + k : ℂ) ^ i) * PowerSeries.coeff m ψ

private lemma coeff_eulerShiftIter (k i : ℕ) (ψ : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m (eulerShiftIter k i ψ) = ((m + k : ℂ) ^ i) * PowerSeries.coeff m ψ := by
  simp [eulerShiftIter]

private lemma eulerPS_iter_X_pow_mul (k i : ℕ) (ψ : PowerSeries ℂ) :
    eulerPS^[i] (PowerSeries.X ^ k * ψ) = PowerSeries.X ^ k * eulerShiftIter k i ψ := by
  ext m
  rw [coeff_eulerPS_iter, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with hm
  · rw [coeff_eulerShiftIter]
    have hmk : (m - k + k : ℕ) = m := Nat.sub_add_cancel hm
    have hmkC : ((m - k : ℕ) : ℂ) + (k : ℂ) = (m : ℂ) := by exact_mod_cast hmk
    rw [hmkC]
  · simp

/-- Polynomial Euler operator `X * p'` matching `eulerPS` on `Polynomial ℂ`. -/
private def polyEuler (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * Polynomial.derivative p

private lemma coe_polyEuler (p : Polynomial ℂ) :
    ((polyEuler p : Polynomial ℂ) : PowerSeries ℂ) = eulerPS (p : PowerSeries ℂ) := by
  ext m
  rw [coeff_eulerPS, Polynomial.coeff_coe, Polynomial.coeff_coe]
  unfold polyEuler
  cases m with
  | zero => simp
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

private lemma coe_polyEuler_iter (i : ℕ) (p : Polynomial ℂ) :
    ((polyEuler^[i] p : Polynomial ℂ) : PowerSeries ℂ) = eulerPS^[i] (p : PowerSeries ℂ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_polyEuler, ih]

/-! ### 1.2 Converting Ordinary-Derivative ADEs to Euler-Derivative ADEs -/

/-- `X^j * f^{(j)} = ∏_{t < j} (δ - t) f`, expressed as a polynomial linear combination of
`eulerPS^[i] f` (`i ≤ j`) with leading coefficient `1` at `i = j`. -/
private def stirlingDerivRow : ℕ → List ℂ
  | 0 => [1]
  | j + 1 =>
    let prev := stirlingDerivRow j
    -- (δ - j) * ∑ c_i δ^i = ∑ c_i δ^{i+1} - j * ∑ c_i δ^i
    let shifted : List ℂ := 0 :: prev
    let scaled : List ℂ := (prev.map fun c => -(j : ℂ) * c) ++ [0]
    List.zipWith (· + ·) shifted scaled

private lemma stirlingDerivRow_length (j : ℕ) : (stirlingDerivRow j).length = j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp [stirlingDerivRow, ih]

private lemma stirlingDerivRow_last (j : ℕ) :
    (stirlingDerivRow j).getD j 0 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlen : (stirlingDerivRow j).length = j + 1 := stirlingDerivRow_length j
    have hget : (stirlingDerivRow j)[j]'(by omega) = 1 := by
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < (stirlingDerivRow j).length)] using ih
    simp [stirlingDerivRow, List.getD_eq_getElem?_getD, hlen, hget]

private lemma stirlingDerivRow_getD_ge (j i : ℕ) (hi : j + 1 ≤ i) :
    (stirlingDerivRow j).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [stirlingDerivRow_length]; omega)]
  rfl

private lemma stirlingDerivRow_succ_getD (j i : ℕ) (hi : i < j + 2) :
    (stirlingDerivRow (j + 1)).getD i 0 =
      (if i = 0 then (0 : ℂ) else (stirlingDerivRow j).getD (i - 1) 0) -
        (j : ℂ) * (stirlingDerivRow j).getD i 0 := by
  have hlen : (stirlingDerivRow j).length = j + 1 := stirlingDerivRow_length j
  simp only [stirlingDerivRow, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  rcases i with _ | k
  · simp [hlen]
  · by_cases hk : k < j + 1
    · by_cases hlt : k + 1 < j + 1
      · simp [List.getElem?_append, hlen, hk, hlt]
        ring
      · have hkeq : k = j := by omega
        rw [hkeq]
        simp [hlen]
    · omega

private lemma X_pow_mul_derivative_iter (f : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.X ^ j * PowerSeries.derivative^[j] f =
      ∑ i ∈ Finset.range (j + 1),
        PowerSeries.C ((stirlingDerivRow j).getD i 0) * eulerPS^[i] f := by
  induction j with
  | zero => simp [stirlingDerivRow]
  | succ j ih =>
    -- Apply `eulerPS` to `X^j * f^{(j)}`:
    -- `δ(X^j f^{(j)}) = j X^j f^{(j)} + X^{j+1} f^{(j+1)}`.
    have hstep : PowerSeries.X ^ (j + 1) * PowerSeries.derivative^[j + 1] f =
        eulerPS (PowerSeries.X ^ j * PowerSeries.derivative^[j] f) -
        (j : ℂ) • (PowerSeries.X ^ j * PowerSeries.derivative^[j] f) := by
      have h1 : eulerPS (PowerSeries.X ^ j * PowerSeries.derivative^[j] f) =
          (j : ℂ) • (PowerSeries.X ^ j * PowerSeries.derivative^[j] f) +
            PowerSeries.X ^ (j + 1) * PowerSeries.derivative^[j + 1] f := by
        rw [eulerPS_mul]
        have hXj : eulerPS (PowerSeries.X ^ j : PowerSeries ℂ) = (j : ℂ) • (PowerSeries.X ^ j) := by
          ext m
          rw [coeff_eulerPS, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow]
          split_ifs with hm <;> simp [hm]
        rw [hXj, smul_mul_assoc, Function.iterate_succ_apply']
        unfold eulerPS
        ring
      rw [h1]
      abel
    rw [hstep, ih]
    ext m
    simp only [map_sub, map_sum, coeff_eulerPS, PowerSeries.coeff_smul, smul_eq_mul,
      PowerSeries.coeff_C_mul, coeff_eulerPS_iter]
    have hlen : (stirlingDerivRow j).length = j + 1 := stirlingDerivRow_length j
    have hzip : ∀ i ∈ Finset.range (j + 2),
        (stirlingDerivRow (j + 1)).getD i 0 =
          (if i = 0 then 0 else (stirlingDerivRow j).getD (i - 1) 0) +
          (if i < j + 1 then -(j : ℂ) * (stirlingDerivRow j).getD i 0 else 0) := by
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [stirlingDerivRow, List.getD_eq_getElem?_getD]
      have h1 : (0 :: stirlingDerivRow j)[i]? =
          if i = 0 then some 0 else (stirlingDerivRow j)[i - 1]? := by
        cases i <;> simp
      have h2 : ((stirlingDerivRow j).map (fun c => -(j : ℂ) * c) ++ [0])[i]? =
          if i < j + 1 then ((stirlingDerivRow j)[i]?).map (fun c => -(j : ℂ) * c)
          else some 0 := by
        by_cases hilt : i < j + 1
        · rw [ite_eq_left_iff.mpr (fun h => absurd hilt h),
            List.getElem?_append_left (by simp [hlen, hilt]), List.getElem?_map]
        · have hi_eq : i = j + 1 := by omega
          subst hi_eq
          rw [ite_eq_right_iff.mpr (fun h => absurd h hilt),
            List.getElem?_append_right (by simp [hlen])]
          simp [hlen]
      rw [List.getElem?_zipWith, h1, h2]
      by_cases hi0 : i = 0
      · subst hi0
        have hj0 : 0 < j + 1 := Nat.succ_pos j
        cases hq : (stirlingDerivRow j)[0]? with
        | none =>
          exfalso; exact (List.getElem?_eq_none_iff.mp hq).not_gt (by omega)
        | some v => simp [hj0]
      · by_cases hilt : i < j + 1
        · cases hq1 : (stirlingDerivRow j)[i - 1]? with
          | none =>
            exfalso; exact (List.getElem?_eq_none_iff.mp hq1).not_gt (by omega)
          | some v1 =>
            cases hq2 : (stirlingDerivRow j)[i]? with
            | none =>
              exfalso; exact (List.getElem?_eq_none_iff.mp hq2).not_gt (by omega)
            | some v2 => simp [hi0, hilt]
        · cases hq1 : (stirlingDerivRow j)[i - 1]? with
          | none =>
            exfalso; exact (List.getElem?_eq_none_iff.mp hq1).not_gt (by omega)
          | some v1 => simp [hi0, hilt]
    have hRHS : ∑ i ∈ Finset.range (j + 2),
        (stirlingDerivRow (j + 1)).getD i 0 * ((m : ℂ) ^ i * PowerSeries.coeff m f) =
        ∑ i ∈ Finset.range (j + 2),
          ((if i = 0 then (0 : ℂ) else (stirlingDerivRow j).getD (i - 1) 0) +
            (if i < j + 1 then -(j : ℂ) * (stirlingDerivRow j).getD i 0 else 0)) *
            ((m : ℂ) ^ i * PowerSeries.coeff m f) :=
      Finset.sum_congr rfl fun i hi => by rw [hzip i hi]
    rw [hRHS]
    simp only [add_mul, Finset.sum_add_distrib]
    have hA : ∑ i ∈ Finset.range (j + 2),
        (if i = 0 then (0 : ℂ) else (stirlingDerivRow j).getD (i - 1) 0) *
          ((m : ℂ) ^ i * PowerSeries.coeff m f) =
        (m : ℂ) * ∑ i ∈ Finset.range (j + 1),
          (stirlingDerivRow j).getD i 0 * ((m : ℂ) ^ i * PowerSeries.coeff m f) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [ite_true, zero_mul, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ite_false, Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ']
      ring
    have hB : ∑ i ∈ Finset.range (j + 2),
        (if i < j + 1 then -(j : ℂ) * (stirlingDerivRow j).getD i 0 else 0) *
          ((m : ℂ) ^ i * PowerSeries.coeff m f) =
        -((j : ℂ) * ∑ i ∈ Finset.range (j + 1),
          (stirlingDerivRow j).getD i 0 * ((m : ℂ) ^ i * PowerSeries.coeff m f)) := by
      rw [Finset.sum_range_succ, Finset.mul_sum, ← Finset.sum_neg_distrib]
      simp only [lt_self_iff_false, ite_false, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [hi, ite_true]
      ring
    rw [hA, hB]
    ring

/-- Convert a nonzero ordinary-derivative ADE `evalDerivPS P f = 0` into a nonzero Euler-derivative
ADE `evalEulerPS Q f = 0` of the same order `r`. -/
lemma exists_nonzero_euler_ade_of_deriv_ade {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : P ≠ 0) {f : PowerSeries ℂ}
    (hf : evalDerivPS P f = 0) :
    ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q ≠ 0 ∧ evalEulerPS Q f = 0 := by
  let D : ℕ := P.totalDegree
  let L : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun j =>
    ∑ i : Fin (r + 1),
      if i.1 ≤ j.1 then
        MvPolynomial.C (Polynomial.C ((stirlingDerivRow j.1).getD i.1 0)) * MvPolynomial.X i
      else 0
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ d ∈ P.support,
      MvPolynomial.C (P.coeff d * Polynomial.X ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j)) *
        ∏ j : Fin (r + 1), (L j) ^ (d j)
  refine ⟨Q, ?_, ?_⟩
  · obtain ⟨d₀, hd₀⟩ := MvPolynomial.support_nonempty.mpr hP
    have hcoeff_ne : P.coeff d₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hd₀
    have hex_x₀ : ∃ x₀ : ℂ, x₀ ≠ 0 ∧ (P.coeff d₀).eval x₀ ≠ 0 := by
      have hne : Polynomial.X * P.coeff d₀ ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hcoeff_ne
      by_contra h
      push Not at h
      have hzero : ∀ x : ℂ, (Polynomial.X * P.coeff d₀).eval x = 0 := by
        intro x
        by_cases hx : x = 0
        · simp [hx]
        · simp [h x hx]
      exact hne (Polynomial.funext fun x => by simpa using hzero x)
    obtain ⟨x₀, hx₀, hpx₀⟩ := hex_x₀
    let ev : Polynomial ℂ →+* ℂ := Polynomial.evalRingHom x₀
    let P_ev : MvPolynomial (Fin (r + 1)) ℂ := MvPolynomial.map ev P
    have hP_ev_ne : P_ev ≠ 0 := by
      intro h0
      have := congr_arg (fun p : MvPolynomial (Fin (r + 1)) ℂ => p.coeff d₀) h0
      simp only [P_ev, ev, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero,
        Polynomial.coe_evalRingHom] at this
      exact hpx₀ this
    let φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ := fun j =>
      MvPolynomial.C (x₀⁻¹ ^ j.1) *
        ∑ i : Fin (r + 1),
          if i.1 ≤ j.1 then
            MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * MvPolynomial.X i
          else 0
    have hQ_ev : MvPolynomial.map ev Q = MvPolynomial.C (x₀ ^ (r * D)) * MvPolynomial.aeval φ P_ev := by
      have hbound : ∀ d ∈ P.support, ∑ j : Fin (r + 1), j.1 * d j ≤ r * D := by
        intro d hd
        calc ∑ j : Fin (r + 1), j.1 * d j
            ≤ ∑ j : Fin (r + 1), r * d j :=
              Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.2)
          _ = r * ∑ j : Fin (r + 1), d j := (Finset.mul_sum ..).symm
          _ = r * d.sum (fun _ m => m) := by
              congr 1; rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
          _ ≤ r * D := Nat.mul_le_mul_left _ (MvPolynomial.le_totalDegree hd)
      have hP_ev_sum : MvPolynomial.aeval φ P_ev =
          ∑ d ∈ P.support, MvPolynomial.C (ev (P.coeff d)) * ∏ j : Fin (r + 1), (φ j) ^ (d j) := by
        dsimp only [P_ev]
        conv_lhs => rw [P.as_sum]
        simp only [map_sum, MvPolynomial.map_monomial, MvPolynomial.aeval_monomial,
          MvPolynomial.C_eq_smul_one]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        simp [Algebra.smul_def]
      rw [hP_ev_sum, Finset.mul_sum]
      simp only [Q, map_sum, map_mul, map_prod, map_pow, MvPolynomial.map_C]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hbd := hbound d hd
      have hpow : x₀ ^ (r * D) * ∏ j : Fin (r + 1), (x₀⁻¹ ^ j.1) ^ (d j) =
          x₀ ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j) := by
        have hprod : ∏ j : Fin (r + 1), (x₀⁻¹ ^ j.1) ^ (d j) =
            (x₀ ^ (∑ j : Fin (r + 1), j.1 * d j))⁻¹ := by
          simp_rw [← pow_mul, ← inv_pow, Finset.prod_pow_eq_pow_sum]
        rw [hprod, ← div_eq_mul_inv, pow_sub₀ _ hx₀ hbd, div_eq_mul_inv]
      have hLmap : ∀ j : Fin (r + 1), MvPolynomial.map ev (L j) =
          ∑ i : Fin (r + 1),
            if i.1 ≤ j.1 then
              MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * MvPolynomial.X i
            else 0 := by
        intro j
        simp only [L, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp [ev]
      simp only [φ, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, hLmap]
      simp only [ev, Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X]
      have hCpow : MvPolynomial.C (σ := Fin (r + 1)) (x₀ ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j)) =
          MvPolynomial.C (x₀ ^ (r * D)) * MvPolynomial.C (∏ j : Fin (r + 1), (x₀⁻¹ ^ j.1) ^ (d j)) := by
        rw [← hpow]
        exact map_mul (MvPolynomial.C (σ := Fin (r + 1))) _ _
      rw [hCpow]
      ring
    have hφ_inj : Function.Injective (MvPolynomial.aeval (R := ℂ) φ) := by
      have hinv : ∀ m : ℕ, m ≤ r + 1 →
          ∃ ψ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ,
            ∀ j : Fin (r + 1), j.1 < m → MvPolynomial.aeval (R := ℂ) ψ (φ j) = MvPolynomial.X j := by
        intro m
        induction m with
        | zero => intro _; exact ⟨MvPolynomial.X, fun j hj => by omega⟩
        | succ m ih =>
          intro hm
          obtain ⟨ψ, hψ⟩ := ih (by omega)
          let j₀ : Fin (r + 1) := ⟨m, hm⟩
          let val₀ : MvPolynomial (Fin (r + 1)) ℂ :=
            MvPolynomial.C (x₀ ^ m) * MvPolynomial.X j₀ -
              ∑ i : Fin (r + 1),
                if i.1 < m then
                  MvPolynomial.C ((stirlingDerivRow m).getD i.1 0) * ψ i
                else 0
          let ψ' : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ := fun i =>
            if i = j₀ then val₀ else ψ i
          refine ⟨ψ', fun j hj => ?_⟩
          have hφ_eval : ∀ k : Fin (r + 1),
              MvPolynomial.aeval (R := ℂ) ψ' (φ k) =
                MvPolynomial.C (x₀⁻¹ ^ k.1) *
                  ∑ i : Fin (r + 1),
                    if i.1 ≤ k.1 then
                      MvPolynomial.C ((stirlingDerivRow k.1).getD i.1 0) * ψ' i
                    else 0 := by
            intro k
            simp only [φ, map_mul, map_sum, MvPolynomial.aeval_C]
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs <;> simp
          by_cases hjm : j.1 < m
          · rw [hφ_eval j]
            have hsum_eq : ∑ i : Fin (r + 1),
                (if i.1 ≤ j.1 then MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * ψ' i else 0) =
              ∑ i : Fin (r + 1),
                (if i.1 ≤ j.1 then MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * ψ i else 0) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              split_ifs with hij
              · have hne : i ≠ j₀ := by
                  intro heq; subst heq; dsimp [j₀] at hij; omega
                simp [ψ', hne]
              · rfl
            rw [hsum_eq]
            have hprev := hψ j hjm
            rw [← hprev]
            simp only [φ, map_mul, map_sum, MvPolynomial.aeval_C]
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs <;> simp
          · have hjeq : j = j₀ := Fin.ext (by dsimp [j₀]; omega)
            subst hjeq
            rw [hφ_eval j₀]
            have hsplit : ∑ i : Fin (r + 1),
                (if i.1 ≤ m then MvPolynomial.C ((stirlingDerivRow m).getD i.1 0) * ψ' i else 0) =
                MvPolynomial.C ((stirlingDerivRow m).getD m 0) * ψ' j₀ +
                ∑ i : Fin (r + 1),
                  (if i.1 < m then MvPolynomial.C ((stirlingDerivRow m).getD i.1 0) * ψ i else 0) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
              have hj0m : j₀.1 ≤ m := le_rfl
              simp only [j₀, hj0m, ite_true]
              congr 1
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨m, hm⟩ : Fin (r + 1)))]
              simp only [lt_self_iff_false, ite_false, zero_add]
              refine Finset.sum_congr rfl fun i hi => ?_
              have hne : i ≠ ⟨m, hm⟩ := (Finset.mem_erase.mp hi).1
              have hval_ne : i.1 ≠ m := fun h => hne (Fin.ext h)
              have hiff : i.1 ≤ m ↔ i.1 < m := by omega
              simp only [hiff]
              split_ifs with hlt
              · simp [ψ', j₀, hne]
              · rfl
            dsimp only [j₀]
            rw [hsplit, stirlingDerivRow_last m, map_one, one_mul]
            have hψ'j : ψ' j₀ = val₀ := by simp [ψ']
            rw [hψ'j]
            simp only [val₀, sub_add_cancel, ← mul_assoc, ← map_mul, ← mul_pow,
              inv_mul_cancel₀ hx₀, one_pow, map_one, one_mul]
            rfl
      obtain ⟨ψ, hψ⟩ := hinv (r + 1) le_rfl
      have hcomp : ∀ p : MvPolynomial (Fin (r + 1)) ℂ,
          MvPolynomial.aeval (R := ℂ) ψ (MvPolynomial.aeval (R := ℂ) φ p) = p := by
        intro p
        induction p using MvPolynomial.induction_on with
        | C c => simp
        | add p q hp hq => rw [map_add, map_add, hp, hq]
        | mul_X p j hp =>
          simp only [map_mul, hp, MvPolynomial.aeval_X, hψ j j.2]
      intro p q hpq
      have := congr_arg (MvPolynomial.aeval (R := ℂ) ψ) hpq
      rwa [hcomp, hcomp] at this
    intro hQ0
    rw [hQ0, map_zero] at hQ_ev
    have hpow_ne : MvPolynomial.C (x₀ ^ (r * D)) ≠ (0 : MvPolynomial (Fin (r + 1)) ℂ) := by
      intro hc
      exact pow_ne_zero _ hx₀ (MvPolynomial.C_eq_zero.mp hc)
    have haeval0 : MvPolynomial.aeval (R := ℂ) φ P_ev = 0 :=
      (mul_eq_zero.mp hQ_ev.symm).resolve_left hpow_ne
    exact hP_ev_ne (hφ_inj (by rw [haeval0, map_zero]))
  · have hL_eval : ∀ j : Fin (r + 1),
        evalEulerPS (L j) f = PowerSeries.X ^ j.1 * PowerSeries.derivative^[j.1] f := by
      intro j
      rw [X_pow_mul_derivative_iter]
      unfold evalEulerPS
      dsimp only [L]
      rw [MvPolynomial.eval₂_sum]
      have hsum : ∑ i : Fin (r + 1),
          MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
            (fun i : Fin (r + 1) => eulerPS^[i.1] f)
            (if i.1 ≤ j.1 then
              MvPolynomial.C (Polynomial.C ((stirlingDerivRow j.1).getD i.1 0)) * MvPolynomial.X i
            else 0) =
          ∑ i : Fin (r + 1),
            if i.1 ≤ j.1 then
              PowerSeries.C ((stirlingDerivRow j.1).getD i.1 0) * eulerPS^[i.1] f
            else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [hsum]
      rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ j.1 then
          PowerSeries.C ((stirlingDerivRow j.1).getD i 0) * eulerPS^[i] f else 0)]
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have hbound : ∀ d ∈ P.support, ∑ j : Fin (r + 1), j.1 * d j ≤ r * D := by
      intro d hd
      calc ∑ j : Fin (r + 1), j.1 * d j
          ≤ ∑ j : Fin (r + 1), r * d j :=
            Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.2)
        _ = r * ∑ j : Fin (r + 1), d j := (Finset.mul_sum ..).symm
        _ = r * d.sum (fun _ m => m) := by
            congr 1; rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        _ ≤ r * D := Nat.mul_le_mul_left _ (MvPolynomial.le_totalDegree hd)
    have hQ_eq : evalEulerPS Q f = PowerSeries.X ^ (r * D) * evalDerivPS P f := by
      unfold evalEulerPS evalDerivPS
      dsimp only [Q]
      rw [MvPolynomial.eval₂_sum]
      conv_rhs => rw [P.as_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hbd := hbound d hd
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod,
        MvPolynomial.eval₂_monomial]
      have hprod : ∏ j : Fin (r + 1),
          MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
            (fun i : Fin (r + 1) => eulerPS^[i.1] f) ((L j) ^ (d j)) =
          PowerSeries.X ^ (∑ j : Fin (r + 1), j.1 * d j) *
            ∏ j : Fin (r + 1), (PowerSeries.derivative^[j.1] f) ^ (d j) := by
        have h1 : ∀ j : Fin (r + 1),
            MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
              (fun i : Fin (r + 1) => eulerPS^[i.1] f) ((L j) ^ (d j)) =
            PowerSeries.X ^ (j.1 * d j) * (PowerSeries.derivative^[j.1] f) ^ (d j) := by
          intro j
          rw [MvPolynomial.eval₂_pow,
            show MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
              (fun i : Fin (r + 1) => eulerPS^[i.1] f) (L j) = evalEulerPS (L j) f from rfl,
            hL_eval j, mul_pow, ← pow_mul]
        simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hprod, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul,
        Polynomial.coe_pow, Polynomial.coe_X]
      calc (P.coeff d : PowerSeries ℂ) * PowerSeries.X ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j) *
            (PowerSeries.X ^ (∑ j : Fin (r + 1), j.1 * d j) *
              ∏ j : Fin (r + 1), (PowerSeries.derivative^[j.1] f) ^ (d j))
          = (PowerSeries.X ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j) *
              PowerSeries.X ^ (∑ j : Fin (r + 1), j.1 * d j)) *
            ((P.coeff d : PowerSeries ℂ) * ∏ j : Fin (r + 1), (PowerSeries.derivative^[j.1] f) ^ (d j)) := by
            ring
        _ = PowerSeries.X ^ (r * D) *
            ((P.coeff d : PowerSeries ℂ) * ∏ j : Fin (r + 1), (PowerSeries.derivative^[j.1] f) ^ (d j)) := by
            rw [← pow_add, Nat.sub_add_cancel hbd]
    rw [hQ_eq, hf, mul_zero]

/-! ### 1.3 Minimality Reduction: Nonvanishing Top Partial Derivative -/

/-- If `f` satisfies some nonzero Euler ADE, it satisfies one of minimal order `n` and minimal
degree in `Y_n`, so that `(∂F/∂Y_n)(X, f, δf, ..., δ^n f) ≠ 0`. -/
private lemma exists_minimal_euler_ade {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : P ≠ 0) {f : PowerSeries ℂ}
    (hf : evalEulerPS P f = 0) :
    ∃ (n : ℕ) (F : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)),
      F ≠ 0 ∧ evalEulerPS F f = 0 ∧
      evalEulerPS (MvPolynomial.pderiv (Fin.last n) F) f ≠ 0 := by
  have hex : ∃ n : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) (Polynomial ℂ),
      F ≠ 0 ∧ evalEulerPS F f = 0 := ⟨r, P, hP, hf⟩
  classical
  obtain ⟨n, hn_spec, hn_min⟩ :
      ∃ n : ℕ, (∃ F : MvPolynomial (Fin (n + 1)) (Polynomial ℂ), F ≠ 0 ∧ evalEulerPS F f = 0) ∧
        (∀ m < n, ¬ ∃ F : MvPolynomial (Fin (m + 1)) (Polynomial ℂ), F ≠ 0 ∧ evalEulerPS F f = 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hex_deg : ∃ d : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) (Polynomial ℂ),
      F ≠ 0 ∧ evalEulerPS F f = 0 ∧ F.degreeOf (Fin.last n) = d := by
    obtain ⟨F, hFne, hFeval⟩ := hn_spec
    exact ⟨F.degreeOf (Fin.last n), F, hFne, hFeval, rfl⟩
  obtain ⟨d, ⟨F, hFne, hFeval, hFdeg⟩, hd_min⟩ :
      ∃ d : ℕ, (∃ F : MvPolynomial (Fin (n + 1)) (Polynomial ℂ),
        F ≠ 0 ∧ evalEulerPS F f = 0 ∧ F.degreeOf (Fin.last n) = d) ∧
        (∀ d' < d, ¬ ∃ F : MvPolynomial (Fin (n + 1)) (Polynomial ℂ),
          F ≠ 0 ∧ evalEulerPS F f = 0 ∧ F.degreeOf (Fin.last n) = d') :=
    ⟨Nat.find hex_deg, Nat.find_spec hex_deg, fun d' hd' => Nat.find_min hex_deg hd'⟩
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd_eq : d = 0 := by omega
    rw [hd_eq] at hFdeg
    have hlast0 : ∀ s ∈ F.support, s (Fin.last n) = 0 := by
      intro s hs
      have hle : s (Fin.last n) ≤ F.degreeOf (Fin.last n) := by
        rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.le_sup (f := fun t => t (Fin.last n)) hs
      omega
    cases n with
    | zero =>
      have hFc : F = MvPolynomial.C (F.coeff 0) := by
        refine MvPolynomial.ext F (MvPolynomial.C (F.coeff 0)) fun s => ?_
        by_cases hs : s = 0
        · subst hs; simp
        · rw [MvPolynomial.coeff_C, ite_eq_right_iff.mpr (fun h => absurd h.symm hs)]
          by_contra hne
          have hmem : s ∈ F.support := MvPolynomial.mem_support_iff.mpr hne
          have hs0 : s 0 = 0 := hlast0 s hmem
          apply hs
          ext i; fin_cases i; exact hs0
      have hpne : F.coeff 0 ≠ 0 := by
        intro h0; rw [h0, map_zero] at hFc; exact hFne hFc
      rw [hFc] at hFeval
      simp only [evalEulerPS, MvPolynomial.eval₂_C, Polynomial.coeToPowerSeries.ringHom_apply] at hFeval
      apply hpne
      ext m
      have hm := congr_arg (PowerSeries.coeff m) hFeval
      simpa using hm
    | succ m =>
      let emb : Fin (m + 1) → Fin (m + 2) := Fin.castSucc
      let G : MvPolynomial (Fin (m + 1)) (Polynomial ℂ) :=
        ∑ s ∈ F.support, MvPolynomial.monomial (s.comapDomain emb (by
          intro a _ b _ h; exact Fin.castSucc_injective (m + 1) h)) (F.coeff s)
      have hGne : G ≠ 0 := by
        obtain ⟨s₀, hs₀⟩ := MvPolynomial.support_nonempty.mpr hFne
        intro hG0
        have hc := congr_arg (fun p : MvPolynomial (Fin (m + 1)) (Polynomial ℂ) =>
          p.coeff (s₀.comapDomain emb (fun a _ b _ h => Fin.castSucc_injective (m + 1) h))) hG0
        simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
          AddMonoidAlgebra.coeff_zero] at hc
        have hsing : ∑ s ∈ F.support,
            (if s.comapDomain emb (fun a _ b _ h => Fin.castSucc_injective (m + 1) h) =
                s₀.comapDomain emb (fun a _ b _ h => Fin.castSucc_injective (m + 1) h)
              then F.coeff s else 0) =
            F.coeff s₀ := by
          rw [Finset.sum_eq_single s₀]
          · simp
          · intro s hs hne
            refine ite_eq_right_iff.mpr fun heq => absurd ?_ hne
            ext j
            refine Fin.lastCases ?_ (fun i => ?_) j
            · rw [hlast0 s hs, hlast0 s₀ hs₀]
            · exact congr_arg (fun g => g i) heq
          · intro hnot; exact absurd hs₀ hnot
        rw [hsing] at hc
        exact MvPolynomial.mem_support_iff.mp hs₀ hc
      have hGeval : evalEulerPS G f = 0 := by
        have hrel : evalEulerPS G f = evalEulerPS F f := by
          unfold evalEulerPS
          conv_rhs => rw [F.as_sum, MvPolynomial.eval₂_sum]
          dsimp only [G]
          rw [MvPolynomial.eval₂_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial]
          congr 1
          rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
            Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
          conv_rhs => rw [Fin.prod_univ_castSucc, hlast0 s hs, pow_zero, mul_one]
          refine Finset.prod_congr rfl fun i _ => rfl
        rw [hrel, hFeval]
      exact hn_min m (Nat.lt_succ_self m) ⟨G, hGne, hGeval⟩
  let G := MvPolynomial.pderiv (Fin.last n) F
  have hGne : G ≠ 0 := by
    have hex_s : ∃ s ∈ F.support, s (Fin.last n) = d := by
      rw [← hFdeg]
      have hne : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hFne
      obtain ⟨s, hs, hmax⟩ := F.support.exists_max_image (fun s => s (Fin.last n)) hne
      refine ⟨s, hs, le_antisymm ?_ ?_⟩
      · rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.le_sup (f := fun t => t (Fin.last n)) hs
      · rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.sup_le fun t ht => hmax t ht
    obtain ⟨s, hs, hsd⟩ := hex_s
    intro hG0
    let s' : Fin (n + 1) →₀ ℕ := s - Finsupp.single (Fin.last n) 1
    have hs_eq : s' + Finsupp.single (Fin.last n) 1 = s := by
      ext j
      by_cases hj : j = Fin.last n
      · subst hj; simp [s', hsd]; omega
      · simp [s', hj]
    have hc := congr_arg (fun p : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) => p.coeff s') hG0
    rw [MvPolynomial.coeff_pderiv, hs_eq, AddMonoidAlgebra.coeff_zero] at hc
    have hdne : ((s' (Fin.last n) + 1 : ℕ) : Polynomial ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    have hcoeff0 : F.coeff s = 0 := (mul_eq_zero.mp (by simpa [mul_comm] using hc)).resolve_left hdne
    exact MvPolynomial.mem_support_iff.mp hs hcoeff0
  have hGdeg : G.degreeOf (Fin.last n) < d := by
    rw [MvPolynomial.degreeOf_eq_sup]
    refine (Finset.sup_lt_iff hd_pos).mpr fun s' hs' => ?_
    have hc_ne : G.coeff s' ≠ 0 := MvPolynomial.mem_support_iff.mp hs'
    rw [MvPolynomial.coeff_pderiv] at hc_ne
    let t : Fin (n + 1) →₀ ℕ := s' + Finsupp.single (Fin.last n) 1
    have hmem : t ∈ F.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      exact hc_ne (by simp [t, h0])
    have hle : t (Fin.last n) ≤ F.degreeOf (Fin.last n) := by
      rw [MvPolynomial.degreeOf_eq_sup]
      exact Finset.le_sup (f := fun u : Fin (n + 1) →₀ ℕ => u (Fin.last n)) hmem
    have hval : t (Fin.last n) = s' (Fin.last n) + 1 := by simp [t]
    rw [hval, hFdeg] at hle
    omega
  refine ⟨n, F, hFne, hFeval, fun hGeval => ?_⟩
  exact hd_min (G.degreeOf (Fin.last n)) hGdeg ⟨G, hGne, hGeval, rfl⟩

/-! ### 1.4 Weighted `ℓ¹` Sequence Spaces & Simultaneous Banach Contraction -/

/-- Positive weight `w s A m = A^m * (m!)^s`. -/
private def gWeight (s A : ℝ) (m : ℕ) : ℝ :=
  A ^ m * ((m.factorial : ℝ) ^ s)

private lemma gWeight_pos {s A : ℝ} (hA : 0 < A) (m : ℕ) : 0 < gWeight s A m :=
  mul_pos (pow_pos hA m) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) s)

private lemma gWeight_zero_eq (A : ℝ) (m : ℕ) : gWeight 0 A m = A ^ m := by
  simp [gWeight]

private lemma gWeight_le_of_le {s₁ s₂ A : ℝ} (hs : s₁ ≤ s₂) (hA : 0 < A) (m : ℕ) :
    gWeight s₁ A m ≤ gWeight s₂ A m := by
  unfold gWeight
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA.le m)
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (Nat.factorial_pos m)) hs

private lemma gWeight_mul_le {s A : ℝ} (hs : 0 ≤ s) (hA : 0 < A) (a b : ℕ) :
    gWeight s A a * gWeight s A b ≤ gWeight s A (a + b) := by
  unfold gWeight
  calc A ^ a * (a.factorial : ℝ) ^ s * (A ^ b * (b.factorial : ℝ) ^ s)
      = A ^ (a + b) * (((a.factorial : ℝ) * (b.factorial : ℝ)) ^ s) := by
        rw [pow_add, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        ring
    _ ≤ A ^ (a + b) * (((a + b).factorial : ℝ) ^ s) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA.le _)
        refine Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ hs
        exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
          (Nat.factorial_mul_factorial_dvd_factorial_add a b)

/-- `0`-norm summability and value on sequences `ℕ → ℂ`. -/
private def Summable0 (s A : ℝ) (u : ℕ → ℂ) : Prop :=
  Summable fun m : ℕ => ‖u m‖ / gWeight s A m

private def norm0 (s A : ℝ) (u : ℕ → ℂ) : ℝ :=
  ∑' m : ℕ, ‖u m‖ / gWeight s A m

/-- `n`-norm summability and value on sequences `ℕ → ℂ`, with Euler factor `(m + k)^n`. -/
private def SummableN (k n : ℕ) (s A : ℝ) (v : ℕ → ℂ) : Prop :=
  Summable fun m : ℕ => (((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ / gWeight s A m

private def normN (k n : ℕ) (s A : ℝ) (v : ℕ → ℂ) : ℝ :=
  ∑' m : ℕ, (((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ / gWeight s A m

/-- Cauchy convolution product on sequences `ℕ → ℂ`. -/
private def seqMul (u v : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), u j * v (m - j)

private lemma coeff_mul_eq_seqMul (f g : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m (f * g) =
      seqMul (fun j => PowerSeries.coeff j f) (fun j => PowerSeries.coeff j g) m := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
    PowerSeries.coeff a f * PowerSeries.coeff b g)]
  rfl

private lemma norm0_nonneg {s A : ℝ} (hA : 0 < A) (u : ℕ → ℂ) : 0 ≤ norm0 s A u :=
  tsum_nonneg fun m => div_nonneg (norm_nonneg _) (gWeight_pos hA m).le

private lemma normN_nonneg {k n : ℕ} {s A : ℝ} (hA : 0 < A) (v : ℕ → ℂ) :
    0 ≤ normN k n s A v :=
  tsum_nonneg fun m =>
    div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _)) (gWeight_pos hA m).le

private lemma summable0_of_le {s₁ s₂ A : ℝ} (hs : s₁ ≤ s₂) (hA : 0 < A) {u : ℕ → ℂ}
    (hu : Summable0 s₁ A u) : Summable0 s₂ A u :=
  Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (gWeight_pos hA m).le)
    (fun m => div_le_div_of_nonneg_left (norm_nonneg _) (gWeight_pos hA m) (gWeight_le_of_le hs hA m))
    hu

private lemma norm0_le_of_le {s₁ s₂ A : ℝ} (hs : s₁ ≤ s₂) (hA : 0 < A) {u : ℕ → ℂ}
    (hu : Summable0 s₁ A u) : norm0 s₂ A u ≤ norm0 s₁ A u :=
  Summable.tsum_le_tsum
    (fun m => div_le_div_of_nonneg_left (norm_nonneg _) (gWeight_pos hA m) (gWeight_le_of_le hs hA m))
    (summable0_of_le hs hA hu) hu

private lemma summableN_of_le {k n : ℕ} {s₁ s₂ A : ℝ} (hs : s₁ ≤ s₂) (hA : 0 < A) {v : ℕ → ℂ}
    (hv : SummableN k n s₁ A v) : SummableN k n s₂ A v :=
  Summable.of_nonneg_of_le
    (fun m => div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
      (gWeight_pos hA m).le)
    (fun m => div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
      (gWeight_pos hA m) (gWeight_le_of_le hs hA m))
    hv

private lemma normN_le_of_le {k n : ℕ} {s₁ s₂ A : ℝ} (hs : s₁ ≤ s₂) (hA : 0 < A) {v : ℕ → ℂ}
    (hv : SummableN k n s₁ A v) : normN k n s₂ A v ≤ normN k n s₁ A v :=
  Summable.tsum_le_tsum
    (fun m => div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
      (gWeight_pos hA m) (gWeight_le_of_le hs hA m))
    (summableN_of_le hs hA hv) hv

private lemma summable0_zero (s A : ℝ) : Summable0 s A 0 := by
  simp [Summable0]

private lemma norm0_zero (s A : ℝ) : norm0 s A 0 = 0 := by
  simp [norm0]

private lemma summableN_zero (k n : ℕ) (s A : ℝ) : SummableN k n s A 0 := by
  simp [SummableN]

private lemma normN_zero (k n : ℕ) (s A : ℝ) : normN k n s A 0 = 0 := by
  simp [normN]

private lemma summable0_add {s A : ℝ} (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : Summable0 s A u) (hv : Summable0 s A v) : Summable0 s A (u + v) := by
  refine Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (gWeight_pos hA m).le)
    (fun m => ?_) (hu.add hv)
  calc ‖(u + v) m‖ / gWeight s A m
      ≤ (‖u m‖ + ‖v m‖) / gWeight s A m :=
        div_le_div_of_nonneg_right (norm_add_le (u m) (v m)) (gWeight_pos hA m).le
    _ = ‖u m‖ / gWeight s A m + ‖v m‖ / gWeight s A m := add_div _ _ _

private lemma norm0_add_le {s A : ℝ} (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : Summable0 s A u) (hv : Summable0 s A v) :
    norm0 s A (u + v) ≤ norm0 s A u + norm0 s A v := by
  unfold norm0
  rw [← Summable.tsum_add hu hv]
  refine Summable.tsum_le_tsum (fun m => ?_) (summable0_add hA hu hv) (hu.add hv)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le (u m) (v m)) (gWeight_pos hA m).le

private lemma summable0_neg {s A : ℝ} {u : ℕ → ℂ} (hu : Summable0 s A u) :
    Summable0 s A (-u) := by
  simpa [Summable0] using hu

private lemma norm0_neg {s A : ℝ} (u : ℕ → ℂ) : norm0 s A (-u) = norm0 s A u := by
  simp [norm0]

private lemma summable0_sub {s A : ℝ} (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : Summable0 s A u) (hv : Summable0 s A v) : Summable0 s A (u - v) := by
  rw [sub_eq_add_neg]; exact summable0_add hA hu (summable0_neg hv)

private lemma norm0_sub_le {s A : ℝ} (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : Summable0 s A u) (hv : Summable0 s A v) :
    norm0 s A (u - v) ≤ norm0 s A u + norm0 s A v := by
  rw [sub_eq_add_neg, ← norm0_neg v]
  exact norm0_add_le hA hu (summable0_neg hv)

private lemma summable0_const_mul {s A : ℝ} (c : ℂ) {u : ℕ → ℂ} (hu : Summable0 s A u) :
    Summable0 s A (fun m => c * u m) := by
  have : (fun m => ‖c * u m‖ / gWeight s A m) = fun m => ‖c‖ * (‖u m‖ / gWeight s A m) := by
    ext m; rw [norm_mul, mul_div_assoc]
  unfold Summable0; rw [this]; exact hu.mul_left ‖c‖

private lemma norm0_const_mul {s A : ℝ} (c : ℂ) (u : ℕ → ℂ) :
    norm0 s A (fun m => c * u m) = ‖c‖ * norm0 s A u := by
  unfold norm0
  simp_rw [norm_mul, mul_div_assoc]
  rw [tsum_mul_left]

private lemma summable0_of_finite_support {s A : ℝ} {u : ℕ → ℂ} (N : ℕ)
    (h : ∀ m ≥ N, u m = 0) : Summable0 s A u := by
  refine summable_of_ne_finset_zero (s := Finset.range N) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  simp [h m hm]

private lemma summableN_add {k n : ℕ} {s A : ℝ} (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : SummableN k n s A u) (hv : SummableN k n s A v) : SummableN k n s A (u + v) := by
  refine Summable.of_nonneg_of_le
    (fun m => div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
      (gWeight_pos hA m).le)
    (fun m => ?_) (hu.add hv)
  calc (((m + k : ℕ) : ℝ) ^ n) * ‖(u + v) m‖ / gWeight s A m
      ≤ (((m + k : ℕ) : ℝ) ^ n) * (‖u m‖ + ‖v m‖) / gWeight s A m :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_add_le (u m) (v m)) (pow_nonneg (Nat.cast_nonneg _) n))
          (gWeight_pos hA m).le
    _ = (((m + k : ℕ) : ℝ) ^ n) * ‖u m‖ / gWeight s A m +
          (((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ / gWeight s A m := by ring

private lemma normN_add_le {k n : ℕ} {s A : ℝ} (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : SummableN k n s A u) (hv : SummableN k n s A v) :
    normN k n s A (u + v) ≤ normN k n s A u + normN k n s A v := by
  unfold normN
  rw [← Summable.tsum_add hu hv]
  refine Summable.tsum_le_tsum (fun m => ?_) (summableN_add hA hu hv) (hu.add hv)
  rw [← add_div, ← mul_add]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_add_le (u m) (v m)) (pow_nonneg (Nat.cast_nonneg _) n))
    (gWeight_pos hA m).le

private lemma summableN_neg {k n : ℕ} {s A : ℝ} {u : ℕ → ℂ} (hu : SummableN k n s A u) :
    SummableN k n s A (-u) := by
  simpa [SummableN] using hu

private lemma summableN_sub {k n : ℕ} {s A : ℝ} (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : SummableN k n s A u) (hv : SummableN k n s A v) : SummableN k n s A (u - v) := by
  rw [sub_eq_add_neg]; exact summableN_add hA hu (summableN_neg hv)

private lemma normN_sub_comm {k n : ℕ} {s A : ℝ} (u v : ℕ → ℂ) :
    normN k n s A (u - v) = normN k n s A (v - u) := by
  unfold normN
  congr 1; ext m; simp [norm_sub_rev]

/-- Banach algebra inequality for Cauchy convolution in the weighted `ℓ¹` `0`-norm. -/
private lemma summable0_and_norm0_seqMul {s A : ℝ} (hs : 0 ≤ s) (hA : 0 < A) {u v : ℕ → ℂ}
    (hu : Summable0 s A u) (hv : Summable0 s A v) :
    Summable0 s A (seqMul u v) ∧ norm0 s A (seqMul u v) ≤ norm0 s A u * norm0 s A v := by
  have hpart : ∀ N : ℕ, ∑ m ∈ Finset.range N, ‖seqMul u v m‖ / gWeight s A m ≤
      norm0 s A u * norm0 s A v := by
    intro N
    have h1 : ∀ m : ℕ, ‖seqMul u v m‖ / gWeight s A m ≤
        ∑ j ∈ Finset.range (m + 1), (‖u j‖ / gWeight s A j) * (‖v (m - j)‖ / gWeight s A (m - j)) := by
      intro m
      unfold seqMul
      calc ‖∑ j ∈ Finset.range (m + 1), u j * v (m - j)‖ / gWeight s A m
          ≤ (∑ j ∈ Finset.range (m + 1), ‖u j‖ * ‖v (m - j)‖) / gWeight s A m := by
            refine div_le_div_of_nonneg_right ?_ (gWeight_pos hA m).le
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by rw [norm_mul])
        _ = ∑ j ∈ Finset.range (m + 1), (‖u j‖ * ‖v (m - j)‖) / gWeight s A m := Finset.sum_div ..
        _ ≤ ∑ j ∈ Finset.range (m + 1),
              (‖u j‖ / gWeight s A j) * (‖v (m - j)‖ / gWeight s A (m - j)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_range] at hj
            rw [div_mul_div_comm]
            have hm_eq : j + (m - j) = m := Nat.add_sub_of_le (Nat.lt_succ_iff.mp hj)
            refine div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (mul_pos (gWeight_pos hA j) (gWeight_pos hA (m - j))) ?_
            have hg := gWeight_mul_le hs hA j (m - j)
            rwa [hm_eq] at hg
    have h2 : ∑ m ∈ Finset.range N,
          ∑ j ∈ Finset.range (m + 1),
            (‖u j‖ / gWeight s A j) * (‖v (m - j)‖ / gWeight s A (m - j)) ≤
        (∑ a ∈ Finset.range N, ‖u a‖ / gWeight s A a) *
          (∑ b ∈ Finset.range N, ‖v b‖ / gWeight s A b) := by
      rw [Finset.sum_mul_sum]
      let S := (Finset.range N).sigma fun m => Finset.range (m + 1)
      let f : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2, p.1 - p.2)
      let g : ℕ × ℕ → ℝ := fun x => (‖u x.1‖ / gWeight s A x.1) * (‖v x.2‖ / gWeight s A x.2)
      have hf_inj : Set.InjOn f (S : Set (Σ _ : ℕ, ℕ)) := by
        intro p hp q hq heq
        simp only [S, Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hp hq
        have h1 : p.2 = q.2 := congr_arg Prod.fst heq
        have h2 : p.1 - p.2 = q.1 - q.2 := congr_arg Prod.snd heq
        have hp_eq : p.1 = q.1 := by omega
        cases p; cases q; dsimp at hp_eq h1; subst hp_eq h1; rfl
      have hsub : S.image f ⊆ Finset.range N ×ˢ Finset.range N := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
        simp only [S, Finset.mem_sigma, Finset.mem_range] at hp
        simp only [f, Finset.mem_product, Finset.mem_range]
        omega
      calc ∑ m ∈ Finset.range N,
            ∑ j ∈ Finset.range (m + 1),
              (‖u j‖ / gWeight s A j) * (‖v (m - j)‖ / gWeight s A (m - j))
          = ∑ p ∈ S, g (f p) := by rw [Finset.sum_sigma]
        _ = ∑ x ∈ S.image f, g x :=
            (Finset.sum_image (f := g) (g := f) (fun p hp q hq heq => hf_inj hp hq heq)).symm
        _ ≤ ∑ x ∈ Finset.range N ×ˢ Finset.range N, g x :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
              mul_nonneg (div_nonneg (norm_nonneg _) (gWeight_pos hA _).le)
                (div_nonneg (norm_nonneg _) (gWeight_pos hA _).le)
        _ = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
              (‖u a‖ / gWeight s A a) * (‖v b‖ / gWeight s A b) :=
            Finset.sum_product ..
    calc ∑ m ∈ Finset.range N, ‖seqMul u v m‖ / gWeight s A m
        ≤ ∑ m ∈ Finset.range N,
            ∑ j ∈ Finset.range (m + 1),
              (‖u j‖ / gWeight s A j) * (‖v (m - j)‖ / gWeight s A (m - j)) :=
          Finset.sum_le_sum fun m _ => h1 m
      _ ≤ (∑ a ∈ Finset.range N, ‖u a‖ / gWeight s A a) *
            (∑ b ∈ Finset.range N, ‖v b‖ / gWeight s A b) := h2
      _ ≤ norm0 s A u * norm0 s A v := by
          refine mul_le_mul ?_ ?_
            (Finset.sum_nonneg fun b _ => div_nonneg (norm_nonneg _) (gWeight_pos hA b).le)
            (norm0_nonneg hA u)
          · exact hu.sum_le_tsum (Finset.range N) (fun a _ => div_nonneg (norm_nonneg _) (gWeight_pos hA a).le)
          · exact hv.sum_le_tsum (Finset.range N) (fun b _ => div_nonneg (norm_nonneg _) (gWeight_pos hA b).le)
  have hsum : Summable0 s A (seqMul u v) :=
    summable_of_sum_range_le (fun m => div_nonneg (norm_nonneg _) (gWeight_pos hA m).le) hpart
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hpart⟩

/-- Finite product of sequences under Cauchy convolution `seqMul`. -/
private def seqListProd : List (ℕ → ℂ) → (ℕ → ℂ)
  | [] => fun m => if m = 0 then 1 else 0
  | u :: us => seqMul u (seqListProd us)

private lemma summable0_and_norm0_seqListProd {s A : ℝ} (hs : 0 ≤ s) (hA : 0 < A)
    (L : List (ℕ → ℂ)) (hL : ∀ u ∈ L, Summable0 s A u) :
    Summable0 s A (seqListProd L) ∧ norm0 s A (seqListProd L) ≤ (L.map (norm0 s A)).prod := by
  induction L with
  | nil =>
    have hsum : Summable0 s A (seqListProd []) :=
      summable0_of_finite_support 1 fun m hm => by simp [seqListProd]; omega
    refine ⟨hsum, ?_⟩
    unfold norm0 seqListProd
    rw [tsum_eq_single 0]
    · simp [gWeight]
    · intro m hm; simp [hm]
  | cons u us ih =>
    have hu : Summable0 s A u := hL u (List.mem_cons_self ..)
    have hus : ∀ v ∈ us, Summable0 s A v := fun v hv => hL v (List.mem_cons_of_mem _ hv)
    obtain ⟨hs_prod, hnorm_prod⟩ := ih hus
    obtain ⟨hs_mul, hnorm_mul⟩ := summable0_and_norm0_seqMul hs hA hu hs_prod
    refine ⟨hs_mul, ?_⟩
    calc norm0 s A (seqMul u (seqListProd us))
        ≤ norm0 s A u * norm0 s A (seqListProd us) := hnorm_mul
      _ ≤ norm0 s A u * (us.map (norm0 s A)).prod :=
          mul_le_mul_of_nonneg_left hnorm_prod (norm0_nonneg hA u)
      _ = ((u :: us).map (norm0 s A)).prod := rfl

/-- Telescoping Lipschitz bound for `seqListProd` of two lists of the same length. -/
private lemma norm0_seqListProd_sub_le {s A R : ℝ} (hs : 0 ≤ s) (hA : 0 < A) (hR : 1 ≤ R)
    (L₁ L₂ : List (ℕ → ℂ)) (hlen : L₁.length = L₂.length)
    (h1 : ∀ u ∈ L₁, Summable0 s A u ∧ norm0 s A u ≤ R)
    (h2 : ∀ v ∈ L₂, Summable0 s A v ∧ norm0 s A v ≤ R)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdiff : ∀ i (hi : i < L₁.length),
      norm0 s A (L₁[i] - L₂[i]'(hlen ▸ hi)) ≤ δ) :
    norm0 s A (seqListProd L₁ - seqListProd L₂) ≤ (L₁.length : ℝ) * R ^ (L₁.length - 1) * δ := by
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => simp [norm0_zero]
    | cons _ _ => simp at hlen
  | cons u₁ us₁ ih =>
    cases L₂ with
    | nil => simp at hlen
    | cons u₂ us₂ =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hu1 := h1 u₁ (List.mem_cons_self ..)
      have hu2 := h2 u₂ (List.mem_cons_self ..)
      have hus1 : ∀ u ∈ us₁, Summable0 s A u ∧ norm0 s A u ≤ R :=
        fun u hu => h1 u (List.mem_cons_of_mem _ hu)
      have hus2 : ∀ v ∈ us₂, Summable0 s A v ∧ norm0 s A v ≤ R :=
        fun v hv => h2 v (List.mem_cons_of_mem _ hv)
      obtain ⟨hp1_s, hp1_n⟩ := summable0_and_norm0_seqListProd hs hA us₁ (fun u hu => (hus1 u hu).1)
      obtain ⟨hp2_s, hp2_n⟩ := summable0_and_norm0_seqListProd hs hA us₂ (fun v hv => (hus2 v hv).1)
      have hp1_le : norm0 s A (seqListProd us₁) ≤ R ^ us₁.length := by
        refine hp1_n.trans ?_
        have hlist : ∀ (L : List (ℕ → ℂ)), (∀ x ∈ L, norm0 s A x ≤ R) →
            (L.map (norm0 s A)).prod ≤ R ^ L.length := by
          intro L hL
          induction L with
          | nil => simp
          | cons x xs ihL =>
            simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
            exact mul_le_mul (hL x (List.mem_cons_self ..))
              (ihL fun y hy => hL y (List.mem_cons_of_mem _ hy))
              (List.prod_nonneg fun r hr => by
                rcases List.mem_map.mp hr with ⟨y, _, rfl⟩; exact norm0_nonneg hA y)
              (by linarith)
        exact hlist us₁ (fun u hu => (hus1 u hu).2)
      have hp2_le : norm0 s A (seqListProd us₂) ≤ R ^ us₁.length := by
        rw [hlen]
        refine hp2_n.trans ?_
        have hlist : ∀ (L : List (ℕ → ℂ)), (∀ x ∈ L, norm0 s A x ≤ R) →
            (L.map (norm0 s A)).prod ≤ R ^ L.length := by
          intro L hL
          induction L with
          | nil => simp
          | cons x xs ihL =>
            simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
            exact mul_le_mul (hL x (List.mem_cons_self ..))
              (ihL fun y hy => hL y (List.mem_cons_of_mem _ hy))
              (List.prod_nonneg fun r hr => by
                rcases List.mem_map.mp hr with ⟨y, _, rfl⟩; exact norm0_nonneg hA y)
              (by linarith)
        exact hlist us₂ (fun v hv => (hus2 v hv).2)
      -- Split `u₁ ⋆ P₁ - u₂ ⋆ P₂ = (u₁ - u₂) ⋆ P₁ + u₂ ⋆ (P₁ - P₂)`.
      have hsplit : seqListProd (u₁ :: us₁) - seqListProd (u₂ :: us₂) =
          seqMul (u₁ - u₂) (seqListProd us₁) + seqMul u₂ (seqListProd us₁ - seqListProd us₂) := by
        ext m
        simp only [seqListProd, Pi.sub_apply, Pi.add_apply, seqMul, ← Finset.sum_add_distrib]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hsplit]
      obtain ⟨hA_s, hA_n⟩ := summable0_and_norm0_seqMul hs hA
        (summable0_sub hA hu1.1 hu2.1) hp1_s
      obtain ⟨hB_s, hB_n⟩ := summable0_and_norm0_seqMul hs hA
        hu2.1 (summable0_sub hA hp1_s hp2_s)
      have hdiff0 : norm0 s A (u₁ - u₂) ≤ δ := hdiff 0 (Nat.succ_pos _)
      have hdiff_tail : ∀ i (hi : i < us₁.length),
          norm0 s A (us₁[i] - us₂[i]'(hlen ▸ hi)) ≤ δ := fun i hi =>
        hdiff (i + 1) (Nat.succ_lt_succ hi)
      have hih := ih us₂ hlen hus1 hus2 hdiff_tail
      have hR0 : 0 ≤ R := by linarith
      calc norm0 s A (seqMul (u₁ - u₂) (seqListProd us₁) + seqMul u₂ (seqListProd us₁ - seqListProd us₂))
          ≤ norm0 s A (seqMul (u₁ - u₂) (seqListProd us₁)) +
              norm0 s A (seqMul u₂ (seqListProd us₁ - seqListProd us₂)) :=
            norm0_add_le hA hA_s hB_s
        _ ≤ norm0 s A (u₁ - u₂) * norm0 s A (seqListProd us₁) +
              norm0 s A u₂ * norm0 s A (seqListProd us₁ - seqListProd us₂) :=
            add_le_add hA_n hB_n
        _ ≤ δ * R ^ us₁.length + R * ((us₁.length : ℝ) * R ^ (us₁.length - 1) * δ) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hdiff0 hp1_le (norm0_nonneg hA _) hδ
            · exact mul_le_mul hu2.2 hih (norm0_nonneg hA _) hR0
        _ ≤ ((us₁.length + 1 : ℕ) : ℝ) * R ^ ((us₁.length + 1) - 1) * δ := by
            simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
            cases hlen_us : us₁.length with
            | zero => simp
            | succ l =>
              have hpow : R * R ^ l = R ^ (l + 1) := by rw [pow_succ']
              simp only [Nat.add_sub_cancel]
              have heq : δ * R ^ (l + 1) + R * (((l + 1 : ℕ) : ℝ) * R ^ l * δ) =
                  (((l + 1 : ℕ) : ℝ) + 1) * R ^ (l + 1) * δ := by
                calc δ * R ^ (l + 1) + R * (((l + 1 : ℕ) : ℝ) * R ^ l * δ)
                    = δ * R ^ (l + 1) + ((l + 1 : ℕ) : ℝ) * (R * R ^ l) * δ := by ring
                  _ = δ * R ^ (l + 1) + ((l + 1 : ℕ) : ℝ) * R ^ (l + 1) * δ := by rw [hpow]
                  _ = (((l + 1 : ℕ) : ℝ) + 1) * R ^ (l + 1) * δ := by ring
              exact heq.le

/-! ### 1.5 Simultaneous Weighted `ℓ¹` Fixed-Point Contraction -/

/-- If `Φ` is a `1/2`-contraction on the closed unit ball of tail sequences (`v m = 0` for `m < M`)
in BOTH `normN k n 0 A` and `normN k n ε A` with `normN k n 0 A (Φ 0) ≤ 1/2`, then ANY fixed point
`φ` in the closed unit ball of `normN k n ε A` actually lies in the closed unit ball of
`normN k n 0 A` (so `‖φ m‖ ≤ A^m` for all `m`). -/
private lemma simultaneous_contraction_fixed_point {k n M : ℕ} {A ε : ℝ}
    (hk : 1 ≤ k) (hA : 1 ≤ A) (hε : 0 < ε)
    (Φ : (ℕ → ℂ) → (ℕ → ℂ))
    (hΦ_supp : ∀ v m, m < M → Φ v m = 0)
    (_hΦ0_sum : SummableN k n 0 A (Φ 0))
    (hΦ0_le : normN k n 0 A (Φ 0) ≤ 1 / 2)
    (hΦ_lip0 : ∀ v w, (∀ m < M, v m = 0) → (∀ m < M, w m = 0) →
      SummableN k n 0 A v → SummableN k n 0 A w →
      normN k n 0 A v ≤ 1 → normN k n 0 A w ≤ 1 →
      SummableN k n 0 A (Φ v) ∧ normN k n 0 A (Φ v - Φ w) ≤ (1 / 2) * normN k n 0 A (v - w))
    (hΦ_lipE : ∀ v w, (∀ m < M, v m = 0) → (∀ m < M, w m = 0) →
      SummableN k n ε A v → SummableN k n ε A w →
      normN k n ε A v ≤ 1 → normN k n ε A w ≤ 1 →
      SummableN k n ε A (Φ v) ∧ normN k n ε A (Φ v - Φ w) ≤ (1 / 2) * normN k n ε A (v - w))
    {φ : ℕ → ℂ} (hφ_supp : ∀ m < M, φ m = 0)
    (hφ_sum : SummableN k n ε A φ) (hφ_le : normN k n ε A φ ≤ 1)
    (hφ_fix : Φ φ = φ) :
    SummableN k n 0 A φ ∧ normN k n 0 A φ ≤ 1 := by
  have hApos : 0 < A := by linarith
  have hmk_ge_one : ∀ m : ℕ, (1 : ℝ) ≤ (((m + k : ℕ) : ℝ) ^ n) := fun m =>
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ m + k by omega))
  -- Pointwise coordinate bound from `normN k n 0 A`.
  have hcoord_le : ∀ (v : ℕ → ℂ), SummableN k n 0 A v → ∀ m : ℕ,
      ‖v m‖ ≤ A ^ m * normN k n 0 A v := by
    intro v hv m
    have hterm : (((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ / A ^ m ≤ normN k n 0 A v := by
      have hle := hv.le_tsum m (fun j _ =>
        div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
          (gWeight_pos hApos j).le)
      simpa [normN, gWeight_zero_eq] using hle
    have hmul : (((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ ≤ A ^ m * normN k n 0 A v := by
      rwa [div_le_iff₀ (pow_pos hApos m), mul_comm (normN k n 0 A v)] at hterm
    calc ‖v m‖ = 1 * ‖v m‖ := (one_mul _).symm
      _ ≤ (((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ := mul_le_mul_of_nonneg_right (hmk_ge_one m) (norm_nonneg _)
      _ ≤ A ^ m * normN k n 0 A v := hmul
  -- Picard iterates `seq t = Φ^[t] 0`.
  let seq : ℕ → (ℕ → ℂ) := fun t => Φ^[t] 0
  have hseq_prop : ∀ t : ℕ,
      (∀ m < M, seq t m = 0) ∧ SummableN k n 0 A (seq t) ∧
      normN k n 0 A (seq t) ≤ 1 - (1 / 2 : ℝ) ^ t ∧
      normN k n 0 A (seq (t + 1) - seq t) ≤ (1 / 2 : ℝ) ^ (t + 1) := by
    intro t
    induction t with
    | zero =>
      refine ⟨fun m _ => rfl, summableN_zero k n 0 A, by simp [seq, normN_zero], ?_⟩
      simpa [seq, pow_one, sub_zero] using hΦ0_le
    | succ t ih =>
      obtain ⟨hsupp_t, hsum_t, hnorm_t, hdiff_t⟩ := ih
      have hnorm_t1 : normN k n 0 A (seq t) ≤ 1 := by
        linarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) t]
      have hsupp_s : ∀ m < M, seq (t + 1) m = 0 := fun m hm => by
        rw [show seq (t + 1) = Φ (seq t) from Function.iterate_succ_apply' Φ t 0]
        exact hΦ_supp (seq t) m hm
      have hsum_s : SummableN k n 0 A (seq (t + 1)) := by
        rw [show seq (t + 1) = Φ (seq t) from Function.iterate_succ_apply' Φ t 0]
        exact (hΦ_lip0 (seq t) 0 hsupp_t (fun _ _ => rfl) hsum_t (summableN_zero k n 0 A)
          hnorm_t1 (by simp [normN_zero])).1
      have hnorm_s : normN k n 0 A (seq (t + 1)) ≤ 1 - (1 / 2 : ℝ) ^ (t + 1) := by
        have htri : seq (t + 1) = (seq (t + 1) - seq t) + seq t := by ext m; simp
        rw [htri]
        have hle := normN_add_le hApos (summableN_sub hApos hsum_s hsum_t) hsum_t
        have hhalf : (1 / 2 : ℝ) ^ (t + 1) + (1 - (1 / 2 : ℝ) ^ t) = 1 - (1 / 2 : ℝ) ^ (t + 1) := by
          rw [pow_succ]; ring
        linarith
      have hnorm_s1 : normN k n 0 A (seq (t + 1)) ≤ 1 := by
        linarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (t + 1)]
      have hdiff_s : normN k n 0 A (seq (t + 2) - seq (t + 1)) ≤ (1 / 2 : ℝ) ^ (t + 2) := by
        have hs2 : seq (t + 2) = Φ (seq (t + 1)) := Function.iterate_succ_apply' Φ (t + 1) 0
        have hs1 : seq (t + 1) = Φ (seq t) := Function.iterate_succ_apply' Φ t 0
        have hlip := (hΦ_lip0 (seq (t + 1)) (seq t) hsupp_s hsupp_t hsum_s hsum_t hnorm_s1 hnorm_t1).2
        calc normN k n 0 A (seq (t + 2) - seq (t + 1))
            = normN k n 0 A (Φ (seq (t + 1)) - Φ (seq t)) := by rw [hs2, hs1]
          _ ≤ (1 / 2) * normN k n 0 A (seq (t + 1) - seq t) := hlip
          _ ≤ (1 / 2) * (1 / 2 : ℝ) ^ (t + 1) := by linarith
          _ = (1 / 2 : ℝ) ^ (t + 2) := by rw [pow_succ']; ring
      exact ⟨hsupp_s, hsum_s, hnorm_s, hdiff_s⟩
  -- Telescoping bound `normN k n 0 A (seq u - seq t) ≤ (1 / 2)^t` for `t ≤ u`.
  have hteles : ∀ t d : ℕ, normN k n 0 A (seq (t + d) - seq t) ≤ (1 / 2 : ℝ) ^ t := by
    intro t d
    have hsum_step : ∀ d : ℕ,
        normN k n 0 A (seq (t + d) - seq t) ≤
          ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (t + j + 1) := by
      intro d
      induction d with
      | zero => simp [normN_zero]
      | succ d ihd =>
        have hsplit : seq (t + (d + 1)) - seq t =
            (seq (t + d + 1) - seq (t + d)) + (seq (t + d) - seq t) := by
          ext m; simp [Nat.add_assoc]
        rw [hsplit, Finset.sum_range_succ]
        have h1 := summableN_sub hApos (hseq_prop (t + d + 1)).2.1 (hseq_prop (t + d)).2.1
        have h2 := summableN_sub hApos (hseq_prop (t + d)).2.1 (hseq_prop t).2.1
        have hle := normN_add_le hApos h1 h2
        have hd1 := (hseq_prop (t + d)).2.2.2
        linarith
    refine (hsum_step d).trans ?_
    have hgeom : ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (t + j + 1) =
        (1 / 2 : ℝ) ^ t * (1 - (1 / 2 : ℝ) ^ d) := by
      induction d with
      | zero => simp
      | succ d ihd =>
        rw [Finset.sum_range_succ, ihd]
        have : (1 / 2 : ℝ) ^ (t + d + 1) = (1 / 2 : ℝ) ^ t * ((1 / 2 : ℝ) ^ d * (1 / 2)) := by
          rw [pow_add, pow_add, pow_one, mul_assoc]
        rw [this, pow_succ]
        ring
    rw [hgeom]
    have h1 : 1 - (1 / 2 : ℝ) ^ d ≤ 1 := by linarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) d]
    calc (1 / 2 : ℝ) ^ t * (1 - (1 / 2 : ℝ) ^ d)
        ≤ (1 / 2 : ℝ) ^ t * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg (by norm_num) t)
      _ = (1 / 2 : ℝ) ^ t := mul_one _
  -- Coordinatewise Cauchy sequence -> pointwise limit `vStar`.
  have hcauchy : ∀ m : ℕ, CauchySeq (fun t => seq t m) := by
    intro m
    refine cauchySeq_of_le_geometric (1 / 2) (A ^ m / 2) (by norm_num) fun t => ?_
    rw [dist_eq_norm, norm_sub_rev]
    have hle := hcoord_le (seq (t + 1) - seq t)
      (summableN_sub hApos (hseq_prop (t + 1)).2.1 (hseq_prop t).2.1) m
    calc ‖seq (t + 1) m - seq t m‖
        ≤ A ^ m * normN k n 0 A (seq (t + 1) - seq t) := hle
      _ ≤ A ^ m * (1 / 2 : ℝ) ^ (t + 1) :=
          mul_le_mul_of_nonneg_left (hseq_prop t).2.2.2 (pow_nonneg hApos.le m)
      _ = A ^ m / 2 * (1 / 2 : ℝ) ^ t := by rw [pow_succ']; ring
  choose vStar hvStar using fun m => cauchySeq_tendsto_of_complete (hcauchy m)
  have hvStar_supp : ∀ m < M, vStar m = 0 := fun m hm =>
    tendsto_nhds_unique (hvStar m)
      (tendsto_const_nhds.congr fun t => ((hseq_prop t).1 m hm).symm)
  -- Helper: finite-range sum of convergent real sequences converges.
  have htend_range : ∀ (N : ℕ) (f_seq : ℕ → ℕ → ℝ) (f_lim : ℕ → ℝ),
      (∀ m < N, Tendsto (fun t => f_seq t m) atTop (𝓝 (f_lim m))) →
      Tendsto (fun t => ∑ m ∈ Finset.range N, f_seq t m) atTop
        (𝓝 (∑ m ∈ Finset.range N, f_lim m)) := by
    intro N f_seq f_lim hf
    induction N with
    | zero => simp
    | succ N ihN =>
      simp_rw [Finset.sum_range_succ]
      exact (ihN fun m hm => hf m (Nat.lt_succ_of_lt hm)).add (hf N (Nat.lt_succ_self N))
  -- `SummableN k n 0 A vStar` and `normN k n 0 A vStar ≤ 1`.
  have hvStar_part : ∀ N : ℕ,
      ∑ m ∈ Finset.range N, (((m + k : ℕ) : ℝ) ^ n) * ‖vStar m‖ / gWeight 0 A m ≤ 1 := by
    intro N
    have htend : Tendsto
        (fun t => ∑ m ∈ Finset.range N, (((m + k : ℕ) : ℝ) ^ n) * ‖seq t m‖ / gWeight 0 A m)
        atTop
        (𝓝 (∑ m ∈ Finset.range N, (((m + k : ℕ) : ℝ) ^ n) * ‖vStar m‖ / gWeight 0 A m)) :=
      htend_range N _ _ fun m _ =>
        (((hvStar m).norm.const_mul (((m + k : ℕ) : ℝ) ^ n)).div_const (gWeight 0 A m))
    refine le_of_tendsto htend (Eventually.of_forall fun t => ?_)
    have hle := (hseq_prop t).2.1.sum_le_tsum (Finset.range N) fun m _ =>
      div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
        (gWeight_pos hApos m).le
    have hnorm1 : normN k n 0 A (seq t) ≤ 1 := by
      linarith [(hseq_prop t).2.2.1, pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) t]
    exact hle.trans hnorm1
  have hvStar_sum : SummableN k n 0 A vStar :=
    summable_of_sum_range_le
      (fun m => div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
        (gWeight_pos hApos m).le)
      hvStar_part
  have hvStar_le : normN k n 0 A vStar ≤ 1 := hvStar_sum.tsum_le_of_sum_range_le hvStar_part
  -- Rate of convergence `normN k n 0 A (vStar - seq t) ≤ (1 / 2)^t`.
  have hvStar_rate : ∀ t : ℕ, normN k n 0 A (vStar - seq t) ≤ (1 / 2 : ℝ) ^ t := by
    intro t
    have hsum_diff : SummableN k n 0 A (vStar - seq t) :=
      summableN_sub hApos hvStar_sum (hseq_prop t).2.1
    refine hsum_diff.tsum_le_of_sum_range_le fun N => ?_
    have htend : Tendsto
        (fun d => ∑ m ∈ Finset.range N,
          (((m + k : ℕ) : ℝ) ^ n) * ‖seq (t + d) m - seq t m‖ / gWeight 0 A m)
        atTop
        (𝓝 (∑ m ∈ Finset.range N,
          (((m + k : ℕ) : ℝ) ^ n) * ‖vStar m - seq t m‖ / gWeight 0 A m)) :=
      htend_range N _ _ fun m _ => by
        have hshift : Tendsto (fun d => seq (t + d) m) atTop (𝓝 (vStar m)) :=
          (hvStar m).comp ((tendsto_add_atTop_nat t).congr fun d => add_comm d t)
        exact (((hshift.sub_const (seq t m)).norm.const_mul (((m + k : ℕ) : ℝ) ^ n)).div_const
          (gWeight 0 A m))
    refine le_of_tendsto htend (Eventually.of_forall fun d => ?_)
    have hle := (summableN_sub hApos (hseq_prop (t + d)).2.1 (hseq_prop t).2.1).sum_le_tsum
      (Finset.range N) fun m _ =>
        div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
          (gWeight_pos hApos m).le
    exact hle.trans (hteles t d)
  -- Show `Φ vStar = vStar`.
  have hvStar_fix : Φ vStar = vStar := by
    ext m
    have h1 : Tendsto (fun t => seq (t + 1) m) atTop (𝓝 (vStar m)) :=
      (hvStar m).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun t => seq (t + 1) m) atTop (𝓝 (Φ vStar m)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      have htend0 : Tendsto (fun t : ℕ => A ^ m * ((1 / 2 : ℝ) ^ (t + 1))) atTop (𝓝 0) := by
        simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).comp (tendsto_add_atTop_nat 1)).const_mul (A ^ m)
      obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp htend0) δ hδ
      refine ⟨T, fun t ht => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      have hseq_t1 : seq (t + 1) = Φ (seq t) := Function.iterate_succ_apply' Φ t 0
      rw [hseq_t1]
      have hnorm_t1 : normN k n 0 A (seq t) ≤ 1 := by
        linarith [(hseq_prop t).2.2.1, pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) t]
      have hlip := hΦ_lip0 vStar (seq t) hvStar_supp (hseq_prop t).1 hvStar_sum (hseq_prop t).2.1
        hvStar_le hnorm_t1
      have hΦs := (hΦ_lip0 (seq t) vStar (hseq_prop t).1 hvStar_supp (hseq_prop t).2.1 hvStar_sum
        hnorm_t1 hvStar_le).1
      have hdist_le : ‖Φ vStar m - Φ (seq t) m‖ ≤ A ^ m * (1 / 2 : ℝ) ^ (t + 1) := by
        calc ‖(Φ vStar - Φ (seq t)) m‖
            ≤ A ^ m * normN k n 0 A (Φ vStar - Φ (seq t)) :=
              hcoord_le (Φ vStar - Φ (seq t)) (summableN_sub hApos hlip.1 hΦs) m
          _ ≤ A ^ m * ((1 / 2) * normN k n 0 A (vStar - seq t)) :=
              mul_le_mul_of_nonneg_left hlip.2 (pow_nonneg hApos.le m)
          _ ≤ A ^ m * ((1 / 2) * (1 / 2 : ℝ) ^ t) :=
              mul_le_mul_of_nonneg_left (by linarith [hvStar_rate t]) (pow_nonneg hApos.le m)
          _ = A ^ m * (1 / 2 : ℝ) ^ (t + 1) := by rw [pow_succ']
      have hTval := hT t ht
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg hApos.le m)
        (pow_nonneg (by norm_num) _))] at hTval
      exact hdist_le.trans_lt hTval
    exact tendsto_nhds_unique h2 h1
  -- Compare `φ` and `vStar` in `normN k n ε A`: contraction forces `φ = vStar`!
  have hvStar_sumE : SummableN k n ε A vStar := summableN_of_le hε.le hApos hvStar_sum
  have hvStar_leE : normN k n ε A vStar ≤ 1 := (normN_le_of_le hε.le hApos hvStar_sum).trans hvStar_le
  have hlipE := (hΦ_lipE φ vStar hφ_supp hvStar_supp hφ_sum hvStar_sumE hφ_le hvStar_leE).2
  rw [hφ_fix, hvStar_fix] at hlipE
  have hzero : normN k n ε A (φ - vStar) = 0 :=
    le_antisymm (by linarith) (normN_nonneg hApos _)
  have hφ_eq : φ = vStar := by
    ext m
    have hsum_diff := summableN_sub hApos hφ_sum hvStar_sumE
    have hterm_le : (((m + k : ℕ) : ℝ) ^ n) * ‖φ m - vStar m‖ / gWeight ε A m ≤ 0 := by
      rw [← hzero]
      exact hsum_diff.le_tsum m fun j _ =>
        div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
          (gWeight_pos hApos j).le
    have hterm_nonneg : 0 ≤ (((m + k : ℕ) : ℝ) ^ n) * ‖φ m - vStar m‖ / gWeight ε A m :=
      div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
        (gWeight_pos hApos m).le
    have hterm0 : (((m + k : ℕ) : ℝ) ^ n) * ‖φ m - vStar m‖ / gWeight ε A m = 0 :=
      le_antisymm hterm_le hterm_nonneg
    have hmul0 : (((m + k : ℕ) : ℝ) ^ n) * ‖φ m - vStar m‖ = 0 :=
      (div_eq_zero_iff.mp hterm0).resolve_right (gWeight_pos hApos m).ne'
    have hnorm0 : ‖φ m - vStar m‖ = 0 :=
      (mul_eq_zero.mp hmul0).resolve_left (by linarith [hmk_ge_one m])
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  rw [hφ_eq]
  exact ⟨hvStar_sum, hvStar_le⟩

/-! ### 1.6 Polynomial Translation Identity (`pderiv` = Linear Term of Shifted `MvPolynomial`) -/

private lemma coeff_zero_aeval_add {n : ℕ} (p : Fin (n + 1) → Polynomial ℂ)
    (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    (MvPolynomial.aeval (fun i => MvPolynomial.C (p i) + MvPolynomial.X i) P).coeff 0 =
      MvPolynomial.eval₂ (RingHom.id _) p P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.eval₂_add, hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    rw [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_comm _ (MvPolynomial.C (p j)),
      MvPolynomial.coeff_C_mul, hP, mul_comm (p j)]
    have hX0 : (MvPolynomial.aeval (fun i => MvPolynomial.C (p i) + MvPolynomial.X i) P *
        MvPolynomial.X j).coeff 0 = 0 := by
      rw [MvPolynomial.coeff_mul_X']
      simp
    rw [hX0, add_zero]

private lemma coeff_single_aeval_add {n : ℕ} (p : Fin (n + 1) → Polynomial ℂ)
    (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) (i : Fin (n + 1)) :
    (MvPolynomial.aeval (fun j => MvPolynomial.C (p j) + MvPolynomial.X j) P).coeff
        (Finsupp.single i 1) =
      MvPolynomial.eval₂ (RingHom.id _) p (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hne : (0 : Fin (n + 1) →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h; have := congr_arg (fun f => f i) h; simp at this
    simp [MvPolynomial.coeff_C, hne]
  | add P Q hP hQ =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, MvPolynomial.eval₂_add, hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul,
      MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_X]
    rw [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_comm _ (MvPolynomial.C (p j)),
      MvPolynomial.coeff_C_mul, hP, MvPolynomial.coeff_mul_X']
    by_cases hij : j = i
    · subst hij
      have hmem : j ∈ (Finsupp.single j 1 : Fin (n + 1) →₀ ℕ).support := by simp
      simp only [hmem, ite_true, tsub_self, coeff_zero_aeval_add, Pi.single_eq_same,
        MvPolynomial.eval₂_one, mul_one]
      ring
    · have hnot : j ∉ (Finsupp.single i 1 : Fin (n + 1) →₀ ℕ).support := by
        rw [Finsupp.mem_support_iff, not_not]
        exact Finsupp.single_eq_of_ne hij
      simp only [hnot, ite_false, add_zero]
      rw [Pi.single_eq_of_ne hij, MvPolynomial.eval₂_zero, mul_zero, zero_add]

/-! ### 1.7 Sibuya's Sub-Gevrey Convergence Theorem (Unconditional, Fuchsian & Irregular Unified) -/

/-- Helper: sequence-level shift `X^r * v`. -/
private def shiftSeq (r : ℕ) (v : ℕ → ℂ) : ℕ → ℂ :=
  fun m => if r ≤ m then v (m - r) else 0

private lemma summable0_and_norm0_shiftSeq {s A : ℝ} (hs : 0 ≤ s) (hA : 1 ≤ A) (r : ℕ)
    {v : ℕ → ℂ} (hv : Summable0 s A v) :
    Summable0 s A (shiftSeq r v) ∧ norm0 s A (shiftSeq r v) ≤ A⁻¹ ^ r * norm0 s A v := by
  have hApos : 0 < A := by linarith
  have hbound : ∀ m : ℕ, ‖shiftSeq r v m‖ / gWeight s A m ≤
      A⁻¹ ^ r * (if r ≤ m then ‖v (m - r)‖ / gWeight s A (m - r) else 0) := by
    intro m
    by_cases hrm : r ≤ m
    · simp only [shiftSeq, hrm, ite_true]
      rw [inv_pow, ← div_eq_inv_mul, div_div]
      refine div_le_div_of_nonneg_left (norm_nonneg _)
        (mul_pos (gWeight_pos hApos (m - r)) (pow_pos hApos r)) ?_
      unfold gWeight
      have hm_eq : m - r + r = m := Nat.sub_add_cancel hrm
      calc A ^ (m - r) * ((m - r).factorial : ℝ) ^ s * A ^ r
          = A ^ m * ((m - r).factorial : ℝ) ^ s := by rw [mul_right_comm, ← pow_add, hm_eq]
        _ ≤ A ^ m * (m.factorial : ℝ) ^ s := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hApos.le m)
            exact Real.rpow_le_rpow (Nat.cast_nonneg _)
              (Nat.cast_le.mpr (Nat.factorial_le (Nat.sub_le m r))) hs
    · simp [shiftSeq, hrm]
  have hinj : Function.Injective (fun j : ℕ => j + r) := add_left_injective r
  have hsupp : ∀ m ∉ Set.range (fun j : ℕ => j + r),
      (if r ≤ m then ‖v (m - r)‖ / gWeight s A (m - r) else 0) = 0 := by
    intro m hm
    by_cases hrm : r ≤ m
    · exact absurd ⟨m - r, Nat.sub_add_cancel hrm⟩ hm
    · simp [hrm]
  have hsum_ind : Summable (fun m => if r ≤ m then ‖v (m - r)‖ / gWeight s A (m - r) else 0) := by
    rw [← Function.Injective.summable_iff hinj hsupp]
    unfold Summable0 at hv
    simpa [Function.comp_def] using hv
  have hsum_rhs : Summable (fun m => A⁻¹ ^ r * (if r ≤ m then ‖v (m - r)‖ / gWeight s A (m - r) else 0)) :=
    hsum_ind.mul_left _
  have hsum : Summable0 s A (shiftSeq r v) :=
    Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le)
      hbound hsum_rhs
  refine ⟨hsum, ?_⟩
  have hsupp' : Function.support (fun m => if r ≤ m then ‖v (m - r)‖ / gWeight s A (m - r) else 0) ⊆
      Set.range (fun j : ℕ => j + r) := fun m hm => by
    by_contra hnot
    exact (Function.mem_support.mp hm) (hsupp m hnot)
  have htsum_eq : (∑' m : ℕ, if r ≤ m then ‖v (m - r)‖ / gWeight s A (m - r) else 0) = norm0 s A v := by
    rw [← Function.Injective.tsum_eq hinj hsupp']
    simp [norm0]
  calc norm0 s A (shiftSeq r v)
      ≤ ∑' m, A⁻¹ ^ r * (if r ≤ m then ‖v (m - r)‖ / gWeight s A (m - r) else 0) :=
        Summable.tsum_le_tsum hbound hsum hsum_rhs
    _ = A⁻¹ ^ r * norm0 s A v := by rw [tsum_mul_left, htsum_eq]

/-- Helper: sequence-level Euler shift `(δ + k)^i v`. -/
private def eulerShiftSeq (k i : ℕ) (v : ℕ → ℂ) : ℕ → ℂ :=
  fun m => (((m + k : ℕ) : ℂ) ^ i) * v m

private lemma summable0_and_norm0_eulerShiftSeq {k n i : ℕ} {s A : ℝ}
    (hk : 1 ≤ k) (hin : i ≤ n) (hA : 0 < A) {v : ℕ → ℂ} (hv : SummableN k n s A v) :
    Summable0 s A (eulerShiftSeq k i v) ∧
      norm0 s A (eulerShiftSeq k i v) ≤ normN k n s A v := by
  have hle : ∀ m : ℕ, ‖eulerShiftSeq k i v m‖ / gWeight s A m ≤
      (((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ / gWeight s A m := by
    intro m
    simp only [eulerShiftSeq, norm_mul, norm_pow, Complex.norm_natCast]
    refine div_le_div_of_nonneg_right ?_ (gWeight_pos hA m).le
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m + k by omega)) hin
  have hsum : Summable0 s A (eulerShiftSeq k i v) :=
    Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (gWeight_pos hA m).le) hle hv
  exact ⟨hsum, Summable.tsum_le_tsum hle hsum hv⟩

private lemma norm0_eulerShiftSeq_lt_le {k n i M : ℕ} {s A : ℝ}
    (hk : 1 ≤ k) (hin : i < n) (hM : 1 ≤ M) (hA : 0 < A) {v : ℕ → ℂ}
    (hv_supp : ∀ m < M, v m = 0) (hv : SummableN k n s A v) :
    norm0 s A (eulerShiftSeq k i v) ≤ (M : ℝ)⁻¹ * normN k n s A v := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  have hle : ∀ m : ℕ, ‖eulerShiftSeq k i v m‖ / gWeight s A m ≤
      (M : ℝ)⁻¹ * ((((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ / gWeight s A m) := by
    intro m
    by_cases hm : m < M
    · simp [eulerShiftSeq, hv_supp m hm]
    · push Not at hm
      simp only [eulerShiftSeq, norm_mul, norm_pow, Complex.norm_natCast]
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (gWeight_pos hA m).le
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hmk_ge : (M : ℝ) ≤ ((m + k : ℕ) : ℝ) := by exact_mod_cast (show M ≤ m + k by omega)
      have hmk_pos : (0 : ℝ) < ((m + k : ℕ) : ℝ) := lt_of_lt_of_le hMpos hmk_ge
      rw [inv_mul_eq_div, le_div_iff₀ hMpos]
      calc (((m + k : ℕ) : ℝ) ^ i) * (M : ℝ)
          ≤ (((m + k : ℕ) : ℝ) ^ i) * ((m + k : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hmk_ge (pow_nonneg hmk_pos.le i)
        _ = ((m + k : ℕ) : ℝ) ^ (i + 1) := (pow_succ _ _).symm
        _ ≤ ((m + k : ℕ) : ℝ) ^ n :=
            pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m + k by omega)) hin
  have hsum := (summable0_and_norm0_eulerShiftSeq hk hin.le hA hv).1
  calc norm0 s A (eulerShiftSeq k i v)
      ≤ ∑' m, (M : ℝ)⁻¹ * ((((m + k : ℕ) : ℝ) ^ n) * ‖v m‖ / gWeight s A m) :=
        Summable.tsum_le_tsum hle hsum (hv.mul_left _)
    _ = (M : ℝ)⁻¹ * normN k n s A v := tsum_mul_left

/-- Helper: sequence of coefficients of a polynomial `q ∈ ℂ[X]`. -/
private def polySeq (q : Polynomial ℂ) : ℕ → ℂ := fun m => q.coeff m

private def polyL1 (q : Polynomial ℂ) : ℝ :=
  ∑ j ∈ Finset.range (q.natDegree + 1), ‖q.coeff j‖

private lemma polyL1_nonneg (q : Polynomial ℂ) : 0 ≤ polyL1 q :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma summable0_and_norm0_polySeq {s A : ℝ} (hs : 0 ≤ s) (hA : 1 ≤ A) (q : Polynomial ℂ) :
    Summable0 s A (polySeq q) ∧ norm0 s A (polySeq q) ≤ polyL1 q := by
  have hApos : 0 < A := by linarith
  have hsum : Summable0 s A (polySeq q) :=
    summable0_of_finite_support (q.natDegree + 1) fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨hsum, ?_⟩
  unfold norm0 polyL1
  rw [tsum_eq_sum (s := Finset.range (q.natDegree + 1))]
  · refine Finset.sum_le_sum fun j _ => ?_
    have hgw : 1 ≤ gWeight s A j := by
      calc (1 : ℝ) = 1 ^ j * 1 := by simp
        _ ≤ A ^ j * ((j.factorial : ℝ) ^ s) :=
            mul_le_mul (pow_le_pow_left₀ zero_le_one hA j)
              (Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.factorial_pos j)) hs)
              zero_le_one (pow_nonneg hApos.le j)
    exact div_le_self (norm_nonneg _) hgw
  · intro m hm
    rw [Finset.mem_range, not_lt] at hm
    have h0 : q.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [polySeq, h0]

private lemma norm0_polySeq_X_mul {s A : ℝ} (hs : 0 ≤ s) (hA : 1 ≤ A) (q : Polynomial ℂ) :
    norm0 s A (polySeq (Polynomial.X * q)) ≤ A⁻¹ * polyL1 q := by
  have heq : polySeq (Polynomial.X * q) = shiftSeq 1 (polySeq q) := by
    ext m
    cases m with
    | zero => simp [polySeq, shiftSeq]
    | succ m => simp [polySeq, shiftSeq, Polynomial.coeff_X_mul]
  rw [heq]
  obtain ⟨hq_s, hq_n⟩ := summable0_and_norm0_polySeq hs hA q
  obtain ⟨_, hsh_n⟩ := summable0_and_norm0_shiftSeq hs hA 1 hq_s
  rw [pow_one] at hsh_n
  exact hsh_n.trans (mul_le_mul_of_nonneg_left hq_n (inv_nonneg.mpr (by linarith)))

/-- Helper: irregular forward-shift operator `m ↦ if M ≤ m then (m + p + k)^i * v (m + p) else 0`. -/
private def irregSeq (k i p M : ℕ) (v : ℕ → ℂ) : ℕ → ℂ :=
  fun m => if M ≤ m then (((m + p + k : ℕ) : ℂ) ^ i) * v (m + p) else 0

private lemma summable0_and_norm0_irregSeq {k n i p l_n B : ℕ} {s : ℝ}
    (hk : 1 ≤ k) (hin : i < n) (hp1 : 1 ≤ p) (hpl : p ≤ l_n) (hB : 2 ≤ B)
    (hs0 : 0 ≤ s) (hs_le : s ≤ 1 / ((4 * l_n + 2 : ℕ) : ℝ))
    {v : ℕ → ℂ} (hv : SummableN k n s ((B : ℝ) ^ 2) v) :
    let M : ℕ := B ^ (4 * l_n + 2)
    Summable0 s ((B : ℝ) ^ 2) (irregSeq k i p M v) ∧
      norm0 s ((B : ℝ) ^ 2) (irregSeq k i p M v) ≤ (B : ℝ)⁻¹ * normN k n s ((B : ℝ) ^ 2) v := by
  intro M
  set A : ℝ := (B : ℝ) ^ 2 with hA_def
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hApos : 0 < A := pow_pos hBpos 2
  -- Key per-term bound for `m ≥ M` with `j = m + p`:
  -- `(j + k)^i / gWeight s A m ≤ B⁻¹ * (j + k)^n / gWeight s A j`.
  have hterm : ∀ m : ℕ, M ≤ m →
      (((m + p + k : ℕ) : ℝ) ^ i) * ‖v (m + p)‖ / gWeight s A m ≤
        (B : ℝ)⁻¹ * ((((m + p + k : ℕ) : ℝ) ^ n) * ‖v (m + p)‖ / gWeight s A (m + p)) := by
    intro m hm
    set j : ℕ := m + p
    have hj_ge_M : M ≤ j := by omega
    have hjk_pos : (0 : ℝ) < ((j + k : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hjk_ge1 : (1 : ℝ) ≤ ((j + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j + k by omega)
    -- Step 1: `gWeight s A j / gWeight s A m ≤ A^p * (j + k)^(1/2)`.
    have hfact_ratio : (j.factorial : ℝ) / (m.factorial : ℝ) ≤ ((j + k : ℕ) : ℝ) ^ p := by
      have hfac_le : j.factorial ≤ m.factorial * (j + k) ^ p := by
        have haux : ∀ q : ℕ, (m + q).factorial ≤ m.factorial * (m + q + k) ^ q := by
          intro q
          induction q with
          | zero => simp
          | succ q ihq =>
            rw [Nat.add_succ, Nat.factorial_succ, pow_succ]
            calc (m + q + 1) * (m + q).factorial
                ≤ (m + q + 1) * (m.factorial * (m + q + k) ^ q) :=
                  Nat.mul_le_mul_left _ ihq
              _ = m.factorial * ((m + q + k) ^ q * (m + q + 1)) := by ring
              _ ≤ m.factorial * ((m + q + 1 + k) ^ q * (m + q + 1 + k)) := by
                  refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ ?_)
                  · exact Nat.pow_le_pow_left (by omega) q
                  · omega
        simpa [j] using haux p
      rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos m))]
      calc (j.factorial : ℝ)
          ≤ ((m.factorial * (j + k) ^ p : ℕ) : ℝ) := Nat.cast_le.mpr hfac_le
        _ = ((j + k : ℕ) : ℝ) ^ p * (m.factorial : ℝ) := by push_cast; ring
    have hrpow_le : ((j.factorial : ℝ) / (m.factorial : ℝ)) ^ s ≤ Real.sqrt ((j + k : ℕ) : ℝ) := by
      have hps : (p : ℝ) * s ≤ 1 / 2 := by
        have h4 : (0 : ℝ) < ((4 * l_n + 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        calc (p : ℝ) * s
            ≤ (l_n : ℝ) * (1 / ((4 * l_n + 2 : ℕ) : ℝ)) :=
              mul_le_mul (Nat.cast_le.mpr hpl) hs_le hs0 (Nat.cast_nonneg l_n)
          _ ≤ 1 / 2 := by
              rw [mul_one_div, div_le_div_iff₀ h4 (by norm_num : (0 : ℝ) < 2)]
              push_cast; linarith
      calc ((j.factorial : ℝ) / (m.factorial : ℝ)) ^ s
          ≤ (((j + k : ℕ) : ℝ) ^ p) ^ s :=
            Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hfact_ratio hs0
        _ = ((j + k : ℕ) : ℝ) ^ ((p : ℝ) * s) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hjk_pos.le]
        _ ≤ ((j + k : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hjk_ge1 hps
        _ = Real.sqrt ((j + k : ℕ) : ℝ) := (Real.sqrt_eq_rpow _).symm
    -- Step 2: `A^p * Real.sqrt (j + k) ≤ B⁻¹ * (j + k)`.
    have hsqrt_ge : (B : ℝ) ^ (2 * l_n + 1) ≤ Real.sqrt ((j + k : ℕ) : ℝ) := by
      have hsq : ((B : ℝ) ^ (2 * l_n + 1)) ^ 2 ≤ ((j + k : ℕ) : ℝ) := by
        calc ((B : ℝ) ^ (2 * l_n + 1)) ^ 2
            = (B : ℝ) ^ (4 * l_n + 2) := by rw [← pow_mul]; congr 1; omega
          _ = (M : ℝ) := by simp [M]
          _ ≤ ((j + k : ℕ) : ℝ) := by exact_mod_cast (show M ≤ j + k by omega)
      rw [← Real.sqrt_sq (pow_nonneg hBpos.le _)]
      exact Real.sqrt_le_sqrt hsq
    have hAp_le : A ^ p ≤ (B : ℝ) ^ (2 * l_n) := by
      rw [hA_def, ← pow_mul]
      exact pow_le_pow_right₀ hB1 (by omega)
    have hkey : A ^ p * (((j.factorial : ℝ) / (m.factorial : ℝ)) ^ s) ≤
        (B : ℝ)⁻¹ * ((j + k : ℕ) : ℝ) := by
      have hsq_jk : Real.sqrt ((j + k : ℕ) : ℝ) * Real.sqrt ((j + k : ℕ) : ℝ) = ((j + k : ℕ) : ℝ) :=
        Real.mul_self_sqrt hjk_pos.le
      calc A ^ p * (((j.factorial : ℝ) / (m.factorial : ℝ)) ^ s)
          ≤ (B : ℝ) ^ (2 * l_n) * Real.sqrt ((j + k : ℕ) : ℝ) :=
            mul_le_mul hAp_le hrpow_le
              (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) s)
              (pow_nonneg hBpos.le _)
        _ = (B : ℝ)⁻¹ * ((B : ℝ) ^ (2 * l_n + 1) * Real.sqrt ((j + k : ℕ) : ℝ)) := by
            rw [pow_succ', ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hBpos.ne', one_mul]
        _ ≤ (B : ℝ)⁻¹ * (Real.sqrt ((j + k : ℕ) : ℝ) * Real.sqrt ((j + k : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsqrt_ge (Real.sqrt_nonneg _)) (inv_nonneg.mpr hBpos.le)
        _ = (B : ℝ)⁻¹ * ((j + k : ℕ) : ℝ) := by rw [hsq_jk]
    -- Step 3: relate `gWeight s A j / gWeight s A m` and `(j + k)^i` vs `(j + k)^n`.
    have hgw_ratio : gWeight s A j =
        gWeight s A m * (A ^ p * (((j.factorial : ℝ) / (m.factorial : ℝ)) ^ s)) := by
      unfold gWeight
      have hm_fac : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      rw [show j = m + p from rfl, pow_add, Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      have hmr : (m.factorial : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) s).ne'
      field_simp [hmr]
    have hpow_in : (((j + k : ℕ) : ℝ) ^ i) * ((j + k : ℕ) : ℝ) ≤ (((j + k : ℕ) : ℝ) ^ n) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hjk_ge1 hin
    rw [← mul_div_assoc, div_le_div_iff₀ (gWeight_pos hApos m) (gWeight_pos hApos j), hgw_ratio]
    calc (((j + k : ℕ) : ℝ) ^ i) * ‖v j‖ *
          (gWeight s A m * (A ^ p * (((j.factorial : ℝ) / (m.factorial : ℝ)) ^ s)))
        = gWeight s A m * ‖v j‖ * ((((j + k : ℕ) : ℝ) ^ i) *
            (A ^ p * (((j.factorial : ℝ) / (m.factorial : ℝ)) ^ s))) := by ring
      _ ≤ gWeight s A m * ‖v j‖ * ((((j + k : ℕ) : ℝ) ^ i) * ((B : ℝ)⁻¹ * ((j + k : ℕ) : ℝ))) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hkey (pow_nonneg hjk_pos.le i))
            (mul_nonneg (gWeight_pos hApos m).le (norm_nonneg _))
      _ = gWeight s A m * ‖v j‖ * (B : ℝ)⁻¹ * ((((j + k : ℕ) : ℝ) ^ i) * ((j + k : ℕ) : ℝ)) := by ring
      _ ≤ gWeight s A m * ‖v j‖ * (B : ℝ)⁻¹ * (((j + k : ℕ) : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hpow_in
            (mul_nonneg (mul_nonneg (gWeight_pos hApos m).le (norm_nonneg _)) (inv_nonneg.mpr hBpos.le))
      _ = (B : ℝ)⁻¹ * ((((j + k : ℕ) : ℝ) ^ n) * ‖v j‖) * gWeight s A m := by ring
  -- Combine into summability & tsum bound by reindexing `m ↦ m + p`.
  have hle_all : ∀ m : ℕ, ‖irregSeq k i p M v m‖ / gWeight s A m ≤
      (B : ℝ)⁻¹ * ((((m + p + k : ℕ) : ℝ) ^ n) * ‖v (m + p)‖ / gWeight s A (m + p)) := by
    intro m
    by_cases hm : M ≤ m
    · simp only [irregSeq, hm, ite_true, norm_mul, norm_pow, Complex.norm_natCast]
      exact hterm m hm
    · simp only [irregSeq, hm, ite_false, norm_zero, zero_div]
      exact mul_nonneg (inv_nonneg.mpr hBpos.le)
        (div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
          (gWeight_pos hApos _).le)
  have hsum_shift : Summable (fun m : ℕ =>
      (((m + p + k : ℕ) : ℝ) ^ n) * ‖v (m + p)‖ / gWeight s A (m + p)) :=
    hv.comp_injective (add_left_injective p)
  have hsum : Summable0 s A (irregSeq k i p M v) :=
    Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le)
      hle_all (hsum_shift.mul_left _)
  refine ⟨hsum, ?_⟩
  have htsum_le : (∑' m : ℕ, (((m + p + k : ℕ) : ℝ) ^ n) * ‖v (m + p)‖ / gWeight s A (m + p)) ≤
      normN k n s A v := by
    unfold normN
    exact tsum_comp_le_tsum_of_inj hv
      (fun j => div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
        (gWeight_pos hApos j).le)
      (add_left_injective p)
  calc norm0 s A (irregSeq k i p M v)
      ≤ ∑' m, (B : ℝ)⁻¹ * ((((m + p + k : ℕ) : ℝ) ^ n) * ‖v (m + p)‖ / gWeight s A (m + p)) :=
        Summable.tsum_le_tsum hle_all hsum (hsum_shift.mul_left _)
    _ = (B : ℝ)⁻¹ * ∑' m, (((m + p + k : ℕ) : ℝ) ^ n) * ‖v (m + p)‖ / gWeight s A (m + p) :=
        tsum_mul_left
    _ ≤ (B : ℝ)⁻¹ * normN k n s A v := mul_le_mul_of_nonneg_left htsum_le (inv_nonneg.mpr hBpos.le)

/-- **Sibuya's Sub-Gevrey Convergence Theorem (Euler form, 100% unconditional):**
If `f : PowerSeries ℂ` is sub-Gevrey (`∀ s > 0, IsGevrey s f`) and satisfies a nonzero
polynomial algebraic differential equation `P(X, f, δf, ..., δ^r f) = 0` over `ℂ[X]`,
then `f` is convergent (`IsConvergentPS f`). -/
theorem sibuya_subGevrey_convergent_euler {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : P ≠ 0)
    {f : PowerSeries ℂ} (hsub : IsSubGevrey f) (hf : evalEulerPS P f = 0) :
    IsConvergentPS f := by
  classical
  -- Step 1: Minimality reduction gives `F` of order `n` with `a_n = (∂F/∂Y_n)(X, Φ) ≠ 0`.
  obtain ⟨n, F, _, hFeval, hTopNe⟩ := exists_minimal_euler_ade hP hf
  let a_top : PowerSeries ℂ := evalEulerPS (MvPolynomial.pderiv (Fin.last n) F) f
  have ha_top_ne : a_top ≠ 0 := hTopNe
  -- Step 2: Fix `l_n = ord_0(a_top)`, `c_n = coeff l_n a_top ≠ 0`, and `k = l_n + 2`.
  have hord_lt : a_top.order < ⊤ := PowerSeries.order_finite_iff_ne_zero.mpr ha_top_ne
  let l_n : ℕ := a_top.order.toNat
  have hord_eq : a_top.order = l_n := (ENat.natCast_toNat hord_lt.ne).symm
  have hc_n_ne : PowerSeries.coeff l_n a_top ≠ 0 := PowerSeries.coeff_order ha_top_ne
  have ha_top_lt : ∀ j < l_n, PowerSeries.coeff j a_top = 0 := fun j hj =>
    PowerSeries.coeff_of_lt_order j (by rw [hord_eq]; exact_mod_cast hj)
  let c_n : ℂ := PowerSeries.coeff l_n a_top
  let k : ℕ := l_n + 2
  have hk1 : 1 ≤ k := by omega
  -- Step 3: Split `f = u_k + X^k * ψ` with `u_k` a fixed polynomial of degree ≤ `k` and `ψ(0) = 0`.
  let u_k : Polynomial ℂ := ∑ j ∈ Finset.range (k + 1), Polynomial.monomial j (PowerSeries.coeff j f)
  let ψ : PowerSeries ℂ := PowerSeries.mk fun m => if m = 0 then 0 else PowerSeries.coeff (k + m) f
  have hf_split : f = (u_k : PowerSeries ℂ) + PowerSeries.X ^ k * ψ := by
    ext m
    rw [map_add, Polynomial.coeff_coe, PowerSeries.coeff_X_pow_mul']
    have huk : u_k.coeff m = if m ≤ k then PowerSeries.coeff m f else 0 := by
      dsimp only [u_k]
      rw [← Polynomial.lcoeff_apply, map_sum]
      simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
      by_cases hmk : m ≤ k
      · rw [Finset.sum_eq_single m]
        · simp [hmk]
        · intro j _ hne; simp [hne]
        · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
      · rw [Finset.sum_eq_zero]
        · simp [hmk]
        · intro j hj; rw [Finset.mem_range] at hj; simp [show j ≠ m by omega]
    rw [huk]
    by_cases hmk : m ≤ k
    · by_cases hkm : k ≤ m
      · have hmeq : m = k := by omega
        subst hmeq
        simp [ψ]
      · simp [hmk, hkm]
    · have hkm : k ≤ m := by omega
      have hsub_ne : m - k ≠ 0 := by omega
      simp [hmk, hkm, ψ, hsub_ne, Nat.add_sub_of_le hkm]
  -- Step 4: Translate `F` by `Φ_k = (u_k, δ u_k, ..., δ^n u_k)`.
  let Φ_k_poly : Fin (n + 1) → Polynomial ℂ := fun i => polyEuler^[i.1] u_k
  let F_shift : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
    MvPolynomial.aeval (fun i => MvPolynomial.C (Φ_k_poly i) + MvPolynomial.X i) F
  have hF_shift_eval :
      MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
        (fun i : Fin (n + 1) => PowerSeries.X ^ k * eulerShiftIter k i.1 ψ) F_shift = 0 := by
    have hcomp : ∀ Q : MvPolynomial (Fin (n + 1)) (Polynomial ℂ),
        MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
          (fun i => PowerSeries.X ^ k * eulerShiftIter k i.1 ψ)
          (MvPolynomial.aeval (fun i => MvPolynomial.C (Φ_k_poly i) + MvPolynomial.X i) Q) =
        evalEulerPS Q f := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => simp [evalEulerPS]
      | add P₁ P₂ h1 h2 =>
        rw [map_add, MvPolynomial.eval₂_add, h1, h2]
        simp [evalEulerPS]
      | mul_X P₁ j h1 =>
        simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, h1, evalEulerPS]
        congr 1
        rw [hf_split, eulerPS_iter_add, eulerPS_iter_X_pow_mul]
        simp [Φ_k_poly, coe_polyEuler_iter]
    rw [hcomp F, hFeval]
  let a_k : Fin (n + 1) → Polynomial ℂ := fun i => F_shift.coeff (Finsupp.single i 1)
  have ha_top_agree : ∀ j ≤ l_n, (a_k (Fin.last n)).coeff j = PowerSeries.coeff j a_top := by
    have ha_k_eq : ((a_k (Fin.last n) : Polynomial ℂ) : PowerSeries ℂ) =
        evalEulerPS (MvPolynomial.pderiv (Fin.last n) F) (u_k : PowerSeries ℂ) := by
      dsimp only [a_k, F_shift]
      rw [coeff_single_aeval_add]
      unfold evalEulerPS
      have hhom : ∀ Q : MvPolynomial (Fin (n + 1)) (Polynomial ℂ),
          ((MvPolynomial.eval₂ (RingHom.id _) Φ_k_poly Q : Polynomial ℂ) : PowerSeries ℂ) =
            MvPolynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
              (fun i => eulerPS^[i.1] (u_k : PowerSeries ℂ)) Q := by
        intro Q
        induction Q using MvPolynomial.induction_on with
        | C c => simp
        | add P₁ P₂ h1 h2 =>
          rw [MvPolynomial.eval₂_add, Polynomial.coe_add, MvPolynomial.eval₂_add, h1, h2]
        | mul_X P₁ j h1 =>
          rw [MvPolynomial.eval₂_mul, Polynomial.coe_mul, MvPolynomial.eval₂_mul, h1,
            MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
          simp [Φ_k_poly, coe_polyEuler_iter]
      exact hhom _
    have hdiff_zero : ∀ (Q : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) (j : ℕ), j ≤ k →
        PowerSeries.coeff j (evalEulerPS Q (u_k : PowerSeries ℂ)) =
          PowerSeries.coeff j (evalEulerPS Q f) := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => intro j _; simp [evalEulerPS]
      | add P₁ P₂ h1 h2 =>
        intro j hj
        simp only [evalEulerPS, MvPolynomial.eval₂_add, map_add]
        exact congr_arg₂ (· + ·) (h1 j hj) (h2 j hj)
      | mul_X P₁ i h1 =>
        intro j hj
        simp only [evalEulerPS, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
          PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun pq hpq => ?_
        have hp_le : pq.1 ≤ j := (Finset.mem_antidiagonal.mp hpq ▸ Nat.le_add_right _ _)
        have hq_le : pq.2 ≤ j := (Finset.mem_antidiagonal.mp hpq ▸ Nat.le_add_left _ _)
        have harg : PowerSeries.coeff pq.2 (eulerPS^[i.1] (u_k : PowerSeries ℂ)) =
            PowerSeries.coeff pq.2 (eulerPS^[i.1] f) := by
          rw [hf_split, eulerPS_iter_add, eulerPS_iter_X_pow_mul, map_add,
            PowerSeries.coeff_X_pow_mul']
          have h0 : (if k ≤ pq.2 then PowerSeries.coeff (pq.2 - k) (eulerShiftIter k i.1 ψ) else 0) = 0 := by
            by_cases hkq : k ≤ pq.2
            · have hqeq : pq.2 - k = 0 := by omega
              simp [hkq, hqeq, coeff_eulerShiftIter, ψ]
            · simp [hkq]
          rw [h0, add_zero]
        exact congr_arg₂ (· * ·) (h1 pq.1 (hp_le.trans hj)) harg
    intro j hj
    rw [← Polynomial.coeff_coe, ha_k_eq]
    exact hdiff_zero (MvPolynomial.pderiv (Fin.last n) F) j (by omega)
  let b_n : Polynomial ℂ :=
    ∑ j ∈ Finset.range ((a_k (Fin.last n)).natDegree + 1),
      Polynomial.monomial j ((a_k (Fin.last n)).coeff (l_n + 1 + j))
  let b_low : Fin (n + 1) → Polynomial ℂ := fun i =>
    ∑ j ∈ Finset.range ((a_k i).natDegree + 1),
      Polynomial.monomial j ((a_k i).coeff (l_n + j))
  let c_irreg : Fin (n + 1) → ℕ → ℂ := fun i p => (a_k i).coeff (l_n - p)
  let h_0 : Polynomial ℂ := F_shift.coeff 0
  let S_nl : Finset (Fin (n + 1) →₀ ℕ) :=
    F_shift.support.filter fun d => 2 ≤ d.sum (fun _ m => m)
  let varList : (Fin (n + 1) →₀ ℕ) → List (Fin (n + 1)) := fun d =>
    (List.finRange (n + 1)).flatMap fun i => List.replicate (d i) i
  have hvarList_len : ∀ d : Fin (n + 1) →₀ ℕ,
      (varList d).length = d.sum (fun _ m => m) := by
    intro d
    rw [Finsupp.sum_fintype d (fun _ m => m) (fun _ => rfl)]
    simp only [varList, List.length_flatMap, List.length_replicate]
    rw [← Fin.sum_univ_def]
  have hvarList_prod : ∀ (d : Fin (n + 1) →₀ ℕ) (g : Fin (n + 1) → PowerSeries ℂ),
      (∏ i : Fin (n + 1), (g i) ^ (d i)) = ((varList d).map g).prod := by
    intro d g
    simp only [varList, List.map_flatMap, List.map_replicate]
    have hprod_flat : ∀ (L : List (Fin (n + 1))),
        (L.flatMap fun a => List.replicate (d a) (g a)).prod =
          (L.map fun a => (g a) ^ (d a)).prod := by
      intro L
      induction L with
      | nil => simp
      | cons a as ihL => simp [List.prod_replicate, ihL]
    rw [hprod_flat, ← Fin.prod_univ_def]
  -- For any `m ≥ 1`, extract the exact coefficient `[X^{k + l_n + m}]` of `hF_shift_eval = 0`!
  -- Define the sequence-level nonlinear term `nlSeq v` (divided by `X^{k + l_n}`, i.e. shifted by `r_d = (D - 1)*k - l_n ≥ 2`)!
  let nlTermSeq (d : Fin (n + 1) →₀ ℕ) (w : ℕ → ℂ) : ℕ → ℂ :=
    let r_d : ℕ := (d.sum (fun _ m => m) - 1) * k - l_n
    shiftSeq r_d (seqMul (polySeq (F_shift.coeff d))
      (seqListProd ((varList d).map fun i => eulerShiftSeq k i.1 w)))
  -- For `m ≥ 1`, let `fullRHS w m` be the coefficient `[X^{k + l_n + m}]` of ALL terms EXCEPT `c_n (m + k)^n w m`:
  -- Wait: `P_M + v` is passed to `nlTermSeq` and regular terms; irregular terms act on `w`.
  have hcoeff_eq : ∀ m : ℕ, 1 ≤ m →
      c_n * (((m + k : ℕ) : ℂ) ^ n) * PowerSeries.coeff m ψ =
        -(h_0.coeff (k + l_n + m))
        - seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (fun j => PowerSeries.coeff j ψ)) m
        - (∑ i : Fin (n + 1),
            if i.1 < n then
              seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (fun j => PowerSeries.coeff j ψ)) m +
              ∑ p ∈ Finset.Icc 1 l_n,
                c_irreg i p * (((m + p + k : ℕ) : ℂ) ^ i.1) * PowerSeries.coeff (m + p) ψ
            else 0)
        - ∑ d ∈ S_nl, nlTermSeq d (fun j => PowerSeries.coeff j ψ) m := by
    intro m hm1
    have h0 := congr_arg (PowerSeries.coeff (k + l_n + m)) hF_shift_eval
    rw [map_zero] at h0
    -- Partition `F_shift.support` by total degree `0`, `1`, `≥ 2`.
    have hdeg_split : F_shift =
        MvPolynomial.C h_0 +
        ∑ i : Fin (n + 1), MvPolynomial.C (a_k i) * MvPolynomial.X i +
        ∑ d ∈ S_nl, MvPolynomial.monomial d (F_shift.coeff d) := by
      refine MvPolynomial.ext _ _ fun s => ?_
      simp only [← MvPolynomial.lcoeff_apply, map_add, map_sum]
      simp only [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_C, MvPolynomial.coeff_mul_X',
        MvPolynomial.coeff_monomial]
      by_cases hs0 : s = 0
      · subst hs0
        have hnot2 : (0 : Fin (n + 1) →₀ ℕ) ∉ S_nl := by simp [S_nl]
        simp [h_0, hnot2]
      · by_cases hs1 : s.sum (fun _ m => m) = 1
        · have hex_i : ∃ i₀ : Fin (n + 1), s = Finsupp.single i₀ 1 := by
            have hne : s.support.Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hs0 (Finsupp.support_eq_empty.mp h0)
            obtain ⟨i₀, hi₀⟩ := hne
            have hpos : 1 ≤ s i₀ := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi₀)
            have hle1 : s i₀ ≤ s.sum (fun _ m => m) :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi₀
            have hval : s i₀ = 1 := by omega
            refine ⟨i₀, ?_⟩
            ext j
            by_cases hji : j = i₀
            · subst hji; simp [hval]
            · rw [Finsupp.single_eq_of_ne hji]
              by_contra hjne
              have hjmem : j ∈ s.support := Finsupp.mem_support_iff.mpr hjne
              have hsum2 : s i₀ + s j ≤ s.sum (fun _ m => m) :=
                Finset.add_le_sum (f := fun x => s x) (fun _ _ => Nat.zero_le _) hi₀ hjmem (Ne.symm hji)
              have hjpos : 1 ≤ s j := Nat.one_le_iff_ne_zero.mpr hjne
              omega
          obtain ⟨i₀, rfl⟩ := hex_i
          have hnot2 : Finsupp.single i₀ 1 ∉ S_nl := by simp [S_nl]
          have hsum_i : ∑ i : Fin (n + 1),
              (if i ∈ (Finsupp.single i₀ 1 : Fin (n + 1) →₀ ℕ).support then
                if (0 : Fin (n + 1) →₀ ℕ) = Finsupp.single i₀ 1 - Finsupp.single i 1 then a_k i else 0
              else 0) = a_k i₀ := by
            rw [Finset.sum_eq_single i₀]
            · simp
            · intro i _ hne
              have hnot : i ∉ (Finsupp.single i₀ 1 : Fin (n + 1) →₀ ℕ).support := by
                rw [Finsupp.mem_support_iff, not_not]; exact Finsupp.single_eq_of_ne hne
              rw [ite_eq_right_iff.mpr fun h => absurd h hnot]
            · intro h; exact absurd (Finset.mem_univ i₀) h
          have h0ne : (0 : Fin (n + 1) →₀ ℕ) ≠ Finsupp.single i₀ 1 := Ne.symm hs0
          have hsum_nl : ∑ d ∈ S_nl,
              (if d = Finsupp.single i₀ 1 then F_shift.coeff d else 0) = 0 :=
            Finset.sum_eq_zero fun d hd => by
              simp [show d ≠ Finsupp.single i₀ 1 from fun h => hnot2 (h ▸ hd)]
          rw [ite_eq_right_iff.mpr (fun h => absurd h h0ne), zero_add, hsum_nl, add_zero]
          exact hsum_i.symm
        · have hge2 : 2 ≤ s.sum (fun _ m => m) := by
            have hne0 : s.sum (fun _ m => m) ≠ 0 := by
              intro hsum0
              apply hs0
              ext j
              have hle : s j ≤ s.sum (fun _ m => m) := by
                by_cases hj : j ∈ s.support
                · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
                · rw [Finsupp.notMem_support_iff.mp hj]; exact Nat.zero_le _
              have h0j : (0 : Fin (n + 1) →₀ ℕ) j = 0 := rfl
              omega
            omega
          have hsum_i : ∑ i : Fin (n + 1),
              (if i ∈ s.support then
                if (0 : Fin (n + 1) →₀ ℕ) = s - Finsupp.single i 1 then a_k i else 0
              else 0) = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            split_ifs with hi hsub0
            · exfalso
              have hle : Finsupp.single i 1 ≤ s := by
                rw [Finsupp.single_le_iff]
                exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
              have hsum_eq : s = Finsupp.single i 1 := by
                have hsub := tsub_add_cancel_of_le hle
                rw [← hsub0, zero_add] at hsub
                exact hsub.symm
              rw [hsum_eq] at hge2
              simp at hge2
            · rfl
            · rfl
          have h0ne : (0 : Fin (n + 1) →₀ ℕ) ≠ s := Ne.symm hs0
          rw [ite_eq_right_iff.mpr (fun h => absurd h h0ne), zero_add, hsum_i, zero_add]
          by_cases hmem : s ∈ F_shift.support
          · have hmem2 : s ∈ S_nl := Finset.mem_filter.mpr ⟨hmem, hge2⟩
            rw [Finset.sum_eq_single s]
            · simp
            · intro d _ hne; simp [hne]
            · intro hnot; exact absurd hmem2 hnot
          · have hnot2 : s ∉ S_nl := fun h => hmem (Finset.mem_filter.mp h).1
            rw [Finset.sum_eq_zero (fun d hd => by simp [show d ≠ s from fun h => hnot2 (h ▸ hd)])]
            exact MvPolynomial.notMem_support_iff.mp hmem
    rw [hdeg_split] at h0
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_monomial,
      map_add, map_sum, Polynomial.coeToPowerSeries.ringHom_apply] at h0
    have hP0 : PowerSeries.coeff (k + l_n + m) (h_0 : PowerSeries ℂ) = h_0.coeff (k + l_n + m) :=
      Polynomial.coeff_coe h_0 _
    have hP1_top : PowerSeries.coeff (k + l_n + m)
        ((a_k (Fin.last n) : PowerSeries ℂ) * (PowerSeries.X ^ k * eulerShiftIter k n ψ)) =
        c_n * (((m + k : ℕ) : ℂ) ^ n) * PowerSeries.coeff m ψ +
        seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (fun j => PowerSeries.coeff j ψ)) m := by
      rw [← mul_assoc, mul_comm ((a_k (Fin.last n) : PowerSeries ℂ)), mul_assoc,
        PowerSeries.coeff_X_pow_mul']
      have hkm : k ≤ k + l_n + m := by omega
      simp only [hkm, ite_true, show k + l_n + m - k = l_n + m by omega]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
        PowerSeries.coeff a (a_k (Fin.last n) : PowerSeries ℂ) * PowerSeries.coeff b (eulerShiftIter k n ψ))]
      have hsplit_sum : ∑ j ∈ Finset.range (l_n + m).succ,
          PowerSeries.coeff j (a_k (Fin.last n) : PowerSeries ℂ) *
            PowerSeries.coeff (l_n + m - j) (eulerShiftIter k n ψ) =
          PowerSeries.coeff l_n (a_k (Fin.last n) : PowerSeries ℂ) *
            PowerSeries.coeff m (eulerShiftIter k n ψ) +
          ∑ r ∈ Finset.range m,
            PowerSeries.coeff (l_n + 1 + r) (a_k (Fin.last n) : PowerSeries ℂ) *
              PowerSeries.coeff (m - 1 - r) (eulerShiftIter k n ψ) := by
        rw [Nat.succ_eq_add_one, show l_n + m + 1 = (l_n + 1) + m by omega,
          Finset.sum_range_add, Finset.sum_range_succ]
        have hlt0 : ∑ j ∈ Finset.range l_n,
            PowerSeries.coeff j (a_k (Fin.last n) : PowerSeries ℂ) *
              PowerSeries.coeff (l_n + m - j) (eulerShiftIter k n ψ) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          rw [Finset.mem_range] at hj
          rw [Polynomial.coeff_coe, ha_top_agree j (by omega), ha_top_lt j hj, zero_mul]
        rw [hlt0, zero_add, show l_n + m - l_n = m by omega]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [show l_n + m - (l_n + 1 + r) = m - 1 - r by omega]
      rw [hsplit_sum]
      have hcn_eq : PowerSeries.coeff l_n (a_k (Fin.last n) : PowerSeries ℂ) = c_n := by
        rw [Polynomial.coeff_coe, ha_top_agree l_n le_rfl]
      rw [hcn_eq, coeff_eulerShiftIter, mul_assoc]
      congr 1
      · push_cast; ring
      · unfold seqMul polySeq eulerShiftSeq
        rw [Finset.sum_range_succ']
        simp only [Polynomial.coeff_X_mul_zero, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        rw [Polynomial.coeff_coe, Polynomial.coeff_X_mul, coeff_eulerShiftIter]
        have hbn_coeff : b_n.coeff r = (a_k (Fin.last n)).coeff (l_n + 1 + r) := by
          dsimp only [b_n]; rw [← Polynomial.lcoeff_apply, map_sum]
          simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
          by_cases hdeg : r ≤ (a_k (Fin.last n)).natDegree
          · rw [Finset.sum_eq_single r]
            · simp
            · intro j _ hne; simp [hne]
            · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
          · rw [Finset.sum_eq_zero (fun j hj => by rw [Finset.mem_range] at hj; simp [show j ≠ r by omega])]
            exact (Polynomial.coeff_eq_zero_of_natDegree_lt (p := a_k (Fin.last n)) (by omega)).symm
        rw [hbn_coeff, show m - (r + 1) = m - 1 - r by omega]
        push_cast
        ring
    have hP1_low : ∀ i : Fin (n + 1), i.1 < n →
        PowerSeries.coeff (k + l_n + m)
          ((a_k i : PowerSeries ℂ) * (PowerSeries.X ^ k * eulerShiftIter k i.1 ψ)) =
        seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (fun j => PowerSeries.coeff j ψ)) m +
        ∑ p ∈ Finset.Icc 1 l_n,
          c_irreg i p * (((m + p + k : ℕ) : ℂ) ^ i.1) * PowerSeries.coeff (m + p) ψ := by
      intro i _
      rw [← mul_assoc, mul_comm ((a_k i : PowerSeries ℂ)), mul_assoc,
        PowerSeries.coeff_X_pow_mul']
      have hkm : k ≤ k + l_n + m := by omega
      simp only [hkm, ite_true, show k + l_n + m - k = l_n + m by omega]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
          PowerSeries.coeff a (a_k i : PowerSeries ℂ) * PowerSeries.coeff b (eulerShiftIter k i.1 ψ)),
        show (l_n + m).succ = l_n + (m + 1) by omega, Finset.sum_range_add, add_comm]
      congr 1
      · unfold seqMul polySeq eulerShiftSeq
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        rw [Polynomial.coeff_coe, coeff_eulerShiftIter]
        have hbl : (b_low i).coeff r = (a_k i).coeff (l_n + r) := by
          dsimp only [b_low]; rw [← Polynomial.lcoeff_apply, map_sum]
          simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
          by_cases hdeg : r ≤ (a_k i).natDegree
          · rw [Finset.sum_eq_single r]
            · simp
            · intro j _ hne; simp [hne]
            · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
          · rw [Finset.sum_eq_zero (fun j hj => by rw [Finset.mem_range] at hj; simp [show j ≠ r by omega])]
            exact (Polynomial.coeff_eq_zero_of_natDegree_lt (p := a_k i) (by omega)).symm
        rw [hbl, show l_n + m - (l_n + r) = m - r by omega]
        push_cast; ring
      · refine Finset.sum_bij (fun j _ => l_n - j) ?_ ?_ ?_ ?_
        · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Icc]; omega
        · intro j₁ hj₁ j₂ hj₂ heq; rw [Finset.mem_range] at hj₁ hj₂; omega
        · intro p hp; rw [Finset.mem_Icc] at hp
          exact ⟨l_n - p, Finset.mem_range.mpr (by omega), by omega⟩
        · intro j hj
          rw [Finset.mem_range] at hj
          rw [Polynomial.coeff_coe, coeff_eulerShiftIter]
          simp only [c_irreg, show l_n - (l_n - j) = j by omega,
            show l_n + m - j = m + (l_n - j) by omega]
          push_cast; ring
    have hP1 : ∑ i : Fin (n + 1), PowerSeries.coeff (k + l_n + m)
        ((a_k i : PowerSeries ℂ) * (PowerSeries.X ^ k * eulerShiftIter k i.1 ψ)) =
        c_n * (((m + k : ℕ) : ℂ) ^ n) * PowerSeries.coeff m ψ +
        seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (fun j => PowerSeries.coeff j ψ)) m +
        ∑ i : Fin (n + 1),
          if i.1 < n then
            seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (fun j => PowerSeries.coeff j ψ)) m +
            ∑ p ∈ Finset.Icc 1 l_n,
              c_irreg i p * (((m + p + k : ℕ) : ℂ) ^ i.1) * PowerSeries.coeff (m + p) ψ
          else 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.last n))]
      simp only [Fin.val_last]
      rw [hP1_top, add_assoc]
      conv_rhs => rw [add_assoc]
      congr 1
      congr 1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.last n))]
      simp only [Fin.val_last, lt_self_iff_false, ite_false, zero_add]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i ≠ Fin.last n := (Finset.mem_erase.mp hi).1
      have hlt : i.1 < n := by have := i.2; have : i.1 ≠ n := fun h => hne (Fin.ext h); omega
      simp only [hlt, ite_true]
      exact hP1_low i hlt
    have hP2 : ∀ d ∈ S_nl,
        PowerSeries.coeff (k + l_n + m)
          ((F_shift.coeff d : PowerSeries ℂ) *
            d.prod fun i e => (PowerSeries.X ^ k * eulerShiftIter k i.1 ψ) ^ e) =
        nlTermSeq d (fun j => PowerSeries.coeff j ψ) m := by
      intro d hd
      have hD2 : 2 ≤ d.sum (fun _ m => m) := (Finset.mem_filter.mp hd).2
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      have hprod_split : (∏ i : Fin (n + 1), (PowerSeries.X ^ k * eulerShiftIter k i.1 ψ) ^ (d i)) =
          PowerSeries.X ^ (d.sum (fun _ m => m) * k) *
            ∏ i : Fin (n + 1), (eulerShiftIter k i.1 ψ) ^ (d i) := by
        simp_rw [mul_pow, ← pow_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        congr 2
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [hprod_split, ← mul_assoc, mul_comm ((F_shift.coeff d : PowerSeries ℂ)), mul_assoc]
      let D : ℕ := d.sum (fun _ m => m)
      let r_d : ℕ := (D - 1) * k - l_n
      have hDk : D * k = (k + l_n) + r_d := by
        have h1 : k + l_n ≤ D * k := by
          calc k + l_n ≤ 2 * k := by omega
            _ ≤ D * k := Nat.mul_le_mul_right k hD2
        have h2 : (D - 1) * k = D * k - k := by
          rw [Nat.sub_mul, one_mul]
        omega
      rw [hDk, pow_add, mul_assoc, PowerSeries.coeff_X_pow_mul']
      have hklm : k + l_n ≤ k + l_n + m := by omega
      simp only [hklm, ite_true, show k + l_n + m - (k + l_n) = m by omega]
      rw [PowerSeries.coeff_X_pow_mul']
      dsimp only [nlTermSeq, shiftSeq]
      change (if r_d ≤ m then _ else 0) = if r_d ≤ m then _ else 0
      split_ifs with hrm
      · rw [coeff_mul_eq_seqMul]
        have h1eq : (fun j => PowerSeries.coeff j (F_shift.coeff d : PowerSeries ℂ)) =
            polySeq (F_shift.coeff d) := by ext j; exact Polynomial.coeff_coe _ j
        have hlist_coeff : ∀ (L : List (Fin (n + 1))) (j : ℕ),
            PowerSeries.coeff j (L.map fun i => eulerShiftIter k i.1 ψ).prod =
              seqListProd (L.map fun i => eulerShiftSeq k i.1 (fun t => PowerSeries.coeff t ψ)) j := by
          intro L
          induction L with
          | nil =>
            intro j
            simp [seqListProd, PowerSeries.coeff_one]
          | cons i is ihL =>
            intro j
            simp only [List.map_cons, List.prod_cons, seqListProd, coeff_mul_eq_seqMul]
            have hf1 : (fun t => PowerSeries.coeff t (eulerShiftIter k i.1 ψ)) =
                eulerShiftSeq k i.1 (fun t => PowerSeries.coeff t ψ) := by
              ext t; simp [coeff_eulerShiftIter, eulerShiftSeq]
            have hf2 : (fun t => PowerSeries.coeff t (List.map (fun i => eulerShiftIter k i.1 ψ) is).prod) =
                seqListProd (List.map (fun i => eulerShiftSeq k i.1 (fun t => PowerSeries.coeff t ψ)) is) := by
              ext t; exact ihL t
            rw [hf1, hf2]
        have h2eq : (fun j => PowerSeries.coeff j (∏ i : Fin (n + 1), (eulerShiftIter k i.1 ψ) ^ (d i))) =
            seqListProd ((varList d).map fun i => eulerShiftSeq k i.1 (fun t => PowerSeries.coeff t ψ)) := by
          ext j; rw [hvarList_prod]; exact hlist_coeff (varList d) j
        rw [h1eq, h2eq]
      · rfl
    rw [hP0, hP1, Finset.sum_congr rfl hP2] at h0
    linear_combination h0
  -- Step 5: Set `ε = 1 / (4 * l_n + 2)` and extract Gevrey-`ε` bound for `ψ` from `hsub`.
  let ε : ℝ := 1 / ((4 * l_n + 2 : ℕ) : ℝ)
  have hε_pos : 0 < ε := by positivity
  obtain ⟨C₀, A₀, hC₀, hA₀, hgev_f⟩ := hsub ε hε_pos
  -- Convert `IsGevrey ε f` to a Gevrey-`ε` bound on `ψ`:
  -- For `m ≥ 1`, `‖ψ m‖ = ‖f (k + m)‖ ≤ C₀ A₀^(k + m) ((k + m)!)^ε ≤ C₁ * A₁^m * (m!)^ε`.
  have hgev_ψ : ∃ C₁ A₁ : ℝ, 0 ≤ C₁ ∧ 1 ≤ A₁ ∧
      ∀ m : ℕ, ‖PowerSeries.coeff m ψ‖ ≤ C₁ * A₁ ^ m * ((m.factorial : ℝ) ^ ε) := by
    let C₁ : ℝ := C₀ * A₀ ^ k * ((2 ^ k * k.factorial : ℕ) : ℝ) ^ ε
    let A₁ : ℝ := max 1 (A₀ * (2 : ℝ) ^ ε)
    refine ⟨C₁, A₁, by positivity, le_max_left _ _, fun m => ?_⟩
    by_cases hm0 : m = 0
    · subst hm0; simp [ψ]; positivity
    · have hcoeff : PowerSeries.coeff m ψ = PowerSeries.coeff (k + m) f := by simp [ψ, hm0]
      rw [hcoeff]
      have hfac_le : (k + m).factorial ≤ (2 ^ k * k.factorial) * (2 ^ m * m.factorial) := by
        have hbin : (k + m).factorial = (k + m).choose k * (k.factorial * m.factorial) := by
          have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k m)
          rw [Nat.add_sub_cancel_left] at this
          linarith
        have hch : (k + m).choose k ≤ 2 ^ (k + m) := by
          calc (k + m).choose k
              ≤ ∑ j ∈ Finset.range (k + m + 1), (k + m).choose j :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                  (Finset.mem_range.mpr (by omega))
            _ = 2 ^ (k + m) := Nat.sum_range_choose (k + m)
        calc (k + m).factorial
            = (k + m).choose k * (k.factorial * m.factorial) := hbin
          _ ≤ 2 ^ (k + m) * (k.factorial * m.factorial) := Nat.mul_le_mul_right _ hch
          _ = (2 ^ k * k.factorial) * (2 ^ m * m.factorial) := by rw [pow_add]; ring
      have hrpow_le : (((k + m).factorial : ℝ) ^ ε) ≤
          (((2 ^ k * k.factorial : ℕ) : ℝ) ^ ε) * ((2 : ℝ) ^ ε) ^ m * ((m.factorial : ℝ) ^ ε) := by
        calc (((k + m).factorial : ℝ) ^ ε)
            ≤ (((2 ^ k * k.factorial : ℕ) : ℝ) * (((2 : ℝ) ^ m) * (m.factorial : ℝ))) ^ ε := by
              refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hε_pos.le
              exact_mod_cast hfac_le
          _ = (((2 ^ k * k.factorial : ℕ) : ℝ) ^ ε) * ((((2 : ℝ) ^ m) * (m.factorial : ℝ)) ^ ε) :=
              Real.mul_rpow (Nat.cast_nonneg _) (by positivity)
          _ = (((2 ^ k * k.factorial : ℕ) : ℝ) ^ ε) * (((2 : ℝ) ^ m) ^ ε * ((m.factorial : ℝ) ^ ε)) := by
              rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
          _ = (((2 ^ k * k.factorial : ℕ) : ℝ) ^ ε) * ((2 : ℝ) ^ ε) ^ m * ((m.factorial : ℝ) ^ ε) := by
              rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
                mul_comm (m : ℝ) ε, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
              ring
      calc ‖PowerSeries.coeff (k + m) f‖
          ≤ C₀ * A₀ ^ (k + m) * (((k + m).factorial : ℝ) ^ ε) := hgev_f (k + m)
        _ ≤ C₀ * (A₀ ^ k * A₀ ^ m) *
              ((((2 ^ k * k.factorial : ℕ) : ℝ) ^ ε) * ((2 : ℝ) ^ ε) ^ m * ((m.factorial : ℝ) ^ ε)) := by
            rw [pow_add]
            exact mul_le_mul_of_nonneg_left hrpow_le (by positivity)
        _ = C₁ * (A₀ * (2 : ℝ) ^ ε) ^ m * ((m.factorial : ℝ) ^ ε) := by
            rw [mul_pow]; dsimp only [C₁]; ring
        _ ≤ C₁ * A₁ ^ m * ((m.factorial : ℝ) ^ ε) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_max_right _ _) m)
                (by positivity))
              (Real.rpow_nonneg (Nat.cast_nonneg _) ε)
  obtain ⟨C₁, A₁, hC₁, hA₁, hψ_gev⟩ := hgev_ψ
  -- Step 6: Compute fixed problem-dependent constants (independent of `B`) and pick `B : ℕ` large!
  have hcn_pos : 0 < ‖c_n‖ := norm_pos_iff.mpr hc_n_ne
  let K_bn : ℝ := polyL1 b_n
  let K_blow : ℝ := ∑ i : Fin (n + 1), if i.1 < n then polyL1 (b_low i) else 0
  let K_irreg : ℝ := ∑ i : Fin (n + 1), if i.1 < n then ∑ p ∈ Finset.Icc 1 l_n, ‖c_irreg i p‖ else 0
  let K_nl : ℝ := ∑ d ∈ S_nl,
    polyL1 (F_shift.coeff d) * ((varList d).length : ℝ) * (2 : ℝ) ^ ((varList d).length)
  have hKbn_nn : 0 ≤ K_bn := polyL1_nonneg b_n
  have hKblow_nn : 0 ≤ K_blow :=
    Finset.sum_nonneg fun i _ => by split_ifs; exact polyL1_nonneg _; exact le_rfl
  have hKirreg_nn : 0 ≤ K_irreg :=
    Finset.sum_nonneg fun i _ => by
      split_ifs; exact Finset.sum_nonneg fun _ _ => norm_nonneg _; exact le_rfl
  have hKnl_nn : 0 ≤ K_nl :=
    Finset.sum_nonneg fun d _ => mul_nonneg (mul_nonneg (polyL1_nonneg _) (Nat.cast_nonneg _))
      (pow_nonneg (by norm_num) _)
  -- Also `(m + k)^n ≤ ((k + 1) : ℝ)^n * (2^n)^m` for all `m ≥ 1`!
  have hmk_exp : ∀ m : ℕ, 1 ≤ m → (((m + k : ℕ) : ℝ) ^ n) ≤ ((k + 1 : ℕ) : ℝ) ^ n * ((2 : ℝ) ^ n) ^ m := by
    intro m hm
    have hm2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
    calc (((m + k : ℕ) : ℝ) ^ n)
        ≤ (((k + 1 : ℕ) : ℝ) * (m : ℝ)) ^ n := by
          refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ n
          have : m + k ≤ (k + 1) * m := by nlinarith
          exact_mod_cast this
      _ = ((k + 1 : ℕ) : ℝ) ^ n * (m : ℝ) ^ n := mul_pow _ _ _
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ n * ((2 : ℝ) ^ m) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hm2 n) (by positivity)
      _ = ((k + 1 : ℕ) : ℝ) ^ n * ((2 : ℝ) ^ n) ^ m := by
          rw [← pow_mul, ← pow_mul, mul_comm m n]
  let K_pref : ℝ := C₁ * ((k + 1 : ℕ) : ℝ) ^ n
  let A_eff : ℝ := (2 : ℝ) ^ n * A₁
  have hKpref_nn : 0 ≤ K_pref := by positivity
  have hAeff_ge1 : 1 ≤ A_eff := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hA₁
  -- Choose natural number `B` sufficiently large so ALL constants are `< 1/10`!
  let B_real : ℝ :=
    max 2 (max (h_0.natDegree + 1 : ℝ)
      (max (4 * A_eff)
        (max (8 * K_pref * A_eff)
          (max (8 * (K_bn + K_blow + K_irreg + K_nl + 1) / ‖c_n‖)
            (8 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1) / ‖c_n‖)))))
  let B : ℕ := Nat.ceil B_real + 2
  have hB_ge_real : B_real ≤ (B : ℝ) := by
    have := Nat.le_ceil B_real
    push_cast [B]; linarith
  have hB2 : 2 ≤ B := by
    have : (2 : ℝ) ≤ B := (le_max_left _ _).trans hB_ge_real
    exact_mod_cast this
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  let A : ℝ := (B : ℝ) ^ 2
  let M : ℕ := B ^ (4 * l_n + 2)
  have hA1 : 1 ≤ A := by
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
    exact one_le_pow₀ hB1
  have hApos : 0 < A := by linarith
  have hM_ge_B : B ≤ M := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ (4 * l_n + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hM1 : 1 ≤ M := by omega
  have hM_gt_h0 : h_0.natDegree < M := by
    have h1 : (h_0.natDegree + 1 : ℝ) ≤ B :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hB_ge_real
    have h2 : h_0.natDegree + 1 ≤ B := by exact_mod_cast h1
    omega
  -- Split `ψ` at `M`: `P_M` (supported on `1 ≤ m < M`) and `φ` (supported on `m ≥ M`).
  let P_M : ℕ → ℂ := fun m => if m < M then PowerSeries.coeff m ψ else 0
  let φ : ℕ → ℂ := fun m => if M ≤ m then PowerSeries.coeff m ψ else 0
  have hψ_eq_sum : (fun m => PowerSeries.coeff m ψ) = P_M + φ := by
    ext m
    simp only [Pi.add_apply, P_M, φ]
    by_cases hm : m < M
    · simp [hm, show ¬ M ≤ m by omega]
    · simp [hm, show M ≤ m by omega]
  have hφ_supp : ∀ m < M, φ m = 0 := fun m hm => by simp [φ, show ¬ M ≤ m by omega]
  -- Bound 1: `‖P_M‖_{n, 0, A} ≤ 2 * K_pref * A_eff / B ≤ 1 / 4`!
  have hPM_sum0 : SummableN k n 0 A P_M :=
    summable_of_ne_finset_zero (s := Finset.range M) fun m hm => by
      rw [Finset.mem_range, not_lt] at hm
      simp [P_M, show ¬ m < M by omega]
  have hPM_le_B : normN k n 0 A P_M ≤ 2 * K_pref * A_eff / (B : ℝ) := by
    unfold normN
    rw [tsum_eq_sum (s := Finset.range M)]
    · have hM_rpow : ((M : ℝ) ^ ε) = (B : ℝ) := by
        have hM_cast : (M : ℝ) = (B : ℝ) ^ (4 * l_n + 2) := by simp [M]
        rw [hM_cast, ← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
        have hne : ((4 * l_n + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        dsimp only [ε]
        rw [mul_one_div_cancel hne, Real.rpow_one]
      have hterm_le : ∀ m ∈ Finset.range M,
          (((m + k : ℕ) : ℝ) ^ n) * ‖P_M m‖ / gWeight 0 A m ≤
            K_pref * (A_eff / (B : ℝ)) ^ m := by
        intro m hm
        rw [Finset.mem_range] at hm
        by_cases hm0 : m = 0
        · subst hm0; simp [P_M, ψ]; positivity
        · have hm1 : 1 ≤ m := by omega
          simp only [P_M, hm, ite_true, gWeight_zero_eq]
          have hfac_M : ((m.factorial : ℝ) ^ ε) ≤ (B : ℝ) ^ m := by
            have hfm : (m.factorial : ℝ) ≤ (M : ℝ) ^ m := by
              have : m.factorial ≤ m ^ m := Nat.factorial_le_pow m
              calc (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast this
                _ ≤ (M : ℝ) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hm.le) m
            calc ((m.factorial : ℝ) ^ ε)
                ≤ ((M : ℝ) ^ m) ^ ε := Real.rpow_le_rpow (Nat.cast_nonneg _) hfm hε_pos.le
              _ = ((M : ℝ) ^ ε) ^ m := by
                  rw [← Real.rpow_natCast (M : ℝ) m, ← Real.rpow_mul (Nat.cast_nonneg _),
                    mul_comm (m : ℝ) ε, Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
              _ = (B : ℝ) ^ m := by rw [hM_rpow]
          calc (((m + k : ℕ) : ℝ) ^ n) * ‖PowerSeries.coeff m ψ‖ / A ^ m
              ≤ (((k + 1 : ℕ) : ℝ) ^ n * ((2 : ℝ) ^ n) ^ m) *
                  (C₁ * A₁ ^ m * (B : ℝ) ^ m) / ((B : ℝ) ^ 2) ^ m := by
                refine div_le_div_of_nonneg_right ?_ (pow_nonneg hApos.le m)
                refine mul_le_mul (hmk_exp m hm1) ?_ (norm_nonneg _) (by positivity)
                exact (hψ_gev m).trans
                  (mul_le_mul_of_nonneg_left hfac_M (by positivity))
            _ = K_pref * (A_eff / (B : ℝ)) ^ m := by
                have hBne : (B : ℝ) ≠ 0 := hBpos.ne'
                rw [div_pow, mul_pow]
                dsimp only [K_pref, A_eff]
                field_simp [hBne]
                rw [← pow_mul, ← pow_mul, mul_comm 2 m]
      have hr_le : A_eff / (B : ℝ) ≤ 1 / 2 := by
        have h4 : 4 * A_eff ≤ (B : ℝ) :=
          ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hB_ge_real
        rw [div_le_iff₀ hBpos]; linarith
      have hsum_geom : ∑ m ∈ Finset.range M, (if m = 0 then (0 : ℝ) else (A_eff / (B : ℝ)) ^ m) ≤
          2 * (A_eff / (B : ℝ)) := by
        cases M with
        | zero => simp; positivity
        | succ M' =>
          rw [Finset.sum_range_succ']
          simp only [ite_true, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
          have hr0 : 0 ≤ A_eff / (B : ℝ) := by positivity
          have hr_lt : A_eff / (B : ℝ) < 1 := by linarith
          calc ∑ m ∈ Finset.range M', (A_eff / (B : ℝ)) ^ (m + 1)
              = (A_eff / (B : ℝ)) * ∑ m ∈ Finset.range M', (A_eff / (B : ℝ)) ^ m := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by rw [pow_succ']
            _ ≤ (A_eff / (B : ℝ)) * (1 - A_eff / (B : ℝ))⁻¹ := by
                refine mul_le_mul_of_nonneg_left ?_ hr0
                rw [geom_sum_eq hr_lt.ne]
                have hnum : (A_eff / (B : ℝ)) ^ M' - 1 = -(1 - (A_eff / (B : ℝ)) ^ M') := by ring
                have hden : A_eff / (B : ℝ) - 1 = -(1 - A_eff / (B : ℝ)) := by ring
                rw [hnum, hden, neg_div_neg_eq, div_eq_mul_inv]
                have hle1 : 1 - (A_eff / (B : ℝ)) ^ M' ≤ 1 := by linarith [pow_nonneg hr0 M']
                calc (1 - (A_eff / (B : ℝ)) ^ M') * (1 - A_eff / (B : ℝ))⁻¹
                    ≤ 1 * (1 - A_eff / (B : ℝ))⁻¹ :=
                      mul_le_mul_of_nonneg_right hle1 (inv_nonneg.mpr (by linarith))
                  _ = (1 - A_eff / (B : ℝ))⁻¹ := one_mul _
            _ ≤ (A_eff / (B : ℝ)) * 2 := by
                refine mul_le_mul_of_nonneg_left ?_ hr0
                rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
            _ = 2 * (A_eff / (B : ℝ)) := mul_comm _ _
      calc ∑ m ∈ Finset.range M, (((m + k : ℕ) : ℝ) ^ n) * ‖P_M m‖ / gWeight 0 A m
          ≤ ∑ m ∈ Finset.range M, K_pref * (if m = 0 then 0 else (A_eff / (B : ℝ)) ^ m) := by
            refine Finset.sum_le_sum fun m hm => ?_
            by_cases hm0 : m = 0
            · subst hm0; simp [P_M, ψ]
            · simp only [hm0, ite_false]; exact hterm_le m hm
        _ = K_pref * ∑ m ∈ Finset.range M, (if m = 0 then 0 else (A_eff / (B : ℝ)) ^ m) :=
            (Finset.mul_sum ..).symm
        _ ≤ K_pref * (2 * (A_eff / (B : ℝ))) := mul_le_mul_of_nonneg_left hsum_geom hKpref_nn
        _ = 2 * K_pref * A_eff / (B : ℝ) := by ring
    · intro m hm; rw [Finset.mem_range, not_lt] at hm; simp [P_M, show ¬ m < M by omega]
  have hPM_le_one : normN k n 0 A P_M ≤ 1 := by
    have h8 : 8 * K_pref * A_eff ≤ (B : ℝ) :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))).trans hB_ge_real
    have : 2 * K_pref * A_eff / (B : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hBpos]; linarith
    linarith
  -- Bound 2: `SummableN k n ε A φ` and `normN k n ε A φ ≤ 1`!
  have hφ_sumE_and_le : SummableN k n ε A φ ∧ normN k n ε A φ ≤ 1 := by
    have hr_le : A_eff / A ≤ 1 / 2 := by
      have h4 : 4 * A_eff ≤ (B : ℝ) :=
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hB_ge_real
      have hB_le_A : (B : ℝ) ≤ A := by
        dsimp only [A]; nlinarith
      rw [div_le_iff₀ hApos]; linarith
    have hterm : ∀ m : ℕ, (((m + k : ℕ) : ℝ) ^ n) * ‖φ m‖ / gWeight ε A m ≤
        if m = 0 then 0 else K_pref * (A_eff / A) ^ m := by
      intro m
      by_cases hm0 : m = 0
      · subst hm0; simp [φ, show ¬ M ≤ 0 by omega]
      · simp only [hm0, ite_false]
        by_cases hmM : M ≤ m
        · simp only [φ, hmM, ite_true]
          unfold gWeight
          have hfac_pos : 0 < ((m.factorial : ℝ) ^ ε) :=
            Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) ε
          calc (((m + k : ℕ) : ℝ) ^ n) * ‖PowerSeries.coeff m ψ‖ / (A ^ m * (m.factorial : ℝ) ^ ε)
              ≤ (((k + 1 : ℕ) : ℝ) ^ n * ((2 : ℝ) ^ n) ^ m) *
                  (C₁ * A₁ ^ m * (m.factorial : ℝ) ^ ε) / (A ^ m * (m.factorial : ℝ) ^ ε) := by
                refine div_le_div_of_nonneg_right ?_ (mul_pos (pow_pos hApos m) hfac_pos).le
                exact mul_le_mul (hmk_exp m (by omega)) (hψ_gev m) (norm_nonneg _) (by positivity)
            _ = K_pref * (A_eff / A) ^ m := by
                rw [div_pow, mul_pow]
                dsimp only [K_pref, A_eff]
                field_simp [hfac_pos.ne', (pow_pos hApos m).ne']
        · simp only [φ, hmM, ite_false, norm_zero, mul_zero, zero_div]
          positivity
    have hsum_rhs : Summable (fun m : ℕ => if m = 0 then (0 : ℝ) else K_pref * (A_eff / A) ^ m) := by
      refine Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
        (fun m => by split_ifs; positivity; exact le_rfl)
        ((summable_geometric_of_lt_one (by positivity) (by linarith : A_eff / A < 1)).mul_left K_pref)
    have hsum : SummableN k n ε A φ :=
      Summable.of_nonneg_of_le
        (fun m => div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
          (gWeight_pos hApos m).le)
        hterm hsum_rhs
    refine ⟨hsum, ?_⟩
    have htsum_rhs : (∑' m : ℕ, if m = 0 then (0 : ℝ) else K_pref * (A_eff / A) ^ m) =
        K_pref * ((A_eff / A) * (1 - A_eff / A)⁻¹) := by
      rw [hsum_rhs.tsum_eq_zero_add]
      simp only [ite_true, zero_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      simp_rw [pow_succ', ← mul_assoc, mul_comm K_pref (A_eff / A), mul_assoc, tsum_mul_left,
        tsum_geometric_of_lt_one (by positivity) (by linarith : A_eff / A < 1)]
    have h8 : 8 * K_pref * A_eff ≤ (B : ℝ) :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))).trans hB_ge_real
    have hB_le_A : (B : ℝ) ≤ A := by dsimp only [A]; nlinarith
    have hle1 : K_pref * ((A_eff / A) * (1 - A_eff / A)⁻¹) ≤ 1 := by
      have hinv : (1 - A_eff / A)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      calc K_pref * ((A_eff / A) * (1 - A_eff / A)⁻¹)
          ≤ K_pref * ((A_eff / A) * 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv (by positivity)) hKpref_nn
        _ = 2 * K_pref * A_eff / A := by ring
        _ ≤ 1 := by rw [div_le_one hApos]; linarith
    exact (Summable.tsum_le_tsum hterm hsum hsum_rhs).trans (htsum_rhs ▸ hle1)
  -- Step 7: Define the tail operator `Φ : (ℕ → ℂ) → (ℕ → ℂ)` on `m ≥ M`!
  let rhsSeq (v : ℕ → ℂ) : ℕ → ℂ := fun m =>
    if M ≤ m then
      -(h_0.coeff (k + l_n + m))
      - seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (P_M + v)) m
      - (∑ i : Fin (n + 1),
          if i.1 < n then
            seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + v)) m +
            ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M v m
          else 0)
      - ∑ d ∈ S_nl, nlTermSeq d (P_M + v) m
    else 0
  let Φ (v : ℕ → ℂ) : ℕ → ℂ := fun m =>
    if M ≤ m then (c_n * (((m + k : ℕ) : ℂ) ^ n))⁻¹ * rhsSeq v m else 0
  have hΦ_supp : ∀ v m, m < M → Φ v m = 0 := fun v m hm => by simp [Φ, show ¬ M ≤ m by omega]
  have hφ_fix : Φ φ = φ := by
    ext m
    by_cases hm : M ≤ m
    · have hm1 : 1 ≤ m := by omega
      have hcn_mk_ne : c_n * (((m + k : ℕ) : ℂ) ^ n) ≠ 0 :=
        mul_ne_zero hc_n_ne (pow_ne_zero n (Nat.cast_ne_zero.mpr (by omega)))
      simp only [Φ, hm, ite_true, rhsSeq, φ]
      have hirreg_eq : ∀ (i : Fin (n + 1)) (p : ℕ),
          irregSeq k i.1 p M φ m = (((m + p + k : ℕ) : ℂ) ^ i.1) * PowerSeries.coeff (m + p) ψ := by
        intro i p
        simp only [irregSeq, hm, ite_true, φ, show M ≤ m + p by omega]
      have hsum_eq :
          -(h_0.coeff (k + l_n + m))
          - seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (P_M + φ)) m
          - (∑ i : Fin (n + 1),
              if i.1 < n then
                seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + φ)) m +
                ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M φ m
              else 0)
          - ∑ d ∈ S_nl, nlTermSeq d (P_M + φ) m =
          c_n * (((m + k : ℕ) : ℂ) ^ n) * PowerSeries.coeff m ψ := by
        rw [← hψ_eq_sum]
        have hirr_sum : (∑ i : Fin (n + 1),
            if i.1 < n then
              seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (fun j => PowerSeries.coeff j ψ)) m +
              ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M φ m
            else 0) =
            ∑ i : Fin (n + 1),
              if i.1 < n then
                seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (fun j => PowerSeries.coeff j ψ)) m +
                ∑ p ∈ Finset.Icc 1 l_n,
                  c_irreg i p * (((m + p + k : ℕ) : ℂ) ^ i.1) * PowerSeries.coeff (m + p) ψ
              else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs with hlt
          · congr 1
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hirreg_eq i p]; ring
          · rfl
        rw [hirr_sum, ← hcoeff_eq m hm1]
      rw [hsum_eq, inv_mul_cancel_left₀ hcn_mk_ne]
    · simp [Φ, φ, hm]
  have hdiv_normN : ∀ {s : ℝ} {u : ℕ → ℂ}, Summable0 s A u →
      SummableN k n s A (fun m => if M ≤ m then (c_n * (((m + k : ℕ) : ℂ) ^ n))⁻¹ * u m else 0) ∧
      normN k n s A (fun m => if M ≤ m then (c_n * (((m + k : ℕ) : ℂ) ^ n))⁻¹ * u m else 0) ≤
        ‖c_n‖⁻¹ * norm0 s A u := by
    intro s u hu
    have hle : ∀ m : ℕ,
        (((m + k : ℕ) : ℝ) ^ n) *
            ‖if M ≤ m then (c_n * (((m + k : ℕ) : ℂ) ^ n))⁻¹ * u m else 0‖ / gWeight s A m ≤
          ‖c_n‖⁻¹ * (‖u m‖ / gWeight s A m) := by
      intro m
      by_cases hm : M ≤ m
      · simp only [hm, ite_true, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        have hmk_ne : (((m + k : ℕ) : ℝ) ^ n) ≠ 0 :=
          (pow_pos (Nat.cast_pos.mpr (by omega)) n).ne'
        rw [mul_inv]
        have heq : (((m + k : ℕ) : ℝ) ^ n) * (‖c_n‖⁻¹ * ((((m + k : ℕ) : ℝ) ^ n)⁻¹) * ‖u m‖) /
            gWeight s A m = ‖c_n‖⁻¹ * (‖u m‖ / gWeight s A m) := by
          field_simp [hmk_ne]
        exact heq.le
      · simp only [hm, ite_false, norm_zero, mul_zero, zero_div]
        exact mul_nonneg (inv_nonneg.mpr hcn_pos.le)
          (div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le)
    have hsum := Summable.of_nonneg_of_le
      (fun m => div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
        (gWeight_pos hApos m).le)
      hle (hu.mul_left _)
    refine ⟨hsum, ?_⟩
    calc normN k n s A _
        ≤ ∑' m, ‖c_n‖⁻¹ * (‖u m‖ / gWeight s A m) :=
          Summable.tsum_le_tsum hle hsum (hu.mul_left _)
      _ = ‖c_n‖⁻¹ * norm0 s A u := tsum_mul_left
  -- Uniform bound on `rhsSeq v` and `rhsSeq v - rhsSeq w` for ANY `s ∈ [0, ε]`!
  have hrhs_bound : ∀ (s : ℝ), 0 ≤ s → s ≤ ε →
      ∀ (v : ℕ → ℂ), (∀ m < M, v m = 0) → SummableN k n s A v → normN k n s A v ≤ 1 →
      Summable0 s A (rhsSeq v) := by
    intro s hs0 hsE v _ hv_sum _
    have hPM_s : SummableN k n s A P_M := summableN_of_le hs0 hApos hPM_sum0
    have hPv_s : SummableN k n s A (P_M + v) := summableN_add hApos hPM_s hv_sum
    -- Show each piece of `rhsSeq v` is `Summable0 s A`!
    have h0_s : Summable0 s A (fun m => if M ≤ m then -(h_0.coeff (k + l_n + m)) else 0) := by
      refine summable0_of_finite_support 0 fun m _ => ?_
      by_cases hm : M ≤ m
      · simp only [hm, ite_true, neg_eq_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      · simp [hm]
    have hbn_s : Summable0 s A
        (seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (P_M + v))) :=
      (summable0_and_norm0_seqMul hs0 hApos
        (summable0_and_norm0_polySeq hs0 hA1 _).1
        (summable0_and_norm0_eulerShiftSeq hk1 le_rfl hApos hPv_s).1).1
    have hlow_s : Summable0 s A (fun m => ∑ i : Fin (n + 1),
        if i.1 < n then
          seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + v)) m +
          ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M v m
        else 0) := by
      have hterm_s : ∀ i : Fin (n + 1), Summable0 s A (fun m =>
          if i.1 < n then
            seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + v)) m +
            ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M v m
          else 0) := by
        intro i
        by_cases hlt : i.1 < n
        · simp only [hlt, ite_true]
          refine summable0_add hApos ?_ ?_
          · exact (summable0_and_norm0_seqMul hs0 hApos
              (summable0_and_norm0_polySeq hs0 hA1 _).1
              (summable0_and_norm0_eulerShiftSeq hk1 hlt.le hApos hPv_s).1).1
          · have : ∀ (S : Finset ℕ), (∀ p ∈ S, 1 ≤ p ∧ p ≤ l_n) →
                Summable0 s A (fun m => ∑ p ∈ S, c_irreg i p * irregSeq k i.1 p M v m) := by
              intro S
              induction S using Finset.induction_on with
              | empty => intro _; exact summable0_zero s A
              | @insert p S hp ihS =>
                intro hS
                have hp_mem := hS p (Finset.mem_insert_self p S)
                have hirr : Summable0 s A (irregSeq k i.1 p M v) :=
                  (summable0_and_norm0_irregSeq hk1 hlt hp_mem.1 hp_mem.2 hB2 hs0 hsE hv_sum).1
                have h1 := summable0_const_mul (c_irreg i p) hirr
                have h2 := ihS fun q hq => hS q (Finset.mem_insert_of_mem hq)
                convert summable0_add hApos h1 h2 using 1
                ext m; simp [Finset.sum_insert hp]
            exact this (Finset.Icc 1 l_n) (fun p hp => Finset.mem_Icc.mp hp)
        · simp only [hlt, ite_false]; exact summable0_zero s A
      have hfin : ∀ (S : Finset (Fin (n + 1))),
          Summable0 s A (fun m => ∑ i ∈ S,
            if i.1 < n then
              seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + v)) m +
              ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M v m
            else 0) := by
        intro S
        induction S using Finset.induction_on with
        | empty => exact summable0_zero s A
        | @insert i S hi ihS =>
          convert summable0_add hApos (hterm_s i) ihS using 1
          ext m; simp [Finset.sum_insert hi]
      exact hfin Finset.univ
    have hnl_s : Summable0 s A (fun m => ∑ d ∈ S_nl, nlTermSeq d (P_M + v) m) := by
      have hd_s : ∀ d ∈ S_nl, Summable0 s A (nlTermSeq d (P_M + v)) := by
        intro d _
        refine (summable0_and_norm0_shiftSeq hs0 hA1 _ ?_).1
        refine (summable0_and_norm0_seqMul hs0 hApos
          (summable0_and_norm0_polySeq hs0 hA1 _).1 ?_).1
        refine (summable0_and_norm0_seqListProd hs0 hApos _ fun u hu => ?_).1
        rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
        exact (summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPv_s).1
      have hfin : ∀ (S : Finset (Fin (n + 1) →₀ ℕ)), (∀ d ∈ S, d ∈ S_nl) →
          Summable0 s A (fun m => ∑ d ∈ S, nlTermSeq d (P_M + v) m) := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro _; exact summable0_zero s A
        | @insert d S hd ihS =>
          intro hS
          convert summable0_add hApos (hd_s d (hS d (Finset.mem_insert_self d S)))
            (ihS fun d' hd' => hS d' (Finset.mem_insert_of_mem hd')) using 1
          ext m; simp [Finset.sum_insert hd]
      exact hfin S_nl (fun _ h => h)
    -- `rhsSeq v` is pointwise bounded by the sum of these 4 summable pieces.
    have hcomb := summable0_sub hApos (summable0_sub hApos (summable0_sub hApos h0_s hbn_s) hlow_s) hnl_s
    refine Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le)
      (fun m => ?_) hcomb
    by_cases hm : M ≤ m
    · simp only [rhsSeq, hm, ite_true, Pi.sub_apply]; exact le_rfl
    · simp only [rhsSeq, hm, ite_false, norm_zero, zero_div]
      exact div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le
  -- Bound 3: `Φ 0` has `normN k n 0 A (Φ 0) ≤ 1 / 2`!
  have hΦ0_sum_and_le : SummableN k n 0 A (Φ 0) ∧ normN k n 0 A (Φ 0) ≤ 1 / 2 := by
    have hrhs0_s : Summable0 0 A (rhsSeq 0) :=
      hrhs_bound 0 le_rfl hε_pos.le 0 (fun _ _ => rfl) (summableN_zero k n 0 A) (by simp [normN_zero])
    obtain ⟨hsum, hle⟩ := hdiv_normN hrhs0_s
    refine ⟨hsum, hle.trans ?_⟩
    -- Bound `norm0 0 A (rhsSeq 0)`!
    have h0_zero : ∀ m, M ≤ m → h_0.coeff (k + l_n + m) = 0 := fun m hm =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hterm_rhs0 : ∀ m : ℕ, ‖rhsSeq 0 m‖ / gWeight 0 A m ≤
        ‖seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m‖ / gWeight 0 A m +
        (∑ i : Fin (n + 1), if i.1 < n then
          ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m‖ / gWeight 0 A m else 0) +
        (∑ d ∈ S_nl, ‖nlTermSeq d P_M m‖ / gWeight 0 A m) := by
      intro m
      by_cases hm : M ≤ m
      · simp only [rhsSeq, hm, ite_true, h0_zero m hm, neg_zero, add_zero, zero_sub]
        have hirr0 : ∀ (i : Fin (n + 1)) (p : ℕ), irregSeq k i.1 p M 0 m = 0 := by
          intro i p; simp [irregSeq]
        have h1 : ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m)
            - (∑ i : Fin (n + 1), if i.1 < n then
                seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m +
                ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M 0 m else 0)
            - ∑ d ∈ S_nl, nlTermSeq d P_M m‖ ≤
            ‖seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m‖ +
            (∑ i : Fin (n + 1), if i.1 < n then
              ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m‖ else 0) +
            (∑ d ∈ S_nl, ‖nlTermSeq d P_M m‖) := by
          simp_rw [hirr0, mul_zero, Finset.sum_const_zero, add_zero]
          calc ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m)
                - (∑ i : Fin (n + 1), if i.1 < n then seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m else 0)
                - ∑ d ∈ S_nl, nlTermSeq d P_M m‖
              ≤ ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m)
                  - (∑ i : Fin (n + 1), if i.1 < n then seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m else 0)‖ +
                ‖∑ d ∈ S_nl, nlTermSeq d P_M m‖ := norm_sub_le _ _
            _ ≤ ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m)‖ +
                ‖∑ i : Fin (n + 1), (if i.1 < n then seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m else 0)‖ +
                ∑ d ∈ S_nl, ‖nlTermSeq d P_M m‖ := by
                gcongr
                · exact norm_sub_le _ _
                · exact norm_sum_le _ _
            _ ≤ ‖seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m‖ +
                (∑ i : Fin (n + 1), if i.1 < n then ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m‖ else 0) +
                ∑ d ∈ S_nl, ‖nlTermSeq d P_M m‖ := by
                rw [norm_neg]
                gcongr
                refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
                split_ifs <;> simp
        refine (div_le_div_of_nonneg_right h1 (gWeight_pos hApos m).le).trans_eq ?_
        rw [add_div, add_div, Finset.sum_div, Finset.sum_div]
        congr 2
        refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
      · simp only [rhsSeq, hm, ite_false, norm_zero, zero_div]
        refine add_nonneg (add_nonneg ?_ ?_) ?_
        · exact div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le
        · exact Finset.sum_nonneg fun i _ => by
            split_ifs
            · exact div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le
            · exact le_rfl
        · exact Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le
    have hbn_0 := summable0_and_norm0_seqMul le_rfl hApos
      (summable0_and_norm0_polySeq le_rfl hA1 (Polynomial.X * b_n)).1
      (summable0_and_norm0_eulerShiftSeq hk1 le_rfl hApos hPM_sum0).1
    have hlow_0 : ∀ i : Fin (n + 1), Summable (fun m => if i.1 < n then
        ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m‖ / gWeight 0 A m else 0) := by
      intro i
      by_cases hlt : i.1 < n
      · simp only [hlt, ite_true]
        exact (summable0_and_norm0_seqMul le_rfl hApos
          (summable0_and_norm0_polySeq le_rfl hA1 _).1
          (summable0_and_norm0_eulerShiftSeq hk1 hlt.le hApos hPM_sum0).1).1
      · simp [hlt]
    have hnl_0 : ∀ d ∈ S_nl, Summable0 0 A (nlTermSeq d P_M) := fun d _ =>
      (summable0_and_norm0_shiftSeq le_rfl hA1 _
        (summable0_and_norm0_seqMul le_rfl hApos
          (summable0_and_norm0_polySeq le_rfl hA1 _).1
          (summable0_and_norm0_seqListProd le_rfl hApos _ fun u hu => by
            rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
            exact (summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPM_sum0).1).1).1).1
    have hrhs0_le : norm0 0 A (rhsSeq 0) ≤
        K_bn * A⁻¹ + K_blow * (2 * K_pref * A_eff / (B : ℝ)) + K_nl * A⁻¹ := by
      have hsum_comb : Summable (fun m =>
          ‖seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M) m‖ / gWeight 0 A m +
          (∑ i : Fin (n + 1), if i.1 < n then
            ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M) m‖ / gWeight 0 A m else 0) +
          (∑ d ∈ S_nl, ‖nlTermSeq d P_M m‖ / gWeight 0 A m)) :=
        (hbn_0.1.add (summable_sum fun i _ => hlow_0 i)).add (summable_sum fun d hd => hnl_0 d hd)
      have hts := Summable.tsum_le_tsum hterm_rhs0 hrhs0_s hsum_comb
      rw [Summable.tsum_add (hbn_0.1.add (summable_sum fun i _ => hlow_0 i))
            (summable_sum fun d hd => hnl_0 d hd),
        Summable.tsum_add hbn_0.1 (summable_sum fun i _ => hlow_0 i),
        Summable.tsum_finsetSum (fun i _ => hlow_0 i),
        Summable.tsum_finsetSum (fun d hd => hnl_0 d hd)] at hts
      refine hts.trans (add_le_add (add_le_add ?_ ?_) ?_)
      · calc norm0 0 A (seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n P_M))
            ≤ norm0 0 A (polySeq (Polynomial.X * b_n)) * norm0 0 A (eulerShiftSeq k n P_M) := hbn_0.2
          _ ≤ (A⁻¹ * K_bn) * 1 :=
              mul_le_mul (norm0_polySeq_X_mul le_rfl hA1 b_n)
                ((summable0_and_norm0_eulerShiftSeq hk1 le_rfl hApos hPM_sum0).2.trans hPM_le_one)
                (norm0_nonneg hApos _) (by positivity)
          _ = K_bn * A⁻¹ := by ring
      · rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hlt : i.1 < n
        · simp only [hlt, ite_true]
          have hm := summable0_and_norm0_seqMul le_rfl hApos
            (summable0_and_norm0_polySeq le_rfl hA1 (b_low i)).1
            (summable0_and_norm0_eulerShiftSeq hk1 hlt.le hApos hPM_sum0).1
          calc norm0 0 A (seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 P_M))
              ≤ norm0 0 A (polySeq (b_low i)) * norm0 0 A (eulerShiftSeq k i.1 P_M) := hm.2
            _ ≤ polyL1 (b_low i) * (2 * K_pref * A_eff / (B : ℝ)) :=
                mul_le_mul (summable0_and_norm0_polySeq le_rfl hA1 (b_low i)).2
                  ((summable0_and_norm0_eulerShiftSeq hk1 hlt.le hApos hPM_sum0).2.trans hPM_le_B)
                  (norm0_nonneg hApos _) (polyL1_nonneg _)
        · simp [hlt]
      · rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun d hd => ?_
        have hD2 : 2 ≤ d.sum (fun _ m => m) := (Finset.mem_filter.mp hd).2
        have hrd1 : 1 ≤ (d.sum (fun _ m => m) - 1) * k - l_n := by
          have : k ≤ (d.sum (fun _ m => m) - 1) * k :=
            Nat.le_mul_of_pos_left k (by omega)
          omega
        have hlist_s : ∀ u ∈ (varList d).map (fun i => eulerShiftSeq k i.1 P_M), Summable0 0 A u := by
          intro u hu; rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
          exact (summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPM_sum0).1
        obtain ⟨hp_s, hp_n⟩ := summable0_and_norm0_seqListProd le_rfl hApos _ hlist_s
        have hp_le1 : norm0 0 A (seqListProd ((varList d).map fun i => eulerShiftSeq k i.1 P_M)) ≤ 1 := by
          refine hp_n.trans ?_
          have hprod1 : ∀ L : List (ℕ → ℂ), (∀ u ∈ L, norm0 0 A u ≤ 1) →
              (L.map (norm0 0 A)).prod ≤ 1 := by
            intro L hL
            induction L with
            | nil => simp
            | cons x xs ihL =>
              simp only [List.map_cons, List.prod_cons]
              have hxs_nn : 0 ≤ (xs.map (norm0 0 A)).prod := List.prod_nonneg fun r hr => by
                rcases List.mem_map.mp hr with ⟨y, _, rfl⟩; exact norm0_nonneg hApos y
              calc norm0 0 A x * (xs.map (norm0 0 A)).prod
                  ≤ 1 * 1 := mul_le_mul (hL x (List.mem_cons_self ..))
                    (ihL fun y hy => hL y (List.mem_cons_of_mem _ hy)) hxs_nn zero_le_one
                _ = 1 := one_mul 1
          refine hprod1 _ fun u hu => ?_
          rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
          exact (summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPM_sum0).2.trans hPM_le_one
        obtain ⟨hm_s, hm_n⟩ := summable0_and_norm0_seqMul le_rfl hApos
          (summable0_and_norm0_polySeq le_rfl hA1 (F_shift.coeff d)).1 hp_s
        obtain ⟨_, hsh_n⟩ := summable0_and_norm0_shiftSeq le_rfl hA1
          ((d.sum (fun _ m => m) - 1) * k - l_n) hm_s
        have hApow : A⁻¹ ^ ((d.sum (fun _ m => m) - 1) * k - l_n) ≤ A⁻¹ := by
          calc A⁻¹ ^ ((d.sum (fun _ m => m) - 1) * k - l_n)
              ≤ A⁻¹ ^ 1 := pow_le_pow_of_le_one (inv_nonneg.mpr hApos.le) (inv_le_one_of_one_le₀ hA1) hrd1
            _ = A⁻¹ := pow_one _
        have hlen_ge1 : (1 : ℝ) ≤ ((varList d).length : ℝ) * (2 : ℝ) ^ ((varList d).length) := by
          rw [hvarList_len d]
          have h1 : (1 : ℝ) ≤ ((d.sum (fun _ m => m) : ℕ) : ℝ) := Nat.one_le_cast.mpr (by omega)
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (d.sum (fun _ m => m)) := one_le_pow₀ (by norm_num)
          nlinarith
        calc norm0 0 A (nlTermSeq d P_M)
            ≤ A⁻¹ ^ ((d.sum (fun _ m => m) - 1) * k - l_n) *
                norm0 0 A (seqMul (polySeq (F_shift.coeff d))
                  (seqListProd ((varList d).map fun i => eulerShiftSeq k i.1 P_M))) := hsh_n
          _ ≤ A⁻¹ * (polyL1 (F_shift.coeff d) * 1) := by
              refine mul_le_mul hApow ?_ (norm0_nonneg hApos _) (inv_nonneg.mpr hApos.le)
              exact hm_n.trans (mul_le_mul (summable0_and_norm0_polySeq le_rfl hA1 _).2 hp_le1
                (norm0_nonneg hApos _) (polyL1_nonneg _))
          _ ≤ polyL1 (F_shift.coeff d) * ((varList d).length : ℝ) * (2 : ℝ) ^ ((varList d).length) * A⁻¹ := by
              rw [mul_one, mul_comm A⁻¹]
              have : polyL1 (F_shift.coeff d) * 1 ≤
                  polyL1 (F_shift.coeff d) * (((varList d).length : ℝ) * (2 : ℝ) ^ ((varList d).length)) :=
                mul_le_mul_of_nonneg_left hlen_ge1 (polyL1_nonneg _)
              nlinarith [inv_nonneg.mpr hApos.le]
    have hinvA_le : A⁻¹ ≤ (B : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hApos hBpos]; dsimp only [A]; nlinarith
    have h8_big : 8 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1) / ‖c_n‖ ≤ (B : ℝ) :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))).trans hB_ge_real
    have h8_mul : 8 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1) ≤ (B : ℝ) * ‖c_n‖ := by
      rwa [div_le_iff₀ hcn_pos] at h8_big
    have htot : K_bn * A⁻¹ + K_blow * (2 * K_pref * A_eff / (B : ℝ)) + K_nl * A⁻¹ ≤
        (B : ℝ)⁻¹ * (2 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1)) := by
      have h1 : K_bn * A⁻¹ ≤ (B : ℝ)⁻¹ * K_bn := by
        rw [mul_comm (B : ℝ)⁻¹]; exact mul_le_mul_of_nonneg_left hinvA_le hKbn_nn
      have h2 : K_nl * A⁻¹ ≤ (B : ℝ)⁻¹ * K_nl := by
        rw [mul_comm (B : ℝ)⁻¹]; exact mul_le_mul_of_nonneg_left hinvA_le hKnl_nn
      have h3 : K_blow * (2 * K_pref * A_eff / (B : ℝ)) = (B : ℝ)⁻¹ * (2 * K_blow * (K_pref * A_eff)) := by
        rw [div_eq_mul_inv]; ring
      rw [h3]
      have h4 : K_bn + 2 * K_blow * (K_pref * A_eff) + K_nl ≤
          2 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1) := by
        have : 0 ≤ K_pref * A_eff := by positivity
        nlinarith
      calc K_bn * A⁻¹ + (B : ℝ)⁻¹ * (2 * K_blow * (K_pref * A_eff)) + K_nl * A⁻¹
          ≤ (B : ℝ)⁻¹ * K_bn + (B : ℝ)⁻¹ * (2 * K_blow * (K_pref * A_eff)) + (B : ℝ)⁻¹ * K_nl := by
            linarith
        _ = (B : ℝ)⁻¹ * (K_bn + 2 * K_blow * (K_pref * A_eff) + K_nl) := by ring
        _ ≤ (B : ℝ)⁻¹ * (2 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1)) :=
            mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hBpos.le)
    calc ‖c_n‖⁻¹ * norm0 0 A (rhsSeq 0)
        ≤ ‖c_n‖⁻¹ * ((B : ℝ)⁻¹ * (2 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1))) :=
          mul_le_mul_of_nonneg_left (hrhs0_le.trans htot) (inv_nonneg.mpr hcn_pos.le)
      _ = (2 * (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1)) / ((B : ℝ) * ‖c_n‖) := by
          rw [div_eq_mul_inv, mul_inv]; ring
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (mul_pos hBpos hcn_pos)]
          have : 0 ≤ (K_bn + K_blow + K_nl + 1) * (K_pref * A_eff + 1) := by positivity
          linarith
  -- Bound 4: Simultaneous `1/2`-Lipschitz contraction in BOTH `s = 0` and `s = ε`!
  have hΦ_lip : ∀ (s : ℝ), 0 ≤ s → s ≤ ε →
      ∀ v w, (∀ m < M, v m = 0) → (∀ m < M, w m = 0) →
        SummableN k n s A v → SummableN k n s A w →
        normN k n s A v ≤ 1 → normN k n s A w ≤ 1 →
        SummableN k n s A (Φ v) ∧ normN k n s A (Φ v - Φ w) ≤ (1 / 2) * normN k n s A (v - w) := by
    intro s hs0 hsE v w hv_supp hw_supp hv_sum hw_sum hv_le hw_le
    have hΦv_s : SummableN k n s A (Φ v) :=
      (hdiv_normN (hrhs_bound s hs0 hsE v hv_supp hv_sum hv_le)).1
    refine ⟨hΦv_s, ?_⟩
    have hrhs_v := hrhs_bound s hs0 hsE v hv_supp hv_sum hv_le
    have hrhs_w := hrhs_bound s hs0 hsE w hw_supp hw_sum hw_le
    have hdiff_eq : Φ v - Φ w =
        fun m => if M ≤ m then (c_n * (((m + k : ℕ) : ℂ) ^ n))⁻¹ * (rhsSeq v - rhsSeq w) m else 0 := by
      ext m; by_cases hm : M ≤ m <;> simp [Φ, hm, mul_sub]
    rw [hdiff_eq]
    refine (hdiv_normN (summable0_sub hApos hrhs_v hrhs_w)).2.trans ?_
    -- Bound `norm0 s A (rhsSeq v - rhsSeq w)` by `(K_bn + K_blow + K_irreg + K_nl) * B⁻¹ * normN k n s A (v - w)`!
    have hvw_supp : ∀ m < M, (v - w) m = 0 := fun m hm => by simp [hv_supp m hm, hw_supp m hm]
    have hvw_sum : SummableN k n s A (v - w) := summableN_sub hApos hv_sum hw_sum
    have hPM_s : SummableN k n s A P_M := summableN_of_le hs0 hApos hPM_sum0
    have hPM_le_s : normN k n s A P_M ≤ 1 := (normN_le_of_le hs0 hApos hPM_sum0).trans hPM_le_one
    have hPv_s : SummableN k n s A (P_M + v) := summableN_add hApos hPM_s hv_sum
    have hPw_s : SummableN k n s A (P_M + w) := summableN_add hApos hPM_s hw_sum
    have hPv_le : normN k n s A (P_M + v) ≤ 2 :=
      (normN_add_le hApos hPM_s hv_sum).trans (by linarith)
    have hPw_le : normN k n s A (P_M + w) ≤ 2 :=
      (normN_add_le hApos hPM_s hw_sum).trans (by linarith)
    -- Pointwise triangle inequality on `(rhsSeq v - rhsSeq w) m`:
    have hpt : ∀ m : ℕ, ‖(rhsSeq v - rhsSeq w) m‖ / gWeight s A m ≤
        ‖seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m‖ / gWeight s A m +
        (∑ i : Fin (n + 1), if i.1 < n then
          ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m‖ / gWeight s A m +
          ∑ p ∈ Finset.Icc 1 l_n, ‖c_irreg i p‖ * (‖irregSeq k i.1 p M (v - w) m‖ / gWeight s A m)
        else 0) +
        (∑ d ∈ S_nl, ‖(nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖ / gWeight s A m) := by
      intro m
      by_cases hm : M ≤ m
      · have hlin_bn : seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (P_M + v)) m -
            seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (P_M + w)) m =
            seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m := by
          simp only [seqMul, eulerShiftSeq, ← Finset.sum_sub_distrib, Pi.add_apply, Pi.sub_apply]
          refine Finset.sum_congr rfl fun j _ => by ring
        have hlin_low : ∀ i : Fin (n + 1),
            seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + v)) m -
            seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + w)) m =
            seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m := by
          intro i
          simp only [seqMul, eulerShiftSeq, ← Finset.sum_sub_distrib, Pi.add_apply, Pi.sub_apply]
          refine Finset.sum_congr rfl fun j _ => by ring
        have hlin_irr : ∀ (i : Fin (n + 1)) (p : ℕ),
            irregSeq k i.1 p M v m - irregSeq k i.1 p M w m =
            irregSeq k i.1 p M (v - w) m := by
          intro i p; simp only [irregSeq, hm, ite_true, Pi.sub_apply]; ring
        have hdiff_m : (rhsSeq v - rhsSeq w) m =
            -(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m)
            - (∑ i : Fin (n + 1), if i.1 < n then
                seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m +
                ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M (v - w) m else 0)
            - ∑ d ∈ S_nl, (nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m := by
          simp only [Pi.sub_apply, rhsSeq, hm, ite_true, ← hlin_bn]
          have hsub_low : ∑ i : Fin (n + 1),
              ((if i.1 < n then seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + v)) m +
                  ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M v m else 0) -
               (if i.1 < n then seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (P_M + w)) m +
                  ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M w m else 0)) =
              ∑ i : Fin (n + 1), if i.1 < n then
                seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m +
                ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M (v - w) m else 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs with hlt
            · rw [← hlin_low i]
              have : ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M v m -
                  ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M w m =
                  ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M (v - w) m := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun p _ => by rw [← mul_sub, hlin_irr i p]
              linear_combination this
            · ring
          rw [← hsub_low]
          simp only [Finset.sum_sub_distrib]
          ring
        rw [hdiff_m]
        have htri : ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m)
            - (∑ i : Fin (n + 1), if i.1 < n then
                seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m +
                ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M (v - w) m else 0)
            - ∑ d ∈ S_nl, (nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖ ≤
            ‖seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m‖ +
            (∑ i : Fin (n + 1), if i.1 < n then
              ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m‖ +
              ∑ p ∈ Finset.Icc 1 l_n, ‖c_irreg i p‖ * ‖irregSeq k i.1 p M (v - w) m‖ else 0) +
            ∑ d ∈ S_nl, ‖(nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖ := by
          calc _ ≤ ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m)
                - (∑ i : Fin (n + 1), if i.1 < n then
                    seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m +
                    ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M (v - w) m else 0)‖ +
                ‖∑ d ∈ S_nl, (nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖ := norm_sub_le _ _
            _ ≤ ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m)‖ +
                ‖∑ i : Fin (n + 1), (if i.1 < n then
                    seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m +
                    ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M (v - w) m else 0)‖ +
                ∑ d ∈ S_nl, ‖(nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖ := by
                gcongr
                · exact norm_sub_le _ _
                · exact norm_sum_le _ _
            _ ≤ _ := by
                rw [norm_neg]
                gcongr
                refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
                split_ifs with hlt
                · refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
                  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => by rw [norm_mul])
                · simp
        calc ‖-(seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m)
              - (∑ i : Fin (n + 1), if i.1 < n then
                  seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m +
                  ∑ p ∈ Finset.Icc 1 l_n, c_irreg i p * irregSeq k i.1 p M (v - w) m else 0)
              - ∑ d ∈ S_nl, (nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖ / gWeight s A m
            ≤ (‖seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)) m‖ +
                (∑ i : Fin (n + 1), if i.1 < n then
                  ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m‖ +
                  ∑ p ∈ Finset.Icc 1 l_n, ‖c_irreg i p‖ * ‖irregSeq k i.1 p M (v - w) m‖ else 0) +
                ∑ d ∈ S_nl, ‖(nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖) / gWeight s A m :=
              div_le_div_of_nonneg_right htri (gWeight_pos hApos m).le
          _ = _ := by
              rw [add_div, add_div, Finset.sum_div, Finset.sum_div]
              congr 2
              refine Finset.sum_congr rfl fun i _ => ?_
              split_ifs with hlt
              · rw [add_div, Finset.sum_div]
                congr 1
                refine Finset.sum_congr rfl fun p _ => mul_div_assoc _ _ _
              · simp
      · simp only [Pi.sub_apply, rhsSeq, hm, ite_false, sub_self, norm_zero, zero_div]
        refine add_nonneg (add_nonneg ?_ ?_) ?_
        · exact div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le
        · exact Finset.sum_nonneg fun i _ => by
            split_ifs
            · exact add_nonneg (div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le)
                (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _)
                  (div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le))
            · exact le_rfl
        · exact Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (gWeight_pos hApos m).le
    -- Summability of each RHS piece in `hpt`.
    have hs_bn := summable0_and_norm0_seqMul hs0 hApos
      (summable0_and_norm0_polySeq hs0 hA1 (Polynomial.X * b_n)).1
      (summable0_and_norm0_eulerShiftSeq hk1 le_rfl hApos hvw_sum).1
    have hs_low : ∀ i : Fin (n + 1), Summable (fun m => if i.1 < n then
        ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m‖ / gWeight s A m +
        ∑ p ∈ Finset.Icc 1 l_n, ‖c_irreg i p‖ * (‖irregSeq k i.1 p M (v - w) m‖ / gWeight s A m)
      else 0) := by
      intro i
      by_cases hlt : i.1 < n
      · simp only [hlt, ite_true]
        refine Summable.add ?_ (summable_sum fun p hp => ?_)
        · exact (summable0_and_norm0_seqMul hs0 hApos
            (summable0_and_norm0_polySeq hs0 hA1 (b_low i)).1
            (summable0_and_norm0_eulerShiftSeq hk1 hlt.le hApos hvw_sum).1).1
        · have hp_mem := Finset.mem_Icc.mp hp
          exact ((summable0_and_norm0_irregSeq hk1 hlt hp_mem.1 hp_mem.2 hB2 hs0 hsE hvw_sum).1).mul_left _
      · simp [hlt]
    have hs_nl : ∀ d ∈ S_nl, Summable0 s A (nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) := by
      intro d _
      have h1 : Summable0 s A (nlTermSeq d (P_M + v)) :=
        (summable0_and_norm0_shiftSeq hs0 hA1 _
          (summable0_and_norm0_seqMul hs0 hApos
            (summable0_and_norm0_polySeq hs0 hA1 _).1
            (summable0_and_norm0_seqListProd hs0 hApos _ fun u hu => by
              rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
              exact (summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPv_s).1).1).1).1
      have h2 : Summable0 s A (nlTermSeq d (P_M + w)) :=
        (summable0_and_norm0_shiftSeq hs0 hA1 _
          (summable0_and_norm0_seqMul hs0 hApos
            (summable0_and_norm0_polySeq hs0 hA1 _).1
            (summable0_and_norm0_seqListProd hs0 hApos _ fun u hu => by
              rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
              exact (summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPw_s).1).1).1).1
      exact summable0_sub hApos h1 h2
    have hs_low_sum : Summable (fun m => ∑ i : Fin (n + 1), if i.1 < n then
        ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m‖ / gWeight s A m +
          ∑ p ∈ Finset.Icc 1 l_n, ‖c_irreg i p‖ * (‖irregSeq k i.1 p M (v - w) m‖ / gWeight s A m)
        else 0) := summable_sum (s := Finset.univ) fun i _ => hs_low i
    have hs_nl_sum : Summable (fun m => ∑ d ∈ S_nl,
        ‖(nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w)) m‖ / gWeight s A m) :=
      summable_sum (s := S_nl) fun d hd => hs_nl d hd
    have hsum_all := (hs_bn.1.add hs_low_sum).add hs_nl_sum
    have hts := Summable.tsum_le_tsum hpt (summable0_sub hApos hrhs_v hrhs_w) hsum_all
    rw [Summable.tsum_add (hs_bn.1.add hs_low_sum) hs_nl_sum,
      Summable.tsum_add hs_bn.1 hs_low_sum,
      Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => hs_low i),
      Summable.tsum_finsetSum (s := S_nl) (fun d hd => hs_nl d hd)] at hts
    have hinvA_le : A⁻¹ ≤ (B : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hApos hBpos]; dsimp only [A]; nlinarith
    have hinvM_le : (M : ℝ)⁻¹ ≤ (B : ℝ)⁻¹ :=
      inv_anti₀ hBpos (by exact_mod_cast hM_ge_B)
    -- Bound each of the 3 pieces!
    have hP_bn : norm0 s A (seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w))) ≤
        K_bn * (B : ℝ)⁻¹ * normN k n s A (v - w) := by
      calc norm0 s A (seqMul (polySeq (Polynomial.X * b_n)) (eulerShiftSeq k n (v - w)))
          ≤ norm0 s A (polySeq (Polynomial.X * b_n)) * norm0 s A (eulerShiftSeq k n (v - w)) := hs_bn.2
        _ ≤ (A⁻¹ * K_bn) * normN k n s A (v - w) :=
            mul_le_mul (norm0_polySeq_X_mul hs0 hA1 b_n)
              (summable0_and_norm0_eulerShiftSeq hk1 le_rfl hApos hvw_sum).2
              (norm0_nonneg hApos _) (by positivity)
        _ ≤ ((B : ℝ)⁻¹ * K_bn) * normN k n s A (v - w) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinvA_le hKbn_nn)
              (normN_nonneg hApos _)
        _ = K_bn * (B : ℝ)⁻¹ * normN k n s A (v - w) := by ring
    have hP_low : (∑ i : Fin (n + 1), ∑' m, if i.1 < n then
          ‖seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)) m‖ / gWeight s A m +
          ∑ p ∈ Finset.Icc 1 l_n, ‖c_irreg i p‖ * (‖irregSeq k i.1 p M (v - w) m‖ / gWeight s A m)
        else 0) ≤ (K_blow + K_irreg) * (B : ℝ)⁻¹ * normN k n s A (v - w) := by
      rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hlt : i.1 < n
      · simp only [hlt, ite_true]
        have h1s := (summable0_and_norm0_seqMul hs0 hApos
          (summable0_and_norm0_polySeq hs0 hA1 (b_low i)).1
          (summable0_and_norm0_eulerShiftSeq hk1 hlt.le hApos hvw_sum).1)
        have h2s : ∀ p ∈ Finset.Icc 1 l_n,
            Summable (fun m => ‖c_irreg i p‖ * (‖irregSeq k i.1 p M (v - w) m‖ / gWeight s A m)) := by
          intro p hp; have hp_mem := Finset.mem_Icc.mp hp
          exact ((summable0_and_norm0_irregSeq hk1 hlt hp_mem.1 hp_mem.2 hB2 hs0 hsE hvw_sum).1).mul_left _
        rw [Summable.tsum_add h1s.1 (summable_sum h2s), Summable.tsum_finsetSum h2s]
        refine add_le_add ?_ ?_
        · calc norm0 s A (seqMul (polySeq (b_low i)) (eulerShiftSeq k i.1 (v - w)))
              ≤ norm0 s A (polySeq (b_low i)) * norm0 s A (eulerShiftSeq k i.1 (v - w)) := h1s.2
            _ ≤ polyL1 (b_low i) * ((M : ℝ)⁻¹ * normN k n s A (v - w)) :=
                mul_le_mul (summable0_and_norm0_polySeq hs0 hA1 (b_low i)).2
                  (norm0_eulerShiftSeq_lt_le hk1 hlt hM1 hApos hvw_supp hvw_sum)
                  (norm0_nonneg hApos _) (polyL1_nonneg _)
            _ ≤ polyL1 (b_low i) * ((B : ℝ)⁻¹ * normN k n s A (v - w)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hinvM_le (normN_nonneg hApos _)) (polyL1_nonneg _)
            _ = polyL1 (b_low i) * (B : ℝ)⁻¹ * normN k n s A (v - w) := by ring
        · rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_mem := Finset.mem_Icc.mp hp
          rw [tsum_mul_left]
          have hirr := (summable0_and_norm0_irregSeq hk1 hlt hp_mem.1 hp_mem.2 hB2 hs0 hsE hvw_sum).2
          calc ‖c_irreg i p‖ * norm0 s A (irregSeq k i.1 p M (v - w))
              ≤ ‖c_irreg i p‖ * ((B : ℝ)⁻¹ * normN k n s A (v - w)) :=
                mul_le_mul_of_nonneg_left hirr (norm_nonneg _)
            _ = ‖c_irreg i p‖ * (B : ℝ)⁻¹ * normN k n s A (v - w) := by ring
      · simp [hlt]
    have hP_nl : (∑ d ∈ S_nl, norm0 s A (nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w))) ≤
        K_nl * (B : ℝ)⁻¹ * normN k n s A (v - w) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun d hd => ?_
      have hD2 : 2 ≤ d.sum (fun _ m => m) := (Finset.mem_filter.mp hd).2
      have hrd1 : 1 ≤ (d.sum (fun _ m => m) - 1) * k - l_n := by
        have : k ≤ (d.sum (fun _ m => m) - 1) * k := Nat.le_mul_of_pos_left k (by omega)
        omega
      let L₁ := (varList d).map fun i => eulerShiftSeq k i.1 (P_M + v)
      let L₂ := (varList d).map fun i => eulerShiftSeq k i.1 (P_M + w)
      have hnl_sub : nlTermSeq d (P_M + v) - nlTermSeq d (P_M + w) =
          shiftSeq ((d.sum (fun _ m => m) - 1) * k - l_n)
            (seqMul (polySeq (F_shift.coeff d)) (seqListProd L₁ - seqListProd L₂)) := by
        ext m
        simp only [nlTermSeq, shiftSeq, Pi.sub_apply]
        split_ifs with hrm
        · simp only [seqMul, ← Finset.sum_sub_distrib, Pi.sub_apply]
          refine Finset.sum_congr rfl fun j _ => by ring
        · ring
      rw [hnl_sub]
      have hL1 : ∀ u ∈ L₁, Summable0 s A u ∧ norm0 s A u ≤ 2 := by
        intro u hu; rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
        obtain ⟨hs1, hn1⟩ := summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPv_s
        exact ⟨hs1, hn1.trans hPv_le⟩
      have hL2 : ∀ u ∈ L₂, Summable0 s A u ∧ norm0 s A u ≤ 2 := by
        intro u hu; rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
        obtain ⟨hs2, hn2⟩ := summable0_and_norm0_eulerShiftSeq hk1 (Nat.lt_succ_iff.mp i.2) hApos hPw_s
        exact ⟨hs2, hn2.trans hPw_le⟩
      have hprod_sub_s : Summable0 s A (seqListProd L₁ - seqListProd L₂) :=
        summable0_sub hApos
          (summable0_and_norm0_seqListProd hs0 hApos L₁ (fun u hu => (hL1 u hu).1)).1
          (summable0_and_norm0_seqListProd hs0 hApos L₂ (fun u hu => (hL2 u hu).1)).1
      have hprod_sub_n : norm0 s A (seqListProd L₁ - seqListProd L₂) ≤
          ((varList d).length : ℝ) * (2 : ℝ) ^ ((varList d).length) * normN k n s A (v - w) := by
        have hlen : L₁.length = L₂.length := by simp [L₁, L₂]
        have hlip := norm0_seqListProd_sub_le hs0 hApos (by norm_num : (1 : ℝ) ≤ 2)
          L₁ L₂ hlen hL1 hL2 (normN_nonneg hApos _) (fun idx hidx => by
            have hidx' : idx < (varList d).length := by simpa [L₁] using hidx
            have heq_sub : L₁[idx] - L₂[idx]'(hlen ▸ hidx) =
                eulerShiftSeq k ((varList d)[idx]'hidx').1 (v - w) := by
              ext m; simp [L₁, L₂, eulerShiftSeq]; ring
            rw [heq_sub]
            exact (summable0_and_norm0_eulerShiftSeq hk1
              (Nat.lt_succ_iff.mp ((varList d)[idx]'hidx').2) hApos hvw_sum).2)
        have hlen1 : L₁.length = (varList d).length := by simp [L₁]
        rw [hlen1] at hlip
        refine hlip.trans ?_
        have hpow_le : (2 : ℝ) ^ ((varList d).length - 1) ≤ (2 : ℝ) ^ ((varList d).length) :=
          pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ 1)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_le (Nat.cast_nonneg _)) (normN_nonneg hApos _)
      obtain ⟨hm_s, hm_n⟩ := summable0_and_norm0_seqMul hs0 hApos
        (summable0_and_norm0_polySeq hs0 hA1 (F_shift.coeff d)).1 hprod_sub_s
      obtain ⟨_, hsh_n⟩ := summable0_and_norm0_shiftSeq hs0 hA1
        ((d.sum (fun _ m => m) - 1) * k - l_n) hm_s
      have hApow : A⁻¹ ^ ((d.sum (fun _ m => m) - 1) * k - l_n) ≤ (B : ℝ)⁻¹ := by
        calc A⁻¹ ^ ((d.sum (fun _ m => m) - 1) * k - l_n)
            ≤ A⁻¹ ^ 1 := pow_le_pow_of_le_one (inv_nonneg.mpr hApos.le) (inv_le_one_of_one_le₀ hA1) hrd1
          _ = A⁻¹ := pow_one _
          _ ≤ (B : ℝ)⁻¹ := hinvA_le
      calc norm0 s A _
          ≤ A⁻¹ ^ ((d.sum (fun _ m => m) - 1) * k - l_n) *
              norm0 s A (seqMul (polySeq (F_shift.coeff d)) (seqListProd L₁ - seqListProd L₂)) := hsh_n
        _ ≤ (B : ℝ)⁻¹ * (polyL1 (F_shift.coeff d) *
              (((varList d).length : ℝ) * (2 : ℝ) ^ ((varList d).length) * normN k n s A (v - w))) := by
            refine mul_le_mul hApow ?_ (norm0_nonneg hApos _) (inv_nonneg.mpr hBpos.le)
            exact hm_n.trans (mul_le_mul (summable0_and_norm0_polySeq hs0 hA1 _).2 hprod_sub_n
              (norm0_nonneg hApos _) (polyL1_nonneg _))
        _ = polyL1 (F_shift.coeff d) * ((varList d).length : ℝ) * (2 : ℝ) ^ ((varList d).length) *
              (B : ℝ)⁻¹ * normN k n s A (v - w) := by ring
    have h8_lip : 8 * (K_bn + K_blow + K_irreg + K_nl + 1) / ‖c_n‖ ≤ (B : ℝ) :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))).trans hB_ge_real
    have h8_mul : 8 * (K_bn + K_blow + K_irreg + K_nl + 1) ≤ (B : ℝ) * ‖c_n‖ := by
      rwa [div_le_iff₀ hcn_pos] at h8_lip
    have hrhs_tot : norm0 s A (rhsSeq v - rhsSeq w) ≤
        (K_bn + K_blow + K_irreg + K_nl) * (B : ℝ)⁻¹ * normN k n s A (v - w) := by
      have hcomb : norm0 s A (rhsSeq v - rhsSeq w) ≤
          K_bn * (B : ℝ)⁻¹ * normN k n s A (v - w) +
          (K_blow + K_irreg) * (B : ℝ)⁻¹ * normN k n s A (v - w) +
          K_nl * (B : ℝ)⁻¹ * normN k n s A (v - w) :=
        hts.trans (add_le_add (add_le_add hP_bn hP_low) hP_nl)
      linarith
    calc ‖c_n‖⁻¹ * norm0 s A (rhsSeq v - rhsSeq w)
        ≤ ‖c_n‖⁻¹ * ((K_bn + K_blow + K_irreg + K_nl) * (B : ℝ)⁻¹ * normN k n s A (v - w)) :=
          mul_le_mul_of_nonneg_left hrhs_tot (inv_nonneg.mpr hcn_pos.le)
      _ = ((K_bn + K_blow + K_irreg + K_nl) / ((B : ℝ) * ‖c_n‖)) * normN k n s A (v - w) := by
          rw [div_eq_mul_inv, mul_inv]; ring
      _ ≤ (1 / 2) * normN k n s A (v - w) := by
          refine mul_le_mul_of_nonneg_right ?_ (normN_nonneg hApos _)
          rw [div_le_iff₀ (mul_pos hBpos hcn_pos)]; linarith
  -- Step 8: Apply `simultaneous_contraction_fixed_point`!
  obtain ⟨hφ_sum0, hφ_le0⟩ := simultaneous_contraction_fixed_point hk1 hA1 hε_pos Φ hΦ_supp
    hΦ0_sum_and_le.1 hΦ0_sum_and_le.2
    (hΦ_lip 0 le_rfl hε_pos.le) (hΦ_lip ε hε_pos.le le_rfl)
    hφ_supp hφ_sumE_and_le.1 hφ_sumE_and_le.2 hφ_fix
  -- Step 9: Deduce `IsConvergentPS f`!
  -- For `j ≥ k + M`, `‖coeff j f‖ = ‖φ (j - k)‖ ≤ A^(j - k) ≤ A^j`!
  -- For `j < k + M`, there are finitely many coefficients, bounded by `C_fin`.
  let C_fin : ℝ := (Finset.range (k + M)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun j => ‖PowerSeries.coeff j f‖)
  let C : ℝ := max 1 C_fin
  refine ⟨C, A, by positivity, hApos, fun j => ?_⟩
  by_cases hj : j < k + M
  · have hle_fin : ‖PowerSeries.coeff j f‖ ≤ C_fin :=
      Finset.le_sup' (f := fun t => ‖PowerSeries.coeff t f‖) (Finset.mem_range.mpr hj)
    calc ‖PowerSeries.coeff j f‖
        ≤ C := hle_fin.trans (le_max_right 1 C_fin)
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * A ^ j := mul_le_mul_of_nonneg_left (one_le_pow₀ hA1) (by positivity)
  · push Not at hj
    have hjm : M ≤ j - k := by omega
    have hcoeff_eq_φ : PowerSeries.coeff j f = φ (j - k) := by
      have hne : j - k ≠ 0 := by omega
      simp [φ, hjm, ψ, hne, Nat.add_sub_of_le (show k ≤ j by omega)]
    rw [hcoeff_eq_φ]
    have hmk1 : (1 : ℝ) ≤ (((j - k + k : ℕ) : ℝ) ^ n) :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ j - k + k by omega))
    have hterm_le : (((j - k + k : ℕ) : ℝ) ^ n) * ‖φ (j - k)‖ / A ^ (j - k) ≤ 1 := by
      have hle_tsum := hφ_sum0.le_tsum (j - k) fun t _ =>
        div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) n) (norm_nonneg _))
          (gWeight_pos hApos t).le
      have hle' : (((j - k + k : ℕ) : ℝ) ^ n) * ‖φ (j - k)‖ / A ^ (j - k) ≤ normN k n 0 A φ := by
        simpa [normN, gWeight_zero_eq] using hle_tsum
      exact hle'.trans hφ_le0
    have hφ_bd : ‖φ (j - k)‖ ≤ A ^ (j - k) := by
      rw [div_le_one (pow_pos hApos (j - k))] at hterm_le
      calc ‖φ (j - k)‖ = 1 * ‖φ (j - k)‖ := (one_mul _).symm
        _ ≤ (((j - k + k : ℕ) : ℝ) ^ n) * ‖φ (j - k)‖ :=
            mul_le_mul_of_nonneg_right hmk1 (norm_nonneg _)
        _ ≤ A ^ (j - k) := hterm_le
    calc ‖φ (j - k)‖
        ≤ A ^ (j - k) := hφ_bd
      _ ≤ A ^ j := pow_le_pow_right₀ hA1 (Nat.sub_le j k)
      _ = 1 * A ^ j := (one_mul _).symm
      _ ≤ C * A ^ j := mul_le_mul_of_nonneg_right (le_max_left 1 C_fin) (pow_nonneg hApos.le j)

/-- **Sibuya's Sub-Gevrey Convergence Theorem (Ordinary-Derivative form, 100% unconditional):**
If `f : PowerSeries ℂ` is sub-Gevrey (`∀ s > 0, IsGevrey s f`) and satisfies a nonzero
polynomial algebraic differential equation `P(X, f, f', ..., f^{(r)}) = 0` over `ℂ[X]`,
then `f` is convergent (`IsConvergentPS f`). -/
theorem sibuya_subGevrey_convergent {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : P ≠ 0)
    {f : PowerSeries ℂ} (hsub : IsSubGevrey f) (hf : evalDerivPS P f = 0) :
    IsConvergentPS f := by
  obtain ⟨Q, hQne, hQeval⟩ := exists_nonzero_euler_ade_of_deriv_ade hP hf
  exact sibuya_subGevrey_convergent_euler hQne hsub hQeval

/-!
## Section 2: Reciprocal Gamma Growth & Sub-Gevrey Divergence of `volterraAsympSeries`

For every `α : ℂ` and `β : ℂ` with `-1 < β.re`, we define:
- `recipGamma α z := (Complex.Gamma (1 + α + z))⁻¹` (entire on `ℂ`),
- `volterraCoeff β α n := (Γ(n + β + 1) / Γ(β + 1)) * (iteratedDeriv n (recipGamma α) 0 / n!)`,
- `volterraAsympSeries β α := PowerSeries.mk (volterraCoeff β α)`.

We prove unconditionally:
1. `recipGamma_entire_growth`: `‖1 / Γ(1 + α + z)‖ ≤ exp (C * (‖z‖ + 1) * log (2 + ‖z‖))`.
2. `volterraAsympSeries_isSubGevrey`: `IsSubGevrey (volterraAsympSeries β α)`.
3. `volterraAsympSeries_not_convergent`: `¬ IsConvergentPS (volterraAsympSeries β α)`.
-/

/-- The entire reciprocal Gamma function `z ↦ (Γ(1 + α + z))⁻¹`. -/
@[expose] noncomputable def recipGamma (α : ℂ) (z : ℂ) : ℂ :=
  (Complex.Gamma (1 + α + z))⁻¹

/-- The `n`-th coefficient of the formal asymptotic expansion of the Volterra function
`μ(t, β, α)` at `t = 0⁺`. -/
@[expose] noncomputable def volterraCoeff (β α : ℂ) (n : ℕ) : ℂ :=
  (Complex.Gamma ((n : ℂ) + β + 1) / Complex.Gamma (β + 1)) *
    (iteratedDeriv n (recipGamma α) 0 / (n.factorial : ℂ))

/-- The formal asymptotic power series of `u ↦ e^{α u} u^{β + 1} μ(e^{-u}, β, α)` in `x = 1/u`. -/
@[expose] noncomputable def volterraAsympSeries (β α : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (volterraCoeff β α)

lemma differentiable_recipGamma (α : ℂ) : Differentiable ℂ (recipGamma α) :=
  Complex.differentiable_one_div_Gamma.comp ((differentiable_const (1 + α)).add differentiable_id)

/-! ### Harmonic number and elementary product bounds -/

private lemma harmonic_bounds {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ∧
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ≤ Real.log (n : ℝ) + 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp
    · obtain ⟨hlo, hhi⟩ := ih (by omega)
      rw [Finset.sum_range_succ]
      have hm1 : (0 : ℝ) < (m + 1 : ℝ) := by positivity
      have hm2 : (0 : ℝ) < (m + 2 : ℝ) := by positivity
      have hdiff_le : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤
          1 / ((m + 1 : ℕ) : ℝ) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < ((m + 2 : ℕ) : ℝ))
          (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ)))
        have h2 : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = 1 / ((m + 1 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        linarith
      have hge_diff : 1 / ((m + 1 : ℝ) + 1) ≤
          Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ))
          (by positivity : (0 : ℝ) < ((m + 2 : ℕ) : ℝ)))
        rw [Real.log_div (by positivity) (by positivity)] at h1
        have h2 : ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℝ) + 1)) := by
          push_cast; field_simp; ring
        linarith
      have hstep_le : Real.log ((m + 2 : ℕ) : ℝ) ≤
          ∑ j ∈ Finset.range (m + 1), (1 : ℝ) / ((j : ℝ) + 1) + 1 / ((m + 1 : ℝ) + 1) := by
        -- Use `(m+2)/(m+1) ≤ 1 + 1/(m+1)` and `log((m+2)/(m+1))`? Even better:
        -- `Real.log (m + 2) - Real.log (m + 1) ≤ 1 / (m + 1)` gives `log(m+2) ≤ log(m+1) + 1/(m+1)`,
        -- wait: we need `log(m+2) ≤ H_{m+1} + 1/(m+2)`, which holds if we induct on `log(n+1) ≤ H_n`?
        -- Actually `log(n) ≤ ∑_{j=0}^{n-2} 1/(j+1)`! Let's prove that directly!
        have hlo_strong : Real.log ((m + 2 : ℕ) : ℝ) ≤
            ∑ j ∈ Finset.range (m + 1), (1 : ℝ) / ((j : ℝ) + 1) := by
          have hsub : ∀ k : ℕ, 1 ≤ k →
              Real.log (k : ℝ) ≤ ∑ j ∈ Finset.range (k - 1), (1 : ℝ) / ((j : ℝ) + 1) := by
            intro k hk
            induction k with
            | zero => omega
            | succ r ihr =>
              rcases r with _ | r
              · simp
              · have hr := ihr (by omega)
                simp only [Nat.add_sub_cancel] at hr ⊢
                rw [Finset.sum_range_succ]
                have hd : Real.log ((r + 2 : ℕ) : ℝ) - Real.log ((r + 1 : ℕ) : ℝ) ≤
                    1 / ((r : ℝ) + 1) := by
                  rw [← Real.log_div (by positivity) (by positivity)]
                  have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < ((r + 2 : ℕ) : ℝ))
                    (by positivity : (0 : ℝ) < ((r + 1 : ℕ) : ℝ)))
                  have h2 : ((r + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ) - 1 = 1 / ((r : ℝ) + 1) := by
                    push_cast; field_simp; ring
                  linarith
                linarith
          simpa using hsub (m + 2) (by omega)
        have hnn : (0 : ℝ) ≤ 1 / ((m + 1 : ℝ) + 1) := by positivity
        linarith
      constructor
      · simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hstep_le
      · have : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) = 1 / ((m + 1 : ℝ) + 1) := by push_cast; rfl
        rw [this]
        linarith

private lemma norm_one_add_mul_exp_neg_re (w : ℂ) :
    ‖1 + w‖ * Real.exp (-w.re) ≤ Real.exp (‖w‖ ^ 2 / 2) := by
  have hsq : ‖1 + w‖ ^ 2 = 1 + 2 * w.re + ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
    ring
  have hexp : ‖1 + w‖ ^ 2 ≤ Real.exp (2 * w.re + ‖w‖ ^ 2) := by
    rw [hsq]
    have := Real.add_one_le_exp (2 * w.re + ‖w‖ ^ 2)
    linarith
  have hsqrt : ‖1 + w‖ ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) := by
    have h1 := Real.sqrt_le_sqrt hexp
    rw [Real.sqrt_sq (norm_nonneg _)] at h1
    refine h1.trans_eq ?_
    rw [← Real.exp_half]
    congr 1; ring
  calc ‖1 + w‖ * Real.exp (-w.re)
      ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) * Real.exp (-w.re) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le
    _ = Real.exp (‖w‖ ^ 2 / 2) := by rw [← Real.exp_add]; congr 1; ring

private lemma finset_prod_le_prod {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine mul_le_mul
      (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))

private lemma sum_inv_sq_Ico_le (N n : ℕ) (hN : 1 ≤ N) (hNn : N ≤ n) :
    ∑ j ∈ Finset.Ico N n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) := by
  have hterm : ∀ j ∈ Finset.Ico N n,
      (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) := by
    intro j hj
    have hj1 : 1 ≤ j := le_trans hN (Finset.mem_Ico.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
    have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [div_sub_div _ _ hjpos.ne' hj1pos.ne', one_mul, mul_one, add_sub_cancel_left]
    exact one_div_le_one_div_of_le (mul_pos hjpos hj1pos) (by nlinarith)
  have htel : ∀ m : ℕ, N ≤ m →
      ∑ j ∈ Finset.Ico N m, ((1 : ℝ) / (j : ℝ) - 1 / ((j : ℝ) + 1)) =
        1 / (N : ℝ) - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
      have : N = 0 := by omega
      omega
    | succ k ih =>
      by_cases hNk : N ≤ k
      · rw [Finset.sum_Ico_succ_top hNk, ih hNk]
        push_cast; ring
      · have hNeq : N = k + 1 := by omega
        subst hNeq; simp
  calc ∑ j ∈ Finset.Ico N n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2
      ≤ ∑ j ∈ Finset.Ico N n, (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) := Finset.sum_le_sum hterm
    _ = 1 / (N : ℝ) - 1 / (n : ℝ) := htel n hNn
    _ ≤ 1 / (N : ℝ) := by
        have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
        linarith

private lemma one_le_two_mul_log_two : (1 : ℝ) ≤ 2 * Real.log 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [one_div, Real.log_inv] at h1
  linarith

private lemma exp_one_le_four : Real.exp 1 ≤ 4 := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [this, Real.log_pow]; norm_num
    linarith [one_le_two_mul_log_two]
  calc Real.exp 1 ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hlog4
    _ = 4 := Real.exp_log (by norm_num)

/-- Explicit global growth bound for `s ↦ (Complex.Gamma s)⁻¹` on all of `ℂ`. -/
lemma norm_one_div_Gamma_le (s : ℂ) :
    ‖(Complex.Gamma s)⁻¹‖ ≤ Real.exp (8 * (‖s‖ + 1) * Real.log (2 + ‖s‖)) := by
  by_cases hG0 : Complex.Gamma s = 0
  · simp [hG0, (Real.exp_pos _).le]
  have hs0 : s ≠ 0 := by
    intro h; subst h; exact hG0 Complex.Gamma_zero
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log (2 + ‖s‖) := by
    have hle : Real.log 2 ≤ Real.log (2 + ‖s‖) :=
      Real.log_le_log (by norm_num) (by linarith [norm_nonneg s])
    linarith [one_le_two_mul_log_two]
  have hlog_pos : 0 < Real.log (2 + ‖s‖) := by linarith
  have htend : Filter.Tendsto (fun n : ℕ => ‖(Complex.GammaSeq s n)⁻¹‖)
      Filter.atTop (nhds ‖(Complex.Gamma s)⁻¹‖) :=
    ((Complex.GammaSeq_tendsto_Gamma s).inv₀ hG0).norm
  let N : ℕ := ⌊‖s‖⌋₊ + 1
  have hN1 : 1 ≤ N := by omega
  have hs_lt_N : ‖s‖ < (N : ℝ) := by
    dsimp [N]; push_cast; exact Nat.lt_floor_add_one ‖s‖
  have hN_le : (N : ℝ) ≤ ‖s‖ + 1 := by
    dsimp [N]; push_cast; linarith [Nat.floor_le (norm_nonneg s)]
  refine le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩)
  have hn1 : 1 ≤ n := by omega
  have hNn : N ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hGseq_inv : (Complex.GammaSeq s n)⁻¹ =
      s * ((n : ℂ) ^ s)⁻¹ * ∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1)) := by
    rw [Complex.GammaSeq, inv_div]
    have hprod_split : ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)) =
        s * ∏ j ∈ Finset.range n, (s + ((j : ℂ) + 1)) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, add_zero, mul_comm s]
      congr 1
      refine Finset.prod_congr rfl fun j _ => by push_cast; ring
    have hfact_prod : ((n.factorial : ℕ) : ℂ) = ∏ j ∈ Finset.range n, ((j : ℂ) + 1) := by
      rw [← Finset.prod_range_add_one_eq_factorial n]
      push_cast; rfl
    have hdiv_prod : (∏ j ∈ Finset.range n, (s + ((j : ℂ) + 1))) /
        (∏ j ∈ Finset.range n, ((j : ℂ) + 1)) =
        ∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1)) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hjne : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
      field_simp [hjne]; ring
    rw [hprod_split, hfact_prod]
    calc (s * ∏ j ∈ Finset.range n, (s + (↑j + 1))) / ((n : ℂ) ^ s * ∏ j ∈ Finset.range n, (↑j + 1))
        = s * ((n : ℂ) ^ s)⁻¹ *
            ((∏ j ∈ Finset.range n, (s + (↑j + 1))) / (∏ j ∈ Finset.range n, (↑j + 1))) := by
          rw [div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = s * ((n : ℂ) ^ s)⁻¹ * ∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1)) := by
          rw [hdiv_prod]
  rw [hGseq_inv, norm_mul, norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n),
    norm_prod]
  have hnpow : ((n : ℝ) ^ s.re)⁻¹ = Real.exp (-s.re * Real.log (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hn_pos, ← Real.exp_neg]; congr 1; ring
  rw [hnpow]
  let H : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, (1 : ℝ) / ((j : ℝ) + 1)
  have hexp_H : Real.exp (s.re * H n) * Real.exp (-s.re * H n) = 1 := by
    rw [← Real.exp_add]; simp
  have hprod_exp : Real.exp (-s.re * H n) =
      ∏ j ∈ Finset.range n, Real.exp (-s.re / ((j : ℝ) + 1)) := by
    rw [← Real.exp_sum]
    congr 1
    dsimp [H]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hreorg : ‖s‖ * Real.exp (-s.re * Real.log (n : ℝ)) *
      ∏ j ∈ Finset.range n, ‖1 + s / ((j : ℂ) + 1)‖ =
      ‖s‖ * Real.exp (s.re * (H n - Real.log (n : ℝ))) *
      ∏ j ∈ Finset.range n, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1))) := by
    rw [Finset.prod_mul_distrib, ← hprod_exp]
    have : Real.exp (-s.re * Real.log (n : ℝ)) =
        Real.exp (s.re * (H n - Real.log (n : ℝ))) * Real.exp (-s.re * H n) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [hreorg]
  -- Split the product at `N ≤ n`.
  have hsplit_prod : ∏ j ∈ Finset.range n, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1))) =
      (∏ j ∈ Finset.range N, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1)))) *
      (∏ j ∈ Finset.Ico N n, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1)))) := by
    have hunion : Finset.range n = Finset.range N ∪ Finset.Ico N n := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range N) (Finset.Ico N n) := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      simp only [Finset.mem_range] at hj1
      simp only [Finset.mem_Ico] at hj2; omega
    rw [hunion, Finset.prod_union hdisj]
  rw [hsplit_prod]
  -- Bound 1: `‖s‖ ≤ Real.exp (Real.log (2 + ‖s‖))`.
  have hb1 : ‖s‖ ≤ Real.exp (Real.log (2 + ‖s‖)) := by
    rw [Real.exp_log (by linarith [norm_nonneg s])]; linarith
  -- Bound 2: `Real.exp (s.re * (H n - Real.log n)) ≤ Real.exp ‖s‖`.
  have hb2 : Real.exp (s.re * (H n - Real.log (n : ℝ))) ≤ Real.exp ‖s‖ := by
    refine Real.exp_le_exp.mpr ?_
    obtain ⟨hlo, hhi⟩ := harmonic_bounds hn1
    have habs : |H n - Real.log (n : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc s.re * (H n - Real.log (n : ℝ))
        ≤ |s.re * (H n - Real.log (n : ℝ))| := le_abs_self _
      _ = |s.re| * |H n - Real.log (n : ℝ)| := abs_mul _ _
      _ ≤ ‖s‖ * 1 := mul_le_mul (Complex.abs_re_le_norm s) habs (abs_nonneg _) (norm_nonneg s)
      _ = ‖s‖ := mul_one _
  -- Bound 3: Head product `j ∈ Finset.range N`.
  have hb3 : ∏ j ∈ Finset.range N, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1))) ≤
      Real.exp ((N : ℝ) * Real.log (2 + ‖s‖) + ‖s‖ * (Real.log (N : ℝ) + 1)) := by
    have hhead : ∏ j ∈ Finset.range N, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1))) ≤
        ∏ j ∈ Finset.range N, ((2 + ‖s‖) * Real.exp (‖s‖ / ((j : ℝ) + 1))) := by
      refine finset_prod_le_prod (fun j _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
        fun j _ => mul_le_mul ?_ ?_ (Real.exp_pos _).le (by linarith [norm_nonneg s])
      · calc ‖1 + s / ((j : ℂ) + 1)‖
            ≤ ‖(1 : ℂ)‖ + ‖s / ((j : ℂ) + 1)‖ := norm_add_le _ _
          _ = 1 + ‖s‖ / ((j : ℝ) + 1) := by
              rw [norm_one, norm_div]
              congr 1
              have : ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
              rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          _ ≤ 1 + ‖s‖ / 1 := by
              gcongr; linarith [Nat.cast_nonneg (α := ℝ) j]
          _ ≤ 2 + ‖s‖ := by linarith
      · refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (by positivity))
        calc -s.re ≤ |s.re| := neg_le_abs _
          _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    refine hhead.trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Real.exp_sum]
    have hpow_exp : (2 + ‖s‖) ^ N = Real.exp ((N : ℝ) * Real.log (2 + ‖s‖)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith [norm_nonneg s])]; ring_nf
    rw [hpow_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsum_eq : ∑ j ∈ Finset.range N, ‖s‖ / ((j : ℝ) + 1) = ‖s‖ * H N := by
      dsimp [H]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsum_eq]
    have hHN := (harmonic_bounds hN1).2
    nlinarith [norm_nonneg s]
  -- Bound 4: Tail product `j ∈ Finset.Ico N n`.
  have hb4 : ∏ j ∈ Finset.Ico N n, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1))) ≤
      Real.exp (‖s‖ / 2) := by
    have htail : ∏ j ∈ Finset.Ico N n, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1))) ≤
        ∏ j ∈ Finset.Ico N n, Real.exp ((‖s‖ ^ 2 / 2) * (1 / ((j : ℝ) + 1) ^ 2)) := by
      refine finset_prod_le_prod (fun j _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
        fun j _ => ?_
      have hw := norm_one_add_mul_exp_neg_re (s / ((j : ℂ) + 1))
      have hre : (s / ((j : ℂ) + 1)).re = s.re / ((j : ℝ) + 1) := by
        have : ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.div_ofReal_re]
      have hnorm : ‖s / ((j : ℂ) + 1)‖ = ‖s‖ / ((j : ℝ) + 1) := by
        rw [norm_div]
        have : ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hre, hnorm, div_pow, ← neg_div] at hw
      refine hw.trans_eq ?_
      congr 1; ring
    refine htail.trans ?_
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.mpr ?_
    rw [← Finset.mul_sum]
    have hinv := sum_inv_sq_Ico_le N n hN1 hNn
    calc (‖s‖ ^ 2 / 2) * ∑ j ∈ Finset.Ico N n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2
        ≤ (‖s‖ ^ 2 / 2) * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (‖s‖ / (N : ℝ)) * (‖s‖ / 2) := by ring
      _ ≤ 1 * (‖s‖ / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one (Nat.cast_pos.mpr (by omega))]; exact hs_lt_N.le
      _ = ‖s‖ / 2 := one_mul _
  -- Combine all 4 bounds!
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 + ‖s‖) :=
    Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by linarith)
  calc ‖s‖ * Real.exp (s.re * (H n - Real.log (n : ℝ))) *
        ((∏ j ∈ Finset.range N, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1)))) *
         (∏ j ∈ Finset.Ico N n, (‖1 + s / ((j : ℂ) + 1)‖ * Real.exp (-s.re / ((j : ℝ) + 1)))))
      ≤ Real.exp (Real.log (2 + ‖s‖)) * Real.exp ‖s‖ *
        (Real.exp ((N : ℝ) * Real.log (2 + ‖s‖) + ‖s‖ * (Real.log (N : ℝ) + 1)) *
         Real.exp (‖s‖ / 2)) := by
        refine mul_le_mul
          (mul_le_mul hb1 hb2 (Real.exp_pos _).le (Real.exp_pos _).le)
          (mul_le_mul hb3 hb4 (Finset.prod_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
            (Real.exp_pos _).le)
          (mul_nonneg (Finset.prod_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
            (Finset.prod_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le))
          (by positivity)
    _ = Real.exp (Real.log (2 + ‖s‖) + ‖s‖ + ((N : ℝ) * Real.log (2 + ‖s‖) +
          ‖s‖ * (Real.log (N : ℝ) + 1)) + ‖s‖ / 2) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (8 * (‖s‖ + 1) * Real.log (2 + ‖s‖)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (N : ℝ) * Real.log (2 + ‖s‖) ≤ (‖s‖ + 1) * Real.log (2 + ‖s‖) :=
          mul_le_mul_of_nonneg_right hN_le hlog_pos.le
        have h2 : ‖s‖ * Real.log (N : ℝ) ≤ ‖s‖ * Real.log (2 + ‖s‖) :=
          mul_le_mul_of_nonneg_left hlogN (norm_nonneg s)
        have h3 : (5 / 2 : ℝ) * ‖s‖ ≤ 5 * ‖s‖ * Real.log (2 + ‖s‖) := by
          nlinarith [norm_nonneg s]
        nlinarith

/-- Entire super-exponential growth bound for `recipGamma α`:
`‖(Γ(1 + α + z))⁻¹‖ ≤ exp (C * (‖z‖ + 1) * log (2 + ‖z‖))`. -/
theorem recipGamma_entire_growth (α : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖recipGamma α z‖ ≤ Real.exp (C * (‖z‖ + 1) * Real.log (2 + ‖z‖)) := by
  let M : ℝ := 2 + ‖α‖
  have hM2 : 2 ≤ M := by dsimp [M]; linarith [norm_nonneg α]
  have hMpos : 0 < M := by linarith
  let C : ℝ := 8 * M * (1 + Real.log M / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
    positivity
  refine ⟨C, hCpos, fun z => ?_⟩
  refine (norm_one_div_Gamma_le (1 + α + z)).trans (Real.exp_le_exp.mpr ?_)
  have hnorm_le : ‖1 + α + z‖ ≤ 1 + ‖α‖ + ‖z‖ := by
    calc ‖1 + α + z‖ ≤ ‖1 + α‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + ‖α‖ + ‖z‖ := by linarith [norm_add_le (1 : ℂ) α]
      _ = 1 + ‖α‖ + ‖z‖ := by rw [norm_one]
  have h1 : ‖1 + α + z‖ + 1 ≤ M * (‖z‖ + 1) := by
    dsimp [M]; nlinarith [norm_nonneg α, norm_nonneg z]
  have h2 : 2 + ‖1 + α + z‖ ≤ M * (2 + ‖z‖) := by
    dsimp [M]; nlinarith [norm_nonneg α, norm_nonneg z]
  have hlog_z : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have hlog_le : Real.log (2 + ‖1 + α + z‖) ≤ (1 + Real.log M / Real.log 2) * Real.log (2 + ‖z‖) := by
    calc Real.log (2 + ‖1 + α + z‖)
        ≤ Real.log (M * (2 + ‖z‖)) := Real.log_le_log (by positivity) h2
      _ = Real.log M + Real.log (2 + ‖z‖) := Real.log_mul hMpos.ne' (by positivity)
      _ ≤ (Real.log M / Real.log 2) * Real.log (2 + ‖z‖) + Real.log (2 + ‖z‖) := by
          gcongr
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
          exact mul_le_mul_of_nonneg_left hlog_z (Real.log_nonneg (by linarith))
      _ = (1 + Real.log M / Real.log 2) * Real.log (2 + ‖z‖) := by ring
  calc 8 * (‖1 + α + z‖ + 1) * Real.log (2 + ‖1 + α + z‖)
      ≤ 8 * (M * (‖z‖ + 1)) * ((1 + Real.log M / Real.log 2) * Real.log (2 + ‖z‖)) := by
        have hnn1 : 0 ≤ Real.log (2 + ‖1 + α + z‖) := Real.log_nonneg (by linarith [norm_nonneg (1 + α + z)])
        have hnn2 : 0 ≤ 8 * (M * (‖z‖ + 1)) := by positivity
        exact mul_le_mul (by linarith) hlog_le hnn1 hnn2
    _ = C * (‖z‖ + 1) * Real.log (2 + ‖z‖) := by dsimp [C]; ring

/-! ### Pochhammer bounds for `Γ(n + β + 1) / Γ(β + 1)` -/

lemma Gamma_nat_add_div_Gamma (β : ℂ) (hβ : -1 < β.re) (n : ℕ) :
    Complex.Gamma ((n : ℂ) + β + 1) / Complex.Gamma (β + 1) =
      ∏ j ∈ Finset.range n, (β + 1 + (j : ℂ)) := by
  have hGne : Complex.Gamma (β + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  induction n with
  | zero => simp [div_self hGne]
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih]
    have hne : ((m : ℂ) + β + 1) ≠ 0 := by
      intro h0
      have hre := congr_arg Complex.re h0
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hstep : Complex.Gamma (((m + 1 : ℕ) : ℂ) + β + 1) =
        ((m : ℂ) + β + 1) * Complex.Gamma ((m : ℂ) + β + 1) := by
      have : (((m + 1 : ℕ) : ℂ) + β + 1) = ((m : ℂ) + β + 1) + 1 := by push_cast; ring
      rw [this, Complex.Gamma_add_one _ hne]
    rw [hstep]
    field_simp [hGne]; ring

private lemma norm_pochhammer_le_factorial (β : ℂ) (n : ℕ) :
    ‖∏ j ∈ Finset.range n, (β + 1 + (j : ℂ))‖ ≤ (1 + ‖β‖) ^ n * (n.factorial : ℝ) := by
  rw [norm_prod, ← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod]
  have hpow : (1 + ‖β‖) ^ n = ∏ _j ∈ Finset.range n, (1 + ‖β‖) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hpow, ← Finset.prod_mul_distrib]
  refine finset_prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
  calc ‖β + 1 + (j : ℂ)‖
      = ‖β + ((j + 1 : ℕ) : ℂ)‖ := by push_cast; ring_nf
    _ ≤ ‖β‖ + ‖((j + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
    _ = ‖β‖ + ((j + 1 : ℕ) : ℝ) := by rw [Complex.norm_natCast]
    _ ≤ (1 + ‖β‖) * ((j + 1 : ℕ) : ℝ) := by
        have hj1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
        nlinarith [norm_nonneg β]

private lemma norm_pochhammer_ge_factorial {β : ℂ} (hβ : -1 < β.re) {n : ℕ} (hn : 1 ≤ n) :
    ((β.re + 1) / (n : ℝ)) * (n.factorial : ℝ) ≤ ‖∏ j ∈ Finset.range n, (β + 1 + (j : ℂ))‖ := by
  rw [norm_prod]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Finset.prod_range_succ']
  have h0 : β.re + 1 ≤ ‖β + 1 + ((0 : ℕ) : ℂ)‖ := by
    calc β.re + 1 = (β + 1 + ((0 : ℕ) : ℂ)).re := by simp
      _ ≤ ‖β + 1 + ((0 : ℕ) : ℂ)‖ := Complex.re_le_norm _
  have hrest : (m.factorial : ℝ) ≤ ∏ j ∈ Finset.range m, ‖β + 1 + ((j + 1 : ℕ) : ℂ)‖ := by
    rw [← Finset.prod_range_add_one_eq_factorial m, Nat.cast_prod]
    refine finset_prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
    calc ((j + 1 : ℕ) : ℝ)
        ≤ (β.re + 1) + ((j + 1 : ℕ) : ℝ) := by linarith
      _ = (β + 1 + ((j + 1 : ℕ) : ℂ)).re := by simp [add_assoc]
      _ ≤ ‖β + 1 + ((j + 1 : ℕ) : ℂ)‖ := Complex.re_le_norm _
  have hfact : ((β.re + 1) / ((m + 1 : ℕ) : ℝ)) * (((m + 1).factorial : ℕ) : ℝ) =
      (m.factorial : ℝ) * (β.re + 1) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hm1]
  rw [hfact]
  exact mul_le_mul hrest h0 (by linarith) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-! ### Sub-Gevrey bound for `volterraAsympSeries β α` -/

private lemma pow_le_exp_mul_factorial (n : ℕ) :
    (n : ℝ) ^ n ≤ (Real.exp 1) ^ n * (n.factorial : ℝ) := by
  have hsum : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n : ℝ) := by
    have h1 := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n) (n + 1)
    have h2 : (n : ℝ) ^ n / (n.factorial : ℝ) ≤
        ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k.factorial : ℝ) :=
      Finset.single_le_sum (f := fun k => (n : ℝ) ^ k / (k.factorial : ℝ))
        (fun k _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact h2.trans h1
  rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))] at hsum
  refine hsum.trans_eq ?_
  rw [← Real.exp_nat_mul, mul_one]

/-- **Unconditional Sub-Gevrey Theorem for `volterraAsympSeries β α`:**
For every `α : ℂ` and `β : ℂ` with `-1 < β.re`, the formal Volterra asymptotic series is
sub-Gevrey (`∀ s > 0, IsGevrey s (volterraAsympSeries β α)`). -/
theorem volterraAsympSeries_isSubGevrey (α β : ℂ) (hβ : -1 < β.re) :
    IsSubGevrey (volterraAsympSeries β α) := by
  obtain ⟨K, hKpos, hgrowth⟩ := recipGamma_entire_growth α
  intro s hs
  let A₀ : ℝ := (1 + ‖β‖) * Real.exp (3 * K) * ((2 : ℝ) ^ s / s) * Real.exp s
  have hA₀_pos : 0 < A₀ := by positivity
  let A : ℝ := max 1 A₀
  have hApos : 0 < A := lt_of_lt_of_le one_pos (le_max_left 1 A₀)
  have hA1 : 1 ≤ A := le_max_left 1 A₀
  let C : ℝ := max 1 (max ‖volterraCoeff β α 0‖ ‖volterraCoeff β α 1‖)
  have hCnn : 0 ≤ C := by positivity
  refine ⟨C, A, hCnn, hApos, fun n => ?_⟩
  rw [volterraAsympSeries, PowerSeries.coeff_mk]
  by_cases hn2 : n < 2
  · have hleC : ‖volterraCoeff β α n‖ ≤ C := by
      interval_cases n
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    have h1 : (1 : ℝ) ≤ A ^ n * (n.factorial : ℝ) ^ s := by
      have ha : (1 : ℝ) ≤ A ^ n := one_le_pow₀ hA1
      have hf : (1 : ℝ) ≤ (n.factorial : ℝ) ^ s :=
        Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.factorial_pos n)) hs.le
      nlinarith
    calc ‖volterraCoeff β α n‖ ≤ C := hleC
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (A ^ n * (n.factorial : ℝ) ^ s) := mul_le_mul_of_nonneg_left h1 hCnn
      _ = C * A ^ n * (n.factorial : ℝ) ^ s := by ring
  · push Not at hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog_ge1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
      have h4 : Real.exp 1 ≤ (n : ℝ) + 2 := by
        have h1 : Real.exp 1 ≤ 4 := exp_one_le_four
        have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) h4
    let R : ℝ := (n : ℝ) / Real.log ((n : ℝ) + 2)
    have hRpos : 0 < R := div_pos hn_pos (by linarith)
    have hR_le_n : R ≤ (n : ℝ) := div_le_self hn_pos.le hlog_ge1
    -- Cauchy bound on `Metric.sphere 0 R`:
    have hcauchy : ‖iteratedDeriv n (recipGamma α) 0‖ ≤
        (n.factorial : ℝ) * Real.exp (3 * K * (n : ℝ)) / R ^ n := by
      refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hRpos
        (differentiable_recipGamma α).diffContOnCl fun z hz => ?_
      have hzn : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      refine (hgrowth z).trans (Real.exp_le_exp.mpr ?_)
      rw [hzn]
      have hlogR : Real.log (2 + R) ≤ Real.log ((n : ℝ) + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hlog_le_n : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 2)
        linarith
      have hRn : (R + 1) * Real.log ((n : ℝ) + 2) ≤ 3 * (n : ℝ) := by
        have hmul : R * Real.log ((n : ℝ) + 2) = (n : ℝ) :=
          div_mul_cancel₀ _ (by linarith)
        have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        nlinarith
      calc K * (R + 1) * Real.log (2 + R)
          ≤ K * (R + 1) * Real.log ((n : ℝ) + 2) := by
            gcongr
        _ = K * ((R + 1) * Real.log ((n : ℝ) + 2)) := by ring
        _ ≤ K * (3 * (n : ℝ)) := mul_le_mul_of_nonneg_left hRn hKpos.le
        _ = 3 * K * (n : ℝ) := by ring
    -- Bound `‖volterraCoeff β α n‖`:
    have hcoeff_bd : ‖volterraCoeff β α n‖ ≤
        ((1 + ‖β‖) * Real.exp (3 * K) * Real.log ((n : ℝ) + 2)) ^ n *
          ((n.factorial : ℝ) / (n : ℝ) ^ n) := by
      rw [volterraCoeff, Gamma_nat_add_div_Gamma β hβ n, norm_mul, norm_div, Complex.norm_natCast]
      have hpoch := norm_pochhammer_le_factorial β n
      have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
      have hdiv_cauchy : ‖iteratedDeriv n (recipGamma α) 0‖ / (n.factorial : ℝ) ≤
          Real.exp (3 * K * (n : ℝ)) / R ^ n := by
        rw [div_le_iff₀ hfact_pos]
        refine hcauchy.trans_eq ?_; ring
      have hmul_le : ‖∏ j ∈ Finset.range n, (β + 1 + (j : ℂ))‖ *
          (‖iteratedDeriv n (recipGamma α) 0‖ / (n.factorial : ℝ)) ≤
          ((1 + ‖β‖) ^ n * (n.factorial : ℝ)) * (Real.exp (3 * K * (n : ℝ)) / R ^ n) :=
        mul_le_mul hpoch hdiv_cauchy (by positivity) (by positivity)
      refine hmul_le.trans_eq ?_
      have hexp_pow : Real.exp (3 * K * (n : ℝ)) = (Real.exp (3 * K)) ^ n := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      dsimp only [R]
      rw [hexp_pow, div_pow, div_div_eq_mul_div, mul_pow, mul_pow]
      ring
    -- Use `n! ≤ n^n` so `n! / n^n ≤ 1`:
    have hfact_le_pow : (n.factorial : ℝ) / (n : ℝ) ^ n ≤ 1 := by
      rw [div_le_one (pow_pos hn_pos n)]
      exact_mod_cast Nat.factorial_le_pow n
    have hlog_bd : (Real.log ((n : ℝ) + 2)) ^ n ≤
        (((2 : ℝ) ^ s / s) * Real.exp s) ^ n * (n.factorial : ℝ) ^ s := by
      have hlog_step : Real.log ((n : ℝ) + 2) ≤ ((2 : ℝ) ^ s / s) * (n : ℝ) ^ s := by
        have h1 : s * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ s) :=
          (Real.log_rpow (by positivity) s).symm
        have h2 : Real.log (((n : ℝ) + 2) ^ s) ≤ ((n : ℝ) + 2) ^ s := by
          have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2) s)
          linarith
        have h3 : ((n : ℝ) + 2) ^ s ≤ (2 : ℝ) ^ s * (n : ℝ) ^ s := by
          rw [← Real.mul_rpow (by positivity) hn_pos.le]
          refine Real.rpow_le_rpow (by positivity) ?_ hs.le
          have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
          linarith
        rw [← mul_div_right_comm, le_div_iff₀' hs]
        linarith
      have hpow_n : (Real.log ((n : ℝ) + 2)) ^ n ≤
          ((2 : ℝ) ^ s / s) ^ n * ((n : ℝ) ^ n) ^ s := by
        calc (Real.log ((n : ℝ) + 2)) ^ n
            ≤ (((2 : ℝ) ^ s / s) * (n : ℝ) ^ s) ^ n :=
              pow_le_pow_left₀ (by linarith) hlog_step n
          _ = ((2 : ℝ) ^ s / s) ^ n * ((n : ℝ) ^ s) ^ n := mul_pow _ _ n
          _ = ((2 : ℝ) ^ s / s) ^ n * ((n : ℝ) ^ n) ^ s := by
              congr 1
              rw [← Real.rpow_natCast ((n : ℝ) ^ s), ← Real.rpow_mul hn_pos.le,
                ← Real.rpow_natCast (n : ℝ), ← Real.rpow_mul hn_pos.le, mul_comm]
      have hstirl : ((n : ℝ) ^ n) ^ s ≤ (Real.exp s) ^ n * (n.factorial : ℝ) ^ s := by
        have hbase := pow_le_exp_mul_factorial n
        calc ((n : ℝ) ^ n) ^ s
            ≤ ((Real.exp 1) ^ n * (n.factorial : ℝ)) ^ s :=
              Real.rpow_le_rpow (by positivity) hbase hs.le
          _ = ((Real.exp 1) ^ n) ^ s * (n.factorial : ℝ) ^ s :=
              Real.mul_rpow (by positivity) (Nat.cast_nonneg _)
          _ = (Real.exp s) ^ n * (n.factorial : ℝ) ^ s := by
              congr 1
              rw [← Real.exp_nat_mul, mul_one, ← Real.exp_mul, ← Real.exp_nat_mul]
      calc (Real.log ((n : ℝ) + 2)) ^ n
          ≤ ((2 : ℝ) ^ s / s) ^ n * ((n : ℝ) ^ n) ^ s := hpow_n
        _ ≤ ((2 : ℝ) ^ s / s) ^ n * ((Real.exp s) ^ n * (n.factorial : ℝ) ^ s) :=
            mul_le_mul_of_nonneg_left hstirl (by positivity)
        _ = (((2 : ℝ) ^ s / s) * Real.exp s) ^ n * (n.factorial : ℝ) ^ s := by
            rw [mul_pow]; ring
    calc ‖volterraCoeff β α n‖
        ≤ ((1 + ‖β‖) * Real.exp (3 * K) * Real.log ((n : ℝ) + 2)) ^ n * 1 :=
          hcoeff_bd.trans (mul_le_mul_of_nonneg_left hfact_le_pow (by positivity))
      _ = ((1 + ‖β‖) * Real.exp (3 * K)) ^ n * (Real.log ((n : ℝ) + 2)) ^ n := by
          rw [mul_one, mul_pow]
      _ ≤ ((1 + ‖β‖) * Real.exp (3 * K)) ^ n *
            ((((2 : ℝ) ^ s / s) * Real.exp s) ^ n * (n.factorial : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_left hlog_bd (by positivity)
      _ = 1 * A₀ ^ n * (n.factorial : ℝ) ^ s := by
          dsimp only [A₀]; rw [one_mul, ← mul_assoc, ← mul_pow]; congr 2; ring
      _ ≤ C * A ^ n * (n.factorial : ℝ) ^ s := by
          gcongr
          · exact le_max_left 1 _
          · exact le_max_right 1 A₀

/-! ### Divergence of `volterraAsympSeries β α` -/

private lemma entire_taylor_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n : ℕ => (iteratedDeriv n f 0 / (n.factorial : ℂ)) * z ^ n) (f z) := by
  have hp := hf.hasFPowerSeriesOnBall (0 : ℂ) (R := 1) one_pos
  have hmem : z ∈ Metric.eball (0 : ℂ) ⊤ := by simp
  have hsum := hp.hasSum hmem
  rw [zero_add] at hsum
  refine hsum.congr_fun fun n => ?_
  have hfs := hp.factorial_smul z n
  have hmult : (iteratedFDeriv ℂ n f 0) (fun _ : Fin n => z) = z ^ n * iteratedDeriv n f 0 := by
    have hfun : (fun _ : Fin n => z) = fun _ : Fin n => z • (1 : ℂ) := by
      ext _; simp
    rw [hfun, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← iteratedDeriv_eq_iteratedFDeriv]
    rfl
  rw [hmult, nsmul_eq_mul] at hfs
  have hfact_ne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  calc (iteratedDeriv n f 0 / (n.factorial : ℂ)) * z ^ n
      = (z ^ n * iteratedDeriv n f 0) / (n.factorial : ℂ) := by ring
    _ = ((n.factorial : ℂ) * (cauchyPowerSeries f 0 (1 : NNReal) n) (fun _ => z)) /
          (n.factorial : ℂ) := by rw [← hfs]
    _ = (cauchyPowerSeries f 0 (1 : NNReal) n) (fun _ => z) := by field_simp [hfact_ne]

/-- **Unconditional Divergence Theorem for `volterraAsympSeries β α`:**
For every `α : ℂ` and `β : ℂ` with `-1 < β.re`, the formal Volterra asymptotic series has
zero radius of convergence (`¬ IsConvergentPS (volterraAsympSeries β α)`). -/
theorem volterraAsympSeries_not_convergent (α β : ℂ) (hβ : -1 < β.re) :
    ¬ IsConvergentPS (volterraAsympSeries β α) := by
  rintro ⟨C, R, hC, hR, hbd⟩
  have hβ1 : 0 < β.re + 1 := by linarith
  let c : ℕ → ℂ := fun n => iteratedDeriv n (recipGamma α) 0 / (n.factorial : ℂ)
  let C₁ : ℝ := max (C / (β.re + 1)) ‖c 0‖
  have hC₁_nn : 0 ≤ C₁ := le_trans (norm_nonneg _) (le_max_right _ _)
  have hc_bd : ∀ n : ℕ, ‖c n‖ ≤ C₁ * (2 * R) ^ n / (n.factorial : ℝ) := by
    intro n
    rcases n with _ | m
    · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      exact le_max_right _ _
    · have hbn := hbd (m + 1)
      rw [volterraAsympSeries, PowerSeries.coeff_mk, volterraCoeff,
        Gamma_nat_add_div_Gamma β hβ (m + 1), norm_mul] at hbn
      have hpoch_ge := norm_pochhammer_ge_factorial hβ (Nat.succ_pos m)
      have hmul_le : ((β.re + 1) / ((m + 1 : ℕ) : ℝ) * (((m + 1).factorial : ℕ) : ℝ)) * ‖c (m + 1)‖ ≤
          C * R ^ (m + 1) :=
        (mul_le_mul_of_nonneg_right hpoch_ge (norm_nonneg _)).trans hbn
      have hpos_m : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos m)
      have hpos_f : (0 : ℝ) < (((m + 1).factorial : ℕ) : ℝ) :=
        Nat.cast_pos.mpr (Nat.factorial_pos (m + 1))
      have hden_pos : 0 < (β.re + 1) / ((m + 1 : ℕ) : ℝ) * (((m + 1).factorial : ℕ) : ℝ) :=
        by positivity
      have hstep : ‖c (m + 1)‖ ≤ (C / (β.re + 1)) * (((m + 1 : ℕ) : ℝ) * R ^ (m + 1)) /
          (((m + 1).factorial : ℕ) : ℝ) := by
        rw [le_div_iff₀ hpos_f]
        have h1 : (β.re + 1) * (((m + 1).factorial : ℕ) : ℝ) * ‖c (m + 1)‖ ≤
            ((m + 1 : ℕ) : ℝ) * (C * R ^ (m + 1)) := by
          have := (mul_le_mul_of_nonneg_left hmul_le hpos_m.le)
          have hsimp : ((m + 1 : ℕ) : ℝ) * ((β.re + 1) / ((m + 1 : ℕ) : ℝ) *
              (((m + 1).factorial : ℕ) : ℝ) * ‖c (m + 1)‖) =
              (β.re + 1) * (((m + 1).factorial : ℕ) : ℝ) * ‖c (m + 1)‖ := by
            field_simp [hpos_m.ne']
          linarith
        have h2 := (div_le_div_of_nonneg_right h1 hβ1.le)
        have h3 : (β.re + 1) * (((m + 1).factorial : ℕ) : ℝ) * ‖c (m + 1)‖ / (β.re + 1) =
            ‖c (m + 1)‖ * (((m + 1).factorial : ℕ) : ℝ) := by
          field_simp [hβ1.ne']
        rw [h3] at h2
        refine h2.trans_eq ?_; ring
      have hm_pow : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
        exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := m + 1))
      calc ‖c (m + 1)‖
          ≤ (C / (β.re + 1)) * (((m + 1 : ℕ) : ℝ) * R ^ (m + 1)) / (((m + 1).factorial : ℕ) : ℝ) :=
            hstep
        _ ≤ C₁ * ((2 : ℝ) ^ (m + 1) * R ^ (m + 1)) / (((m + 1).factorial : ℕ) : ℝ) := by
            gcongr
            exact le_max_left _ _
        _ = C₁ * (2 * R) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℝ) := by
            rw [mul_pow]
  -- Deduce exponential type `‖recipGamma α z‖ ≤ C₁ * exp (2 * R * ‖z‖)` for all `z : ℂ`:
  have hexp_type : ∀ z : ℂ, ‖recipGamma α z‖ ≤ C₁ * Real.exp (2 * R * ‖z‖) := by
    intro z
    have hsum := entire_taylor_hasSum (differentiable_recipGamma α) z
    have hexp_sum : HasSum (fun n : ℕ => C₁ * ((2 * R * ‖z‖) ^ n / (n.factorial : ℝ)))
        (C₁ * Real.exp (2 * R * ‖z‖)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp (2 * R * ‖z‖)).mul_left C₁
    have hle_term : ∀ n : ℕ, ‖c n * z ^ n‖ ≤ C₁ * ((2 * R * ‖z‖) ^ n / (n.factorial : ℝ)) := by
      intro n
      rw [norm_mul, norm_pow]
      calc ‖c n‖ * ‖z‖ ^ n
          ≤ (C₁ * (2 * R) ^ n / (n.factorial : ℝ)) * ‖z‖ ^ n :=
            mul_le_mul_of_nonneg_right (hc_bd n) (pow_nonneg (norm_nonneg z) n)
        _ = C₁ * ((2 * R * ‖z‖) ^ n / (n.factorial : ℝ)) := by rw [mul_pow]; ring
    have hnorm_sum : Summable (fun n : ℕ => ‖c n * z ^ n‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle_term hexp_sum.summable
    calc ‖recipGamma α z‖
        = ‖∑' n : ℕ, c n * z ^ n‖ := by rw [hsum.tsum_eq]
      _ ≤ ∑' n : ℕ, ‖c n * z ^ n‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' n : ℕ, C₁ * ((2 * R * ‖z‖) ^ n / (n.factorial : ℝ)) :=
          Summable.tsum_le_tsum hle_term hnorm_sum hexp_sum.summable
      _ = C₁ * Real.exp (2 * R * ‖z‖) := hexp_sum.tsum_eq
  -- Contradiction along negative half-integers `z_m = -m - 3/2 - α` via Euler's reflection formula:
  let B : ℝ := Real.exp (2 * R)
  have hBpos : 0 < B := Real.exp_pos _
  let C₂ : ℝ := C₁ * Real.exp (2 * R * (2 + ‖α‖)) * Real.pi
  have hfact_le : ∀ m : ℕ, 1 ≤ m → (m.factorial : ℝ) ≤ C₂ * B ^ m := by
    intro m hm
    let z_m : ℂ := -(m : ℂ) - 3 / 2 - α
    have h1az : 1 + α + z_m = -((m : ℂ) + 1 / 2) := by dsimp [z_m]; ring
    have hrefl := Complex.Gamma_mul_Gamma_one_sub (-((m : ℂ) + 1 / 2))
    have h1sub : (1 : ℂ) - (-((m : ℂ) + 1 / 2)) = (((m : ℝ) + 3 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1sub, Complex.Gamma_ofReal] at hrefl
    have hsin_norm : ‖Complex.sin ((Real.pi : ℂ) * (-((m : ℂ) + 1 / 2)))‖ = 1 := by
      have harg : (Real.pi : ℂ) * (-((m : ℂ) + 1 / 2)) =
          -(((m : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 2)) := by ring
      rw [harg, Complex.sin_neg, norm_neg, Complex.sin_add_pi_div_two]
      have hcos_norm : ∀ k : ℕ, ‖Complex.cos ((k : ℂ) * (Real.pi : ℂ))‖ = 1 := by
        intro k
        induction k with
        | zero => simp
        | succ r ihr =>
          have : (((r + 1 : ℕ) : ℂ) * (Real.pi : ℂ)) = (r : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) := by
            push_cast; ring
          rw [this, Complex.cos_add_pi, norm_neg, ihr]
      exact hcos_norm m
    have hG_ne : Complex.Gamma (-((m : ℂ) + 1 / 2)) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hrefl
      have hpi_ne : ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (-((m : ℂ) + 1 / 2)))) ≠ 0 := by
        apply div_ne_zero
        · exact_mod_cast Real.pi_ne_zero
        · intro hs0; rw [hs0, norm_zero] at hsin_norm; norm_num at hsin_norm
      exact hpi_ne hrefl.symm
    have hrecip_eq : (Complex.Gamma (-((m : ℂ) + 1 / 2)))⁻¹ =
        (Real.Gamma ((m : ℝ) + 3 / 2) : ℂ) *
          Complex.sin ((Real.pi : ℂ) * (-((m : ℂ) + 1 / 2))) / (Real.pi : ℂ) := by
      have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hsin_ne : Complex.sin ((Real.pi : ℂ) * (-((m : ℂ) + 1 / 2))) ≠ 0 := by
        intro hs0; rw [hs0, norm_zero] at hsin_norm; norm_num at hsin_norm
      have hmul := congr_arg (fun w => w * Complex.sin ((Real.pi : ℂ) * (-((m : ℂ) + 1 / 2)))) hrefl
      simp only [div_mul_cancel₀ _ hsin_ne] at hmul
      rw [eq_div_iff hpi_ne, inv_mul_eq_iff_eq_mul₀ hG_ne]
      linear_combination hmul.symm
    have hnorm_rg : ‖recipGamma α z_m‖ = Real.Gamma ((m : ℝ) + 3 / 2) / Real.pi := by
      rw [recipGamma, h1az, hrecip_eq, norm_div, norm_mul, hsin_norm, mul_one,
        Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le,
        Real.norm_of_nonneg Real.pi_pos.le]
    have hG_ge : (m.factorial : ℝ) ≤ Real.Gamma ((m : ℝ) + 3 / 2) := by
      rw [← Real.Gamma_nat_eq_factorial m]
      have hm2 : (2 : ℝ) ≤ (m : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      exact Real.Gamma_strictMonoOn_Ici.monotoneOn
        (Set.mem_Ici.mpr hm2) (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have hzm_norm : ‖z_m‖ ≤ (m : ℝ) + 2 + ‖α‖ := by
      dsimp [z_m]
      calc ‖-(m : ℂ) - 3 / 2 - α‖
          ≤ ‖-(m : ℂ) - 3 / 2‖ + ‖α‖ := norm_sub_le _ _
        _ ≤ ‖-(m : ℂ)‖ + ‖(3 / 2 : ℂ)‖ + ‖α‖ := by linarith [norm_sub_le (-(m : ℂ)) (3 / 2 : ℂ)]
        _ = (m : ℝ) + 3 / 2 + ‖α‖ := by
            rw [norm_neg, Complex.norm_natCast]
            have : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by push_cast; rfl
            rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
        _ ≤ (m : ℝ) + 2 + ‖α‖ := by linarith
    have hup := hexp_type z_m
    rw [hnorm_rg, div_le_iff₀ Real.pi_pos] at hup
    calc (m.factorial : ℝ)
        ≤ Real.Gamma ((m : ℝ) + 3 / 2) := hG_ge
      _ ≤ C₁ * Real.exp (2 * R * ‖z_m‖) * Real.pi := hup
      _ ≤ C₁ * Real.exp (2 * R * ((m : ℝ) + 2 + ‖α‖)) * Real.pi := by
          gcongr
      _ = C₂ * B ^ m := by
          dsimp only [C₂, B]
          rw [← Real.exp_nat_mul]
          have : Real.exp (2 * R * ((m : ℝ) + 2 + ‖α‖)) =
              Real.exp (2 * R * (2 + ‖α‖)) * Real.exp ((m : ℝ) * (2 * R)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]; ring
  -- Contradiction: for `M = ⌈2 * B⌉₊ + 1` and large `k`, `(M + k)! > C₂ * B^(M + k)`!
  let M : ℕ := ⌈2 * B⌉₊ + 1
  have hM1 : 1 ≤ M := by omega
  have h2B_le_M : 2 * B ≤ (M : ℝ) := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (2 * B)]
  have hstep_fac : ∀ k : ℕ, (M : ℝ) ^ k * (M.factorial : ℝ) ≤ ((M + k).factorial : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ r ihr =>
      have hfac_step : ((M + (r + 1)).factorial : ℝ) =
          ((M + r + 1 : ℕ) : ℝ) * ((M + r).factorial : ℝ) := by
        rw [show M + (r + 1) = (M + r) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
      rw [hfac_step, pow_succ]
      have hMr : (M : ℝ) ≤ ((M + r + 1 : ℕ) : ℝ) := by exact_mod_cast (show M ≤ M + r + 1 by omega)
      calc (M : ℝ) ^ r * (M : ℝ) * (M.factorial : ℝ)
          = (M : ℝ) * ((M : ℝ) ^ r * (M.factorial : ℝ)) := by ring
        _ ≤ ((M + r + 1 : ℕ) : ℝ) * ((M + r).factorial : ℝ) :=
            mul_le_mul hMr ihr (by positivity) (by positivity)
  have hC2_nn : 0 ≤ C₂ := by positivity
  let k : ℕ := ⌈C₂ * B ^ M⌉₊ + 1
  have hk_gt : C₂ * B ^ M < (2 : ℝ) ^ k := by
    have h1 : C₂ * B ^ M < (k : ℝ) := by
      dsimp [k]; push_cast; linarith [Nat.le_ceil (C₂ * B ^ M)]
    have h2 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
    linarith
  have hle_Mk := hfact_le (M + k) (by omega)
  have hfac1 : (1 : ℝ) ≤ (M.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos M)
  have hpow_ge : (2 : ℝ) ^ k * B ^ k ≤ (M : ℝ) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2B_le_M k
  have hbig : C₂ * B ^ (M + k) < ((M + k).factorial : ℝ) := by
    calc C₂ * B ^ (M + k)
        = (C₂ * B ^ M) * B ^ k := by rw [pow_add]; ring
      _ < (2 : ℝ) ^ k * B ^ k := mul_lt_mul_of_pos_right hk_gt (pow_pos hBpos k)
      _ ≤ (M : ℝ) ^ k := hpow_ge
      _ = (M : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ (M : ℝ) ^ k * (M.factorial : ℝ) := mul_le_mul_of_nonneg_left hfac1 (by positivity)
      _ ≤ ((M + k).factorial : ℝ) := hstep_fac k
  linarith

/-!
## Section 3: Volterra Functions `μ(t, β, α)` and `ν(t)`, Watson's Endpoint Expansion,
Quantum Gas Virial Differential Transcendence, and the Exact Laplace Identity
-/

/-- The generalized Volterra function `μ(t, β, α)` for `t > 0`, `α : ℂ`, and `-1 < β.re`:
`μ(t, β, α) = Γ(β + 1)⁻¹ * ∫_{0}^∞ t^{v + α} * v^β / Γ(1 + α + v) dv`. -/
@[expose] noncomputable def volterraMu (β α : ℂ) (t : ℝ) : ℂ :=
  (Complex.Gamma (β + 1))⁻¹ *
    ∫ v : ℝ in Set.Ioi (0 : ℝ),
      Complex.exp (((v : ℂ) + α) * (Real.log t : ℂ)) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ)

/-- Volterra's function `ν(t) = μ(t, 0, 0) = ∫_{0}^∞ t^v / Γ(1 + v) dv` for `t > 0`.
This equals the interacting 2D two-component Fermi gas second virial shift `Δb₂^{(2D)}(t)`. -/
@[expose] noncomputable def volterraNu (t : ℝ) : ℂ :=
  ∫ v : ℝ in Set.Ioi (0 : ℝ),
    Complex.exp ((v : ℂ) * (Real.log t : ℂ)) * recipGamma 0 (v : ℂ)

/-- Unnormalized Laplace–Volterra integral `z ↦ ∫_{0}^∞ exp (-v / z) * v^β / Γ(1 + α + v) dv`
on the right half-plane `U = {z : ℂ | 0 < z.re}`. -/
@[expose] noncomputable def volterraInt (β α : ℂ) (z : ℂ) : ℂ :=
  ∫ v : ℝ in Set.Ioi (0 : ℝ),
    Complex.exp (-(v : ℂ) / z) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ)

/-- Normalized Laplace–Volterra function on the right half-plane `U = {z : ℂ | 0 < z.re}`:
`F(β, α)(z) = Γ(β + 1)⁻¹ * z^{-(β + 1)} * ∫_{0}^∞ exp (-v / z) * v^β / Γ(1 + α + v) dv`. -/
@[expose] noncomputable def volterraLaplace (β α : ℂ) (z : ℂ) : ℂ :=
  (Complex.Gamma (β + 1))⁻¹ * (z ^ (-(β + 1))) * volterraInt β α z

/-- The right half-plane `U = {z : ℂ | 0 < z.re}`. -/
@[expose] def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

/-- The complex Euler differential operator `δ_ℂ f(z) = z * deriv f z`. -/
@[expose] noncomputable def eulerOpC (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv f z

/-- The real Euler differential operator `D_ℝ f(t) = t * deriv f t`. -/
@[expose] noncomputable def eulerOpR (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * deriv f t

lemma volterraMu_zero_zero (t : ℝ) : volterraMu 0 0 t = volterraNu t := by
  simp [volterraMu, volterraNu, Complex.Gamma_one]

lemma volterraMu_exp_neg_inv (β α : ℂ) {x : ℝ} (hx : 0 < x) :
    volterraMu β α (Real.exp (-(1 : ℝ) / x)) =
      Complex.exp (-α / (x : ℂ)) * ((x : ℂ) ^ (β + 1)) * volterraLaplace β α (x : ℂ) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [volterraMu, volterraLaplace, volterraInt, Real.log_exp]
  have hint :
      ∫ v : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp (((v : ℂ) + α) * ((-(1 : ℝ) / x : ℝ) : ℂ)) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ) =
      Complex.exp (-α / (x : ℂ)) *
        ∫ v : ℝ in Set.Ioi (0 : ℝ),
          Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    have hexp : Complex.exp (((v : ℂ) + α) * ((-(1 : ℝ) / x : ℝ) : ℂ)) =
        Complex.exp (-α / (x : ℂ)) * Complex.exp (-(v : ℂ) / (x : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]; ring
  rw [hint]
  let I : ℂ := ∫ v : ℝ in Set.Ioi (0 : ℝ),
    Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ)
  change (Complex.Gamma (β + 1))⁻¹ * (Complex.exp (-α / (x : ℂ)) * I) =
    Complex.exp (-α / (x : ℂ)) * ((x : ℂ) ^ (β + 1)) *
      ((Complex.Gamma (β + 1))⁻¹ * ((x : ℂ) ^ (-(β + 1))) * I)
  have hcpow : ((x : ℂ) ^ (β + 1)) * ((x : ℂ) ^ (-(β + 1))) = 1 := by
    rw [← Complex.cpow_add _ _ hxne, add_neg_cancel, Complex.cpow_zero]
  calc (Complex.Gamma (β + 1))⁻¹ * (Complex.exp (-α / (x : ℂ)) * I)
      = Complex.exp (-α / (x : ℂ)) * 1 * ((Complex.Gamma (β + 1))⁻¹ * I) := by ring
    _ = Complex.exp (-α / (x : ℂ)) * (((x : ℂ) ^ (β + 1)) * ((x : ℂ) ^ (-(β + 1)))) *
          ((Complex.Gamma (β + 1))⁻¹ * I) := by rw [hcpow]
    _ = Complex.exp (-α / (x : ℂ)) * ((x : ℂ) ^ (β + 1)) *
          ((Complex.Gamma (β + 1))⁻¹ * ((x : ℂ) ^ (-(β + 1))) * I) := by ring

/-! ### Super-exponential decay of `recipGamma α` on `[0, ∞)` and integrability -/

lemma norm_recipGamma_real_exp_decay (α : ℂ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 0 ≤ v → ‖recipGamma α (v : ℂ)‖ ≤ C * Real.exp (-A * v) := by
  -- Reduce to `A₁ = max 1 A > 0`.
  let A₁ : ℝ := max 1 A
  have hA₁_pos : 0 < A₁ := lt_of_lt_of_le one_pos (le_max_left 1 A)
  have hA_le : A ≤ A₁ := le_max_right 1 A
  let M : ℕ := ⌈max 0 (1 - α.re)⌉₊ + 1
  have hM_re : ∀ u : ℝ, (M : ℝ) ≤ u → (2 : ℝ) ≤ (1 + α + (u : ℂ)).re := by
    intro u hu
    have h1 : 1 - α.re ≤ (M : ℝ) := by
      dsimp [M]; push_cast
      linarith [le_max_right (0 : ℝ) (1 - α.re), Nat.le_ceil (max (0 : ℝ) (1 - α.re))]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hcont : ContinuousOn (fun v : ℝ => ‖recipGamma α (v : ℂ)‖) (Set.Icc 0 ((M : ℝ) + 1)) :=
    ((differentiable_recipGamma α).continuous.comp Complex.continuous_ofReal).norm.continuousOn
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let B : ℝ := max 1 B₀
  have hBpos : 0 < B := lt_of_lt_of_le one_pos (le_max_left 1 B₀)
  have hB_on : ∀ r : ℝ, 0 ≤ r → r ≤ (M : ℝ) + 1 → ‖recipGamma α (r : ℂ)‖ ≤ B := by
    intro r hr0 hr1
    have h1 := hB₀ r ⟨hr0, hr1⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at h1
    exact h1.trans (le_max_right 1 B₀)
  -- For `v ≥ M`, `n = ⌊v⌋₊ - M`, `r = v - n ∈ [M, M + 1]`: `‖recipGamma α v‖ ≤ B / n!`.
  have hfac_decay : ∀ v : ℝ, (M : ℝ) ≤ v →
      ‖recipGamma α (v : ℂ)‖ ≤ B / (((⌊v⌋₊ - M).factorial : ℕ) : ℝ) := by
    intro v hv
    let n : ℕ := ⌊v⌋₊ - M
    have hM_le_fl : M ≤ ⌊v⌋₊ := Nat.le_floor hv
    let r : ℝ := v - (n : ℝ)
    have hr_lo : (M : ℝ) ≤ r := by
      dsimp [r, n]
      have h1 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le (by linarith [Nat.cast_nonneg (α := ℝ) M])
      have h2 : ((⌊v⌋₊ - M : ℕ) : ℝ) = (⌊v⌋₊ : ℝ) - (M : ℝ) := Nat.cast_sub hM_le_fl
      linarith
    have hr_hi : r ≤ (M : ℝ) + 1 := by
      dsimp [r, n]
      have h1 : v < (⌊v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v
      have h2 : ((⌊v⌋₊ - M : ℕ) : ℝ) = (⌊v⌋₊ : ℝ) - (M : ℝ) := Nat.cast_sub hM_le_fl
      linarith
    have hr_nn : 0 ≤ r := le_trans (Nat.cast_nonneg M) hr_lo
    have hv_eq : (v : ℂ) = (r : ℂ) + (n : ℂ) := by
      dsimp [r]; push_cast; ring
    -- Gamma recurrence: `Γ(1 + α + r + n) = (∏_{j < n} (1 + α + r + j)) * Γ(1 + α + r)`.
    have hG_rec : ∀ k : ℕ,
        Complex.Gamma (1 + α + (r : ℂ) + (k : ℂ)) =
          (∏ j ∈ Finset.range k, (1 + α + (r : ℂ) + (j : ℂ))) * Complex.Gamma (1 + α + (r : ℂ)) := by
      intro k
      induction k with
      | zero => simp
      | succ m ihm =>
        rw [Finset.prod_range_succ]
        have hstep : 1 + α + (r : ℂ) + (((m + 1 : ℕ) : ℂ)) = (1 + α + (r : ℂ) + (m : ℂ)) + 1 := by
          push_cast; ring
        have hne : 1 + α + (r : ℂ) + (m : ℂ) ≠ 0 := by
          intro h0
          have hre := congr_arg Complex.re h0
          have := hM_re r hr_lo
          simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.natCast_re,
            Complex.zero_re] at hre this
          have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        rw [hstep, Complex.Gamma_add_one _ hne, ihm]; ring
    have hpoch_ge : (n.factorial : ℝ) ≤ ‖∏ j ∈ Finset.range n, (1 + α + (r : ℂ) + (j : ℂ))‖ := by
      rw [norm_prod, ← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod]
      refine finset_prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
      have hr2 := hM_re r hr_lo
      calc ((j + 1 : ℕ) : ℝ)
          ≤ (1 + α + (r : ℂ) + (j : ℂ)).re := by
            simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.natCast_re] at hr2 ⊢
            push_cast; linarith
        _ ≤ ‖1 + α + (r : ℂ) + (j : ℂ)‖ := Complex.re_le_norm _
    have hGr_ne : Complex.Gamma (1 + α + (r : ℂ)) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by linarith [hM_re r hr_lo])
    have hpoch_ne : ∏ j ∈ Finset.range n, (1 + α + (r : ℂ) + (j : ℂ)) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hpoch_ge
      have : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
      linarith
    have hinv_eq : recipGamma α (v : ℂ) =
        (∏ j ∈ Finset.range n, (1 + α + (r : ℂ) + (j : ℂ)))⁻¹ * recipGamma α (r : ℂ) := by
      rw [recipGamma, recipGamma, hv_eq, ← add_assoc, hG_rec n, mul_inv, mul_comm]
    rw [hinv_eq, norm_mul, norm_inv, inv_mul_eq_div]
    exact div_le_div₀ hBpos.le (hB_on r hr_nn hr_hi)
      (Nat.cast_pos.mpr (Nat.factorial_pos n)) hpoch_ge
  -- Now beat `exp (A₁ * v)` using `1 / n! ≤ K^K * exp (-A₁ * n)` where `K = ⌈exp A₁⌉₊ + 1`!
  let K : ℕ := ⌈Real.exp A₁⌉₊ + 1
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  have hexp_le_K : Real.exp A₁ ≤ (K : ℝ) := by
    dsimp [K]; push_cast; linarith [Nat.le_ceil (Real.exp A₁)]
  have hfac_ge_exp : ∀ n : ℕ, (Real.exp A₁) ^ n ≤ (K : ℝ) ^ K * (n.factorial : ℝ) := by
    intro n
    by_cases hnK : n ≤ K
    · calc (Real.exp A₁) ^ n
          ≤ (K : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hexp_le_K n
        _ ≤ (K : ℝ) ^ K := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ K by omega)) hnK
        _ = (K : ℝ) ^ K * 1 := (mul_one _).symm
        _ ≤ (K : ℝ) ^ K * (n.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.one_le_cast.mpr (Nat.factorial_pos n)) (by positivity)
    · push Not at hnK
      have hstep : ∀ d : ℕ, (K : ℝ) ^ d ≤ ((K + d).factorial : ℝ) := by
        intro d
        induction d with
        | zero => simp [Nat.one_le_cast.mpr (Nat.factorial_pos K)]
        | succ r ihr =>
          have hfs : ((K + (r + 1)).factorial : ℝ) =
              ((K + r + 1 : ℕ) : ℝ) * ((K + r).factorial : ℝ) := by
            rw [show K + (r + 1) = (K + r) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
          rw [hfs, pow_succ]
          have hK_le : (K : ℝ) ≤ ((K + r + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show K ≤ K + r + 1 by omega)
          calc (K : ℝ) ^ r * (K : ℝ)
              = (K : ℝ) * (K : ℝ) ^ r := mul_comm _ _
            _ ≤ ((K + r + 1 : ℕ) : ℝ) * ((K + r).factorial : ℝ) :=
                mul_le_mul hK_le ihr (by positivity) (by positivity)
      have hn_eq : n = K + (n - K) := by omega
      calc (Real.exp A₁) ^ n
          ≤ (K : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hexp_le_K n
        _ = (K : ℝ) ^ K * (K : ℝ) ^ (n - K) := by rw [← pow_add, ← hn_eq]
        _ ≤ (K : ℝ) ^ K * ((K + (n - K)).factorial : ℝ) :=
            mul_le_mul_of_nonneg_left (hstep (n - K)) (by positivity)
        _ = (K : ℝ) ^ K * (n.factorial : ℝ) := by rw [← hn_eq]
  have hCpos : 0 < B * (K : ℝ) ^ K * Real.exp (A₁ * ((M : ℝ) + 1)) := by positivity
  refine ⟨B * (K : ℝ) ^ K * Real.exp (A₁ * ((M : ℝ) + 1)), hCpos, fun v hv => ?_⟩
  set C : ℝ := B * (K : ℝ) ^ K * Real.exp (A₁ * ((M : ℝ) + 1))
  have hexp_mono : Real.exp (-A₁ * v) ≤ Real.exp (-A * v) :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hexp_mono hCpos.le)
  by_cases hvM : v ≤ (M : ℝ)
  · have hB_v : ‖recipGamma α (v : ℂ)‖ ≤ B := hB_on v hv (by linarith)
    have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ K := one_le_pow₀ (by exact_mod_cast (show 1 ≤ K by omega))
    have hexp_ge1 : (1 : ℝ) ≤ Real.exp (A₁ * ((M : ℝ) + 1)) * Real.exp (-A₁ * v) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖recipGamma α (v : ℂ)‖ ≤ B := hB_v
      _ = B * 1 * 1 := by ring
      _ ≤ B * (K : ℝ) ^ K * (Real.exp (A₁ * ((M : ℝ) + 1)) * Real.exp (-A₁ * v)) := by
          gcongr
      _ = C * Real.exp (-A₁ * v) := by dsimp [C]; ring
  · push Not at hvM
    let n : ℕ := ⌊v⌋₊ - M
    have hM_le_fl : M ≤ ⌊v⌋₊ := Nat.le_floor hvM.le
    have hv_lt : v < (n : ℝ) + (M : ℝ) + 1 := by
      dsimp [n]
      have h1 : v < (⌊v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v
      have h2 : ((⌊v⌋₊ - M : ℕ) : ℝ) = (⌊v⌋₊ : ℝ) - (M : ℝ) := Nat.cast_sub hM_le_fl
      linarith
    have hinv_fac : 1 / (n.factorial : ℝ) ≤ (K : ℝ) ^ K * Real.exp (-A₁ * (n : ℝ)) := by
      rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))]
      have h1 := hfac_ge_exp n
      rw [← Real.exp_nat_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-A₁ * (n : ℝ))).le
      have hcancel : Real.exp (-A₁ * (n : ℝ)) * Real.exp ((n : ℝ) * A₁) = 1 := by
        rw [← Real.exp_add]; convert Real.exp_zero; ring
      rw [hcancel] at h2
      linarith
    have hexp_n : Real.exp (-A₁ * (n : ℝ)) ≤ Real.exp (A₁ * ((M : ℝ) + 1)) * Real.exp (-A₁ * v) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc ‖recipGamma α (v : ℂ)‖
        ≤ B / (n.factorial : ℝ) := hfac_decay v hvM.le
      _ = B * (1 / (n.factorial : ℝ)) := by ring
      _ ≤ B * ((K : ℝ) ^ K * Real.exp (-A₁ * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hinv_fac hBpos.le
      _ ≤ B * ((K : ℝ) ^ K * (Real.exp (A₁ * ((M : ℝ) + 1)) * Real.exp (-A₁ * v))) := by
          gcongr
      _ = C * Real.exp (-A₁ * v) := by dsimp [C]; ring

/-! ### Integrability, Holomorphicity, and Exact Euler Identity for `volterraLaplace` -/

private lemma norm_exp_neg_div_le_one {z : ℂ} (hz : 0 < z.re) {v : ℝ} (hv : 0 ≤ v) :
    ‖Complex.exp (-(v : ℂ) / z)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.mpr ?_
  have hre : (-(v : ℂ) / z).re = -v * z.re / Complex.normSq z := by
    rw [div_eq_mul_inv, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.inv_re]
    ring
  rw [hre]
  have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr (by intro h0; rw [h0] at hz; simp at hz)
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hns.le

private lemma norm_ofReal_cpow_of_pos {v : ℝ} (hv : 0 < v) (β : ℂ) :
    ‖(v : ℂ) ^ β‖ = v ^ β.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]

private lemma integrableOn_volterraInt (β α : ℂ) (hβ : -1 < β.re) {z : ℂ} (hz : 0 < z.re) :
    MeasureTheory.IntegrableOn
      (fun v : ℝ => Complex.exp (-(v : ℂ) / z) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  obtain ⟨C, hCpos, hdecay⟩ := norm_recipGamma_real_exp_decay α 1
  have hdom : MeasureTheory.IntegrableOn (fun v : ℝ => C * (Real.exp (-v) * v ^ β.re))
      (Set.Ioi (0 : ℝ)) := by
    have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < β.re + 1 by linarith)
    simp only [add_sub_cancel_right] at hG
    exact hG.const_mul C
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun v : ℝ => Complex.exp (-(v : ℂ) / z) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hcont : ContinuousOn
        (fun v : ℝ => Complex.exp (-(v : ℂ) / z) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ))
        (Set.Ioi (0 : ℝ)) := by
      refine ((ContinuousOn.mul ?_ ?_).mul ?_)
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.neg).div_const z)).continuousOn
      · intro v hv
        have hv_slit : (v : ℂ) ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hv))
        exact ((Complex.hasStrictDerivAt_cpow_const hv_slit).hasDerivAt.continuousAt.comp
          Complex.continuous_ofReal.continuousAt).continuousWithinAt
      · exact ((differentiable_recipGamma α).continuous.comp Complex.continuous_ofReal).continuousOn
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  refine hdom.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
  have hvpos : 0 < v := hv
  rw [norm_mul, norm_mul, norm_ofReal_cpow_of_pos hvpos β]
  calc ‖Complex.exp (-(v : ℂ) / z)‖ * v ^ β.re * ‖recipGamma α (v : ℂ)‖
      ≤ 1 * v ^ β.re * (C * Real.exp (-1 * v)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (norm_exp_neg_div_le_one hz hvpos.le)
          (Real.rpow_nonneg hvpos.le _)) (hdecay v hvpos.le) (norm_nonneg _)
          (by positivity)
    _ = C * (Real.exp (-v) * v ^ β.re) := by ring_nf

lemma hasDerivAt_volterraInt (β α : ℂ) (hβ : -1 < β.re) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (volterraInt β α) ((z₀ ^ 2)⁻¹ * volterraInt (β + 1) α z₀) z₀ := by
  let r : ℝ := z₀.re / 2
  have hrpos : 0 < r := by positivity
  let s : Set ℂ := Metric.ball z₀ r
  have hs_nhds : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hs_re : ∀ z ∈ s, r < z.re := by
    intro z hz
    have hdist : ‖z - z₀‖ < r := by simpa [s, Metric.mem_ball, dist_eq_norm] using hz
    have hre_diff : |z.re - z₀.re| < r :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - z₀)) hdist
    have := (abs_lt.mp hre_diff).1
    dsimp [r] at *; linarith
  have hs_norm : ∀ z ∈ s, r < ‖z‖ := fun z hz =>
    lt_of_lt_of_le (hs_re z hz) (Complex.re_le_norm z)
  obtain ⟨C, hCpos, hdecay⟩ := norm_recipGamma_real_exp_decay α 1
  let F : ℂ → ℝ → ℂ := fun z v =>
    Complex.exp (-(v : ℂ) / z) * ((v : ℂ) ^ β) * recipGamma α (v : ℂ)
  let F' : ℂ → ℝ → ℂ := fun z v =>
    ((z ^ 2)⁻¹ * Complex.exp (-(v : ℂ) / z)) * ((v : ℂ) ^ (β + 1)) * recipGamma α (v : ℂ)
  let bound : ℝ → ℝ := fun v => (r ^ 2)⁻¹ * C * (Real.exp (-v) * v ^ (β.re + 1))
  have hbound_int : MeasureTheory.IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < β.re + 2 by linarith)
    have hsimp : (β.re + 2) - 1 = β.re + 1 := by ring
    rw [hsimp] at hG
    exact hG.const_mul ((r ^ 2)⁻¹ * C)
  have hF_meas : ∀ᶠ z in nhds z₀,
      MeasureTheory.AEStronglyMeasurable (F z) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [hs_nhds] with z hz
    exact (integrableOn_volterraInt β α hβ (lt_trans hrpos (hs_re z hz))).aestronglyMeasurable
  have hF_int : MeasureTheory.Integrable (F z₀) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_volterraInt β α hβ hz₀
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' z₀)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 := (integrableOn_volterraInt (β + 1) α (by simp; linarith) hz₀).const_mul (z₀ ^ 2)⁻¹
    refine h1.aestronglyMeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v _
    dsimp [F']; ring
  have h_bound : ∀ᵐ v ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ s, ‖F' z v‖ ≤ bound v := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv z hz
    have hvpos : 0 < v := hv
    have hzre : 0 < z.re := lt_trans hrpos (hs_re z hz)
    have hznorm : r < ‖z‖ := hs_norm z hz
    dsimp [F', bound]
    rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_pow,
      norm_ofReal_cpow_of_pos hvpos (β + 1)]
    have hre1 : (β + 1).re = β.re + 1 := by simp
    rw [hre1]
    have hinv_le : (‖z‖ ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos hrpos 2) (pow_le_pow_left₀ hrpos.le hznorm.le 2)
    calc (‖z‖ ^ 2)⁻¹ * ‖Complex.exp (-(v : ℂ) / z)‖ * v ^ (β.re + 1) * ‖recipGamma α (v : ℂ)‖
        ≤ (r ^ 2)⁻¹ * 1 * v ^ (β.re + 1) * (C * Real.exp (-1 * v)) := by
          gcongr
          · exact norm_exp_neg_div_le_one hzre hvpos.le
          · exact hdecay v hvpos.le
      _ = (r ^ 2)⁻¹ * C * (Real.exp (-v) * v ^ (β.re + 1)) := by ring_nf
  have h_diff : ∀ᵐ v ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ s, HasDerivAt (fun w => F w v) (F' z v) z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv z hz
    have hvpos : 0 < v := hv
    have hvne : (v : ℂ) ≠ 0 := by exact_mod_cast hvpos.ne'
    have hzne : z ≠ 0 := by
      intro h0; have := hs_re z hz; rw [h0] at this; simp at this; linarith
    have hdiv : HasDerivAt (fun w : ℂ => -(v : ℂ) / w) ((v : ℂ) / z ^ 2) z := by
      have h1 := (hasDerivAt_inv hzne).const_mul (-(v : ℂ))
      convert h1 using 1
      · ext w; rw [div_eq_mul_inv]
      · ring
    have hexp := hdiv.cexp
    have hmul := (hexp.mul_const ((v : ℂ) ^ β)).mul_const (recipGamma α (v : ℂ))
    convert hmul using 1
    dsimp [F']
    have hvcpow : (v : ℂ) ^ (β + 1) = (v : ℂ) ^ β * (v : ℂ) := by
      rw [Complex.cpow_add _ _ hvne, Complex.cpow_one]
    rw [hvcpow]; ring
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds hF_meas hF_int
    hF'_meas h_bound hbound_int h_diff).2
  refine hres.congr_deriv ?_
  dsimp only [volterraInt]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => by dsimp [F']; ring

lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

lemma isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane := by
  have hconv : Convex ℝ rightHalfPlane := by
    intro x hx y hy a b ha hb hab
    simp only [rightHalfPlane, Set.mem_ofPred_eq] at hx hy ⊢
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · nlinarith
  exact hconv.isPreconnected

lemma analyticOnNhd_volterraInt (β α : ℂ) (hβ : -1 < β.re) :
    AnalyticOnNhd ℂ (volterraInt β α) rightHalfPlane := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_rightHalfPlane
  intro z hz
  exact (hasDerivAt_volterraInt β α hβ hz).differentiableAt.differentiableWithinAt

/-- Exact complex derivative and Euler differential identity for `volterraLaplace β α` on `U`:
`z * deriv (volterraLaplace β α) z = (β + 1) * (volterraLaplace (β + 1) α z - volterraLaplace β α z)`. -/
lemma hasDerivAt_volterraLaplace (β α : ℂ) (hβ : -1 < β.re) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (volterraLaplace β α)
      (z⁻¹ * ((β + 1) * (volterraLaplace (β + 1) α z - volterraLaplace β α z))) z := by
  have hz_slit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hzne : z ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
  have hβ1_ne : β + 1 ≠ 0 := by
    intro h0; have := congr_arg Complex.re h0; simp at this; linarith
  have hGne : Complex.Gamma (β + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hcpow : HasDerivAt (fun w : ℂ => w ^ (-(β + 1))) (-(β + 1) * z ^ (-(β + 1) - 1)) z :=
    (Complex.hasStrictDerivAt_cpow_const hz_slit).hasDerivAt
  have hint := hasDerivAt_volterraInt β α hβ hz
  have hprod := (hcpow.const_mul (Complex.Gamma (β + 1))⁻¹).mul hint
  refine hprod.congr_deriv ?_
  have hpow1 : z ^ (-(β + 1) - 1) = z⁻¹ * z ^ (-(β + 1)) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hzne, Complex.cpow_neg_one, mul_comm]
  have hpow2 : z ^ (-(β + 1 + 1)) = z⁻¹ * z ^ (-(β + 1)) := by
    have : -(β + 1 + 1) = -(β + 1) + (-1) := by ring
    rw [this, Complex.cpow_add _ _ hzne, Complex.cpow_neg_one, mul_comm]
  have hG2 : Complex.Gamma (β + 1 + 1) = (β + 1) * Complex.Gamma (β + 1) :=
    Complex.Gamma_add_one (β + 1) hβ1_ne
  dsimp only [volterraLaplace]
  rw [hG2, hpow1, hpow2]
  field_simp [hzne, hβ1_ne, hGne]
  ring

lemma analyticOnNhd_volterraLaplace (β α : ℂ) (hβ : -1 < β.re) :
    AnalyticOnNhd ℂ (volterraLaplace β α) rightHalfPlane := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_rightHalfPlane
  intro z hz
  exact (hasDerivAt_volterraLaplace β α hβ hz).differentiableAt.differentiableWithinAt

lemma eulerOpC_volterraLaplace (β α : ℂ) (hβ : -1 < β.re) {z : ℂ} (hz : 0 < z.re) :
    eulerOpC (volterraLaplace β α) z =
      (β + 1) * (volterraLaplace (β + 1) α z - volterraLaplace β α z) := by
  have hzne : z ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
  rw [eulerOpC, (hasDerivAt_volterraLaplace β α hβ hz).deriv]
  field_simp [hzne]

lemma eulerPS_volterraAsympSeries (β α : ℂ) (hβ : -1 < β.re) :
    eulerPS (volterraAsympSeries β α) =
      PowerSeries.C (β + 1) * (volterraAsympSeries (β + 1) α - volterraAsympSeries β α) := by
  ext n
  rw [coeff_eulerPS, PowerSeries.coeff_C_mul, map_sub]
  simp only [volterraAsympSeries, PowerSeries.coeff_mk, volterraCoeff]
  have hβ1_ne : β + 1 ≠ 0 := by
    intro h0; have := congr_arg Complex.re h0; simp at this; linarith
  have hGne : Complex.Gamma (β + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG1 : Complex.Gamma (β + 1 + 1) = (β + 1) * Complex.Gamma (β + 1) :=
    Complex.Gamma_add_one (β + 1) hβ1_ne
  have hnβ_ne : (n : ℂ) + β + 1 ≠ 0 := by
    intro h0; have := congr_arg Complex.re h0
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at this
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hG2 : Complex.Gamma ((n : ℂ) + (β + 1) + 1) =
      ((n : ℂ) + β + 1) * Complex.Gamma ((n : ℂ) + β + 1) := by
    have : (n : ℂ) + (β + 1) + 1 = ((n : ℂ) + β + 1) + 1 := by ring
    rw [this, Complex.Gamma_add_one _ hnβ_ne]
  rw [hG1, hG2]
  field_simp [hβ1_ne, hGne]
  ring

/-! ### All-orders asymptotic expansions at `0⁺` and Watson's Lemma -/

/-- `HasAsympExpAtZero f S` means `f : ℝ → ℂ` has `S : PowerSeries ℂ` as its all-orders
Poincaré asymptotic expansion as `x → 0⁺`. -/
@[expose] def HasAsympExpAtZero (f : ℝ → ℂ) (S : PowerSeries ℂ) : Prop :=
  ∀ N : ℕ, ∃ C > 0, ∃ δ > 0, ∀ x : ℝ, 0 < x → x < δ →
    ‖f x - ∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n‖ ≤ C * x ^ N

lemma hasAsympExpAtZero_congr {f g : ℝ → ℂ} {S : PowerSeries ℂ}
    (hfg : ∀ x : ℝ, 0 < x → f x = g x) (hf : HasAsympExpAtZero f S) :
    HasAsympExpAtZero g S := by
  intro N
  obtain ⟨C, hC, δ, hδ, h⟩ := hf N
  exact ⟨C, hC, δ, hδ, fun x hx hxd => by rw [← hfg x hx]; exact h x hx hxd⟩

lemma hasAsympExpAtZero_const (c : ℂ) : HasAsympExpAtZero (fun _ => c) (PowerSeries.C c) := by
  intro N
  refine ⟨max 1 ‖c‖, lt_of_lt_of_le one_pos (le_max_left _ _), 1, one_pos, fun x hx _ => ?_⟩
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one]
    exact le_max_right 1 ‖c‖
  · have hsum : ∑ n ∈ Finset.range (M + 1), PowerSeries.coeff n (PowerSeries.C c) * (x : ℂ) ^ n = c := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro n _ hn0; simp [PowerSeries.coeff_C, hn0]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos M)) h
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (pow_nonneg hx.le _)

lemma hasAsympExpAtZero_poly (p : Polynomial ℂ) :
    HasAsympExpAtZero (fun x => p.eval (x : ℂ)) (p : PowerSeries ℂ) := by
  intro N
  let M : ℕ := max N (p.natDegree + 1)
  let C : ℝ := 1 + ∑ n ∈ Finset.Ico N M, ‖p.coeff n‖
  have hC : 0 < C := by
    have : 0 ≤ ∑ n ∈ Finset.Ico N M, ‖p.coeff n‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    dsimp [C]; linarith
  refine ⟨C, hC, 1, one_pos, fun x hx hx1 => ?_⟩
  have heval : p.eval (x : ℂ) = ∑ n ∈ Finset.range M, p.coeff n * (x : ℂ) ^ n := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right N _))]
  have hsplit : ∑ n ∈ Finset.range M, p.coeff n * (x : ℂ) ^ n -
      ∑ n ∈ Finset.range N, PowerSeries.coeff n (p : PowerSeries ℂ) * (x : ℂ) ^ n =
      ∑ n ∈ Finset.Ico N M, p.coeff n * (x : ℂ) ^ n := by
    have hcoeff : ∑ n ∈ Finset.range N, PowerSeries.coeff n (p : PowerSeries ℂ) * (x : ℂ) ^ n =
        ∑ n ∈ Finset.range N, p.coeff n * (x : ℂ) ^ n := by
      refine Finset.sum_congr rfl fun n _ => by rw [Polynomial.coeff_coe]
    rw [hcoeff]
    have hNM : N ≤ M := le_max_left _ _
    have hunion : Finset.range M = Finset.range N ∪ Finset.Ico N M := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range N) (Finset.Ico N M) := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      simp only [Finset.mem_range] at hj1; simp only [Finset.mem_Ico] at hj2; omega
    rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left]
  dsimp only
  rw [heval, hsplit]
  calc ‖∑ n ∈ Finset.Ico N M, p.coeff n * (x : ℂ) ^ n‖
      ≤ ∑ n ∈ Finset.Ico N M, ‖p.coeff n * (x : ℂ) ^ n‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ico N M, ‖p.coeff n‖ * x ^ n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
    _ ≤ ∑ n ∈ Finset.Ico N M, ‖p.coeff n‖ * x ^ N := by
        refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hx.le hx1.le (Finset.mem_Ico.mp hn).1) (norm_nonneg _)
    _ = (∑ n ∈ Finset.Ico N M, ‖p.coeff n‖) * x ^ N := (Finset.sum_mul _ _ _).symm
    _ ≤ C * x ^ N := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hx.le N)

lemma hasAsympExpAtZero_add {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExpAtZero f S) (hg : HasAsympExpAtZero g T) :
    HasAsympExpAtZero (fun x => f x + g x) (S + T) := by
  intro N
  obtain ⟨C₁, hC₁, δ₁, hδ₁, h1⟩ := hf N
  obtain ⟨C₂, hC₂, δ₂, hδ₂, h2⟩ := hg N
  refine ⟨C₁ + C₂, by linarith, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hxd => ?_⟩
  have hsum : ∑ n ∈ Finset.range N, PowerSeries.coeff n (S + T) * (x : ℂ) ^ n =
      (∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n) +
      (∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => by rw [map_add, add_mul]
  rw [hsum]
  have heq : f x + g x -
      ((∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n) +
       (∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n)) =
      (f x - ∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n) +
      (g x - ∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n) := by ring
  rw [heq]
  calc ‖_ + _‖ ≤ ‖f x - ∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n‖ +
        ‖g x - ∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n‖ := norm_add_le _ _
    _ ≤ C₁ * x ^ N + C₂ * x ^ N :=
        add_le_add (h1 x hx (lt_of_lt_of_le hxd (min_le_left _ _)))
          (h2 x hx (lt_of_lt_of_le hxd (min_le_right _ _)))
    _ = (C₁ + C₂) * x ^ N := by ring

lemma hasAsympExpAtZero_sub {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExpAtZero f S) (hg : HasAsympExpAtZero g T) :
    HasAsympExpAtZero (fun x => f x - g x) (S - T) := by
  intro N
  obtain ⟨C₁, hC₁, δ₁, hδ₁, h1⟩ := hf N
  obtain ⟨C₂, hC₂, δ₂, hδ₂, h2⟩ := hg N
  refine ⟨C₁ + C₂, by linarith, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hxd => ?_⟩
  have hsum : ∑ n ∈ Finset.range N, PowerSeries.coeff n (S - T) * (x : ℂ) ^ n =
      (∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n) -
      (∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by rw [map_sub, sub_mul]
  rw [hsum]
  have heq : f x - g x -
      ((∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n) -
       (∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n)) =
      (f x - ∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n) -
      (g x - ∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n) := by ring
  rw [heq]
  calc ‖_ - _‖ ≤ ‖f x - ∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n‖ +
        ‖g x - ∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n‖ := norm_sub_le _ _
    _ ≤ C₁ * x ^ N + C₂ * x ^ N :=
        add_le_add (h1 x hx (lt_of_lt_of_le hxd (min_le_left _ _)))
          (h2 x hx (lt_of_lt_of_le hxd (min_le_right _ _)))
    _ = (C₁ + C₂) * x ^ N := by ring

lemma hasAsympExpAtZero_mul {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExpAtZero f S) (hg : HasAsympExpAtZero g T) :
    HasAsympExpAtZero (fun x => f x * g x) (S * T) := by
  intro N
  obtain ⟨C₁, hC₁, δ₁, hδ₁, h1⟩ := hf N
  obtain ⟨C₂, hC₂, δ₂, hδ₂, h2⟩ := hg N
  let P_S : ℝ → ℂ := fun x => ∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n
  let P_T : ℝ → ℂ := fun x => ∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n
  let M_S : ℝ := ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n S‖
  let M_T : ℝ := ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n T‖
  have hMS_nn : 0 ≤ M_S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hMT_nn : 0 ≤ M_T := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let δ : ℝ := min 1 (min δ₁ δ₂)
  have hδ : 0 < δ := lt_min one_pos (lt_min hδ₁ hδ₂)
  let C : ℝ := C₁ * M_T + M_S * C₂ + C₁ * C₂ + M_S * M_T + 1
  have hC : 0 < C := by positivity
  refine ⟨C, hC, δ, hδ, fun x hx hxd => ?_⟩
  have hx1 : x < 1 := lt_of_lt_of_le hxd (min_le_left _ _)
  have hx1' : x < δ₁ := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_left _ _))
  have hx2' : x < δ₂ := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_right _ _))
  have hPS_le : ‖P_S x‖ ≤ M_S := by
    calc ‖∑ n ∈ Finset.range N, PowerSeries.coeff n S * (x : ℂ) ^ n‖
        ≤ ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n S * (x : ℂ) ^ n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n S‖ * x ^ n :=
          Finset.sum_congr rfl fun n _ => by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
      _ ≤ ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n S‖ * 1 :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (pow_le_one₀ hx.le hx1.le) (norm_nonneg _)
      _ = M_S := by simp [M_S]
  have hPT_le : ‖P_T x‖ ≤ M_T := by
    calc ‖∑ n ∈ Finset.range N, PowerSeries.coeff n T * (x : ℂ) ^ n‖
        ≤ ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n T * (x : ℂ) ^ n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n T‖ * x ^ n :=
          Finset.sum_congr rfl fun n _ => by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
      _ ≤ ∑ n ∈ Finset.range N, ‖PowerSeries.coeff n T‖ * 1 :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (pow_le_one₀ hx.le hx1.le) (norm_nonneg _)
      _ = M_T := by simp [M_T]
  -- Compare `P_S x * P_T x` with `∑_{k < N} coeff k (S * T) * x^k`:
  have hprod_diff : ‖P_S x * P_T x - ∑ k ∈ Finset.range N, PowerSeries.coeff k (S * T) * (x : ℂ) ^ k‖ ≤
      M_S * M_T * x ^ N := by
    have hexpand : P_S x * P_T x =
        ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * (x : ℂ) ^ (p.1 + p.2) := by
      dsimp [P_S, P_T]
      rw [Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [pow_add]; ring
    have hlow : ∑ k ∈ Finset.range N, PowerSeries.coeff k (S * T) * (x : ℂ) ^ k =
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N),
          PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * (x : ℂ) ^ (p.1 + p.2) := by
      have h1 : ∑ k ∈ Finset.range N, PowerSeries.coeff k (S * T) * (x : ℂ) ^ k =
          ∑ k ∈ Finset.range N, ∑ p ∈ Finset.antidiagonal k,
            PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * (x : ℂ) ^ (p.1 + p.2) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [PowerSeries.coeff_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_antidiagonal.mp hp)]
      rw [h1, Finset.sum_sigma']
      refine Finset.sum_nbij'
        (fun s => s.2)
        (fun p => ⟨p.1 + p.2, p⟩)
        (fun s hs => ?_)
        (fun p hp => ?_)
        (fun s hs => ?_)
        (fun p _ => rfl)
        (fun _ _ => rfl)
      · rcases Finset.mem_sigma.mp hs with ⟨hk, hp⟩
        have hlt := Finset.mem_range.mp hk
        have hadd := Finset.mem_antidiagonal.mp hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩, by omega⟩
      · rcases Finset.mem_filter.mp hp with ⟨_, hlt⟩
        exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hlt, Finset.mem_antidiagonal.mpr rfl⟩
      · rcases Finset.mem_sigma.mp hs with ⟨_, hp⟩
        exact Sigma.ext (Finset.mem_antidiagonal.mp hp) (heq_of_eq rfl)
    rw [hexpand, hlow]
    have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.range N ×ˢ Finset.range N)
      (fun p : ℕ × ℕ => p.1 + p.2 < N)
      (fun p => PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * (x : ℂ) ^ (p.1 + p.2))).symm
    rw [hpart, add_sub_cancel_left]
    calc ‖∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => ¬ p.1 + p.2 < N),
            PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * (x : ℂ) ^ (p.1 + p.2)‖
        ≤ ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => ¬ p.1 + p.2 < N),
            ‖PowerSeries.coeff p.1 S * PowerSeries.coeff p.2 T * (x : ℂ) ^ (p.1 + p.2)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => ¬ p.1 + p.2 < N),
            ‖PowerSeries.coeff p.1 S‖ * ‖PowerSeries.coeff p.2 T‖ * x ^ N := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hge : N ≤ p.1 + p.2 := by
            have := (Finset.mem_filter.mp hp).2; omega
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx.le hx1.le hge) (by positivity)
      _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            ‖PowerSeries.coeff p.1 S‖ * ‖PowerSeries.coeff p.2 T‖ * x ^ N :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ = (∑ p ∈ Finset.range N ×ˢ Finset.range N,
            ‖PowerSeries.coeff p.1 S‖ * ‖PowerSeries.coeff p.2 T‖) * x ^ N :=
          (Finset.sum_mul _ _ _).symm
      _ = M_S * M_T * x ^ N := by
          dsimp [M_S, M_T]; rw [Finset.sum_mul_sum, Finset.sum_product]
  have hident : f x * g x - ∑ k ∈ Finset.range N, PowerSeries.coeff k (S * T) * (x : ℂ) ^ k =
      (f x - P_S x) * P_T x + P_S x * (g x - P_T x) + (f x - P_S x) * (g x - P_T x) +
      (P_S x * P_T x - ∑ k ∈ Finset.range N, PowerSeries.coeff k (S * T) * (x : ℂ) ^ k) := by ring
  rw [hident]
  have hfN := h1 x hx hx1'
  have hgN := h2 x hx hx2'
  have hxN_le1 : x ^ N ≤ 1 := pow_le_one₀ hx.le hx1.le
  calc ‖_‖ ≤ ‖(f x - P_S x) * P_T x‖ + ‖P_S x * (g x - P_T x)‖ +
        ‖(f x - P_S x) * (g x - P_T x)‖ +
        ‖P_S x * P_T x - ∑ k ∈ Finset.range N, PowerSeries.coeff k (S * T) * (x : ℂ) ^ k‖ := by
        calc ‖((f x - P_S x) * P_T x + P_S x * (g x - P_T x) + (f x - P_S x) * (g x - P_T x)) + _‖
            ≤ ‖(f x - P_S x) * P_T x + P_S x * (g x - P_T x) + (f x - P_S x) * (g x - P_T x)‖ + _ :=
              norm_add_le _ _
          _ ≤ (‖(f x - P_S x) * P_T x + P_S x * (g x - P_T x)‖ + ‖(f x - P_S x) * (g x - P_T x)‖) + _ := by
              gcongr; exact norm_add_le _ _
          _ ≤ ((‖(f x - P_S x) * P_T x‖ + ‖P_S x * (g x - P_T x)‖) + ‖(f x - P_S x) * (g x - P_T x)‖) + _ := by
              gcongr; exact norm_add_le _ _
    _ ≤ (C₁ * x ^ N) * M_T + M_S * (C₂ * x ^ N) + (C₁ * x ^ N) * (C₂ * x ^ N) + M_S * M_T * x ^ N := by
        rw [norm_mul, norm_mul, norm_mul]
        gcongr
    _ ≤ (C₁ * M_T + M_S * C₂ + C₁ * C₂ + M_S * M_T + 1) * x ^ N := by
        have hsq : (C₁ * x ^ N) * (C₂ * x ^ N) ≤ C₁ * C₂ * x ^ N := by
          have : (C₁ * x ^ N) * (C₂ * x ^ N) = (C₁ * C₂ * x ^ N) * x ^ N := by ring
          rw [this]
          exact mul_le_of_le_one_right (by positivity) hxN_le1
        have hxN_nn : 0 ≤ x ^ N := pow_nonneg hx.le N
        linarith

lemma hasAsympExpAtZero_pow {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExpAtZero f S) (k : ℕ) :
    HasAsympExpAtZero (fun x => (f x) ^ k) (S ^ k) := by
  induction k with
  | zero => simpa using hasAsympExpAtZero_const 1
  | succ m ih =>
    simpa [pow_succ] using hasAsympExpAtZero_mul ih hf

lemma hasAsympExpAtZero_finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → ℂ} {S : ι → PowerSeries ℂ}
    (h : ∀ i ∈ s, HasAsympExpAtZero (f i) (S i)) :
    HasAsympExpAtZero (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasAsympExpAtZero_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hasAsympExpAtZero_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma hasAsympExpAtZero_finset_prod {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → ℂ} {S : ι → PowerSeries ℂ}
    (h : ∀ i ∈ s, HasAsympExpAtZero (f i) (S i)) :
    HasAsympExpAtZero (fun x => ∏ i ∈ s, f i x) (∏ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasAsympExpAtZero_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact hasAsympExpAtZero_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma hasAsympExpAtZero_mvPolynomial {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    {g : Fin (r + 1) → ℝ → ℂ} {S : Fin (r + 1) → PowerSeries ℂ}
    (hg : ∀ i : Fin (r + 1), HasAsympExpAtZero (g i) (S i)) :
    HasAsympExpAtZero
      (fun x => MvPolynomial.eval₂ (Polynomial.evalRingHom (x : ℂ)) (fun i => g i x) P)
      (MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom S P) := by
  have hfun : ∀ x : ℝ,
      MvPolynomial.eval₂ (Polynomial.evalRingHom (x : ℂ)) (fun i => g i x) P =
      ∑ d ∈ P.support, (P.coeff d).eval (x : ℂ) * ∏ i : Fin (r + 1), (g i x) ^ d i := by
    intro x
    rw [MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d _ => by rfl
  have hps : MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom S P =
      ∑ d ∈ P.support, (P.coeff d : PowerSeries ℂ) * ∏ i : Fin (r + 1), (S i) ^ d i := by
    rw [MvPolynomial.eval₂_eq']
    rfl
  rw [hps]
  refine hasAsympExpAtZero_congr (fun x _ => (hfun x).symm) ?_
  refine hasAsympExpAtZero_finset_sum P.support fun d _ => ?_
  exact hasAsympExpAtZero_mul (hasAsympExpAtZero_poly (P.coeff d))
    (hasAsympExpAtZero_finset_prod Finset.univ fun i _ => hasAsympExpAtZero_pow (hg i) (d i))

/-- Uniqueness of asymptotic expansion at `0⁺`: if `0` has asymptotic expansion `S`, then `S = 0`. -/
lemma eq_zero_of_hasAsympExpAtZero_zero {S : PowerSeries ℂ}
    (h : HasAsympExpAtZero (fun _ => (0 : ℂ)) S) : S = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨C, hC, δ, hδ, hbd⟩ := h (k + 1)
    by_contra hne
    have hpos : 0 < ‖PowerSeries.coeff k S‖ := norm_pos_iff.mpr hne
    let x : ℝ := min (δ / 2) (‖PowerSeries.coeff k S‖ / (2 * C))
    have hx_pos : 0 < x := lt_min (by positivity) (by positivity)
    have hx_lt_δ : x < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hbd_x := hbd x hx_pos hx_lt_δ
    have hsum : ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff j S * (x : ℂ) ^ j =
        PowerSeries.coeff k S * (x : ℂ) ^ k := by
      rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
        rw [ih j (Finset.mem_range.mp hj), zero_mul]), zero_add]
    rw [hsum, zero_sub, norm_neg, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hx_pos.le, pow_succ] at hbd_x
    have hx_le : x ≤ ‖PowerSeries.coeff k S‖ / (2 * C) := min_le_right _ _
    have hC_mul : C * x ≤ ‖PowerSeries.coeff k S‖ / 2 := by
      have := mul_le_mul_of_nonneg_left hx_le hC.le
      have hsimp : C * (‖PowerSeries.coeff k S‖ / (2 * C)) = ‖PowerSeries.coeff k S‖ / 2 := by
        field_simp [hC.ne']
      linarith
    have hxk_pos : 0 < x ^ k := pow_pos hx_pos k
    have h1 : ‖PowerSeries.coeff k S‖ * x ^ k ≤ (‖PowerSeries.coeff k S‖ / 2) * x ^ k := by
      calc ‖PowerSeries.coeff k S‖ * x ^ k
          ≤ C * (x ^ k * x) := hbd_x
        _ = (C * x) * x ^ k := by ring
        _ ≤ (‖PowerSeries.coeff k S‖ / 2) * x ^ k := mul_le_mul_of_nonneg_right hC_mul hxk_pos.le
    nlinarith

/-! ### Watson's Endpoint Expansion for `volterraLaplace β α` and All Euler Derivatives -/

private lemma integral_exp_neg_div_mul_cpow {β : ℂ} (hβ : -1 < β.re) {x : ℝ} (hx : 0 < x) :
    ∫ v : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) =
      ((x : ℂ) ^ (β + 1)) * Complex.Gamma (β + 1) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hG : Complex.Gamma (β + 1) =
      ∫ u : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ)) * ((u : ℂ) ^ β) := by
    rw [Complex.Gamma_eq_integral (by simp; linarith), Complex.GammaIntegral]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp [Complex.ofReal_exp, add_sub_cancel_right]
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
    (fun u : ℝ => Complex.exp (-(u : ℂ)) * ((u : ℂ) ^ β)) (0 : ℝ) (inv_pos.mpr hx)
  rw [mul_zero, inv_inv] at hcomp
  -- `∫ v in Ioi 0, exp (-(x⁻¹ * v)) * (x⁻¹ * v)^β = x • ∫ u in Ioi 0, exp (-u) * u^β`
  have hlhs : ∫ v : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) =
      ((x : ℂ) ^ β) *
        ∫ v : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-((x⁻¹ * v : ℝ) : ℂ)) * (((x⁻¹ * v : ℝ) : ℂ) ^ β) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hvpos : 0 < v := hv
    have hexp : -((x⁻¹ * v : ℝ) : ℂ) = -(v : ℂ) / (x : ℂ) := by push_cast; ring
    have hpow : ((x : ℂ) ^ β) * (((x⁻¹ * v : ℝ) : ℂ) ^ β) = (v : ℂ) ^ β := by
      rw [show ((x⁻¹ * v : ℝ) : ℂ) = ((x⁻¹ : ℝ) : ℂ) * (v : ℂ) by push_cast; rfl]
      rw [Complex.mul_cpow_ofReal_nonneg (inv_pos.mpr hx).le hvpos.le, ← mul_assoc,
        ← Complex.mul_cpow_ofReal_nonneg hx.le (inv_pos.mpr hx).le]
      have : ((x : ℂ) * ((x⁻¹ : ℝ) : ℂ)) = 1 := by push_cast; field_simp [hxne]
      rw [this, Complex.one_cpow, one_mul]
    rw [hexp]; linear_combination Complex.exp (-(v : ℂ) / (x : ℂ)) * hpow.symm
  rw [hlhs, hcomp, ← hG, Complex.real_smul]
  have hxcpow : (x : ℂ) ^ (β + 1) = (x : ℂ) ^ β * (x : ℂ) := by
    rw [Complex.cpow_add _ _ hxne, Complex.cpow_one]
  rw [hxcpow]; ring

private lemma integral_exp_neg_div_mul_rpow {γ : ℝ} (hγ : -1 < γ) {x : ℝ} (hx : 0 < x) :
    ∫ v : ℝ in Set.Ioi (0 : ℝ), Real.exp (-v / x) * v ^ γ =
      x ^ (γ + 1) * Real.Gamma (γ + 1) := by
  have hG : Real.Gamma (γ + 1) = ∫ u : ℝ in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ γ := by
    rw [Real.Gamma_eq_integral (by linarith)]
    simp [add_sub_cancel_right]
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
    (fun u : ℝ => Real.exp (-u) * u ^ γ) (0 : ℝ) (inv_pos.mpr hx)
  rw [mul_zero, inv_inv] at hcomp
  have hlhs : ∫ v : ℝ in Set.Ioi (0 : ℝ), Real.exp (-v / x) * v ^ γ =
      x ^ γ * ∫ v : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(x⁻¹ * v)) * (x⁻¹ * v) ^ γ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hvpos : 0 < v := hv
    rw [Real.mul_rpow (inv_pos.mpr hx).le hvpos.le,
      show -(x⁻¹ * v) = -v / x by ring]
    have hcancel : x ^ γ * (x⁻¹) ^ γ = 1 := by
      rw [← Real.mul_rpow hx.le (inv_pos.mpr hx).le, mul_inv_cancel₀ hx.ne', Real.one_rpow]
    calc Real.exp (-v / x) * v ^ γ
        = Real.exp (-v / x) * (1 * v ^ γ) := by ring
      _ = Real.exp (-v / x) * (x ^ γ * (x⁻¹) ^ γ * v ^ γ) := by rw [hcancel]
      _ = x ^ γ * (Real.exp (-v / x) * ((x⁻¹) ^ γ * v ^ γ)) := by ring
  rw [hlhs, hcomp, ← hG, smul_eq_mul, Real.rpow_add hx, Real.rpow_one]
  ring

private lemma recipGamma_taylor_remainder_bound (α : ℂ) (N : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ v : ℝ, 0 ≤ v →
      ‖recipGamma α (v : ℂ) -
        ∑ n ∈ Finset.range N, (iteratedDeriv n (recipGamma α) 0 / (n.factorial : ℂ)) * (v : ℂ) ^ n‖ ≤
      M * v ^ N := by
  let c : ℕ → ℂ := fun n => iteratedDeriv n (recipGamma α) 0 / (n.factorial : ℂ)
  -- Bound `‖c n‖ ≤ K₀ / 2^n` via Cauchy on circle of radius `2`:
  obtain ⟨K_g, _, hgrowth⟩ := recipGamma_entire_growth α
  let K₀ : ℝ := Real.exp (K_g * 3 * Real.log 4)
  have hK₀_pos : 0 < K₀ := Real.exp_pos _
  have hc_le : ∀ n : ℕ, ‖c n‖ ≤ K₀ / (2 : ℝ) ^ n := by
    intro n
    have hcauchy : ‖iteratedDeriv n (recipGamma α) 0‖ ≤ (n.factorial : ℝ) * K₀ / (2 : ℝ) ^ n := by
      refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num : (0 : ℝ) < 2)
        (differentiable_recipGamma α).diffContOnCl fun z hz => ?_
      have hzn : ‖z‖ = 2 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      refine (hgrowth z).trans (Real.exp_le_exp.mpr ?_)
      rw [hzn]; norm_num
    have hc_norm : ‖c n‖ = ‖iteratedDeriv n (recipGamma α) 0‖ / (n.factorial : ℝ) := by
      dsimp [c]; rw [norm_div, Complex.norm_natCast]
    rw [hc_norm, div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))]
    refine hcauchy.trans_eq ?_; ring
  -- Bound on `[1, ∞)` using boundedness of `recipGamma α` on `[0, ∞)`:
  obtain ⟨B₀, hB₀_pos, hB₀⟩ := norm_recipGamma_real_exp_decay α 0
  let M₁ : ℝ := 2 * K₀
  let M₂ : ℝ := B₀ + ∑ n ∈ Finset.range N, ‖c n‖
  let M : ℝ := max M₁ M₂
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left M₁ M₂)
  refine ⟨M, hMpos, fun v hv => ?_⟩
  by_cases hv1 : v ≤ 1
  · have hsum := entire_taylor_hasSum (differentiable_recipGamma α) (v : ℂ)
    have hshift : HasSum (fun m : ℕ => c (N + m) * (v : ℂ) ^ (N + m))
        (recipGamma α (v : ℂ) - ∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n) := by
      have h1 := (hasSum_nat_add_iff' N (f := fun n => c n * (v : ℂ) ^ n)).mpr hsum
      convert h1 using 1
      · ext m; rw [add_comm]
    have hgeom : HasSum (fun m : ℕ => K₀ * (2 : ℝ)⁻¹ ^ m) (2 * K₀) := by
      have h0 := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_left K₀
      convert h0 using 1; ring
    have hterm : ∀ m : ℕ, ‖c (N + m) * (v : ℂ) ^ (N + m)‖ ≤
        (K₀ * (2 : ℝ)⁻¹ ^ m) * v ^ N := by
      intro m
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv, pow_add]
      have h1 : ‖c (N + m)‖ ≤ K₀ * (2 : ℝ)⁻¹ ^ m := by
        calc ‖c (N + m)‖ ≤ K₀ / (2 : ℝ) ^ (N + m) := hc_le (N + m)
          _ = K₀ * (2 : ℝ)⁻¹ ^ N * (2 : ℝ)⁻¹ ^ m := by rw [pow_add, div_eq_mul_inv, mul_inv, inv_pow, inv_pow]; ring
          _ ≤ K₀ * 1 * (2 : ℝ)⁻¹ ^ m := by
              gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
          _ = K₀ * (2 : ℝ)⁻¹ ^ m := by ring
      have hvm : v ^ m ≤ 1 := pow_le_one₀ hv hv1
      calc ‖c (N + m)‖ * (v ^ N * v ^ m)
          ≤ (K₀ * (2 : ℝ)⁻¹ ^ m) * (v ^ N * 1) := by gcongr
        _ = (K₀ * (2 : ℝ)⁻¹ ^ m) * v ^ N := by ring
    have hdom_sum : HasSum (fun m : ℕ => (K₀ * (2 : ℝ)⁻¹ ^ m) * v ^ N) ((2 * K₀) * v ^ N) :=
      hgeom.mul_right (v ^ N)
    have hnorm_sum : Summable (fun m : ℕ => ‖c (N + m) * (v : ℂ) ^ (N + m)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom_sum.summable
    calc ‖recipGamma α (v : ℂ) - ∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n‖
        = ‖∑' m : ℕ, c (N + m) * (v : ℂ) ^ (N + m)‖ := by rw [hshift.tsum_eq]
      _ ≤ ∑' m : ℕ, ‖c (N + m) * (v : ℂ) ^ (N + m)‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' m : ℕ, (K₀ * (2 : ℝ)⁻¹ ^ m) * v ^ N :=
          Summable.tsum_le_tsum hterm hnorm_sum hdom_sum.summable
      _ = M₁ * v ^ N := hdom_sum.tsum_eq
      _ ≤ M * v ^ N := mul_le_mul_of_nonneg_right (le_max_left M₁ M₂) (pow_nonneg hv N)
  · push Not at hv1
    have hvN1 : (1 : ℝ) ≤ v ^ N := one_le_pow₀ hv1.le
    calc ‖recipGamma α (v : ℂ) - ∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n‖
        ≤ ‖recipGamma α (v : ℂ)‖ + ‖∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n‖ := norm_sub_le _ _
      _ ≤ B₀ * 1 + ∑ n ∈ Finset.range N, ‖c n * (v : ℂ) ^ n‖ := by
          refine add_le_add ?_ (norm_sum_le _ _)
          simpa using hB₀ v hv
      _ ≤ B₀ * v ^ N + ∑ n ∈ Finset.range N, ‖c n‖ * v ^ N := by
          refine add_le_add (mul_le_mul_of_nonneg_left hvN1 hB₀_pos.le) (Finset.sum_le_sum fun n hn => ?_)
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hv1.le (le_of_lt (Finset.mem_range.mp hn))) (norm_nonneg _)
      _ = M₂ * v ^ N := by rw [← Finset.sum_mul]; dsimp [M₂]; ring
      _ ≤ M * v ^ N := mul_le_mul_of_nonneg_right (le_max_right M₁ M₂) (pow_nonneg hv N)

private lemma integrableOn_Ioi_comp_mul_left {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg : MeasureTheory.IntegrableOn g (Set.Ioi (0 : ℝ))) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => g (b * v)) (Set.Ioi (0 : ℝ)) := by
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at hg ⊢
  have hcomp := hg.comp_mul_left' hb.ne'
  refine hcomp.congr (Filter.Eventually.of_forall fun v => ?_)
  by_cases hv : 0 < v
  · have hbv : 0 < b * v := mul_pos hb hv
    simp [Set.indicator, hv, hbv]
  · have hbv : ¬ 0 < b * v := by
      intro h; exact hv (pos_of_mul_pos_right h hb.le)
    simp [Set.indicator, hv, hbv]

private lemma integrableOn_finset_sum {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    {s : Finset ι} {f : ι → ℝ → E} {S : Set ℝ}
    (h : ∀ i ∈ s, MeasureTheory.IntegrableOn (f i) S) :
    MeasureTheory.IntegrableOn (fun v => ∑ i ∈ s, f i v) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have heq : (fun v => ∑ i ∈ insert a s, f i v) = fun v => f a v + ∑ i ∈ s, f i v := by
      ext v; exact Finset.sum_insert ha
    rw [heq]
    exact MeasureTheory.Integrable.add h1 h2

private lemma setIntegral_finset_sum {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : ι → ℝ → E} {S : Set ℝ}
    (h : ∀ i ∈ s, MeasureTheory.IntegrableOn (f i) S) :
    ∫ v in S, (∑ i ∈ s, f i v) = ∑ i ∈ s, ∫ v in S, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := integrableOn_finset_sum (s := s) (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp_rw [Finset.sum_insert ha]
    rw [MeasureTheory.integral_add h1 h2, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- **Watson's Endpoint Asymptotic Expansion for `volterraLaplace β α`:**
For every `α : ℂ` and `β : ℂ` with `-1 < β.re`, `x ↦ volterraLaplace β α x` has
`volterraAsympSeries β α` as its all-orders asymptotic expansion as `x → 0⁺`. -/
theorem hasAsympExpAtZero_volterraLaplace (α β : ℂ) (hβ : -1 < β.re) :
    HasAsympExpAtZero (fun x : ℝ => volterraLaplace β α (x : ℂ)) (volterraAsympSeries β α) := by
  intro N
  obtain ⟨M, hMpos, hrem⟩ := recipGamma_taylor_remainder_bound α N
  let c : ℕ → ℂ := fun n => iteratedDeriv n (recipGamma α) 0 / (n.factorial : ℂ)
  let C : ℝ := ‖(Complex.Gamma (β + 1))⁻¹‖ * M * Real.Gamma ((N : ℝ) + β.re + 1) + 1
  have hCpos : 0 < C := by
    have hGpos : 0 < Real.Gamma ((N : ℝ) + β.re + 1) :=
      Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith)
    positivity
  refine ⟨C, hCpos, 1, one_pos, fun x hx _ => ?_⟩
  have hterm_int : ∀ n : ℕ,
      MeasureTheory.IntegrableOn
        (fun v : ℝ => Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * (c n * (v : ℂ) ^ n))
        (Set.Ioi (0 : ℝ)) := by
    intro n
    have hdom : MeasureTheory.IntegrableOn (fun v : ℝ => ‖c n‖ * (Real.exp (-v / x) * v ^ (β.re + (n : ℝ))))
        (Set.Ioi (0 : ℝ)) := by
      have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < β.re + (n : ℝ) + 1 by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      simp only [add_sub_cancel_right] at hG
      have h1 := integrableOn_Ioi_comp_mul_left hG (inv_pos.mpr hx)
      have h2 := h1.const_mul (‖c n‖ * x ^ (β.re + (n : ℝ)))
      refine MeasureTheory.IntegrableOn.congr_fun h2 (fun v hv => ?_) measurableSet_Ioi
      have hvpos : 0 < v := hv
      rw [Real.mul_rpow (inv_pos.mpr hx).le hvpos.le, show -(x⁻¹ * v) = -v / x by ring]
      have hcancel : x ^ (β.re + (n : ℝ)) * (x⁻¹) ^ (β.re + (n : ℝ)) = 1 := by
        rw [← Real.mul_rpow hx.le (inv_pos.mpr hx).le, mul_inv_cancel₀ hx.ne', Real.one_rpow]
      calc ‖c n‖ * x ^ (β.re + (n : ℝ)) * (Real.exp (-v / x) * ((x⁻¹) ^ (β.re + (n : ℝ)) * v ^ (β.re + (n : ℝ))))
          = ‖c n‖ * (Real.exp (-v / x) * ((x ^ (β.re + (n : ℝ)) * (x⁻¹) ^ (β.re + (n : ℝ))) * v ^ (β.re + (n : ℝ)))) := by ring
        _ = ‖c n‖ * (Real.exp (-v / x) * v ^ (β.re + (n : ℝ))) := by rw [hcancel, one_mul]
    have hcont : ContinuousOn
        (fun v : ℝ => Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * (c n * (v : ℂ) ^ n))
        (Set.Ioi (0 : ℝ)) := by
      refine ((ContinuousOn.mul ?_ ?_).mul ?_)
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.neg).div_const (x : ℂ))).continuousOn
      · intro v hv
        have hv_slit : (v : ℂ) ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hv))
        exact ((Complex.hasStrictDerivAt_cpow_const hv_slit).hasDerivAt.continuousAt.comp
          Complex.continuous_ofReal.continuousAt).continuousWithinAt
      · exact (continuous_const.mul (Complex.continuous_ofReal.pow n)).continuousOn
    refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
    have hvpos : 0 < v := hv
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, norm_ofReal_cpow_of_pos hvpos β,
      norm_pow, Complex.norm_real, Real.norm_of_nonneg hvpos.le,
      Real.rpow_add hvpos, Real.rpow_natCast]
    have hre : (-(v : ℂ) / (x : ℂ)).re = -v / x := by
      have : -(v : ℂ) / (x : ℂ) = (((-v / x : ℝ)) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [hre]; exact le_of_eq (by ring)
  have hterm_val : ∀ n : ℕ,
      (Complex.Gamma (β + 1))⁻¹ * ((x : ℂ) ^ (-(β + 1))) *
        ∫ v : ℝ in Set.Ioi (0 : ℝ),
          Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * (c n * (v : ℂ) ^ n) =
      volterraCoeff β α n * (x : ℂ) ^ n := by
    intro n
    have hre_n : -1 < (β + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
    have hint_eq : ∫ v : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * (c n * (v : ℂ) ^ n) =
        c n * (((x : ℂ) ^ ((β + (n : ℂ)) + 1)) * Complex.Gamma ((β + (n : ℂ)) + 1)) := by
      rw [← integral_exp_neg_div_mul_cpow hre_n hx, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      have hvne : (v : ℂ) ≠ 0 := by exact_mod_cast (show 0 < v from hv).ne'
      rw [Complex.cpow_add _ _ hvne, Complex.cpow_natCast]; ring
    rw [hint_eq, volterraCoeff]
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have harg : (β + (n : ℂ)) + 1 = (n : ℂ) + β + 1 := by ring
    have hcpow : ((x : ℂ) ^ (-(β + 1))) * ((x : ℂ) ^ ((n : ℂ) + β + 1)) = (x : ℂ) ^ n := by
      rw [← Complex.cpow_add _ _ hxne, show -(β + 1) + ((n : ℂ) + β + 1) = (n : ℂ) by ring,
        Complex.cpow_natCast]
    rw [harg]
    calc (Complex.Gamma (β + 1))⁻¹ * (x : ℂ) ^ (-(β + 1)) *
          (c n * ((x : ℂ) ^ ((n : ℂ) + β + 1) * Complex.Gamma (↑n + β + 1)))
        = (Complex.Gamma (↑n + β + 1) / Complex.Gamma (β + 1)) * c n *
          ((x : ℂ) ^ (-(β + 1)) * (x : ℂ) ^ ((n : ℂ) + β + 1)) := by
          rw [div_eq_mul_inv]; ring
      _ = (Complex.Gamma (↑n + β + 1) / Complex.Gamma (β + 1)) * c n * (x : ℂ) ^ n := by
          rw [hcpow]
  -- Rewrite the difference as a single integral over `Ioi 0`:
  have hsum_int : MeasureTheory.IntegrableOn
      (fun v : ℝ => ∑ n ∈ Finset.range N,
        Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * (c n * (v : ℂ) ^ n))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_finset_sum fun n _ => hterm_int n
  have hdiff_eq : volterraLaplace β α (x : ℂ) -
      ∑ n ∈ Finset.range N, PowerSeries.coeff n (volterraAsympSeries β α) * (x : ℂ) ^ n =
      (Complex.Gamma (β + 1))⁻¹ * ((x : ℂ) ^ (-(β + 1))) *
        ∫ v : ℝ in Set.Ioi (0 : ℝ),
          Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) *
            (recipGamma α (v : ℂ) - ∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n) := by
    have hsum_val : ∑ n ∈ Finset.range N, PowerSeries.coeff n (volterraAsympSeries β α) * (x : ℂ) ^ n =
        (Complex.Gamma (β + 1))⁻¹ * ((x : ℂ) ^ (-(β + 1))) *
          ∫ v : ℝ in Set.Ioi (0 : ℝ),
            ∑ n ∈ Finset.range N,
              Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) * (c n * (v : ℂ) ^ n) := by
      rw [setIntegral_finset_sum (fun n _ => hterm_int n), Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [volterraAsympSeries, PowerSeries.coeff_mk, hterm_val n]
    rw [hsum_val, volterraLaplace, ← mul_sub, volterraInt,
      ← MeasureTheory.integral_sub (integrableOn_volterraInt β α hβ (by simpa using hx)) hsum_int]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [← Finset.mul_sum, mul_sub]
  rw [hdiff_eq, norm_mul, norm_mul, norm_ofReal_cpow_of_pos hx (-(β + 1))]
  have hre_neg : (-(β + 1)).re = -(β.re + 1) := by simp
  rw [hre_neg]
  -- Bound the remainder integral by `M * x^(N + β.re + 1) * Real.Gamma (N + β.re + 1)`:
  have hdom_rem : MeasureTheory.IntegrableOn
      (fun v : ℝ => M * (Real.exp (-v / x) * v ^ ((N : ℝ) + β.re))) (Set.Ioi (0 : ℝ)) := by
    have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < (N : ℝ) + β.re + 1 by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith)
    simp only [add_sub_cancel_right] at hG
    have h1 := integrableOn_Ioi_comp_mul_left hG (inv_pos.mpr hx)
    have h2 := h1.const_mul (M * x ^ ((N : ℝ) + β.re))
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun v hv => ?_) measurableSet_Ioi
    have hvpos : 0 < v := hv
    rw [Real.mul_rpow (inv_pos.mpr hx).le hvpos.le, show -(x⁻¹ * v) = -v / x by ring]
    have hcancel : x ^ ((N : ℝ) + β.re) * (x⁻¹) ^ ((N : ℝ) + β.re) = 1 := by
      rw [← Real.mul_rpow hx.le (inv_pos.mpr hx).le, mul_inv_cancel₀ hx.ne', Real.one_rpow]
    calc M * x ^ ((N : ℝ) + β.re) * (Real.exp (-v / x) * ((x⁻¹) ^ ((N : ℝ) + β.re) * v ^ ((N : ℝ) + β.re)))
        = M * (Real.exp (-v / x) * ((x ^ ((N : ℝ) + β.re) * (x⁻¹) ^ ((N : ℝ) + β.re)) * v ^ ((N : ℝ) + β.re))) := by ring
      _ = M * (Real.exp (-v / x) * v ^ ((N : ℝ) + β.re)) := by rw [hcancel, one_mul]
  have hint_le :
      ‖∫ v : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) *
          (recipGamma α (v : ℂ) - ∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n)‖ ≤
      M * (x ^ ((N : ℝ) + β.re + 1) * Real.Gamma ((N : ℝ) + β.re + 1)) := by
    have h1 : ‖∫ v : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp (-(v : ℂ) / (x : ℂ)) * ((v : ℂ) ^ β) *
          (recipGamma α (v : ℂ) - ∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n)‖ ≤
        ∫ v : ℝ in Set.Ioi (0 : ℝ), M * (Real.exp (-v / x) * v ^ ((N : ℝ) + β.re)) := by
      refine MeasureTheory.norm_integral_le_of_norm_le hdom_rem ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
      have hvpos : 0 < v := hv
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_ofReal_cpow_of_pos hvpos β]
      have hre : (-(v : ℂ) / (x : ℂ)).re = -v / x := by
        have : -(v : ℂ) / (x : ℂ) = (((-v / x : ℝ)) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [hre]
      calc Real.exp (-v / x) * v ^ β.re *
            ‖recipGamma α (v : ℂ) - ∑ n ∈ Finset.range N, c n * (v : ℂ) ^ n‖
          ≤ Real.exp (-v / x) * v ^ β.re * (M * v ^ N) :=
            mul_le_mul_of_nonneg_left (hrem v hvpos.le) (by positivity)
        _ = M * (Real.exp (-v / x) * v ^ ((N : ℝ) + β.re)) := by
            rw [Real.rpow_add hvpos, Real.rpow_natCast]; ring
    refine h1.trans_eq ?_
    rw [MeasureTheory.integral_const_mul,
      integral_exp_neg_div_mul_rpow (by have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith) hx]
  calc ‖(Complex.Gamma (β + 1))⁻¹‖ * x ^ (-(β.re + 1)) * ‖_‖
      ≤ ‖(Complex.Gamma (β + 1))⁻¹‖ * x ^ (-(β.re + 1)) *
          (M * (x ^ ((N : ℝ) + β.re + 1) * Real.Gamma ((N : ℝ) + β.re + 1))) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = (‖(Complex.Gamma (β + 1))⁻¹‖ * M * Real.Gamma ((N : ℝ) + β.re + 1)) *
          (x ^ (-(β.re + 1)) * x ^ ((N : ℝ) + β.re + 1)) := by ring
    _ = (‖(Complex.Gamma (β + 1))⁻¹‖ * M * Real.Gamma ((N : ℝ) + β.re + 1)) * x ^ N := by
        rw [← Real.rpow_add hx, show -(β.re + 1) + ((N : ℝ) + β.re + 1) = (N : ℝ) by ring,
          Real.rpow_natCast]
    _ ≤ C * x ^ N := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hx.le N)

/-- All Euler derivatives of `volterraLaplace β α` have `eulerPS^[k] (volterraAsympSeries β α)`
as their asymptotic expansion at `0⁺`, proved by 5-line induction via the exact shift identity
`δ(F_β) = (β + 1) * (F_{β + 1} - F_β)`. -/
theorem hasAsympExpAtZero_eulerIter_volterraLaplace (α : ℂ) (k : ℕ) :
    ∀ β : ℂ, -1 < β.re →
      HasAsympExpAtZero (fun x : ℝ => (eulerOpC^[k] (volterraLaplace β α)) (x : ℂ))
        (eulerPS^[k] (volterraAsympSeries β α)) := by
  induction k with
  | zero =>
    intro β hβ
    simpa using hasAsympExpAtZero_volterraLaplace α β hβ
  | succ m ih =>
    intro β hβ
    have heq_fn : ∀ z ∈ rightHalfPlane,
        (eulerOpC^[m + 1] (volterraLaplace β α)) z =
        (β + 1) * ((eulerOpC^[m] (volterraLaplace (β + 1) α)) z -
          (eulerOpC^[m] (volterraLaplace β α)) z) := by
      -- Prove the general linearity of `eulerOpC^[m]` on functions agreeing on `rightHalfPlane`!
      have heuler_congr : ∀ {f g : ℂ → ℂ}, Set.EqOn f g rightHalfPlane →
          Set.EqOn (eulerOpC f) (eulerOpC g) rightHalfPlane := by
        intro f g hfg z hz
        dsimp [eulerOpC]
        congr 1
        have hfeq : f =ᶠ[nhds z] g :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨rightHalfPlane, isOpen_rightHalfPlane.mem_nhds hz, hfg⟩
        exact hfeq.deriv_eq
      have heuler_sub : ∀ {f g : ℂ → ℂ},
          DifferentiableOn ℂ f rightHalfPlane → DifferentiableOn ℂ g rightHalfPlane →
          Set.EqOn (eulerOpC (fun z => f z - g z)) (fun z => eulerOpC f z - eulerOpC g z) rightHalfPlane := by
        intro f g hf hg z hz
        dsimp [eulerOpC]
        have hdf := (hf z hz).differentiableAt (isOpen_rightHalfPlane.mem_nhds hz)
        have hdg := (hg z hz).differentiableAt (isOpen_rightHalfPlane.mem_nhds hz)
        rw [deriv_fun_sub hdf hdg]; ring
      have heuler_cmul : ∀ (c : ℂ) {f : ℂ → ℂ},
          DifferentiableOn ℂ f rightHalfPlane →
          Set.EqOn (eulerOpC (fun z => c * f z)) (fun z => c * eulerOpC f z) rightHalfPlane := by
        intro c f hf z hz
        dsimp [eulerOpC]
        have hdf := (hf z hz).differentiableAt (isOpen_rightHalfPlane.mem_nhds hz)
        rw [deriv_const_mul c hdf]; ring
      have heuler_iter_diff : ∀ (j : ℕ) {f : ℂ → ℂ}, AnalyticOnNhd ℂ f rightHalfPlane →
          AnalyticOnNhd ℂ (eulerOpC^[j] f) rightHalfPlane := by
        intro j
        induction j with
        | zero => intro f hf; simpa using hf
        | succ r ihr =>
          intro f hf
          rw [Function.iterate_succ_apply']
          have hr := ihr hf
          exact analyticOnNhd_id.mul hr.deriv
      have heuler_iter_lin : ∀ (j : ℕ) (c : ℂ) {f g : ℂ → ℂ},
          AnalyticOnNhd ℂ f rightHalfPlane → AnalyticOnNhd ℂ g rightHalfPlane →
          Set.EqOn (eulerOpC^[j] (fun z => c * (f z - g z)))
            (fun z => c * ((eulerOpC^[j] f) z - (eulerOpC^[j] g) z)) rightHalfPlane := by
        intro j c f g hf hg
        induction j with
        | zero => intro z _; simp
        | succ r ihr =>
          intro z hz
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
          have h1 := heuler_congr ihr hz
          have h2 := heuler_cmul c (f := fun w => eulerOpC^[r] f w - eulerOpC^[r] g w)
            ((heuler_iter_diff r hf).differentiableOn.sub
              (heuler_iter_diff r hg).differentiableOn) hz
          have h3 := heuler_sub (heuler_iter_diff r hf).differentiableOn
            (heuler_iter_diff r hg).differentiableOn hz
          dsimp only at h1 h2 h3 ⊢
          rw [h1, h2, h3]
      intro z hz
      rw [Function.iterate_succ_apply]
      have hstep0 : Set.EqOn (eulerOpC (volterraLaplace β α))
          (fun w => (β + 1) * (volterraLaplace (β + 1) α w - volterraLaplace β α w)) rightHalfPlane :=
        fun w hw => eulerOpC_volterraLaplace β α hβ hw
      have hcongr_m : ∀ (j : ℕ) {f g : ℂ → ℂ}, Set.EqOn f g rightHalfPlane →
          Set.EqOn (eulerOpC^[j] f) (eulerOpC^[j] g) rightHalfPlane := by
        intro j
        induction j with
        | zero => intro f g hfg; exact hfg
        | succ r ihr =>
          intro f g hfg w hw
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact heuler_congr (ihr hfg) hw
      rw [hcongr_m m hstep0 hz]
      exact heuler_iter_lin m (β + 1)
        (analyticOnNhd_volterraLaplace (β + 1) α (by simp; linarith))
        (analyticOnNhd_volterraLaplace β α hβ) hz
    -- Power series side: `eulerPS^[m + 1] S_β = C (β + 1) * (eulerPS^[m] S_{β+1} - eulerPS^[m] S_β)`.
    have heq_ps : eulerPS^[m + 1] (volterraAsympSeries β α) =
        PowerSeries.C (β + 1) *
          (eulerPS^[m] (volterraAsympSeries (β + 1) α) - eulerPS^[m] (volterraAsympSeries β α)) := by
      have heulerPS_lin : ∀ (j : ℕ) (c : ℂ) (S T : PowerSeries ℂ),
          eulerPS^[j] (PowerSeries.C c * (S - T)) = PowerSeries.C c * (eulerPS^[j] S - eulerPS^[j] T) := by
        intro j c S T
        induction j with
        | zero => simp
        | succ r ihr =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
            Function.iterate_succ_apply', ihr]
          ext n
          rw [coeff_eulerPS, PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_C_mul, map_sub,
            coeff_eulerPS, coeff_eulerPS]
          ring
      rw [Function.iterate_succ_apply, eulerPS_volterraAsympSeries β α hβ, heulerPS_lin]
    rw [heq_ps]
    refine hasAsympExpAtZero_congr (fun x hx => (heq_fn (x : ℂ) (by simpa [rightHalfPlane] using hx)).symm) ?_
    exact hasAsympExpAtZero_mul (hasAsympExpAtZero_const (β + 1))
      (hasAsympExpAtZero_sub (ih (β + 1) (by simp; linarith)) (ih β hβ))

/-!
### Differential-Algebraicity Transfer on the Integral Domain of Holomorphic Functions on `U`
-/

open scoped Classical in
/-- Extend a function `rightHalfPlane → ℂ` by `0` outside `rightHalfPlane`. -/
private noncomputable def extendU (f : rightHalfPlane → ℂ) (z : ℂ) : ℂ :=
  if hz : z ∈ rightHalfPlane then f ⟨z, hz⟩ else 0

/-- Restrict a function `ℂ → ℂ` to `rightHalfPlane`. -/
private def restrictU (g : ℂ → ℂ) : rightHalfPlane → ℂ := fun z => g z.1

private lemma extendU_restrictU_eqOn (g : ℂ → ℂ) :
    Set.EqOn (extendU (restrictU g)) g rightHalfPlane := by
  intro z hz; simp [extendU, restrictU, hz]

private lemma analyticOnNhd_congr_rightHalfPlane {f g : ℂ → ℂ}
    (hfg : Set.EqOn f g rightHalfPlane) (hf : AnalyticOnNhd ℂ f rightHalfPlane) :
    AnalyticOnNhd ℂ g rightHalfPlane := by
  intro z hz
  refine (hf z hz).congr ?_
  exact Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨rightHalfPlane, isOpen_rightHalfPlane.mem_nhds hz, hfg⟩

/-- The `ℂ`-subalgebra of functions `rightHalfPlane → ℂ` that are holomorphic on `rightHalfPlane`. -/
private noncomputable def HolU : Subalgebra ℂ (rightHalfPlane → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ (extendU f) rightHalfPlane}
  mul_mem' {f g} hf hg := by
    refine analyticOnNhd_congr_rightHalfPlane (f := fun z => extendU f z * extendU g z) ?_ (hf.mul hg)
    intro z hz; simp [extendU, hz]
  one_mem' := by
    refine analyticOnNhd_congr_rightHalfPlane (f := fun _ => (1 : ℂ)) ?_ analyticOnNhd_const
    intro z hz; simp [extendU, hz]
  add_mem' {f g} hf hg := by
    refine analyticOnNhd_congr_rightHalfPlane (f := fun z => extendU f z + extendU g z) ?_ (hf.add hg)
    intro z hz; simp [extendU, hz]
  zero_mem' := by
    refine analyticOnNhd_congr_rightHalfPlane (f := fun _ => (0 : ℂ)) ?_ analyticOnNhd_const
    intro z hz; simp [extendU, hz]
  algebraMap_mem' c := by
    refine analyticOnNhd_congr_rightHalfPlane (f := fun _ => c) ?_ analyticOnNhd_const
    intro z hz; simp [extendU, hz]

private noncomputable def holUMk {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g rightHalfPlane) : HolU :=
  ⟨restrictU g, analyticOnNhd_congr_rightHalfPlane (extendU_restrictU_eqOn g).symm hg⟩

private lemma holUMk_apply {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g rightHalfPlane) (z : rightHalfPlane) :
    (holUMk hg : rightHalfPlane → ℂ) z = g z.1 := rfl

private lemma holU_eq_zero_of_eqOn_pos_reals {f : HolU}
    (hf : ∀ x : ℝ, ∀ hx : 0 < x, (f : rightHalfPlane → ℂ) ⟨(x : ℂ), by simpa [rightHalfPlane] using hx⟩ = 0) :
    f = 0 := by
  ext z
  have h1mem : (1 : ℂ) ∈ rightHalfPlane := by simp [rightHalfPlane]
  have hfreq : ∃ᶠ w in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, extendU f.1 w = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hVopen, h1V, hVU⟩ := hU
    obtain ⟨r, hrpos, hrV⟩ := Metric.isOpen_iff.mp hVopen 1 h1V
    let w : ℂ := ((1 + r / 2 : ℝ) : ℂ)
    have hw_ne : w ≠ 1 := by
      intro h0
      have hre := congr_arg Complex.re h0
      simp only [w, Complex.ofReal_re, Complex.one_re] at hre
      linarith
    have hw_ball : w ∈ Metric.ball (1 : ℂ) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : w - 1 = ((r / 2 : ℝ) : ℂ) := by dsimp [w]; push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hw_pos : 0 < (1 + r / 2 : ℝ) := by positivity
    refine ⟨w, hVU ⟨hrV hw_ball, hw_ne⟩, ?_⟩
    have hwU : w ∈ rightHalfPlane := by simpa [rightHalfPlane, w] using hw_pos
    simp only [extendU, hwU, dite_true]
    exact hf (1 + r / 2) hw_pos
  have hzero := f.2.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_rightHalfPlane
    h1mem hfreq z.2
  simpa [extendU, z.2] using hzero

private instance instIsDomainHolU : IsDomain HolU := by
  have : Nontrivial HolU := by
    refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
    have hval := congr_arg (fun g : HolU => g.1 ⟨1, by simp [rightHalfPlane]⟩) h01
    simp at hval
  have : NoZeroDivisors HolU := by
    constructor
    intro f g hfg
    by_cases hf : f = 0
    · exact Or.inl hf
    · right
      have hex : ∃ z₀ : rightHalfPlane, f.1 z₀ ≠ 0 := by
        by_contra hall; push Not at hall
        exact hf (Subtype.ext (funext hall))
      obtain ⟨z₀, hz₀⟩ := hex
      have hcont : ContinuousAt (extendU f.1) z₀.1 := (f.2 z₀.1 z₀.2).continuousAt
      have hne_ev : ∀ᶠ w in nhds z₀.1, extendU f.1 w ≠ 0 :=
        hcont.eventually_ne (by simpa [extendU, z₀.2] using hz₀)
      have hmem_ev : ∀ᶠ w in nhds z₀.1, w ∈ rightHalfPlane :=
        isOpen_rightHalfPlane.mem_nhds z₀.2
      have hg_ev : extendU g.1 =ᶠ[nhds z₀.1] 0 := by
        filter_upwards [hne_ev, hmem_ev] with w hwne hwU
        have hmul0 : f.1 ⟨w, hwU⟩ * g.1 ⟨w, hwU⟩ = 0 :=
          congr_arg (fun h : HolU => h.1 ⟨w, hwU⟩) hfg
        have hfne : f.1 ⟨w, hwU⟩ ≠ 0 := by simpa [extendU, hwU] using hwne
        have hg0 : g.1 ⟨w, hwU⟩ = 0 := (mul_eq_zero.mp hmul0).resolve_left hfne
        simpa [extendU, hwU] using hg0
      have hzero := g.2.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_rightHalfPlane z₀.2 hg_ev
      ext z
      simpa [extendU, z.2] using hzero z.2
  exact NoZeroDivisors.to_isDomain HolU

/-- The Euler derivation `δ_U f(z) = z * f'(z)` on `HolU`. -/
private noncomputable def holUEuler (f : HolU) : HolU :=
  holUMk (analyticOnNhd_id.mul f.2.deriv)

private lemma holUEuler_mk {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g rightHalfPlane) :
    holUEuler (holUMk hg) = holUMk (analyticOnNhd_id.mul hg.deriv) := by
  ext z
  simp only [holUEuler, holUMk_apply]
  congr 1
  have heq : extendU (holUMk hg).1 =ᶠ[nhds z.1] g :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨rightHalfPlane, isOpen_rightHalfPlane.mem_nhds z.2, extendU_restrictU_eqOn g⟩
  exact heq.deriv_eq

private lemma holUEuler_add (f g : HolU) : holUEuler (f + g) = holUEuler f + holUEuler g := by
  ext z
  have heq : extendU (f + g).1 =ᶠ[nhds z.1] fun w => extendU f.1 w + extendU g.1 w :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨rightHalfPlane, isOpen_rightHalfPlane.mem_nhds z.2, fun w hw => by simp [extendU, hw]⟩
  change z.1 * deriv (extendU (f + g).1) z.1 =
    z.1 * deriv (extendU f.1) z.1 + z.1 * deriv (extendU g.1) z.1
  rw [heq.deriv_eq, deriv_fun_add (f.2 z.1 z.2).differentiableAt (g.2 z.1 z.2).differentiableAt]
  ring

private lemma holUEuler_mul (f g : HolU) :
    holUEuler (f * g) = holUEuler f * g + f * holUEuler g := by
  ext z
  have heq : extendU (f * g).1 =ᶠ[nhds z.1] fun w => extendU f.1 w * extendU g.1 w :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨rightHalfPlane, isOpen_rightHalfPlane.mem_nhds z.2, fun w hw => by simp [extendU, hw]⟩
  change z.1 * deriv (extendU (f * g).1) z.1 =
    z.1 * deriv (extendU f.1) z.1 * g.1 z + f.1 z * (z.1 * deriv (extendU g.1) z.1)
  rw [heq.deriv_eq, deriv_fun_mul (f.2 z.1 z.2).differentiableAt (g.2 z.1 z.2).differentiableAt]
  simp only [extendU, z.2, dite_true]
  ring

private lemma holUEuler_sub (f g : HolU) : holUEuler (f - g) = holUEuler f - holUEuler g := by
  have h := holUEuler_add (f - g) g
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private lemma holUEuler_neg (f : HolU) : holUEuler (-f) = -holUEuler f := by
  have h := holUEuler_sub 0 f
  have h0 : holUEuler 0 = 0 := by
    have hadd := holUEuler_add 0 0
    rw [add_zero] at hadd
    linear_combination -hadd
  rw [zero_sub, h0, zero_sub] at h
  exact h

private lemma holUEuler_C (c : ℂ) : holUEuler (algebraMap ℂ HolU c) = 0 := by
  ext z
  simp only [holUEuler, holUMk_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
  have heq : extendU (algebraMap ℂ HolU c).1 =ᶠ[nhds z.1] fun _ => c :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨rightHalfPlane, isOpen_rightHalfPlane.mem_nhds z.2, fun w hw => by simp [extendU, hw]⟩
  rw [heq.deriv_eq, deriv_const, mul_zero]

/-- Embedding `ℂ[X] →+* HolU` sending `p` to `z ↦ p.eval z`. -/
private noncomputable def polyToHolU : Polynomial ℂ →+* HolU :=
  Polynomial.eval₂RingHom (algebraMap ℂ HolU) (holUMk analyticOnNhd_id)

private lemma polyToHolU_apply (p : Polynomial ℂ) (z : rightHalfPlane) :
    (polyToHolU p : rightHalfPlane → ℂ) z = p.eval z.1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
    simp [polyToHolU, Polynomial.eval₂_monomial, holUMk_apply]

private lemma polyToHolU_injective : Function.Injective polyToHolU := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hroots : ∀ n : ℕ, p.IsRoot (((n + 1 : ℕ) : ℂ)) := by
    intro n
    have hz : (((n + 1 : ℕ) : ℂ)) ∈ rightHalfPlane := by
      simp only [rightHalfPlane, Set.mem_ofPred_eq, Complex.natCast_re]
      exact Nat.cast_pos.mpr (Nat.succ_pos n)
    have hval := congr_arg (fun f : HolU => f.1 ⟨_, hz⟩) hp
    simpa [polyToHolU_apply, Polynomial.IsRoot] using hval
  by_contra hne
  have hfin : (p.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
  have hinf : Set.Infinite (Set.range fun n : ℕ => (((n + 1 : ℕ) : ℂ))) := by
    refine Set.infinite_range_of_injective fun a b hab => ?_
    have : a + 1 = b + 1 := Nat.cast_injective hab
    omega
  refine hinf (hfin.subset ?_)
  rintro _ ⟨n, rfl⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
  exact hroots n

private lemma holUEuler_poly (p : Polynomial ℂ) :
    holUEuler (polyToHolU p) = polyToHolU (polyEuler p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, holUEuler_add, hp, hq]
    have hpe : polyEuler (p + q) = polyEuler p + polyEuler q := by
      simp [polyEuler, mul_add]
    rw [hpe, map_add]
  | monomial n a =>
    ext z
    have hmon_eq : polyToHolU (Polynomial.monomial n a) =
        holUMk ((analyticOnNhd_const (v := a)).mul (analyticOnNhd_id.pow n)) := by
      ext w
      simp [polyToHolU_apply, holUMk_apply, Polynomial.eval_monomial]
    rw [hmon_eq, holUEuler_mk]
    simp only [holUMk_apply, polyToHolU_apply]
    have hd : deriv (fun w : ℂ => a * w ^ n) z.1 = a * ((n : ℂ) * z.1 ^ (n - 1)) := by
      have h1 : HasDerivAt (fun w : ℂ => a * w ^ n) (a * ((n : ℂ) * z.1 ^ (n - 1))) z.1 :=
        (hasDerivAt_pow n z.1).const_mul a
      exact h1.deriv
    change z.1 * deriv (fun w : ℂ => a * w ^ n) z.1 = _
    rw [hd, polyEuler, Polynomial.derivative_monomial, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_monomial]
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]
      ring

/-- The fraction field of `HolU`. -/
private abbrev FracHolU := FractionRing HolU

/-- Extension of the Euler derivation `holUEuler` to `FracHolU` via the quotient rule. -/
private noncomputable def fracEuler : FracHolU → FracHolU :=
  fun x => Localization.liftOn x
    (fun a b => algebraMap HolU FracHolU (holUEuler a * b.1 - a * holUEuler b.1) /
      (algebraMap HolU FracHolU b.1) ^ 2)
    (fun {a₁ a₂ b₁ b₂} hr => by
      rcases Localization.r_iff_exists.mp hr with ⟨c, hc⟩
      have hcb : a₁ * b₂.1 = a₂ * b₁.1 := by
        have hcne : (c : HolU) ≠ 0 := nonZeroDivisors.ne_zero c.2
        have : (c : HolU) * (a₁ * b₂.1) = (c : HolU) * (a₂ * b₁.1) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hc
        exact mul_left_cancel₀ hcne this
      have hb₁_ne : algebraMap HolU FracHolU b₁.1 ≠ 0 :=
        map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective HolU FracHolU) b₁.2
      have hb₂_ne : algebraMap HolU FracHolU b₂.1 ≠ 0 :=
        map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective HolU FracHolU) b₂.2
      rw [div_eq_div_iff (pow_ne_zero 2 hb₁_ne) (pow_ne_zero 2 hb₂_ne)]
      simp only [← map_pow, ← map_mul]
      congr 1
      have hder := congr_arg holUEuler hcb
      rw [holUEuler_mul, holUEuler_mul] at hder
      linear_combination b₁.1 * b₂.1 * hder - (holUEuler b₁.1 * b₂.1 + b₁.1 * holUEuler b₂.1) * hcb)

private lemma fracEuler_mk (a : HolU) (b : nonZeroDivisors HolU) :
    fracEuler (Localization.mk a b) =
      algebraMap HolU FracHolU (holUEuler a * b.1 - a * holUEuler b.1) /
        (algebraMap HolU FracHolU b.1) ^ 2 := rfl

private lemma fracEuler_algebraMap (a : HolU) :
    fracEuler (algebraMap HolU FracHolU a) = algebraMap HolU FracHolU (holUEuler a) := by
  have h1 : algebraMap HolU FracHolU a = Localization.mk a 1 := Localization.mk_one_eq_algebraMap a |>.symm
  rw [h1, fracEuler_mk]
  have h10 : holUEuler (1 : HolU) = 0 := by
    simpa using holUEuler_C 1
  simp [h10]

private lemma fracEuler_add (x y : FracHolU) : fracEuler (x + y) = fracEuler x + fracEuler y := by
  induction x using Localization.induction_on with | H p =>
  induction y using Localization.induction_on with | H q =>
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  rw [Localization.add_mk, fracEuler_mk, fracEuler_mk, fracEuler_mk]
  have hb : algebraMap HolU FracHolU b.1 ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective HolU FracHolU) b.2
  have hd : algebraMap HolU FracHolU d.1 ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective HolU FracHolU) d.2
  simp only [Submonoid.coe_mul, holUEuler_add, holUEuler_mul, map_add, map_sub, map_mul]
  field_simp [hb, hd]
  ring

private lemma fracEuler_mul (x y : FracHolU) :
    fracEuler (x * y) = fracEuler x * y + x * fracEuler y := by
  induction x using Localization.induction_on with | H p =>
  induction y using Localization.induction_on with | H q =>
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  rw [Localization.mk_mul, fracEuler_mk, fracEuler_mk, fracEuler_mk]
  have hb : algebraMap HolU FracHolU b.1 ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective HolU FracHolU) b.2
  have hd : algebraMap HolU FracHolU d.1 ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective HolU FracHolU) d.2
  have hmk1 : Localization.mk a b = algebraMap HolU FracHolU a / algebraMap HolU FracHolU b.1 := by
    rw [Localization.mk_eq_mk']; exact IsFractionRing.mk'_eq_div b
  have hmk2 : Localization.mk c d = algebraMap HolU FracHolU c / algebraMap HolU FracHolU d.1 := by
    rw [Localization.mk_eq_mk']; exact IsFractionRing.mk'_eq_div d
  rw [hmk1, hmk2]
  simp only [Submonoid.coe_mul, holUEuler_mul, map_add, map_sub, map_mul]
  field_simp [hb, hd]
  ring

private lemma fracEuler_zero : fracEuler 0 = 0 := by
  have h0 : holUEuler (0 : HolU) = 0 := by
    have hadd := holUEuler_add 0 0; rw [add_zero] at hadd; linear_combination -hadd
  have h := fracEuler_algebraMap 0
  simpa [h0] using h

private lemma fracEuler_one : fracEuler 1 = 0 := by
  have h := fracEuler_algebraMap 1
  have h1 : holUEuler (1 : HolU) = 0 := by simpa using holUEuler_C 1
  simpa [h1] using h

private lemma fracEuler_sub (x y : FracHolU) : fracEuler (x - y) = fracEuler x - fracEuler y := by
  have h := fracEuler_add (x - y) y
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private lemma fracEuler_neg (x : FracHolU) : fracEuler (-x) = -fracEuler x := by
  have h := fracEuler_sub 0 x
  rw [zero_sub, fracEuler_zero, zero_sub] at h
  exact h

private lemma fracEuler_inv (x : FracHolU) : fracEuler x⁻¹ = -fracEuler x / x ^ 2 := by
  by_cases hx : x = 0
  · subst hx; simp [fracEuler_zero]
  · have h := fracEuler_mul x x⁻¹
    rw [mul_inv_cancel₀ hx, fracEuler_one] at h
    have h1 : x * fracEuler x⁻¹ = -(fracEuler x * x⁻¹) := eq_neg_of_add_eq_zero_right h.symm
    have h2 : x ^ 2 * fracEuler x⁻¹ = -fracEuler x := by
      calc x ^ 2 * fracEuler x⁻¹ = x * (x * fracEuler x⁻¹) := by ring
        _ = x * -(fracEuler x * x⁻¹) := by rw [h1]
        _ = -(fracEuler x * (x * x⁻¹)) := by ring
        _ = -fracEuler x := by rw [mul_inv_cancel₀ hx, mul_one]
    rw [eq_div_iff (pow_ne_zero 2 hx), mul_comm]; exact h2

private lemma fracEuler_div (x y : FracHolU) :
    fracEuler (x / y) = (fracEuler x * y - x * fracEuler y) / y ^ 2 := by
  by_cases hy : y = 0
  · subst hy; simp [fracEuler_zero]
  · rw [div_eq_mul_inv, fracEuler_mul, fracEuler_inv]
    field_simp [hy]
    ring

/-- The rational-function field `K = FractionRing (Polynomial ℂ)`. -/
private abbrev RatPoly := FractionRing (Polynomial ℂ)

/-- The canonical field embedding `RatPoly →+* FracHolU`. -/
private noncomputable def ratPolyToFrac : RatPoly →+* FracHolU :=
  IsFractionRing.lift (g := (algebraMap HolU FracHolU).comp polyToHolU)
    ((IsFractionRing.injective HolU FracHolU).comp polyToHolU_injective)

private lemma ratPolyToFrac_algebraMap (p : Polynomial ℂ) :
    ratPolyToFrac (algebraMap (Polynomial ℂ) RatPoly p) =
      algebraMap HolU FracHolU (polyToHolU p) :=
  IsFractionRing.lift_algebraMap _ p

private lemma fracEuler_mem_ratPolyRange (q : RatPoly) :
    ∃ q' : RatPoly, fracEuler (ratPolyToFrac q) = ratPolyToFrac q' := by
  induction q using Localization.induction_on with | H pq =>
  rcases pq with ⟨a, b⟩
  have hmk : Localization.mk a b =
      algebraMap (Polynomial ℂ) RatPoly a / algebraMap (Polynomial ℂ) RatPoly b.1 := by
    rw [Localization.mk_eq_mk']; exact IsFractionRing.mk'_eq_div b
  rw [hmk, map_div₀, ratPolyToFrac_algebraMap, ratPolyToFrac_algebraMap, fracEuler_div,
    fracEuler_algebraMap, fracEuler_algebraMap, holUEuler_poly, holUEuler_poly]
  refine ⟨(algebraMap (Polynomial ℂ) RatPoly (polyEuler a) * algebraMap (Polynomial ℂ) RatPoly b.1 -
      algebraMap (Polynomial ℂ) RatPoly a * algebraMap (Polynomial ℂ) RatPoly (polyEuler b.1)) /
      (algebraMap (Polynomial ℂ) RatPoly b.1) ^ 2, ?_⟩
  simp only [map_div₀, map_sub, map_mul, map_pow, ratPolyToFrac_algebraMap]

/-! ### Multivariable chain rule for `fracEuler` and transcendence-degree elimination -/

private noncomputable def derivCoeffMv {m : ℕ} (P : MvPolynomial (Fin (m + 1)) FracHolU) :
    MvPolynomial (Fin (m + 1)) FracHolU :=
  ∑ d ∈ P.support, MvPolynomial.monomial d (fracEuler (P.coeff d))

private lemma derivCoeffMv_coeff {m : ℕ} (R : MvPolynomial (Fin (m + 1)) FracHolU)
    (d : Fin (m + 1) →₀ ℕ) :
    (derivCoeffMv R).coeff d = fracEuler (R.coeff d) := by
  dsimp only [derivCoeffMv]
  rw [← MvPolynomial.lcoeff_apply, map_sum]
  simp only [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
  by_cases hd : d ∈ R.support
  · rw [Finset.sum_eq_single d]
    · simp
    · intro s _ hne; simp [hne]
    · intro h; exact absurd hd h
  · have h0 : R.coeff d = 0 := by rwa [MvPolynomial.mem_support_iff, not_not] at hd
    rw [h0, fracEuler_zero]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hne : s ≠ d := fun h => hd (h ▸ hs)
    simp [hne]

private lemma derivCoeffMv_C {m : ℕ} (c : FracHolU) :
    derivCoeffMv (m := m) (MvPolynomial.C c) = MvPolynomial.C (fracEuler c) := by
  ext d
  rw [derivCoeffMv_coeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs
  · rfl
  · exact fracEuler_zero

private lemma derivCoeffMv_add {m : ℕ} (P Q : MvPolynomial (Fin (m + 1)) FracHolU) :
    derivCoeffMv (P + Q) = derivCoeffMv P + derivCoeffMv Q := by
  ext d
  rw [derivCoeffMv_coeff, ← MvPolynomial.lcoeff_apply, map_add,
    MvPolynomial.lcoeff_apply, MvPolynomial.lcoeff_apply, fracEuler_add,
    ← derivCoeffMv_coeff, ← derivCoeffMv_coeff,
    ← MvPolynomial.lcoeff_apply, ← MvPolynomial.lcoeff_apply, ← map_add, MvPolynomial.lcoeff_apply]

private lemma derivCoeffMv_mul_X {m : ℕ} (P : MvPolynomial (Fin (m + 1)) FracHolU)
    (i : Fin (m + 1)) :
    derivCoeffMv (P * MvPolynomial.X i) = derivCoeffMv P * MvPolynomial.X i := by
  ext d
  rw [derivCoeffMv_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs with h
  · exact (derivCoeffMv_coeff P (d - Finsupp.single i 1)).symm
  · exact fracEuler_zero

private lemma fracEuler_mvPoly_eval {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) FracHolU) (Φ : Fin (m + 1) → FracHolU) :
    fracEuler (MvPolynomial.eval Φ P) =
      MvPolynomial.eval Φ (derivCoeffMv P) +
      ∑ i : Fin (m + 1), MvPolynomial.eval Φ (MvPolynomial.pderiv i P) * fracEuler (Φ i) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [derivCoeffMv_C]
  | add P Q hP hQ =>
    rw [RingHom.map_add, fracEuler_add, derivCoeffMv_add, RingHom.map_add, hP, hQ]
    have hsum : ∑ i : Fin (m + 1), MvPolynomial.eval Φ (MvPolynomial.pderiv i (P + Q)) * fracEuler (Φ i) =
        (∑ i : Fin (m + 1), MvPolynomial.eval Φ (MvPolynomial.pderiv i P) * fracEuler (Φ i)) +
        (∑ i : Fin (m + 1), MvPolynomial.eval Φ (MvPolynomial.pderiv i Q) * fracEuler (Φ i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, RingHom.map_add, add_mul]
    rw [hsum]; ring
  | mul_X P j hP =>
    rw [RingHom.map_mul, MvPolynomial.eval_X, fracEuler_mul, derivCoeffMv_mul_X,
      RingHom.map_mul, MvPolynomial.eval_X, hP]
    have hsplit : ∑ i : Fin (m + 1),
        MvPolynomial.eval Φ (MvPolynomial.pderiv i (P * MvPolynomial.X j)) * fracEuler (Φ i) =
        MvPolynomial.eval Φ P * fracEuler (Φ j) +
        (∑ i : Fin (m + 1), MvPolynomial.eval Φ (MvPolynomial.pderiv i P) * fracEuler (Φ i)) * Φ j := by
      have hterm : ∀ i : Fin (m + 1),
          MvPolynomial.eval Φ (MvPolynomial.pderiv i (P * MvPolynomial.X j)) * fracEuler (Φ i) =
          (if j = i then MvPolynomial.eval Φ P * fracEuler (Φ i) else 0) +
          (MvPolynomial.eval Φ (MvPolynomial.pderiv i P) * fracEuler (Φ i)) * Φ j := by
        intro i
        rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, smul_eq_mul,
          RingHom.map_add, RingHom.map_mul, RingHom.map_mul, MvPolynomial.eval_X]
        split_ifs <;> simp <;> ring
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
      congr 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsplit]; ring

private noncomputable instance instAlgebraRatPolyFracHolU : Algebra RatPoly FracHolU :=
  ratPolyToFrac.toAlgebra

/-- **Transcendence-Degree Elimination Lemma on `(FracHolU, fracEuler)`:**
If `g₁, g₂, g₃ ∈ FracHolU` generate a `fracEuler`-stable field `E₀ = K(g₁, g₂, g₃)` over
`K = FractionRing (Polynomial ℂ)` and `h ∈ FracHolU` satisfies a nonzero polynomial ADE over `E₀`,
then `h` satisfies a nonzero polynomial Euler ADE over `Polynomial ℂ`. -/
private lemma exists_nonzero_poly_ade_of_adjoin_ade {r : ℕ}
    (g₁ g₂ g₃ h : FracHolU)
    (hg₁ : fracEuler g₁ ∈ IntermediateField.adjoin RatPoly ({g₁, g₂, g₃} : Set FracHolU))
    (hg₂ : fracEuler g₂ ∈ IntermediateField.adjoin RatPoly ({g₁, g₂, g₃} : Set FracHolU))
    (hg₃ : fracEuler g₃ ∈ IntermediateField.adjoin RatPoly ({g₁, g₂, g₃} : Set FracHolU))
    (P_E : MvPolynomial (Fin (r + 1)) FracHolU)
    (hP_ne : P_E ≠ 0)
    (hP_coeffs : ∀ d ∈ P_E.support,
      P_E.coeff d ∈ IntermediateField.adjoin RatPoly ({g₁, g₂, g₃} : Set FracHolU))
    (hP_eval : MvPolynomial.eval (fun i : Fin (r + 1) => fracEuler^[i.1] h) P_E = 0) :
    ∃ (N : ℕ) (Q : MvPolynomial (Fin (N + 1)) (Polynomial ℂ)),
      Q ≠ 0 ∧
      MvPolynomial.eval₂ (ratPolyToFrac.comp (algebraMap (Polynomial ℂ) RatPoly))
        (fun i : Fin (N + 1) => fracEuler^[i.1] h) Q = 0 := by
  let E₀ : IntermediateField RatPoly FracHolU := IntermediateField.adjoin RatPoly {g₁, g₂, g₃}
  -- First show `E₀` is closed under `fracEuler`!
  have hE₀_closed : ∀ y ∈ E₀, fracEuler y ∈ E₀ := by
    let E₀_cl : IntermediateField RatPoly FracHolU :=
      { carrier := {y | y ∈ E₀ ∧ fracEuler y ∈ E₀}
        mul_mem' := fun {a b} ⟨ha, hda⟩ ⟨hb, hdb⟩ =>
          ⟨E₀.mul_mem ha hb, by rw [fracEuler_mul]; exact E₀.add_mem (E₀.mul_mem hda hb) (E₀.mul_mem ha hdb)⟩
        one_mem' := ⟨E₀.one_mem, by rw [fracEuler_one]; exact E₀.zero_mem⟩
        add_mem' := fun {a b} ⟨ha, hda⟩ ⟨hb, hdb⟩ =>
          ⟨E₀.add_mem ha hb, by rw [fracEuler_add]; exact E₀.add_mem hda hdb⟩
        zero_mem' := ⟨E₀.zero_mem, by rw [fracEuler_zero]; exact E₀.zero_mem⟩
        inv_mem' := fun {a} ⟨ha, hda⟩ =>
          ⟨E₀.inv_mem ha, by
            rw [fracEuler_inv]
            exact E₀.div_mem (E₀.neg_mem hda) (E₀.pow_mem ha 2)⟩
        algebraMap_mem' := fun q => by
          obtain ⟨q', hq'⟩ := fracEuler_mem_ratPolyRange q
          exact ⟨E₀.algebraMap_mem q, hq' ▸ E₀.algebraMap_mem q'⟩ }
    have hle : E₀ ≤ E₀_cl := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨IntermediateField.subset_adjoin _ _ (by simp), hg₁⟩
      · exact ⟨IntermediateField.subset_adjoin _ _ (by simp), hg₂⟩
      · exact ⟨IntermediateField.subset_adjoin _ _ (by simp), hg₃⟩
    intro y hy
    exact (hle hy).2
  -- Minimize order `m`, then `degreeOf (Fin.last m)` of a nonzero `F` with coefficients in `E₀`:
  let HasOrd : ℕ → Prop := fun m =>
    ∃ F : MvPolynomial (Fin (m + 1)) FracHolU,
      F ≠ 0 ∧ (∀ d ∈ F.support, F.coeff d ∈ E₀) ∧
      MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) F = 0
  have hExOrd : ∃ m, HasOrd m := ⟨r, P_E, hP_ne, hP_coeffs, hP_eval⟩
  classical
  let m : ℕ := Nat.find hExOrd
  have hm_spec : HasOrd m := Nat.find_spec hExOrd
  have hm_min : ∀ m' < m, ¬ HasOrd m' := fun m' hlt => Nat.find_min hExOrd hlt
  let HasDeg : ℕ → Prop := fun D =>
    ∃ F : MvPolynomial (Fin (m + 1)) FracHolU,
      F ≠ 0 ∧ (∀ d ∈ F.support, F.coeff d ∈ E₀) ∧
      MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) F = 0 ∧
      F.degreeOf (Fin.last m) = D
  have hExDeg : ∃ D, HasDeg D := by
    obtain ⟨F, hFne, hFc, hFev⟩ := hm_spec
    exact ⟨F.degreeOf (Fin.last m), F, hFne, hFc, hFev, rfl⟩
  let D : ℕ := Nat.find hExDeg
  obtain ⟨F, hFne, hFc, hFev, hFdeg⟩ := Nat.find_spec hExDeg
  have hD_min : ∀ D' < D, ¬ HasDeg D' := fun D' hlt => Nat.find_min hExDeg hlt
  -- Show `D ≥ 1`:
  have hD_pos : 1 ≤ D := by
    by_contra hD0
    have hD_eq0 : D = 0 := by omega
    have hFdeg0 : F.degreeOf (Fin.last m) = 0 := by
      change F.degreeOf (Fin.last m) = D at hFdeg
      rw [hFdeg, hD_eq0]
    rcases m with _ | m'
    · -- `m = 0` and `degreeOf 0 F = 0`, so `F = C c` with `c ≠ 0`, contradicting `eval F = 0`!
      have hFconst : F = MvPolynomial.C (F.coeff 0) := by
        ext d
        by_cases hd : d = 0
        · subst hd; simp
        · rw [MvPolynomial.coeff_C, ite_eq_right_iff.mpr (fun h => absurd h.symm hd)]
          by_contra hne0
          have hmem : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hne0
          have hdeg_le : d (Fin.last 0) ≤ F.degreeOf (Fin.last 0) :=
            MvPolynomial.degreeOf_le_iff.mp le_rfl d hmem
          rw [hFdeg0] at hdeg_le
          have hd0 : d = 0 := by
            ext i; fin_cases i
            simp only [Finsupp.coe_zero, Pi.zero_apply]
            exact Nat.eq_zero_of_le_zero hdeg_le
          exact hd hd0
      have hc0 : F.coeff 0 = 0 := by
        rw [hFconst, MvPolynomial.eval_C] at hFev; exact hFev
      rw [hc0, map_zero] at hFconst
      exact hFne hFconst
    · -- `m = m' + 1` and `degreeOf (Fin.last (m' + 1)) F = 0`: drop last variable, contradicts `hm_min`!
      let F' : MvPolynomial (Fin (m' + 1)) FracHolU :=
        MvPolynomial.eval₂ MvPolynomial.C
          (fun i : Fin (m' + 2) => if h : i.1 < m' + 1 then MvPolynomial.X ⟨i.1, h⟩ else 0) F
      have hF'_eval : MvPolynomial.eval (fun i : Fin (m' + 1) => fracEuler^[i.1] h) F' = 0 := by
        rw [← hFev]
        dsimp [F']
        have hcomp : ∀ P : MvPolynomial (Fin (m' + 2)) FracHolU,
            (∀ d ∈ P.support, d (Fin.last (m' + 1)) = 0) →
            MvPolynomial.eval (fun i : Fin (m' + 1) => fracEuler^[i.1] h)
              (MvPolynomial.eval₂ MvPolynomial.C
                (fun i : Fin (m' + 2) => if h : i.1 < m' + 1 then MvPolynomial.X ⟨i.1, h⟩ else 0) P) =
            MvPolynomial.eval (fun i : Fin (m' + 2) => fracEuler^[i.1] h) P := by
          intro P hP0
          rw [MvPolynomial.eval₂_eq']
          change MvPolynomial.eval₂ (RingHom.id FracHolU) (fun i : Fin (m' + 1) => fracEuler^[i.1] h) _ = _
          rw [MvPolynomial.eval₂_sum, MvPolynomial.eval_eq']
          refine Finset.sum_congr rfl fun d hd => ?_
          simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply,
            MvPolynomial.eval₂_prod, MvPolynomial.eval₂_pow]
          congr 1
          have hlast := hP0 d hd
          conv_lhs => rw [Fin.prod_univ_castSucc]
          conv_rhs => rw [Fin.prod_univ_castSucc]
          rw [hlast, pow_zero, pow_zero, mul_one, mul_one]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [Fin.val_castSucc, i.2, dite_true, Fin.eta, MvPolynomial.eval₂_X]
        have hF0 : ∀ d ∈ F.support, d (Fin.last (m' + 1)) = 0 := fun d hd =>
          Nat.eq_zero_of_le_zero (MvPolynomial.degreeOf_le_iff.mp hFdeg0.le d hd)
        exact hcomp F hF0
      have hF'_ne : F' ≠ 0 := by
        have hback : MvPolynomial.rename Fin.castSucc F' = F := by
          dsimp [F']
          rw [MvPolynomial.eval₂_eq', map_sum]
          conv_rhs => rw [MvPolynomial.as_sum (p := F)]
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
            map_mul, MvPolynomial.rename_C, map_prod]
          congr 1
          have hlast : d (Fin.last (m' + 1)) = 0 :=
            Nat.eq_zero_of_le_zero (MvPolynomial.degreeOf_le_iff.mp hFdeg0.le d hd)
          conv_lhs => rw [Fin.prod_univ_castSucc]
          conv_rhs => rw [Fin.prod_univ_castSucc]
          simp only [hlast, pow_zero, map_pow, map_one, mul_one]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [Fin.val_castSucc, i.2, dite_true, Fin.eta, MvPolynomial.rename_X]
        intro h0; rw [h0, map_zero] at hback; exact hFne hback.symm
      have hF'_coeffs : ∀ d ∈ F'.support, F'.coeff d ∈ E₀ := by
        intro d hd
        have hback : MvPolynomial.rename Fin.castSucc F' = F := by
          dsimp [F']
          rw [MvPolynomial.eval₂_eq', map_sum]
          conv_rhs => rw [MvPolynomial.as_sum (p := F)]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
            map_mul, MvPolynomial.rename_C, map_prod]
          congr 1
          have hlast : s (Fin.last (m' + 1)) = 0 :=
            Nat.eq_zero_of_le_zero (MvPolynomial.degreeOf_le_iff.mp hFdeg0.le s hs)
          conv_lhs => rw [Fin.prod_univ_castSucc]
          conv_rhs => rw [Fin.prod_univ_castSucc]
          simp only [hlast, pow_zero, map_pow, map_one, mul_one]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [Fin.val_castSucc, i.2, dite_true, Fin.eta, MvPolynomial.rename_X]
        have hcoeff_eq : F.coeff (Finsupp.mapDomain Fin.castSucc d) = F'.coeff d := by
          rw [← hback, MvPolynomial.coeff_rename_mapDomain _ (Fin.castSucc_injective (m' + 1))]
        rw [← hcoeff_eq]
        exact hFc _ (MvPolynomial.mem_support_iff.mpr (by rw [hcoeff_eq]; exact MvPolynomial.mem_support_iff.mp hd))
      exact hm_min m' (Nat.lt_succ_self m') ⟨F', hF'_ne, hF'_coeffs, hF'_eval⟩
  -- Hence `(pderiv (Fin.last m) F)` is nonzero, has coefficients in `E₀`, and has strictly smaller `degreeOf`,
  -- so its evaluation at `(h, ..., δ^m h)` is NONZERO!
  have hpderiv_ne0 : MvPolynomial.pderiv (Fin.last m) F ≠ 0 := by
    obtain ⟨d, hd, hdeg_eq⟩ : ∃ d ∈ F.support, d (Fin.last m) = D := by
      have hpos_deg : 0 < F.degreeOf (Fin.last m) := by omega
      rw [MvPolynomial.degreeOf_eq_sup] at hFdeg
      have hne_supp : F.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hFne (MvPolynomial.support_eq_empty.mp h0)
      obtain ⟨d, hd, hmax⟩ := Finset.exists_mem_eq_sup F.support hne_supp (fun s => s (Fin.last m))
      exact ⟨d, hd, by rw [← hmax, hFdeg]⟩
    intro h0
    have hc0 := congr_arg
      (fun q : MvPolynomial (Fin (m + 1)) FracHolU => q.coeff (d - Finsupp.single (Fin.last m) 1)) h0
    rw [AddMonoidAlgebra.coeff_zero, MvPolynomial.coeff_pderiv] at hc0
    have hadd : d - Finsupp.single (Fin.last m) 1 + Finsupp.single (Fin.last m) 1 = d := by
      refine tsub_add_cancel_of_le ?_
      rw [Finsupp.single_le_iff]; omega
    rw [hadd] at hc0
    have hDne : ((d (Fin.last m) : ℕ) : FracHolU) ≠ 0 := by
      rw [← map_natCast (algebraMap ℂ FracHolU)]
      intro hc
      have h2 := (map_eq_zero_iff _ (algebraMap ℂ FracHolU).injective).mp hc
      exact Nat.cast_ne_zero.mpr (by omega) h2
    have hFcoeff_ne : F.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hd_sub : ((d - Finsupp.single (Fin.last m) (1 : ℕ)) (Fin.last m) + 1 : ℕ) = d (Fin.last m) := by
      simp; omega
    have hcast : (((d - Finsupp.single (Fin.last m) (1 : ℕ)) (Fin.last m) : ℕ) : FracHolU) + 1 =
        ((d (Fin.last m) : ℕ) : FracHolU) := by
      rw [← Nat.cast_succ ((d - Finsupp.single (Fin.last m) (1 : ℕ)) (Fin.last m))]
      exact congr_arg Nat.cast hd_sub
    rw [hcast] at hc0
    exact mul_ne_zero hFcoeff_ne hDne hc0
  have hpderiv_coeffs : ∀ d ∈ (MvPolynomial.pderiv (Fin.last m) F).support,
      (MvPolynomial.pderiv (Fin.last m) F).coeff d ∈ E₀ := by
    intro d hd
    rw [MvPolynomial.coeff_pderiv]
    have hmem : d + Finsupp.single (Fin.last m) 1 ∈ F.support := by
      rw [MvPolynomial.mem_support_iff] at hd ⊢
      rw [MvPolynomial.coeff_pderiv] at hd
      intro h0; rw [h0, zero_mul] at hd; exact hd rfl
    exact E₀.mul_mem (hFc _ hmem) (E₀.add_mem
      (by rw [← map_natCast (algebraMap RatPoly FracHolU)]; exact E₀.algebraMap_mem _) E₀.one_mem)
  have hpderiv_deg : (MvPolynomial.pderiv (Fin.last m) F).degreeOf (Fin.last m) < D := by
    rw [MvPolynomial.degreeOf_eq_sup]
    have hFdegD : F.degreeOf (Fin.last m) = D := hFdeg
    have hle : (MvPolynomial.pderiv (Fin.last m) F).support.sup (fun s => s (Fin.last m)) ≤ D - 1 := by
      refine Finset.sup_le fun d hd => ?_
      have hmem : d + Finsupp.single (Fin.last m) 1 ∈ F.support := by
        rw [MvPolynomial.mem_support_iff] at hd ⊢
        rw [MvPolynomial.coeff_pderiv] at hd
        intro h0; rw [h0, zero_mul] at hd; exact hd rfl
      have hleD : (d + Finsupp.single (Fin.last m) (1 : ℕ)) (Fin.last m) ≤ D := by
        rw [← hFdegD]; exact MvPolynomial.degreeOf_le_iff.mp le_rfl _ hmem
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hleD
      omega
    omega
  have hpderiv_eval_ne :
      MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h)
        (MvPolynomial.pderiv (Fin.last m) F) ≠ 0 := by
    intro h0
    exact hD_min _ hpderiv_deg ⟨MvPolynomial.pderiv (Fin.last m) F, hpderiv_ne0, hpderiv_coeffs, h0, rfl⟩
  -- Build `S = {g₁, g₂, g₃} ∪ {h, δ h, ..., δ^{m-1} h}`, `F₁ = K(S)`, `E = K(S ∪ {δ^m h})`.
  let S : Finset FracHolU := {g₁, g₂, g₃} ∪ (Finset.range m).image (fun i => fracEuler^[i] h)
  have hS_card : S.card ≤ m + 3 := by
    calc S.card ≤ ({g₁, g₂, g₃} : Finset FracHolU).card +
          ((Finset.range m).image (fun i => fracEuler^[i] h)).card := Finset.card_union_le _ _
      _ ≤ 3 + m := add_le_add
          ((Finset.card_insert_le _ _).trans (by
            have := Finset.card_insert_le g₂ {g₃}; simp at this ⊢; omega))
          (Finset.card_image_le.trans (by simp))
      _ = m + 3 := add_comm 3 m
  let F₁ : IntermediateField RatPoly FracHolU := IntermediateField.adjoin RatPoly (S : Set FracHolU)
  let E : IntermediateField RatPoly FracHolU :=
    IntermediateField.adjoin RatPoly ((S : Set FracHolU) ∪ {fracEuler^[m] h})
  have hE₀_le_F₁ : E₀ ≤ F₁ := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    refine IntermediateField.subset_adjoin _ _ ?_
    simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe]
    exact Or.inl (by simpa using hx)
  have hF₁_le_E : F₁ ≤ E := IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
  have hE₀_le_E : E₀ ≤ E := hE₀_le_F₁.trans hF₁_le_E
  have hmem_E_le : ∀ i : ℕ, i ≤ m → fracEuler^[i] h ∈ E := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | rfl
    · refine hF₁_le_E (IntermediateField.subset_adjoin _ _ ?_)
      simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨i, hlt, rfl⟩
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_union_right _ rfl)
  -- Show `E` is closed under `fracEuler`!
  have hE_closed : ∀ y ∈ E, fracEuler y ∈ E := by
    let E_cl : IntermediateField RatPoly FracHolU :=
      { carrier := {y | y ∈ E ∧ fracEuler y ∈ E}
        mul_mem' := fun {a b} ⟨ha, hda⟩ ⟨hb, hdb⟩ =>
          ⟨E.mul_mem ha hb, by rw [fracEuler_mul]; exact E.add_mem (E.mul_mem hda hb) (E.mul_mem ha hdb)⟩
        one_mem' := ⟨E.one_mem, by rw [fracEuler_one]; exact E.zero_mem⟩
        add_mem' := fun {a b} ⟨ha, hda⟩ ⟨hb, hdb⟩ =>
          ⟨E.add_mem ha hb, by rw [fracEuler_add]; exact E.add_mem hda hdb⟩
        zero_mem' := ⟨E.zero_mem, by rw [fracEuler_zero]; exact E.zero_mem⟩
        inv_mem' := fun {a} ⟨ha, hda⟩ =>
          ⟨E.inv_mem ha, by rw [fracEuler_inv]; exact E.div_mem (E.neg_mem hda) (E.pow_mem ha 2)⟩
        algebraMap_mem' := fun q => by
          obtain ⟨q', hq'⟩ := fracEuler_mem_ratPolyRange q
          exact ⟨E.algebraMap_mem q, hq' ▸ E.algebraMap_mem q'⟩ }
    have hE_eval_mem : ∀ P : MvPolynomial (Fin (m + 1)) FracHolU,
        (∀ d ∈ P.support, P.coeff d ∈ E₀) →
        MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) P ∈ E := by
      intro P hPc
      rw [MvPolynomial.eval_eq']
      refine E.sum_mem fun d hd => E.mul_mem (hE₀_le_E (hPc d hd))
        (E.prod_mem fun i _ => E.pow_mem (hmem_E_le i.1 (Nat.lt_succ_iff.mp i.2)) (d i))
    have hdm_mem : fracEuler (fracEuler^[m] h) ∈ E := by
      have hchain := fracEuler_mvPoly_eval F (fun i : Fin (m + 1) => fracEuler^[i.1] h)
      rw [hFev, fracEuler_zero] at hchain
      rw [Fin.sum_univ_castSucc] at hchain
      simp only [Fin.val_last, Fin.val_castSucc] at hchain
      have hlast_term :
          MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h)
            (MvPolynomial.pderiv (Fin.last m) F) * fracEuler (fracEuler^[m] h) =
          -(MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) (derivCoeffMv F) +
            ∑ i : Fin m, MvPolynomial.eval (fun j : Fin (m + 1) => fracEuler^[j.1] h)
              (MvPolynomial.pderiv (Fin.castSucc i) F) * fracEuler (fracEuler^[i.1] h)) := by
        linear_combination -hchain
      have hdc_mem : MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) (derivCoeffMv F) ∈ E := by
        refine hE_eval_mem (derivCoeffMv F) fun d _ => ?_
        rw [derivCoeffMv_coeff]
        by_cases hdm : d ∈ F.support
        · exact hE₀_closed _ (hFc d hdm)
        · have h0 : F.coeff d = 0 := by rwa [MvPolynomial.mem_support_iff, not_not] at hdm
          rw [h0, fracEuler_zero]; exact E₀.zero_mem
      have hsum_mem : ∑ i : Fin m,
          MvPolynomial.eval (fun j : Fin (m + 1) => fracEuler^[j.1] h)
            (MvPolynomial.pderiv (Fin.castSucc i) F) * fracEuler (fracEuler^[i.1] h) ∈ E := by
        refine E.sum_mem fun i _ => E.mul_mem ?_ ?_
        · refine hE_eval_mem (MvPolynomial.pderiv (Fin.castSucc i) F) fun d hd => ?_
          rw [MvPolynomial.coeff_pderiv]
          have hmem : d + Finsupp.single (Fin.castSucc i) 1 ∈ F.support := by
            rw [MvPolynomial.mem_support_iff] at hd ⊢
            rw [MvPolynomial.coeff_pderiv] at hd
            intro h0; rw [h0, zero_mul] at hd; exact hd rfl
          exact E₀.mul_mem (hFc _ hmem) (E₀.add_mem
            (by rw [← map_natCast (algebraMap RatPoly FracHolU)]; exact E₀.algebraMap_mem _) E₀.one_mem)
        · rw [← Function.iterate_succ_apply' fracEuler i.1 h]
          exact hmem_E_le (i.1 + 1) i.2
      have htop_mem : MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h)
          (MvPolynomial.pderiv (Fin.last m) F) ∈ E :=
        hE_eval_mem _ hpderiv_coeffs
      have hrhs_mem : -(MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) (derivCoeffMv F) +
          ∑ i : Fin m, MvPolynomial.eval (fun j : Fin (m + 1) => fracEuler^[j.1] h)
            (MvPolynomial.pderiv (Fin.castSucc i) F) * fracEuler (fracEuler^[i.1] h)) ∈ E :=
        E.neg_mem (E.add_mem hdc_mem hsum_mem)
      have heq_div : fracEuler (fracEuler^[m] h) =
          (-(MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) (derivCoeffMv F) +
            ∑ i : Fin m, MvPolynomial.eval (fun j : Fin (m + 1) => fracEuler^[j.1] h)
              (MvPolynomial.pderiv (Fin.castSucc i) F) * fracEuler (fracEuler^[i.1] h))) /
          MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h)
            (MvPolynomial.pderiv (Fin.last m) F) := by
        rw [eq_div_iff hpderiv_eval_ne, mul_comm]; exact hlast_term
      rw [heq_div]
      exact E.div_mem hrhs_mem htop_mem
    have hle : E ≤ E_cl := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with hxS | rfl
      · simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_image, Finset.mem_range] at hxS
        rcases hxS with (rfl | rfl | rfl) | ⟨i, hi, rfl⟩
        · exact ⟨hE₀_le_E (IntermediateField.subset_adjoin _ _ (by simp)), hE₀_le_E hg₁⟩
        · exact ⟨hE₀_le_E (IntermediateField.subset_adjoin _ _ (by simp)), hE₀_le_E hg₂⟩
        · exact ⟨hE₀_le_E (IntermediateField.subset_adjoin _ _ (by simp)), hE₀_le_E hg₃⟩
        · refine ⟨hmem_E_le i hi.le, ?_⟩
          rw [← Function.iterate_succ_apply' fracEuler i h]
          exact hmem_E_le (i + 1) hi
      · exact ⟨hmem_E_le m le_rfl, hdm_mem⟩
    intro y hy; exact (hle hy).2
  have hall_mem_E : ∀ k : ℕ, fracEuler^[k] h ∈ E := by
    intro k
    induction k with
    | zero => simpa using hmem_E_le 0 (Nat.zero_le m)
    | succ r ihr =>
      rw [Function.iterate_succ_apply']
      exact hE_closed _ ihr
  -- Prove `Algebra.IsAlgebraic (Algebra.adjoin RatPoly s') E` where `s' ⊆ E` is the lift of `S`:
  let sE : Set E := {y : E | y.1 ∈ (S : Set FracHolU)}
  have hsE_card : Cardinal.mk sE ≤ (m + 3 : ℕ) := by
    have hinj : Function.Injective (fun y : sE => (⟨y.1.1, y.2⟩ : S)) := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congr_arg (fun z : S => z.1) hab
    calc Cardinal.mk sE ≤ Cardinal.mk S := Cardinal.mk_le_of_injective hinj
      _ = S.card := Cardinal.mk_coe_finset
      _ ≤ (m + 3 : ℕ) := by exact_mod_cast hS_card
  have hAlg_F₁ : ∀ x : FracHolU, x ∈ F₁ → IsAlgebraic (Algebra.adjoin RatPoly (S : Set FracHolU)) x := by
    let R := Algebra.adjoin RatPoly (S : Set FracHolU)
    let F_alg : IntermediateField RatPoly FracHolU :=
      { carrier := {x : FracHolU | IsAlgebraic R x}
        mul_mem' := fun {_ _} ha hb => ha.mul hb
        one_mem' := isAlgebraic_one
        add_mem' := fun {_ _} ha hb => ha.add hb
        zero_mem' := isAlgebraic_zero
        inv_mem' := fun {_} ha => ha.inv
        algebraMap_mem' := fun q => isAlgebraic_algebraMap (⟨algebraMap RatPoly FracHolU q, R.algebraMap_mem q⟩ : R) }
    have hle : F₁ ≤ F_alg := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      exact isAlgebraic_algebraMap (⟨x, Algebra.subset_adjoin hx⟩ : R)
    exact fun x hx => hle hx
  -- Show `fracEuler^[m] h` is algebraic over `F₁`:
  have hm_alg_F₁ : IsAlgebraic F₁ (fracEuler^[m] h) := by
    -- Evaluate `F` at `(h, δ h, ..., δ^{m-1} h, X)` as a univariate polynomial in `Polynomial F₁`!
    let eval_last : MvPolynomial (Fin (m + 1)) FracHolU → Polynomial FracHolU :=
      MvPolynomial.eval₂ Polynomial.C
        (fun i : Fin (m + 1) =>
          if i.1 < m then Polynomial.C (fracEuler^[i.1] h) else Polynomial.X)
    have heval_last_mem : ∀ k : ℕ, (eval_last F).coeff k ∈ F₁ := by
      intro k
      dsimp [eval_last]
      rw [MvPolynomial.eval₂_eq', ← Polynomial.lcoeff_apply, map_sum]
      refine F₁.sum_mem fun d hd => ?_
      rw [Polynomial.lcoeff_apply]
      have hprod : (∏ i : Fin (m + 1),
          (if i.1 < m then Polynomial.C (fracEuler^[i.1] h) else Polynomial.X) ^ d i) =
          Polynomial.C (∏ i : Fin m, (fracEuler^[i.1] h) ^ d (Fin.castSucc i)) *
            Polynomial.X ^ d (Fin.last m) := by
        rw [Fin.prod_univ_castSucc]
        have hlast : ¬ (Fin.last m).1 < m := by simp
        simp only [hlast, ite_false]
        congr 1
        rw [map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp
      rw [hprod, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · refine F₁.mul_mem (hE₀_le_F₁ (hFc d hd)) (F₁.prod_mem fun i _ => F₁.pow_mem ?_ (d (Fin.castSucc i)))
        refine IntermediateField.subset_adjoin _ _ ?_
        simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨i.1, i.2, rfl⟩
      · exact F₁.zero_mem
    let p_F₁ : Polynomial F₁ :=
      ∑ k ∈ (eval_last F).support, Polynomial.monomial k ⟨(eval_last F).coeff k, heval_last_mem k⟩
    have hp_map : p_F₁.map (algebraMap F₁ FracHolU) = eval_last F := by
      ext k
      rw [Polynomial.coeff_map]
      dsimp only [p_F₁]
      rw [← Polynomial.lcoeff_apply, map_sum]
      simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
      by_cases hk : k ∈ (eval_last F).support
      · rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hne; simp [hne]
        · intro h; exact absurd hk h
      · have h0 : (eval_last F).coeff k = 0 := by rwa [Polynomial.mem_support_iff, not_not] at hk
        rw [h0]
        refine (map_eq_zero_iff _ (algebraMap F₁ FracHolU).injective).mpr ?_
        refine Finset.sum_eq_zero fun j hj => by simp [show j ≠ k from fun h => hk (h ▸ hj)]
    have hp_eval0 : Polynomial.aeval (fracEuler^[m] h) p_F₁ = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hp_map]
      have hcomp : Polynomial.eval (fracEuler^[m] h) (eval_last F) =
          MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) F := by
        dsimp [eval_last]
        rw [MvPolynomial.eval₂_eq', ← Polynomial.coe_evalRingHom, map_sum, MvPolynomial.eval_eq']
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C]
        congr 1
        rw [Polynomial.eval_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Polynomial.eval_pow]
        split_ifs with hi
        · simp
        · have heq : i.1 = m := by omega
          simp [heq]
      rw [hcomp, hFev]
    have hp_ne0 : p_F₁ ≠ 0 := by
      intro h0
      have he0 : eval_last F = 0 := by rw [← hp_map, h0, Polynomial.map_zero]
      have hderiv_eq : Polynomial.eval (fracEuler^[m] h) (Polynomial.derivative (eval_last F)) =
          MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h)
            (MvPolynomial.pderiv (Fin.last m) F) := by
        have hgen : ∀ P : MvPolynomial (Fin (m + 1)) FracHolU,
            Polynomial.eval (fracEuler^[m] h) (Polynomial.derivative (eval_last P)) =
              MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h)
                (MvPolynomial.pderiv (Fin.last m) P) := by
          intro P
          induction P using MvPolynomial.induction_on with
          | C c => simp [eval_last]
          | add P Q hP hQ =>
            dsimp only [eval_last] at hP hQ ⊢
            rw [MvPolynomial.eval₂_add, map_add, Polynomial.eval_add, hP, hQ, map_add, RingHom.map_add]
          | mul_X P j hP =>
            have hmul : eval_last (P * MvPolynomial.X j) =
                eval_last P * (if j.1 < m then Polynomial.C (fracEuler^[j.1] h) else Polynomial.X) := by
              dsimp only [eval_last]
              rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
            rw [hmul, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_mul, hP, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply,
              smul_eq_mul, smul_eq_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul]
            have hPev : Polynomial.eval (fracEuler^[m] h) (eval_last P) =
                MvPolynomial.eval (fun i : Fin (m + 1) => fracEuler^[i.1] h) P := by
              dsimp [eval_last]
              rw [MvPolynomial.eval₂_eq', ← Polynomial.coe_evalRingHom, map_sum, MvPolynomial.eval_eq']
              refine Finset.sum_congr rfl fun d _ => ?_
              simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C]
              congr 1
              rw [Polynomial.eval_prod]
              refine Finset.prod_congr rfl fun i _ => ?_
              rw [Polynomial.eval_pow]
              split_ifs with hi
              · simp
              · have heq : i.1 = m := by omega
                simp [heq]
            rw [hPev]
            by_cases hjm : j.1 < m
            · have hne : j ≠ Fin.last m := fun heq => by subst heq; simp at hjm
              simp [hjm, hne]; ring
            · have heq : j = Fin.last m := Fin.ext (by simp; omega)
              subst heq; simp; ring
        exact hgen F
      rw [he0, map_zero, Polynomial.eval_zero] at hderiv_eq
      exact hpderiv_eval_ne hderiv_eq.symm
    exact ⟨p_F₁, hp_ne0, hp_eval0⟩
  -- Hence every element of `E` is algebraic over `F₁`, and therefore over `Algebra.adjoin RatPoly (S : Set FracHolU)`!
  have hE_alg_F₁ : ∀ x : FracHolU, x ∈ E → IsAlgebraic F₁ x := by
    let F_alg₁ : IntermediateField RatPoly FracHolU :=
      { carrier := {x : FracHolU | IsAlgebraic F₁ x}
        mul_mem' := fun {_ _} ha hb => ha.mul hb
        one_mem' := isAlgebraic_one
        add_mem' := fun {_ _} ha hb => ha.add hb
        zero_mem' := isAlgebraic_zero
        inv_mem' := fun {_} ha => ha.inv
        algebraMap_mem' := fun q => isAlgebraic_algebraMap (⟨algebraMap RatPoly FracHolU q, F₁.algebraMap_mem q⟩ : F₁) }
    have hle : E ≤ F_alg₁ := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with hxS | rfl
      · exact isAlgebraic_algebraMap (⟨x, IntermediateField.subset_adjoin _ _ hxS⟩ : F₁)
      · exact hm_alg_F₁
    exact fun x hx => hle hx
  -- Lift `Algebra.IsAlgebraic (Algebra.adjoin RatPoly sE) E`!
  have hAlg_sE : Algebra.IsAlgebraic (Algebra.adjoin RatPoly sE) E := by
    let R_E := Algebra.adjoin RatPoly sE
    let F₁_E : IntermediateField RatPoly E := IntermediateField.adjoin RatPoly sE
    have hmap_R : ∀ y : FracHolU, y ∈ Algebra.adjoin RatPoly (S : Set FracHolU) →
        ∃ z : R_E, z.1.1 = y := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        have hxE : x ∈ E := hF₁_le_E (IntermediateField.subset_adjoin _ _ hx)
        exact ⟨⟨⟨x, hxE⟩, Algebra.subset_adjoin hx⟩, rfl⟩
      | algebraMap q =>
        exact ⟨algebraMap RatPoly R_E q, rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨zx, rfl⟩ := hx; obtain ⟨zy, rfl⟩ := hy
        exact ⟨zx + zy, rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨zx, rfl⟩ := hx; obtain ⟨zy, rfl⟩ := hy
        exact ⟨zx * zy, rfl⟩
    have hAlg_R_E_of_R : ∀ x : E, IsAlgebraic (Algebra.adjoin RatPoly (S : Set FracHolU)) x.1 →
        IsAlgebraic R_E x := by
      rintro x ⟨p, hpne, hpev⟩
      have hR_le_F₁_orig : Algebra.adjoin RatPoly (S : Set FracHolU) ≤ F₁.toSubalgebra := by
        rw [Algebra.adjoin_le_iff]; exact IntermediateField.subset_adjoin _ _
      let φ : Algebra.adjoin RatPoly (S : Set FracHolU) →+* R_E :=
        { toFun := fun a => ⟨⟨a.1, hF₁_le_E (hR_le_F₁_orig a.2)⟩, by
            obtain ⟨z, hz⟩ := hmap_R a.1 a.2
            have heq : (⟨a.1, hF₁_le_E (hR_le_F₁_orig a.2)⟩ : E) = z.1 := Subtype.ext hz.symm
            rw [heq]; exact z.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hφ_inj : Function.Injective φ := fun a b hab =>
        Subtype.ext (congr_arg (fun z : R_E => z.1.1) hab)
      refine ⟨p.map φ, (Polynomial.map_ne_zero_iff hφ_inj).mpr hpne, ?_⟩
      apply Subtype.ext
      have hval : (Polynomial.aeval x (p.map φ)).1 = Polynomial.aeval x.1 p := by
        have hgen : ∀ r : Polynomial (Algebra.adjoin RatPoly (S : Set FracHolU)),
            (Polynomial.aeval x (r.map φ)).1 = Polynomial.aeval x.1 r := by
          intro r
          induction r using Polynomial.induction_on' with
          | add r₁ r₂ h₁ h₂ =>
            simp only [Polynomial.map_add, Polynomial.aeval_def, Polynomial.eval₂_add] at h₁ h₂ ⊢
            exact congr_arg₂ (· + ·) h₁ h₂
          | monomial n a =>
            rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial]; rfl
        exact hgen p
      rw [hval, hpev]; rfl
    have hF₁_E_eq : ∀ x : E, x ∈ F₁_E ↔ x.1 ∈ F₁ := by
      intro x
      constructor
      · intro hx
        let K₁ : IntermediateField RatPoly E :=
          { carrier := {y : E | y.1 ∈ F₁}
            mul_mem' := fun {_ _} ha hb => F₁.mul_mem ha hb
            one_mem' := F₁.one_mem
            add_mem' := fun {_ _} ha hb => F₁.add_mem ha hb
            zero_mem' := F₁.zero_mem
            inv_mem' := fun {_} ha => F₁.inv_mem ha
            algebraMap_mem' := fun q => F₁.algebraMap_mem q }
        have hle : F₁_E ≤ K₁ := by
          rw [IntermediateField.adjoin_le_iff]
          intro y hy; exact IntermediateField.subset_adjoin _ _ hy
        exact hle hx
      · intro hx
        let K₂ : IntermediateField RatPoly FracHolU :=
          { carrier := {y : FracHolU | ∃ z : E, z ∈ F₁_E ∧ z.1 = y}
            mul_mem' := fun {_ _} ⟨a, ha, h1⟩ ⟨b, hb, h2⟩ =>
              ⟨a * b, F₁_E.mul_mem ha hb, by rw [← h1, ← h2]; rfl⟩
            one_mem' := ⟨1, F₁_E.one_mem, rfl⟩
            add_mem' := fun {_ _} ⟨a, ha, h1⟩ ⟨b, hb, h2⟩ =>
              ⟨a + b, F₁_E.add_mem ha hb, by rw [← h1, ← h2]; rfl⟩
            zero_mem' := ⟨0, F₁_E.zero_mem, rfl⟩
            inv_mem' := fun {_} ⟨a, ha, h1⟩ =>
              ⟨a⁻¹, F₁_E.inv_mem ha, by rw [← h1]; rfl⟩
            algebraMap_mem' := fun q => ⟨algebraMap RatPoly E q, F₁_E.algebraMap_mem q, rfl⟩ }
        have hle : F₁ ≤ K₂ := by
          rw [IntermediateField.adjoin_le_iff]
          intro y hy
          exact ⟨⟨y, hF₁_le_E (IntermediateField.subset_adjoin _ _ hy)⟩,
            IntermediateField.subset_adjoin _ _ hy, rfl⟩
        obtain ⟨z, hz, hzx⟩ := hle hx
        exact (Subtype.ext hzx.symm : x = z) ▸ hz
    have hR_le_F₁ : R_E ≤ F₁_E.toSubalgebra := by
      rw [Algebra.adjoin_le_iff]; exact IntermediateField.subset_adjoin _ _
    let incRF : R_E →+* F₁_E :=
      { toFun := fun a => ⟨a.1, hR_le_F₁ a.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let instAlgRF : Algebra R_E F₁_E := incRF.toAlgebra
    let instTower : @IsScalarTower R_E F₁_E E instAlgRF.toSMul _ _ :=
      @IsScalarTower.of_algebraMap_eq R_E F₁_E E _ _ _ instAlgRF _ _ (fun _ => rfl)
    have hAlg_R_F₁ : @Algebra.IsAlgebraic R_E F₁_E _ _ instAlgRF := by
      refine @Algebra.IsAlgebraic.mk R_E F₁_E _ _ instAlgRF fun y => ?_
      have hy : IsAlgebraic R_E y.1 := hAlg_R_E_of_R y.1 (hAlg_F₁ y.1.1 ((hF₁_E_eq y.1).mp y.2))
      obtain ⟨p, hpne, hpev⟩ := hy
      refine ⟨p, hpne, ?_⟩
      apply Subtype.ext
      have hval : (@Polynomial.aeval R_E F₁_E _ _ instAlgRF y p).1 = Polynomial.aeval y.1 p := by
        have hgen : ∀ r : Polynomial R_E,
            (@Polynomial.aeval R_E F₁_E _ _ instAlgRF y r).1 = Polynomial.aeval y.1 r := by
          intro r
          induction r using Polynomial.induction_on' with
          | add r₁ r₂ h₁ h₂ =>
            simp only [@Polynomial.aeval_def R_E F₁_E _ _ instAlgRF, Polynomial.aeval_def,
              Polynomial.eval₂_add] at h₁ h₂ ⊢
            exact congr_arg₂ (· + ·) h₁ h₂
          | monomial n a =>
            rw [@Polynomial.aeval_monomial R_E F₁_E _ _ instAlgRF, Polynomial.aeval_monomial]; rfl
        exact hgen p
      rw [hval, hpev]; rfl
    have hAlg_F₁_E : Algebra.IsAlgebraic F₁_E E := by
      constructor
      intro y
      obtain ⟨p, hpne, hpev⟩ := hE_alg_F₁ y.1 y.2
      let ψ : F₁ →+* F₁_E :=
        { toFun := fun a => ⟨⟨a.1, hF₁_le_E a.2⟩, (hF₁_E_eq ⟨a.1, hF₁_le_E a.2⟩).mpr a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hψ_inj : Function.Injective ψ := fun a b hab =>
        Subtype.ext (congr_arg (fun z : F₁_E => z.1.1) hab)
      refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff hψ_inj).mpr hpne, ?_⟩
      apply Subtype.ext
      have hval : (Polynomial.aeval y (p.map ψ)).1 = Polynomial.aeval y.1 p := by
        have hgen : ∀ r : Polynomial F₁,
            (Polynomial.aeval y (r.map ψ)).1 = Polynomial.aeval y.1 r := by
          intro r
          induction r using Polynomial.induction_on' with
          | add r₁ r₂ h₁ h₂ =>
            simp only [Polynomial.map_add, Polynomial.aeval_def, Polynomial.eval₂_add] at h₁ h₂ ⊢
            exact congr_arg₂ (· + ·) h₁ h₂
          | monomial n a =>
            rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial]; rfl
        exact hgen p
      rw [hval, hpev]; rfl
    exact @Algebra.IsAlgebraic.trans R_E F₁_E E _ _ _ instAlgRF _ _ instTower _ hAlg_R_F₁ hAlg_F₁_E
  -- Now apply `trdeg_le_cardinalMk` and `cardinalMk_le_trdeg`!
  have htrdeg : Algebra.trdeg RatPoly E ≤ (m + 3 : ℕ) :=
    (Algebra.IsAlgebraic.trdeg_le_cardinalMk RatPoly sE).trans hsE_card
  let xE : Fin (m + 4) → E := fun i => ⟨fracEuler^[i.1] h, hall_mem_E i.1⟩
  have hnot_indep : ¬ AlgebraicIndependent RatPoly xE := by
    intro hind
    have hcard := hind.cardinalMk_le_trdeg
    have hfin : Cardinal.mk (Fin (m + 4)) = ((m + 4 : ℕ) : Cardinal) := by simp
    rw [hfin] at hcard
    have hle : ((m + 4 : ℕ) : Cardinal) ≤ ((m + 3 : ℕ) : Cardinal) := hcard.trans htrdeg
    have hnat : m + 4 ≤ m + 3 := by exact_mod_cast hle
    omega
  rw [algebraicIndependent_iff] at hnot_indep
  push Not at hnot_indep
  obtain ⟨Q_K, hQ_K_eval, hQ_K_ne⟩ := hnot_indep
  -- Clear the finitely many denominators of `Q_K.coeffs` in `RatPoly = FractionRing (Polynomial ℂ)`!
  have hex_den : ∀ d ∈ Q_K.support,
      ∃ num : Polynomial ℂ, ∃ den : nonZeroDivisors (Polynomial ℂ),
        Q_K.coeff d = algebraMap (Polynomial ℂ) RatPoly num /
          algebraMap (Polynomial ℂ) RatPoly den.1 := by
    intro d _
    obtain ⟨⟨num, den⟩, hmk⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial ℂ)) (Q_K.coeff d)
    dsimp only at hmk
    exact ⟨num, den, by rw [← hmk, IsFractionRing.mk'_eq_div]⟩
  choose num den hden using hex_den
  let D_all : Polynomial ℂ := ∏ d ∈ Q_K.support, if hd : d ∈ Q_K.support then (den d hd).1 else 1
  have hD_all_ne : D_all ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun d hd => ?_
    simp only [hd, dite_true]
    exact nonZeroDivisors.ne_zero (den d hd).2
  let Q : MvPolynomial (Fin (m + 4)) (Polynomial ℂ) :=
    ∑ d ∈ Q_K.support,
      if hd : d ∈ Q_K.support then
        MvPolynomial.monomial d
          (num d hd * ∏ s ∈ Q_K.support.erase d, if hs : s ∈ Q_K.support then (den s hs).1 else 1)
      else 0
  have hQ_map : MvPolynomial.map (algebraMap (Polynomial ℂ) RatPoly) Q =
      MvPolynomial.C (algebraMap (Polynomial ℂ) RatPoly D_all) * Q_K := by
    ext d
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
    dsimp only [Q]
    rw [← MvPolynomial.lcoeff_apply, map_sum]
    simp only [MvPolynomial.lcoeff_apply]
    by_cases hd : d ∈ Q_K.support
    · rw [Finset.sum_eq_single d]
      · simp only [hd, dite_true, MvPolynomial.coeff_monomial, ite_true, map_mul, map_prod]
        rw [hden d hd]
        have hD_split : D_all = (den d hd).1 *
            ∏ s ∈ Q_K.support.erase d, if hs : s ∈ Q_K.support then (den s hs).1 else 1 := by
          dsimp [D_all]
          rw [← Finset.mul_prod_erase _ _ hd]
          simp [hd]
        have hden_ne : algebraMap (Polynomial ℂ) RatPoly (den d hd).1 ≠ 0 :=
          map_ne_zero_of_mem_nonZeroDivisors _
            (IsFractionRing.injective (Polynomial ℂ) RatPoly) (den d hd).2
        rw [hD_split, map_mul, map_prod]
        field_simp [hden_ne]
      · intro s hs hne
        simp only [hs, dite_true, MvPolynomial.coeff_monomial, hne, ite_false]
      · intro h; exact absurd hd h
    · have h0 : Q_K.coeff d = 0 := by rwa [MvPolynomial.mem_support_iff, not_not] at hd
      rw [h0, mul_zero]
      have hsum0 : (∑ s ∈ Q_K.support,
          (if hs : s ∈ Q_K.support then MvPolynomial.monomial s
            (num s hs * ∏ t ∈ Q_K.support.erase s, if ht : t ∈ Q_K.support then (den t ht).1 else 1)
          else 0).coeff d) = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        have hne : s ≠ d := fun h => hd (h ▸ hs)
        simp only [hs, dite_true, MvPolynomial.coeff_monomial, hne, ite_false]
      rw [hsum0, map_zero]
  have hQ_ne : Q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ_map
    have hD_ne_K : algebraMap (Polynomial ℂ) RatPoly D_all ≠ 0 := by
      intro hc
      exact hD_all_ne ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℂ) RatPoly)).mp hc)
    have hC_ne : MvPolynomial.C (algebraMap (Polynomial ℂ) RatPoly D_all) ≠
        (0 : MvPolynomial (Fin (m + 4)) RatPoly) := by
      intro hc; exact hD_ne_K (MvPolynomial.C_eq_zero.mp hc)
    exact hQ_K_ne ((mul_eq_zero.mp hQ_map.symm).resolve_left hC_ne)
  refine ⟨m + 3, Q, hQ_ne, ?_⟩
  have hQ_eval_E : MvPolynomial.aeval xE (MvPolynomial.map (algebraMap (Polynomial ℂ) RatPoly) Q) = 0 := by
    rw [hQ_map, map_mul, hQ_K_eval, mul_zero]
  have hQ_val := congr_arg Subtype.val hQ_eval_E
  rw [ZeroMemClass.coe_zero] at hQ_val
  rw [← hQ_val]
  have hcomp : ∀ R : MvPolynomial (Fin (m + 4)) (Polynomial ℂ),
      MvPolynomial.eval₂ (ratPolyToFrac.comp (algebraMap (Polynomial ℂ) RatPoly))
        (fun i : Fin (m + 4) => fracEuler^[i.1] h) R =
      (MvPolynomial.aeval xE (MvPolynomial.map (algebraMap (Polynomial ℂ) RatPoly) R)).1 := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C p =>
      rw [MvPolynomial.eval₂_C, MvPolynomial.map_C, MvPolynomial.aeval_C]; rfl
    | add P₁ P₂ h₁ h₂ =>
      rw [MvPolynomial.eval₂_add, map_add, map_add, h₁, h₂]; rfl
    | mul_X P₁ j h₁ =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, MvPolynomial.map_X,
        map_mul, MvPolynomial.aeval_X, h₁]; rfl
  exact hcomp Q

/-! ### Real Polynomial ADEs, Change-of-Variable Transfer, and `volterraMu_no_rat_ade` -/

/-- Evaluation of a polynomial algebraic differential equation `P(t, f(t), f'(t), ..., f^{(r)}(t))`
at a real point `t : ℝ`. -/
@[expose] noncomputable def evalRealADE {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom (t : ℂ)) (fun i => (deriv^[i.1] f) t) P

/-- Evaluation of a polynomial Euler ADE `P(t, f(t), (t d/dt) f(t), ..., (t d/dt)^r f(t))`
at a real point `t : ℝ`. -/
@[expose] noncomputable def evalRealEulerADE {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom (t : ℂ)) (fun i => (eulerOpR^[i.1] f) t) P

private lemma eulerOpR_iter_congr {f g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hfg : Set.EqOn f g U) (k : ℕ) :
    Set.EqOn (eulerOpR^[k] f) (eulerOpR^[k] g) U := by
  induction k with
  | zero => exact hfg
  | succ m ih =>
    intro t ht
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    dsimp [eulerOpR]
    congr 1
    have hev : eulerOpR^[m] f =ᶠ[nhds t] eulerOpR^[m] g :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds ht, ih⟩
    exact hev.deriv_eq

private lemma deriv_iter_congr {f g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hfg : Set.EqOn f g U) (k : ℕ) :
    Set.EqOn (deriv^[k] f) (deriv^[k] g) U := by
  induction k with
  | zero => exact hfg
  | succ m ih =>
    intro t ht
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hev : deriv^[m] f =ᶠ[nhds t] deriv^[m] g :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds ht, ih⟩
    exact hev.deriv_eq

/-- Stirling conversion on any open interval `U ⊆ (0, ∞)`:
`t^j * (deriv^[j] f t) = ∑_{i ≤ j} stirlingDerivRow j i * (eulerOpR^[i] f t)`. -/
private lemma real_pow_mul_deriv_iter_eq_stirling {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℂ} (hdiff : ∀ k : ℕ, DifferentiableOn ℝ (deriv^[k] f) U)
    (j : ℕ) :
    ∀ t ∈ U, (t : ℂ) ^ j * (deriv^[j] f t) =
      ∑ i ∈ Finset.range (j + 1),
        ((stirlingDerivRow j).getD i 0 : ℂ) * (eulerOpR^[i] f t) := by
  have heuler_diff : ∀ k : ℕ, DifferentiableOn ℝ (eulerOpR^[k] f) U := by
    -- Express `eulerOpR^[k] f` as a polynomial in `t` and `deriv^[i] f`? Easier: prove by induction on `k`
    -- that `∀ m, DifferentiableOn ℝ (deriv^[m] (eulerOpR^[k] f)) U`!
    have hstrong : ∀ k m : ℕ, DifferentiableOn ℝ (deriv^[m] (eulerOpR^[k] f)) U := by
      intro k
      induction k with
      | zero => intro m; simpa using hdiff m
      | succ r ihr =>
        -- `eulerOpR (g) t = (t : ℂ) * deriv g t`, and by Leibniz `deriv^[m] (t * h) = t * deriv^[m] h + m * deriv^[m-1] h`!
        have hmul_t : ∀ (m : ℕ) {h : ℝ → ℂ}, (∀ p : ℕ, DifferentiableOn ℝ (deriv^[p] h) U) →
            DifferentiableOn ℝ (deriv^[m] (fun t : ℝ => (t : ℂ) * h t)) U ∧
            Set.EqOn (deriv^[m] (fun t : ℝ => (t : ℂ) * h t))
              (fun t => (t : ℂ) * deriv^[m] h t + (m : ℂ) * (if m = 0 then 0 else deriv^[m - 1] h t)) U := by
          intro m
          induction m with
          | zero =>
            intro h hh
            refine ⟨(Complex.ofRealCLM.differentiable.differentiableOn).mul (hh 0), fun t _ => by simp⟩
          | succ q ihq =>
            intro h hh
            obtain ⟨hdq, heqq⟩ := ihq hh
            have hderiv_eq : Set.EqOn (deriv^[q + 1] (fun t : ℝ => (t : ℂ) * h t))
                (fun t => (t : ℂ) * deriv^[q + 1] h t + ((q + 1 : ℕ) : ℂ) * deriv^[q] h t) U := by
              intro t ht
              rw [Function.iterate_succ_apply']
              have hev : deriv^[q] (fun s : ℝ => (s : ℂ) * h s) =ᶠ[nhds t]
                  (fun s => (s : ℂ) * deriv^[q] h s + (q : ℂ) * (if q = 0 then 0 else deriv^[q - 1] h s)) :=
                Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds ht, heqq⟩
              rw [hev.deriv_eq]
              have hd1 : HasDerivAt (fun s : ℝ => (s : ℂ) * deriv^[q] h s)
                  (1 * deriv^[q] h t + (t : ℂ) * deriv (deriv^[q] h) t) t := by
                have hofR : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
                exact hofR.mul ((hh q t ht).differentiableAt (hU.mem_nhds ht)).hasDerivAt
              rcases q with _ | q'
              · simp only [Nat.cast_zero, ↓reduceIte, mul_zero, add_zero, zero_add, Nat.cast_one, one_mul]
                rw [hd1.deriv]; simp; ring
              · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
                have hd2 : HasDerivAt (fun s : ℝ => ((q' + 1 : ℕ) : ℂ) * deriv^[q'] h s)
                    (((q' + 1 : ℕ) : ℂ) * deriv (deriv^[q'] h) t) t :=
                  (((hh q' t ht).differentiableAt (hU.mem_nhds ht)).hasDerivAt).const_mul _
                rw [(hd1.fun_add hd2).deriv]
                simp only [Function.iterate_succ_apply']
                push_cast; ring
            have hdiff_rhs : DifferentiableOn ℝ
                (fun t : ℝ => (t : ℂ) * deriv^[q + 1] h t + ((q + 1 : ℕ) : ℂ) * deriv^[q] h t) U :=
              ((Complex.ofRealCLM.differentiable.differentiableOn).mul (hh (q + 1))).add
                ((hh q).const_mul _)
            refine ⟨hdiff_rhs.congr hderiv_eq, ?_⟩
            intro t ht; simpa using hderiv_eq ht
        intro m
        have hstep : eulerOpR^[r + 1] f = fun t : ℝ => (t : ℂ) * deriv (eulerOpR^[r] f) t := by
          ext t; rw [Function.iterate_succ_apply']; rfl
        rw [hstep]
        exact (hmul_t m (fun p => by simpa [Function.iterate_succ_apply] using ihr (p + 1))).1
    intro k; simpa using hstrong k 0
  -- Now prove the Stirling identity by induction on `j`!
  induction j with
  | zero =>
    intro t _; simp [stirlingDerivRow]
  | succ m ih =>
    intro t ht
    have hstep : eulerOpR (fun s : ℝ => (s : ℂ) ^ m * deriv^[m] f s) t =
        (m : ℂ) * ((t : ℂ) ^ m * deriv^[m] f t) + (t : ℂ) ^ (m + 1) * deriv^[m + 1] f t := by
      dsimp [eulerOpR]
      have hpow : HasDerivAt (fun s : ℝ => (s : ℂ) ^ m) ((m : ℂ) * (t : ℂ) ^ (m - 1)) t := by
        have hofR : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
        have h1 := hofR.fun_pow m
        simpa using h1
      have hdf : HasDerivAt (deriv^[m] f) (deriv (deriv^[m] f) t) t :=
        ((hdiff m t ht).differentiableAt (hU.mem_nhds ht)).hasDerivAt
      rw [(hpow.fun_mul hdf).deriv, ← Function.iterate_succ_apply deriv m f,
        Function.iterate_succ_apply' deriv m f]
      rcases m with _ | m'
      · simp
      · simp only [Nat.add_sub_cancel, pow_succ]; ring
    have heuler_lhs : eulerOpR (fun s : ℝ => (s : ℂ) ^ m * deriv^[m] f s) t =
        ∑ i ∈ Finset.range (m + 1),
          ((stirlingDerivRow m).getD i 0 : ℂ) * (eulerOpR^[i + 1] f t) := by
      have hev : (fun s : ℝ => (s : ℂ) ^ m * deriv^[m] f s) =ᶠ[nhds t]
          (fun s : ℝ => ∑ i ∈ Finset.range (m + 1),
            ((stirlingDerivRow m).getD i 0 : ℂ) * (eulerOpR^[i] f s)) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds ht, ih⟩
      dsimp [eulerOpR]
      rw [hev.deriv_eq]
      have hsum_d : HasDerivAt
          (fun s : ℝ => ∑ i ∈ Finset.range (m + 1), ((stirlingDerivRow m).getD i 0 : ℂ) * (eulerOpR^[i] f s))
          (∑ i ∈ Finset.range (m + 1), ((stirlingDerivRow m).getD i 0 : ℂ) * deriv (eulerOpR^[i] f) t) t := by
        refine HasDerivAt.fun_sum fun i _ => ?_
        exact (((heuler_diff i t ht).differentiableAt (hU.mem_nhds ht)).hasDerivAt).const_mul _
      rw [hsum_d.deriv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Function.iterate_succ_apply eulerOpR i f, Function.iterate_succ_apply' eulerOpR i f]
      dsimp [eulerOpR]; ring
    have hrec : (t : ℂ) ^ (m + 1) * deriv^[m + 1] f t =
        ∑ i ∈ Finset.range (m + 1), ((stirlingDerivRow m).getD i 0 : ℂ) * (eulerOpR^[i + 1] f t) -
        (m : ℂ) * ∑ i ∈ Finset.range (m + 1), ((stirlingDerivRow m).getD i 0 : ℂ) * (eulerOpR^[i] f t) := by
      rw [← ih t ht, ← heuler_lhs]; linear_combination -hstep
    rw [hrec]
    -- Match coefficients with `stirlingDerivRow (m + 1)` using `stirlingDerivRow_succ_getD`!
    have hrhs : ∑ i ∈ Finset.range (m + 2), ((stirlingDerivRow (m + 1)).getD i 0 : ℂ) * (eulerOpR^[i] f t) =
        ∑ i ∈ Finset.range (m + 2),
          ((if i = 0 then (0 : ℂ) else ((stirlingDerivRow m).getD (i - 1) 0 : ℂ)) -
            (m : ℂ) * ((stirlingDerivRow m).getD i 0 : ℂ)) * (eulerOpR^[i] f t) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [stirlingDerivRow_succ_getD m i (Finset.mem_range.mp hi)]
    rw [hrhs]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    · symm
      rw [Finset.sum_range_succ']
      simp
    · symm
      rw [Finset.sum_range_succ, stirlingDerivRow_getD_ge m (m + 1) (by omega)]
      simp only [zero_mul, mul_zero, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring

/-- Convert a nonzero real polynomial ADE on an open set `U : Set ℝ` into a nonzero real Euler ADE
on `U`. -/
private lemma exists_nonzero_real_euler_ade_on_open {U : Set ℝ} (hU : IsOpen U) {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : P ≠ 0)
    {f : ℝ → ℂ} (hdiff : ∀ k : ℕ, DifferentiableOn ℝ (deriv^[k] f) U)
    (hf : ∀ t ∈ U, evalRealADE P f t = 0) :
    ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      Q ≠ 0 ∧ ∀ t ∈ U, evalRealEulerADE Q f t = 0 := by
  let D : ℕ := P.totalDegree
  let L : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun j =>
    ∑ i : Fin (r + 1),
      if i.1 ≤ j.1 then
        MvPolynomial.C (Polynomial.C ((stirlingDerivRow j.1).getD i.1 0)) * MvPolynomial.X i
      else 0
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ d ∈ P.support,
      MvPolynomial.C (P.coeff d * Polynomial.X ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j)) *
        ∏ j : Fin (r + 1), (L j) ^ (d j)
  -- `Q ≠ 0` by the exact same triangular evaluation at a nonzero `x₀ : ℂ` as in Section 1!
  have hQne : Q ≠ 0 := by
    -- Reuse `exists_nonzero_euler_ade_of_deriv_ade`'s exact `Q`: wait, we can prove `Q ≠ 0` directly
    -- by noting `evalDerivPS P 0`? No, prove `Q ≠ 0` cleanly in 30 lines using `x₀ ≠ 0`!
    obtain ⟨d₀, hd₀⟩ : P.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hP (MvPolynomial.support_eq_empty.mp h0)
    have hcoeff_ne : P.coeff d₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hd₀
    obtain ⟨x₀, hx₀, hpx₀⟩ : ∃ x₀ : ℂ, x₀ ≠ 0 ∧ (P.coeff d₀).eval x₀ ≠ 0 := by
      by_contra hall; push Not at hall
      have hinf : Set.Infinite {z : ℂ | z ≠ 0} := Set.infinite_of_injective_forall_mem
        (f := fun n : ℕ => ((n + 1 : ℕ) : ℂ)) (fun a b hab => by
          have : a + 1 = b + 1 := Nat.cast_injective hab; omega)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      have hfin : ((P.coeff d₀).roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
      refine hinf (hfin.subset fun z hz => ?_)
      simp [Polynomial.mem_roots hcoeff_ne, Polynomial.IsRoot, hall z hz]
    let ev : Polynomial ℂ →+* ℂ := Polynomial.evalRingHom x₀
    let P_ev : MvPolynomial (Fin (r + 1)) ℂ := MvPolynomial.map ev P
    have hP_ev_ne : P_ev ≠ 0 := by
      intro h0
      have hc := congr_arg (fun q : MvPolynomial (Fin (r + 1)) ℂ => q.coeff d₀) h0
      rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at hc
      exact hpx₀ hc
    let φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ := fun j =>
      MvPolynomial.C (x₀⁻¹ ^ j.1) *
        ∑ i : Fin (r + 1),
          if i.1 ≤ j.1 then
            MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * MvPolynomial.X i
          else 0
    have hQ_ev : MvPolynomial.map ev Q = MvPolynomial.C (x₀ ^ (r * D)) * MvPolynomial.aeval (R := ℂ) φ P_ev := by
      dsimp only [Q, P_ev]
      rw [map_sum]
      conv_rhs => rw [MvPolynomial.as_sum (p := P), map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hsum_le : ∑ j : Fin (r + 1), j.1 * d j ≤ r * D := by
        calc ∑ j : Fin (r + 1), j.1 * d j
            ≤ ∑ j : Fin (r + 1), r * d j :=
              Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.2)
          _ = r * ∑ j : Fin (r + 1), d j := (Finset.mul_sum _ _ _).symm
          _ ≤ r * D := Nat.mul_le_mul_left r (by
              have hdeg := MvPolynomial.le_totalDegree hd
              rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
              exact hdeg)
      have hpow : x₀ ^ (r * D) * ∏ j : Fin (r + 1), (x₀⁻¹ ^ j.1) ^ (d j) =
          x₀ ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j) := by
        have h1 : ∏ j : Fin (r + 1), (x₀⁻¹ ^ j.1) ^ (d j) =
            (x₀ ^ (∑ j : Fin (r + 1), j.1 * d j))⁻¹ := by
          simp_rw [← pow_mul, inv_pow]
          rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
        rw [h1]
        have hsplit : x₀ ^ (r * D) =
            x₀ ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j) * x₀ ^ (∑ j : Fin (r + 1), j.1 * d j) := by
          rw [← pow_add, Nat.sub_add_cancel hsum_le]
        rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx₀), mul_one]
      have hLmap : ∀ j : Fin (r + 1),
          MvPolynomial.map ev (L j) =
            ∑ i : Fin (r + 1), if i.1 ≤ j.1 then
              MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * MvPolynomial.X i else 0 := by
        intro j; simp only [L, map_sum]
        refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp [ev]
      have hprodL : MvPolynomial.map ev (∏ j : Fin (r + 1), L j ^ d j) =
          ∏ j : Fin (r + 1), (∑ i : Fin (r + 1),
            if i.1 ≤ j.1 then MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * MvPolynomial.X i else 0) ^ d j := by
        rw [map_prod]
        refine Finset.prod_congr rfl fun j _ => by rw [map_pow, hLmap]
      rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        map_mul, MvPolynomial.map_C, hprodL, MvPolynomial.algebraMap_eq]
      have hφprod : ∏ j : Fin (r + 1), (φ j) ^ d j =
          MvPolynomial.C (∏ j : Fin (r + 1), (x₀⁻¹ ^ j.1) ^ d j) *
          ∏ j : Fin (r + 1), (∑ i : Fin (r + 1),
            if i.1 ≤ j.1 then MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * MvPolynomial.X i else 0) ^ d j := by
        simp only [φ, mul_pow, Finset.prod_mul_distrib]
        congr 1
        rw [map_prod]
        refine Finset.prod_congr rfl fun j _ => by rw [← map_pow]
      rw [hφprod]
      have hCev : MvPolynomial.C (R := ℂ) (σ := Fin (r + 1)) (ev (P.coeff d * Polynomial.X ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j))) =
          MvPolynomial.C (ev (P.coeff d)) * MvPolynomial.C (x₀ ^ (r * D)) *
            MvPolynomial.C (∏ j : Fin (r + 1), (x₀⁻¹ ^ j.1) ^ d j) := by
        simp only [ev, Polynomial.coe_evalRingHom, Polynomial.eval_pow,
          Polynomial.eval_X, ← hpow, map_mul]
        ring
      rw [hCev]; ring
    have hφ_inj : Function.Injective (MvPolynomial.aeval (R := ℂ) φ) := by
      have hinv : ∀ m : ℕ, m ≤ r + 1 →
          ∃ ψ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ,
            ∀ j : Fin (r + 1), j.1 < m → MvPolynomial.aeval (R := ℂ) ψ (φ j) = MvPolynomial.X j := by
        intro m
        induction m with
        | zero => intro _; exact ⟨MvPolynomial.X, fun j hj => by omega⟩
        | succ m ih =>
          intro hm
          obtain ⟨ψ, hψ⟩ := ih (by omega)
          let j₀ : Fin (r + 1) := ⟨m, hm⟩
          let val₀ : MvPolynomial (Fin (r + 1)) ℂ :=
            MvPolynomial.C (x₀ ^ m) * MvPolynomial.X j₀ -
              ∑ i : Fin (r + 1), if i.1 < m then MvPolynomial.C ((stirlingDerivRow m).getD i.1 0) * ψ i else 0
          let ψ' : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ := fun i => if i = j₀ then val₀ else ψ i
          refine ⟨ψ', fun j hj => ?_⟩
          have hφ_eval : ∀ k : Fin (r + 1),
              MvPolynomial.aeval (R := ℂ) ψ' (φ k) =
                MvPolynomial.C (x₀⁻¹ ^ k.1) *
                  ∑ i : Fin (r + 1), if i.1 ≤ k.1 then
                    MvPolynomial.C ((stirlingDerivRow k.1).getD i.1 0) * ψ' i else 0 := by
            intro k; simp only [φ, map_mul, map_sum, MvPolynomial.aeval_C]; congr 1
            refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
          by_cases hjm : j.1 < m
          · rw [hφ_eval j]
            have hsum_eq : ∑ i : Fin (r + 1),
                (if i.1 ≤ j.1 then MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * ψ' i else 0) =
              ∑ i : Fin (r + 1),
                (if i.1 ≤ j.1 then MvPolynomial.C ((stirlingDerivRow j.1).getD i.1 0) * ψ i else 0) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              split_ifs with hij
              · have hne : i ≠ j₀ := by intro heq; subst heq; dsimp [j₀] at hij; omega
                simp [ψ', hne]
              · rfl
            rw [hsum_eq, ← hψ j hjm]
            simp only [φ, map_mul, map_sum, MvPolynomial.aeval_C]; congr 1
            refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
          · have hjeq : j = j₀ := Fin.ext (by dsimp [j₀]; omega)
            subst hjeq
            rw [hφ_eval j₀]
            have hsplit : ∑ i : Fin (r + 1),
                (if i.1 ≤ m then MvPolynomial.C ((stirlingDerivRow m).getD i.1 0) * ψ' i else 0) =
                MvPolynomial.C ((stirlingDerivRow m).getD m 0) * ψ' j₀ +
                ∑ i : Fin (r + 1), if i.1 < m then MvPolynomial.C ((stirlingDerivRow m).getD i.1 0) * ψ i else 0 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
              simp only [j₀, le_refl, ite_true]
              congr 1
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨m, hm⟩ : Fin (r + 1)))]
              simp only [lt_self_iff_false, ite_false, zero_add]
              refine Finset.sum_congr rfl fun i hi => ?_
              have hne : i ≠ ⟨m, hm⟩ := (Finset.mem_erase.mp hi).1
              have hval_ne : i.1 ≠ m := fun h => hne (Fin.ext h)
              have hiff : i.1 ≤ m ↔ i.1 < m := by omega
              simp only [hiff]; split_ifs with hlt
              · simp [ψ', j₀, hne]
              · rfl
            dsimp only [j₀]
            rw [hsplit, stirlingDerivRow_last m, map_one, one_mul]
            have hψ'j : ψ' j₀ = val₀ := by simp [ψ']
            rw [hψ'j]
            simp only [val₀, sub_add_cancel, ← mul_assoc, ← map_mul, ← mul_pow,
              inv_mul_cancel₀ hx₀, one_pow, map_one, one_mul]
            rfl
      obtain ⟨ψ, hψ⟩ := hinv (r + 1) le_rfl
      have hcomp : ∀ p : MvPolynomial (Fin (r + 1)) ℂ,
          MvPolynomial.aeval (R := ℂ) ψ (MvPolynomial.aeval (R := ℂ) φ p) = p := by
        intro p
        induction p using MvPolynomial.induction_on with
        | C c => simp
        | add p q hp hq => rw [map_add, map_add, hp, hq]
        | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.aeval_X, hψ j j.2]
      intro p q hpq
      have := congr_arg (MvPolynomial.aeval (R := ℂ) ψ) hpq
      rwa [hcomp, hcomp] at this
    intro hQ0
    rw [hQ0, map_zero] at hQ_ev
    have hpow_ne : MvPolynomial.C (x₀ ^ (r * D)) ≠ (0 : MvPolynomial (Fin (r + 1)) ℂ) := fun hc =>
      pow_ne_zero _ hx₀ (MvPolynomial.C_eq_zero.mp hc)
    exact hP_ev_ne (hφ_inj (by rw [(mul_eq_zero.mp hQ_ev.symm).resolve_left hpow_ne, map_zero]))
  refine ⟨Q, hQne, fun t ht => ?_⟩
  have hL_eval : ∀ j : Fin (r + 1),
      MvPolynomial.eval₂ (Polynomial.evalRingHom (t : ℂ)) (fun i => eulerOpR^[i.1] f t) (L j) =
        (t : ℂ) ^ j.1 * deriv^[j.1] f t := by
    intro j
    rw [real_pow_mul_deriv_iter_eq_stirling hU hdiff j.1 t ht]
    dsimp [L]
    rw [MvPolynomial.eval₂_sum]
    have hsum_eq : ∑ i : Fin (r + 1),
        (if i.1 ≤ j.1 then ((stirlingDerivRow j.1).getD i.1 0 : ℂ) * eulerOpR^[i.1] f t else 0) =
        ∑ i ∈ Finset.range (j.1 + 1),
          ((stirlingDerivRow j.1).getD i 0 : ℂ) * eulerOpR^[i] f t := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun i _ => i.1)
        (fun i hi => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hi).2; omega))
        (fun a _ b _ hab => Fin.ext hab)
        (fun k hk => ⟨⟨k, by have := Finset.mem_range.mp hk; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; have := Finset.mem_range.mp hk; omega⟩, rfl⟩)
        (fun _ _ => rfl)
    rw [← hsum_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hQ_eq : evalRealEulerADE Q f t = (t : ℂ) ^ (r * D) * evalRealADE P f t := by
    dsimp only [evalRealEulerADE, evalRealADE, Q]
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod,
      MvPolynomial.eval₂_pow, hL_eval, mul_pow, Finset.prod_mul_distrib,
      Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    have hsum_le : ∑ j : Fin (r + 1), j.1 * d j ≤ r * D := by
      calc ∑ j : Fin (r + 1), j.1 * d j
          ≤ ∑ j : Fin (r + 1), r * d j :=
            Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.2)
        _ = r * ∑ j : Fin (r + 1), d j := (Finset.mul_sum _ _ _).symm
        _ ≤ r * D := Nat.mul_le_mul_left r (by
            have hdeg := MvPolynomial.le_totalDegree hd
            rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
            exact hdeg)
    have hpow : (t : ℂ) ^ (r * D - ∑ j : Fin (r + 1), j.1 * d j) *
        ∏ j : Fin (r + 1), ((t : ℂ) ^ j.1) ^ d j = (t : ℂ) ^ (r * D) := by
      simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.sub_add_cancel hsum_le]
    calc (Polynomial.eval (↑t) (P.coeff d) * (↑t) ^ (r * D - ∑ j, j.1 * d j)) *
          ((∏ j, ((↑t) ^ j.1) ^ d j) * ∏ j, (deriv^[j.1] f t) ^ d j)
        = Polynomial.eval (↑t) (P.coeff d) *
          ((↑t) ^ (r * D - ∑ j, j.1 * d j) * ∏ j, ((↑t) ^ j.1) ^ d j) *
          ∏ j, (deriv^[j.1] f t) ^ d j := by ring
      _ = Polynomial.eval (↑t) (P.coeff d) * (↑t) ^ (r * D) * ∏ j, (deriv^[j.1] f t) ^ d j := by
          rw [hpow]
      _ = (↑t) ^ (r * D) * (Polynomial.eval (↑t) (P.coeff d) * ∏ j, (deriv^[j.1] f t) ^ d j) := by
          ring
  rw [hQ_eq, hf t ht, mul_zero]

/-- **Master Theorem 1 (Euler-ADE form on `(0, 1)`, `volterraMu_no_euler_ade_Ioo`):**
For every `α : ℂ` and `β : ℂ` with `-1 < β.re`, the generalized Volterra function `μ(t, β, α)`
satisfies NO nonzero polynomial Euler ADE over `ℂ[t]` on `(0, 1)`. -/
theorem volterraMu_no_euler_ade_Ioo (α β : ℂ) (hβ : -1 < β.re) {r : ℕ}
    (P₁ : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP₁_ne : P₁ ≠ 0)
    (hP₁_eval : ∀ t ∈ Set.Ioo (0 : ℝ) 1, evalRealEulerADE P₁ (volterraMu β α) t = 0) : False := by
  -- Define `μ_U(z) = exp (-α / z) * z^(β + 1) * volterraLaplace β α z` on `rightHalfPlane`:
  let μ_U : ℂ → ℂ := fun z =>
    Complex.exp (-α / z) * (z ^ (β + 1)) * volterraLaplace β α z
  have hg1_an : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-(1 : ℂ) / z)) rightHalfPlane := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_rightHalfPlane
    have hzne : z ≠ 0 := by intro h0; rw [h0] at hz; simp [rightHalfPlane] at hz
    exact ((differentiableAt_const (-(1 : ℂ))).div differentiableAt_id hzne).cexp.differentiableWithinAt
  have hg2_an : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-α / z)) rightHalfPlane := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_rightHalfPlane
    have hzne : z ≠ 0 := by intro h0; rw [h0] at hz; simp [rightHalfPlane] at hz
    exact ((differentiableAt_const (-α)).div differentiableAt_id hzne).cexp.differentiableWithinAt
  have hg3_an : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (β + 1)) rightHalfPlane := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_rightHalfPlane
    have hz_slit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
    exact (Complex.hasStrictDerivAt_cpow_const hz_slit).hasDerivAt.differentiableAt.differentiableWithinAt
  have hf_an : AnalyticOnNhd ℂ (volterraLaplace β α) rightHalfPlane :=
    analyticOnNhd_volterraLaplace β α hβ
  have hμU_an : AnalyticOnNhd ℂ μ_U rightHalfPlane := (hg2_an.mul hg3_an).mul hf_an
  -- Step 2: Chain-rule identity `((z * δ_ℂ)^[j] μ_U) (x : ℂ) = (eulerOpR^[j] (volterraMu β α)) (exp (-1/x))` for `x > 0`!
  let zEulerC : (ℂ → ℂ) → (ℂ → ℂ) := fun g z => z * eulerOpC g z
  have hzEuler_an : ∀ (j : ℕ) {g : ℂ → ℂ}, AnalyticOnNhd ℂ g rightHalfPlane →
      AnalyticOnNhd ℂ (zEulerC^[j] g) rightHalfPlane := by
    intro j
    induction j with
    | zero => intro g hg; simpa using hg
    | succ m ih =>
      intro g hg
      rw [Function.iterate_succ_apply']
      exact analyticOnNhd_id.mul (analyticOnNhd_id.mul (ih hg).deriv)
  have hchain_real : ∀ (j : ℕ) (x : ℝ), 0 < x →
      (zEulerC^[j] μ_U) (x : ℂ) = (eulerOpR^[j] (volterraMu β α)) (Real.exp (-(1 : ℝ) / x)) := by
    intro j
    induction j with
    | zero =>
      intro x hx; exact (volterraMu_exp_neg_inv β α hx).symm
    | succ m ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have htx_mem : Real.exp (-(1 : ℝ) / x) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hx)⟩
      -- Differentiate `s ↦ (zEulerC^[m] μ_U) (s : ℂ) = (eulerOpR^[m] (volterraMu β α)) (exp (-1/s))` at `x`:
      have hG_an : AnalyticAt ℂ (zEulerC^[m] μ_U) (x : ℂ) :=
        hzEuler_an m hμU_an (x : ℂ) (by simpa [rightHalfPlane] using hx)
      have hG_real_d : HasDerivAt (fun s : ℝ => (zEulerC^[m] μ_U) (s : ℂ))
          (deriv (zEulerC^[m] μ_U) (x : ℂ)) x :=
        hG_an.differentiableAt.hasDerivAt.comp_ofReal
      have hφ_d : HasDerivAt (fun s : ℝ => Real.exp (-(1 : ℝ) / s))
          (Real.exp (-(1 : ℝ) / x) / x ^ 2) x := by
        have hinv : HasDerivAt (fun s : ℝ => -(1 : ℝ) / s) (1 / x ^ 2) x := by
          have h1 := (hasDerivAt_inv hx.ne').const_mul (-(1 : ℝ))
          convert h1 using 1
          · ext s; rw [div_eq_mul_inv]
          · ring
        refine hinv.exp.congr_deriv ?_; ring
      have heuler_m_diff : DifferentiableAt ℝ (eulerOpR^[m] (volterraMu β α)) (Real.exp (-(1 : ℝ) / x)) := by
        have heq_Ioo : Set.EqOn (eulerOpR^[m] (volterraMu β α))
            (fun t => (zEulerC^[m] μ_U) (((-(1 : ℝ) / Real.log t : ℝ) : ℂ))) (Set.Ioo (0 : ℝ) 1) := by
          intro t ⟨ht0, ht1⟩
          have hlog_neg : Real.log t < 0 := Real.log_neg ht0 ht1
          have hxpos : 0 < -(1 : ℝ) / Real.log t := div_pos_of_neg_of_neg (by norm_num) hlog_neg
          have hexp_eq : Real.exp (-(1 : ℝ) / (-(1 : ℝ) / Real.log t)) = t := by
            have : -(1 : ℝ) / (-(1 : ℝ) / Real.log t) = Real.log t := by field_simp [hlog_neg.ne]
            rw [this, Real.exp_log ht0]
          rw [← hexp_eq, ← ih _ hxpos, hexp_eq]
        have hcomp_diff : DifferentiableAt ℝ
            (fun t => (zEulerC^[m] μ_U) (((-(1 : ℝ) / Real.log t : ℝ) : ℂ)))
            (Real.exp (-(1 : ℝ) / x)) := by
          have hlog_d : DifferentiableAt ℝ (fun t : ℝ => -(1 : ℝ) / Real.log t) (Real.exp (-(1 : ℝ) / x)) :=
            DifferentiableAt.div (differentiableAt_const _) (Real.differentiableAt_log htx_mem.1.ne')
              (Real.log_neg htx_mem.1 htx_mem.2).ne
          have hval_eq : -(1 : ℝ) / Real.log (Real.exp (-(1 : ℝ) / x)) = x := by
            rw [Real.log_exp]; field_simp [hx.ne']
          have hg_d : DifferentiableAt ℝ (fun s : ℝ => (zEulerC^[m] μ_U) (s : ℂ))
              (-(1 : ℝ) / Real.log (Real.exp (-(1 : ℝ) / x))) := by
            rw [hval_eq]; exact hG_real_d.differentiableAt
          exact DifferentiableAt.comp (Real.exp (-(1 : ℝ) / x))
            (g := fun s : ℝ => (zEulerC^[m] μ_U) (s : ℂ)) hg_d hlog_d
        have hev : (eulerOpR^[m] (volterraMu β α)) =ᶠ[nhds (Real.exp (-(1 : ℝ) / x))]
            (fun t => (zEulerC^[m] μ_U) (((-(1 : ℝ) / Real.log t : ℝ) : ℂ))) :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 0 1, isOpen_Ioo.mem_nhds htx_mem, heq_Ioo⟩
        exact hcomp_diff.congr_of_eventuallyEq hev
      have hcomp_d : HasDerivAt (fun s : ℝ => (eulerOpR^[m] (volterraMu β α)) (Real.exp (-(1 : ℝ) / s)))
          ((Real.exp (-(1 : ℝ) / x) / x ^ 2 : ℝ) •
            deriv (eulerOpR^[m] (volterraMu β α)) (Real.exp (-(1 : ℝ) / x))) x :=
        heuler_m_diff.hasDerivAt.scomp x hφ_d
      have hev_eq : (fun s : ℝ => (zEulerC^[m] μ_U) (s : ℂ)) =ᶠ[nhds x]
          (fun s : ℝ => (eulerOpR^[m] (volterraMu β α)) (Real.exp (-(1 : ℝ) / s))) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds hx, fun s hs => ih s hs⟩
      have hd_eq := hG_real_d.unique (hcomp_d.congr_of_eventuallyEq hev_eq)
      change (x : ℂ) * ((x : ℂ) * deriv (zEulerC^[m] μ_U) (x : ℂ)) =
        (Real.exp (-(1 : ℝ) / x) : ℂ) * deriv (eulerOpR^[m] (volterraMu β α)) (Real.exp (-(1 : ℝ) / x))
      rw [hd_eq, Complex.real_smul]
      have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      push_cast; field_simp [hxne]
  -- Step 3: Lift `P₁(e^{-1/z}, μ_U, (z δ) μ_U, ..., (z δ)^r μ_U) = 0` to `HolU` and `FracHolU`!
  let g₁_U : HolU := holUMk hg1_an
  let g₂_U : HolU := holUMk hg2_an
  let g₃_U : HolU := holUMk hg3_an
  let f_U : HolU := holUMk hf_an
  let μ_holU : HolU := holUMk hμU_an
  let z_U : HolU := holUMk analyticOnNhd_id
  let g₁ : FracHolU := algebraMap HolU FracHolU g₁_U
  let g₂ : FracHolU := algebraMap HolU FracHolU g₂_U
  let g₃ : FracHolU := algebraMap HolU FracHolU g₃_U
  let f_L : FracHolU := algebraMap HolU FracHolU f_U
  let z_L : FracHolU := algebraMap HolU FracHolU z_U
  have hz_L_eq : z_L = ratPolyToFrac (algebraMap (Polynomial ℂ) RatPoly Polynomial.X) := by
    rw [ratPolyToFrac_algebraMap]
    exact congr_arg (algebraMap HolU FracHolU) (by ext w; simp [z_U, polyToHolU_apply, holUMk_apply])
  let E₀ : IntermediateField RatPoly FracHolU := IntermediateField.adjoin RatPoly {g₁, g₂, g₃}
  have hz_mem_E₀ : z_L ∈ E₀ := by rw [hz_L_eq]; exact E₀.algebraMap_mem _
  have hz_ne0 : z_L ≠ 0 := by
    intro h0
    have h1 := (map_eq_zero_iff _ (IsFractionRing.injective HolU FracHolU)).mp h0
    have h2 := congr_arg (fun g : HolU => g.1 ⟨1, by simp [rightHalfPlane]⟩) h1
    simp [z_U, holUMk_apply] at h2
  have hg₁_mem : g₁ ∈ E₀ := IntermediateField.subset_adjoin _ _ (by simp)
  have hg₂_mem : g₂ ∈ E₀ := IntermediateField.subset_adjoin _ _ (by simp)
  have hg₃_mem : g₃ ∈ E₀ := IntermediateField.subset_adjoin _ _ (by simp)
  have hg₁_deriv : fracEuler g₁ = z_L⁻¹ * g₁ := by
    rw [mul_comm z_L⁻¹, eq_mul_inv_iff_mul_eq₀ hz_ne0]
    -- Wait: `z_L * fracEuler g₁ = g₁`!
    have hU : z_U * holUEuler g₁_U = g₁_U := by
      ext w
      have hwne : w.1 ≠ 0 := by intro h0; have := w.2; rw [h0] at this; simp [rightHalfPlane] at this
      have hd : HasDerivAt (fun s : ℂ => Complex.exp (-(1 : ℂ) / s))
          ((w.1 ^ 2)⁻¹ * Complex.exp (-(1 : ℂ) / w.1)) w.1 := by
        have h1 := (hasDerivAt_inv hwne).const_mul (-(1 : ℂ))
        have h2 : HasDerivAt (fun s : ℂ => -(1 : ℂ) / s) (w.1 ^ 2)⁻¹ w.1 := by
          convert h1 using 1
          · ext s; rw [div_eq_mul_inv]
          · ring
        simpa [mul_comm] using h2.cexp
      rw [Subalgebra.coe_mul, Pi.mul_apply, holUEuler_mk]
      simp only [z_U, g₁_U, holUMk_apply, hd.deriv]
      field_simp [hwne]
    calc fracEuler g₁ * z_L
        = algebraMap HolU FracHolU (holUEuler g₁_U) * algebraMap HolU FracHolU z_U := by
          rw [fracEuler_algebraMap]
      _ = algebraMap HolU FracHolU (z_U * holUEuler g₁_U) := by rw [← map_mul, mul_comm]
      _ = g₁ := by rw [hU]
  have hg₂_deriv : fracEuler g₂ = (algebraMap RatPoly FracHolU (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C α))) * z_L⁻¹ * g₂ := by
    have hCα : algebraMap RatPoly FracHolU (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C α)) =
        algebraMap HolU FracHolU (algebraMap ℂ HolU α) := by
      change ratPolyToFrac (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C α)) = _
      rw [ratPolyToFrac_algebraMap]; congr 1
      ext w; simp [polyToHolU_apply]
    rw [hCα]
    have hU : z_U * holUEuler g₂_U = algebraMap ℂ HolU α * g₂_U := by
      ext w
      have hwne : w.1 ≠ 0 := by intro h0; have := w.2; rw [h0] at this; simp [rightHalfPlane] at this
      have hd : HasDerivAt (fun s : ℂ => Complex.exp (-α / s))
          ((α * (w.1 ^ 2)⁻¹) * Complex.exp (-α / w.1)) w.1 := by
        have h1 := (hasDerivAt_inv hwne).const_mul (-α)
        have h2 : HasDerivAt (fun s : ℂ => -α / s) (α * (w.1 ^ 2)⁻¹) w.1 := by
          convert h1 using 1
          · ext s; rw [div_eq_mul_inv]
          · ring
        simpa [mul_comm] using h2.cexp
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Pi.mul_apply, Pi.mul_apply, holUEuler_mk]
      simp only [z_U, g₂_U, holUMk_apply, hd.deriv]
      change w.1 * (w.1 * (α * (w.1 ^ 2)⁻¹ * Complex.exp (-α / w.1))) = α * Complex.exp (-α / w.1)
      field_simp [hwne]
    rw [mul_assoc, mul_comm z_L⁻¹, ← mul_assoc, ← div_eq_mul_inv, eq_div_iff hz_ne0]
    calc fracEuler g₂ * z_L
        = algebraMap HolU FracHolU (z_U * holUEuler g₂_U) := by
          rw [fracEuler_algebraMap, ← map_mul, mul_comm]
      _ = algebraMap HolU FracHolU (algebraMap ℂ HolU α) * g₂ := by rw [hU, map_mul]
  have hg₃_deriv : fracEuler g₃ =
      algebraMap RatPoly FracHolU (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C (β + 1))) * g₃ := by
    have hCβ : algebraMap RatPoly FracHolU (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C (β + 1))) =
        algebraMap HolU FracHolU (algebraMap ℂ HolU (β + 1)) := by
      change ratPolyToFrac (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C (β + 1))) = _
      rw [ratPolyToFrac_algebraMap]; congr 1
      ext w; simp [polyToHolU_apply]
    rw [hCβ]
    have hU : holUEuler g₃_U = algebraMap ℂ HolU (β + 1) * g₃_U := by
      ext w
      have hw_slit : w.1 ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl w.2)
      have hwne : w.1 ≠ 0 := by intro h0; have := w.2; rw [h0] at this; simp [rightHalfPlane] at this
      have hd : HasDerivAt (fun s : ℂ => s ^ (β + 1)) ((β + 1) * w.1 ^ ((β + 1) - 1)) w.1 :=
        (Complex.hasStrictDerivAt_cpow_const hw_slit).hasDerivAt
      rw [Subalgebra.coe_mul, Pi.mul_apply, holUEuler_mk]
      simp only [g₃_U, holUMk_apply, hd.deriv]
      change w.1 * ((β + 1) * w.1 ^ ((β + 1) - 1)) = (β + 1) * w.1 ^ (β + 1)
      have hpow : w.1 * w.1 ^ ((β + 1) - 1) = w.1 ^ (β + 1) := by
        rw [add_sub_cancel_right, Complex.cpow_add _ _ hwne, Complex.cpow_one, mul_comm]
      linear_combination (β + 1) * hpow
    rw [fracEuler_algebraMap, hU, map_mul]
  have hg₁_E₀ : fracEuler g₁ ∈ E₀ := by rw [hg₁_deriv]; exact E₀.mul_mem (E₀.inv_mem hz_mem_E₀) hg₁_mem
  have hg₂_E₀ : fracEuler g₂ ∈ E₀ := by
    rw [hg₂_deriv]
    exact E₀.mul_mem (E₀.mul_mem (E₀.algebraMap_mem _) (E₀.inv_mem hz_mem_E₀)) hg₂_mem
  have hg₃_E₀ : fracEuler g₃ ∈ E₀ := by
    rw [hg₃_deriv]; exact E₀.mul_mem (E₀.algebraMap_mem _) hg₃_mem
  -- Show `g₂ ≠ 0`, `g₃ ≠ 0`, and `g₁` is transcendental over `ℂ`!
  have hg₂_ne0 : g₂ ≠ 0 := by
    intro h0
    have h1 := (map_eq_zero_iff _ (IsFractionRing.injective HolU FracHolU)).mp h0
    have h2 := congr_arg (fun g : HolU => g.1 ⟨1, by simp [rightHalfPlane]⟩) h1
    simp [g₂_U, holUMk_apply, Complex.exp_ne_zero] at h2
  have hg₃_ne0 : g₃ ≠ 0 := by
    intro h0
    have h1 := (map_eq_zero_iff _ (IsFractionRing.injective HolU FracHolU)).mp h0
    have h2 := congr_arg (fun g : HolU => g.1 ⟨1, by simp [rightHalfPlane]⟩) h1
    simp [g₃_U, holUMk_apply] at h2
  have hg₁_transc : ∀ p : Polynomial ℂ, p ≠ 0 →
      Polynomial.eval₂ (algebraMap ℂ FracHolU) g₁ p ≠ 0 := by
    -- Wait: let's write `eval₂` using `ratPolyToFrac (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C c))`!
    intro p hp h0
    have hmap_poly : ∀ q : Polynomial ℂ,
        algebraMap HolU FracHolU (Polynomial.eval₂ (algebraMap ℂ HolU) g₁_U q) =
          Polynomial.eval₂ (algebraMap ℂ FracHolU) g₁ q := by
      intro q
      induction q using Polynomial.induction_on' with
      | add p₁ p₂ h₁ h₂ => rw [Polynomial.eval₂_add, Polynomial.eval₂_add, RingHom.map_add, h₁, h₂]
      | monomial n c =>
        rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, RingHom.map_mul, RingHom.map_pow]
        rfl
    have hev_holU : Polynomial.eval₂ (algebraMap ℂ HolU) g₁_U p = 0 := by
      apply IsFractionRing.injective HolU FracHolU
      rw [map_zero, hmap_poly p, h0]
    have hinf_vals : Set.Infinite (Set.range fun n : ℕ => Complex.exp (-(1 : ℂ) / ((n + 1 : ℕ) : ℂ))) := by
      refine Set.infinite_range_of_injective fun a b hab => ?_
      have hre : Real.exp (-(1 : ℝ) / ((a + 1 : ℕ) : ℝ)) = Real.exp (-(1 : ℝ) / ((b + 1 : ℕ) : ℝ)) := by
        have h1 : Complex.exp (-(1 : ℂ) / ((a + 1 : ℕ) : ℂ)) =
            ((Real.exp (-(1 : ℝ) / ((a + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring
        have h2 : Complex.exp (-(1 : ℂ) / ((b + 1 : ℕ) : ℂ)) =
            ((Real.exp (-(1 : ℝ) / ((b + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring
        rw [h1, h2] at hab
        exact Complex.ofReal_injective hab
      have hdiv := Real.exp_injective hre
      have ha : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hb : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have heq : ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) := by
        have := congr_arg (fun y => -y⁻¹) hdiv
        simpa [inv_div] using this
      have : a + 1 = b + 1 := Nat.cast_injective heq
      omega
    have hfin : (p.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
    refine hinf_vals (hfin.subset ?_)
    rintro _ ⟨n, rfl⟩
    have hnU : (((n + 1 : ℕ) : ℂ)) ∈ rightHalfPlane := by
      simp only [rightHalfPlane, Set.mem_ofPred_eq, Complex.natCast_re]
      exact Nat.cast_pos.mpr (Nat.succ_pos n)
    have hval := congr_arg (fun g : HolU => g.1 ⟨_, hnU⟩) hev_holU
    have heval_eq : ∀ q : Polynomial ℂ,
        (Polynomial.eval₂ (algebraMap ℂ HolU) g₁_U q).1 ⟨_, hnU⟩ =
          q.eval (Complex.exp (-(1 : ℂ) / ((n + 1 : ℕ) : ℂ))) := by
      intro q
      induction q using Polynomial.induction_on' with
      | add p₁ p₂ h₁ h₂ =>
        rw [Polynomial.eval₂_add, Polynomial.eval_add, Subalgebra.coe_add, Pi.add_apply, h₁, h₂]
      | monomial k c => simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial, g₁_U, holUMk_apply]
    rw [heval_eq p] at hval
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
    simpa [Polynomial.IsRoot] using hval
  -- Now prove `P₁` vanishes on `(g₁, μ, (z δ) μ, ..., (z δ)^r μ)` in `FracHolU`!
  let zEulerL : FracHolU → FracHolU := fun x => z_L * fracEuler x
  have hzEuler_iter_eq : ∀ j : ℕ,
      zEulerL^[j] (algebraMap HolU FracHolU μ_holU) =
        algebraMap HolU FracHolU (holUMk (hzEuler_an j hμU_an)) := by
    intro j
    induction j with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      dsimp only [zEulerL]
      rw [fracEuler_algebraMap, ← map_mul, holUEuler_mk]
      congr 1; ext w
      simp [z_U, holUMk_apply, Function.iterate_succ_apply', zEulerC, eulerOpC]
  have hP₁_vanish_L :
      MvPolynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ FracHolU) g₁)
        (fun i : Fin (r + 1) => zEulerL^[i.1] (algebraMap HolU FracHolU μ_holU)) P₁ = 0 := by
    -- Lift from `HolU` via `holU_eq_zero_of_eqOn_pos_reals`!
    let H_U : HolU :=
      MvPolynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ HolU) g₁_U)
        (fun i : Fin (r + 1) => holUMk (hzEuler_an i.1 hμU_an)) P₁
    have hH_zero : H_U = 0 := by
      refine holU_eq_zero_of_eqOn_pos_reals fun x hx => ?_
      have htx : Real.exp (-(1 : ℝ) / x) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hx)⟩
      have h1 := hP₁_eval (Real.exp (-(1 : ℝ) / x)) htx
      rw [← h1]
      dsimp only [H_U, evalRealEulerADE]
      have hpoly_val : ∀ p : Polynomial ℂ,
          (Polynomial.eval₂ (algebraMap ℂ HolU) g₁_U p).1 ⟨(x : ℂ), by simpa [rightHalfPlane] using hx⟩ =
          p.eval ((Real.exp (-(1 : ℝ) / x) : ℝ) : ℂ) := by
        intro p
        induction p using Polynomial.induction_on' with
        | add p₁ p₂ h₁ h₂ => simp [Polynomial.eval₂_add, Polynomial.eval_add, h₁, h₂]
        | monomial k c =>
          simp only [Polynomial.eval₂_monomial, Polynomial.eval_monomial, Subalgebra.coe_mul,
            Subalgebra.coe_pow, Pi.mul_apply, Pi.pow_apply, g₁_U, holUMk_apply]
          congr 1; congr 1
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring
      have heval_eq : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
          (MvPolynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ HolU) g₁_U)
            (fun i : Fin (r + 1) => holUMk (hzEuler_an i.1 hμU_an)) R).1
            ⟨(x : ℂ), by simpa [rightHalfPlane] using hx⟩ =
          MvPolynomial.eval₂ (Polynomial.evalRingHom ((Real.exp (-(1 : ℝ) / x) : ℝ) : ℂ))
            (fun i : Fin (r + 1) => (eulerOpR^[i.1] (volterraMu β α)) (Real.exp (-(1 : ℝ) / x))) R := by
        intro R
        induction R using MvPolynomial.induction_on with
        | C p => simpa using hpoly_val p
        | add R₁ R₂ h₁ h₂ =>
          rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, Subalgebra.coe_add, Pi.add_apply, h₁, h₂]
        | mul_X R₁ j h₁ =>
          rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
            Subalgebra.coe_mul, Pi.mul_apply, h₁, holUMk_apply, hchain_real j.1 x hx]
      exact heval_eq P₁
    have hmap_H : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
        algebraMap HolU FracHolU
          (MvPolynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ HolU) g₁_U)
            (fun i : Fin (r + 1) => holUMk (hzEuler_an i.1 hμU_an)) R) =
        MvPolynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ FracHolU) g₁)
          (fun i : Fin (r + 1) => zEulerL^[i.1] (algebraMap HolU FracHolU μ_holU)) R := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C p =>
        rw [MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
        simp only [Polynomial.coe_eval₂RingHom]
        induction p using Polynomial.induction_on' with
        | add p₁ p₂ h₁ h₂ => rw [Polynomial.eval₂_add, Polynomial.eval₂_add, RingHom.map_add, h₁, h₂]
        | monomial k c =>
          rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, RingHom.map_mul, RingHom.map_pow]; rfl
      | add R₁ R₂ h₁ h₂ =>
        rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, RingHom.map_add, h₁, h₂]
      | mul_X R₁ j h₁ =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
          RingHom.map_mul, h₁, hzEuler_iter_eq j.1]
    rw [← hmap_H P₁]
    change algebraMap HolU FracHolU H_U = 0
    rw [hH_zero, map_zero]
  -- Step 4: Triangular affine substitution `zEulerL^[j] (g₂ * g₃ * f_L) = ∑_{i ≤ j} c_{j,i} * fracEuler^[i] f_L`
  -- with coefficients `c_{j,i} ∈ E₀` and leading coefficient `c_{j,j} = g₂ * g₃ * z_L^j ≠ 0`!
  have hE₀_closed' : ∀ y ∈ E₀, fracEuler y ∈ E₀ := by
    let E₀_cl : IntermediateField RatPoly FracHolU :=
      { carrier := {y | y ∈ E₀ ∧ fracEuler y ∈ E₀}
        mul_mem' := fun {a b} ⟨ha, hda⟩ ⟨hb, hdb⟩ =>
          ⟨E₀.mul_mem ha hb, by rw [fracEuler_mul]; exact E₀.add_mem (E₀.mul_mem hda hb) (E₀.mul_mem ha hdb)⟩
        one_mem' := ⟨E₀.one_mem, by rw [fracEuler_one]; exact E₀.zero_mem⟩
        add_mem' := fun {a b} ⟨ha, hda⟩ ⟨hb, hdb⟩ =>
          ⟨E₀.add_mem ha hb, by rw [fracEuler_add]; exact E₀.add_mem hda hdb⟩
        zero_mem' := ⟨E₀.zero_mem, by rw [fracEuler_zero]; exact E₀.zero_mem⟩
        inv_mem' := fun {a} ⟨ha, hda⟩ =>
          ⟨E₀.inv_mem ha, by rw [fracEuler_inv]; exact E₀.div_mem (E₀.neg_mem hda) (E₀.pow_mem ha 2)⟩
        algebraMap_mem' := fun q => by
          obtain ⟨q', hq'⟩ := fracEuler_mem_ratPolyRange q
          exact ⟨E₀.algebraMap_mem q, hq' ▸ E₀.algebraMap_mem q'⟩ }
    have hle : E₀ ≤ E₀_cl := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hg₁_mem, hg₁_E₀⟩
      · exact ⟨hg₂_mem, hg₂_E₀⟩
      · exact ⟨hg₃_mem, hg₃_E₀⟩
    exact fun y hy => (hle hy).2
  have hμ_prod : algebraMap HolU FracHolU μ_holU = g₂ * g₃ * f_L := by
    rw [← map_mul, ← map_mul]
    exact congr_arg (algebraMap HolU FracHolU) (by ext w; simp [μ_holU, g₂_U, g₃_U, f_U, holUMk_apply, μ_U])
  have htri : ∀ j : ℕ, ∃ c : ℕ → FracHolU,
      (∀ i ≤ j, c i ∈ E₀) ∧ c j = g₂ * g₃ * z_L ^ j ∧
      zEulerL^[j] (algebraMap HolU FracHolU μ_holU) =
        ∑ i ∈ Finset.range (j + 1), c i * fracEuler^[i] f_L := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun _ => g₂ * g₃, fun _ _ => E₀.mul_mem hg₂_mem hg₃_mem, by simp, ?_⟩
      simpa using hμ_prod
    | succ k ih =>
      obtain ⟨c, hc_mem, hc_top, hck⟩ := ih
      let c' : ℕ → FracHolU := fun i =>
        (if i ≤ k then z_L * fracEuler (c i) else 0) +
        (if 1 ≤ i then z_L * c (i - 1) else 0)
      refine ⟨c', ?_, ?_, ?_⟩
      · intro i hi
        refine E₀.add_mem ?_ ?_
        · split_ifs with hik
          · exact E₀.mul_mem hz_mem_E₀ (hE₀_closed' _ (hc_mem i hik))
          · exact E₀.zero_mem
        · split_ifs with hi1
          · exact E₀.mul_mem hz_mem_E₀ (hc_mem (i - 1) (by omega))
          · exact E₀.zero_mem
      · dsimp only [c']
        have h1 : ¬ (k + 1 ≤ k) := by omega
        have h2 : 1 ≤ k + 1 := by omega
        simp only [h1, ite_false, zero_add, h2, ite_true, Nat.add_sub_cancel, hc_top, pow_succ]
        ring
      · rw [Function.iterate_succ_apply', hck]
        dsimp only [zEulerL]
        have hsum_d : fracEuler (∑ i ∈ Finset.range (k + 1), c i * fracEuler^[i] f_L) =
            ∑ i ∈ Finset.range (k + 1),
              (fracEuler (c i) * fracEuler^[i] f_L + c i * fracEuler^[i + 1] f_L) := by
          have hgen : ∀ s : Finset ℕ,
              fracEuler (∑ i ∈ s, c i * fracEuler^[i] f_L) =
                ∑ i ∈ s, (fracEuler (c i) * fracEuler^[i] f_L + c i * fracEuler^[i + 1] f_L) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp [fracEuler_zero]
            | insert a s ha ihs =>
              rw [Finset.sum_insert ha, fracEuler_add, fracEuler_mul, ihs, Finset.sum_insert ha,
                Function.iterate_succ_apply']
          exact hgen _
        rw [hsum_d, Finset.mul_sum]
        simp_rw [mul_add, Finset.sum_add_distrib]
        have hrhs : ∑ i ∈ Finset.range (k + 2), c' i * fracEuler^[i] f_L =
            (∑ i ∈ Finset.range (k + 2), (if i ≤ k then z_L * fracEuler (c i) else 0) * fracEuler^[i] f_L) +
            (∑ i ∈ Finset.range (k + 2), (if 1 ≤ i then z_L * c (i - 1) else 0) * fracEuler^[i] f_L) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by dsimp [c']; ring
        rw [hrhs]
        congr 1
        · conv_rhs => rw [Finset.sum_range_succ]
          simp only [show ¬ k + 1 ≤ k by omega, ite_false, zero_mul, add_zero]
          refine Finset.sum_congr rfl fun i hi => by
            simp only [show i ≤ k by have := Finset.mem_range.mp hi; omega, ite_true]; ring
        · conv_rhs => rw [Finset.sum_range_succ']
          simp only [show ¬ 1 ≤ 0 by omega, ite_false, zero_mul, add_zero]
          refine Finset.sum_congr rfl fun i _ => by
            simp only [show 1 ≤ i + 1 by omega, ite_true, Nat.add_sub_cancel]; ring
  choose cMat hcMat_mem hcMat_top hcMat_eq using htri
  -- Build the triangular substitution `φ_L : Fin (r + 1) → MvPolynomial (Fin (r + 1)) FracHolU`:
  let φ_L : Fin (r + 1) → MvPolynomial (Fin (r + 1)) FracHolU := fun j =>
    ∑ i : Fin (r + 1), if i.1 ≤ j.1 then MvPolynomial.C (cMat j.1 i.1) * MvPolynomial.X i else 0
  let P₁_L : MvPolynomial (Fin (r + 1)) FracHolU :=
    MvPolynomial.map (Polynomial.eval₂RingHom (algebraMap ℂ FracHolU) g₁) P₁
  have hP₁_L_ne : P₁_L ≠ 0 := by
    obtain ⟨d₀, hd₀⟩ : P₁.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hP₁_ne (MvPolynomial.support_eq_empty.mp h0)
    intro h0
    have hc := congr_arg (fun q : MvPolynomial (Fin (r + 1)) FracHolU => q.coeff d₀) h0
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at hc
    exact hg₁_transc (P₁.coeff d₀) (MvPolynomial.mem_support_iff.mp hd₀) hc
  let P_E : MvPolynomial (Fin (r + 1)) FracHolU := MvPolynomial.aeval (R := FracHolU) φ_L P₁_L
  -- Triangular inversion proves `MvPolynomial.aeval φ_L` is injective, so `P_E ≠ 0`!
  have hP_E_ne : P_E ≠ 0 := by
    have hinv : ∀ k : ℕ, k ≤ r + 1 →
        ∃ ψ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) FracHolU,
          ∀ j : Fin (r + 1), j.1 < k → MvPolynomial.aeval (R := FracHolU) ψ (φ_L j) = MvPolynomial.X j := by
      intro k
      induction k with
      | zero => intro _; exact ⟨MvPolynomial.X, fun j hj => by omega⟩
      | succ k ih =>
        intro hk
        obtain ⟨ψ, hψ⟩ := ih (by omega)
        let j₀ : Fin (r + 1) := ⟨k, hk⟩
        have htop_ne : cMat k k ≠ 0 := by
          rw [hcMat_top k]; exact mul_ne_zero (mul_ne_zero hg₂_ne0 hg₃_ne0) (pow_ne_zero k hz_ne0)
        let val₀ : MvPolynomial (Fin (r + 1)) FracHolU :=
          MvPolynomial.C (cMat k k)⁻¹ *
            (MvPolynomial.X j₀ - ∑ i : Fin (r + 1), if i.1 < k then MvPolynomial.C (cMat k i.1) * ψ i else 0)
        let ψ' : Fin (r + 1) → MvPolynomial (Fin (r + 1)) FracHolU := fun i => if i = j₀ then val₀ else ψ i
        refine ⟨ψ', fun j hj => ?_⟩
        have hφ_ev : ∀ t : Fin (r + 1),
            MvPolynomial.aeval (R := FracHolU) ψ' (φ_L t) =
              ∑ i : Fin (r + 1), if i.1 ≤ t.1 then MvPolynomial.C (cMat t.1 i.1) * ψ' i else 0 := by
          intro t; simp only [φ_L, map_sum]
          refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
        by_cases hjk : j.1 < k
        · rw [hφ_ev j]
          have hsame : ∑ i : Fin (r + 1), (if i.1 ≤ j.1 then MvPolynomial.C (cMat j.1 i.1) * ψ' i else 0) =
              ∑ i : Fin (r + 1), (if i.1 ≤ j.1 then MvPolynomial.C (cMat j.1 i.1) * ψ i else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs with hij
            · have hne : i ≠ j₀ := by intro heq; subst heq; dsimp [j₀] at hij; omega
              simp [ψ', hne]
            · rfl
          rw [hsame, ← hψ j hjk]
          simp only [φ_L, map_sum]
          refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
        · have hjeq : j = j₀ := Fin.ext (by dsimp [j₀]; omega)
          subst hjeq
          rw [hφ_ev j₀]
          have hsplit : ∑ i : Fin (r + 1), (if i.1 ≤ k then MvPolynomial.C (cMat k i.1) * ψ' i else 0) =
              MvPolynomial.C (cMat k k) * ψ' j₀ +
              ∑ i : Fin (r + 1), if i.1 < k then MvPolynomial.C (cMat k i.1) * ψ i else 0 := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
            simp only [j₀, le_refl, ite_true]
            congr 1
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin (r + 1)))]
            simp only [lt_self_iff_false, ite_false, zero_add]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hne : i ≠ ⟨k, hk⟩ := (Finset.mem_erase.mp hi).1
            have hval_ne : i.1 ≠ k := fun h => hne (Fin.ext h)
            have hiff : i.1 ≤ k ↔ i.1 < k := by omega
            simp only [hiff]; split_ifs with hlt
            · simp [ψ', j₀, hne]
            · rfl
          dsimp only [j₀]
          have hψ'j : ψ' j₀ = val₀ := by simp [ψ']
          rw [hsplit, hψ'j]
          simp only [val₀, ← mul_assoc, ← map_mul, mul_inv_cancel₀ htop_ne, map_one, one_mul,
            sub_add_cancel]
          rfl
    obtain ⟨ψ, hψ⟩ := hinv (r + 1) le_rfl
    have hcomp : ∀ q : MvPolynomial (Fin (r + 1)) FracHolU,
        MvPolynomial.aeval (R := FracHolU) ψ (MvPolynomial.aeval (R := FracHolU) φ_L q) = q := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C c => simp
      | add q₁ q₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
      | mul_X q₁ j h₁ => simp only [map_mul, h₁, MvPolynomial.aeval_X, hψ j j.2]
    intro h0
    have := congr_arg (MvPolynomial.aeval (R := FracHolU) ψ) h0
    rw [hcomp, map_zero] at this
    exact hP₁_L_ne this
  -- Every coefficient of `P_E` belongs to `E₀`:
  have hP_E_coeffs : ∀ d ∈ P_E.support, P_E.coeff d ∈ E₀ := by
    have hsub : ∀ R : MvPolynomial (Fin (r + 1)) FracHolU,
        (∀ d ∈ R.support, R.coeff d ∈ E₀) → ∀ d, (MvPolynomial.aeval (R := FracHolU) φ_L R).coeff d ∈ E₀ := by
      let sub : Subring (MvPolynomial (Fin (r + 1)) FracHolU) :=
        { carrier := {Q | ∀ d, Q.coeff d ∈ E₀}
          mul_mem' := fun {A B} hA hB d => by
            rw [MvPolynomial.coeff_mul]
            exact E₀.sum_mem fun p _ => E₀.mul_mem (hA p.1) (hB p.2)
          one_mem' := fun d => by
            rw [MvPolynomial.coeff_one]; split_ifs <;> [exact E₀.one_mem; exact E₀.zero_mem]
          add_mem' := fun {A B} hA hB d => by
            rw [← MvPolynomial.lcoeff_apply, map_add, MvPolynomial.lcoeff_apply, MvPolynomial.lcoeff_apply]
            exact E₀.add_mem (hA d) (hB d)
          zero_mem' := fun _ => by simp [E₀.zero_mem]
          neg_mem' := fun {A} hA d => by
            rw [← MvPolynomial.lcoeff_apply, map_neg, MvPolynomial.lcoeff_apply]
            exact E₀.neg_mem (hA d) }
      have hφ_sub : ∀ j : Fin (r + 1), φ_L j ∈ sub := fun j => by
        refine sub.sum_mem fun i _ => ?_
        split_ifs with hij
        · refine sub.mul_mem (fun d => by
            rw [MvPolynomial.coeff_C]; split_ifs <;> [exact hcMat_mem j.1 i.1 hij; exact E₀.zero_mem])
            (fun d => by
              rw [MvPolynomial.coeff_X]; split_ifs <;> [exact E₀.one_mem; exact E₀.zero_mem])
        · exact sub.zero_mem
      intro R hR
      rw [MvPolynomial.as_sum (p := R), map_sum]
      refine sub.sum_mem fun s hs => ?_
      rw [MvPolynomial.aeval_monomial]
      exact sub.mul_mem (fun d => by
        rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C]
        split_ifs <;> [exact hR s hs; exact E₀.zero_mem])
        (sub.prod_mem fun j _ => sub.pow_mem (hφ_sub j) _)
    intro d _
    refine hsub P₁_L (fun s _ => ?_) d
    rw [MvPolynomial.coeff_map]
    have hp_E₀ : ∀ p : Polynomial ℂ, Polynomial.eval₂ (algebraMap ℂ FracHolU) g₁ p ∈ E₀ := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p₁ p₂ h₁ h₂ => rw [Polynomial.eval₂_add]; exact E₀.add_mem h₁ h₂
      | monomial k c =>
        rw [Polynomial.eval₂_monomial]
        have hcE : algebraMap ℂ FracHolU c ∈ E₀ := by
          have : algebraMap ℂ FracHolU c =
              algebraMap RatPoly FracHolU (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C c)) := by
            change algebraMap ℂ FracHolU c = ratPolyToFrac (algebraMap (Polynomial ℂ) RatPoly (Polynomial.C c))
            rw [ratPolyToFrac_algebraMap]
            exact congr_arg (algebraMap HolU FracHolU) (by ext w; simp [polyToHolU_apply])
          rw [this]; exact E₀.algebraMap_mem _
        exact E₀.mul_mem hcE (E₀.pow_mem hg₁_mem k)
    exact hp_E₀ (P₁.coeff s)
  -- `P_E` vanishes at `(f_L, fracEuler f_L, ..., fracEuler^r f_L)`:
  have hP_E_eval : MvPolynomial.eval (fun i : Fin (r + 1) => fracEuler^[i.1] f_L) P_E = 0 := by
    have hφ_ev : ∀ j : Fin (r + 1),
        MvPolynomial.eval (fun i : Fin (r + 1) => fracEuler^[i.1] f_L) (φ_L j) =
          zEulerL^[j.1] (algebraMap HolU FracHolU μ_holU) := by
      intro j
      rw [hcMat_eq j.1]
      dsimp only [φ_L]
      change MvPolynomial.eval₂ (RingHom.id FracHolU) (fun i : Fin (r + 1) => fracEuler^[i.1] f_L) _ = _
      rw [MvPolynomial.eval₂_sum]
      have hsum_eq : ∑ i : Fin (r + 1),
          (if i.1 ≤ j.1 then cMat j.1 i.1 * fracEuler^[i.1] f_L else 0) =
          ∑ i ∈ Finset.range (j.1 + 1), cMat j.1 i * fracEuler^[i] f_L := by
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun i _ => i.1)
          (fun i hi => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hi).2; omega))
          (fun a _ b _ hab => Fin.ext hab)
          (fun k hk => ⟨⟨k, by have := Finset.mem_range.mp hk; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; have := Finset.mem_range.mp hk; omega⟩, rfl⟩)
          (fun _ _ => rfl)
      rw [← hsum_eq]
      refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    have hcomp : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
        MvPolynomial.eval (fun i : Fin (r + 1) => fracEuler^[i.1] f_L)
          (MvPolynomial.aeval (R := FracHolU) φ_L
            (MvPolynomial.map (Polynomial.eval₂RingHom (algebraMap ℂ FracHolU) g₁) R)) =
        MvPolynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ FracHolU) g₁)
          (fun j : Fin (r + 1) => zEulerL^[j.1] (algebraMap HolU FracHolU μ_holU)) R := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C p => simp
      | add R₁ R₂ h₁ h₂ =>
        rw [RingHom.map_add, map_add, RingHom.map_add, MvPolynomial.eval₂_add, h₁, h₂]
      | mul_X R₁ j h₁ =>
        rw [RingHom.map_mul, MvPolynomial.map_X, map_mul, MvPolynomial.aeval_X,
          RingHom.map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, h₁, hφ_ev j]
    rw [hcomp P₁, hP₁_vanish_L]
  -- Step 5: Eliminate `(g₁, g₂, g₃)` via transcendence degree to get a nonzero Euler ADE `Q` over `ℂ[X]`!
  obtain ⟨N, Q, hQ_ne, hQ_eval⟩ :=
    exists_nonzero_poly_ade_of_adjoin_ade g₁ g₂ g₃ f_L hg₁_E₀ hg₂_E₀ hg₃_E₀ P_E hP_E_ne hP_E_coeffs hP_E_eval
  -- Pull `Q` back to pointwise vanishing on `x > 0`, pass through Watson's Lemma, and contradict Sibuya!
  have hf_iter_an : ∀ j : ℕ, AnalyticOnNhd ℂ (eulerOpC^[j] (volterraLaplace β α)) rightHalfPlane := by
    intro j
    induction j with
    | zero => exact hf_an
    | succ k ih => rw [Function.iterate_succ_apply']; exact analyticOnNhd_id.mul ih.deriv
  have hf_iter_L : ∀ j : ℕ, fracEuler^[j] f_L = algebraMap HolU FracHolU (holUMk (hf_iter_an j)) := by
    intro j
    induction j with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, fracEuler_algebraMap, holUEuler_mk]
      congr 1; ext w; simp [holUMk_apply, Function.iterate_succ_apply', eulerOpC]
  have hQ_pt : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval₂ (Polynomial.evalRingHom (x : ℂ))
        (fun i : Fin (N + 1) => (eulerOpC^[i.1] (volterraLaplace β α)) (x : ℂ)) Q = 0 := by
    let Q_U : HolU :=
      MvPolynomial.eval₂ polyToHolU (fun i : Fin (N + 1) => holUMk (hf_iter_an i.1)) Q
    have hQ_U_zero : Q_U = 0 := by
      apply IsFractionRing.injective HolU FracHolU
      rw [map_zero, ← hQ_eval]
      dsimp only [Q_U]
      have hgen : ∀ R : MvPolynomial (Fin (N + 1)) (Polynomial ℂ),
          algebraMap HolU FracHolU
            (MvPolynomial.eval₂ polyToHolU (fun i : Fin (N + 1) => holUMk (hf_iter_an i.1)) R) =
          MvPolynomial.eval₂ (ratPolyToFrac.comp (algebraMap (Polynomial ℂ) RatPoly))
            (fun i : Fin (N + 1) => fracEuler^[i.1] f_L) R := by
        intro R
        induction R using MvPolynomial.induction_on with
        | C p =>
          rw [MvPolynomial.eval₂_C, MvPolynomial.eval₂_C, RingHom.comp_apply, ratPolyToFrac_algebraMap]
        | add R₁ R₂ h₁ h₂ =>
          rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, RingHom.map_add, h₁, h₂]
        | mul_X R₁ j h₁ =>
          rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
            MvPolynomial.eval₂_X, RingHom.map_mul, h₁, hf_iter_L j.1]
      exact hgen Q
    intro x hx
    have hval := congr_arg (fun g : HolU => g.1 ⟨(x : ℂ), by simpa [rightHalfPlane] using hx⟩) hQ_U_zero
    rw [ZeroMemClass.coe_zero, Pi.zero_apply] at hval
    rw [← hval]
    dsimp only [Q_U]
    have hgen2 : ∀ R : MvPolynomial (Fin (N + 1)) (Polynomial ℂ),
        MvPolynomial.eval₂ (Polynomial.evalRingHom (x : ℂ))
          (fun i : Fin (N + 1) => (eulerOpC^[i.1] (volterraLaplace β α)) (x : ℂ)) R =
        (MvPolynomial.eval₂ polyToHolU (fun i : Fin (N + 1) => holUMk (hf_iter_an i.1)) R).1
          ⟨(x : ℂ), by simpa [rightHalfPlane] using hx⟩ := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C p =>
        rw [MvPolynomial.eval₂_C, MvPolynomial.eval₂_C, polyToHolU_apply]; rfl
      | add R₁ R₂ h₁ h₂ =>
        rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, h₁, h₂]; rfl
      | mul_X R₁ j h₁ =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
          MvPolynomial.eval₂_X, h₁]; rfl
    exact hgen2 Q
  -- Pass through `HasAsympExpAtZero`!
  have hasymp_Q : HasAsympExpAtZero (fun _ : ℝ => (0 : ℂ)) (evalEulerPS Q (volterraAsympSeries β α)) := by
    refine hasAsympExpAtZero_congr (fun x hx => hQ_pt x hx) ?_
    exact hasAsympExpAtZero_mvPolynomial Q fun i =>
      hasAsympExpAtZero_eulerIter_volterraLaplace α i.1 β hβ
  have hPS_zero : evalEulerPS Q (volterraAsympSeries β α) = 0 :=
    eq_zero_of_hasAsympExpAtZero_zero hasymp_Q
  -- Contradict Sibuya's convergence theorem + sub-Gevrey + divergence!
  have hconv : IsConvergentPS (volterraAsympSeries β α) :=
    sibuya_subGevrey_convergent_euler hQ_ne (volterraAsympSeries_isSubGevrey α β hβ) hPS_zero
  exact volterraAsympSeries_not_convergent α β hβ hconv

private lemma contDiffOn_deriv_iter {f : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ⊤ f s) (k : ℕ) : ContDiffOn ℝ ⊤ (deriv^[k] f) s := by
  induction k with
  | zero => exact hf
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.deriv_of_isOpen hs (by simp)

/-- **Master Theorem 1 (`volterraMu_no_rat_ade_Ioo`):**
For every `α : ℂ` and `β : ℂ` with `-1 < β.re`, the generalized Volterra function `μ(t, β, α)`
satisfies NO nonzero polynomial algebraic differential equation over `ℂ[t]` on `(0, 1)`. -/
theorem volterraMu_no_rat_ade_Ioo (α β : ℂ) (hβ : -1 < β.re) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioo (0 : ℝ) 1, evalRealADE P (volterraMu β α) t = 0) : False := by
  let μ_U : ℂ → ℂ := fun z =>
    Complex.exp (-α / z) * (z ^ (β + 1)) * volterraLaplace β α z
  have hg2_an : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-α / z)) rightHalfPlane := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_rightHalfPlane
    have hzne : z ≠ 0 := by intro h0; rw [h0] at hz; simp [rightHalfPlane] at hz
    exact ((differentiableAt_const (-α)).div differentiableAt_id hzne).cexp.differentiableWithinAt
  have hg3_an : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (β + 1)) rightHalfPlane := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_rightHalfPlane
    have hz_slit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
    exact (Complex.hasStrictDerivAt_cpow_const hz_slit).hasDerivAt.differentiableAt.differentiableWithinAt
  have hμU_an : AnalyticOnNhd ℂ μ_U rightHalfPlane :=
    (hg2_an.mul hg3_an).mul (analyticOnNhd_volterraLaplace β α hβ)
  have hμ_eq_Ioo : Set.EqOn (volterraMu β α) (fun t => μ_U (((-(1 : ℝ) / Real.log t : ℝ) : ℂ)))
      (Set.Ioo (0 : ℝ) 1) := by
    intro t ⟨ht0, ht1⟩
    have hlog_neg : Real.log t < 0 := Real.log_neg ht0 ht1
    have hxpos : 0 < -(1 : ℝ) / Real.log t := div_pos_of_neg_of_neg (by norm_num) hlog_neg
    have hexp_eq : Real.exp (-(1 : ℝ) / (-(1 : ℝ) / Real.log t)) = t := by
      have : -(1 : ℝ) / (-(1 : ℝ) / Real.log t) = Real.log t := by field_simp [hlog_neg.ne]
      rw [this, Real.exp_log ht0]
    have h := volterraMu_exp_neg_inv β α hxpos
    rw [hexp_eq] at h; exact h
  have hμ_smooth : ∀ k : ℕ, DifferentiableOn ℝ (deriv^[k] (volterraMu β α)) (Set.Ioo (0 : ℝ) 1) := by
    have hlog_cd : ContDiffOn ℝ ⊤ (fun t : ℝ => -(1 : ℝ) / Real.log t) (Set.Ioo (0 : ℝ) 1) :=
      ContDiffOn.div contDiffOn_const (contDiffOn_log.mono fun t ht => ht.1.ne')
        (fun t ht => (Real.log_neg ht.1 ht.2).ne)
    have hμU_cd : ContDiffOn ℝ ⊤ (fun x : ℝ => μ_U (x : ℂ)) (Set.Ioi (0 : ℝ)) :=
      ((hμU_an.contDiffOn isOpen_rightHalfPlane.uniqueDiffOn).restrict_scalars ℝ).comp
        Complex.ofRealCLM.contDiff.contDiffOn fun x hx => by
          simpa [rightHalfPlane] using hx
    have hμ_cd : ContDiffOn ℝ ⊤ (volterraMu β α) (Set.Ioo (0 : ℝ) 1) :=
      (hμU_cd.comp hlog_cd fun t ht => div_pos_of_neg_of_neg (by norm_num) (Real.log_neg ht.1 ht.2)).congr
        hμ_eq_Ioo
    intro k
    exact (contDiffOn_deriv_iter isOpen_Ioo hμ_cd k).differentiableOn (by simp)
  obtain ⟨P₁, hP₁_ne, hP₁_eval⟩ := exists_nonzero_real_euler_ade_on_open isOpen_Ioo hP hμ_smooth hADE
  exact volterraMu_no_euler_ade_Ioo α β hβ P₁ hP₁_ne hP₁_eval

/-- **Master Theorem 1' (`volterraMu_no_rat_ade`):**
For every `α : ℂ` and `β : ℂ` with `-1 < β.re`, the generalized Volterra function `μ(t, β, α)`
satisfies NO nonzero polynomial algebraic differential equation over `ℂ[t]` on `(0, ∞)`. -/
theorem volterraMu_no_rat_ade (α β : ℂ) (hβ : -1 < β.re) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioi (0 : ℝ), evalRealADE P (volterraMu β α) t = 0) : False :=
  volterraMu_no_rat_ade_Ioo α β hβ P hP fun t ht => hADE t ht.1

/-!
## Section 4: Interacting Quantum Gas Virial Differential Transcendence & Exact Laplace Transform
-/

/-- **Master Theorem 2 (`volterraNu_no_rat_ade`):**
Volterra's function `ν(t)` (equivalently Ramanujan's integral and the interacting 2D two-component
Fermi gas second virial shift `Δb₂^{(2D)}(t)`) satisfies NO nonzero polynomial algebraic
differential equation over `ℂ[t]` on `(0, ∞)` (nor even on `(0, 1)`). -/
theorem volterraNu_no_rat_ade {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioi (0 : ℝ), evalRealADE P volterraNu t = 0) : False := by
  have heq : volterraMu 0 0 = volterraNu := funext volterraMu_zero_zero
  exact volterraMu_no_rat_ade 0 0 (by simp) P hP (by simpa [heq] using hADE)

/-- **Master Theorem 3 (`volterraNu_temp_no_rat_ade`):**
For any dimer binding energy `E_B > 0`, the temperature-variable interacting 2D Fermi gas second
virial shift `T ↦ ν(E_B / T)` satisfies NO nonzero polynomial ADE over `ℂ[T]` on `(0, ∞)`. -/
theorem volterraNu_temp_no_rat_ade {E_B : ℝ} (hE : 0 < E_B) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ T ∈ Set.Ioi (0 : ℝ), evalRealADE P (fun T => volterraNu (E_B / T)) T = 0) : False := by
  let g : ℝ → ℂ := fun T => volterraNu (E_B / T)
  -- `g` is smooth on `(E_B, ∞)` because `T ↦ E_B / T` maps `(E_B, ∞)` into `(0, 1)`!
  have hν_cd : ContDiffOn ℝ ⊤ volterraNu (Set.Ioo (0 : ℝ) 1) := by
    have hlog_cd : ContDiffOn ℝ ⊤ (fun t : ℝ => -(1 : ℝ) / Real.log t) (Set.Ioo (0 : ℝ) 1) :=
      ContDiffOn.div contDiffOn_const (contDiffOn_log.mono fun t ht => ht.1.ne')
        (fun t ht => (Real.log_neg ht.1 ht.2).ne)
    have hμU_an : AnalyticOnNhd ℂ (fun z : ℂ => z * volterraLaplace 0 0 z) rightHalfPlane :=
      analyticOnNhd_id.mul (analyticOnNhd_volterraLaplace 0 0 (by simp))
    have hμU_cd : ContDiffOn ℝ ⊤ (fun x : ℝ => (x : ℂ) * volterraLaplace 0 0 (x : ℂ)) (Set.Ioi (0 : ℝ)) :=
      ((hμU_an.contDiffOn isOpen_rightHalfPlane.uniqueDiffOn).restrict_scalars ℝ).comp
        Complex.ofRealCLM.contDiff.contDiffOn fun x hx => by
          simpa [rightHalfPlane] using hx
    have hcomp := hμU_cd.comp hlog_cd fun t ht => div_pos_of_neg_of_neg (by norm_num) (Real.log_neg ht.1 ht.2)
    refine hcomp.congr fun t ⟨ht0, ht1⟩ => ?_
    have hlog_neg : Real.log t < 0 := Real.log_neg ht0 ht1
    have hxpos : 0 < -(1 : ℝ) / Real.log t := div_pos_of_neg_of_neg (by norm_num) hlog_neg
    have hexp : Real.exp (-(1 : ℝ) / (-(1 : ℝ) / Real.log t)) = t := by
      have : -(1 : ℝ) / (-(1 : ℝ) / Real.log t) = Real.log t := by field_simp [hlog_neg.ne]
      rw [this, Real.exp_log ht0]
    have h := volterraMu_exp_neg_inv 0 0 hxpos
    rw [hexp, volterraMu_zero_zero] at h
    simpa using h
  have hg_cd : ContDiffOn ℝ ⊤ g (Set.Ioi E_B) := by
    have hdiv_cd : ContDiffOn ℝ ⊤ (fun T : ℝ => E_B / T) (Set.Ioi E_B) :=
      ContDiffOn.div contDiffOn_const contDiffOn_id fun T hT => (lt_trans hE hT).ne'
    exact hν_cd.comp hdiv_cd fun T hT =>
      ⟨div_pos hE (lt_trans hE hT), (div_lt_one (lt_trans hE hT)).mpr hT⟩
  have hg_diff : ∀ k : ℕ, DifferentiableOn ℝ (deriv^[k] g) (Set.Ioi E_B) := fun k =>
    (contDiffOn_deriv_iter isOpen_Ioi hg_cd k).differentiableOn (by simp)
  -- Prove `eulerOpR^[j] g T = (-1)^j * eulerOpR^[j] volterraNu (E_B / T)` on `T > E_B`!
  have heuler_inv : ∀ (j : ℕ) (T : ℝ), E_B < T →
      (eulerOpR^[j] g) T = (-1 : ℂ) ^ j * (eulerOpR^[j] volterraNu) (E_B / T) := by
    intro j
    induction j with
    | zero => intro T _; simp [g]
    | succ m ih =>
      intro T hT
      have hTpos : 0 < T := lt_trans hE hT
      have ht_mem : E_B / T ∈ Set.Ioo (0 : ℝ) 1 := ⟨div_pos hE hTpos, (div_lt_one hTpos).mpr hT⟩
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hev : (eulerOpR^[m] g) =ᶠ[nhds T] fun S => (-1 : ℂ) ^ m * (eulerOpR^[m] volterraNu) (E_B / S) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi E_B, isOpen_Ioi.mem_nhds hT, fun S hS => ih S hS⟩
      have hνm_diff : DifferentiableAt ℝ (eulerOpR^[m] volterraNu) (E_B / T) := by
        have heq_back : Set.EqOn (eulerOpR^[m] volterraNu)
            (fun t => (-1 : ℂ) ^ m * (eulerOpR^[m] g) (E_B / t)) (Set.Ioo (0 : ℝ) 1) := by
          intro t ⟨ht0, ht1⟩
          have hS : E_B < E_B / t := (lt_div_iff₀ ht0).mpr (by nlinarith)
          have hinv_t : E_B / (E_B / t) = t := by field_simp [hE.ne', ht0.ne']
          have h1 := ih (E_B / t) hS
          rw [hinv_t] at h1
          dsimp only
          rw [h1, ← mul_assoc, ← mul_pow]; norm_num
        have hgm_diff : DifferentiableAt ℝ (eulerOpR^[m] g) (E_B / (E_B / T)) := by
          have hinv_T : E_B / (E_B / T) = T := by field_simp [hE.ne', hTpos.ne']
          rw [hinv_T]
          have hcd_m : ContDiffOn ℝ ⊤ (eulerOpR^[m] g) (Set.Ioi E_B) := by
            clear hev heq_back hinv_T ih
            induction m with
            | zero => exact hg_cd
            | succ q ihq =>
              rw [Function.iterate_succ_apply']
              exact (Complex.ofRealCLM.contDiff.contDiffOn).mul (ihq.deriv_of_isOpen isOpen_Ioi (by simp))
          exact (hcd_m.differentiableOn (by simp) T hT).differentiableAt (isOpen_Ioi.mem_nhds hT)
        have hdiv_d : DifferentiableAt ℝ (fun t : ℝ => E_B / t) (E_B / T) :=
          DifferentiableAt.div (differentiableAt_const _) differentiableAt_id ht_mem.1.ne'
        have hcomp_d : DifferentiableAt ℝ (fun t => (-1 : ℂ) ^ m * (eulerOpR^[m] g) (E_B / t)) (E_B / T) :=
          (hgm_diff.comp _ hdiv_d).const_mul _
        exact hcomp_d.congr_of_eventuallyEq
          (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 0 1, isOpen_Ioo.mem_nhds ht_mem, heq_back⟩)
      have hdiv_d : HasDerivAt (fun S : ℝ => E_B / S) (-(E_B / T ^ 2)) T := by
        have h1 := (hasDerivAt_inv hTpos.ne').const_mul E_B
        convert h1 using 1
        · ext S; rw [div_eq_mul_inv]
        · ring
      have hcomp_d : HasDerivAt (fun S => (-1 : ℂ) ^ m * (eulerOpR^[m] volterraNu) (E_B / S))
          ((-1 : ℂ) ^ m * ((-(E_B / T ^ 2) : ℝ) • deriv (eulerOpR^[m] volterraNu) (E_B / T))) T :=
        (hνm_diff.hasDerivAt.scomp T hdiv_d).const_mul _
      dsimp only [eulerOpR]
      rw [hev.deriv_eq, hcomp_d.deriv, Complex.real_smul, pow_succ]
      have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hTpos.ne'
      push_cast; field_simp [hTne]; ring
  -- Convert `P` on `Set.Ioi E_B` into a nonzero Euler ADE `P₁` in `T`:
  obtain ⟨P₁, hP₁_ne, hP₁_eval⟩ := exists_nonzero_real_euler_ade_on_open isOpen_Ioi hP hg_diff
    (fun T hT => hADE T (lt_trans hE hT))
  -- Replace `T ↦ E_B / t` (multiply by `t^M`) and `Y_j ↦ (-1)^j Y_j` to get a nonzero Euler ADE `Q` for `ν` on `(0, 1)`!
  let M : ℕ := P₁.support.sup (fun d => (P₁.coeff d).natDegree)
  let revPoly : Polynomial ℂ → Polynomial ℂ := fun p =>
    ∑ k ∈ Finset.range (M + 1), Polynomial.monomial (M - k) (p.coeff k * (E_B : ℂ) ^ k)
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ d ∈ P₁.support,
      MvPolynomial.monomial d
        (revPoly (P₁.coeff d) * Polynomial.C (∏ j : Fin (r + 1), ((-1 : ℂ) ^ j.1) ^ d j))
  have hQ_ne : Q ≠ 0 := by
    obtain ⟨d₀, hd₀⟩ : P₁.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h0; exact hP₁_ne (MvPolynomial.support_eq_empty.mp h0)
    have hp₀_ne : P₁.coeff d₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hd₀
    let k₀ : ℕ := (P₁.coeff d₀).natDegree
    have hk₀_le : k₀ ≤ M := Finset.le_sup (f := fun d => (P₁.coeff d).natDegree) hd₀
    have hcoeff_k₀ : (P₁.coeff d₀).coeff k₀ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp₀_ne
    intro hQ0
    have hQd₀ := congr_arg (fun q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) => q.coeff d₀) hQ0
    rw [AddMonoidAlgebra.coeff_zero] at hQd₀
    have hQd₀_eq : Q.coeff d₀ =
        revPoly (P₁.coeff d₀) * Polynomial.C (∏ j : Fin (r + 1), ((-1 : ℂ) ^ j.1) ^ d₀ j) := by
      dsimp only [Q]
      rw [← MvPolynomial.lcoeff_apply, map_sum]
      simp only [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single d₀]
      · simp
      · intro d _ hne; simp [hne]
      · intro h; exact absurd hd₀ h
    rw [hQd₀_eq] at hQd₀
    have hsign_ne : (∏ j : Fin (r + 1), ((-1 : ℂ) ^ j.1) ^ d₀ j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (pow_ne_zero _ (by norm_num))
    have hrev0 : revPoly (P₁.coeff d₀) = 0 :=
      (mul_eq_zero.mp hQd₀).resolve_right (fun hc => hsign_ne (Polynomial.C_eq_zero.mp hc))
    have hmk := congr_arg (fun p : Polynomial ℂ => p.coeff (M - k₀)) hrev0
    rw [Polynomial.coeff_zero] at hmk
    have hrev_c : (revPoly (P₁.coeff d₀)).coeff (M - k₀) = (P₁.coeff d₀).coeff k₀ * (E_B : ℂ) ^ k₀ := by
      dsimp only [revPoly]
      rw [← Polynomial.lcoeff_apply, map_sum]
      simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single k₀]
      · simp
      · intro k hk hne
        have hk_le : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hsub_ne : M - k ≠ M - k₀ := by omega
        simp [hsub_ne]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hrev_c] at hmk
    have hE_ne : (E_B : ℂ) ≠ 0 := by exact_mod_cast hE.ne'
    exact mul_ne_zero hcoeff_k₀ (pow_ne_zero k₀ hE_ne) hmk
  have hQ_eval : ∀ t ∈ Set.Ioo (0 : ℝ) 1, evalRealEulerADE Q (volterraMu 0 0) t = 0 := by
    intro t ⟨ht0, ht1⟩
    have hT : E_B < E_B / t := (lt_div_iff₀ ht0).mpr (by nlinarith)
    have ht_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hinv_t : E_B / (E_B / t) = t := by field_simp [hE.ne', ht0.ne']
    have hrev_eval : ∀ d ∈ P₁.support,
        (revPoly (P₁.coeff d)).eval (t : ℂ) = (t : ℂ) ^ M * (P₁.coeff d).eval ((E_B / t : ℝ) : ℂ) := by
      intro d hd
      have hdeg_le : (P₁.coeff d).natDegree ≤ M := Finset.le_sup (f := fun s => (P₁.coeff s).natDegree) hd
      dsimp only [revPoly]
      rw [← Polynomial.coe_evalRingHom, map_sum]
      simp only [Polynomial.coe_evalRingHom]
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_le), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Polynomial.eval_monomial]
      push_cast
      have hpow : (t : ℂ) ^ M * ((E_B : ℂ) / (t : ℂ)) ^ k = (E_B : ℂ) ^ k * (t : ℂ) ^ (M - k) := by
        rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero k ht_ne)]
        have : (t : ℂ) ^ (M - k) * (t : ℂ) ^ k = (t : ℂ) ^ M := by
          rw [← pow_add, Nat.sub_add_cancel hk_le]
        linear_combination (E_B : ℂ) ^ k * this.symm
      linear_combination (P₁.coeff d).coeff k * hpow.symm
    have hμ0 : volterraMu 0 0 = volterraNu := funext volterraMu_zero_zero
    rw [hμ0]
    have hQ_eq : evalRealEulerADE Q volterraNu t = (t : ℂ) ^ M * evalRealEulerADE P₁ g (E_B / t) := by
      dsimp only [evalRealEulerADE, Q]
      rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_eq', Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, hrev_eval d hd]
      have hprod_eq : ∏ j : Fin (r + 1), (eulerOpR^[j.1] g (E_B / t)) ^ d j =
          (∏ j : Fin (r + 1), ((-1 : ℂ) ^ j.1) ^ d j) * ∏ j : Fin (r + 1), (eulerOpR^[j.1] volterraNu t) ^ d j := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [heuler_inv j.1 (E_B / t) hT, hinv_t, mul_pow]
      rw [hprod_eq]; ring
    rw [hQ_eq, hP₁_eval (E_B / t) hT, mul_zero]
  exact volterraMu_no_euler_ade_Ioo 0 0 (by simp) Q hQ_ne hQ_eval

/-- **Master Theorem 4 (`volterraNu_eulerDeriv_no_rat_ade`):**
The logarithmic derivative `t ↦ t * deriv volterraNu t` satisfies NO nonzero polynomial ADE over
`ℂ[t]` on `(0, ∞)`. -/
theorem volterraNu_eulerDeriv_no_rat_ade {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioi (0 : ℝ), evalRealADE P (eulerOpR volterraNu) t = 0) : False := by
  have hν_cd : ContDiffOn ℝ ⊤ volterraNu (Set.Ioo (0 : ℝ) 1) := by
    have hlog_cd : ContDiffOn ℝ ⊤ (fun t : ℝ => -(1 : ℝ) / Real.log t) (Set.Ioo (0 : ℝ) 1) :=
      ContDiffOn.div contDiffOn_const (contDiffOn_log.mono fun t ht => ht.1.ne')
        (fun t ht => (Real.log_neg ht.1 ht.2).ne)
    have hμU_an : AnalyticOnNhd ℂ (fun z : ℂ => z * volterraLaplace 0 0 z) rightHalfPlane :=
      analyticOnNhd_id.mul (analyticOnNhd_volterraLaplace 0 0 (by simp))
    have hμU_cd : ContDiffOn ℝ ⊤ (fun x : ℝ => (x : ℂ) * volterraLaplace 0 0 (x : ℂ)) (Set.Ioi (0 : ℝ)) :=
      ((hμU_an.contDiffOn isOpen_rightHalfPlane.uniqueDiffOn).restrict_scalars ℝ).comp
        Complex.ofRealCLM.contDiff.contDiffOn fun x hx => by
          simpa [rightHalfPlane] using hx
    refine (hμU_cd.comp hlog_cd fun t ht => div_pos_of_neg_of_neg (by norm_num) (Real.log_neg ht.1 ht.2)).congr
      fun t ⟨ht0, ht1⟩ => ?_
    have hlog_neg : Real.log t < 0 := Real.log_neg ht0 ht1
    have hxpos : 0 < -(1 : ℝ) / Real.log t := div_pos_of_neg_of_neg (by norm_num) hlog_neg
    have hexp : Real.exp (-(1 : ℝ) / (-(1 : ℝ) / Real.log t)) = t := by
      have : -(1 : ℝ) / (-(1 : ℝ) / Real.log t) = Real.log t := by field_simp [hlog_neg.ne]
      rw [this, Real.exp_log ht0]
    have h := volterraMu_exp_neg_inv 0 0 hxpos
    rw [hexp, volterraMu_zero_zero] at h
    simpa using h
  have hd_cd : ContDiffOn ℝ ⊤ (eulerOpR volterraNu) (Set.Ioo (0 : ℝ) 1) :=
    (Complex.ofRealCLM.contDiff.contDiffOn).mul (hν_cd.deriv_of_isOpen isOpen_Ioo (by simp))
  have hd_diff : ∀ k : ℕ, DifferentiableOn ℝ (deriv^[k] (eulerOpR volterraNu)) (Set.Ioo (0 : ℝ) 1) := fun k =>
    (contDiffOn_deriv_iter isOpen_Ioo hd_cd k).differentiableOn (by simp)
  obtain ⟨P₁, hP₁_ne, hP₁_eval⟩ := exists_nonzero_real_euler_ade_on_open isOpen_Ioo hP hd_diff
    (fun t ht => hADE t ht.1)
  -- Shift variables `Y_j ↦ Y_{j+1}` via `MvPolynomial.rename Fin.succ`:
  let Q : MvPolynomial (Fin (r + 2)) (Polynomial ℂ) := MvPolynomial.rename Fin.succ P₁
  have hQ_ne : Q ≠ 0 := by
    intro h0
    apply hP₁_ne
    apply MvPolynomial.rename_injective Fin.succ (Fin.succ_injective (r + 1))
    rw [map_zero]
    exact h0
  have hQ_eval : ∀ t ∈ Set.Ioo (0 : ℝ) 1, evalRealEulerADE Q (volterraMu 0 0) t = 0 := by
    intro t ht
    have hμ0 : volterraMu 0 0 = volterraNu := funext volterraMu_zero_zero
    rw [hμ0]
    have h1 := hP₁_eval t ht
    rw [← h1]
    dsimp only [evalRealEulerADE, Q]
    rw [MvPolynomial.eval₂_rename]
    refine congr_arg (fun g => MvPolynomial.eval₂ (Polynomial.evalRingHom (t : ℂ)) g P₁) (funext fun i => ?_)
    exact congr_fun (Function.iterate_succ_apply eulerOpR i.1 volterraNu) t
  exact volterraMu_no_euler_ade_Ioo 0 0 (by simp) Q hQ_ne hQ_eval

/-- The interacting 1D three-species Fermi gas third virial shift:
`Δb₃^{(1D)}(t) = ν(t) / √3`. -/
@[expose] noncomputable def fermiGas1D_virial3 (t : ℝ) : ℂ :=
  volterraNu t / (Real.sqrt 3 : ℂ)

/-- **Master Theorem 5 (`fermiGas1D_virial3_no_rat_ade`):**
The interacting 1D three-species Fermi gas third virial shift `Δb₃^{(1D)}(t) = ν(t) / √3`
satisfies NO nonzero polynomial ADE over `ℂ[t]` on `(0, ∞)`. -/
theorem fermiGas1D_virial3_no_rat_ade {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioi (0 : ℝ), evalRealADE P fermiGas1D_virial3 t = 0) : False := by
  let c : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)⁻¹
  have hc_ne : c ≠ 0 := by
    dsimp [c]; apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  -- Substitute `Y_j ↦ c * Y_j`:
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.aeval (R := Polynomial ℂ) (fun i => MvPolynomial.C (Polynomial.C c) * MvPolynomial.X i) P
  have hQ_ne : Q ≠ 0 := by
    let Qinv := MvPolynomial.aeval (R := Polynomial ℂ)
      (fun i : Fin (r + 1) => MvPolynomial.C (Polynomial.C c⁻¹) * MvPolynomial.X i)
    have hcomp : Qinv Q = P := by
      have hgen : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
          Qinv (MvPolynomial.aeval (R := Polynomial ℂ)
            (fun i => MvPolynomial.C (Polynomial.C c) * MvPolynomial.X i) R) = R := by
        intro R
        induction R using MvPolynomial.induction_on with
        | C p => simp [Qinv]
        | add R₁ R₂ h₁ h₂ =>
          rw [map_add, map_add, h₁, h₂]
        | mul_X R₁ j h₁ =>
          simp only [Qinv, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq] at h₁ ⊢
          rw [h₁, ← mul_assoc (MvPolynomial.C (Polynomial.C c)), ← map_mul, ← Polynomial.C_mul,
            mul_inv_cancel₀ hc_ne, map_one, map_one, one_mul]
      exact hgen P
    intro h0; rw [h0, map_zero] at hcomp; exact hP hcomp.symm
  have hderiv_scale : ∀ k : ℕ, deriv^[k] fermiGas1D_virial3 = fun t => c * deriv^[k] volterraNu t := by
    intro k
    induction k with
    | zero => ext t; simp [fermiGas1D_virial3, c, div_eq_mul_inv, mul_comm]
    | succ m ih =>
      ext t
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, deriv_const_mul_field]
  refine volterraNu_no_rat_ade Q hQ_ne fun t ht => ?_
  have h1 := hADE t ht
  rw [← h1]
  dsimp only [evalRealADE, Q]
  have hgen : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      MvPolynomial.eval₂ (Polynomial.evalRingHom (t : ℂ)) (fun i => deriv^[i.1] volterraNu t)
        (MvPolynomial.aeval (R := Polynomial ℂ)
          (fun i => MvPolynomial.C (Polynomial.C c) * MvPolynomial.X i) R) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom (t : ℂ)) (fun i => deriv^[i.1] fermiGas1D_virial3 t) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C p => simp
    | add R₁ R₂ h₁ h₂ =>
      rw [map_add, MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, h₁, h₂]
    | mul_X R₁ j h₁ =>
      rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
        h₁, Polynomial.coe_evalRingHom, Polynomial.eval_C, hderiv_scale j.1]
  exact hgen P

/-- **Master Theorem 6 (`fermiGas1D_virial3_temp_no_rat_ade`):**
For any binding energy `E_B > 0`, the temperature-variable 1D three-species Fermi gas third virial
shift `T ↦ Δb₃^{(1D)}(E_B / T)` satisfies NO nonzero polynomial ADE over `ℂ[T]` on `(0, ∞)`. -/
theorem fermiGas1D_virial3_temp_no_rat_ade {E_B : ℝ} (hE : 0 < E_B) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ T ∈ Set.Ioi (0 : ℝ), evalRealADE P (fun T => fermiGas1D_virial3 (E_B / T)) T = 0) : False := by
  let c : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)⁻¹
  have hc_ne : c ≠ 0 := by
    dsimp [c]; apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.aeval (R := Polynomial ℂ) (fun i => MvPolynomial.C (Polynomial.C c) * MvPolynomial.X i) P
  have hQ_ne : Q ≠ 0 := by
    let Qinv := MvPolynomial.aeval (R := Polynomial ℂ)
      (fun i : Fin (r + 1) => MvPolynomial.C (Polynomial.C c⁻¹) * MvPolynomial.X i)
    have hcomp : Qinv Q = P := by
      have hgen : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
          Qinv (MvPolynomial.aeval (R := Polynomial ℂ)
            (fun i => MvPolynomial.C (Polynomial.C c) * MvPolynomial.X i) R) = R := by
        intro R
        induction R using MvPolynomial.induction_on with
        | C p => simp [Qinv]
        | add R₁ R₂ h₁ h₂ =>
          rw [map_add, map_add, h₁, h₂]
        | mul_X R₁ j h₁ =>
          simp only [Qinv, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq] at h₁ ⊢
          rw [h₁, ← mul_assoc (MvPolynomial.C (Polynomial.C c)), ← map_mul, ← Polynomial.C_mul,
            mul_inv_cancel₀ hc_ne, map_one, map_one, one_mul]
      exact hgen P
    intro h0; rw [h0, map_zero] at hcomp; exact hP hcomp.symm
  have hderiv_scale : ∀ k : ℕ,
      deriv^[k] (fun T => fermiGas1D_virial3 (E_B / T)) =
        fun T => c * deriv^[k] (fun T => volterraNu (E_B / T)) T := by
    intro k
    induction k with
    | zero => ext T; simp [fermiGas1D_virial3, c, div_eq_mul_inv, mul_comm]
    | succ m ih =>
      ext T
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, deriv_const_mul_field]
  refine volterraNu_temp_no_rat_ade hE Q hQ_ne fun T hT => ?_
  have h1 := hADE T hT
  rw [← h1]
  dsimp only [evalRealADE, Q]
  have hgen : ∀ R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      MvPolynomial.eval₂ (Polynomial.evalRingHom (T : ℂ)) (fun i => deriv^[i.1] (fun S => volterraNu (E_B / S)) T)
        (MvPolynomial.aeval (R := Polynomial ℂ)
          (fun i => MvPolynomial.C (Polynomial.C c) * MvPolynomial.X i) R) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom (T : ℂ))
        (fun i => deriv^[i.1] (fun S => fermiGas1D_virial3 (E_B / S)) T) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C p => simp
    | add R₁ R₂ h₁ h₂ =>
      rw [map_add, MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, h₁, h₂]
    | mul_X R₁ j h₁ =>
      rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
        h₁, Polynomial.coe_evalRingHom, Polynomial.eval_C, hderiv_scale j.1]
  exact hgen P

/-! ### Bonus Theorem: Exact Laplace Transform of Volterra's `ν(t)` -/

/-- **Bonus Master Theorem (`laplace_volterraNu`):**
For every real `s > 1`, the Laplace transform of the differentially transcendental Volterra
function `ν(t)` is the elementary function `(s * log s)⁻¹`:
`∫ t in Ioi 0, exp (-s * t) * ν(t) = ((s : ℂ) * (Real.log s : ℂ))⁻¹`. -/
theorem laplace_volterraNu {s : ℝ} (hs : 1 < s) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(s : ℂ) * (t : ℂ)) * volterraNu t =
      ((s : ℂ) * (Real.log s : ℂ))⁻¹ := by
  have hs_pos : 0 < s := lt_trans zero_lt_one hs
  have hlogs_pos : 0 < Real.log s := Real.log_pos hs
  let invGamma1 : ℝ → ℝ := fun v => (recipGamma 0 (v : ℂ)).re
  have hinvGamma1_eq : ∀ v : ℝ, invGamma1 v = (Real.Gamma (1 + v))⁻¹ := by
    intro v
    dsimp only [invGamma1, recipGamma]
    rw [add_zero, show (1 : ℂ) + (v : ℂ) = ((1 + v : ℝ) : ℂ) by push_cast; rfl,
      Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]
  have hinvGamma1_cont : Continuous invGamma1 :=
    Complex.continuous_re.comp ((differentiable_recipGamma 0).continuous.comp Complex.continuous_ofReal)
  have hinvGamma1_meas : Measurable invGamma1 := hinvGamma1_cont.measurable
  -- First rewrite `volterraNu t` on `t > 0` as the complex cast of a nonnegative real integral:
  have hν_real : ∀ t : ℝ, 0 < t →
      volterraNu t = ((∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v : ℝ) : ℂ) := by
    intro t ht
    rw [volterraNu]
    have hofR : ((∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v : ℝ) : ℂ) =
        ∫ v : ℝ in Set.Ioi (0 : ℝ), ((t ^ v * invGamma1 v : ℝ) : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    rw [hofR]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [hinvGamma1_eq v, recipGamma, add_zero,
      show (1 : ℂ) + (v : ℂ) = ((1 + v : ℝ) : ℂ) by push_cast; rfl,
      Complex.Gamma_ofReal, ← Complex.ofReal_inv,
      show (v : ℂ) * (Real.log t : ℂ) = ((Real.log t * v : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.rpow_def_of_pos ht]
  -- Rewrite the LHS as the complex cast of the real integral `∫ t in Ioi 0, exp (-s t) * ∫ v in Ioi 0, t^v * invGamma1 v`:
  have hlhs_real :
      ∫ t : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(s : ℂ) * (t : ℂ)) * volterraNu t =
      ((∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-s * t) *
        ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v : ℝ) : ℂ) := by
    have hofR : ((∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-s * t) *
          ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v : ℝ) : ℂ) =
        ∫ t : ℝ in Set.Ioi (0 : ℝ), ((Real.exp (-s * t) *
          ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v : ℝ) : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    rw [hofR]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hν_real t ht, show -(s : ℂ) * (t : ℂ) = ((-s * t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  rw [hlhs_real]
  have hrhs_real : ((s : ℂ) * (Real.log s : ℂ))⁻¹ = (((s * Real.log s)⁻¹ : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hrhs_real]
  congr 1
  -- Now prove the real Tonelli identity:
  -- `∫ t in Ioi 0, exp (-s t) * ∫ v in Ioi 0, t^v * invGamma1 v = (s * log s)⁻¹`!
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun t v => Real.exp (-s * t) * (t ^ v * invGamma1 v)
  have hF_nn : ∀ t : ℝ, 0 < t → ∀ v : ℝ, 0 < v → 0 ≤ F t v := fun t ht v hv => by
    dsimp only [F]; rw [hinvGamma1_eq v]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.rpow_nonneg ht.le v)
      (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith)).le))
  have hF_meas : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun p : ℝ × ℝ => Real.exp (-s * p.1)) :=
      Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)
    have h2 : Measurable (fun p : ℝ × ℝ => p.1 ^ p.2) :=
      measurable_fst.pow measurable_snd
    have h3 : Measurable (fun p : ℝ × ℝ => invGamma1 p.2) :=
      hinvGamma1_meas.comp measurable_snd
    exact h1.mul (h2.mul h3)
  -- Step 1: Compute the inner `t`-integral for each `v > 0`:
  have hinner_t : ∀ v : ℝ, 0 < v →
      ∫⁻ t : ℝ, ENNReal.ofReal (F t v) ∂μ = ENNReal.ofReal (s ^ (-(v + 1))) := by
    intro v hv
    have hint_t : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ v) (Set.Ioi (0 : ℝ)) := by
      have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < v + 1 by linarith)
      simp only [add_sub_cancel_right] at hG
      have h1 := integrableOn_Ioi_comp_mul_left hG hs_pos
      have h2 := h1.const_mul (s ^ (-v))
      refine MeasureTheory.IntegrableOn.congr_fun h2 (fun t ht => ?_) measurableSet_Ioi
      have htpos : 0 < t := ht
      rw [Real.mul_rpow hs_pos.le htpos.le, show -(s * t) = -s * t by ring]
      have hcancel : s ^ (-v) * s ^ v = 1 := by
        rw [← Real.rpow_add hs_pos, neg_add_cancel, Real.rpow_zero]
      calc s ^ (-v) * (Real.exp (-s * t) * (s ^ v * t ^ v))
          = Real.exp (-s * t) * ((s ^ (-v) * s ^ v) * t ^ v) := by ring
        _ = Real.exp (-s * t) * t ^ v := by rw [hcancel, one_mul]
    have hF_int : MeasureTheory.Integrable (fun t : ℝ => F t v) μ := by
      have h1 := hint_t.mul_const (invGamma1 v)
      refine h1.congr (Filter.Eventually.of_forall fun t => by dsimp [F]; ring)
    have hval_t : ∫ t : ℝ in Set.Ioi (0 : ℝ), F t v = s ^ (-(v + 1)) := by
      have heq : ∫ t : ℝ in Set.Ioi (0 : ℝ), F t v =
          (Real.Gamma (1 + v))⁻¹ * ∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-t / s⁻¹) * t ^ v := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        dsimp only [F]; rw [hinvGamma1_eq v, show -t / s⁻¹ = -s * t by rw [div_inv_eq_mul]; ring]; ring
      rw [heq, integral_exp_neg_div_mul_rpow (by linarith) (inv_pos.mpr hs_pos), add_comm 1 v]
      have hGne : Real.Gamma (v + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
      rw [Real.inv_rpow hs_pos.le, ← Real.rpow_neg hs_pos.le]
      field_simp [hGne]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF_int
      (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht; exact hF_nn t ht v hv),
      hval_t]
  -- Step 2: Compute the outer `v`-integral `∫⁻ v, ofReal (s ^ (-(v + 1))) ∂μ = ofReal ((s * log s)⁻¹)`:
  have houter_v : ∫⁻ v : ℝ, ENNReal.ofReal (s ^ (-(v + 1))) ∂μ = ENNReal.ofReal ((s * Real.log s)⁻¹) := by
    have hv_int : MeasureTheory.IntegrableOn (fun v : ℝ => s ^ (-(v + 1))) (Set.Ioi (0 : ℝ)) := by
      have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < 1 by norm_num)
      simp only [sub_self, Real.rpow_zero, mul_one] at hG
      have h1 := integrableOn_Ioi_comp_mul_left hG hlogs_pos
      have h2 := h1.const_mul s⁻¹
      refine MeasureTheory.IntegrableOn.congr_fun h2 (fun v _ => ?_) measurableSet_Ioi
      have hs_inv : s⁻¹ = Real.exp (-Real.log s) := by rw [Real.exp_neg, Real.exp_log hs_pos]
      rw [Real.rpow_def_of_pos hs_pos, hs_inv, ← Real.exp_add]
      congr 1; ring
    have hv_val : ∫ v : ℝ in Set.Ioi (0 : ℝ), s ^ (-(v + 1)) = (s * Real.log s)⁻¹ := by
      have heq : ∫ v : ℝ in Set.Ioi (0 : ℝ), s ^ (-(v + 1)) =
          s⁻¹ * ∫ v : ℝ in Set.Ioi (0 : ℝ), Real.exp (-v / (Real.log s)⁻¹) * v ^ (0 : ℝ) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        rw [Real.rpow_zero, mul_one, div_inv_eq_mul, Real.rpow_def_of_pos hs_pos]
        have : s⁻¹ = Real.exp (-Real.log s) := by rw [Real.exp_neg, Real.exp_log hs_pos]
        rw [this, ← Real.exp_add]; congr 1; ring
      rw [heq, integral_exp_neg_div_mul_rpow (by norm_num : (-1 : ℝ) < 0) (inv_pos.mpr hlogs_pos)]
      simp [mul_comm]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hv_int
      (Filter.Eventually.of_forall fun v => Real.rpow_nonneg hs_pos.le _), hv_val]
  -- Step 3: Tonelli swap!
  have htonelli : ∫⁻ t : ℝ, ∫⁻ v : ℝ, ENNReal.ofReal (F t v) ∂μ ∂μ =
      ENNReal.ofReal ((s * Real.log s)⁻¹) := by
    have hae : AEMeasurable (Function.uncurry fun t v => ENNReal.ofReal (F t v)) (μ.prod μ) :=
      (ENNReal.measurable_ofReal.comp hF_meas).aemeasurable
    rw [MeasureTheory.lintegral_lintegral_swap hae]
    have hcongr : ∫⁻ v : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal (F t v) ∂μ ∂μ =
        ∫⁻ v : ℝ, ENNReal.ofReal (s ^ (-(v + 1))) ∂μ :=
      MeasureTheory.lintegral_congr_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
        exact hinner_t v hv)
    rw [hcongr, houter_v]
  -- Step 4: Match the inner `v`-lintegral with `ofReal (exp (-s t) * ∫ v in Ioi 0, t^v * invGamma1 v)`!
  have hinner_v : ∀ t : ℝ, 0 < t →
      ∫⁻ v : ℝ, ENNReal.ofReal (F t v) ∂μ =
        ENNReal.ofReal (Real.exp (-s * t) * ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v) := by
    intro t ht
    obtain ⟨C, _, hdecay⟩ := norm_recipGamma_real_exp_decay 0 (Real.log t + 1)
    have hv_int : MeasureTheory.IntegrableOn (fun v : ℝ => t ^ v * invGamma1 v) (Set.Ioi (0 : ℝ)) := by
      have hdom : MeasureTheory.IntegrableOn (fun v : ℝ => C * Real.exp (-v)) (Set.Ioi (0 : ℝ)) := by
        have hG := Real.GammaIntegral_convergent (show (0 : ℝ) < 1 by norm_num)
        simp only [sub_self, Real.rpow_zero, mul_one] at hG
        exact hG.const_mul C
      have hmeas_v : MeasureTheory.AEStronglyMeasurable (fun v : ℝ => t ^ v * invGamma1 v) μ := by
        have hcont : ContinuousOn (fun v : ℝ => t ^ v * invGamma1 v) (Set.Ioi (0 : ℝ)) :=
          (continuous_const.rpow continuous_id fun _ => Or.inl ht.ne').continuousOn.mul
            hinvGamma1_cont.continuousOn
        exact hcont.aestronglyMeasurable measurableSet_Ioi
      refine hdom.mono' hmeas_v ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
      have hvpos : 0 < v := hv
      rw [hinvGamma1_eq v, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le v)
        (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith)).le)), Real.rpow_def_of_pos ht]
      have hdec := hdecay v hvpos.le
      rw [recipGamma, add_zero, show (1 : ℂ) + (v : ℂ) = ((1 + v : ℝ) : ℂ) by push_cast; rfl,
        Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith)).le)] at hdec
      calc Real.exp (Real.log t * v) * (Real.Gamma (1 + v))⁻¹
          ≤ Real.exp (Real.log t * v) * (C * Real.exp (-(Real.log t + 1) * v)) :=
            mul_le_mul_of_nonneg_left hdec (Real.exp_pos _).le
        _ = C * Real.exp (-v) := by
            rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]; congr 2; ring
    have hFv_int : MeasureTheory.Integrable (fun v : ℝ => F t v) μ := hv_int.const_mul (Real.exp (-s * t))
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFv_int
      (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv; exact hF_nn t ht v hv),
      MeasureTheory.integral_const_mul]
  -- Combine Steps 3 & 4 via `integral_eq_lintegral_of_nonneg_ae`!
  have hg_meas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-s * t) * ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v) μ := by
    have hsm : MeasureTheory.StronglyMeasurable (fun t : ℝ => ∫ v : ℝ, F t v ∂μ) :=
      hF_meas.stronglyMeasurable.integral_prod_right
    have heq : (fun t : ℝ => Real.exp (-s * t) * ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v) =
        fun t : ℝ => ∫ v : ℝ, F t v ∂μ := by
      ext t; exact (MeasureTheory.integral_const_mul (Real.exp (-s * t)) _).symm
    rw [heq]; exact hsm.aestronglyMeasurable
  have hg_nn : 0 ≤ᵐ[μ] fun t : ℝ => Real.exp (-s * t) * ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    refine mul_nonneg (Real.exp_pos _).le (MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun v hv => ?_)
    rw [hinvGamma1_eq v]
    exact mul_nonneg (Real.rpow_nonneg (show 0 < t from ht).le v)
      (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith [show (0 : ℝ) < v from hv])).le)
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hg_nn hg_meas]
  have hlin_eq : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-s * t) *
      ∫ v : ℝ in Set.Ioi (0 : ℝ), t ^ v * invGamma1 v) ∂μ =
      ENNReal.ofReal ((s * Real.log s)⁻¹) := by
    rw [← htonelli]
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hinner_v t ht).symm
  rw [hlin_eq, ENNReal.toReal_ofReal (by positivity)]

end
end PakPrimes.VolterraVirialDTrans
end
