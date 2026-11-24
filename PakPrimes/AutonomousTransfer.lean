module

public import PakPrimes.BorelStokesVandermonde
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Link 1 & Link 2: Exact Series Equivalence and Autonomous Transfer

This module formalizes:
1. **Prime & companion power series**:
   - `I_prime : PowerSeries ℂ := ∑_{p prime} q^p`
   - `Pi_series : PowerSeries ℂ := ∑_{n ≥ 0} π(n) q^n`
   - `logReciprocalSeries : PowerSeries ℂ := ∑_{n ≥ 2} q^n / log n`
   - `partLogDerivSeries : PowerSeries ℂ := ∑_{n ≥ 1} (∑_{p prime, p ∣ n} p) q^n`
2. **Link 1 (`Pi_series_eq_I_prime_div`, `piCoordinates_independent_iff_indicatorCoordinates`)**:
   `(1 - PowerSeries.X) * Pi_series = I_prime`, and a general equivalence showing that whenever
   `(1 - PowerSeries.X) * G = F` in `ℂ[[X]]`, `seriesCoordinates F` is algebraically independent
   over `ℂ` iff `seriesCoordinates G` is.
3. **Link 2 (`autonomous_transfer`, `autonomous_transfer_indicator`, `autonomous_transfer_log_deriv`)**:
   Any formal algebraic differential equation over `ℂ(q)` satisfied by a power series `F` with
   polynomial coefficient growth (or by a non-vanishing unit-normalized series `P` with
   `X * P' = G * P`) transfers along `qRay u = exp (-exp (-u))` (`u ∈ ℝ`) to a nonzero autonomous
   polynomial differential equation for `u ↦ exp (-u) * value F (qRay u)` eventually as `u → +∞`.
-/

set_option maxHeartbeats 800000

public section
namespace PakPrimes.PrimeNome

open Complex Real Filter MeasureTheory Set MvPolynomial
open scoped Topology Nat.Prime

noncomputable section

/-! ### 1. Power Series Definitions & Link 1 (`(1 - X) * Pi_series = I_prime`) -/

/-- Prime indicator power series `I_prime(q) = ∑_{p prime} q^p`. -/
@[expose] def I_prime : PowerSeries ℂ := by
  classical exact PowerSeries.mk fun n => if Nat.Prime n then 1 else 0

/-- Prime counting power series `Π(q) = ∑_{n ≥ 0} π(n) q^n` (`π(0) = π(1) = 0`). -/
@[expose] def Pi_series : PowerSeries ℂ :=
  PowerSeries.mk fun n => (Nat.primeCounting n : ℂ)

/-- Smooth logarithmic reciprocal power series `∑_{n ≥ 2} q^n / log n`. -/
@[expose] def logReciprocalSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => if 2 ≤ n then ((Real.log (n : ℝ))⁻¹ : ℂ) else 0

/-- Log-derivative `q P'/P` of partitions into primes: `∑_{n ≥ 1} (∑_{p prime, p ∣ n} p) q^n`. -/
@[expose] def partLogDerivSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, if p ∣ n then (p : ℂ) else 0

/-- `j`-th formal derivative `(d/dq)^j F`. -/
@[expose] def seriesJet (F : PowerSeries ℂ) (j : ℕ) : PowerSeries ℂ :=
  (PowerSeries.derivative (R := ℂ))^[j] F

/-- Differential coordinates `(q, F, F', F'', ...)` in `ℂ[[q]]`. -/
@[expose] def seriesCoordinates (F : PowerSeries ℂ) : ℕ → PowerSeries ℂ
  | 0 => PowerSeries.X
  | j + 1 => seriesJet F j

@[expose] def indicatorCoordinates : ℕ → PowerSeries ℂ := seriesCoordinates I_prime
@[expose] def piCoordinates : ℕ → PowerSeries ℂ := seriesCoordinates Pi_series
@[expose] def logReciprocalCoordinates : ℕ → PowerSeries ℂ := seriesCoordinates logReciprocalSeries
@[expose] def partLogDerivCoordinates : ℕ → PowerSeries ℂ := seriesCoordinates partLogDerivSeries

@[expose] def term (S : PowerSeries ℂ) (q : ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff n S * q ^ n

@[expose] def value (S : PowerSeries ℂ) (q : ℂ) : ℂ :=
  ∑' n, term S q n

@[expose] def AbsAt (S : PowerSeries ℂ) (q : ℂ) : Prop :=
  Summable (fun n => ‖term S q n‖)

@[expose] def analyticCoordinates (F : PowerSeries ℂ) (q : ℂ) : ℕ → ℂ
  | 0 => q
  | j + 1 => value (seriesJet F j) q

/-- Exact formal identity `(1 - q) * Π(q) = I_prime(q)`. -/
theorem Pi_series_eq_I_prime_div : (1 - PowerSeries.X) * Pi_series = I_prime := by
  ext n
  cases n with
  | zero =>
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_zero_X_mul, sub_zero]
    simp [Pi_series, I_prime, Nat.not_prime_zero]
  | succ k =>
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul]
    simp only [Pi_series, I_prime, PowerSeries.coeff_mk]
    have hcount : Nat.primeCounting (k + 1) =
        Nat.primeCounting k + if Nat.Prime (k + 1) then 1 else 0 := by
      rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting_eq_primeCounting'_succ]
      exact Nat.count_succ Nat.Prime (k + 1)
    rw [hcount]
    push_cast
    split_ifs <;> ring

private theorem seriesJet_succ (F : PowerSeries ℂ) (k : ℕ) :
    seriesJet F (k + 1) = PowerSeries.derivative (seriesJet F k) :=
  Function.iterate_succ_apply' PowerSeries.derivative k F

private theorem seriesJet_mul_one_sub {F G : PowerSeries ℂ}
    (h : (1 - PowerSeries.X) * G = F) (k : ℕ) :
    seriesJet F k = match k with
      | 0 => (1 - PowerSeries.X) * seriesJet G 0
      | m + 1 => (1 - PowerSeries.X) * seriesJet G (m + 1) - ((m + 1 : ℕ) : ℂ) • seriesJet G m := by
  induction k with
  | zero => simpa [seriesJet] using h.symm
  | succ k ih =>
    have hD1 : PowerSeries.derivative (1 - PowerSeries.X : PowerSeries ℂ) = -1 := by
      simp
    cases k with
    | zero =>
      simp only [seriesJet, Function.iterate_zero, id_eq] at ih
      dsimp only
      rw [seriesJet_succ, show seriesJet F 0 = F from rfl, ih, Derivation.leibniz, hD1]
      simp only [smul_eq_mul, seriesJet, Function.iterate_zero, Function.iterate_one, id_eq,
        zero_add, Nat.cast_one, one_smul]
      ring
    | succ m =>
      dsimp only at ih ⊢
      rw [seriesJet_succ, ih, map_sub, Derivation.leibniz, hD1, Derivation.map_smul_of_tower,
        ← seriesJet_succ G (m + 1), ← seriesJet_succ G m]
      simp only [smul_eq_mul, PowerSeries.smul_eq_C_mul]
      push_cast
      simp only [map_add, map_natCast, map_one]
      ring

private def fwdVar : ℕ → MvPolynomial ℕ ℂ
  | 0 => X 0
  | 1 => (1 - X 0) * X 1
  | k + 2 => (1 - X 0) * X (k + 2) - C ((k + 1 : ℕ) : ℂ) * X (k + 1)

private theorem aeval_fwdVar {F G : PowerSeries ℂ} (h : (1 - PowerSeries.X) * G = F) (i : ℕ) :
    MvPolynomial.aeval (seriesCoordinates G) (fwdVar i) = seriesCoordinates F i := by
  rcases i with _ | _ | k
  · simp [fwdVar, seriesCoordinates]
  · simp only [fwdVar, seriesCoordinates, map_mul, map_sub, map_one, aeval_X]
    simpa [seriesJet] using h
  · simp only [fwdVar, seriesCoordinates, map_sub, map_mul, map_one, aeval_C,
      PowerSeries.algebraMap_apply, aeval_X]
    rw [← PowerSeries.smul_eq_C_mul]
    exact (seriesJet_mul_one_sub h (k + 1)).symm

private def invFwd (x : ℕ → ℂ) : ℕ → ℂ
  | 0 => x 0
  | 1 => (1 - x 0)⁻¹ * x 1
  | k + 2 => (1 - x 0)⁻¹ * (x (k + 2) + ((k + 1 : ℕ) : ℂ) * invFwd x (k + 1))

private theorem eval_invFwd_fwdVar {x : ℕ → ℂ} (hx0 : x 0 ≠ 1) (i : ℕ) :
    MvPolynomial.eval (invFwd x) (fwdVar i) = x i := by
  have h1x : 1 - x 0 ≠ 0 := sub_ne_zero.mpr hx0.symm
  rcases i with _ | _ | k
  · simp [fwdVar, invFwd]
  · simp only [fwdVar, invFwd, map_mul, map_sub, map_one, eval_X]
    rw [← mul_assoc, mul_inv_cancel₀ h1x, one_mul]
  · simp only [fwdVar, invFwd, map_sub, map_mul, map_one, eval_C, eval_X]
    rw [← mul_assoc, mul_inv_cancel₀ h1x, one_mul]
    ring

private theorem infinite_ne_one : ({c : ℂ | c ≠ 1} : Set ℂ).Infinite := by
  have : ({c : ℂ | c ≠ 1} : Set ℂ) = Set.univ \ {1} := by
    ext c; simp [Set.mem_sdiff, Set.mem_singleton_iff]
  rw [this]
  exact Set.infinite_univ.sdiff (Set.finite_singleton 1)

private theorem bind₁_fwdVar_eq_zero {Q : MvPolynomial ℕ ℂ} (hQ : bind₁ fwdVar Q = 0) :
    Q = 0 := by
  refine MvPolynomial.funext_set
    (fun i => if i = 0 then {c : ℂ | c ≠ 1} else Set.univ)
    (fun i => by split_ifs; exact infinite_ne_one; exact Set.infinite_univ)
    fun x hx => ?_
  have hx0 : x 0 ≠ 1 := by simpa using hx 0 (Set.mem_univ 0)
  have hbind : MvPolynomial.eval (invFwd x) (bind₁ fwdVar Q) = 0 := by rw [hQ, map_zero]
  change MvPolynomial.aeval (invFwd x) (bind₁ fwdVar Q) = 0 at hbind
  rw [MvPolynomial.aeval_bind₁] at hbind
  have hev : (fun i => MvPolynomial.aeval (invFwd x) (fwdVar i)) = x :=
    funext (eval_invFwd_fwdVar hx0)
  rw [hev] at hbind
  exact hbind

private def polyStep : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | j + 1 => X (j + 2)

private def polyDeriv (A : MvPolynomial ℕ ℂ) : MvPolynomial ℕ ℂ :=
  ∑ i ∈ A.vars, MvPolynomial.pderiv i A * polyStep i

private theorem polyDeriv_eq_sum_of_vars_subset {A : MvPolynomial ℕ ℂ} {s : Finset ℕ}
    (hs : A.vars ⊆ s) :
    ∑ i ∈ s, MvPolynomial.pderiv i A * polyStep i = polyDeriv A := by
  rw [polyDeriv]
  refine (Finset.sum_subset hs fun i _ hi => ?_).symm
  simp [MvPolynomial.pderiv_eq_zero_of_notMem_vars hi]

private theorem polyDeriv_add (A B : MvPolynomial ℕ ℂ) :
    polyDeriv (A + B) = polyDeriv A + polyDeriv B := by
  classical
  let s := (A + B).vars ∪ A.vars ∪ B.vars
  rw [← polyDeriv_eq_sum_of_vars_subset (s := s) (Finset.subset_union_left.trans Finset.subset_union_left),
    ← polyDeriv_eq_sum_of_vars_subset (A := A) (s := s)
      (Finset.subset_union_right.trans Finset.subset_union_left),
    ← polyDeriv_eq_sum_of_vars_subset (A := B) (s := s) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, add_mul]

private theorem polyDeriv_mul (A B : MvPolynomial ℕ ℂ) :
    polyDeriv (A * B) = polyDeriv A * B + A * polyDeriv B := by
  classical
  let s := (A * B).vars ∪ A.vars ∪ B.vars
  rw [← polyDeriv_eq_sum_of_vars_subset (s := s) (Finset.subset_union_left.trans Finset.subset_union_left),
    ← polyDeriv_eq_sum_of_vars_subset (A := A) (s := s)
      (Finset.subset_union_right.trans Finset.subset_union_left),
    ← polyDeriv_eq_sum_of_vars_subset (A := B) (s := s) Finset.subset_union_right,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.pderiv_mul]
  ring

private theorem aeval_polyDeriv (F : PowerSeries ℂ) (A : MvPolynomial ℕ ℂ) :
    MvPolynomial.aeval (seriesCoordinates F) (polyDeriv A) =
      PowerSeries.derivative (MvPolynomial.aeval (seriesCoordinates F) A) := by
  induction A using MvPolynomial.induction_on with
  | C c => simp [polyDeriv]
  | add A B hA hB => simp [polyDeriv_add, map_add, hA, hB]
  | mul_X A i hA =>
    have hXi : polyDeriv (X i) = polyStep i := by
      classical
      have hi : ({i} : Finset ℕ) = (X i : MvPolynomial ℕ ℂ).vars := by simp
      rw [polyDeriv, ← hi, Finset.sum_singleton, MvPolynomial.pderiv_X_self, one_mul]
    rw [polyDeriv_mul, hXi, map_add, map_mul, map_mul, map_mul, Derivation.leibniz, hA]
    have hstep : MvPolynomial.aeval (seriesCoordinates F) (polyStep i) =
        PowerSeries.derivative (seriesCoordinates F i) := by
      cases i with
      | zero => simp [polyStep, seriesCoordinates]
      | succ j => simp [polyStep, seriesCoordinates, seriesJet, Function.iterate_succ_apply']
    simp only [aeval_X, smul_eq_mul, hstep]
    ring

private theorem vars_pderiv_subset (i : ℕ) (A : MvPolynomial ℕ ℂ) :
    (MvPolynomial.pderiv i A).vars ⊆ A.vars := by
  intro j hj
  rw [MvPolynomial.mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨d, hd, hjd⟩ := hj
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hd
  have hne : A.coeff (d + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hd
  refine ⟨d + Finsupp.single i 1, MvPolynomial.mem_support_iff.mpr hne, ?_⟩
  rw [Finsupp.mem_support_iff] at hjd ⊢
  simp [hjd]

private theorem polyDeriv_vars_subset_zero {A : MvPolynomial ℕ ℂ} (hA : A.vars ⊆ {0}) :
    (polyDeriv A).vars ⊆ {0} := by
  classical
  refine (MvPolynomial.vars_sum_subset _ _).trans ?_
  rw [Finset.biUnion_subset]
  intro i hi
  have hi0 : i = 0 := Finset.mem_singleton.mp (hA hi)
  subst hi0
  refine (MvPolynomial.vars_mul _ _).trans ?_
  simp only [polyStep, MvPolynomial.vars_one, Finset.union_empty]
  exact (vars_pderiv_subset 0 A).trans hA

private theorem polyDeriv_vars_subset_range {k : ℕ} {A : MvPolynomial ℕ ℂ}
    (hA : A.vars ⊆ Finset.range (k + 1)) :
    (polyDeriv A).vars ⊆ Finset.range (k + 2) := by
  classical
  refine (MvPolynomial.vars_sum_subset _ _).trans ?_
  rw [Finset.biUnion_subset]
  intro i hi
  have hik : i ∈ Finset.range (k + 1) := hA hi
  refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ?_ ?_)
  · exact (vars_pderiv_subset i A).trans (hA.trans (Finset.range_mono (Nat.le_succ _)))
  · cases i with
    | zero => simp [polyStep]
    | succ j =>
      simp only [polyStep, MvPolynomial.vars_X, Finset.singleton_subset_iff, Finset.mem_range]
      rw [Finset.mem_range] at hik
      omega

private def backPoly : ℕ → MvPolynomial ℕ ℂ
  | 0 => X 1
  | k + 1 => (1 - X 0) * polyDeriv (backPoly k) + ((k + 1 : ℕ) : ℂ) • backPoly k

private theorem aeval_backPoly {F G : PowerSeries ℂ} (h : (1 - PowerSeries.X) * G = F) (k : ℕ) :
    MvPolynomial.aeval (seriesCoordinates F) (backPoly k) =
      (1 - PowerSeries.X) ^ (k + 1) * seriesJet G k := by
  induction k with
  | zero =>
    simp only [backPoly, aeval_X, zero_add, pow_one, seriesCoordinates, seriesJet,
      Function.iterate_zero, id_eq]
    exact h.symm
  | succ k ih =>
    have hD1 : PowerSeries.derivative (1 - PowerSeries.X : PowerSeries ℂ) = -1 := by simp
    have hD_pow : PowerSeries.derivative ((1 - PowerSeries.X : PowerSeries ℂ) ^ (k + 1)) =
        -(((k + 1 : ℕ) : ℂ) • (1 - PowerSeries.X) ^ k) := by
      rw [(PowerSeries.derivative).leibniz_pow, hD1, smul_eq_mul, mul_neg_one,
        PowerSeries.smul_eq_C_mul]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one,
        Nat.add_sub_cancel]
      ring
    have hDeriv_ih : PowerSeries.derivative (MvPolynomial.aeval (seriesCoordinates F) (backPoly k)) =
        -(((k + 1 : ℕ) : ℂ) • (1 - PowerSeries.X) ^ k) * seriesJet G k +
          (1 - PowerSeries.X) ^ (k + 1) * seriesJet G (k + 1) := by
      rw [ih, Derivation.leibniz, hD_pow, seriesJet_succ G k]
      simp [smul_eq_mul, mul_comm, add_comm]
    have hs0 : seriesCoordinates F 0 = PowerSeries.X := rfl
    rw [backPoly, map_add, map_mul, map_sub, map_one, map_smul, aeval_X, hs0, aeval_polyDeriv,
      hDeriv_ih, ih, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one, pow_succ']
    ring

private theorem backPoly_split (k : ℕ) :
    ∃ R : MvPolynomial ℕ ℂ,
      R.vars ⊆ Finset.range (k + 1) ∧ backPoly k = (1 - X 0) ^ k * X (k + 1) + R := by
  classical
  have h10_vars : (1 - X 0 : MvPolynomial ℕ ℂ).vars ⊆ {0} := by
    have hneg : (-X 0 : MvPolynomial ℕ ℂ) = C (-1) * X 0 := by simp
    rw [sub_eq_add_neg, hneg]
    refine (MvPolynomial.vars_add_subset _ _).trans ?_
    simp only [MvPolynomial.vars_one, Finset.empty_union]
    exact (MvPolynomial.vars_mul _ _).trans (by simp)
  induction k with
  | zero =>
    refine ⟨0, by simp, by simp [backPoly]⟩
  | succ k ih =>
    obtain ⟨R, hR_vars, hR_eq⟩ := ih
    let A : MvPolynomial ℕ ℂ := (1 - X 0) ^ k
    have hA_vars : A.vars ⊆ {0} := (MvPolynomial.vars_pow _ _).trans h10_vars
    have hdA_vars : (polyDeriv A).vars ⊆ {0} := polyDeriv_vars_subset_zero hA_vars
    have hdR_vars : (polyDeriv R).vars ⊆ Finset.range (k + 2) :=
      polyDeriv_vars_subset_range hR_vars
    let R' : MvPolynomial ℕ ℂ :=
      (1 - X 0) * (polyDeriv A * X (k + 1) + polyDeriv R) +
        ((k + 1 : ℕ) : ℂ) • ((1 - X 0) ^ k * X (k + 1) + R)
    refine ⟨R', ?_, ?_⟩
    · have h0_mem : (0 : ℕ) ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
      have h10_r : (1 - X 0 : MvPolynomial ℕ ℂ).vars ⊆ Finset.range (k + 2) :=
        h10_vars.trans (Finset.singleton_subset_iff.mpr h0_mem)
      have hA_r : A.vars ⊆ Finset.range (k + 2) :=
        hA_vars.trans (Finset.singleton_subset_iff.mpr h0_mem)
      have hdA_r : (polyDeriv A).vars ⊆ Finset.range (k + 2) :=
        hdA_vars.trans (Finset.singleton_subset_iff.mpr h0_mem)
      have hXk1 : (X (k + 1) : MvPolynomial ℕ ℂ).vars ⊆ Finset.range (k + 2) := by
        simp [Finset.mem_range]
      refine (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset ?_ ?_)
      · refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset h10_r ?_)
        refine (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset ?_ hdR_vars)
        exact (MvPolynomial.vars_mul _ _).trans (Finset.union_subset hdA_r hXk1)
      · rw [MvPolynomial.smul_eq_C_mul]
        refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ?_ ?_)
        · rw [MvPolynomial.vars_C]; exact Finset.empty_subset _
        · refine (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset ?_ ?_)
          · exact (MvPolynomial.vars_mul _ _).trans (Finset.union_subset hA_r hXk1)
          · exact hR_vars.trans (Finset.range_mono (Nat.le_succ _))
    · have hdX : polyDeriv (X (k + 1)) = X (k + 2) := by
        have hv : ({k + 1} : Finset ℕ) = (X (k + 1) : MvPolynomial ℕ ℂ).vars := by simp
        rw [polyDeriv, ← hv, Finset.sum_singleton, MvPolynomial.pderiv_X_self, one_mul, polyStep]
      rw [backPoly, hR_eq, polyDeriv_add, polyDeriv_mul, hdX]
      dsimp only [R', A]
      rw [pow_succ']
      ring

private def weightVar (i : ℕ) : ℕ :=
  if i = 0 then 0 else i

private def weightMon (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun i e => weightVar i * e)

private noncomputable def backRem (k : ℕ) : MvPolynomial ℕ ℂ :=
  Classical.choose (backPoly_split k)

private theorem backRem_vars (k : ℕ) : (backRem k).vars ⊆ Finset.range (k + 1) :=
  (Classical.choose_spec (backPoly_split k)).1

private theorem backPoly_eq_rem (k : ℕ) :
    backPoly k = (1 - X 0) ^ k * X (k + 1) + backRem k :=
  (Classical.choose_spec (backPoly_split k)).2

private noncomputable def liftVec (t : ℕ → ℂ) (ht : t 0 ≠ 1) : ℕ → (ℕ → ℂ)
  | 0 => fun i => if i = 0 then t 0 else 0
  | k + 1 =>
    let prev := liftVec t ht k
    fun i =>
      if i = k + 1 then ((1 - t 0) ^ k)⁻¹ * (t (k + 1) - MvPolynomial.eval prev (backRem k))
      else prev i

private theorem liftVec_stable (t : ℕ → ℂ) (ht : t 0 ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    liftVec t ht n m = liftVec t ht m m := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmn
    rfl
  | succ n ih =>
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · rfl
    · have hne : m ≠ n + 1 := by omega
      dsimp only [liftVec]
      simp only [hne, ↓reduceIte]
      exact ih (Nat.lt_succ_iff.mp hlt)

private noncomputable def liftX (t : ℕ → ℂ) (ht : t 0 ≠ 1) (m : ℕ) : ℂ :=
  liftVec t ht m m

private theorem liftX_zero (t : ℕ → ℂ) (ht : t 0 ≠ 1) : liftX t ht 0 = t 0 := by
  simp [liftX, liftVec]

private theorem eval_liftX_backPoly (t : ℕ → ℂ) (ht : t 0 ≠ 1) (k : ℕ) :
    MvPolynomial.eval (liftX t ht) (backPoly k) = t (k + 1) := by
  have h1t : 1 - t 0 ≠ 0 := sub_ne_zero.mpr ht.symm
  have hcongr : MvPolynomial.eval (liftX t ht) (backRem k) =
      MvPolynomial.eval (liftVec t ht k) (backRem k) := by
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ _ = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ _
    refine MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => ?_) rfl
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp (backRem_vars k hi))
    exact (liftVec_stable t ht hik).symm
  rw [backPoly_eq_rem k, map_add, map_mul, map_pow, map_sub, map_one, eval_X, eval_X, hcongr,
    liftX_zero]
  have hltk : liftX t ht (k + 1) =
      ((1 - t 0) ^ k)⁻¹ * (t (k + 1) - MvPolynomial.eval (liftVec t ht k) (backRem k)) := by
    simp [liftX, liftVec]
  rw [hltk, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k h1t), one_mul]
  ring

/-- **Link 1 (`algIndep_seriesCoordinates_iff_mul_one_sub`)**:
If `(1 - PowerSeries.X) * G = F` in `ℂ[[X]]`, then `seriesCoordinates F` is
algebraically independent over `ℂ` iff `seriesCoordinates G` is. -/
theorem algIndep_seriesCoordinates_iff_mul_one_sub {F G : PowerSeries ℂ}
    (h : (1 - PowerSeries.X) * G = F) :
    AlgebraicIndependent ℂ (seriesCoordinates F) ↔ AlgebraicIndependent ℂ (seriesCoordinates G) := by
  classical
  constructor
  · intro hF
    rw [algebraicIndependent_iff]
    intro P hP
    let M : ℕ := P.support.sup weightMon
    let termMap (i : ℕ) : MvPolynomial ℕ ℂ :=
      match i with
      | 0 => X 0
      | j + 1 => backPoly j
    let Q : MvPolynomial ℕ ℂ :=
      ∑ m ∈ P.support, C (P.coeff m) * (1 - X 0) ^ (M - weightMon m) *
        ∏ i ∈ m.support, (termMap i) ^ m i
    have hterm_aeval (i : ℕ) :
        MvPolynomial.aeval (seriesCoordinates F) (termMap i) =
          (1 - PowerSeries.X) ^ (weightVar i) * seriesCoordinates G i := by
      cases i with
      | zero => simp [termMap, weightVar, seriesCoordinates]
      | succ j =>
        simp only [termMap, weightVar, Nat.succ_ne_zero, ↓reduceIte, seriesCoordinates]
        exact aeval_backPoly h j
    have hQ_aeval :
        MvPolynomial.aeval (seriesCoordinates F) Q =
          (1 - PowerSeries.X) ^ M * MvPolynomial.aeval (seriesCoordinates G) P := by
      have hs0 : seriesCoordinates F 0 = PowerSeries.X := rfl
      conv_rhs => rw [MvPolynomial.as_sum P, map_sum, Finset.mul_sum]
      simp only [Q, map_sum, map_mul, map_pow, map_sub, map_one, aeval_X, aeval_C,
        PowerSeries.algebraMap_apply, hs0, map_prod]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hprod : ∏ i ∈ m.support, (MvPolynomial.aeval (seriesCoordinates F)) (termMap i) ^ m i =
          (1 - PowerSeries.X) ^ (weightMon m) *
            ∏ i ∈ m.support, (seriesCoordinates G i) ^ m i := by
        simp_rw [hterm_aeval, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
        rfl
      have hmon : (MvPolynomial.aeval (seriesCoordinates G)) (monomial m (P.coeff m)) =
          PowerSeries.C (P.coeff m) * ∏ i ∈ m.support, (seriesCoordinates G i) ^ m i := by
        rw [aeval_monomial, PowerSeries.algebraMap_apply, Finsupp.prod]
        simp
      have hle : weightMon m ≤ M := Finset.le_sup hm
      rw [hprod, hmon]
      calc PowerSeries.C (P.coeff m) * (1 - PowerSeries.X) ^ (M - weightMon m) *
              ((1 - PowerSeries.X) ^ weightMon m * ∏ i ∈ m.support, seriesCoordinates G i ^ m i)
          = PowerSeries.C (P.coeff m) *
              ((1 - PowerSeries.X) ^ (M - weightMon m) * (1 - PowerSeries.X) ^ weightMon m) *
              ∏ i ∈ m.support, seriesCoordinates G i ^ m i := by ring
        _ = (1 - PowerSeries.X) ^ M *
              (PowerSeries.C (P.coeff m) * ∏ i ∈ m.support, seriesCoordinates G i ^ m i) := by
            rw [← pow_add, Nat.sub_add_cancel hle]; ring
    have hQ0 : Q = 0 := by
      apply (algebraicIndependent_iff.mp hF) Q
      rw [hQ_aeval, hP, mul_zero]
    refine MvPolynomial.funext_set
      (fun i => if i = 0 then {c : ℂ | c ≠ 1} else Set.univ)
      (fun i => by split_ifs; exact infinite_ne_one; exact Set.infinite_univ)
      fun y hy => ?_
    have hy0 : y 0 ≠ 1 := by simpa using hy 0 (Set.mem_univ 0)
    have h1y : 1 - y 0 ≠ 0 := sub_ne_zero.mpr hy0.symm
    let t (i : ℕ) : ℂ := if i = 0 then y 0 else (1 - y 0) ^ i * y i
    have ht0 : t 0 ≠ 1 := by simpa [t] using hy0
    let x := liftX t ht0
    have hx0 : x 0 = y 0 := by simpa [x, t] using liftX_zero t ht0
    have hx_term (i : ℕ) : MvPolynomial.eval x (termMap i) = (1 - y 0) ^ weightVar i * y i := by
      cases i with
      | zero =>
        simp only [termMap, weightVar, ↓reduceIte, pow_zero, one_mul, eval_X]
        exact hx0
      | succ j =>
        simp only [termMap, weightVar, Nat.succ_ne_zero, ↓reduceIte]
        rw [eval_liftX_backPoly t ht0 j]
        simp [t]
    have hQx : MvPolynomial.eval x Q = (1 - y 0) ^ M * MvPolynomial.eval y P := by
      conv_rhs => rw [MvPolynomial.as_sum P, map_sum, Finset.mul_sum]
      simp only [Q, map_sum, map_mul, map_pow, map_sub, map_one, eval_X, eval_C, hx0]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hprod : MvPolynomial.eval x (∏ i ∈ m.support, termMap i ^ m i) =
          (1 - y 0) ^ weightMon m * ∏ i ∈ m.support, y i ^ m i := by
        rw [map_prod]
        simp_rw [map_pow, hx_term, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
          Finset.prod_pow_eq_pow_sum]
        rfl
      have hmon : MvPolynomial.eval y (monomial m (P.coeff m)) =
          P.coeff m * ∏ i ∈ m.support, y i ^ m i := by
        rw [eval_monomial, Finsupp.prod]
      have hle : weightMon m ≤ M := Finset.le_sup hm
      rw [hprod, hmon]
      calc P.coeff m * (1 - y 0) ^ (M - weightMon m) *
              ((1 - y 0) ^ weightMon m * ∏ i ∈ m.support, y i ^ m i)
          = P.coeff m * ((1 - y 0) ^ (M - weightMon m) * (1 - y 0) ^ weightMon m) *
              ∏ i ∈ m.support, y i ^ m i := by ring
        _ = (1 - y 0) ^ M * (P.coeff m * ∏ i ∈ m.support, y i ^ m i) := by
            rw [← pow_add, Nat.sub_add_cancel hle]; ring
    have hQx0 : MvPolynomial.eval x Q = 0 := by rw [hQ0, map_zero]
    rw [hQx] at hQx0
    exact (mul_eq_zero.mp hQx0).resolve_left (pow_ne_zero M h1y)
  · intro hG
    rw [algebraicIndependent_iff]
    intro Q hQ
    apply bind₁_fwdVar_eq_zero
    apply (algebraicIndependent_iff.mp hG) (bind₁ fwdVar Q)
    rw [MvPolynomial.aeval_bind₁]
    simpa only [aeval_fwdVar h] using hQ

/-- **Link 1 Specialization for Pak's Conjecture 2.5b**:
`PrimeNome.piCoordinates` is algebraically independent over `ℂ` iff
`PrimeNome.indicatorCoordinates` is algebraically independent over `ℂ`. -/
theorem piCoordinates_independent_iff_indicatorCoordinates :
    AlgebraicIndependent ℂ piCoordinates ↔ AlgebraicIndependent ℂ indicatorCoordinates :=
  (algIndep_seriesCoordinates_iff_mul_one_sub Pi_series_eq_I_prime_div).symm

/-! ### 2. Polynomial Coefficient Bounds & Analytic Convergence on the Unit Disk -/

/-- Polynomial coefficient growth `‖a_n‖ ≤ C * (n + 1)^p`. -/
@[expose] def PolyCoeffBound (F : PowerSeries ℂ) : Prop :=
  ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ n : ℕ, ‖PowerSeries.coeff n F‖ ≤ C * (n + 1 : ℝ) ^ p

lemma I_prime_polyBound : PolyCoeffBound I_prime := by
  refine ⟨1, 0, zero_le_one, fun n => ?_⟩
  simp only [I_prime, PowerSeries.coeff_mk, pow_zero, mul_one]
  split_ifs <;> simp

lemma Pi_series_polyBound : PolyCoeffBound Pi_series := by
  refine ⟨1, 1, zero_le_one, fun n => ?_⟩
  simp only [Pi_series, PowerSeries.coeff_mk, Complex.norm_natCast, pow_one, one_mul]
  have hle : Nat.primeCounting n ≤ n + 1 := by
    rw [Nat.primeCounting_eq_primeCounting'_succ]
    exact Nat.count_le Nat.Prime
  exact_mod_cast hle

lemma logReciprocal_polyBound : PolyCoeffBound logReciprocalSeries := by
  refine ⟨(Real.log 2)⁻¹, 0, inv_nonneg.mpr (Real.log_nonneg one_le_two), fun n => ?_⟩
  simp only [logReciprocalSeries, PowerSeries.coeff_mk, pow_zero, mul_one]
  split_ifs with hn
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hlog2.trans_le hlogn)]
    exact inv_anti₀ hlog2 hlogn
  · simp [inv_nonneg.mpr (Real.log_nonneg one_le_two)]

lemma partLogDeriv_polyBound : PolyCoeffBound partLogDerivSeries := by
  refine ⟨1, 2, zero_le_one, fun n => ?_⟩
  simp only [partLogDerivSeries, PowerSeries.coeff_mk, one_mul]
  refine (norm_sum_le _ _).trans ?_
  have hle : ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, ‖if p ∣ n then (p : ℂ) else 0‖ ≤
      ∑ _p ∈ Finset.range (n + 1), (n : ℝ) := by
    calc ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, ‖if p ∣ n then (p : ℂ) else 0‖
        ≤ ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (n : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_le : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
          split_ifs
          · rw [Complex.norm_natCast]; exact_mod_cast hp_le
          · simp
      _ ≤ ∑ _p ∈ Finset.range (n + 1), (n : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
          intro p hp
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
  calc _ ≤ ((n : ℝ) + 1) * (n : ℝ) := by
        simpa [Finset.card_range, Nat.cast_add, Nat.cast_one] using hle
    _ ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [show (0 : ℝ) ≤ n by positivity]

/-- All-radii disk convergence bound: for every `0 < r < 1`, `‖a_n‖ ≤ C_r * r⁻¹ ^ n`. -/
@[expose] def DiskCoeffBound (F : PowerSeries ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖PowerSeries.coeff n F‖ ≤ C * r⁻¹ ^ n

lemma PolyCoeffBound.to_diskCoeffBound {F : PowerSeries ℂ} (hF : PolyCoeffBound F) :
    DiskCoeffBound F := by
  obtain ⟨C, p, hC, hb⟩ := hF
  intro r hr0 hr1
  have hsum : Summable (fun n : ℕ => (n + 1 : ℝ) ^ p * r ^ n) := by
    have hs := summable_pow_mul_geometric_of_norm_lt_one p
      (show ‖r‖ < 1 by simpa [abs_of_pos hr0] using hr1)
    have h := (hs.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by intro i m hh; exact Nat.add_right_cancel hh)).mul_right r⁻¹
    simpa [Function.comp_def, pow_succ, mul_assoc, hr0.ne'] using h
  obtain ⟨N, hN⟩ := (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one)).exists_forall_of_atTop
  let f : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ p * r ^ n
  let B : ℝ := max 1 (∑ k ∈ Finset.range (N + 1), f k)
  have hB_nonneg : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hB : ∀ n : ℕ, f n ≤ B := by
    intro n
    by_cases hn : N ≤ n
    · exact (hN n hn).le.trans (le_max_left _ _)
    · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      exact (Finset.single_le_sum (fun k _ => by dsimp [f]; positivity) hmem).trans (le_max_right _ _)
  refine ⟨C * B, mul_nonneg hC hB_nonneg, fun n => ?_⟩
  have hrn_pos : 0 < r ^ n := pow_pos hr0 n
  have hpow : (n + 1 : ℝ) ^ p ≤ B * r⁻¹ ^ n := by
    rw [inv_pow]
    calc (n + 1 : ℝ) ^ p = f n * (r ^ n)⁻¹ := by
          dsimp [f]; field_simp [hrn_pos.ne']
      _ ≤ B * (r ^ n)⁻¹ := mul_le_mul_of_nonneg_right (hB n) (inv_nonneg.mpr hrn_pos.le)
  calc ‖PowerSeries.coeff n F‖ ≤ C * (n + 1 : ℝ) ^ p := hb n
    _ ≤ C * (B * r⁻¹ ^ n) := mul_le_mul_of_nonneg_left hpow hC
    _ = (C * B) * r⁻¹ ^ n := by ring

private lemma shifted_geom (k : ℕ) {r : ℝ} (hr : 0 < r) (h1 : r < 1) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ k * r ^ n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k
    (show ‖r‖ < 1 by simpa [abs_of_pos hr] using h1)
  have h := (hs.comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) by intro i m hh; exact Nat.add_right_cancel hh)).mul_right r⁻¹
  simpa [Function.comp_def, pow_succ, mul_assoc, hr.ne'] using h

private lemma disk_jet_coeff_bound {F : PowerSeries ℂ} (hF : DiskCoeffBound F)
    (j : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖PowerSeries.coeff n (seriesJet F j)‖ ≤ K * (n + 1 : ℝ) ^ j * r⁻¹ ^ n := by
  obtain ⟨C, hC, hb⟩ := hF r hr0 hr1
  refine ⟨C * (j.factorial : ℝ) * r⁻¹ ^ j, by positivity, fun n => ?_⟩
  rw [seriesJet, PowerSeries.coeff_iterate_derivative, norm_mul, Complex.norm_natCast]
  have hasc : ((n + 1).ascFactorial j : ℝ) ≤ j.factorial * (n + 1 : ℝ) ^ j := by
    exact_mod_cast Nat.ascFactorial_le_factorial_mul_pow (n + 1) j
  have hFn : ‖PowerSeries.coeff (n + j) F‖ ≤ C * r⁻¹ ^ (n + j) := hb (n + j)
  calc ((n + 1).ascFactorial j : ℝ) * ‖PowerSeries.coeff (n + j) F‖
      ≤ (j.factorial * (n + 1 : ℝ) ^ j) * (C * r⁻¹ ^ (n + j)) :=
        mul_le_mul hasc hFn (norm_nonneg _) (by positivity)
    _ = (C * (j.factorial : ℝ) * r⁻¹ ^ j) * (n + 1 : ℝ) ^ j * r⁻¹ ^ n := by
        rw [pow_add]; ring

theorem seriesJet_abs {F : PowerSeries ℂ} (hF : DiskCoeffBound F) (j : ℕ)
    {q : ℂ} (hq : ‖q‖ < 1) : AbsAt (seriesJet F j) q := by
  obtain ⟨r₁, hqr₁, hr₁_lt⟩ := exists_between hq
  obtain ⟨r₂, hr₁₂, hr₂_lt⟩ := exists_between hr₁_lt
  have hr₁_pos : 0 < r₁ := (norm_nonneg q).trans_lt hqr₁
  have hr₂_pos : 0 < r₂ := hr₁_pos.trans hr₁₂
  obtain ⟨K, _, hbd⟩ := disk_jet_coeff_bound hF j hr₂_pos hr₂_lt
  have hr_ratio_pos : 0 < r₁ / r₂ := div_pos hr₁_pos hr₂_pos
  have hr_ratio_lt : r₁ / r₂ < 1 := (div_lt_one hr₂_pos).mpr hr₁₂
  refine ((shifted_geom j hr_ratio_pos hr_ratio_lt).mul_left K).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun n => ?_
  rw [term, norm_mul, norm_pow]
  calc ‖PowerSeries.coeff n (seriesJet F j)‖ * ‖q‖ ^ n
      ≤ (K * (n + 1 : ℝ) ^ j * r₂⁻¹ ^ n) * r₁ ^ n :=
        mul_le_mul (hbd n) (pow_le_pow_left₀ (norm_nonneg q) hqr₁.le n) (by positivity) (by positivity)
    _ = K * ((n + 1 : ℝ) ^ j * (r₁ / r₂) ^ n) := by
        rw [div_eq_mul_inv, mul_pow]; ring

theorem seriesJet_deriv {F : PowerSeries ℂ} (hF : DiskCoeffBound F) (j : ℕ)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt (value (seriesJet F j)) (value (seriesJet F (j + 1)) q) q := by
  obtain ⟨r₁, hqr₁, hr₁_lt⟩ := exists_between hq
  obtain ⟨r₂, hr₁₂, hr₂_lt⟩ := exists_between hr₁_lt
  have hr₁_pos : 0 < r₁ := (norm_nonneg q).trans_lt hqr₁
  have hr₂_pos : 0 < r₂ := hr₁_pos.trans hr₁₂
  obtain ⟨K, _, hbd_coeff⟩ := disk_jet_coeff_bound hF (j + 1) hr₂_pos hr₂_lt
  have hr_ratio_pos : 0 < r₁ / r₂ := div_pos hr₁_pos hr₂_pos
  have hr_ratio_lt : r₁ / r₂ < 1 := (div_lt_one hr₂_pos).mpr hr₁₂
  let f (n : ℕ) (z : ℂ) := term (seriesJet F j) z (n + 1)
  let g (n : ℕ) (z : ℂ) := term (seriesJet F (j + 1)) z n
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (f n) (g n z) z := by
    have he : PowerSeries.coeff n (seriesJet F (j + 1)) =
        PowerSeries.coeff (n + 1) (seriesJet F j) * (n + 1) := by
      rw [seriesJet, Function.iterate_succ_apply', PowerSeries.coeff_derivative]; rfl
    simpa [f, g, term, he, mul_assoc] using
      ((hasDerivAt_pow (n + 1) z).const_mul (PowerSeries.coeff (n + 1) (seriesJet F j)))
  have hbd : ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball (0 : ℂ) r₁ →
      ‖g n z‖ ≤ K * ((n + 1 : ℝ) ^ (j + 1) * (r₁ / r₂) ^ n) := fun n z hz => by
    have hzr : ‖z‖ ≤ r₁ := by simpa [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp hz).le
    rw [show g n z = term (seriesJet F (j + 1)) z n from rfl, term, norm_mul, norm_pow]
    calc ‖PowerSeries.coeff n (seriesJet F (j + 1))‖ * ‖z‖ ^ n
        ≤ (K * (n + 1 : ℝ) ^ (j + 1) * r₂⁻¹ ^ n) * r₁ ^ n :=
          mul_le_mul (hbd_coeff n) (pow_le_pow_left₀ (norm_nonneg z) hzr n) (by positivity) (by positivity)
      _ = K * ((n + 1 : ℝ) ^ (j + 1) * (r₁ / r₂) ^ n) := by
          rw [div_eq_mul_inv, mul_pow]; ring
  have hs := hasDerivAt_tsum_of_isPreconnected
    ((shifted_geom (j + 1) hr_ratio_pos hr_ratio_lt).mul_left K)
    (t := Metric.ball (0 : ℂ) r₁) Metric.isOpen_ball (convex_ball (0 : ℂ) r₁).isPreconnected
    (fun n z _ => hd n z) hbd (y₀ := q) (by simpa using hqr₁)
    ((seriesJet_abs hF j hq).of_norm.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by intro i m hh; exact Nat.add_right_cancel hh))
    (by simpa using hqr₁)
  have near : value (seriesJet F j) =ᶠ[𝓝 q] fun z => PowerSeries.coeff 0 (seriesJet F j) + ∑' n, f n z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show q ∈ Metric.ball (0 : ℂ) 1 by simpa using hq)] with z hz
    have h := (seriesJet_abs hF j (by simpa using hz : ‖z‖ < 1)).of_norm.sum_add_tsum_nat_add 1
    simpa [value, f, term] using h.symm
  exact (hs.const_add _).congr_of_eventuallyEq near

theorem seriesJet_analytic {F : PowerSeries ℂ} (hF : DiskCoeffBound F) (j : ℕ) :
    AnalyticOnNhd ℂ (value (seriesJet F j)) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro q hq
  exact (seriesJet_deriv hF j (by simpa using hq)).differentiableAt.differentiableWithinAt

private theorem eval_add {S T : PowerSeries ℂ} {q : ℂ} (h : AbsAt S q) (k : AbsAt T q) :
    AbsAt (S + T) q ∧ value (S + T) q = value S q + value T q := by
  have he : term (S + T) q = fun n => term S q n + term T q n := by
    funext n; simp [term, add_mul]
  exact ⟨by unfold AbsAt; rw [he]; exact (h.add k).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _),
    by simp only [value, he, h.of_norm.tsum_add k.of_norm]⟩

private theorem eval_mul {S T : PowerSeries ℂ} {q : ℂ} (h : AbsAt S q) (k : AbsAt T q) :
    AbsAt (S * T) q ∧ value (S * T) q = value S q * value T q := by
  have hconv (n : ℕ) : term (S * T) q n = ∑ kl ∈ Finset.antidiagonal n, term S q kl.1 * term T q kl.2 := by
    rw [term, PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.mem_antidiagonal.mp hkl, pow_add]; unfold term; ring
  constructor
  · simpa only [AbsAt, hconv] using summable_norm_sum_mul_antidiagonal_of_summable_norm h k
  · simpa only [value, hconv] using (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h k).symm

private theorem eval_const (c q : ℂ) : AbsAt (PowerSeries.C c) q ∧ value (PowerSeries.C c) q = c := by
  classical
  have he : term (PowerSeries.C c) q = Pi.single 0 c := by
    funext n; by_cases hn : n = 0 <;> simp [term, PowerSeries.coeff_C, hn]
  simp only [AbsAt, value, he, Pi.single_apply, apply_ite (fun z : ℂ => ‖z‖), norm_zero]
  refine ⟨summable_of_ne_finset_zero (s := {0}) (by simp_all), ?_⟩
  simp

theorem polynomial_value {ι : Type*} (P : MvPolynomial ι ℂ) {S : ι → PowerSeries ℂ}
    {q : ℂ} (hs : ∀ i, AbsAt (S i) q) :
    AbsAt (MvPolynomial.aeval S P) q ∧
      value (MvPolynomial.aeval S P) q = MvPolynomial.eval (fun i => value (S i) q) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa [PowerSeries.algebraMap_apply] using eval_const c q
  | add p t hp ht => simpa [hp.2, ht.2] using eval_add hp.1 ht.1
  | mul_X p i hp => simpa [hp.2] using eval_mul hp.1 (hs i)

theorem nome_abs (q : ℂ) : AbsAt PowerSeries.X q ∧ value PowerSeries.X q = q := by
  classical
  have he : term PowerSeries.X q = Pi.single 1 q := by
    funext n; by_cases hn : n = 1 <;> simp [term, PowerSeries.coeff_X, hn]
  simp only [AbsAt, value, he, Pi.single_apply, apply_ite (fun z : ℂ => ‖z‖), norm_zero]
  refine ⟨summable_of_ne_finset_zero (s := {1}) (by simp_all), ?_⟩
  simp

theorem formal_identity_on_disk {F : PowerSeries ℂ} (hF : DiskCoeffBound F)
    (P : MvPolynomial ℕ ℂ) (zero : MvPolynomial.aeval (seriesCoordinates F) P = 0)
    {q : ℂ} (hq : ‖q‖ < 1) :
    MvPolynomial.eval (analyticCoordinates F q) P = 0 := by
  have ha (j) : AbsAt (seriesCoordinates F j) q := by
    cases j with
    | zero => exact (nome_abs q).1
    | succ j => exact seriesJet_abs hF j hq
  have he : (fun i => value (seriesCoordinates F i) q) = analyticCoordinates F q := by
    funext i
    cases i with
    | zero => exact (nome_abs q).2
    | succ j => rfl
  have hh := (polynomial_value P ha).2
  rw [zero, he] at hh
  simpa [value, term] using hh.symm

/-! ### 3. Ordinary Point Selection & Polynomial Differential Flow -/

private theorem partial_ne {P : MvPolynomial ℕ ℂ} {i : ℕ} (hi : i ∈ P.vars) :
    MvPolynomial.pderiv i P ≠ 0 := by
  obtain ⟨m, hm, hi⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have h := Finsupp.mem_support_iff.mp hi
  intro hz
  have he := congrArg (fun f : MvPolynomial ℕ ℂ => f.coeff (m - Finsupp.single i 1)) hz
  rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel h] at he
  change _ = (0 : ℂ) at he
  refine (mul_ne_zero (MvPolynomial.mem_support_iff.mp hm) ?_) he
  exact_mod_cast Nat.succ_ne_zero (((m - Finsupp.single i 1 : ℕ →₀ ℕ)) i)

/-- Minimal-total-degree ordinary relation lemma. -/
theorem ordinary_relation {α : Type} (U : Set α) (ne : U.Nonempty) (y : ℕ → α → ℂ)
    (ex : ∃ P : MvPolynomial ℕ ℂ, P ≠ 0 ∧ ∀ x ∈ U, MvPolynomial.eval (fun i => y i x) P = 0) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℂ) (x : α), x ∈ U ∧
      MvPolynomial.eval (fun i : Fin (n + 1) => y i.val x) (MvPolynomial.pderiv (Fin.last n) Q) ≠ 0 ∧
      ∀ z ∈ U, MvPolynomial.eval (fun i : Fin (n + 1) => y i.val z) Q = 0 := by
  classical
  let rel (P : MvPolynomial ℕ ℂ) := P ≠ 0 ∧ ∀ x ∈ U, MvPolynomial.eval (fun i => y i x) P = 0
  have hex : ∃ d : ℕ, ∃ P : MvPolynomial ℕ ℂ, P.totalDegree = d ∧ rel P := by
    obtain ⟨P, hp⟩ := ex; exact ⟨_, P, rfl, hp⟩
  obtain ⟨P, hd, hp⟩ := Nat.find_spec hex
  have vars : P.vars.Nonempty := by
    by_contra! hv
    have hc := MvPolynomial.vars_eq_empty_iff_eq_C.mp hv
    obtain ⟨x, hx⟩ := ne
    have hh := hp.2 x hx; rw [hc, MvPolynomial.eval_C] at hh
    exact hp.1 (hc.trans (by rw [hh, MvPolynomial.C_0]))
  let n := P.vars.max' vars
  have hn : n ∈ P.vars := Finset.max'_mem _ _
  obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P (Fin.val : Fin (n + 1) → ℕ)
    Fin.val_injective (fun i hi => ⟨⟨i, Nat.lt_succ_of_le (Finset.le_max' _ i hi)⟩, rfl⟩)
  have hpd : 0 < P.totalDegree := by
    by_contra! h
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    rw [hc, MvPolynomial.vars_C] at hn
    exact Finset.notMem_empty _ hn
  have low := PakPrimes.BorelStokesVandermonde.degree_pderiv_lt n P hpd
  have notRel : ¬ rel (MvPolynomial.pderiv n P) := fun h =>
    Nat.find_min hex (hd ▸ low) ⟨_, rfl, h⟩
  obtain ⟨x, hx, hS⟩ : ∃ x ∈ U, MvPolynomial.eval (fun i => y i x) (MvPolynomial.pderiv n P) ≠ 0 := by
    by_contra! hz; exact notRel ⟨partial_ne hn, hz⟩
  refine ⟨n, Q, x, hx, ?_, ?_⟩
  · rw [← hQ] at hS
    have d := MvPolynomial.pderiv_rename (f := (Fin.val : Fin (n + 1) → ℕ)) Fin.val_injective (Fin.last n) Q
    have hh := congrArg (MvPolynomial.eval (fun i => y i x)) d
    rw [MvPolynomial.eval_rename] at hh
    exact fun he => hS (hh.trans he)
  · intro z hz; have h := hp.2 z hz; rw [← hQ, MvPolynomial.eval_rename] at h; exact h

theorem polynomial_chain {ι : Type} [Fintype ι] (P : MvPolynomial ι ℂ)
    (u v : ι → ℝ → ℂ) (x : ℝ) (hu : ∀ i, HasDerivAt (u i) (v i x) x) :
    HasDerivAt (fun p => MvPolynomial.eval (fun i => u i p) P)
      (∑ i, MvPolynomial.eval (fun j => u j x) (MvPolynomial.pderiv i P) * v i x) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.pderiv_C] using hasDerivAt_const x a
  | add P Q hP hQ => simpa only [map_add, add_mul, Finset.sum_add_distrib] using! hP.add hQ
  | mul_X P k hP =>
    have h := hP.mul (hu k)
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X,
      Pi.single_apply, add_mul, Finset.sum_add_distrib]
    convert h using 1
    simp [Finset.mul_sum, mul_comm, mul_left_comm]

/-- Membership in the local polynomial differential algebra generated by `u`. -/
def Generated {ι : Type} (u : ι → ℝ → ℂ) (x : ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ A : MvPolynomial ι ℂ, f =ᶠ[𝓝 x] fun p => MvPolynomial.eval (fun i => u i p) A

namespace Generated

variable {ι : Type} {u : ι → ℝ → ℂ} {x : ℝ} {f g : ℝ → ℂ}

theorem coord (i : ι) : Generated u x (u i) := ⟨X i, by simp⟩
theorem const (c : ℂ) : Generated u x (fun _ => c) := ⟨C c, by simp⟩
theorem congr (h : Generated u x f) (e : f =ᶠ[𝓝 x] g) : Generated u x g := by
  obtain ⟨P, h⟩ := h; exact ⟨P, e.symm.trans h⟩
theorem add (h : Generated u x f) (k : Generated u x g) : Generated u x (f + g) := by
  obtain ⟨A, h⟩ := h; obtain ⟨B, k⟩ := k; exact ⟨A + B, by simpa using! h.add k⟩
theorem sub (h : Generated u x f) (k : Generated u x g) : Generated u x (f - g) := by
  obtain ⟨A, h⟩ := h; obtain ⟨B, k⟩ := k; exact ⟨A - B, by simpa using! h.sub k⟩
theorem mul (h : Generated u x f) (k : Generated u x g) : Generated u x (f * g) := by
  obtain ⟨A, h⟩ := h; obtain ⟨B, k⟩ := k; exact ⟨A * B, by simpa using! h.mul k⟩
theorem pow (h : Generated u x f) (n : ℕ) : Generated u x (f ^ n) := by
  obtain ⟨A, h⟩ := h; exact ⟨A ^ n, by filter_upwards [h] with p hp; simp [hp]⟩

theorem finsetSum {κ : Type*} (s : Finset κ) (f : κ → ℝ → ℂ)
    (h : ∀ i ∈ s, Generated u x (f i)) :
    Generated u x (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! (const (u := u) (x := x) 0)
  | insert i s hi ih =>
    simpa [hi] using (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem evalPoly {κ : Type} (v : κ → ℝ → ℂ) (hv : ∀ i, Generated u x (v i))
    (P : MvPolynomial κ ℂ) : Generated u x (fun p => MvPolynomial.eval (fun i => v i p) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using const (u := u) (x := x) a
  | add p q hp hq => simpa only [map_add] using! hp.add hq
  | mul_X p i hp => simpa only [map_mul, eval_X] using! hp.mul (hv i)

theorem deriv [Fintype ι] (h : Generated u x f)
    (smooth : ∀ᶠ p in 𝓝 x, ∀ i, DifferentiableAt ℝ (u i) p)
    (closed : ∀ i, Generated u x (_root_.deriv (u i))) :
    Generated u x (_root_.deriv f) := by
  classical
  obtain ⟨A, ha⟩ := h
  have g (i : ι) : Generated u x (fun p => MvPolynomial.eval (fun j => u j p) (MvPolynomial.pderiv i A)) :=
    ⟨_, .rfl⟩
  apply (finsetSum Finset.univ _ (fun i _ => (g i).mul (closed i))).congr
  filter_upwards [ha.eventuallyEq_nhds, smooth] with p hp hd
  simpa only [Finset.sum_apply, Pi.mul_apply] using
    ((polynomial_chain A u (fun i => _root_.deriv (u i)) p
      (fun i => (hd i).hasDerivAt)).deriv.symm.trans hp.deriv_eq.symm)

end Generated

theorem autonomous_readout {ι : Type} [Fintype ι] (u : ι → ℝ → ℂ) (x : ℝ) (f : ℝ → ℂ)
    (readout : Generated u x f)
    (smooth : ∀ᶠ p in 𝓝 x, ∀ i, DifferentiableAt ℝ (u i) p)
    (closed : ∀ i, Generated u x (_root_.deriv (u i))) :
    ∃ P : MvPolynomial (Fin (Fintype.card ι + 1)) ℂ, P ≠ 0 ∧
      ∀ᶠ p in 𝓝 x, MvPolynomial.eval (fun i : Fin (Fintype.card ι + 1) => iteratedDeriv i.val f p) P = 0 := by
  classical
  have all (j : ℕ) : Generated u x (iteratedDeriv j f) := by
    induction j with
    | zero => simpa using readout
    | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv smooth closed
  choose jet hj using fun j : Fin (Fintype.card ι + 1) => all j.val
  have dep : ¬ AlgebraicIndependent ℂ jet := by
    intro hi
    have := hi.cardinalMk_le_trdeg
    simp [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype] at this
  rw [algebraicIndependent_iff] at dep
  push Not at dep
  obtain ⟨P, hz, hp⟩ := dep
  refine ⟨P, hp, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hj] with p he
  have hh := congrArg (MvPolynomial.eval (fun i => u i p)) hz
  change (MvPolynomial.aeval (fun i => u i p)) (MvPolynomial.bind₁ jet P) = 0 at hh
  rw [MvPolynomial.aeval_bind₁] at hh
  simpa only [he] using! hh

/-! ### 4. Real-Analytic Nome Chart on `ℝ` & Link 2 (`autonomous_transfer`) -/

@[expose] def tRay (u : ℝ) : ℂ := (Real.exp (-u) : ℂ)
@[expose] def qRay (u : ℝ) : ℂ := (Real.exp (-Real.exp (-u)) : ℂ)

@[expose] def scaledRay (F : PowerSeries ℂ) (u : ℝ) : ℂ :=
  tRay u * value F (qRay u)

lemma qRay_disk (u : ℝ) : ‖qRay u‖ < 1 := by
  rw [qRay, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr (Real.exp_pos _)

lemma tRay_ne_zero (u : ℝ) : tRay u ≠ 0 := by
  unfold tRay
  exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

lemma qRay_ne_zero (u : ℝ) : qRay u ≠ 0 := by
  unfold qRay
  exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

lemma tRay_deriv (u : ℝ) : HasDerivAt tRay (-tRay u) u := by
  have h : HasDerivAt (fun y : ℝ => (Real.exp (-y) : ℂ)) (-(Real.exp (-u) : ℂ)) u := by
    simpa [Function.comp_def] using (hasDerivAt_id u).neg.exp.ofReal_comp
  exact h

lemma qRay_deriv (u : ℝ) : HasDerivAt qRay (tRay u * qRay u) u := by
  have h1 : HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-u)) u := by
    have h0 : HasDerivAt (fun x : ℝ => -Real.exp (-x)) (-(Real.exp (-u) * -1)) u :=
      ((hasDerivAt_id u).neg.exp).neg
    convert h0 using 1
    ring
  have h2 : HasDerivAt (fun x : ℝ => (Real.exp (-Real.exp (-x)) : ℂ))
      ((Real.exp (-Real.exp (-u)) * Real.exp (-u) : ℝ) : ℂ) u := h1.exp.ofReal_comp
  convert h2 using 1
  · unfold qRay; rfl
  · unfold tRay qRay; rw [← Complex.ofReal_mul, mul_comm]

lemma tRay_analytic (u : ℝ) : AnalyticAt ℝ tRay u :=
  (Complex.ofRealCLM.analyticAt _).comp (analyticAt_id.neg.rexp)

lemma qRay_analytic (u : ℝ) : AnalyticAt ℝ qRay u :=
  (Complex.ofRealCLM.analyticAt _).comp ((analyticAt_id.neg.rexp).neg.rexp)

theorem ray_source_deriv {F : PowerSeries ℂ} (hF : DiskCoeffBound F) (j : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => analyticCoordinates F (qRay x) (j + 1))
      (tRay u * qRay u * analyticCoordinates F (qRay u) (j + 2)) u := by
  simpa [analyticCoordinates, Function.comp_def, mul_comm] using
    (seriesJet_deriv hF j (qRay_disk u)).scomp u (qRay_deriv u)

theorem ray_source_analytic {F : PowerSeries ℂ} (hF : DiskCoeffBound F) (j : ℕ) (u : ℝ) :
    AnalyticAt ℝ (fun x : ℝ => analyticCoordinates F (qRay x) j) u := by
  cases j with
  | zero => exact qRay_analytic u
  | succ j =>
    exact (((seriesJet_analytic hF j) _ (by simpa using qRay_disk u)).restrictScalars (𝕜 := ℝ)).comp
      (qRay_analytic u)

theorem scaledRay_analytic {F : PowerSeries ℂ} (hF : DiskCoeffBound F) (u : ℝ) :
    AnalyticAt ℝ (scaledRay F) u :=
  (tRay_analytic u).mul (ray_source_analytic hF 1 u)

private theorem local_to_tail_real {F : PowerSeries ℂ} (hF : DiskCoeffBound F)
    {J : ℕ} (P : MvPolynomial (Fin J) ℂ) {x : ℝ}
    (h : ∀ᶠ u in 𝓝 x, MvPolynomial.eval (fun i : Fin J => iteratedDeriv i.val (scaledRay F) u) P = 0) :
    ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun i : Fin J => iteratedDeriv i.val (scaledRay F) u) P = 0 := by
  have an (u : ℝ) (k : ℕ) : AnalyticAt ℝ (iteratedDeriv k (scaledRay F)) u := by
    induction k with
    | zero => simpa using scaledRay_analytic hF u
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have all : AnalyticOnNhd ℝ
      (fun u => MvPolynomial.eval (fun i : Fin J => iteratedDeriv i.val (scaledRay F) u) P) univ := by
    clear h
    intro u _
    induction P using MvPolynomial.induction_on with
    | C => simpa using analyticAt_const
    | add a b ha hb => simpa only [map_add] using! ha.add hb
    | mul_X a i ha => simpa only [map_mul, eval_X] using! ha.mul (an u i.val)
  exact eventually_atTop.mpr ⟨0, fun u _ =>
    all.eqOn_zero_of_preconnected_of_eventuallyEq_zero convex_univ.isPreconnected (mem_univ x) h (mem_univ u)⟩

private theorem transfer_at_ordinary {F : PowerSeries ℂ} (hF : DiskCoeffBound F)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℂ) (x : ℝ)
    (ordinary : MvPolynomial.eval (fun i : Fin (n + 1) => analyticCoordinates F (qRay x) i.val)
      (MvPolynomial.pderiv (Fin.last n) Q) ≠ 0)
    (ident : ∀ u : ℝ, MvPolynomial.eval (fun i : Fin (n + 1) => analyticCoordinates F (qRay u) i.val) Q = 0) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop, MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay F) u) P = 0 := by
  classical
  let v (i : Fin (n + 1)) (u : ℝ) := analyticCoordinates F (qRay u) i.val
  let g (i : Fin (n + 1)) (u : ℝ) := MvPolynomial.eval (fun j => v j u) (MvPolynomial.pderiv i Q)
  let top := Fin.last n
  let S := g top
  have hd (u : ℝ) (i : Fin (n + 1)) : DifferentiableAt ℝ (v i) u :=
    (ray_source_analytic hF i.val u).differentiableAt
  have chain (A : MvPolynomial (Fin (n + 1)) ℂ) (u : ℝ) :=
    polynomial_chain A v (fun i => _root_.deriv (v i)) u (fun i => (hd u i).hasDerivAt)
  have vanish (u : ℝ) : ∑ i, g i u * _root_.deriv (v i) u = 0 := by
    have near : (fun z => MvPolynomial.eval (fun i => v i z) Q) =ᶠ[𝓝 u] (fun _ => 0) :=
      Filter.Eventually.of_forall ident
    exact (chain Q u).deriv.symm.trans (near.deriv_eq.trans (deriv_const _ _))
  have hn : n ≠ 0 := by
    rintro rfl
    have he := vanish x
    change ∑ i : Fin 1, g i x * _root_.deriv (v i) x = 0 at he
    rw [Fin.sum_univ_one] at he
    have ds : _root_.deriv (v 0) x = tRay x * qRay x := (qRay_deriv x).deriv
    rw [ds] at he
    have hs : tRay x * qRay x ≠ 0 := mul_ne_zero (tRay_ne_zero x) (qRay_ne_zero x)
    exact mul_ne_zero ordinary hs he
  let invS (u : ℝ) := (S u)⁻¹
  let uState : Fin (n + 1) ⊕ Fin 2 → ℝ → ℂ := Sum.elim v ![tRay, invS]
  have h_inr0 : uState (.inr 0) = tRay := funext fun _ => rfl
  let G := Generated uState x
  have gv (i : Fin (n + 1)) : G (v i) := Generated.coord (u := uState) (.inl i)
  have gt : G tRay := Generated.coord (u := uState) (.inr 0)
  have gw : G invS := Generated.coord (u := uState) (.inr 1)
  have gc (c : ℂ) : G (fun _ => c) := Generated.const _
  have gspeed : G (fun z => tRay z * qRay z) := gt.mul (gv 0)
  have gg (i : Fin (n + 1)) : G (g i) := Generated.evalPoly v gv _
  have Snz : ∀ᶠ u in 𝓝 x, S u ≠ 0 := (chain (MvPolynomial.pderiv top Q) x).continuousAt.eventually_ne ordinary
  have low (i : Fin (n + 1)) (hi : i ≠ top) : G (_root_.deriv (v i)) := by
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact gspeed.congr (Filter.Eventually.of_forall fun z => (qRay_deriv z).deriv.symm)
    | succ k =>
      have lt : k + 2 < n + 1 := by
        have h : k + 1 ≠ n := fun eqn => hi (Fin.ext eqn); omega
      exact (gspeed.mul (gv ⟨k + 2, lt⟩)).congr
        (Filter.Eventually.of_forall fun z => (ray_source_deriv hF k z).deriv.symm)
  let lowSum := ∑ i ∈ Finset.univ.erase top, g i * _root_.deriv (v i)
  have gl : G lowSum :=
    Generated.finsetSum _ _ (fun i hi => (gg i).mul (low i (Finset.mem_erase.mp hi).1))
  have dv (i : Fin (n + 1)) : G (_root_.deriv (v i)) := by
    by_cases hi : i = top
    · subst i
      apply (((gc (-1)).mul gl).mul gw).congr
      filter_upwards [Snz] with z nz
      have he := vanish z
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at he
      change (-1) * lowSum z * (S z)⁻¹ = _root_.deriv (v top) z
      have hh : S z * _root_.deriv (v top) z + lowSum z = 0 := by
        simpa [S, lowSum, Finset.sum_apply] using he
      field_simp [nz]; linear_combination -hh
    · exact low i hi
  have dS : G (_root_.deriv S) := by
    let D (i : Fin (n + 1)) (z : ℝ) :=
      MvPolynomial.eval (fun k => v k z) (MvPolynomial.pderiv i (MvPolynomial.pderiv top Q))
    have gen (i) : G (D i) := Generated.evalPoly v gv _
    apply (Generated.finsetSum Finset.univ _ (fun i _ => (gen i).mul (dv i))).congr
    filter_upwards with z
    simpa [D, Finset.sum_apply] using (chain (MvPolynomial.pderiv top Q) z).deriv.symm
  have smooth : ∀ᶠ z in 𝓝 x, ∀ i, DifferentiableAt ℝ (uState i) z := by
    filter_upwards [Snz] with z nz i
    rcases i with i | i
    · exact hd z i
    · fin_cases i
      · exact (tRay_deriv z).differentiableAt
      · exact (chain (MvPolynomial.pderiv top Q) z).differentiableAt.inv nz
  have closed (i) : G (_root_.deriv (uState i)) := by
    rcases i with i | i
    · exact dv i
    · fin_cases i
      · change G (_root_.deriv (uState (.inr 0)))
        rw [h_inr0]
        exact ((gc (-1)).mul gt).congr
          (Filter.Eventually.of_forall fun z => by simpa using (tRay_deriv z).deriv.symm)
      · apply (((gc (-1)).mul dS).mul (gw.pow 2)).congr
        filter_upwards [Snz] with z nz
        have hi := ((chain (MvPolynomial.pderiv top Q) z).differentiableAt.hasDerivAt.inv nz).deriv
        change (-1) * _root_.deriv S z * ((S z)⁻¹) ^ 2 = _root_.deriv invS z
        change _root_.deriv invS z = -_root_.deriv S z / (S z) ^ 2 at hi
        rw [hi]; simp [inv_pow, div_eq_mul_inv]
  have readout : G (scaledRay F) :=
    (gt.mul (gv ⟨1, by omega⟩)).congr (Filter.Eventually.of_forall fun _ => rfl)
  obtain ⟨P, hp, hz⟩ := autonomous_readout uState x _ readout smooth closed
  exact ⟨_, P, hp, local_to_tail_real hF P hz⟩

/-- **Link 2 (`autonomous_transfer`)**: Any nonzero polynomial relation among
`(q, F, F', ..., F^{(m)})` transfers to a nonzero autonomous polynomial ODE for
`u ↦ exp (-u) * value F (exp (-exp (-u)))` eventually as `u → +∞`. -/
theorem autonomous_transfer_disk {F : PowerSeries ℂ} (hF : DiskCoeffBound F)
    (hdep : ¬ AlgebraicIndependent ℂ (seriesCoordinates F)) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay F) u) P = 0 := by
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨Q, hQ_zero, hQ_ne⟩ := hdep
  have relation (u : ℝ) :
      MvPolynomial.eval (fun i => analyticCoordinates F (qRay u) i) Q = 0 :=
    formal_identity_on_disk hF Q hQ_zero (qRay_disk u)
  obtain ⟨n, A, x, _, ordinary, ident⟩ :=
    ordinary_relation (univ : Set ℝ) ⟨0, mem_univ 0⟩ (fun i u => analyticCoordinates F (qRay u) i)
      ⟨Q, hQ_ne, fun u _ => relation u⟩
  exact transfer_at_ordinary hF A x ordinary (fun u => ident u (mem_univ u))

theorem autonomous_transfer {F : PowerSeries ℂ} (hF : PolyCoeffBound F)
    (hdep : ¬ AlgebraicIndependent ℂ (seriesCoordinates F)) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay F) u) P = 0 :=
  autonomous_transfer_disk hF.to_diskCoeffBound hdep

theorem autonomous_transfer_indicator
    (hdep : ¬ AlgebraicIndependent ℂ indicatorCoordinates) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay I_prime) u) P = 0 :=
  autonomous_transfer I_prime_polyBound hdep

theorem autonomous_transfer_logReciprocal
    (hdep : ¬ AlgebraicIndependent ℂ logReciprocalCoordinates) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay logReciprocalSeries) u) P = 0 :=
  autonomous_transfer logReciprocal_polyBound hdep

/-- **Logarithmic-Derivative Transfer (Partitions into Primes)**:
If `P, G` satisfy all-radii disk coefficient bounds, `X * P' = G * P`, and `value P (qRay u) ≠ 0`
on `ℝ`, then any algebraic differential dependence of `P` transfers to a nonzero autonomous
polynomial ODE for `scaledRay G`. -/
theorem autonomous_transfer_log_deriv {P G : PowerSeries ℂ}
    (hP : DiskCoeffBound P) (hG : DiskCoeffBound G)
    (hode : PowerSeries.X * PowerSeries.derivative P = G * P)
    (hP_nz : ∀ u : ℝ, value P (qRay u) ≠ 0)
    (hdep : ¬ AlgebraicIndependent ℂ (seriesCoordinates P)) :
    ∃ (J : ℕ) (R : MvPolynomial (Fin J) ℂ), R ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.val (scaledRay G) u) R = 0 := by
  classical
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨Q, hQ_zero, hQ_ne⟩ := hdep
  have relation (u : ℝ) :
      MvPolynomial.eval (fun i => analyticCoordinates P (qRay u) i) Q = 0 :=
    formal_identity_on_disk hP Q hQ_zero (qRay_disk u)
  obtain ⟨n, A, x, _, ordinary, ident_set⟩ :=
    ordinary_relation (univ : Set ℝ) ⟨0, mem_univ 0⟩ (fun i u => analyticCoordinates P (qRay u) i)
      ⟨Q, hQ_ne, fun u _ => relation u⟩
  have ident (u : ℝ) :
      MvPolynomial.eval (fun i : Fin (n + 1) => analyticCoordinates P (qRay u) i.val) A = 0 :=
    ident_set u (mem_univ u)
  let v (i : Fin (n + 1)) (u : ℝ) := analyticCoordinates P (qRay u) i.val
  let g (i : Fin (n + 1)) (u : ℝ) := MvPolynomial.eval (fun j => v j u) (MvPolynomial.pderiv i A)
  let top := Fin.last n
  let S := g top
  have hd (u : ℝ) (i : Fin (n + 1)) : DifferentiableAt ℝ (v i) u :=
    (ray_source_analytic hP i.val u).differentiableAt
  have chain (B : MvPolynomial (Fin (n + 1)) ℂ) (u : ℝ) :=
    polynomial_chain B v (fun i => _root_.deriv (v i)) u (fun i => (hd u i).hasDerivAt)
  have vanish (u : ℝ) : ∑ i, g i u * _root_.deriv (v i) u = 0 := by
    have near : (fun z => MvPolynomial.eval (fun i => v i z) A) =ᶠ[𝓝 u] (fun _ => 0) :=
      Filter.Eventually.of_forall ident
    exact (chain A u).deriv.symm.trans (near.deriv_eq.trans (deriv_const _ _))
  have hn : n ≠ 0 := by
    rintro rfl
    have he := vanish x
    change ∑ i : Fin 1, g i x * _root_.deriv (v i) x = 0 at he
    rw [Fin.sum_univ_one] at he
    have ds : _root_.deriv (v 0) x = tRay x * qRay x := (qRay_deriv x).deriv
    rw [ds] at he
    exact mul_ne_zero ordinary (mul_ne_zero (tRay_ne_zero x) (qRay_ne_zero x)) he
  let invS (u : ℝ) := (S u)⁻¹
  let invV1 (u : ℝ) := (v ⟨1, by omega⟩ u)⁻¹
  let uState : Fin (n + 1) ⊕ Fin 3 → ℝ → ℂ := Sum.elim v ![tRay, invS, invV1]
  have h_inr0 : uState (.inr 0) = tRay := funext fun _ => rfl
  let Gen := Generated uState x
  have gv (i : Fin (n + 1)) : Gen (v i) := Generated.coord (u := uState) (.inl i)
  have gt : Gen tRay := Generated.coord (u := uState) (.inr 0)
  have gw : Gen invS := Generated.coord (u := uState) (.inr 1)
  have gz : Gen invV1 := Generated.coord (u := uState) (.inr 2)
  have gc (c : ℂ) : Gen (fun _ => c) := Generated.const _
  have gspeed : Gen (fun z => tRay z * qRay z) := gt.mul (gv 0)
  have gg (i : Fin (n + 1)) : Gen (g i) := Generated.evalPoly v gv _
  have Snz : ∀ᶠ u in 𝓝 x, S u ≠ 0 := (chain (MvPolynomial.pderiv top A) x).continuousAt.eventually_ne ordinary
  have low (i : Fin (n + 1)) (hi : i ≠ top) : Gen (_root_.deriv (v i)) := by
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact gspeed.congr (Filter.Eventually.of_forall fun z => (qRay_deriv z).deriv.symm)
    | succ k =>
      have lt : k + 2 < n + 1 := by
        have h : k + 1 ≠ n := fun eqn => hi (Fin.ext eqn); omega
      exact (gspeed.mul (gv ⟨k + 2, lt⟩)).congr
        (Filter.Eventually.of_forall fun z => (ray_source_deriv hP k z).deriv.symm)
  let lowSum := ∑ i ∈ Finset.univ.erase top, g i * _root_.deriv (v i)
  have gl : Gen lowSum :=
    Generated.finsetSum _ _ (fun i hi => (gg i).mul (low i (Finset.mem_erase.mp hi).1))
  have dv (i : Fin (n + 1)) : Gen (_root_.deriv (v i)) := by
    by_cases hi : i = top
    · subst i
      apply (((gc (-1)).mul gl).mul gw).congr
      filter_upwards [Snz] with z nz
      have he := vanish z
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at he
      change (-1) * lowSum z * (S z)⁻¹ = _root_.deriv (v top) z
      have hh : S z * _root_.deriv (v top) z + lowSum z = 0 := by
        simpa [S, lowSum, Finset.sum_apply] using he
      field_simp [nz]; linear_combination -hh
    · exact low i hi
  have dS : Gen (_root_.deriv S) := by
    let D (i : Fin (n + 1)) (z : ℝ) :=
      MvPolynomial.eval (fun k => v k z) (MvPolynomial.pderiv i (MvPolynomial.pderiv top A))
    have gen (i) : Gen (D i) := Generated.evalPoly v gv _
    apply (Generated.finsetSum Finset.univ _ (fun i _ => (gen i).mul (dv i))).congr
    filter_upwards with z
    simpa [D, Finset.sum_apply] using (chain (MvPolynomial.pderiv top A) z).deriv.symm
  have smooth : ∀ᶠ z in 𝓝 x, ∀ i, DifferentiableAt ℝ (uState i) z := by
    filter_upwards [Snz] with z nz i
    rcases i with i | i
    · exact hd z i
    · fin_cases i
      · exact (tRay_deriv z).differentiableAt
      · exact (chain (MvPolynomial.pderiv top A) z).differentiableAt.inv nz
      · exact (hd z ⟨1, by omega⟩).inv (hP_nz z)
  have closed (i) : Gen (_root_.deriv (uState i)) := by
    rcases i with i | i
    · exact dv i
    · fin_cases i
      · change Gen (_root_.deriv (uState (.inr 0)))
        rw [h_inr0]
        exact ((gc (-1)).mul gt).congr
          (Filter.Eventually.of_forall fun z => by simpa using (tRay_deriv z).deriv.symm)
      · apply (((gc (-1)).mul dS).mul (gw.pow 2)).congr
        filter_upwards [Snz] with z nz
        have hi := ((chain (MvPolynomial.pderiv top A) z).differentiableAt.hasDerivAt.inv nz).deriv
        change (-1) * _root_.deriv S z * ((S z)⁻¹) ^ 2 = _root_.deriv invS z
        change _root_.deriv invS z = -_root_.deriv S z / (S z) ^ 2 at hi
        rw [hi]; simp [inv_pow, div_eq_mul_inv]
      · apply (((gc (-1)).mul (dv ⟨1, by omega⟩)).mul (gz.pow 2)).congr
        filter_upwards with z
        have hi := ((hd z ⟨1, by omega⟩).hasDerivAt.inv (hP_nz z)).deriv
        change (-1) * _root_.deriv (v ⟨1, by omega⟩) z * ((v ⟨1, by omega⟩ z)⁻¹) ^ 2 = _root_.deriv invV1 z
        change _root_.deriv invV1 z = -_root_.deriv (v ⟨1, by omega⟩) z / (v ⟨1, by omega⟩ z) ^ 2 at hi
        rw [hi]; simp [inv_pow, div_eq_mul_inv]
  have g_Pderiv1 : Gen (fun z => value (seriesJet P 1) (qRay z)) := by
    by_cases h1 : n = 1
    · subst h1
      apply (((gc (-1)).mul (gg 0)).mul gw).congr
      filter_upwards [Snz] with z nz
      have he := vanish z
      rw [Fin.sum_univ_two] at he
      have ds0 : _root_.deriv (v 0) z = tRay z * qRay z := (qRay_deriv z).deriv
      have ds1 : _root_.deriv (v 1) z = tRay z * qRay z * value (seriesJet P 1) (qRay z) := by
        simpa [v, analyticCoordinates] using (ray_source_deriv hP 0 z).deriv
      rw [ds0, ds1] at he
      have htz := mul_ne_zero (tRay_ne_zero z) (qRay_ne_zero z)
      have hS_eq : S z = g 1 z := by simp [S, top, Fin.last]
      have hh : g 0 z + g 1 z * value (seriesJet P 1) (qRay z) = 0 := by
        apply mul_right_cancel₀ htz
        linear_combination he
      change (-1) * g 0 z * (S z)⁻¹ = value (seriesJet P 1) (qRay z)
      rw [hS_eq]
      have hgnz : g 1 z ≠ 0 := hS_eq ▸ nz
      field_simp [hgnz]; linear_combination -hh
    · exact (gv ⟨2, by omega⟩).congr (Filter.Eventually.of_forall fun _ => rfl)
  have hval_ode (u : ℝ) :
      qRay u * value (seriesJet P 1) (qRay u) = value G (qRay u) * value P (qRay u) := by
    have hq := qRay_disk u
    have hL := eval_mul (nome_abs (qRay u)).1 (seriesJet_abs hP 1 hq)
    have hR := eval_mul (seriesJet_abs hG 0 hq) (seriesJet_abs hP 0 hq)
    have h1 : seriesJet P 1 = PowerSeries.derivative P := by simp [seriesJet]
    have h2 : seriesJet G 0 = G := by simp [seriesJet]
    have h3 : seriesJet P 0 = P := by simp [seriesJet]
    rw [h1] at hL; rw [h2, h3] at hR
    have hq_val := (nome_abs (qRay u)).2
    have h_eq := congrArg (fun S => value S (qRay u)) hode
    rw [hL.2, hR.2, hq_val] at h_eq
    exact h_eq
  have readout : Gen (scaledRay G) := by
    apply ((gspeed.mul g_Pderiv1).mul gz).congr
    filter_upwards with z
    change tRay z * qRay z * value (seriesJet P 1) (qRay z) * (value P (qRay z))⁻¹ =
      tRay z * value G (qRay z)
    rw [mul_assoc (tRay z) (qRay z), hval_ode z]
    have hpz := hP_nz z
    field_simp [hpz]
  obtain ⟨R, hp, hz⟩ := autonomous_readout uState x _ readout smooth closed
  exact ⟨_, R, hp, local_to_tail_real hG R hz⟩

end
end PakPrimes.PrimeNome
