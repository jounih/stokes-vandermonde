module

public import PakPrimes.NthPrimeNomeTransfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The nth-prime series and the algebraic step in the balanced-residue proof

The prime sequence is indexed from one. The separation theorem uses complex-linear
derivations of a commutative algebra. Constructing those derivations on the ramified
minors and transporting prime coefficients to them are separate analytic obligations.
-/

public section

namespace PakPrimes.NthPrime

open MvPolynomial Filter
open scoped BigOperators Matrix

noncomputable section

/-- Coefficients are `0, 2, 3, 5, 7, 11, ...`. -/
@[expose] def series : PowerSeries ℂ := PowerSeries.mk fun n =>
  match n with
  | 0 => 0
  | k + 1 => (Nat.nth Nat.Prime k : ℂ)

@[simp] theorem coeff_zero : PowerSeries.coeff 0 series = 0 := by simp [series]
@[simp] theorem coeff_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) series = (Nat.nth Nat.Prime n : ℂ) := by simp [series]

example : PowerSeries.coeff 1 series = 2 := by simp
example : PowerSeries.coeff 2 series = 3 := by simp

/-- The elementary Chebyshev bound already gives a quadratic majorant for the primes. -/
theorem nth_prime_quadratic_bound (n : ℕ) : Nat.nth Nat.Prime n ≤ (4 * (n + 1)) ^ 2 := by
  let k := 4 * (n + 1)
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hcount := Chebyshev.pi_ge_of_four_le (n := k ^ 2) (by nlinarith)
  have hlog : 0 < Real.log ((k ^ 2 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k ^ 2 by nlinarith))
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hL : Real.log ((k ^ 2 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith [Real.log_le_sub_one_of_pos hkR]
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnk : (k : ℝ) = 4 * ((n : ℝ) + 1) := by simp [k]
  have hnum : ((n : ℝ) + 1) * Real.log ((k ^ 2 : ℕ) : ℝ) ≤
      (k ^ 2 : ℕ) * Real.log 2 := by
    calc
      _ ≤ ((n : ℝ) + 1) * (2 * k) := by gcongr
      _ = (k : ℝ)^2 * (1/2) := by rw [hnk]; ring
      _ ≤ _ := by push_cast; gcongr
  have hn : n + 1 ≤ Nat.primeCounting (k ^ 2) := by
    exact_mod_cast ((le_div_iff₀ hlog).2 hnum).trans hcount
  have hc : n < Nat.count Nat.Prime (k ^ 2 + 1) := hn
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hc)

theorem series_polyCoeffBound : PrimeNome.PolyCoeffBound series := by
  refine ⟨16, 2, by norm_num, fun n => ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ, Complex.norm_natCast]
    have hh : (Nat.nth Nat.Prime n : ℝ) ≤ (4 * ((n : ℝ) + 1))^2 := by
      exact_mod_cast nth_prime_quadratic_bound n
    push_cast
    nlinarith [show (0 : ℝ) ≤ n by positivity]

theorem series_diskCoeffBound : PrimeNome.DiskCoeffBound series :=
  series_polyCoeffBound.to_diskCoeffBound

variable {A : Type*} [CommRing A] [Nontrivial A] [Algebra ℂ A]

omit [Nontrivial A] in
private theorem derivation_aeval {ι : Type*} [Fintype ι] (d : Derivation ℂ A A)
    (x : ι → A) (P : MvPolynomial ι ℂ) :
    d (aeval x P) = ∑ j, aeval x (pderiv j P) * d (x j) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add,
      pderiv_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]

/-- Simple residues `cₘ (-m)^j` of the individual jets give full algebraic independence.
The integer sites begin at two. The singularity algebra may have zero divisors. -/
theorem independent_of_balanced_derivations (x : ℕ → A)
    (delta : ℕ → Derivation ℂ A A) (c : ℕ → ℂ) (hc : ∀ m, c m ≠ 0)
    (hjet : ∀ m j, delta m (x j) = algebraMap ℂ A (c m * (-((m : ℂ) + 2)) ^ j))
    (k : ℕ) : AlgebraicIndependent ℂ (fun i : Fin k => x i.val) := by
  classical
  rw [algebraicIndependent_iff]
  let y : Fin k → A := fun i => x i.val
  intro P hP
  change aeval y P = 0 at hP
  suffices ∀ n (Q : MvPolynomial (Fin k) ℂ), Q.totalDegree = n → aeval y Q = 0 → Q = 0 from
    this _ P rfl hP
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro Q hdeg hQ
    have hconst (heq : Q = C (Q.coeff 0)) : Q = 0 := by
      have h0 := hQ
      rw [heq, aeval_C] at h0
      have hc0 : Q.coeff 0 = 0 := (algebraMap ℂ A).injective (by simpa using h0)
      simpa [hc0] using heq
    by_cases hn : n = 0
    · exact hconst (totalDegree_eq_zero_iff_eq_C.mp (hdeg.trans hn))
    let nodes : Fin k → ℂ := fun i => -((i.val : ℂ) + 2)
    have hinj : Function.Injective nodes := by
      intro i j he
      change -((i.val : ℂ) + 2) = -((j.val : ℂ) + 2) at he
      exact Fin.ext (by exact_mod_cast (add_right_cancel (neg_inj.mp he)))
    let V := Matrix.vandermonde nodes
    let W := (algebraMap ℂ A).mapMatrix V
    have hdet : W.det ∈ nonZeroDivisors A := by
      change ((algebraMap ℂ A).mapMatrix V).det ∈ _
      rw [← RingHom.map_det]
      exact ((isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)).map _).mem_nonZeroDivisors
    have hv : W *ᵥ (fun j : Fin k => aeval y (pderiv j Q)) = 0 := by
      funext i
      have h := derivation_aeval (delta i.val) y Q
      rw [hQ, map_zero] at h
      simp only [y, hjet, map_mul] at h
      have hf : algebraMap ℂ A (c i.val) * (∑ j : Fin k,
          algebraMap ℂ A ((nodes i) ^ j.val) * aeval y (pderiv j Q)) = 0 := by
        rw [Finset.mul_sum]
        simpa only [nodes, y, mul_comm, mul_left_comm, mul_assoc] using h.symm
      have hnz := (isUnit_iff_ne_zero.mpr (hc i.val)).map (algebraMap ℂ A)
      have hv0 := hnz.mul_right_inj.mp (hf.trans (mul_zero _).symm)
      simpa only [W, V, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.vandermonde_apply, Pi.zero_apply] using hv0
    have hpartials := Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hdet hv
    apply hconst
    apply BorelStokesVandermonde.all_partials_zero
    intro j
    exact ih _ (hdeg ▸ BorelStokesVandermonde.degree_pderiv_lt j Q (by omega)) _
      rfl (congrFun hpartials j)

omit [Nontrivial A] in
/-- The alien commutator determines all jet residues from the single primitive residue. -/
theorem jet_residue_of_commutator (D delta : Derivation ℂ A A) (t : A) (c omega : ℂ)
    (ht : delta t = algebraMap ℂ A c)
    (hcomm : ∀ a, delta (D a) = D (delta a) - omega • delta a) (j : ℕ) :
    delta ((D : A → A)^[j] t) = algebraMap ℂ A (c * (-omega) ^ j) := by
  induction j with
  | zero => simpa using ht
  | succ j ih =>
    rw [Function.iterate_succ_apply', hcomm, ih, D.map_algebraMap, zero_sub,
      Algebra.smul_def, ← map_mul, ← map_neg, pow_succ]
    congr 1
    ring

/-- The analytic input needed to transfer an exact relation on the real prime ray
to the representation of its jets in the ramified singularity algebra. -/
@[expose] def RepresentsPrimeRay (D : Derivation ℂ A A) (t : A) : Prop :=
  ∀ (k : ℕ) (P : MvPolynomial (Fin k) ℂ),
    (∀ᶠ u : ℝ in Filter.atTop,
      eval (fun j : Fin k => iteratedDeriv j.val (PrimeNome.nthPrimeRay series) u) P = 0) →
    aeval (fun j : Fin k => (D : A → A)^[j.val] t) P = 0

/-- Conditional conclusion for Pak 2.5a. The analytic hypotheses are the representation
of the actual prime ray, the alien commutators and the nonzero primitive residues.
The nome transfer, unit-disk convergence, all jet residues and separation are proved. -/
theorem pak_2_5a_of_balanced_model (D : Derivation ℂ A A) (t : A)
    (hrep : RepresentsPrimeRay D t) (delta : ℕ → Derivation ℂ A A)
    (c : ℕ → ℂ) (hc : ∀ m, c m ≠ 0)
    (hres : ∀ m, delta m t = algebraMap ℂ A (c m))
    (hcomm : ∀ m a, delta m (D a) = D (delta m a) - ((m : ℂ) + 2) • delta m a) :
    AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates series) := by
  by_contra hd
  obtain ⟨k, P, hp, hP⟩ := PrimeNome.nthPrime_autonomous_transfer_disk series_diskCoeffBound hd
  have hind := independent_of_balanced_derivations (fun j => (D : A → A)^[j] t) delta c hc
    (fun m => jet_residue_of_commutator D (delta m) t (c m) ((m : ℂ) + 2) (hres m) (hcomm m)) k
  exact hp (algebraicIndependent_iff.mp hind P (hrep k P hP))

end
end PakPrimes.NthPrime
