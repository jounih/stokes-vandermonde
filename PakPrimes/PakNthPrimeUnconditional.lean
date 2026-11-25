module

public import PakPrimes.PakNthPrimeClosure
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic

/-! # Pak Conjecture 2.5a (`∑ p_n q^n`) — Unconditional Discharge of `hsector` from `Main.PNTAllOrders`

This module discharges the final remaining complex-analytic hypothesis (`hsector`) in
`PakPrimes.PakNthPrimeClosure.pak_2_5a_of_pnt_and_sectorial_gevrey1_bridge`, establishing
Pak's Conjecture 2.5a (`AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series)`)
unconditionally from `Main.PNTAllOrders` alone.

### Architecture
1. **Reusable Gevrey-1 Log-Power Asymptotic API (`HasGev1Exp`)**:
   - Submultiplicativity of the `(n! / k!)` weight via Vandermonde's identity.
   - Closure under constants, `1/z`, `log z / z`, sums, products (exact Cauchy-product remainder),
     Cauchy `iteratedDeriv` transfer on shrunk sectors, and multivariate polynomial evaluation.
   - Flatness on a positive real ray forces all formal log-polynomial coefficients to vanish,
     upgrading `HasGev1Exp` directly to the Gevrey-1 Watson bound `‖F z‖ ≤ C * A^N * N! / ‖z‖^N`.
2. **Rotated Stieltjes Integral `S_phi`** (`φ = 11π/24`):
   - Holomorphic on `ℂ \ e^{iφ} ℝ_{≥ 0}`, exact identity `(e^w / w) * S_phi w = Ei_complex w + i π`,
     deep lower half-plane bound, and exact Gevrey-1 asymptotic expansion on `W_δ`.
3. **Implicit Inverse `w_plus` and `F_plus(v) = w_plus(v) / S_phi(w_plus(v))`**:
   - Banach contraction on `{Im v < -C₀}` and wide closed sector `V_δ`, formal Gevrey-1 log-power
     recursion, and finite-degree residual bound yielding `HasGev1Exp V_δ (F_plus v / v)`.
4. **Entire Continuation `I_entire` and Sectorial Truncated Convolution**:
   - Piecewise horizontal contour `Γ(y₀)`, Cauchy overlap invariance, agreement with `I_plus` on `ℝ`,
     exact deep lower half-plane convolution, right-half-plane contour split, and unified exponential
     error bound on the enlarged sector `Σ₀ = rotatedClosedSector (-19π/24) (3π/8) R₀`.
5. **Shift Integration & Closure**:
   - Gevrey-1 log-power expansion of `I_entire u / u` on `Σ₀`, Cauchy jet transfer to
     `Σ = rotatedClosedSector (-3π/4) (π/3) R` (opening `13π/12 > π`), and final theorem
     `pak_2_5a_of_pnt : Main.PNTAllOrders → AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series)`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.PakNthPrimeUnconditional

open Complex Real Filter MeasureTheory Set MvPolynomial
open scoped Topology BigOperators

noncomputable section

open PakPrimes.PakNthPrimeStokes PakPrimes.PakNthPrimeClosure

/-! ### 1. Reusable Gevrey-1 Log-Power Asymptotic Framework (`HasGev1Exp`) -/

/-- Formal log-power coefficient table `a n k` representing `∑_{n ≥ 0} (∑_{k ≤ n} a n k * (log z)^k) / z^n`. -/
abbrev LogCoeff := ℕ → ℕ → ℂ

/-- Single degree-`n` log-polynomial term `(∑_{k=0}^n a n k * (log z)^k) / z^n`. -/
@[expose] def evalTerm (a : LogCoeff) (n : ℕ) (z : ℂ) : ℂ :=
  (∑ k ∈ Finset.range (n + 1), a n k * Complex.log z ^ k) / z ^ n

/-- Order-`N` truncation `∑_{n=0}^{N-1} evalTerm a n z`. -/
@[expose] def evalTrunc (a : LogCoeff) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, evalTerm a n z

/-- Uniform Gevrey-1 log-power asymptotic expansion on a set `S ⊆ {z : ℂ | 1 ≤ ‖z‖}`:
`‖a n k‖ ≤ C * A^n * n! / k!` and `‖f z - evalTrunc a N z‖ ≤ C * ‖z‖ * A^N * N! / ‖z‖^N`. -/
@[expose] def HasGev1Exp (S : Set ℂ) (f : ℂ → ℂ) (a : LogCoeff) : Prop :=
  (∀ n k, n < k → a n k = 0) ∧
  ∃ C > 0, ∃ A ≥ 1,
    (∀ n k, k ≤ n → ‖a n k‖ ≤ C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) ∧
    (∀ N : ℕ, ∀ z ∈ S, ‖f z - evalTrunc a N z‖ ≤ C * ‖z‖ * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N)

/-! #### 1a. Elementary Combinatorial & Complex-Logarithm Inequalities -/

/-- Vandermonde sum bound: for `0 ≤ n, K ≤ N`, `∑_{k} C(K, k) ≤ C(N, n)` over `k ≤ n` and `K - k ≤ N - n`. -/
lemma sum_choose_le_choose {N n K : ℕ} (hn : n ≤ N) (hK : K ≤ N) :
    (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n), K.choose k) ≤ N.choose n := by
  have hvand : N.choose n = ∑ p ∈ Finset.antidiagonal n, K.choose p.1 * (N - K).choose p.2 := by
    have h := Nat.add_choose_eq K (N - K) n
    rwa [Nat.add_sub_of_le hK] at h
  rw [hvand]
  let f : ℕ → ℕ × ℕ := fun k => (k, n - k)
  have hinj : Set.InjOn f ↑((Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n)) := by
    intro a _ b _ hab
    exact congr_arg Prod.fst hab
  have hmaps : ∀ k ∈ (Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n),
      f k ∈ Finset.antidiagonal n := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_antidiagonal]
    exact Nat.add_sub_of_le hk.2.1
  calc ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n), K.choose k
      ≤ ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n),
          K.choose (f k).1 * (N - K).choose (f k).2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        have hnk : n - k ≤ N - K := by omega
        have hpos : 1 ≤ (N - K).choose (n - k) := Nat.choose_pos hnk
        dsimp only [f]
        calc K.choose k = K.choose k * 1 := (mul_one _).symm
          _ ≤ K.choose k * (N - K).choose (n - k) := Nat.mul_le_mul_left _ hpos
    _ = ∑ p ∈ ((Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n)).image f,
          K.choose p.1 * (N - K).choose p.2 :=
        (Finset.sum_image (f := fun p : ℕ × ℕ => K.choose p.1 * (N - K).choose p.2) hinj).symm
    _ ≤ ∑ p ∈ Finset.antidiagonal n, K.choose p.1 * (N - K).choose p.2 := by
        refine Finset.sum_le_sum_of_subset ?_
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
        exact hmaps k hk

/-- Elementary factorial-choose identity for Cauchy product bounds:
`n! / k! * (N - n)! / (K - k)! = (N! / K!) * (C(K, k) / C(N, n))`. -/
lemma fact_div_mul_fact_div {N n K k : ℕ} (hn : n ≤ N) (hkK : k ≤ K) :
    ((n.factorial : ℝ) / (k.factorial : ℝ)) * (((N - n).factorial : ℝ) / ((K - k).factorial : ℝ)) =
      ((N.factorial : ℝ) / (K.factorial : ℝ)) * ((K.choose k : ℝ) / (N.choose n : ℝ)) := by
  have h1 : (K.choose k : ℝ) * (k.factorial : ℝ) * ((K - k).factorial : ℝ) = (K.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkK
  have h2 : (N.choose n : ℝ) * (n.factorial : ℝ) * ((N - n).factorial : ℝ) = (N.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hn
  have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hKkf : ((K - k).factorial : ℝ) ≠ 0 := by positivity
  have hKf : (K.factorial : ℝ) ≠ 0 := by positivity
  have hNn : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  field_simp [hkf, hKkf, hKf, hNn]
  nlinarith

/-- For `1 ≤ ‖z‖`, `exp ‖Complex.log z‖ ≤ exp π * ‖z‖`. -/
lemma exp_norm_log_le {z : ℂ} (hz : 1 ≤ ‖z‖) :
    Real.exp ‖Complex.log z‖ ≤ Real.exp Real.pi * ‖z‖ := by
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hlog_nn : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
  have hnorm_log : ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
    rw [Complex.log]
    calc ‖(Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * I‖
        ≤ ‖(Real.log ‖z‖ : ℂ)‖ + ‖(Complex.arg z : ℂ) * I‖ := norm_add_le _ _
      _ = |Real.log ‖z‖| + |Complex.arg z| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_I, mul_one]
      _ = Real.log ‖z‖ + |Complex.arg z| := by rw [abs_of_nonneg hlog_nn]
      _ ≤ Real.log ‖z‖ + Real.pi := add_le_add_right (Complex.abs_arg_le_pi z) _
  calc Real.exp ‖Complex.log z‖
      ≤ Real.exp (Real.log ‖z‖ + Real.pi) := Real.exp_le_exp.mpr hnorm_log
    _ = Real.exp (Real.log ‖z‖) * Real.exp Real.pi := Real.exp_add _ _
    _ = Real.exp Real.pi * ‖z‖ := by rw [Real.exp_log hz_pos, mul_comm]

/-- Partial sum of `x^k / k!` is bounded by `exp x` for `0 ≤ x`. -/
lemma sum_pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    (∑ k ∈ Finset.range m, x ^ k / (k.factorial : ℝ)) ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx m

/-- Norm bound on `evalTerm a n z` from Gevrey-1 coefficient bounds on `1 ≤ ‖z‖`. -/
lemma norm_evalTerm_le {a : LogCoeff} {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) {n : ℕ}
    (ha : ∀ k ≤ n, ‖a n k‖ ≤ C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ))
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖evalTerm a n z‖ ≤ C * Real.exp Real.pi * ‖z‖ * A ^ n * (n.factorial : ℝ) / ‖z‖ ^ n := by
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  dsimp only [evalTerm]
  rw [norm_div, norm_pow]
  have hsum : ‖∑ k ∈ Finset.range (n + 1), a n k * Complex.log z ^ k‖ ≤
      C * Real.exp Real.pi * ‖z‖ * A ^ n * (n.factorial : ℝ) := by
    calc ‖∑ k ∈ Finset.range (n + 1), a n k * Complex.log z ^ k‖
        ≤ ∑ k ∈ Finset.range (n + 1), ‖a n k * Complex.log z ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            (C * A ^ n * (n.factorial : ℝ)) * (‖Complex.log z‖ ^ k / (k.factorial : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [norm_mul, norm_pow]
          have h1 := ha k hkn
          calc ‖a n k‖ * ‖Complex.log z‖ ^ k
              ≤ (C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) * ‖Complex.log z‖ ^ k :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (C * A ^ n * (n.factorial : ℝ)) * (‖Complex.log z‖ ^ k / (k.factorial : ℝ)) := by ring
      _ = (C * A ^ n * (n.factorial : ℝ)) *
            ∑ k ∈ Finset.range (n + 1), ‖Complex.log z‖ ^ k / (k.factorial : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ (C * A ^ n * (n.factorial : ℝ)) * Real.exp ‖Complex.log z‖ :=
          mul_le_mul_of_nonneg_left (sum_pow_div_factorial_le_exp (norm_nonneg _) _) (by positivity)
      _ ≤ (C * A ^ n * (n.factorial : ℝ)) * (Real.exp Real.pi * ‖z‖) :=
          mul_le_mul_of_nonneg_left (exp_norm_log_le hz) (by positivity)
      _ = C * Real.exp Real.pi * ‖z‖ * A ^ n * (n.factorial : ℝ) := by ring
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- Elementary bound `(n + 1) ≤ 2 ^ n` for all `n : ℕ`. -/
lemma nat_succ_le_two_pow (n : ℕ) : (n + 1 : ℝ) ≤ 2 ^ n := by
  have h : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ']
      omega
  exact_mod_cast h

/-- Elementary factorial shift: `(N + 1)! ≤ 2 ^ N * N!`. -/
lemma factorial_succ_le_two_pow (N : ℕ) : ((N + 1).factorial : ℝ) ≤ 2 ^ N * (N.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact mul_le_mul_of_nonneg_right (nat_succ_le_two_pow N) (by positivity)

/-- Elementary `∑_{n=0}^{N-1} 1 / C(N, n) ≤ 4` for all `N : ℕ`. -/
lemma sum_inv_choose_le (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 : ℝ) / (N.choose n : ℝ)) ≤ 4 := by
  have hC_ge : ∀ a b : ℕ, 1 ≤ b → b ≤ a - 1 → a ≤ a.choose b := by
    intro a
    induction a with
    | zero => intro b hb1 hb2; omega
    | succ a iha =>
      intro b hb1 hb2
      by_cases hb : b = 1
      · subst hb; simp
      · by_cases hba : b = a
        · subst hba
          rw [Nat.choose_symm_of_eq_add (rfl : b + 1 = b + 1), Nat.choose_one_right]
        · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
          rw [Nat.choose_succ_succ]
          have h1' := iha (b' + 1) (by omega) (by omega)
          have h2' : 1 ≤ a.choose b' := Nat.choose_pos (by omega)
          have heq : a.choose b'.succ = a.choose (b' + 1) := rfl
          omega
  match N with
  | 0 => simp
  | 1 => simp
  | 2 =>
    simp [Finset.sum_range_succ, Nat.choose]
    norm_num
  | m + 3 =>
    have hsplit : ∑ n ∈ Finset.range (m + 3), (1 : ℝ) / ((m + 3).choose n : ℝ) =
        1 / ((m + 3).choose 0 : ℝ) + 1 / ((m + 3).choose 1 : ℝ) +
          ∑ n ∈ Finset.Ico 2 (m + 3), (1 : ℝ) / ((m + 3).choose n : ℝ) := by
      have h1 : Finset.range (m + 3) = {0, 1} ∪ Finset.Ico 2 (m + 3) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_Ico]; omega
      rw [h1, Finset.sum_union (by simp [Finset.disjoint_left]),
        Finset.sum_pair (by norm_num), add_assoc]
    rw [hsplit]
    have h0 : (1 : ℝ) / ((m + 3).choose 0 : ℝ) = 1 := by simp
    have h1 : (1 : ℝ) / ((m + 3).choose 1 : ℝ) ≤ 1 := by
      rw [Nat.choose_one_right, div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ m + 3)
    have hmid : ∑ n ∈ Finset.Ico 2 (m + 3), (1 : ℝ) / ((m + 3).choose n : ℝ) ≤
        ∑ _n ∈ Finset.Ico 2 (m + 3), (1 : ℝ) / ((m + 3 : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun n hn => ?_
      simp only [Finset.mem_Ico] at hn
      have hge : m + 3 ≤ (m + 3).choose n := hC_ge (m + 3) n (by omega) (by omega)
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by exact_mod_cast hge)
    have hconst : ∑ _n ∈ Finset.Ico 2 (m + 3), (1 : ℝ) / ((m + 3 : ℕ) : ℝ) ≤ 1 := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one_div,
        div_le_one (by positivity)]
      exact_mod_cast (by omega : m + 3 - 2 ≤ m + 3)
    linarith

/-! #### 1b. Closure Properties of `HasGev1Exp` -/

/-- Constant coefficient table. -/
@[expose] def constCoeff (c : ℂ) : LogCoeff :=
  fun n k => if n = 0 ∧ k = 0 then c else 0

/-- `1/z` coefficient table. -/
@[expose] def invCoeff : LogCoeff :=
  fun n k => if n = 1 ∧ k = 0 then 1 else 0

/-- `log z / z` coefficient table. -/
@[expose] def logDivCoeff : LogCoeff :=
  fun n k => if n = 1 ∧ k = 1 then 1 else 0

/-- Pointwise addition of coefficient tables. -/
@[expose] def addCoeff (a b : LogCoeff) : LogCoeff :=
  fun n k => a n k + b n k

/-- Scalar multiplication of a coefficient table. -/
@[expose] def smulCoeff (c : ℂ) (a : LogCoeff) : LogCoeff :=
  fun n k => c * a n k

/-- Cauchy product of two formal log-power coefficient tables. -/
@[expose] def mulCoeff (a b : LogCoeff) : LogCoeff :=
  fun N K => ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (K + 1), a n k * b (N - n) (K - k)

/-- Formal derivative coefficient table: `d/dz (L^k / z^n) = (k L^{k-1} - n L^k) / z^{n+1}`. -/
@[expose] def derivCoeff (a : LogCoeff) : LogCoeff :=
  fun n k =>
    match n with
    | 0 => 0
    | m + 1 => ((k + 1 : ℕ) : ℂ) * a m (k + 1) - (m : ℂ) * a m k

lemma evalTerm_add (a b : LogCoeff) (n : ℕ) (z : ℂ) :
    evalTerm (addCoeff a b) n z = evalTerm a n z + evalTerm b n z := by
  dsimp only [evalTerm, addCoeff]
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1; exact Finset.sum_congr rfl fun k _ => by ring

lemma evalTrunc_add (a b : LogCoeff) (N : ℕ) (z : ℂ) :
    evalTrunc (addCoeff a b) N z = evalTrunc a N z + evalTrunc b N z := by
  dsimp only [evalTrunc]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => evalTerm_add a b n z

lemma evalTerm_smul (c : ℂ) (a : LogCoeff) (n : ℕ) (z : ℂ) :
    evalTerm (smulCoeff c a) n z = c * evalTerm a n z := by
  dsimp only [evalTerm, smulCoeff]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun k _ => by ring

lemma evalTrunc_smul (c : ℂ) (a : LogCoeff) (N : ℕ) (z : ℂ) :
    evalTrunc (smulCoeff c a) N z = c * evalTrunc a N z := by
  dsimp only [evalTrunc]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => evalTerm_smul c a n z

lemma hasGev1Exp_const {S : Set ℂ} (hS : ∀ z ∈ S, 1 ≤ ‖z‖) (c : ℂ) :
    HasGev1Exp S (fun _ => c) (constCoeff c) := by
  refine ⟨fun n k hnk => by simp [constCoeff]; omega, ‖c‖ + 1, by positivity, 1, le_rfl, ?_, ?_⟩
  · intro n k _
    dsimp only [constCoeff]
    split_ifs with h
    · rcases h with ⟨rfl, rfl⟩; simp
    · simp; positivity
  · intro N z hz
    have hz1 : 1 ≤ ‖z‖ := hS z hz
    cases N with
    | zero =>
      simp only [evalTrunc, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have : ‖c‖ ≤ (‖c‖ + 1) * ‖z‖ := by nlinarith [norm_nonneg c]
      exact this
    | succ M =>
      have hev : evalTrunc (constCoeff c) (M + 1) z = c := by
        dsimp only [evalTrunc]
        rw [Finset.sum_eq_single 0]
        · simp [evalTerm, constCoeff]
        · intro n _ hn0; simp [evalTerm, constCoeff, hn0]
        · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos M)) h0
      rw [hev, sub_self, norm_zero]
      positivity

lemma hasGev1Exp_inv {S : Set ℂ} (hS : ∀ z ∈ S, 1 ≤ ‖z‖) :
    HasGev1Exp S (fun z => z⁻¹) invCoeff := by
  refine ⟨fun n k hnk => by simp [invCoeff]; omega, 1, zero_lt_one, 1, le_rfl, ?_, ?_⟩
  · intro n k _
    dsimp only [invCoeff]
    split_ifs with h
    · rcases h with ⟨rfl, rfl⟩; simp
    · simp; positivity
  · intro N z hz
    have hz1 : 1 ≤ ‖z‖ := hS z hz
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz1
    match N with
    | 0 =>
      simp only [evalTrunc, Finset.range_zero, Finset.sum_empty, sub_zero, norm_inv,
        one_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have : ‖z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz1
      linarith
    | 1 =>
      have hev : evalTrunc invCoeff 1 z = 0 := by
        simp [evalTrunc, evalTerm, invCoeff]
      rw [hev, sub_zero, norm_inv]
      simp only [one_mul, pow_one, Nat.factorial_one, Nat.cast_one, mul_one, div_self hz_pos.ne']
      exact inv_le_one_of_one_le₀ hz1
    | M + 2 =>
      have hev : evalTrunc invCoeff (M + 2) z = z⁻¹ := by
        dsimp only [evalTrunc]
        rw [Finset.sum_eq_single 1]
        · simp [evalTerm, invCoeff]
        · intro n _ hn1; simp [evalTerm, invCoeff, hn1]
        · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
      rw [hev, sub_self, norm_zero]
      positivity

lemma hasGev1Exp_add {S : Set ℂ} {f g : ℂ → ℂ} {a b : LogCoeff}
    (hf : HasGev1Exp S f a) (hg : HasGev1Exp S g b) :
    HasGev1Exp S (fun z => f z + g z) (addCoeff a b) := by
  rcases hf with ⟨ha0, Ca, hCa, Aa, hAa, ha_coeff, ha_rem⟩
  rcases hg with ⟨hb0, Cb, hCb, Ab, hAb, hb_coeff, hb_rem⟩
  let C := Ca + Cb
  let A := max Aa Ab
  have hC : 0 < C := add_pos hCa hCb
  have hA1 : 1 ≤ A := hAa.trans (le_max_left _ _)
  have hAaA : Aa ≤ A := le_max_left _ _
  have hAbA : Ab ≤ A := le_max_right _ _
  refine ⟨fun n k hnk => by simp [addCoeff, ha0 n k hnk, hb0 n k hnk], C, hC, A, hA1, ?_, ?_⟩
  · intro n k hkn
    dsimp only [addCoeff]
    calc ‖a n k + b n k‖ ≤ ‖a n k‖ + ‖b n k‖ := norm_add_le _ _
      _ ≤ Ca * Aa ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) +
            Cb * Ab ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) :=
          add_le_add (ha_coeff n k hkn) (hb_coeff n k hkn)
      _ ≤ Ca * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) +
            Cb * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := by
          gcongr
      _ = C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := by dsimp [C]; ring
  · intro N z hz
    rw [evalTrunc_add]
    have hrew : f z + g z - (evalTrunc a N z + evalTrunc b N z) =
        (f z - evalTrunc a N z) + (g z - evalTrunc b N z) := by ring
    rw [hrew]
    calc ‖(f z - evalTrunc a N z) + (g z - evalTrunc b N z)‖
        ≤ ‖f z - evalTrunc a N z‖ + ‖g z - evalTrunc b N z‖ := norm_add_le _ _
      _ ≤ Ca * ‖z‖ * Aa ^ N * (N.factorial : ℝ) / ‖z‖ ^ N +
            Cb * ‖z‖ * Ab ^ N * (N.factorial : ℝ) / ‖z‖ ^ N :=
          add_le_add (ha_rem N z hz) (hb_rem N z hz)
      _ ≤ Ca * ‖z‖ * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N +
            Cb * ‖z‖ * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by
          gcongr
      _ = C * ‖z‖ * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by dsimp [C]; ring

lemma hasGev1Exp_smul {S : Set ℂ} {f : ℂ → ℂ} {a : LogCoeff} (c : ℂ)
    (hf : HasGev1Exp S f a) :
    HasGev1Exp S (fun z => c * f z) (smulCoeff c a) := by
  rcases hf with ⟨ha0, Ca, hCa, Aa, hAa, ha_coeff, ha_rem⟩
  refine ⟨fun n k hnk => by simp [smulCoeff, ha0 n k hnk], (‖c‖ + 1) * Ca, by positivity, Aa, hAa, ?_, ?_⟩
  · intro n k hkn
    dsimp only [smulCoeff]
    rw [norm_mul]
    calc ‖c‖ * ‖a n k‖ ≤ (‖c‖ + 1) * (Ca * Aa ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) :=
          mul_le_mul (by linarith) (ha_coeff n k hkn) (norm_nonneg _) (by positivity)
      _ = (‖c‖ + 1) * Ca * Aa ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := by ring
  · intro N z hz
    rw [evalTrunc_smul, ← mul_sub, norm_mul]
    calc ‖c‖ * ‖f z - evalTrunc a N z‖
        ≤ (‖c‖ + 1) * (Ca * ‖z‖ * Aa ^ N * (N.factorial : ℝ) / ‖z‖ ^ N) :=
          mul_le_mul (by linarith) (ha_rem N z hz) (norm_nonneg _) (by positivity)
      _ = (‖c‖ + 1) * Ca * ‖z‖ * Aa ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by ring

/-- Exact algebraic identity: `evalTerm (mulCoeff a b) p z = ∑_{n=0}^p evalTerm a n z * evalTerm b (p-n) z`. -/
lemma evalTerm_mulCoeff {a b : LogCoeff}
    (ha0 : ∀ n k, n < k → a n k = 0) (hb0 : ∀ n k, n < k → b n k = 0) (p : ℕ) (z : ℂ) :
    evalTerm (mulCoeff a b) p z =
      ∑ n ∈ Finset.range (p + 1), evalTerm a n z * evalTerm b (p - n) z := by
  dsimp only [evalTerm, mulCoeff]
  have hsum_num :
      ∑ K ∈ Finset.range (p + 1),
        (∑ n ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (K + 1), a n k * b (p - n) (K - k)) *
          Complex.log z ^ K =
      ∑ n ∈ Finset.range (p + 1),
        (∑ k ∈ Finset.range (n + 1), a n k * Complex.log z ^ k) *
          (∑ j ∈ Finset.range (p - n + 1), b (p - n) j * Complex.log z ^ j) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnp : n ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp_rw [Finset.mul_sum]
    -- Expand LHS as `∑_{K ≤ p} ∑_{k ≤ K} a n k * b (p-n) (K-k) * L^K`
    have hL : (∑ K ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (K + 1),
        a n k * b (p - n) (K - k) * Complex.log z ^ K) =
        ∑ k ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p + 1 - k),
          a n k * b (p - n) j * Complex.log z ^ (k + j) := by
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ => (⟨x.2, x.1 - x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
        omega
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Finset.mem_sigma, Finset.mem_range] at hx₁ hx₂
        have h1 : x₁.2 = x₂.2 := congr_arg Sigma.fst heq
        have h2 : x₁.1 - x₁.2 = x₂.1 - x₂.2 := by
          simpa using congr_arg Sigma.snd heq
        exact Sigma.ext (by omega) (heq_of_eq h1)
      · intro y hy
        simp only [Finset.mem_sigma, Finset.mem_range] at hy
        refine ⟨⟨y.1 + y.2, y.1⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_range]; omega
        · ext <;> simp
      · intro x hx
        simp only [Finset.mem_sigma, Finset.mem_range] at hx
        have hadd : x.2 + (x.1 - x.2) = x.1 := Nat.add_sub_of_le (by omega)
        rw [hadd]
    rw [hL]
    have hcut1 : (∑ k ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p + 1 - k),
        a n k * b (p - n) j * Complex.log z ^ (k + j)) =
        ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (p - n + 1),
          a n k * b (p - n) j * Complex.log z ^ (k + j) := by
      rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hnp))]
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [← Finset.sum_subset (Finset.range_mono (by omega : p - n + 1 ≤ p + 1 - k))]
        intro j _ hj
        have hgt : p - n < j := by
          simp only [Finset.mem_range, not_lt] at hj; omega
        rw [hb0 (p - n) j hgt]; ring
      · intro k _ hk
        have hgt : n < k := by
          simp only [Finset.mem_range, not_lt] at hk; omega
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [ha0 n k hgt]; ring
    rw [hcut1]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring
  rw [hsum_num, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnp : n ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hnp]

/-- Exact Cauchy-product remainder identity for `evalTrunc`. -/
lemma evalTrunc_mul_rem {a b : LogCoeff}
    (ha0 : ∀ n k, n < k → a n k = 0) (hb0 : ∀ n k, n < k → b n k = 0)
    (f g : ℂ → ℂ) (M : ℕ) (z : ℂ) :
    f z * g z - evalTrunc (mulCoeff a b) M z =
      (∑ n ∈ Finset.range M, evalTerm a n z * (g z - evalTrunc b (M - n) z)) +
        (f z - evalTrunc a M z) * g z := by
  have hsplit : evalTrunc (mulCoeff a b) M z =
      ∑ n ∈ Finset.range M, evalTerm a n z * evalTrunc b (M - n) z := by
    dsimp only [evalTrunc]
    have h1 : ∑ p ∈ Finset.range M, evalTerm (mulCoeff a b) p z =
        ∑ p ∈ Finset.range M, ∑ n ∈ Finset.range (p + 1), evalTerm a n z * evalTerm b (p - n) z :=
      Finset.sum_congr rfl fun p _ => evalTerm_mulCoeff ha0 hb0 p z
    rw [h1]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ => (⟨x.2, x.1 - x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
      omega
    · intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_sigma, Finset.mem_range] at hx₁ hx₂
      have h1' : x₁.2 = x₂.2 := congr_arg Sigma.fst heq
      have h2' : x₁.1 - x₁.2 = x₂.1 - x₂.2 := by simpa using congr_arg Sigma.snd heq
      exact Sigma.ext (by omega) (heq_of_eq h1')
    · intro y hy
      simp only [Finset.mem_sigma, Finset.mem_range] at hy
      refine ⟨⟨y.1 + y.2, y.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]; omega
      · ext <;> simp
    · intro x _
      rfl
  rw [hsplit]
  have hsub : (∑ n ∈ Finset.range M, evalTerm a n z * (g z - evalTrunc b (M - n) z)) =
      evalTrunc a M z * g z - ∑ n ∈ Finset.range M, evalTerm a n z * evalTrunc b (M - n) z := by
    dsimp only [evalTrunc]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hsub]; ring

/-- **Product Closure of `HasGev1Exp`**: if `f` and `g` have Gevrey-1 log-power expansions on `S`,
then `f * g` has Gevrey-1 log-power expansion `mulCoeff a b` on `S`. -/
theorem hasGev1Exp_mul {S : Set ℂ} (hS : ∀ z ∈ S, 1 ≤ ‖z‖) {f g : ℂ → ℂ} {a b : LogCoeff}
    (hf : HasGev1Exp S f a) (hg : HasGev1Exp S g b) :
    HasGev1Exp S (fun z => f z * g z) (mulCoeff a b) := by
  rcases hf with ⟨ha0, Ca, hCa, Aa, hAa, ha_coeff, ha_rem⟩
  rcases hg with ⟨hb0, Cb, hCb, Ab, hAb, hb_coeff, hb_rem⟩
  let A0 : ℝ := max Aa Ab
  have hA0 : 1 ≤ A0 := hAa.trans (le_max_left _ _)
  have hAa0 : Aa ≤ A0 := le_max_left _ _
  have hAb0 : Ab ≤ A0 := le_max_right _ _
  -- First prove the coefficient bound for `mulCoeff a b` with base `2 * A0`
  have hmul_zero : ∀ N K, N < K → mulCoeff a b N K = 0 := by
    intro N K hNK
    dsimp only [mulCoeff]
    refine Finset.sum_eq_zero fun n hn => Finset.sum_eq_zero fun k hk => ?_
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hkn : n < k
    · rw [ha0 n k hkn, zero_mul]
    · have hgt : N - n < K - k := by omega
      rw [hb0 (N - n) (K - k) hgt, mul_zero]
  have hmul_coeff : ∀ N K, K ≤ N →
      ‖mulCoeff a b N K‖ ≤ (Ca * Cb) * (2 * A0) ^ N * (N.factorial : ℝ) / (K.factorial : ℝ) := by
    intro N K hKN
    dsimp only [mulCoeff]
    have hstep1 : ‖∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (K + 1), a n k * b (N - n) (K - k)‖ ≤
        ∑ n ∈ Finset.range (N + 1),
          (Ca * Cb * A0 ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      let F := (Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n)
      have hfilt : (∑ k ∈ Finset.range (K + 1), a n k * b (N - n) (K - k)) =
          ∑ k ∈ F, a n k * b (N - n) (K - k) := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun k => k ≤ n ∧ K - k ≤ N - n) (Finset.range (K + 1)))]
        intro k hk hnot
        simp only [Finset.mem_filter, not_and, not_le] at hnot
        by_cases hkn : k ≤ n
        · have hgt := hnot hk hkn
          rw [hb0 (N - n) (K - k) hgt, mul_zero]
        · rw [ha0 n k (by omega), zero_mul]
      rw [hfilt]
      calc ‖∑ k ∈ F, a n k * b (N - n) (K - k)‖
          ≤ ∑ k ∈ F, ‖a n k‖ * ‖b (N - n) (K - k)‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by rw [norm_mul])
        _ ≤ ∑ k ∈ F,
              (Ca * A0 ^ n * ((n.factorial : ℝ) / (k.factorial : ℝ))) *
                (Cb * A0 ^ (N - n) * (((N - n).factorial : ℝ) / ((K - k).factorial : ℝ))) := by
            refine Finset.sum_le_sum fun k hk => ?_
            simp only [F, Finset.mem_filter, Finset.mem_range] at hk
            have h1 : ‖a n k‖ ≤ Ca * A0 ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) :=
              (ha_coeff n k hk.2.1).trans (by
                have : Aa ^ n ≤ A0 ^ n := pow_le_pow_left₀ (by positivity) hAa0 n
                gcongr)
            have h2 : ‖b (N - n) (K - k)‖ ≤
                Cb * A0 ^ (N - n) * ((N - n).factorial : ℝ) / ((K - k).factorial : ℝ) :=
              (hb_coeff (N - n) (K - k) hk.2.2).trans (by
                have : Ab ^ (N - n) ≤ A0 ^ (N - n) := pow_le_pow_left₀ (by positivity) hAb0 (N - n)
                gcongr)
            have h1' : ‖a n k‖ ≤ Ca * A0 ^ n * ((n.factorial : ℝ) / (k.factorial : ℝ)) := by
              simpa [mul_div_assoc] using h1
            have h2' : ‖b (N - n) (K - k)‖ ≤
                Cb * A0 ^ (N - n) * (((N - n).factorial : ℝ) / ((K - k).factorial : ℝ)) := by
              simpa [mul_div_assoc] using h2
            exact mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
        _ = (Ca * Cb * A0 ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) *
              ((∑ k ∈ F, (K.choose k : ℝ)) / (N.choose n : ℝ)) := by
            rw [Finset.sum_div, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k hk => ?_
            simp only [F, Finset.mem_filter, Finset.mem_range] at hk
            have hkK : k ≤ K := Nat.lt_succ_iff.mp hk.1
            have hpow : A0 ^ n * A0 ^ (N - n) = A0 ^ N := by
              rw [← pow_add, Nat.add_sub_of_le hnN]
            have hfd := fact_div_mul_fact_div hnN hkK
            calc Ca * A0 ^ n * ((n.factorial : ℝ) / (k.factorial : ℝ)) *
                  (Cb * A0 ^ (N - n) * (((N - n).factorial : ℝ) / ((K - k).factorial : ℝ)))
                = (Ca * Cb * (A0 ^ n * A0 ^ (N - n))) *
                    (((n.factorial : ℝ) / (k.factorial : ℝ)) *
                      (((N - n).factorial : ℝ) / ((K - k).factorial : ℝ))) := by ring
              _ = Ca * Cb * A0 ^ N *
                    (((N.factorial : ℝ) / (K.factorial : ℝ)) * ((K.choose k : ℝ) / (N.choose n : ℝ))) := by
                  rw [hpow, hfd]
              _ = Ca * Cb * A0 ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ)) *
                    ((K.choose k : ℝ) / (N.choose n : ℝ)) := by ring
        _ ≤ Ca * Cb * A0 ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ)) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [div_le_one (by exact_mod_cast Nat.choose_pos hnN)]
            exact_mod_cast sum_choose_le_choose hnN hKN
        _ = Ca * Cb * A0 ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ)) := mul_one _
    calc ‖∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (K + 1), a n k * b (N - n) (K - k)‖
        ≤ (N + 1 : ℝ) * (Ca * Cb * A0 ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) := by
          simpa [Finset.sum_const, nsmul_eq_mul] using hstep1
      _ ≤ 2 ^ N * (Ca * Cb * A0 ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_right (nat_succ_le_two_pow N) (by positivity)
      _ = (Ca * Cb) * (2 * A0) ^ N * (N.factorial : ℝ) / (K.factorial : ℝ) := by
          rw [mul_pow]; ring
  -- Now prove the remainder bound using `evalTrunc_mul_rem` at `M = N + 1`!
  let C_rem : ℝ := Ca * Cb * ((4 * Real.exp Real.pi + 1) * A0 + Real.exp Real.pi)
  let A_fin : ℝ := 2 * A0
  have hC_rem : 0 < C_rem := by positivity
  have hA_fin : 1 ≤ A_fin := by dsimp [A_fin]; linarith
  refine ⟨hmul_zero, C_rem, hC_rem, A_fin, hA_fin, ?_, ?_⟩
  · intro N K hKN
    have hCC : Ca * Cb ≤ C_rem := by
      dsimp only [C_rem]
      have h1 : (1 : ℝ) ≤ (4 * Real.exp Real.pi + 1) * A0 + Real.exp Real.pi := by
        have : 1 ≤ Real.exp Real.pi := Real.one_le_exp Real.pi_pos.le
        nlinarith
      nlinarith [mul_pos hCa hCb]
    exact (hmul_coeff N K hKN).trans (by gcongr)
  · intro N z hz
    have hz1 : 1 ≤ ‖z‖ := hS z hz
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz1
    have hz_ne : z ≠ 0 := norm_pos_iff.mp hz_pos
    have hg0 : ‖g z‖ ≤ Cb * ‖z‖ := by
      have h := hb_rem 0 z hz
      simpa [evalTrunc] using h
    -- Apply `evalTrunc_mul_rem` at `M = N + 1`
    have hrem1 := evalTrunc_mul_rem ha0 hb0 f g (N + 1) z
    have htrunc_succ : evalTrunc (mulCoeff a b) (N + 1) z =
        evalTrunc (mulCoeff a b) N z + evalTerm (mulCoeff a b) N z := by
      simp [evalTrunc, Finset.sum_range_succ]
    have hsplit : f z * g z - evalTrunc (mulCoeff a b) N z =
        (f z * g z - evalTrunc (mulCoeff a b) (N + 1) z) + evalTerm (mulCoeff a b) N z := by
      rw [htrunc_succ]; ring
    rw [hsplit, hrem1]
    -- Bound the sum term at `M = N + 1`
    have hsum_b : ‖∑ n ∈ Finset.range (N + 1), evalTerm a n z * (g z - evalTrunc b (N + 1 - n) z)‖ ≤
        4 * Ca * Cb * Real.exp Real.pi * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N := by
      calc ‖∑ n ∈ Finset.range (N + 1), evalTerm a n z * (g z - evalTrunc b (N + 1 - n) z)‖
          ≤ ∑ n ∈ Finset.range (N + 1), ‖evalTerm a n z‖ * ‖g z - evalTrunc b (N + 1 - n) z‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => by rw [norm_mul])
        _ ≤ ∑ n ∈ Finset.range (N + 1),
              (Ca * Real.exp Real.pi * ‖z‖ * A0 ^ n * (n.factorial : ℝ) / ‖z‖ ^ n) *
                (Cb * ‖z‖ * A0 ^ (N + 1 - n) * ((N + 1 - n).factorial : ℝ) / ‖z‖ ^ (N + 1 - n)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have ht := norm_evalTerm_le (C := Ca) (A := A0) hCa.le (by positivity)
              (fun k hkn => (ha_coeff n k hkn).trans (by gcongr)) hz1
            have hr : ‖g z - evalTrunc b (N + 1 - n) z‖ ≤
                Cb * ‖z‖ * A0 ^ (N + 1 - n) * ((N + 1 - n).factorial : ℝ) / ‖z‖ ^ (N + 1 - n) :=
              (hb_rem (N + 1 - n) z hz).trans (by gcongr)
            exact mul_le_mul ht hr (norm_nonneg _) (by positivity)
        _ = (Ca * Cb * Real.exp Real.pi * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N) *
              ∑ n ∈ Finset.range (N + 1), (1 : ℝ) / ((N + 1).choose n : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n hn => ?_
            have hnle : n ≤ N + 1 := Nat.le_of_lt (Finset.mem_range.mp hn)
            have hpowA : A0 ^ n * A0 ^ (N + 1 - n) = A0 ^ (N + 1) := by
              rw [← pow_add, Nat.add_sub_of_le hnle]
            have hpowz : ‖z‖ ^ n * ‖z‖ ^ (N + 1 - n) = ‖z‖ ^ N * ‖z‖ := by
              rw [← pow_add, Nat.add_sub_of_le hnle, pow_succ]
            have hch : ((N + 1).choose n : ℝ) * (n.factorial : ℝ) * ((N + 1 - n).factorial : ℝ) =
                ((N + 1).factorial : ℝ) := by
              exact_mod_cast Nat.choose_mul_factorial_mul_factorial hnle
            have hch_ne : ((N + 1).choose n : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.choose_pos hnle).ne'
            rw [div_mul_div_comm, hpowz]
            have hzn : ‖z‖ ^ N ≠ 0 := (pow_pos hz_pos N).ne'
            have h1 : (n.factorial : ℝ) * ((N + 1 - n).factorial : ℝ) =
                ((N + 1).factorial : ℝ) / ((N + 1).choose n : ℝ) := by
              field_simp [hch_ne]; linarith
            calc Ca * Real.exp Real.pi * ‖z‖ * A0 ^ n * (n.factorial : ℝ) *
                  (Cb * ‖z‖ * A0 ^ (N + 1 - n) * ((N + 1 - n).factorial : ℝ)) / (‖z‖ ^ N * ‖z‖)
                = Ca * Cb * Real.exp Real.pi * ‖z‖ * (A0 ^ n * A0 ^ (N + 1 - n)) *
                    ((n.factorial : ℝ) * ((N + 1 - n).factorial : ℝ)) * ‖z‖ / (‖z‖ ^ N * ‖z‖) := by ring
              _ = Ca * Cb * Real.exp Real.pi * ‖z‖ * A0 ^ (N + 1) *
                    (((N + 1).factorial : ℝ) / ((N + 1).choose n : ℝ)) / ‖z‖ ^ N := by
                  rw [hpowA, h1, mul_div_mul_right _ _ hz_pos.ne']
              _ = Ca * Cb * Real.exp Real.pi * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N *
                    (1 / ((N + 1).choose n : ℝ)) := by ring
        _ ≤ (Ca * Cb * Real.exp Real.pi * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N) * 4 :=
            mul_le_mul_of_nonneg_left (sum_inv_choose_le (N + 1)) (by positivity)
        _ = 4 * Ca * Cb * Real.exp Real.pi * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N := by ring
    -- Bound the `(f - trunc a (N+1)) * g` term
    have htail_b : ‖(f z - evalTrunc a (N + 1) z) * g z‖ ≤
        Ca * Cb * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N := by
      rw [norm_mul]
      have hf1 : ‖f z - evalTrunc a (N + 1) z‖ ≤
          Ca * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ (N + 1) :=
        (ha_rem (N + 1) z hz).trans (by gcongr)
      calc ‖f z - evalTrunc a (N + 1) z‖ * ‖g z‖
          ≤ (Ca * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ (N + 1)) * (Cb * ‖z‖) :=
            mul_le_mul hf1 hg0 (norm_nonneg _) (by positivity)
        _ = Ca * Cb * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N := by
            rw [pow_succ ‖z‖]; field_simp [hz_pos.ne']
    -- Bound the `N`-th term `evalTerm (mulCoeff a b) N z`
    have hterm_b : ‖evalTerm (mulCoeff a b) N z‖ ≤
        (Ca * Cb) * Real.exp Real.pi * ‖z‖ * A_fin ^ N * (N.factorial : ℝ) / ‖z‖ ^ N :=
      norm_evalTerm_le (mul_pos hCa hCb).le (by positivity) (hmul_coeff N) hz1
    -- Combine using `(N+1)! ≤ 2^N N!`
    have hfac : A0 ^ (N + 1) * ((N + 1).factorial : ℝ) ≤ A0 * A_fin ^ N * (N.factorial : ℝ) := by
      calc A0 ^ (N + 1) * ((N + 1).factorial : ℝ)
          ≤ A0 ^ (N + 1) * (2 ^ N * (N.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left (factorial_succ_le_two_pow N) (by positivity)
        _ = A0 * (2 * A0) ^ N * (N.factorial : ℝ) := by rw [pow_succ, mul_pow]; ring
    have hcomb1 : ‖(∑ n ∈ Finset.range (N + 1), evalTerm a n z * (g z - evalTrunc b (N + 1 - n) z)) +
          (f z - evalTrunc a (N + 1) z) * g z‖ ≤
        Ca * Cb * (4 * Real.exp Real.pi + 1) * A0 * ‖z‖ * A_fin ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by
      calc _ ≤ ‖∑ n ∈ Finset.range (N + 1), evalTerm a n z * (g z - evalTrunc b (N + 1 - n) z)‖ +
              ‖(f z - evalTrunc a (N + 1) z) * g z‖ := norm_add_le _ _
        _ ≤ 4 * Ca * Cb * Real.exp Real.pi * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N +
              Ca * Cb * ‖z‖ * A0 ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ N :=
            add_le_add hsum_b htail_b
        _ = Ca * Cb * (4 * Real.exp Real.pi + 1) * ‖z‖ * (A0 ^ (N + 1) * ((N + 1).factorial : ℝ)) / ‖z‖ ^ N := by
            ring
        _ ≤ Ca * Cb * (4 * Real.exp Real.pi + 1) * ‖z‖ * (A0 * A_fin ^ N * (N.factorial : ℝ)) / ‖z‖ ^ N := by
            gcongr
        _ = Ca * Cb * (4 * Real.exp Real.pi + 1) * A0 * ‖z‖ * A_fin ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by
            ring
    calc ‖((∑ n ∈ Finset.range (N + 1), evalTerm a n z * (g z - evalTrunc b (N + 1 - n) z)) +
            (f z - evalTrunc a (N + 1) z) * g z) + evalTerm (mulCoeff a b) N z‖
        ≤ ‖(∑ n ∈ Finset.range (N + 1), evalTerm a n z * (g z - evalTrunc b (N + 1 - n) z)) +
            (f z - evalTrunc a (N + 1) z) * g z‖ + ‖evalTerm (mulCoeff a b) N z‖ := norm_add_le _ _
      _ ≤ Ca * Cb * (4 * Real.exp Real.pi + 1) * A0 * ‖z‖ * A_fin ^ N * (N.factorial : ℝ) / ‖z‖ ^ N +
            (Ca * Cb) * Real.exp Real.pi * ‖z‖ * A_fin ^ N * (N.factorial : ℝ) / ‖z‖ ^ N :=
          add_le_add hcomb1 hterm_b
      _ = C_rem * ‖z‖ * A_fin ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by dsimp [C_rem]; ring

/-- Power closure of `HasGev1Exp`. -/
lemma hasGev1Exp_pow {S : Set ℂ} (hS : ∀ z ∈ S, 1 ≤ ‖z‖) {f : ℂ → ℂ} {a : LogCoeff}
    (hf : HasGev1Exp S f a) (m : ℕ) :
    ∃ b : LogCoeff, HasGev1Exp S (fun z => f z ^ m) b := by
  induction m with
  | zero =>
    exact ⟨constCoeff 1, by simpa using hasGev1Exp_const hS 1⟩
  | succ k ih =>
    rcases ih with ⟨b, hb⟩
    refine ⟨mulCoeff b a, ?_⟩
    have hmul := hasGev1Exp_mul hS hb hf
    simpa [pow_succ] using hmul

/-- Multivariate polynomial closure of `HasGev1Exp`. -/
theorem hasGev1Exp_mvPolynomial {S : Set ℂ} (hS : ∀ z ∈ S, 1 ≤ ‖z‖) {m : ℕ}
    {g : Fin m → ℂ → ℂ} (hg : ∀ i : Fin m, ∃ a : LogCoeff, HasGev1Exp S (g i) a)
    (P : MvPolynomial (Fin m) ℂ) :
    ∃ a : LogCoeff, HasGev1Exp S (fun z => MvPolynomial.eval (fun i => g i z) P) a := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨constCoeff c, ?_⟩
    simpa [MvPolynomial.eval_C] using hasGev1Exp_const hS c
  | add p q ihp ihq =>
    rcases ihp with ⟨ap, hap⟩
    rcases ihq with ⟨aq, haq⟩
    refine ⟨addCoeff ap aq, ?_⟩
    have h := hasGev1Exp_add hap haq
    simpa [map_add] using h
  | mul_X p i ihp =>
    rcases ihp with ⟨ap, hap⟩
    rcases hg i with ⟨ai, hai⟩
    refine ⟨mulCoeff ap ai, ?_⟩
    have h := hasGev1Exp_mul hS hap hai
    simpa [map_mul, MvPolynomial.eval_X] using h

/-! #### 1c. Cauchy Derivative Transfer for `HasGev1Exp` -/

/-- Exact derivative of `(log z)^k / z^n` on `Complex.slitPlane`. -/
lemma hasDerivAt_log_pow_div_pow {z : ℂ} (hz : z ∈ Complex.slitPlane) (n k : ℕ) :
    HasDerivAt (fun w : ℂ => Complex.log w ^ k / w ^ n)
      (((k : ℂ) * (if k = 0 then 0 else Complex.log z ^ (k - 1)) -
        (n : ℂ) * Complex.log z ^ k) / z ^ (n + 1)) z := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hlog : HasDerivAt Complex.log z⁻¹ z := Complex.hasDerivAt_log hz
  have hnum : HasDerivAt (fun w : ℂ => Complex.log w ^ k)
      ((k : ℂ) * (if k = 0 then 0 else Complex.log z ^ (k - 1)) * z⁻¹) z := by
    cases k with
    | zero =>
      simpa using hasDerivAt_const z (1 : ℂ)
    | succ j =>
      have h := hlog.fun_pow (j + 1)
      simpa [Nat.succ_ne_zero] using h
  have hden : HasDerivAt (fun w : ℂ => w ^ n) ((n : ℂ) * z ^ (n - 1)) z := by
    cases n with
    | zero => simpa using hasDerivAt_const z (1 : ℂ)
    | succ m => simpa using (hasDerivAt_id z).fun_pow (m + 1)
  have hq := hnum.div hden (pow_ne_zero n hz0)
  refine hq.congr_deriv ?_
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero, pow_zero, mul_one, one_pow, div_one, zero_add,
      pow_one]
    ring
  | succ m =>
    have hzn : z ^ (m + 1) ≠ 0 := pow_ne_zero _ hz0
    have hzm : z ^ m ≠ 0 := pow_ne_zero _ hz0
    simp only [Nat.add_sub_cancel]
    field_simp [hz0, hzn, hzm]
    ring

/-- Exact derivative of `evalTrunc a N` on `Complex.slitPlane`: equals `evalTrunc (derivCoeff a) (N + 1)`. -/
lemma hasDerivAt_evalTrunc {a : LogCoeff} (ha0 : ∀ n k, n < k → a n k = 0)
    (N : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (evalTrunc a N) (evalTrunc (derivCoeff a) (N + 1) z) z := by
  have hterm : ∀ n : ℕ,
      HasDerivAt (evalTerm a n) (evalTerm (derivCoeff a) (n + 1) z) z := by
    intro n
    have hsum : HasDerivAt
        (fun w : ℂ => ∑ k ∈ Finset.range (n + 1), a n k * (Complex.log w ^ k / w ^ n))
        (∑ k ∈ Finset.range (n + 1), a n k *
          (((k : ℂ) * (if k = 0 then 0 else Complex.log z ^ (k - 1)) -
            (n : ℂ) * Complex.log z ^ k) / z ^ (n + 1))) z :=
      HasDerivAt.fun_sum fun k _ => (hasDerivAt_log_pow_div_pow hz n k).const_mul (a n k)
    have hfun : (fun w : ℂ => ∑ k ∈ Finset.range (n + 1), a n k * (Complex.log w ^ k / w ^ n)) =
        evalTerm a n := by
      ext w
      dsimp only [evalTerm]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hfun] at hsum
    refine hsum.congr_deriv ?_
    dsimp only [evalTerm, derivCoeff]
    rw [Finset.sum_div]
    have hsplit : (∑ k ∈ Finset.range (n + 1), a n k *
        (((k : ℂ) * (if k = 0 then 0 else Complex.log z ^ (k - 1)) -
          (n : ℂ) * Complex.log z ^ k) / z ^ (n + 1))) =
        (∑ k ∈ Finset.range (n + 1),
          (a n k * (k : ℂ) * (if k = 0 then 0 else Complex.log z ^ (k - 1))) / z ^ (n + 1)) -
        (∑ k ∈ Finset.range (n + 1), (a n k * (n : ℂ) * Complex.log z ^ k) / z ^ (n + 1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit]
    have h1 : (∑ k ∈ Finset.range (n + 1),
        (a n k * (k : ℂ) * (if k = 0 then 0 else Complex.log z ^ (k - 1))) / z ^ (n + 1)) =
        ∑ k ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℂ) * a n (k + 1) * Complex.log z ^ k) / z ^ (n + 1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_div, add_zero, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]
      rw [Finset.sum_range_succ (n := n + 1), Finset.sum_range_succ (n := n)]
      have htop1 : a n (n + 1) = 0 := ha0 n (n + 1) (Nat.lt_succ_self n)
      have htop2 : a n (n + 2) = 0 := ha0 n (n + 2) (by omega)
      simp only [htop1, htop2, mul_zero, zero_mul, zero_div, add_zero]
      refine Finset.sum_congr rfl fun k _ => by ring
    have h2 : (∑ k ∈ Finset.range (n + 1), (a n k * (n : ℂ) * Complex.log z ^ k) / z ^ (n + 1)) =
        ∑ k ∈ Finset.range (n + 2), ((n : ℂ) * a n k * Complex.log z ^ k) / z ^ (n + 1) := by
      rw [Finset.sum_range_succ (n := n + 1)]
      have htop : a n (n + 1) = 0 := ha0 n (n + 1) (Nat.lt_succ_self n)
      simp only [htop, mul_zero, zero_mul, zero_div, add_zero]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have htot : HasDerivAt (fun w => ∑ n ∈ Finset.range N, evalTerm a n w)
      (∑ n ∈ Finset.range N, evalTerm (derivCoeff a) (n + 1) z) z :=
    HasDerivAt.fun_sum fun n (_ : n ∈ Finset.range N) => hterm n
  have hsum_eq : (∑ n ∈ Finset.range N, evalTerm (derivCoeff a) (n + 1) z) =
      evalTrunc (derivCoeff a) (N + 1) z := by
    dsimp only [evalTrunc]
    rw [Finset.sum_range_succ']
    have h0 : evalTerm (derivCoeff a) 0 z = 0 := by simp [evalTerm, derivCoeff]
    rw [h0, add_zero]
  rwa [hsum_eq] at htot

/-- Exact `j`-th iterated derivative of `evalTrunc a N` on `Complex.slitPlane`. -/
lemma iteratedDeriv_evalTrunc {a : LogCoeff} (ha0 : ∀ n k, n < k → a n k = 0) :
    ∀ j N : ℕ, ∀ z ∈ Complex.slitPlane,
      iteratedDeriv j (evalTrunc a N) z = evalTrunc (derivCoeff^[j] a) (N + j) z := by
  have hderiv0 : ∀ b : LogCoeff, (∀ n k, n < k → b n k = 0) →
      ∀ n k, n < k → derivCoeff b n k = 0 := by
    intro b hb0 n k hnk
    cases n with
    | zero => rfl
    | succ m =>
      dsimp only [derivCoeff]
      rw [hb0 m (k + 1) (by omega), hb0 m k (by omega)]
      ring
  have hiter0 : ∀ j : ℕ, ∀ n k, n < k → (derivCoeff^[j] a) n k = 0 := by
    intro j
    induction j with
    | zero => exact ha0
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hderiv0 _ ih
  intro j
  induction j with
  | zero =>
    intro N z _
    simp
  | succ j ih =>
    intro N z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (evalTrunc a N) =ᶠ[𝓝 z] evalTrunc (derivCoeff^[j] a) (N + j) := by
      filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih N w hw
    rw [hev.deriv_eq, (hasDerivAt_evalTrunc (hiter0 j) (N + j) hz).deriv,
      Function.iterate_succ_apply', Nat.add_assoc]

/-- Coefficient bound preservation under `derivCoeff`. -/
lemma derivCoeff_bounds {a : LogCoeff} {C A : ℝ} (hC : 0 < C) (hA : 1 ≤ A)
    (ha0 : ∀ n k, n < k → a n k = 0)
    (ha : ∀ n k, k ≤ n → ‖a n k‖ ≤ C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) :
    (∀ n k, n < k → derivCoeff a n k = 0) ∧
    (∀ n k, k ≤ n → ‖derivCoeff a n k‖ ≤ (2 * C) * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) := by
  refine ⟨fun n k hnk => ?_, fun n k hkn => ?_⟩
  · cases n with
    | zero => rfl
    | succ m =>
      dsimp only [derivCoeff]
      rw [ha0 m (k + 1) (by omega), ha0 m k (by omega)]
      ring
  · cases n with
    | zero =>
      simp only [derivCoeff, norm_zero]
      positivity
    | succ m =>
      dsimp only [derivCoeff]
      have h1 : ‖((k + 1 : ℕ) : ℂ) * a m (k + 1)‖ ≤
          C * A ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) := by
        by_cases hkm : k + 1 ≤ m
        · rw [norm_mul, Complex.norm_natCast]
          have hb := ha m (k + 1) hkm
          have hfac : ((k + 1).factorial : ℝ) = (k + 1 : ℝ) * (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_succ k
          have hmfac : (m.factorial : ℝ) ≤ ((m + 1).factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (Nat.le_succ m)
          have hApow : A ^ m ≤ A ^ (m + 1) := by
            rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < A by linarith) m]
          calc ((k + 1 : ℕ) : ℝ) * ‖a m (k + 1)‖
              ≤ ((k + 1 : ℕ) : ℝ) * (C * A ^ m * (m.factorial : ℝ) / ((k + 1).factorial : ℝ)) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = C * A ^ m * (m.factorial : ℝ) / (k.factorial : ℝ) := by
                rw [hfac]; push_cast; field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
            _ ≤ C * A ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) := by gcongr
        · rw [ha0 m (k + 1) (by omega), mul_zero, norm_zero]; positivity
      have h2 : ‖(m : ℂ) * a m k‖ ≤
          C * A ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) := by
        by_cases hkm : k ≤ m
        · rw [norm_mul, Complex.norm_natCast]
          have hb := ha m k hkm
          have hmfac : (m : ℝ) * (m.factorial : ℝ) ≤ ((m + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul]; push_cast
            nlinarith [show (0 : ℝ) ≤ (m.factorial : ℝ) by positivity]
          have hApow : A ^ m ≤ A ^ (m + 1) := by
            rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < A by linarith) m]
          calc (m : ℝ) * ‖a m k‖
              ≤ (m : ℝ) * (C * A ^ m * (m.factorial : ℝ) / (k.factorial : ℝ)) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = C * A ^ m * ((m : ℝ) * (m.factorial : ℝ)) / (k.factorial : ℝ) := by ring
            _ ≤ C * A ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) := by gcongr
        · rw [ha0 m k (by omega), mul_zero, norm_zero]; positivity
      calc ‖((k + 1 : ℕ) : ℂ) * a m (k + 1) - (m : ℂ) * a m k‖
          ≤ ‖((k + 1 : ℕ) : ℂ) * a m (k + 1)‖ + ‖(m : ℂ) * a m k‖ := norm_sub_le _ _
        _ ≤ C * A ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) +
              C * A ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) := add_le_add h1 h2
        _ = (2 * C) * A ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) := by ring

/-- **Cauchy `iteratedDeriv` Transfer for `HasGev1Exp`**:
If `f` is holomorphic on an open set `U₀ ⊇ S₀`, `S₀ ⊆ Complex.slitPlane`, `HasGev1Exp S₀ f a`,
and for every `z ∈ S`, `closedBall z (ρ * ‖z‖) ⊆ S₀` (with `0 < ρ < 1/2`), then for EVERY `j : ℕ`,
`HasGev1Exp S (iteratedDeriv j f) (derivCoeff^[j] a)`. -/
theorem hasGev1Exp_iteratedDeriv {S S₀ U₀ : Set ℂ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ_half : ρ < 1 / 2)
    (hU₀ : IsOpen U₀) (hS₀_U₀ : S₀ ⊆ U₀) (hS₀_slit : S₀ ⊆ Complex.slitPlane)
    (hS_norm : ∀ z ∈ S, 1 ≤ ‖z‖)
    (hball : ∀ z ∈ S, Metric.closedBall z (ρ * ‖z‖) ⊆ S₀)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U₀) {a : LogCoeff} (hgev : HasGev1Exp S₀ f a) (j : ℕ) :
    HasGev1Exp S (iteratedDeriv j f) (derivCoeff^[j] a) := by
  rcases hgev with ⟨ha0, C, hC, A, hA, ha_coeff, ha_rem⟩
  -- Coefficient bounds for `derivCoeff^[j] a`
  have hcoeff_j : ∀ m : ℕ,
      (∀ n k, n < k → (derivCoeff^[m] a) n k = 0) ∧
      (∀ n k, k ≤ n → ‖(derivCoeff^[m] a) n k‖ ≤
        (2 ^ m * C) * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) := by
    intro m
    induction m with
    | zero => exact ⟨ha0, by simpa using ha_coeff⟩
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      have h := derivCoeff_bounds (C := 2 ^ m * C) (by positivity) hA ih.1 ih.2
      refine ⟨h.1, fun n k hkn => ?_⟩
      simpa [pow_succ', mul_assoc] using h.2 n k hkn
  obtain ⟨hj0, hj_coeff⟩ := hcoeff_j j
  -- For `N < j`, `evalTrunc (derivCoeff^[j] a) N = 0` because first `j` degrees vanish!
  have hlow_zero : ∀ m : ℕ, ∀ n < m, ∀ k, (derivCoeff^[m] a) n k = 0 := by
    intro m
    induction m with
    | zero => intro n hn; omega
    | succ m ih =>
      intro n hn k
      rw [Function.iterate_succ_apply']
      cases n with
      | zero => rfl
      | succ d =>
        dsimp only [derivCoeff]
        rw [ih d (by omega) (k + 1), ih d (by omega) k]
        ring
  -- Constants for the Cauchy bound
  let B : ℝ := A / (1 - ρ)
  have h1mρ : 0 < 1 - ρ := by linarith
  have hB1 : 1 ≤ B := by
    dsimp only [B]; rw [le_div_iff₀ h1mρ]; linarith
  have hAB : A ≤ B := by
    dsimp only [B]; rw [le_div_iff₀ h1mρ]; nlinarith
  let C_fin : ℝ := max (2 ^ j * C) ((j.factorial : ℝ) / ρ ^ j * C * (1 + ρ))
  have hC_fin : 0 < C_fin := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨hj0, C_fin, hC_fin, B, hB1, ?_, ?_⟩
  · intro n k hkn
    exact (hj_coeff n k hkn).trans (by
      have h1 : 2 ^ j * C ≤ C_fin := le_max_left _ _
      gcongr)
  · intro N z hz
    have hz1 : 1 ≤ ‖z‖ := hS_norm z hz
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz1
    have hrad : 0 < ρ * ‖z‖ := mul_pos hρ0 hz_pos
    have hcb_sub : Metric.closedBall z (ρ * ‖z‖) ⊆ S₀ := hball z hz
    have hball_U₀ : Metric.closedBall z (ρ * ‖z‖) ⊆ U₀ := hcb_sub.trans hS₀_U₀
    have hball_slit : Metric.closedBall z (ρ * ‖z‖) ⊆ Complex.slitPlane := hcb_sub.trans hS₀_slit
    have hz_slit : z ∈ Complex.slitPlane := hball_slit (Metric.mem_closedBall_self hrad.le)
    -- Choose truncation index `M = N - j` (so `M + j ≥ N`, and if `N < j` then `M = 0` and trunc is `0`)
    let M : ℕ := N - j
    have heval_eq : evalTrunc (derivCoeff^[j] a) N z = evalTrunc (derivCoeff^[j] a) (M + j) z := by
      by_cases hjN : j ≤ N
      · have hMj : M + j = N := Nat.sub_add_cancel hjN
        rw [hMj]
      · have hM0 : M = 0 := Nat.sub_eq_zero_of_le (by omega)
        rw [hM0, zero_add]
        have hzero : ∀ L ≤ j, evalTrunc (derivCoeff^[j] a) L z = 0 := by
          intro L hLj
          dsimp only [evalTrunc]
          refine Finset.sum_eq_zero fun n hn => ?_
          dsimp only [evalTerm]
          rw [Finset.sum_eq_zero fun k _ => by rw [hlow_zero j n (by
            have := Finset.mem_range.mp hn; omega) k, zero_mul], zero_div]
        rw [hzero N (by omega), hzero j le_rfl]
    rw [heval_eq, ← iteratedDeriv_evalTrunc ha0 j M z hz_slit]
    -- Apply Cauchy's iterated derivative estimate to `g(w) = f w - evalTrunc a M w` on `closedBall z (ρ ‖z‖)`
    let g : ℂ → ℂ := fun w => f w - evalTrunc a M w
    have hg_diffOn : DifferentiableOn ℂ g (Metric.closedBall z (ρ * ‖z‖)) := by
      have hf_cb : DifferentiableOn ℂ f (Metric.closedBall z (ρ * ‖z‖)) := hf.mono hball_U₀
      have hev_cb : DifferentiableOn ℂ (evalTrunc a M) (Metric.closedBall z (ρ * ‖z‖)) :=
        fun w hw => (hasDerivAt_evalTrunc ha0 M (hball_slit hw)).differentiableAt.differentiableWithinAt
      exact hf_cb.sub hev_cb
    have hg_dc : DiffContOnCl ℂ g (Metric.ball z (ρ * ‖z‖)) := by
      have hcl : closure (Metric.ball z (ρ * ‖z‖)) ⊆ Metric.closedBall z (ρ * ‖z‖) :=
        Metric.closure_ball_subset_closedBall
      exact ⟨hg_diffOn.mono Metric.ball_subset_closedBall,
        (hg_diffOn.continuousOn).mono hcl⟩
    have hf_cd : ContDiffAt ℂ j f z :=
      ((hf.analyticOnNhd hU₀ z (hball_U₀ (Metric.mem_closedBall_self hrad.le))).contDiffAt).of_le le_top
    have hev_cd : ContDiffAt ℂ j (evalTrunc a M) z := by
      have hd : DifferentiableOn ℂ (evalTrunc a M) Complex.slitPlane :=
        fun w hw => (hasDerivAt_evalTrunc ha0 M hw).differentiableAt.differentiableWithinAt
      exact ((hd.analyticOnNhd Complex.isOpen_slitPlane z hz_slit).contDiffAt).of_le le_top
    have hsub_id : iteratedDeriv j f z - iteratedDeriv j (evalTrunc a M) z = iteratedDeriv j g z :=
      (iteratedDeriv_sub hf_cd hev_cd).symm
    rw [hsub_id]
    -- Bound `‖g w‖` on `sphere z (ρ * ‖z‖)`
    let K_sph : ℝ := C * ((1 + ρ) * ‖z‖) * B ^ M * (M.factorial : ℝ) / ‖z‖ ^ M
    have hK_nn : 0 ≤ K_sph := by positivity
    have hbound_sph : ∀ w ∈ Metric.sphere z (ρ * ‖z‖), ‖g w‖ ≤ K_sph := by
      intro w hw
      have hw_cb : w ∈ Metric.closedBall z (ρ * ‖z‖) := Metric.sphere_subset_closedBall hw
      have hw_S₀ : w ∈ S₀ := hcb_sub hw_cb
      have hdist : ‖w - z‖ = ρ * ‖z‖ := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
      have hw_hi : ‖w‖ ≤ (1 + ρ) * ‖z‖ := by
        have htri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
        linarith
      have hw_lo : (1 - ρ) * ‖z‖ ≤ ‖w‖ := by
        have htri : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
          have := norm_add_le w (z - w)
          rw [norm_sub_rev] at this
          simpa using this
        linarith
      have hw_lo_pos : 0 < (1 - ρ) * ‖z‖ := mul_pos h1mρ hz_pos
      have hr := ha_rem M w hw_S₀
      calc ‖g w‖ ≤ C * ‖w‖ * A ^ M * (M.factorial : ℝ) / ‖w‖ ^ M := hr
        _ ≤ C * ((1 + ρ) * ‖z‖) * A ^ M * (M.factorial : ℝ) / ((1 - ρ) * ‖z‖) ^ M := by
            refine div_le_div₀ (by positivity) ?_ (pow_pos hw_lo_pos M)
              (pow_le_pow_left₀ hw_lo_pos.le hw_lo M)
            gcongr
        _ = K_sph := by
            dsimp only [K_sph, B]
            rw [mul_pow, div_pow]
            field_simp [h1mρ.ne', (pow_pos hz_pos M).ne']
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (n := j) (R := ρ * ‖z‖) (C := K_sph) hrad hg_dc hbound_sph
    -- Compare `(j! / (ρ ‖z‖)^j) * K_sph` with `C_fin * ‖z‖ * B^N * N! / ‖z‖^N`
    have hM_le_N : M ≤ N := Nat.sub_le N j
    have hMj_ge_N : N ≤ M + j := by dsimp [M]; omega
    have hB_pow : B ^ M ≤ B ^ N := pow_le_pow_right₀ hB1 hM_le_N
    have hfac_M : (M.factorial : ℝ) ≤ (N.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hM_le_N
    have hz_pow : ‖z‖ ^ N ≤ ‖z‖ ^ (M + j) := pow_le_pow_right₀ hz1 hMj_ge_N
    have hC_ge : (j.factorial : ℝ) / ρ ^ j * C * (1 + ρ) ≤ C_fin := le_max_right _ _
    calc ‖iteratedDeriv j g z‖
        ≤ (j.factorial : ℝ) * K_sph / (ρ * ‖z‖) ^ j := hcauchy
      _ = ((j.factorial : ℝ) / ρ ^ j * C * (1 + ρ)) * ‖z‖ * B ^ M * (M.factorial : ℝ) /
            ‖z‖ ^ (M + j) := by
          dsimp only [K_sph]
          rw [mul_pow, pow_add]
          field_simp [hρ0.ne', hz_pos.ne']
      _ ≤ C_fin * ‖z‖ * B ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by
          refine div_le_div₀ (by positivity) ?_ (pow_pos hz_pos N) hz_pow
          gcongr

/-! #### 1d. Flatness on a Positive Real Ray Forces Zero Coefficients & Watson Gevrey-1 Bound -/

/-- If a complex polynomial `P` satisfies `P(log u) → 0` as `u → +∞`, then `P = 0`. -/
lemma poly_eq_zero_of_tendsto_log_zero (P : Polynomial ℂ)
    (hlim : Tendsto (fun u : ℝ => P.eval (Real.log u : ℂ)) atTop (𝓝 0)) :
    P = 0 := by
  by_contra hP
  have hcomp : Tendsto (fun x : ℝ => P.eval (x : ℂ)) atTop (𝓝 0) := by
    have h := hlim.comp Real.tendsto_exp_atTop
    refine h.congr fun x => ?_
    simp [Real.log_exp]
  have hd : P.natDegree = 0 ∨ 0 < P.natDegree := Nat.eq_zero_or_pos P.natDegree
  rcases hd with hdeg0 | hdeg_pos
  · have hC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hconst : Tendsto (fun _ : ℝ => P.coeff 0) atTop (𝓝 0) := by
      refine hcomp.congr fun x => ?_
      conv_lhs => rw [hC]
      simp
    have h0 : P.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
    apply hP; rw [hC, h0, map_zero]
  · -- Divide `P(x)` by `x^{natDegree}`: tends to `leadingCoeff P ≠ 0`, contradiction!
    have hdeg_pos' : (0 : WithBot ℕ) < P.degree := by
      rw [Polynomial.degree_eq_natDegree hP]
      exact_mod_cast hdeg_pos
    have hnorm : Tendsto (fun x : ℝ => ‖P.eval (x : ℂ)‖) atTop atTop := by
      have h2 : Tendsto (fun x : ℝ => ‖(x : ℂ)‖) atTop atTop := by
        refine Filter.tendsto_atTop.mpr fun b => ?_
        filter_upwards [Filter.eventually_ge_atTop (max b 0)] with x hx
        rw [Complex.norm_real, Real.norm_of_nonneg ((le_max_right b 0).trans hx)]
        exact (le_max_left b 0).trans hx
      exact Polynomial.tendsto_norm_atTop P hdeg_pos' h2
    have hnorm0 : Tendsto (fun x : ℝ => ‖P.eval (x : ℂ)‖) atTop (𝓝 0) := by
      simpa using hcomp.norm
    have h1 := Filter.eventually_atTop.mp (hnorm.eventually (Filter.eventually_ge_atTop 1))
    have h2 := Filter.eventually_atTop.mp (hnorm0.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)))
    rcases h1 with ⟨X₁, hX₁⟩
    rcases h2 with ⟨X₂, hX₂⟩
    have ha := hX₁ (max X₁ X₂) (le_max_left _ _)
    have hb := hX₂ (max X₁ X₂) (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hb
    linarith

/-- **Ray Flatness Kills All Log-Power Coefficients**:
If `HasGev1Exp S f a`, `S` contains a real ray `[R, ∞)`, and `f` is flat to all inverse powers on `[U, ∞)`,
then `a n k = 0` for EVERY `n, k : ℕ`! -/
theorem coeff_eq_zero_of_ray_flat {S : Set ℂ} {R : ℝ} (hR : 1 ≤ R)
    (hray : ∀ u : ℝ, R ≤ u → (u : ℂ) ∈ S)
    {f : ℂ → ℂ} {a : LogCoeff} (hgev : HasGev1Exp S f a)
    (hflat : ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U, ‖f (u : ℂ)‖ ≤ C / u ^ N) :
    ∀ n k : ℕ, a n k = 0 := by
  rcases hgev with ⟨ha0, C, hC, A, hA, ha_coeff, ha_rem⟩
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    -- Build polynomial `P_n(L) = ∑_{k=0}^n a n k * L^k`
    let P : Polynomial ℂ := ∑ k ∈ Finset.range (n + 1), Polynomial.C (a n k) * Polynomial.X ^ k
    have hP_eval : ∀ u : ℝ, 0 < u →
        P.eval (Real.log u : ℂ) = (u : ℂ) ^ n * evalTerm a n (u : ℂ) := by
      intro u hu
      change Polynomial.aeval (Real.log u : ℂ) P = _
      dsimp only [P, evalTerm]
      rw [map_sum]
      have hlog : Complex.log (u : ℂ) = (Real.log u : ℂ) := (Complex.ofReal_log hu.le).symm
      rw [hlog, mul_div_cancel₀ _ (pow_ne_zero n (Complex.ofReal_ne_zero.mpr hu.ne'))]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp
    -- Show `P(log u) → 0` as `u → +∞` using `N = n + 2` in `ha_rem`!
    have hlim : Tendsto (fun u : ℝ => P.eval (Real.log u : ℂ)) atTop (𝓝 0) := by
      obtain ⟨Cf, hCf, Uf, hUf⟩ := hflat (n + 1)
      have hlog_pow : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      -- Even simpler: use `norm_evalTerm_le` for `evalTerm a (n+1) u`? Wait: that gives `u / u^{n+1}`,
      -- so we need `u * (log u)^{n+1} / u^{n+2}` — just use `N = n + 2` and bound `evalTerm a (n+1) u` directly!
      have hP1_tend : Tendsto (fun u : ℝ => (u : ℂ) ^ n * evalTerm a (n + 1) (u : ℂ)) atTop (𝓝 0) := by
        have hterm_lim : ∀ k ∈ Finset.range (n + 2),
            Tendsto (fun u : ℝ => a (n + 1) k * ((Real.log u : ℂ) ^ k / (u : ℂ))) atTop (𝓝 0) := by
          intro k _
          have hreal : Tendsto (fun u : ℝ => Real.log u ^ k / u) atTop (𝓝 0) := by
            simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
          have hC' : Tendsto (fun u : ℝ => ((Real.log u ^ k / u : ℝ) : ℂ)) atTop (𝓝 0) :=
            ((Complex.continuous_ofReal.tendsto 0).comp hreal).congr fun u => rfl
          have hC'' := hC'.const_mul (a (n + 1) k)
          rw [mul_zero] at hC''
          refine hC''.congr' ?_
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u _
          push_cast; rfl
        have hsum_lim : Tendsto (fun u : ℝ => ∑ k ∈ Finset.range (n + 2),
            a (n + 1) k * ((Real.log u : ℂ) ^ k / (u : ℂ))) atTop (𝓝 0) := by
          have haux : ∀ S' : Finset ℕ, (∀ k ∈ S', Tendsto (fun u : ℝ =>
              a (n + 1) k * ((Real.log u : ℂ) ^ k / (u : ℂ))) atTop (𝓝 0)) →
              Tendsto (fun u : ℝ => ∑ k ∈ S', a (n + 1) k * ((Real.log u : ℂ) ^ k / (u : ℂ))) atTop (𝓝 0) := by
            intro S'
            induction S' using Finset.induction_on with
            | empty => intro _; simp
            | insert k S' hk ih =>
              intro h
              have h1 := h k (Finset.mem_insert_self k S')
              have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
              simpa [Finset.sum_insert hk] using h1.add h2
          exact haux (Finset.range (n + 2)) hterm_lim
        refine hsum_lim.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u hu
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
        have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
        dsimp only [evalTerm]
        rw [(Complex.ofReal_log hu_pos.le).symm, mul_div_assoc', Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_succ]; field_simp [hu_ne]
      have hrem_tend : Tendsto (fun u : ℝ => (u : ℂ) ^ n * (f (u : ℂ) - evalTrunc a (n + 2) (u : ℂ)))
          atTop (𝓝 0) := by
        let K := C * A ^ (n + 2) * ((n + 2).factorial : ℝ)
        refine squeeze_zero_norm' (a := fun u : ℝ => K / u) ?_ ?_
        · filter_upwards [Filter.eventually_ge_atTop R] with u hu
          have hu1 : 1 ≤ u := hR.trans hu
          have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          have hnorm_u : ‖(u : ℂ)‖ = u := by
            rw [Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
          rw [norm_mul, norm_pow, hnorm_u]
          have hr := ha_rem (n + 2) (u : ℂ) (hray u hu)
          rw [hnorm_u] at hr
          calc u ^ n * ‖f (u : ℂ) - evalTrunc a (n + 2) (u : ℂ)‖
              ≤ u ^ n * (C * u * A ^ (n + 2) * ((n + 2).factorial : ℝ) / u ^ (n + 2)) :=
                mul_le_mul_of_nonneg_left hr (by positivity)
            _ = K / u := by
                dsimp only [K]
                have : u ^ (n + 2) = u ^ n * u * u := by ring
                rw [this]; field_simp [hu_pos.ne']
        · simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul K
      have hf_tend : Tendsto (fun u : ℝ => (u : ℂ) ^ n * f (u : ℂ)) atTop (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun u : ℝ => Cf / u) ?_ ?_
        · filter_upwards [Filter.eventually_ge_atTop (max 1 Uf)] with u hu
          have hu1 : 1 ≤ u := (le_max_left 1 Uf).trans hu
          have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          have hnorm_u : ‖(u : ℂ)‖ = u := by
            rw [Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
          rw [norm_mul, norm_pow, hnorm_u]
          have hf' := hUf u ((le_max_right 1 Uf).trans hu)
          calc u ^ n * ‖f (u : ℂ)‖ ≤ u ^ n * (Cf / u ^ (n + 1)) :=
                mul_le_mul_of_nonneg_left hf' (by positivity)
            _ = Cf / u := by rw [pow_succ]; field_simp [hu_pos.ne']
        · simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul Cf
      have hdiff_tend : Tendsto (fun u : ℝ =>
          (u : ℂ) ^ n * f (u : ℂ) -
          (u : ℂ) ^ n * (f (u : ℂ) - evalTrunc a (n + 2) (u : ℂ)) -
          (u : ℂ) ^ n * evalTerm a (n + 1) (u : ℂ)) atTop (𝓝 0) := by
        simpa using (hf_tend.sub hrem_tend).sub hP1_tend
      refine hdiff_tend.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop R] with u hu
      have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one (hR.trans hu)
      have htrunc : evalTrunc a (n + 2) (u : ℂ) = evalTerm a n (u : ℂ) + evalTerm a (n + 1) (u : ℂ) := by
        dsimp only [evalTrunc]
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hprev : ∑ m ∈ Finset.range n, evalTerm a m (u : ℂ) = 0 := by
          refine Finset.sum_eq_zero fun m hm => ?_
          dsimp only [evalTerm]
          rw [Finset.sum_eq_zero fun k _ => by rw [ih m (Finset.mem_range.mp hm) k, zero_mul], zero_div]
        rw [hprev, zero_add]
      rw [hP_eval u hu_pos, htrunc]; ring
    have hP0 : P = 0 := poly_eq_zero_of_tendsto_log_zero P hlim
    intro k
    by_cases hkn : k ≤ n
    · have hcoeff : P.coeff k = a n k := by
        change Polynomial.lcoeff ℂ k P = a n k
        dsimp only [P]
        rw [map_sum, Finset.sum_eq_single k]
        · simp [Polynomial.lcoeff_apply]
        · intro j _ hjk; simp [Polynomial.lcoeff_apply, Ne.symm hjk]
        · intro hk; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn)) hk
      rw [← hcoeff, hP0, Polynomial.coeff_zero]
    · exact ha0 n k (by omega)

/-- **Upgrade from `HasGev1Exp S f 0` to Watson Gevrey-1 Bound** (dropping the `‖z‖` factor via `N ↦ N + 1`!): -/
theorem gevrey1_bound_of_hasGev1Exp_zero {S : Set ℂ} {f : ℂ → ℂ} {a : LogCoeff}
    (hgev : HasGev1Exp S f a) (ha0 : ∀ n k, a n k = 0) :
    ∃ C > 0, ∃ A > 0, ∀ N : ℕ, ∀ z ∈ S,
      ‖f z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by
  rcases hgev with ⟨_, C, hC, A, hA, _, hrem⟩
  refine ⟨C * A, by positivity, 2 * A, by positivity, fun N z hz => ?_⟩
  have h1 := hrem (N + 1) z hz
  have hev0 : evalTrunc a (N + 1) z = 0 := by
    dsimp only [evalTrunc]
    refine Finset.sum_eq_zero fun n _ => ?_
    dsimp only [evalTerm]
    rw [Finset.sum_eq_zero fun k _ => by rw [ha0 n k, zero_mul], zero_div]
  rw [hev0, sub_zero] at h1
  by_cases hz0 : ‖z‖ = 0
  · rw [hz0] at h1
    simp only [mul_zero, zero_mul, zero_div] at h1
    have hfn : ‖f z‖ = 0 := le_antisymm h1 (norm_nonneg _)
    rw [hfn]; positivity
  · have hz_pos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
    have hfac := factorial_succ_le_two_pow N
    calc ‖f z‖ ≤ C * ‖z‖ * A ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖z‖ ^ (N + 1) := h1
      _ = (C * A) * A ^ N * ((N + 1).factorial : ℝ) / ‖z‖ ^ N := by
          rw [pow_succ A, pow_succ ‖z‖]; field_simp [hz_pos.ne']
      _ ≤ (C * A) * A ^ N * (2 ^ N * (N.factorial : ℝ)) / ‖z‖ ^ N := by gcongr
      _ = (C * A) * (2 * A) ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by rw [mul_pow]; ring

/-! #### 1e. Sector Geometry & Complete Reduction of `hsector` to `HasGev1Exp Σ₀ (I_ext z / z)` -/

/-- Enlarged sector angles `θ₁' = -19π/24`, `θ₂' = 3π/8` (same center `-5π/24` as `[-3π/4, π/3]`). -/
@[expose] def theta1 : ℝ := -3 * Real.pi / 4
@[expose] def theta2 : ℝ := Real.pi / 3
@[expose] def theta1' : ℝ := -19 * Real.pi / 24
@[expose] def theta2' : ℝ := 3 * Real.pi / 8

/-- Open rotated sector matching `rotatedClosedSector`. -/
@[expose] def rotatedOpenSector (θ₁ θ₂ R : ℝ) : Set ℂ :=
  {z : ℂ | R < ‖z‖ ∧ |Complex.arg (Complex.exp (-(((θ₁ + θ₂) / 2 : ℝ) : ℂ) * I) * z)| < (θ₂ - θ₁) / 2}

lemma isOpen_rotatedOpenSector {θ₁ θ₂ R : ℝ} (hlo : 0 < θ₂ - θ₁) (hhi : θ₂ - θ₁ < 2 * Real.pi)
    (hR : 0 ≤ R) : IsOpen (rotatedOpenSector θ₁ θ₂ R) := by
  let invRot : ℂ := Complex.exp (-(((θ₁ + θ₂) / 2 : ℝ) : ℂ) * I)
  have hnorm : ‖invRot‖ = 1 := by
    dsimp [invRot]; rw [Complex.norm_exp]; simp
  have hpre : rotatedOpenSector θ₁ θ₂ R =
      (fun z : ℂ => invRot * z) ⁻¹' openSector ((θ₂ - θ₁) / 2) R := by
    ext z
    simp only [rotatedOpenSector, Set.mem_preimage, openSector, Set.mem_ofPred_eq,
      norm_mul, hnorm, one_mul]
    rfl
  rw [hpre]
  exact (isOpen_openSector (by linarith) (by linarith) hR).preimage
    (continuous_const.mul continuous_id)

lemma rotatedClosedSector_subset_rotatedOpenSector {θ₁ θ₂ R : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) :
    rotatedClosedSector θ₁ θ₂ R ⊆ rotatedOpenSector (θ₁ - δ) (θ₂ + δ) (R / 2) := by
  intro z hz
  have hcenter : (θ₁ - δ + (θ₂ + δ)) / 2 = (θ₁ + θ₂) / 2 := by ring
  refine ⟨by linarith [hz.1], ?_⟩
  rw [hcenter]
  linarith [hz.2]

/-- Every point of `rotatedClosedSector theta1' theta2' R₀` (`R₀ > 0`) lies in `Complex.slitPlane`. -/
lemma rotatedClosedSector_enlarged_subset_slitPlane {R₀ : ℝ} (hR₀ : 0 < R₀) :
    rotatedClosedSector theta1' theta2' R₀ ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨hre, him⟩
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR₀ hz.1)
  have hre_neg : z.re < 0 := by
    rcases lt_or_eq_of_le hre with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq him) hz0
  have hz_eq : z = -((-z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have hr_pos : 0 < -z.re := by linarith
  -- Compute `arg (exp (-i * (-5π/24)) * z) = arg (exp (i * (5π/24 - π)) * (-z.re)) = -19π/24`
  have hcen : (theta1' + theta2') / 2 = -5 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
  have hhw : (theta2' - theta1') / 2 = 14 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
  have hprod : Complex.exp (-(((theta1' + theta2') / 2 : ℝ) : ℂ) * I) * z =
      Complex.exp ((Real.log (-z.re) : ℂ) + (((-19 * Real.pi / 24 : ℝ) : ℂ) * I)) := by
    rw [hcen, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr_pos]
    conv_lhs => rw [hz_eq]
    have hexp_pi : Complex.exp (((-19 * Real.pi / 24 : ℝ) : ℂ) * I) =
        -Complex.exp (-(((-5 * Real.pi / 24 : ℝ) : ℂ)) * I) := by
      have harg : (((-19 * Real.pi / 24 : ℝ) : ℂ) * I) =
          (-(((-5 * Real.pi / 24 : ℝ) : ℂ)) * I) + (-(Real.pi : ℂ) * I) := by push_cast; ring
      rw [harg, Complex.exp_add, show -(Real.pi : ℂ) * I = -((Real.pi : ℂ) * I) by ring,
        Complex.exp_neg, Complex.exp_pi_mul_I]
      ring
    rw [hexp_pi]; ring
  have harg_val := hz.2
  rw [hprod, hhw] at harg_val
  have him_eq : ((Real.log (-z.re) : ℂ) + (((-19 * Real.pi / 24 : ℝ) : ℂ) * I)).im = -19 * Real.pi / 24 := by
    simp
  have harg_eq : Complex.arg (Complex.exp ((Real.log (-z.re) : ℂ) + (((-19 * Real.pi / 24 : ℝ) : ℂ) * I))) =
      -19 * Real.pi / 24 := by
    rw [arg_cexp_eq_im (by rw [him_eq]; linarith [Real.pi_pos]) (by rw [him_eq]; linarith [Real.pi_pos]),
      him_eq]
  rw [harg_eq, abs_of_neg (by linarith [Real.pi_pos])] at harg_val
  linarith [Real.pi_pos]

/-- Small perturbation of `1`: if `‖w‖ ≤ 1/32`, then `|Complex.arg (1 + w)| ≤ 1 / 16`. -/
lemma abs_arg_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) :
    |Complex.arg (1 + w)| ≤ 1 / 16 := by
  have hre : 31 / 32 ≤ (1 + w).re := by
    have h1 : |w.re| ≤ 1 / 32 := (Complex.abs_re_le_norm w).trans hw
    have := (abs_le.mp h1).1
    simp only [Complex.add_re, Complex.one_re]; linarith
  have him : |(1 + w).im| ≤ 1 / 32 := by
    simp only [Complex.add_im, Complex.one_im, zero_add]
    exact (Complex.abs_im_le_norm w).trans hw
  have hpos : 0 < (1 + w).re := by linarith
  have hnorm_ge : 31 / 32 ≤ ‖1 + w‖ := hre.trans (Complex.re_le_norm _)
  have hnorm_pos : 0 < ‖1 + w‖ := lt_of_lt_of_le (by norm_num) hnorm_ge
  have harg : Complex.arg (1 + w) = Real.arcsin ((1 + w).im / ‖1 + w‖) := by
    unfold Complex.arg
    split_ifs with h
    · rfl
    · exact absurd hpos.le h
    · exact absurd hpos.le h
  rw [harg]
  set t : ℝ := (1 + w).im / ‖1 + w‖
  have ht_abs : |t| ≤ 1 / 31 := by
    dsimp only [t]
    rw [abs_div, abs_of_pos hnorm_pos, div_le_iff₀ hnorm_pos]
    linarith
  have hsin : (1 / 31 : ℝ) ≤ Real.sin (1 / 16) := by
    have h1 := Real.sin_gt_sub_cube (show (0 : ℝ) < 1 / 16 by norm_num)
    linarith
  have hpi2 : (1 / 16 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  rw [abs_le]
  constructor
  · have hlo : Real.sin (-(1 / 16 : ℝ)) ≤ t := by
      rw [Real.sin_neg]; linarith [(abs_le.mp ht_abs).1]
    have := Real.arcsin_le_arcsin hlo
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at this
  · have hhi : t ≤ Real.sin (1 / 16) := (abs_le.mp ht_abs).2.trans hsin
    have := Real.arcsin_le_arcsin hhi
    rwa [Real.arcsin_sin (by linarith) hpi2] at this

/-- Disk containment: for `z ∈ rotatedClosedSector theta1 theta2 (2 * R₀)`,
`closedBall z (‖z‖ / 32) ⊆ rotatedClosedSector theta1' theta2' R₀`. -/
lemma closedBall_subset_enlarged_sector {R₀ : ℝ} (hR₀ : 0 < R₀) {z : ℂ}
    (hz : z ∈ rotatedClosedSector theta1 theta2 (2 * R₀)) :
    Metric.closedBall z ((1 / 32 : ℝ) * ‖z‖) ⊆ rotatedClosedSector theta1' theta2' R₀ := by
  intro w hw
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith) hz.1
  have hz_ne : z ≠ 0 := norm_pos_iff.mp hz_pos
  have hdist : ‖w - z‖ ≤ (1 / 32 : ℝ) * ‖z‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hw_norm : R₀ ≤ ‖w‖ := by
    have htri : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      have := norm_add_le w (z - w); rw [norm_sub_rev] at this; simpa using this
    linarith [hz.1]
  have hcen : (theta1' + theta2') / 2 = (theta1 + theta2) / 2 := by
    dsimp [theta1, theta2, theta1', theta2']; ring
  refine ⟨hw_norm, ?_⟩
  rw [hcen]
  let invRot : ℂ := Complex.exp (-(((theta1 + theta2) / 2 : ℝ) : ℂ) * I)
  let δ : ℂ := (w - z) / z
  have hδ_le : ‖δ‖ ≤ 1 / 32 := by
    dsimp only [δ]; rw [norm_div, div_le_iff₀ hz_pos]; linarith
  have h1δ_arg : |Complex.arg (1 + δ)| ≤ 1 / 16 := abs_arg_one_add_le hδ_le
  have h1δ_ne : 1 + δ ≠ 0 := by
    intro h0
    have h1 : ‖δ‖ = 1 := by
      have : δ = -1 := by linear_combination h0
      simp [this]
    linarith
  have hprod : invRot * w = (invRot * z) * (1 + δ) := by
    dsimp only [δ]; field_simp [hz_ne]; ring
  have harg_z : |Complex.arg (invRot * z)| ≤ 13 * Real.pi / 24 := by
    have : (theta2 - theta1) / 2 = 13 * Real.pi / 24 := by dsimp [theta1, theta2]; ring
    simpa [invRot, this] using hz.2
  have hpi24 : (1 / 16 : ℝ) ≤ Real.pi / 24 := by linarith [Real.pi_gt_three]
  have hsum_in : Complex.arg (invRot * z) + Complex.arg (1 + δ) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 := abs_le.mp harg_z
    have h2 := abs_le.mp h1δ_arg
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have harg_mul : Complex.arg (invRot * w) = Complex.arg (invRot * z) + Complex.arg (1 + δ) := by
    rw [hprod]
    have hne1 : invRot * z ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hz_ne
    have h := Complex.arg_mul_coe_angle hne1 h1δ_ne
    have h' : (((Complex.arg ((invRot * z) * (1 + δ)) : ℝ) : Real.Angle)) =
        (((Complex.arg (invRot * z) + Complex.arg (1 + δ) : ℝ) : Real.Angle)) := by
      simpa [Real.Angle.coe_add] using h
    have hto := congr_arg Real.Angle.toReal h'
    rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
      Real.Angle.toReal_coe_eq_self_iff.mpr hsum_in] at hto
    exact hto
  have hhw' : (theta2' - theta1') / 2 = 14 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
  rw [hhw', show Complex.exp (-(((theta1 + theta2) / 2 : ℝ) : ℂ) * I) * w = invRot * w from rfl, harg_mul]
  calc |Complex.arg (invRot * z) + Complex.arg (1 + δ)|
      ≤ |Complex.arg (invRot * z)| + |Complex.arg (1 + δ)| := abs_add_le _ _
    _ ≤ 13 * Real.pi / 24 + 1 / 16 := add_le_add harg_z h1δ_arg
    _ ≤ 14 * Real.pi / 24 := by linarith

/-- Real iterated derivative of `u ↦ f (u : ℂ)` agrees with complex `iteratedDeriv j f (u : ℂ)`
on an open set containing `(u : ℂ)`. -/
lemma iteratedDeriv_comp_ofReal_eq {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    ∀ j : ℕ, ∀ u : ℝ, (u : ℂ) ∈ U →
      iteratedDeriv j (fun x : ℝ => f (x : ℂ)) u = iteratedDeriv j f (u : ℂ) := by
  intro j
  induction j with
  | zero => intro u _; simp
  | succ j ih =>
    intro u hu
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hnhds : ∀ᶠ x : ℝ in 𝓝 u, (x : ℂ) ∈ U :=
      Complex.continuous_ofReal.continuousAt.eventually (hU.mem_nhds hu)
    have hev : iteratedDeriv j (fun x : ℝ => f (x : ℂ)) =ᶠ[𝓝 u]
        fun x : ℝ => iteratedDeriv j f (x : ℂ) :=
      hnhds.mono fun x hx => ih x hx
    rw [hev.deriv_eq]
    have han : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
    have hd_j : DifferentiableAt ℂ (iteratedDeriv j f) (u : ℂ) := by
      have : AnalyticOnNhd ℂ (iteratedDeriv j f) U := by
        clear ih hev
        induction j with
        | zero => simpa using han
        | succ k ihk =>
          rw [iteratedDeriv_succ]
          exact ihk.deriv
      exact (this (u : ℂ) hu).differentiableAt
    exact (hd_j.hasDerivAt.comp_ofReal).deriv

/-- **MASTER SECTION 1 REDUCTION (`hsector_of_Y_gev1`)**:
If `I_ext : ℂ → ℂ` is holomorphic on an open set `U₀` containing `rotatedClosedSector theta1' theta2' R₀`
(`R₀ ≥ 1`), agrees with `I_plus` on `[R₀, ∞)`, and `z ↦ I_ext z / z` has a Gevrey-1 log-power
asymptotic expansion on `rotatedClosedSector theta1' theta2' R₀`, then the ENTIRE `hsector`
hypothesis of `PakNthPrimeClosure.pak_2_5a_of_pnt_and_sectorial_gevrey1_bridge` holds! -/
theorem hsector_of_Y_gev1
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {U₀ : Set ℂ} (hU₀ : IsOpen U₀)
    (hsub₀ : rotatedClosedSector theta1' theta2' R₀ ⊆ U₀)
    {I_ext : ℂ → ℂ} (hdiff : DifferentiableOn ℂ I_ext U₀)
    (hagree : ∀ u : ℝ, R₀ ≤ u → I_ext (u : ℂ) = I_plus u)
    {a_Y : LogCoeff}
    (hgev_Y : HasGev1Exp (rotatedClosedSector theta1' theta2' R₀) (fun z => I_ext z / z) a_Y) :
    ∀ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ),
      (∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U,
        ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖ ≤ C / u ^ N) →
      ∃ (θ₁ θ₂ R C A : ℝ) (U : Set ℂ) (F : ℂ → ℂ),
        θ₁ ≤ 0 ∧ 0 ≤ θ₂ ∧ Real.pi < θ₂ - θ₁ ∧ θ₂ - θ₁ < 2 * Real.pi ∧
        0 < R ∧ 0 < C ∧ 0 < A ∧ IsOpen U ∧ rotatedClosedSector θ₁ θ₂ R ⊆ U ∧
        DifferentiableOn ℂ F U ∧
        (∀ u : ℝ, R ≤ u →
          F (u : ℂ) = MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q) ∧
        (∀ N : ℕ, ∀ z ∈ rotatedClosedSector θ₁ θ₂ R, ‖F z‖ ≤ C * A ^ N * (N.factorial : ℝ) / ‖z‖ ^ N) := by
  intro r Q hflat
  let R : ℝ := 2 * R₀
  have hR_pos : 0 < R := by dsimp [R]; linarith
  have hR_ge1 : 1 ≤ R := by dsimp [R]; linarith
  let S₀ : Set ℂ := rotatedClosedSector theta1' theta2' R₀
  let S : Set ℂ := rotatedClosedSector theta1 theta2 R
  have hS₀_slit : S₀ ⊆ Complex.slitPlane := rotatedClosedSector_enlarged_subset_slitPlane (by linarith)
  have hS_norm : ∀ z ∈ S, 1 ≤ ‖z‖ := fun z hz => hR_ge1.trans hz.1
  have hball : ∀ z ∈ S, Metric.closedBall z ((1 / 32 : ℝ) * ‖z‖) ⊆ S₀ :=
    fun z hz => closedBall_subset_enlarged_sector (by linarith) hz
  have hS_sub_S₀ : S ⊆ S₀ := fun z hz => hball z hz (Metric.mem_closedBall_self (by positivity))
  -- Define `Y z = I_ext z / z`, holomorphic on `U₁ = U₀ \ {0}`
  let U₁ : Set ℂ := U₀ ∩ {(0 : ℂ)}ᶜ
  have hU₁ : IsOpen U₁ := hU₀.inter isOpen_compl_singleton
  have hS₀_U₁ : S₀ ⊆ U₁ := fun z hz =>
    ⟨hsub₀ hz, norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hz.1)⟩
  let Y : ℂ → ℂ := fun z => I_ext z / z
  have hY_diff : DifferentiableOn ℂ Y U₁ :=
    (hdiff.mono Set.inter_subset_left).div differentiableOn_id fun z hz => hz.2
  -- Every `iteratedDeriv j Y` has `HasGev1Exp S`!
  have hY_jet : ∀ j : ℕ, ∃ a : LogCoeff, HasGev1Exp S (iteratedDeriv j Y) a := fun j =>
    ⟨derivCoeff^[j] a_Y, hasGev1Exp_iteratedDeriv (by norm_num) (by norm_num)
      hU₁ hS₀_U₁ hS₀_slit hS_norm hball hY_diff hgev_Y j⟩
  -- For every `j`, `z ↦ iteratedDeriv j I_ext z / z = iteratedDeriv j Y z + j * z⁻¹ * iteratedDeriv (j-1) Y z`
  have hI_eq_zY : Set.EqOn I_ext (fun z => z * Y z) U₁ := fun z hz => by
    dsimp only [Y]; exact (mul_div_cancel₀ (I_ext z) hz.2).symm
  have hI_div_eq : ∀ j : ℕ, ∀ z ∈ U₁,
      iteratedDeriv j I_ext z / z =
        iteratedDeriv j Y z + (j : ℂ) * z⁻¹ * (if j = 0 then 0 else iteratedDeriv (j - 1) Y z) := by
    intro j z hz
    have hev : I_ext =ᶠ[𝓝 z] fun w => w * Y w :=
      Filter.mem_of_superset (hU₁.mem_nhds hz) hI_eq_zY
    rw [hev.iteratedDeriv_eq]
    have hY_an : AnalyticAt ℂ Y z := (hY_diff.analyticOnNhd hU₁) z hz
    have hY_cd : ContDiffAt ℂ j Y z := hY_an.contDiffAt.of_le le_top
    have hid_cd : ContDiffAt ℂ j (fun w : ℂ => w) z := contDiffAt_id
    have hleib := iteratedDeriv_mul hid_cd hY_cd
    have hid_k : ∀ k : ℕ, iteratedDeriv k (fun w : ℂ => w) z =
        if k = 0 then z else if k = 1 then 1 else 0 := by
      intro k
      cases k with
      | zero => simp
      | succ m =>
        cases m with
        | zero => simp [iteratedDeriv_succ]
        | succ p =>
          have hzero : ∀ q : ℕ, iteratedDeriv (q + 2) (fun w : ℂ => w) = 0 := by
            intro q
            induction q with
            | zero => ext w; simp [iteratedDeriv_succ]
            | succ q ihq => rw [iteratedDeriv_succ, ihq]; ext w; simp
          simp [hzero p]
    change iteratedDeriv j ((fun w : ℂ => w) * Y) z / z = _
    rw [hleib]
    cases j with
    | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
        Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero, Nat.cast_zero, zero_mul,
        ↓reduceIte, mul_zero, add_zero]
      exact mul_div_cancel_left₀ (Y z) hz.2
    | succ m =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have htail : ∑ k ∈ Finset.range m,
          ((m + 1).choose (k + 2) : ℂ) * iteratedDeriv (k + 2) (fun w : ℂ => w) z *
            iteratedDeriv (m + 1 - (k + 2)) Y z = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hid_k (k + 2)]
        simp
      rw [htail, zero_add, hid_k 0, hid_k 1]
      have hch1 : ((m + 1).choose 1 : ℂ) = (m + 1 : ℂ) := by
        rw [Nat.choose_one_right]; push_cast; rfl
      simp only [↓reduceIte, one_ne_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
        Nat.sub_zero, mul_one, Nat.add_sub_cancel, Nat.succ_ne_zero, hch1]
      have hz_ne : z ≠ 0 := hz.2
      field_simp [hz_ne]
      push_cast; ring
  have hI_div_gev : ∀ j : ℕ, ∃ a : LogCoeff, HasGev1Exp S (fun z => iteratedDeriv j I_ext z / z) a := by
    intro j
    rcases hY_jet j with ⟨a1, ha1⟩
    cases j with
    | zero =>
      refine ⟨a1, ?_⟩
      rcases ha1 with ⟨h1, C1, hC1, A1, hA1, hc1, hr1⟩
      refine ⟨h1, C1, hC1, A1, hA1, hc1, fun N z hz => ?_⟩
      simpa [hI_div_eq 0 z (hS₀_U₁ (hS_sub_S₀ hz))] using hr1 N z hz
    | succ m =>
      rcases hY_jet m with ⟨a2, ha2⟩
      have hinv := hasGev1Exp_inv hS_norm
      have hterm2 := hasGev1Exp_smul ((m + 1 : ℕ) : ℂ) (hasGev1Exp_mul hS_norm hinv ha2)
      have hsum := hasGev1Exp_add ha1 hterm2
      rcases hsum with ⟨h1, C1, hC1, A1, hA1, hc1, hr1⟩
      refine ⟨_, h1, C1, hC1, A1, hA1, hc1, fun N z hz => ?_⟩
      have heq := hI_div_eq (m + 1) z (hS₀_U₁ (hS_sub_S₀ hz))
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at heq
      dsimp only
      rw [heq]
      simpa [mul_assoc] using hr1 N z hz
  -- Define `F(z) = MvPolynomial.eval (fun j => iteratedDeriv j I_ext z) Q`
  let F : ℂ → ℂ := fun z => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_ext z) Q
  let d : ℕ := Q.totalDegree
  let G : ℂ → ℂ := fun z => z⁻¹ ^ d * F z
  -- Express `G(z)` as a polynomial in `z⁻¹` and `iteratedDeriv j I_ext z / z`, hence `HasGev1Exp S G`!
  have hG_gev : ∃ aG : LogCoeff, HasGev1Exp S G aG := by
    -- Write `Q = ∑ s ∈ Q.support, C (Q.coeff s) * ∏ i, X i ^ (s i)`
    have hG_sum : ∀ z ∈ S, G z =
        ∑ s ∈ Q.support, Q.coeff s *
          (z⁻¹ ^ (d - ∑ i : Fin (r + 1), s i) *
            ∏ i : Fin (r + 1), (iteratedDeriv (i : ℕ) I_ext z / z) ^ (s i)) := by
      intro z hz
      have hz_ne : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hS_norm z hz))
      dsimp only [G, F]
      rw [MvPolynomial.eval_eq', Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hdeg_le : ∑ i : Fin (r + 1), s i ≤ d := by
        dsimp only [d]
        have h1 : s.sum (fun _ e => e) ≤ Q.totalDegree := MvPolynomial.le_totalDegree hs
        have h2 : s.sum (fun _ e => e) = ∑ i : Fin (r + 1), s i := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        omega
      have hprod_div : (∏ i : Fin (r + 1), (iteratedDeriv (i : ℕ) I_ext z / z) ^ (s i)) =
          (∏ i : Fin (r + 1), iteratedDeriv (i : ℕ) I_ext z ^ (s i)) / z ^ (∑ i : Fin (r + 1), s i) := by
        simp_rw [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hprod_div]
      have hpow_z : z⁻¹ ^ (d - ∑ i : Fin (r + 1), s i) * (z ^ (∑ i : Fin (r + 1), s i))⁻¹ = z⁻¹ ^ d := by
        rw [← inv_pow, ← pow_add, Nat.sub_add_cancel hdeg_le]
      rw [div_eq_mul_inv]
      calc z⁻¹ ^ d * (Q.coeff s * ∏ i : Fin (r + 1), iteratedDeriv (i : ℕ) I_ext z ^ s i)
          = Q.coeff s * (z⁻¹ ^ d * ∏ i : Fin (r + 1), iteratedDeriv (i : ℕ) I_ext z ^ s i) := by ring
        _ = Q.coeff s * (z⁻¹ ^ (d - ∑ i : Fin (r + 1), s i) * (z ^ ∑ i : Fin (r + 1), s i)⁻¹ *
              ∏ i : Fin (r + 1), iteratedDeriv (i : ℕ) I_ext z ^ s i) := by rw [hpow_z]
        _ = Q.coeff s * (z⁻¹ ^ (d - ∑ i : Fin (r + 1), s i) *
              ((∏ i : Fin (r + 1), iteratedDeriv (i : ℕ) I_ext z ^ s i) *
                (z ^ ∑ i : Fin (r + 1), s i)⁻¹)) := by ring
    -- Build `HasGev1Exp S` for the RHS sum term by term!
    have hterm_gev : ∀ s : Fin (r + 1) →₀ ℕ, ∃ a : LogCoeff,
        HasGev1Exp S (fun z => Q.coeff s *
          (z⁻¹ ^ (d - ∑ i : Fin (r + 1), s i) *
            ∏ i : Fin (r + 1), (iteratedDeriv (i : ℕ) I_ext z / z) ^ (s i))) a := by
      intro s
      obtain ⟨ap1, hap1⟩ := hasGev1Exp_pow hS_norm (hasGev1Exp_inv hS_norm) (d - ∑ i : Fin (r + 1), s i)
      have hprod_gev : ∀ T : Finset (Fin (r + 1)), ∃ a : LogCoeff,
          HasGev1Exp S (fun z => ∏ i ∈ T, (iteratedDeriv (i : ℕ) I_ext z / z) ^ (s i)) a := by
        intro T
        induction T using Finset.induction_on with
        | empty =>
          exact ⟨constCoeff 1, by simpa using hasGev1Exp_const hS_norm 1⟩
        | insert i T hi ih =>
          rcases ih with ⟨aT, haT⟩
          rcases hI_div_gev (i : ℕ) with ⟨ai, hai⟩
          rcases hasGev1Exp_pow hS_norm hai (s i) with ⟨aip, haip⟩
          refine ⟨mulCoeff aip aT, ?_⟩
          have hm := hasGev1Exp_mul hS_norm haip haT
          simpa [Finset.prod_insert hi] using hm
      obtain ⟨ap2, hap2⟩ := hprod_gev Finset.univ
      exact ⟨smulCoeff (Q.coeff s) (mulCoeff ap1 ap2),
        hasGev1Exp_smul (Q.coeff s) (hasGev1Exp_mul hS_norm hap1 hap2)⟩
    have hfinset_sum : ∀ T : Finset (Fin (r + 1) →₀ ℕ), ∃ a : LogCoeff,
        HasGev1Exp S (fun z => ∑ s ∈ T, Q.coeff s *
          (z⁻¹ ^ (d - ∑ i : Fin (r + 1), s i) *
            ∏ i : Fin (r + 1), (iteratedDeriv (i : ℕ) I_ext z / z) ^ (s i))) a := by
      intro T
      induction T using Finset.induction_on with
      | empty => exact ⟨constCoeff 0, by simpa using hasGev1Exp_const hS_norm 0⟩
      | insert s T hs ih =>
        rcases ih with ⟨aT, haT⟩
        rcases hterm_gev s with ⟨as, has⟩
        refine ⟨addCoeff as aT, ?_⟩
        have ha := hasGev1Exp_add has haT
        simpa [Finset.sum_insert hs] using ha
    obtain ⟨aG, haG⟩ := hfinset_sum Q.support
    rcases haG with ⟨h1, C1, hC1, A1, hA1, hc1, hr1⟩
    exact ⟨aG, h1, C1, hC1, A1, hA1, hc1, fun N z hz => by rw [hG_sum z hz]; exact hr1 N z hz⟩
  -- `F` agrees with `Q(jet I_plus u)` on `[R, ∞)`
  have hF_agree : ∀ u : ℝ, R ≤ u →
      F (u : ℂ) = MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q := by
    intro u hu
    dsimp only [F]
    refine congrArg (fun x => MvPolynomial.eval x Q) (funext fun j => ?_)
    have hu_S : (u : ℂ) ∈ S :=
      ofReal_mem_rotatedClosedSector (by dsimp [theta1]; linarith [Real.pi_pos])
        (by dsimp [theta2]; linarith [Real.pi_pos])
        (by dsimp [theta1, theta2]; linarith [Real.pi_pos]) hR_pos hu
    have hu_U₀ : (u : ℂ) ∈ U₀ := hsub₀ (hS_sub_S₀ hu_S)
    rw [← iteratedDeriv_comp_ofReal_eq hU₀ hdiff (j : ℕ) u hu_U₀]
    have hev : (fun x : ℝ => I_ext (x : ℂ)) =ᶠ[𝓝 u] I_plus := by
      have hu_gt : R₀ < u := by dsimp [R] at hu; linarith
      filter_upwards [isOpen_Ioi.mem_nhds hu_gt] with x hx
      exact hagree x (le_of_lt hx)
    exact hev.iteratedDeriv_eq (j : ℕ)
  -- `G` is flat to all orders on `[R, ∞)`!
  have hG_flat : ∀ N : ℕ, ∃ C > 0, ∃ U : ℝ, ∀ u ≥ U, ‖G (u : ℂ)‖ ≤ C / u ^ N := by
    intro N
    obtain ⟨C, hC, U, hU⟩ := hflat N
    refine ⟨C, hC, max R U, fun u hu => ?_⟩
    have huR : R ≤ u := (le_max_left R U).trans hu
    have hu1 : 1 ≤ u := hR_ge1.trans huR
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    dsimp only [G]
    rw [hF_agree u huR, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    have hinv_le : (u⁻¹) ^ d ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu1)
    calc (u⁻¹) ^ d * ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_plus u) Q‖
        ≤ 1 * (C / u ^ N) := mul_le_mul hinv_le (hU u ((le_max_right R U).trans hu)) (norm_nonneg _) zero_le_one
      _ = C / u ^ N := one_mul _
  -- Kill all coefficients of `aG` and upgrade to Gevrey-1 Watson bound on `G`, hence on `F`!
  rcases hG_gev with ⟨aG, haG⟩
  have hray_S : ∀ u : ℝ, R ≤ u → (u : ℂ) ∈ S := fun u hu =>
    ofReal_mem_rotatedClosedSector (by dsimp [theta1]; linarith [Real.pi_pos])
      (by dsimp [theta2]; linarith [Real.pi_pos])
      (by dsimp [theta1, theta2]; linarith [Real.pi_pos]) hR_pos hu
  have haG0 : ∀ n k, aG n k = 0 := coeff_eq_zero_of_ray_flat hR_ge1 hray_S haG hG_flat
  obtain ⟨CG, hCG, AG, hAG, hG_bound⟩ := gevrey1_bound_of_hasGev1Exp_zero haG haG0
  -- Holomorphicity of `F` on `U₀`
  have hF_diff : DifferentiableOn ℂ F U₀ := by
    have han_I : AnalyticOnNhd ℂ I_ext U₀ := hdiff.analyticOnNhd hU₀
    have hjet_diff : ∀ j : ℕ, DifferentiableOn ℂ (iteratedDeriv j I_ext) U₀ := by
      intro j
      have han_j : AnalyticOnNhd ℂ (iteratedDeriv j I_ext) U₀ := by
        induction j with
        | zero => simpa using han_I
        | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
      exact han_j.differentiableOn
    have hdiff_all : ∀ P : MvPolynomial (Fin (r + 1)) ℂ,
        DifferentiableOn ℂ (fun z => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) I_ext z) P) U₀ := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C c =>
        simp [MvPolynomial.eval_C, differentiableOn_const]
      | add p q ihp ihq =>
        simpa [map_add] using ihp.fun_add ihq
      | mul_X p i ihp =>
        simpa [map_mul, MvPolynomial.eval_X] using ihp.fun_mul (hjet_diff (i : ℕ))
    exact hdiff_all Q
  refine ⟨theta1, theta2, R, CG * AG ^ d * (2 ^ d * (d.factorial : ℝ)), 2 * AG, U₀, F,
    by dsimp [theta1]; linarith [Real.pi_pos],
    by dsimp [theta2]; linarith [Real.pi_pos],
    by dsimp [theta1, theta2]; linarith [Real.pi_pos],
    by dsimp [theta1, theta2]; linarith [Real.pi_pos],
    hR_pos, by positivity, by positivity, hU₀, hS_sub_S₀.trans hsub₀, hF_diff, hF_agree, ?_⟩
  intro N z hz
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one (hS_norm z hz)
  have hz_ne : z ≠ 0 := norm_pos_iff.mp hz_pos
  have hFz : F z = z ^ d * G z := by
    dsimp only [G]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz_ne, one_pow, one_mul]
  have hGb := hG_bound (N + d) z hz
  have hfac_d : ((N + d).factorial : ℝ) ≤ 2 ^ (N + d) * (d.factorial : ℝ) * (N.factorial : ℝ) := by
    have h1 : ((N + d).choose d : ℝ) * (d.factorial : ℝ) * (N.factorial : ℝ) = ((N + d).factorial : ℝ) := by
      exact_mod_cast (by simpa [Nat.add_sub_cancel_right] using
        Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left d N))
    have hch : ((N + d).choose d : ℝ) ≤ 2 ^ (N + d) := by
      have : (N + d).choose d ≤ ∑ k ∈ Finset.range (N + d + 1), (N + d).choose k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      rw [Nat.sum_range_choose] at this
      exact_mod_cast this
    rw [← h1]
    gcongr
  rw [hFz, norm_mul, norm_pow]
  calc ‖z‖ ^ d * ‖G z‖
      ≤ ‖z‖ ^ d * (CG * AG ^ (N + d) * ((N + d).factorial : ℝ) / ‖z‖ ^ (N + d)) :=
        mul_le_mul_of_nonneg_left hGb (by positivity)
    _ = CG * AG ^ (N + d) * ((N + d).factorial : ℝ) / ‖z‖ ^ N := by
        rw [pow_add ‖z‖]; field_simp [hz_pos.ne']
    _ ≤ CG * AG ^ (N + d) * (2 ^ (N + d) * (d.factorial : ℝ) * (N.factorial : ℝ)) / ‖z‖ ^ N := by
        gcongr
    _ = (CG * AG ^ d * (2 ^ d * (d.factorial : ℝ))) * (2 * AG) ^ N * (N.factorial : ℝ) / ‖z‖ ^ N := by
        rw [pow_add AG, pow_add (2 : ℝ), mul_pow]; ring

/-! ### 2. Rotated Stieltjes Integral `S_phi`, Identity with `Ei_complex + iπ`, and Gevrey-1 Expansion -/

/-- Rotation angle `φ = 11π/24` (82.5°) for the rotated Stieltjes integral `S_phi`. -/
@[expose] def phiRay : ℝ := 11 * Real.pi / 24

/-- Unit complex ray direction `e^{iφ}`. -/
@[expose] def eip : ℂ := Complex.exp ((phiRay : ℂ) * I)

lemma phiRay_pos : 0 < phiRay := by dsimp [phiRay]; linarith [Real.pi_pos]

lemma phiRay_lt_pi_div_two : phiRay < Real.pi / 2 := by dsimp [phiRay]; linarith [Real.pi_pos]

lemma cos_phiRay_pos : 0 < Real.cos phiRay :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [phiRay_pos, Real.pi_pos], phiRay_lt_pi_div_two⟩

lemma sin_phiRay_pos : 0 < Real.sin phiRay :=
  Real.sin_pos_of_pos_of_lt_pi phiRay_pos (by linarith [phiRay_lt_pi_div_two, Real.pi_pos])

lemma eip_re : eip.re = Real.cos phiRay := by
  dsimp [eip]; rw [Complex.exp_ofReal_mul_I_re]

lemma eip_im : eip.im = Real.sin phiRay := by
  dsimp [eip]; rw [Complex.exp_ofReal_mul_I_im]

lemma norm_eip : ‖eip‖ = 1 := by
  dsimp [eip]; rw [Complex.norm_exp]; simp

lemma eip_ne_zero : eip ≠ 0 := Complex.exp_ne_zero _

/-- Signed distance from `w` to the line through `0` and `e^{iφ}`: `d_phi w = Re w sin φ - Im w cos φ`. -/
@[expose] def dPhi (w : ℂ) : ℝ := w.re * Real.sin phiRay - w.im * Real.cos phiRay

/-- Unified positive margin `distPhi w = max (-w.im) (dPhi w)` on the open slit domain `OmegaPhi`. -/
@[expose] def distPhi (w : ℂ) : ℝ := max (-w.im) (dPhi w)

/-- Open domain `OmegaPhi = {w : ℂ | w.im < 0 ∨ 0 < dPhi w}` avoiding the rotated ray `e^{iφ} ℝ_{≥ 0}`. -/
@[expose] def OmegaPhi : Set ℂ := {w : ℂ | w.im < 0 ∨ 0 < dPhi w}

lemma isOpen_OmegaPhi : IsOpen OmegaPhi := by
  have h1 : IsOpen {w : ℂ | w.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have h2 : IsOpen {w : ℂ | 0 < dPhi w} :=
    isOpen_lt continuous_const
      ((Complex.continuous_re.mul continuous_const).sub (Complex.continuous_im.mul continuous_const))
  exact h1.union h2

lemma distPhi_pos {w : ℂ} (hw : w ∈ OmegaPhi) : 0 < distPhi w := by
  rcases hw with him | hd
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · exact lt_of_lt_of_le hd (le_max_right _ _)

lemma OmegaPhi_subset_slitPlane : OmegaPhi ⊆ Complex.slitPlane := by
  intro w hw
  rw [Complex.mem_slitPlane_iff]
  rcases hw with him | hd
  · exact Or.inr (ne_of_lt him)
  · by_cases him0 : w.im = 0
    · left
      dsimp only [dPhi] at hd
      rw [him0, zero_mul, sub_zero] at hd
      nlinarith [sin_phiRay_pos]
    · exact Or.inr him0

/-- Key lower bound: for every `w ∈ OmegaPhi` and `r ≥ 0`, `distPhi w ≤ ‖w - r * eip‖`. -/
lemma distPhi_le_norm_sub_ray {w : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    distPhi w ≤ ‖w - (r : ℂ) * eip‖ := by
  apply max_le
  · have h1 := Complex.abs_im_le_norm (w - (r : ℂ) * eip)
    have him : (w - (r : ℂ) * eip).im = w.im - r * Real.sin phiRay := by
      simp [Complex.mul_im, eip_im]
    rw [him] at h1
    have h2 : -(w.im - r * Real.sin phiRay) ≤ |w.im - r * Real.sin phiRay| := neg_le_abs _
    have hr_nn : 0 ≤ r * Real.sin phiRay := mul_nonneg hr sin_phiRay_pos.le
    linarith
  · -- Rotate by `exp (-i φ)`: `Im (exp (-i φ) * (w - r * eip)) = -dPhi w`!
    let rot : ℂ := Complex.exp (-(phiRay : ℂ) * I)
    have hrot_norm : ‖rot‖ = 1 := by dsimp [rot]; rw [Complex.norm_exp]; simp
    have hrot_eip : rot * eip = 1 := by dsimp [rot, eip]; rw [← Complex.exp_add]; simp
    have hmul : rot * (w - (r : ℂ) * eip) = rot * w - (r : ℂ) := by
      rw [mul_sub, mul_left_comm, hrot_eip, mul_one]
    have hnorm : ‖rot * (w - (r : ℂ) * eip)‖ = ‖w - (r : ℂ) * eip‖ := by
      rw [norm_mul, hrot_norm, one_mul]
    have him : (rot * w - (r : ℂ)).im = -dPhi w := by
      have hre_rot : rot.re = Real.cos phiRay := by
        dsimp [rot]
        have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      have him_rot : rot.im = -Real.sin phiRay := by
        dsimp [rot]
        have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      simp [Complex.sub_im, Complex.mul_im, hre_rot, him_rot, dPhi]
      ring
    have h1 := Complex.abs_im_le_norm (rot * (w - (r : ℂ) * eip))
    rw [hnorm, hmul, him, abs_neg] at h1
    exact (le_abs_self _).trans h1

/-- Angular margin on any closed sector `{-π + δ ≤ arg w ≤ φ - δ}` (`0 < δ ≤ π/24`):
`sin δ * ‖w‖ ≤ distPhi w` (and in particular `w ∈ OmegaPhi` whenever `w ≠ 0`). -/
lemma sin_mul_norm_le_distPhi {δ : ℝ} (hδ0 : 0 < δ) (hδ_hi : δ ≤ Real.pi / 24)
    {w : ℂ} (hw0 : w ≠ 0) (harg_lo : -Real.pi + δ ≤ Complex.arg w)
    (harg_hi : Complex.arg w ≤ phiRay - δ) :
    Real.sin δ * ‖w‖ ≤ distPhi w := by
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hre : w.re = ‖w‖ * Real.cos (Complex.arg w) := (Complex.norm_mul_cos_arg w).symm
  have him : w.im = ‖w‖ * Real.sin (Complex.arg w) := (Complex.norm_mul_sin_arg w).symm
  by_cases hhalf : Complex.arg w ≤ -Real.pi / 2
  · have hsin_ge : Real.sin δ ≤ -Real.sin (Complex.arg w) := by
      have h1 : -Real.sin (Complex.arg w) = Real.sin (Complex.arg w + Real.pi) :=
        (Real.sin_add_pi (Complex.arg w)).symm
      rw [h1]
      have harg_in1 : δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have harg_in2 : Complex.arg w + Real.pi ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith⟩
      exact Real.strictMonoOn_sin.monotoneOn harg_in1 harg_in2 (by linarith)
    calc Real.sin δ * ‖w‖ ≤ (-Real.sin (Complex.arg w)) * ‖w‖ :=
          mul_le_mul_of_nonneg_right hsin_ge hw_pos.le
      _ = -w.im := by rw [him]; ring
      _ ≤ distPhi w := le_max_left _ _
  · push Not at hhalf
    have hd_eq : dPhi w = ‖w‖ * Real.sin (phiRay - Complex.arg w) := by
      dsimp only [dPhi]
      rw [hre, him, Real.sin_sub]; ring
    have hsin_ge : Real.sin δ ≤ Real.sin (phiRay - Complex.arg w) := by
      set θ : ℝ := phiRay - Complex.arg w
      have hθ_lo : δ ≤ θ := by dsimp [θ]; linarith
      have hθ_hi : θ ≤ Real.pi - δ := by dsimp [θ, phiRay]; linarith
      by_cases hθ2 : θ ≤ Real.pi / 2
      · exact Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], hθ2⟩ hθ_lo
      · push Not at hθ2
        have h1 : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
        rw [h1]
        exact Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], by linarith⟩ (by linarith)
    calc Real.sin δ * ‖w‖ ≤ Real.sin (phiRay - Complex.arg w) * ‖w‖ :=
          mul_le_mul_of_nonneg_right hsin_ge hw_pos.le
      _ = dPhi w := by rw [hd_eq]; ring
      _ ≤ distPhi w := le_max_right _ _

/-- Rotated real exponential-monomial integral:
`∫_{r > 0} r^n * exp (-a * r) dr = n! / a^(n + 1)` for `a > 0`. -/
lemma integral_Ioi_pow_mul_exp_neg {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ n * Real.exp (-a * r)) = (n.factorial : ℝ) / a ^ (n + 1) := by
  have hint : ∀ m : ℕ, IntegrableOn (fun r : ℝ => r ^ m * Real.exp (-a * r)) (Set.Ioi 0) := by
    intro m
    have h1 := integrableOn_exp_mul_Ioi (show -(a / 2) < 0 by linarith) 0
    have hdom : IntegrableOn (fun r : ℝ => ((m.factorial : ℝ) / (a / 2) ^ m) * Real.exp (-(a / 2) * r))
        (Set.Ioi 0) := h1.const_mul _
    refine hdom.mono' ((continuous_pow m |>.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    rw [Real.norm_of_nonneg (by positivity)]
    have hpow : ((a / 2) * r) ^ m / (m.factorial : ℝ) ≤ Real.exp ((a / 2) * r) :=
      Real.pow_div_factorial_le_exp ((a / 2) * r) (by positivity) m
    have hrm : r ^ m ≤ ((m.factorial : ℝ) / (a / 2) ^ m) * Real.exp ((a / 2) * r) := by
      rw [mul_pow, div_le_iff₀ (by positivity)] at hpow
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    calc r ^ m * Real.exp (-a * r)
        ≤ (((m.factorial : ℝ) / (a / 2) ^ m) * Real.exp ((a / 2) * r)) * Real.exp (-a * r) :=
          mul_le_mul_of_nonneg_right hrm (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / (a / 2) ^ m) * Real.exp (-(a / 2) * r) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  induction n with
  | zero =>
    have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun x : ℝ => -a⁻¹ * Real.exp (-a * x)) (Real.exp (-a * r)) r := by
      intro r _
      have h1 : HasDerivAt (fun x : ℝ => -a * x) (-a) r := by
        simpa using (hasDerivAt_id r).const_mul (-a)
      convert h1.exp.const_mul (-a⁻¹) using 1
      field_simp [ha.ne']
    have htend : Tendsto (fun x : ℝ => -a⁻¹ * Real.exp (-a * x)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => -a * x) atTop atBot :=
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop ha)).congr fun x => by simp
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (-a⁻¹)
    have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      (by simpa using hint 0) htend
    simpa [pow_zero, one_mul, Nat.factorial_zero, pow_one, div_eq_mul_inv] using hval
  | succ m ih =>
    have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun x : ℝ => -x ^ (m + 1) * Real.exp (-a * x))
          (a * (r ^ (m + 1) * Real.exp (-a * r)) - ((m + 1 : ℕ) : ℝ) * (r ^ m * Real.exp (-a * r))) r := by
      intro r _
      have h1 : HasDerivAt (fun x : ℝ => -x ^ (m + 1)) (-((m + 1 : ℕ) : ℝ) * r ^ m) r := by
        have h := ((hasDerivAt_id r).fun_pow (m + 1)).fun_neg
        refine h.congr_deriv ?_; simp only [id_eq, Nat.add_sub_cancel]; push_cast; ring
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-a * x)) (-a * Real.exp (-a * r)) r := by
        have hx : HasDerivAt (fun x : ℝ => -a * x) (-a) r := by
          simpa using (hasDerivAt_id r).const_mul (-a)
        simpa [mul_comm] using hx.exp
      convert h1.mul h2 using 1; ring
    have htend : Tendsto (fun x : ℝ => -x ^ (m + 1) * Real.exp (-a * x)) atTop (𝓝 0) := by
      let K := (((m + 1).factorial : ℝ) / (a / 2) ^ (m + 1))
      refine squeeze_zero_norm' (a := fun x : ℝ => K * Real.exp (-(a / 2) * x)) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
        rw [norm_mul, norm_neg, Real.norm_of_nonneg (pow_nonneg hx _),
          Real.norm_of_nonneg (Real.exp_pos _).le]
        have hpow : ((a / 2) * x) ^ (m + 1) / ((m + 1).factorial : ℝ) ≤ Real.exp ((a / 2) * x) :=
          Real.pow_div_factorial_le_exp ((a / 2) * x) (by positivity) (m + 1)
        have hxm : x ^ (m + 1) ≤ K * Real.exp ((a / 2) * x) := by
          dsimp only [K]
          rw [mul_pow, div_le_iff₀ (by positivity)] at hpow
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          linarith
        calc x ^ (m + 1) * Real.exp (-a * x)
            ≤ (K * Real.exp ((a / 2) * x)) * Real.exp (-a * x) :=
              mul_le_mul_of_nonneg_right hxm (Real.exp_pos _).le
          _ = K * Real.exp (-(a / 2) * x) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      · have h1 : Tendsto (fun x : ℝ => -(a / 2) * x) atTop atBot :=
          (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (half_pos ha))).congr fun x => by simp
        simpa using (Real.tendsto_exp_atBot.comp h1).const_mul K
    have hint_diff : IntegrableOn
        (fun r : ℝ => a * (r ^ (m + 1) * Real.exp (-a * r)) - ((m + 1 : ℕ) : ℝ) * (r ^ m * Real.exp (-a * r)))
        (Set.Ioi 0) :=
      ((hint (m + 1)).const_mul a).sub ((hint m).const_mul _)
    have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_diff htend
    simp only [zero_pow (Nat.succ_ne_zero m), neg_zero, zero_mul, sub_zero] at hval
    rw [integral_sub ((hint (m + 1)).const_mul a) ((hint m).const_mul _),
      integral_const_mul, integral_const_mul, ih] at hval
    have hfac : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_succ m
    have hmul : a * ∫ r in Set.Ioi (0 : ℝ), r ^ (m + 1) * Real.exp (-a * r) =
        ((m + 1).factorial : ℝ) / a ^ (m + 1) := by
      rw [hfac]; linarith [show ((m + 1 : ℕ) : ℝ) * ((m.factorial : ℝ) / a ^ (m + 1)) =
        ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) / a ^ (m + 1) by ring]
    rw [pow_succ, ← div_div, ← hmul]
    field_simp [ha.ne']

/-- Integrability of `(r * eip)^n * exp (-(r * eip)) * eip` on `(0, ∞)`. -/
lemma integrableOn_ray_monomial (n : ℕ) :
    IntegrableOn (fun r : ℝ => ((r : ℂ) * eip) ^ n * Complex.exp (-((r : ℂ) * eip)) * eip)
      (Set.Ioi 0) := by
  have hreal : IntegrableOn (fun r : ℝ => r ^ n * Real.exp (-Real.cos phiRay * r)) (Set.Ioi 0) := by
    have h1 := integrableOn_exp_mul_Ioi (show -(Real.cos phiRay / 2) < 0 by linarith [cos_phiRay_pos]) 0
    have hdom : IntegrableOn (fun r : ℝ =>
        ((n.factorial : ℝ) / (Real.cos phiRay / 2) ^ n) * Real.exp (-(Real.cos phiRay / 2) * r))
        (Set.Ioi 0) := h1.const_mul _
    refine hdom.mono' ((continuous_pow n |>.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hcos : 0 < Real.cos phiRay := cos_phiRay_pos
    have hr0 : 0 < r := hr
    rw [Real.norm_of_nonneg (by positivity)]
    have hpow : ((Real.cos phiRay / 2) * r) ^ n / (n.factorial : ℝ) ≤ Real.exp ((Real.cos phiRay / 2) * r) :=
      Real.pow_div_factorial_le_exp _ (by positivity) n
    have hrn : r ^ n ≤ ((n.factorial : ℝ) / (Real.cos phiRay / 2) ^ n) * Real.exp ((Real.cos phiRay / 2) * r) := by
      rw [mul_pow, div_le_iff₀ (by positivity)] at hpow
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    calc r ^ n * Real.exp (-Real.cos phiRay * r)
        ≤ (((n.factorial : ℝ) / (Real.cos phiRay / 2) ^ n) * Real.exp ((Real.cos phiRay / 2) * r)) *
            Real.exp (-Real.cos phiRay * r) := mul_le_mul_of_nonneg_right hrn (Real.exp_pos _).le
      _ = ((n.factorial : ℝ) / (Real.cos phiRay / 2) ^ n) * Real.exp (-(Real.cos phiRay / 2) * r) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hcont : Continuous (fun r : ℝ => ((r : ℂ) * eip) ^ n * Complex.exp (-((r : ℂ) * eip)) * eip) :=
    (((Complex.continuous_ofReal.mul continuous_const).pow n).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const).neg)).mul continuous_const
  refine hreal.mono' hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le,
    norm_eip, mul_one, mul_one, Complex.norm_exp]
  have hre : (-((r : ℂ) * eip)).re = -Real.cos phiRay * r := by
    simp [Complex.mul_re, eip_re]; ring
  rw [hre]

/-- Exact rotated Gamma identity: `∫_{r > 0} (r * eip)^n * exp (-(r * eip)) * eip dr = n!`. -/
theorem integral_Ioi_ray_monomial (n : ℕ) :
    (∫ r in Set.Ioi (0 : ℝ), ((r : ℂ) * eip) ^ n * Complex.exp (-((r : ℂ) * eip)) * eip) =
      (n.factorial : ℂ) := by
  induction n with
  | zero =>
    have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun x : ℝ => -Complex.exp (-((x : ℂ) * eip)))
          (Complex.exp (-((r : ℂ) * eip)) * eip) r := by
      intro r _
      have h1 : HasDerivAt (fun x : ℝ => -((x : ℂ) * eip)) (-eip) r := by
        simpa using ((hasDerivAt_id r).ofReal_comp.mul_const eip).fun_neg
      convert h1.cexp.fun_neg using 1; ring
    have htend : Tendsto (fun x : ℝ => -Complex.exp (-((x : ℂ) * eip))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun x : ℝ => Real.exp (-Real.cos phiRay * x)) (fun x => ?_) ?_
      · rw [norm_neg, Complex.norm_exp]
        have hre : (-((x : ℂ) * eip)).re = -Real.cos phiRay * x := by
          simp [Complex.mul_re, eip_re]; ring
        rw [hre]
      · have h1 : Tendsto (fun x : ℝ => -Real.cos phiRay * x) atTop atBot :=
          (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop cos_phiRay_pos)).congr fun x => by simp
        exact Real.tendsto_exp_atBot.comp h1
    have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (by simpa using integrableOn_ray_monomial 0) htend
    simpa using hval
  | succ m ih =>
    have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun x : ℝ => -((x : ℂ) * eip) ^ (m + 1) * Complex.exp (-((x : ℂ) * eip)))
          (((r : ℂ) * eip) ^ (m + 1) * Complex.exp (-((r : ℂ) * eip)) * eip -
            ((m + 1 : ℕ) : ℂ) * (((r : ℂ) * eip) ^ m * Complex.exp (-((r : ℂ) * eip)) * eip)) r := by
      intro r _
      have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) * eip) eip r := by
        simpa using (hasDerivAt_id r).ofReal_comp.mul_const eip
      have h1 : HasDerivAt (fun x : ℝ => -((x : ℂ) * eip) ^ (m + 1))
          (-(((m + 1 : ℕ) : ℂ) * ((r : ℂ) * eip) ^ m * eip)) r := by
        simpa using (hlin.fun_pow (m + 1)).fun_neg
      have h2 : HasDerivAt (fun x : ℝ => Complex.exp (-((x : ℂ) * eip)))
          (Complex.exp (-((r : ℂ) * eip)) * (-eip)) r := by
        simpa using hlin.fun_neg.cexp
      convert h1.mul h2 using 1; ring
    have htend : Tendsto (fun x : ℝ => -((x : ℂ) * eip) ^ (m + 1) * Complex.exp (-((x : ℂ) * eip)))
        atTop (𝓝 0) := by
      have hcos : 0 < Real.cos phiRay := cos_phiRay_pos
      let K := (((m + 1).factorial : ℝ) / (Real.cos phiRay / 2) ^ (m + 1))
      refine squeeze_zero_norm' (a := fun x : ℝ => K * Real.exp (-(Real.cos phiRay / 2) * x)) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
        rw [norm_mul, norm_neg, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx,
          norm_eip, mul_one, Complex.norm_exp]
        have hre : (-((x : ℂ) * eip)).re = -Real.cos phiRay * x := by
          simp [Complex.mul_re, eip_re]; ring
        rw [hre]
        have hpow : ((Real.cos phiRay / 2) * x) ^ (m + 1) / ((m + 1).factorial : ℝ) ≤
            Real.exp ((Real.cos phiRay / 2) * x) :=
          Real.pow_div_factorial_le_exp _ (by positivity) (m + 1)
        have hxm : x ^ (m + 1) ≤ K * Real.exp ((Real.cos phiRay / 2) * x) := by
          dsimp only [K]
          rw [mul_pow, div_le_iff₀ (by positivity)] at hpow
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          linarith
        calc x ^ (m + 1) * Real.exp (-Real.cos phiRay * x)
            ≤ (K * Real.exp ((Real.cos phiRay / 2) * x)) * Real.exp (-Real.cos phiRay * x) :=
              mul_le_mul_of_nonneg_right hxm (Real.exp_pos _).le
          _ = K * Real.exp (-(Real.cos phiRay / 2) * x) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      · have h1 : Tendsto (fun x : ℝ => -(Real.cos phiRay / 2) * x) atTop atBot :=
          (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (half_pos cos_phiRay_pos))).congr fun x => by simp
        simpa using (Real.tendsto_exp_atBot.comp h1).const_mul K
    have hint_diff := (integrableOn_ray_monomial (m + 1)).sub
      ((integrableOn_ray_monomial m).const_mul ((m + 1 : ℕ) : ℂ))
    have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_diff htend
    simp only [Complex.ofReal_zero, zero_mul, zero_pow (Nat.succ_ne_zero m), neg_zero, sub_zero] at hval
    rw [integral_sub (integrableOn_ray_monomial (m + 1))
      ((integrableOn_ray_monomial m).const_mul ((m + 1 : ℕ) : ℂ)),
      integral_const_mul, ih] at hval
    have hfac : ((m + 1).factorial : ℂ) = ((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ) := by
      exact_mod_cast Nat.factorial_succ m
    rw [hfac]; linear_combination hval

/-- The rotated Stieltjes inner integral `∫_{r > 0} exp(-(r * eip)) / (w - r * eip) * eip dr`. -/
@[expose] def S_phi_inner (w : ℂ) : ℂ :=
  ∫ r in Set.Ioi (0 : ℝ), Complex.exp (-((r : ℂ) * eip)) / (w - (r : ℂ) * eip) * eip

/-- The rotated Stieltjes function `S_phi(w) = w * S_phi_inner(w)`. -/
@[expose] def S_phi (w : ℂ) : ℂ := w * S_phi_inner w

/-- Auxiliary function `A_phi(w) = exp(w) * S_phi_inner(w) = (exp(w) / w) * S_phi(w)`. -/
@[expose] def A_phi (w : ℂ) : ℂ := Complex.exp w * S_phi_inner w

lemma integrableOn_S_phi_integrand {w : ℂ} (hw : w ∈ OmegaPhi) :
    IntegrableOn (fun r : ℝ => Complex.exp (-((r : ℂ) * eip)) / (w - (r : ℂ) * eip) * eip) (Set.Ioi 0) := by
  have hd : 0 < distPhi w := distPhi_pos hw
  have hreal : IntegrableOn (fun r : ℝ => (distPhi w)⁻¹ * Real.exp (-Real.cos phiRay * r)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -Real.cos phiRay < 0 by linarith [cos_phiRay_pos]) 0).const_mul _
  have hcont : ContinuousOn (fun r : ℝ => Complex.exp (-((r : ℂ) * eip)) / (w - (r : ℂ) * eip) * eip)
      (Set.Ioi 0) := by
    refine ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const).neg).continuousOn.div
      (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_).mul continuousOn_const
    intro r hr
    exact norm_pos_iff.mp (lt_of_lt_of_le hd (distPhi_le_norm_sub_ray (le_of_lt hr)))
  refine hreal.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [norm_mul, norm_div, Complex.norm_exp, norm_eip, mul_one]
  have hre : (-((r : ℂ) * eip)).re = -Real.cos phiRay * r := by
    simp [Complex.mul_re, eip_re]; ring
  rw [hre, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right
    (inv_anti₀ hd (distPhi_le_norm_sub_ray (le_of_lt hr))) (Real.exp_pos _).le

/-- Exact derivative of `A_phi(w) = exp(w) * S_phi_inner(w)` on `OmegaPhi`: `A_phi'(w) = exp(w) / w`. -/
theorem hasDerivAt_A_phi {w₀ : ℂ} (hw₀ : w₀ ∈ OmegaPhi) :
    HasDerivAt A_phi (Complex.exp w₀ / w₀) w₀ := by
  set d : ℝ := distPhi w₀ / 2
  have hd : 0 < d := half_pos (distPhi_pos hw₀)
  have hne_ball : ∀ w ∈ Metric.ball w₀ d, ∀ r : ℝ, 0 ≤ r → d ≤ ‖w - (r : ℂ) * eip‖ := by
    intro w hw r hr
    have hdist : ‖w - w₀‖ < d := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have htri : ‖w₀ - (r : ℂ) * eip‖ ≤ ‖w - (r : ℂ) * eip‖ + ‖w - w₀‖ := by
      have h := norm_add_le (w - (r : ℂ) * eip) (w₀ - w)
      rw [norm_sub_rev w₀ w] at h
      have heq : (w - (r : ℂ) * eip) + (w₀ - w) = w₀ - (r : ℂ) * eip := by ring
      rwa [heq] at h
    have hbase := distPhi_le_norm_sub_ray (w := w₀) hr
    dsimp only [d] at *; linarith
  -- Differentiate `S_phi_inner` under the integral sign first!
  let F : ℂ → ℝ → ℂ := fun w r => Complex.exp (-((r : ℂ) * eip)) / (w - (r : ℂ) * eip) * eip
  let F' : ℂ → ℝ → ℂ := fun w r => -Complex.exp (-((r : ℂ) * eip)) / (w - (r : ℂ) * eip) ^ 2 * eip
  let bound : ℝ → ℝ := fun r => d⁻¹ ^ 2 * Real.exp (-Real.cos phiRay * r)
  have hbound_int : IntegrableOn bound (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -Real.cos phiRay < 0 by linarith [cos_phiRay_pos]) 0).const_mul _
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds w₀ hd] with w hw
    have hc : ContinuousOn (F w) (Set.Ioi 0) := by
      refine ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const).neg).continuousOn.div
        (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_).mul continuousOn_const
      intro r hr
      exact norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball w hw r (le_of_lt hr)))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hF'_meas : AEStronglyMeasurable (F' w₀) (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (F' w₀) (Set.Ioi 0) := by
      refine (((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const).neg).neg).continuousOn.div
        ((continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).pow 2).continuousOn ?_).mul continuousOn_const
      intro r hr
      exact pow_ne_zero 2 (norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball w₀ (Metric.mem_ball_self hd) r (le_of_lt hr))))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hbound_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioi 0)), ∀ w ∈ Metric.ball w₀ d, ‖F' w r‖ ≤ bound r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr w hw
    dsimp only [F', bound]
    rw [norm_mul, norm_div, norm_neg, Complex.norm_exp, norm_pow, norm_eip, mul_one]
    have hre : (-((r : ℂ) * eip)).re = -Real.cos phiRay * r := by
      simp [Complex.mul_re, eip_re]; ring
    rw [hre, div_eq_inv_mul, ← inv_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (inv_anti₀ hd (hne_ball w hw r (le_of_lt hr))) 2) (Real.exp_pos _).le
  have hdiff_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioi 0)), ∀ w ∈ Metric.ball w₀ d,
      HasDerivAt (F · r) (F' w r) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr w hw
    have hne : w - (r : ℂ) * eip ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball w hw r (le_of_lt hr)))
    have hsub : HasDerivAt (fun z : ℂ => z - (r : ℂ) * eip) 1 w := by
      simpa using (hasDerivAt_id w).sub_const ((r : ℂ) * eip)
    have hinv : HasDerivAt (fun z : ℂ => (z - (r : ℂ) * eip)⁻¹) (-(1 : ℂ) / (w - (r : ℂ) * eip) ^ 2) w :=
      hsub.inv hne
    have htot := (hinv.const_mul (Complex.exp (-((r : ℂ) * eip)))).mul_const eip
    refine htot.congr_of_eventuallyEq (Eventually.of_forall fun z => by dsimp [F]; ring) |>.congr_deriv ?_
    dsimp only [F']; ring
  have ⟨hF'_int, hderiv_S⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ hd)
      hF_meas (integrableOn_S_phi_integrand hw₀) hF'_meas hbound_ae hbound_int hdiff_ae
  -- Combine `A_phi = exp * S_phi_inner` and evaluate the integral via FTC!
  have hA_deriv : HasDerivAt A_phi
      (Complex.exp w₀ * (S_phi_inner w₀ + ∫ r in Set.Ioi (0 : ℝ), F' w₀ r)) w₀ := by
    have h := (Complex.hasDerivAt_exp w₀).fun_mul hderiv_S
    refine h.congr_deriv ?_
    dsimp only [S_phi_inner, F]; ring
  have hftc : (∫ r in Set.Ioi (0 : ℝ), Complex.exp w₀ * (F w₀ r + F' w₀ r)) = Complex.exp w₀ / w₀ := by
    have hr_deriv : ∀ r ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun x : ℝ => -Complex.exp (w₀ - (x : ℂ) * eip) / (w₀ - (x : ℂ) * eip))
          (Complex.exp w₀ * (F w₀ r + F' w₀ r)) r := by
      intro r hr
      have hne : w₀ - (r : ℂ) * eip ≠ 0 :=
        norm_pos_iff.mp (lt_of_lt_of_le hd (hne_ball w₀ (Metric.mem_ball_self hd) r hr))
      have hlin : HasDerivAt (fun x : ℝ => w₀ - (x : ℂ) * eip) (-eip) r := by
        simpa using ((hasDerivAt_id r).ofReal_comp.mul_const eip).const_sub w₀
      have hnum : HasDerivAt (fun x : ℝ => -Complex.exp (w₀ - (x : ℂ) * eip))
          (-(Complex.exp (w₀ - (r : ℂ) * eip) * (-eip))) r := hlin.cexp.fun_neg
      have hq := hnum.div hlin hne
      refine hq.congr_deriv ?_
      dsimp only [F, F']
      have hexp_split : Complex.exp (w₀ - (r : ℂ) * eip) =
          Complex.exp w₀ * Complex.exp (-((r : ℂ) * eip)) := by
        rw [← Complex.exp_add]; congr 1
      rw [hexp_split]
      field_simp [hne]
      ring
    have htend : Tendsto (fun x : ℝ => -Complex.exp (w₀ - (x : ℂ) * eip) / (w₀ - (x : ℂ) * eip))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun x : ℝ => (Real.exp w₀.re / d) * Real.exp (-Real.cos phiRay * x)) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
        rw [norm_div, norm_neg, Complex.norm_exp]
        have hre : (w₀ - (x : ℂ) * eip).re = w₀.re + (-Real.cos phiRay * x) := by
          simp [Complex.mul_re, eip_re]; ring
        rw [hre, Real.exp_add, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left (by positivity) hd (hne_ball w₀ (Metric.mem_ball_self hd) x hx)
      · have h1 : Tendsto (fun x : ℝ => -Real.cos phiRay * x) atTop atBot :=
          (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop cos_phiRay_pos)).congr fun x => by simp
        simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (Real.exp w₀.re / d)
    have hint_sum : IntegrableOn (fun r : ℝ => Complex.exp w₀ * (F w₀ r + F' w₀ r)) (Set.Ioi 0) :=
      ((integrableOn_S_phi_integrand hw₀).add hF'_int).const_mul _
    have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hr_deriv hint_sum htend
    simpa [neg_div] using hval
  rw [integral_const_mul, integral_add (integrableOn_S_phi_integrand hw₀) hF'_int] at hftc
  change Complex.exp w₀ * (S_phi_inner w₀ + ∫ r in Set.Ioi (0 : ℝ), F' w₀ r) = Complex.exp w₀ / w₀ at hftc
  rwa [hftc] at hA_deriv

theorem differentiableOn_S_phi_inner : DifferentiableOn ℂ S_phi_inner OmegaPhi := by
  intro w hw
  have hA : DifferentiableAt ℂ A_phi w := (hasDerivAt_A_phi hw).differentiableAt
  have hfun : S_phi_inner = fun z => Complex.exp (-z) * A_phi z := by
    ext z; dsimp only [A_phi]
    rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rw [hfun]
  exact ((Complex.differentiable_exp.comp differentiable_id.neg).differentiableAt.mul hA).differentiableWithinAt

theorem differentiableOn_S_phi : DifferentiableOn ℂ S_phi OmegaPhi :=
  differentiableOn_id.fun_mul differentiableOn_S_phi_inner

/-- **Exact Identity `A_phi(w) = Ei_complex(w) + i * π`** on all of `OmegaPhi`! -/
theorem A_phi_eq_Ei_add_I_pi {w : ℂ} (hw : w ∈ OmegaPhi) :
    A_phi w = Ei_complex w + I * (Real.pi : ℂ) := by
  let h : ℂ → ℂ := fun z => A_phi z - Ei_complex z
  have hh_deriv : ∀ z ∈ OmegaPhi, HasDerivAt h 0 z := by
    intro z hz
    have h1 := hasDerivAt_A_phi hz
    have h2 := hasDerivAt_Ei_complex (OmegaPhi_subset_slitPlane hz)
    have hsub := h1.fun_sub h2
    rwa [sub_self] at hsub
  -- Use `intervalIntegral.integral_eq_sub_of_hasDerivAt` directly for `h z₂ - h z₁ = 0`!
  have hseg : ∀ z₁ z₂ : ℂ, (∀ t ∈ Set.Icc (0 : ℝ) 1, z₁ + (t : ℂ) * (z₂ - z₁) ∈ OmegaPhi) →
      h z₁ = h z₂ := by
    intro z₁ z₂ hline
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun τ : ℝ => h (z₁ + (τ : ℂ) * (z₂ - z₁))) 0 t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hlin : HasDerivAt (fun τ : ℝ => z₁ + (τ : ℂ) * (z₂ - z₁)) (z₂ - z₁) t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (z₂ - z₁)).const_add z₁
      have hc := ((hh_deriv _ (hline t ht)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hlin
      simpa [Function.comp_def] using hc
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv intervalIntegrable_const
    simp only [intervalIntegral.integral_zero, Complex.ofReal_one, one_mul, add_sub_cancel,
      Complex.ofReal_zero, zero_mul, add_zero] at hftc
    exact (sub_eq_zero.mp hftc.symm).symm
  -- Connect every `z ∈ OmegaPhi` to `1 - I` in at most 1 segment
  have h1I_im : ((1 : ℂ) - I).im < 0 := by simp
  have h1I_d : 0 < dPhi ((1 : ℂ) - I) := by
    dsimp [dPhi]; simp; linarith [sin_phiRay_pos, cos_phiRay_pos]
  have hconst_1I : ∀ z ∈ OmegaPhi, h z = h ((1 : ℂ) - I) := by
    intro z hz
    rcases hz with him | hd
    · refine hseg z ((1 : ℂ) - I) fun t ht => Or.inl ?_
      have hre_im : (z + (t : ℂ) * ((1 : ℂ) - I - z)).im = (1 - t) * z.im + t * (-1) := by
        simp; ring
      rw [hre_im]
      by_cases ht0 : t = 0
      · subst ht0; linarith
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        nlinarith [ht.2]
    · refine hseg z ((1 : ℂ) - I) fun t ht => Or.inr ?_
      have hd_lin : dPhi (z + (t : ℂ) * ((1 : ℂ) - I - z)) =
          (1 - t) * dPhi z + t * dPhi ((1 : ℂ) - I) := by
        dsimp [dPhi]; simp; ring
      rw [hd_lin]
      by_cases ht0 : t = 0
      · subst ht0; linarith
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        nlinarith [ht.2]
  -- Evaluate `h (1 - I)` by taking the limit along `z = -x - I` (`x → +∞`), which lies in `{im < 0} ⊆ OmegaPhi`!
  have hlim_A : Tendsto (fun x : ℝ => A_phi (-(x : ℂ) - I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => (1 / Real.cos phiRay) * Real.exp (-x)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x _
      dsimp only [A_phi, S_phi_inner]
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(x : ℂ) - I).re = -x := by simp
      rw [hre]
      have hd1 : (1 : ℝ) ≤ distPhi (-(x : ℂ) - I) := by
        have : -(-(x : ℂ) - I).im = 1 := by simp
        exact this ▸ le_max_left _ _
      have hint_le : ‖∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (-((r : ℂ) * eip)) / (-(x : ℂ) - I - (r : ℂ) * eip) * eip‖ ≤
          1 / Real.cos phiRay := by
        calc ‖∫ r in Set.Ioi (0 : ℝ),
              Complex.exp (-((r : ℂ) * eip)) / (-(x : ℂ) - I - (r : ℂ) * eip) * eip‖
            ≤ ∫ r in Set.Ioi (0 : ℝ),
              ‖Complex.exp (-((r : ℂ) * eip)) / (-(x : ℂ) - I - (r : ℂ) * eip) * eip‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ r in Set.Ioi (0 : ℝ), Real.exp (-Real.cos phiRay * r) := by
              refine setIntegral_mono_on
                (integrableOn_S_phi_integrand (Or.inl (by simp))).norm
                (integrableOn_exp_mul_Ioi (show -Real.cos phiRay < 0 by linarith [cos_phiRay_pos]) 0)
                measurableSet_Ioi fun r hr => ?_
              rw [norm_mul, norm_div, Complex.norm_exp, norm_eip, mul_one]
              have hre' : (-((r : ℂ) * eip)).re = -Real.cos phiRay * r := by
                simp [Complex.mul_re, eip_re]; ring
              rw [hre']
              exact div_le_self (Real.exp_pos _).le (hd1.trans (distPhi_le_norm_sub_ray (le_of_lt hr)))
          _ = 1 / Real.cos phiRay := by
              simpa [pow_zero, one_mul, Nat.factorial_zero, pow_one] using
                integral_Ioi_pow_mul_exp_neg cos_phiRay_pos 0
      calc Real.exp (-x) * ‖∫ r in Set.Ioi (0 : ℝ),
            Complex.exp (-((r : ℂ) * eip)) / (-(x : ℂ) - I - (r : ℂ) * eip) * eip‖
          ≤ Real.exp (-x) * (1 / Real.cos phiRay) :=
            mul_le_mul_of_nonneg_left hint_le (Real.exp_pos _).le
        _ = (1 / Real.cos phiRay) * Real.exp (-x) := mul_comm _ _
    · simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (1 / Real.cos phiRay)
  have hlim_Ei : Tendsto (fun x : ℝ => Ei_complex (-(x : ℂ) - I)) atTop (𝓝 (-I * (Real.pi : ℂ))) := by
    have hE1_lim : Tendsto (fun x : ℝ => E1_complex ((x : ℂ) + I)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun x : ℝ => Real.exp (-x)) ?_
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      have hb := norm_E1_complex_le_E1 (z := (x : ℂ) + I) (by simp; linarith)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at hb
      exact hb.trans ((E1_le_exp_div (by linarith)).trans (div_le_self (Real.exp_pos _).le hx))
    have hsub := hE1_lim.neg.sub_const (I * (Real.pi : ℂ))
    simp only [neg_zero, zero_sub] at hsub
    have hneg_eq : -(I * (Real.pi : ℂ)) = -I * (Real.pi : ℂ) := by ring
    rw [hneg_eq] at hsub
    refine hsub.congr fun x => ?_
    rw [Ei_complex_eq_neg_E1_sub_I_pi (by simp)]
    congr 2; ring
  have hlim_h : Tendsto (fun x : ℝ => h (-(x : ℂ) - I)) atTop (𝓝 (I * (Real.pi : ℂ))) := by
    have hsub := hlim_A.sub hlim_Ei
    simpa [h] using hsub
  have hconst_lim : Tendsto (fun x : ℝ => h (-(x : ℂ) - I)) atTop (𝓝 (h ((1 : ℂ) - I))) :=
    tendsto_const_nhds.congr fun x => (hconst_1I (-(x : ℂ) - I) (Or.inl (by simp))).symm
  have hval_1I : h ((1 : ℂ) - I) = I * (Real.pi : ℂ) := tendsto_nhds_unique hconst_lim hlim_h
  have hval_w : h w = I * (Real.pi : ℂ) := (hconst_1I w hw).trans hval_1I
  dsimp only [h] at hval_w
  linear_combination hval_w

/-- **Exact Gevrey-1 Asymptotic Remainder Bound for `S_phi(w)`** on all of `OmegaPhi`!
For every `N : ℕ` and every `w ∈ OmegaPhi`,
`‖S_phi w - ∑ n < N, (n! : ℂ) / w^n‖ ≤ ‖w‖ / (distPhi w * (cos phiRay)^(N+1)) * N! / ‖w‖^N`. -/
theorem norm_S_phi_sub_trunc_le (N : ℕ) {w : ℂ} (hw : w ∈ OmegaPhi) :
    ‖S_phi w - ∑ n ∈ Finset.range N, (n.factorial : ℂ) / w ^ n‖ ≤
      ‖w‖ / (distPhi w * Real.cos phiRay ^ (N + 1)) * (N.factorial : ℝ) / ‖w‖ ^ N := by
  have hd : 0 < distPhi w := distPhi_pos hw
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero (OmegaPhi_subset_slitPlane hw)
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  -- Finite geometric identity: `w / (w - z) - ∑_{n < N} (z/w)^n = z^N / (w^{N-1} * (w - z))`
  -- Equivalently, multiplying by `w`: `w / (w - z) - ∑_{n < N} z^n / w^n = (z^N / w^N) * (w / (w - z))`!
  have hgeom : ∀ z : ℂ, w - z ≠ 0 →
      w / (w - z) - ∑ n ∈ Finset.range N, z ^ n / w ^ n = (z ^ N / w ^ N) * (w / (w - z)) := by
    intro z hne
    have hsum : (∑ n ∈ Finset.range N, (z / w) ^ n) * (1 - z / w) = 1 - (z / w) ^ N := by
      have := geom_sum_mul (z / w) N
      linear_combination -this
    have h1sub : 1 - z / w = (w - z) / w := by field_simp [hw0]
    have h1sub_ne : 1 - z / w ≠ 0 := by rw [h1sub]; exact div_ne_zero hne hw0
    have hsum' : ∑ n ∈ Finset.range N, z ^ n / w ^ n = (1 - (z / w) ^ N) / (1 - z / w) := by
      simp_rw [← div_pow]
      exact eq_div_of_mul_eq h1sub_ne hsum
    rw [hsum', h1sub, div_pow]
    field_simp [hw0, hne, pow_ne_zero N hw0]
    ring
  -- Express `S_phi w - ∑_{n < N} n! / w^n` as a single integral over `Ioi 0`!
  have hS_int : S_phi w =
      ∫ r in Set.Ioi (0 : ℝ), w / (w - (r : ℂ) * eip) * Complex.exp (-((r : ℂ) * eip)) * eip := by
    dsimp only [S_phi, S_phi_inner]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => by ring
  have hint_term : ∀ n : ℕ, IntegrableOn
      (fun r : ℝ => (((r : ℂ) * eip) ^ n / w ^ n) * Complex.exp (-((r : ℂ) * eip)) * eip) (Set.Ioi 0) := by
    intro n
    have h1 : IntegrableOn
        (fun r : ℝ => (w ^ n)⁻¹ * (((r : ℂ) * eip) ^ n * Complex.exp (-((r : ℂ) * eip)) * eip))
        (Set.Ioi 0) := (integrableOn_ray_monomial n).const_mul (w ^ n)⁻¹
    exact h1.congr_fun (fun r _ => by ring) measurableSet_Ioi
  have hsum_int_aux : ∀ M : ℕ,
      IntegrableOn (fun r : ℝ => ∑ n ∈ Finset.range M,
        (((r : ℂ) * eip) ^ n / w ^ n) * Complex.exp (-((r : ℂ) * eip)) * eip) (Set.Ioi 0) ∧
      (∑ n ∈ Finset.range M, (n.factorial : ℂ) / w ^ n) =
        ∫ r in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.range M,
          (((r : ℂ) * eip) ^ n / w ^ n) * Complex.exp (-((r : ℂ) * eip)) * eip := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hadd_int : IntegrableOn (fun r : ℝ =>
          (∑ n ∈ Finset.range M, (((r : ℂ) * eip) ^ n / w ^ n) * Complex.exp (-((r : ℂ) * eip)) * eip) +
          (((r : ℂ) * eip) ^ M / w ^ M) * Complex.exp (-((r : ℂ) * eip)) * eip) (Set.Ioi 0) :=
        ih.1.add (hint_term M)
      refine ⟨hadd_int.congr_fun (fun r _ => by simp [Finset.sum_range_succ]) measurableSet_Ioi, ?_⟩
      rw [Finset.sum_range_succ, ih.2]
      have hM : (M.factorial : ℂ) / w ^ M =
          ∫ r in Set.Ioi (0 : ℝ), (((r : ℂ) * eip) ^ M / w ^ M) * Complex.exp (-((r : ℂ) * eip)) * eip := by
        rw [div_eq_inv_mul, ← integral_Ioi_ray_monomial M, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun r _ => by ring
      rw [hM, ← integral_add ih.1 (hint_term M)]
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => by simp [Finset.sum_range_succ]
  have hsum_int : (∑ n ∈ Finset.range N, (n.factorial : ℂ) / w ^ n) =
      ∫ r in Set.Ioi (0 : ℝ),
        (∑ n ∈ Finset.range N, ((r : ℂ) * eip) ^ n / w ^ n) * Complex.exp (-((r : ℂ) * eip)) * eip := by
    rw [(hsum_int_aux N).2]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => by rw [Finset.sum_mul, Finset.sum_mul]
  have hint_S : IntegrableOn
      (fun r : ℝ => w / (w - (r : ℂ) * eip) * Complex.exp (-((r : ℂ) * eip)) * eip) (Set.Ioi 0) := by
    have h1 : IntegrableOn
        (fun r : ℝ => w * (Complex.exp (-((r : ℂ) * eip)) / (w - (r : ℂ) * eip) * eip))
        (Set.Ioi 0) := (integrableOn_S_phi_integrand hw).const_mul w
    exact h1.congr_fun (fun r _ => by ring) measurableSet_Ioi
  have hint_sum : IntegrableOn
      (fun r : ℝ => (∑ n ∈ Finset.range N, ((r : ℂ) * eip) ^ n / w ^ n) *
        Complex.exp (-((r : ℂ) * eip)) * eip) (Set.Ioi 0) :=
    (hsum_int_aux N).1.congr_fun (fun r _ => by rw [Finset.sum_mul, Finset.sum_mul]) measurableSet_Ioi
  have hdiff_eq : S_phi w - ∑ n ∈ Finset.range N, (n.factorial : ℂ) / w ^ n =
      ∫ r in Set.Ioi (0 : ℝ),
        (((r : ℂ) * eip) ^ N / w ^ N) * (w / (w - (r : ℂ) * eip)) *
          Complex.exp (-((r : ℂ) * eip)) * eip := by
    rw [hS_int, hsum_int, ← integral_sub hint_S hint_sum]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hne : w - (r : ℂ) * eip ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le hd (distPhi_le_norm_sub_ray (le_of_lt hr)))
    have hg := hgeom ((r : ℂ) * eip) hne
    calc w / (w - (r : ℂ) * eip) * Complex.exp (-((r : ℂ) * eip)) * eip -
          (∑ n ∈ Finset.range N, ((r : ℂ) * eip) ^ n / w ^ n) * Complex.exp (-((r : ℂ) * eip)) * eip
        = (w / (w - (r : ℂ) * eip) - ∑ n ∈ Finset.range N, ((r : ℂ) * eip) ^ n / w ^ n) *
            Complex.exp (-((r : ℂ) * eip)) * eip := by ring
      _ = (((r : ℂ) * eip) ^ N / w ^ N) * (w / (w - (r : ℂ) * eip)) *
            Complex.exp (-((r : ℂ) * eip)) * eip := by rw [hg]
  rw [hdiff_eq]
  have hint_rem : IntegrableOn
      (fun r : ℝ => (((r : ℂ) * eip) ^ N / w ^ N) * (w / (w - (r : ℂ) * eip)) *
        Complex.exp (-((r : ℂ) * eip)) * eip) (Set.Ioi 0) := by
    refine (hint_S.sub hint_sum).congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hne : w - (r : ℂ) * eip ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le hd (distPhi_le_norm_sub_ray (le_of_lt hr)))
    have hg := hgeom ((r : ℂ) * eip) hne
    calc w / (w - (r : ℂ) * eip) * Complex.exp (-((r : ℂ) * eip)) * eip -
          (∑ n ∈ Finset.range N, ((r : ℂ) * eip) ^ n / w ^ n) * Complex.exp (-((r : ℂ) * eip)) * eip
        = (w / (w - (r : ℂ) * eip) - ∑ n ∈ Finset.range N, ((r : ℂ) * eip) ^ n / w ^ n) *
            Complex.exp (-((r : ℂ) * eip)) * eip := by ring
      _ = (((r : ℂ) * eip) ^ N / w ^ N) * (w / (w - (r : ℂ) * eip)) *
            Complex.exp (-((r : ℂ) * eip)) * eip := by rw [hg]
  have hreal_int : IntegrableOn (fun r : ℝ =>
      (‖w‖ / (distPhi w * ‖w‖ ^ N)) * (r ^ N * Real.exp (-Real.cos phiRay * r))) (Set.Ioi 0) := by
    have h1 : IntegrableOn
        (fun r : ℝ => ‖((r : ℂ) * eip) ^ N * Complex.exp (-((r : ℂ) * eip)) * eip‖) (Set.Ioi 0) :=
      (integrableOn_ray_monomial N).norm
    have h2 : IntegrableOn (fun r : ℝ => r ^ N * Real.exp (-Real.cos phiRay * r)) (Set.Ioi 0) := by
      refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioi
      have hr0 : 0 < r := hr
      dsimp only
      rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le,
        norm_eip, mul_one, mul_one, Complex.norm_exp]
      have hre : (-((r : ℂ) * eip)).re = -Real.cos phiRay * r := by
        simp [Complex.mul_re, eip_re]; ring
      rw [hre]
    exact h2.const_mul _
  calc ‖∫ r in Set.Ioi (0 : ℝ),
        (((r : ℂ) * eip) ^ N / w ^ N) * (w / (w - (r : ℂ) * eip)) *
          Complex.exp (-((r : ℂ) * eip)) * eip‖
      ≤ ∫ r in Set.Ioi (0 : ℝ),
          ‖(((r : ℂ) * eip) ^ N / w ^ N) * (w / (w - (r : ℂ) * eip)) *
            Complex.exp (-((r : ℂ) * eip)) * eip‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Set.Ioi (0 : ℝ),
          (‖w‖ / (distPhi w * ‖w‖ ^ N)) * (r ^ N * Real.exp (-Real.cos phiRay * r)) := by
        refine setIntegral_mono_on hint_rem.norm hreal_int measurableSet_Ioi fun r hr => ?_
        have hr0 : 0 < r := hr
        rw [norm_mul, norm_mul, norm_mul, norm_div, norm_div, norm_pow, norm_pow, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_eip, mul_one, mul_one, Complex.norm_exp]
        have hre : (-((r : ℂ) * eip)).re = -Real.cos phiRay * r := by
          simp [Complex.mul_re, eip_re]; ring
        rw [hre]
        have hdiv : ‖w‖ / ‖w - (r : ℂ) * eip‖ ≤ ‖w‖ / distPhi w :=
          div_le_div_of_nonneg_left hw_pos.le hd (distPhi_le_norm_sub_ray hr0.le)
        calc r ^ N / ‖w‖ ^ N * (‖w‖ / ‖w - (r : ℂ) * eip‖) * Real.exp (-Real.cos phiRay * r)
            ≤ r ^ N / ‖w‖ ^ N * (‖w‖ / distPhi w) * Real.exp (-Real.cos phiRay * r) := by gcongr
          _ = (‖w‖ / (distPhi w * ‖w‖ ^ N)) * (r ^ N * Real.exp (-Real.cos phiRay * r)) := by ring
    _ = (‖w‖ / (distPhi w * ‖w‖ ^ N)) *
          ∫ r in Set.Ioi (0 : ℝ), r ^ N * Real.exp (-Real.cos phiRay * r) := integral_const_mul _ _
    _ = (‖w‖ / (distPhi w * ‖w‖ ^ N)) * ((N.factorial : ℝ) / Real.cos phiRay ^ (N + 1)) := by
        rw [integral_Ioi_pow_mul_exp_neg cos_phiRay_pos N]
    _ = ‖w‖ / (distPhi w * Real.cos phiRay ^ (N + 1)) * (N.factorial : ℝ) / ‖w‖ ^ N := by ring

/-- Special case `N = 1`: uniform bound `‖S_phi w - 1‖ ≤ 1 / (distPhi w * cos phiRay ^ 2)` on `OmegaPhi`! -/
lemma norm_S_phi_sub_one_le {w : ℂ} (hw : w ∈ OmegaPhi) :
    ‖S_phi w - 1‖ ≤ 1 / (distPhi w * Real.cos phiRay ^ 2) := by
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero (OmegaPhi_subset_slitPlane hw))
  have h1 := norm_S_phi_sub_trunc_le 1 hw
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, pow_zero,
    div_one, Nat.factorial_one, pow_one, mul_one] at h1
  calc ‖S_phi w - 1‖ ≤ ‖w‖ / (distPhi w * Real.cos phiRay ^ 2) / ‖w‖ := h1
    _ = 1 / (distPhi w * Real.cos phiRay ^ 2) := by field_simp [hw_pos.ne']

/-! ### 3. Implicit Inverse `w_plus`, `F_plus`, and Gevrey-1 Log-Power Expansion -/

/-! #### 3a. Analytic Contraction, `Ei(w_plus v) + iπ = exp v`, and Holomorphicity of `w_plus`, `F_plus` -/

/-- `distPhi` is `1`-Lipschitz: `distPhi v - ‖w - v‖ ≤ distPhi w`. -/
lemma distPhi_sub_norm_le (v w : ℂ) : distPhi v - ‖w - v‖ ≤ distPhi w := by
  have h1 : -v.im - ‖w - v‖ ≤ -w.im := by
    have := (abs_le.mp ((Complex.abs_im_le_norm (w - v)))).2
    simp only [Complex.sub_im] at this
    linarith
  have h2 : dPhi v - ‖w - v‖ ≤ dPhi w := by
    let rot : ℂ := Complex.exp (-(phiRay : ℂ) * I)
    have hrot_norm : ‖rot‖ = 1 := by dsimp [rot]; rw [Complex.norm_exp]; simp
    have hre_rot : rot.re = Real.cos phiRay := by
      dsimp [rot]
      have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    have him_rot : rot.im = -Real.sin phiRay := by
      dsimp [rot]
      have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    have him_diff : (rot * (w - v)).im = -(dPhi w - dPhi v) := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, hre_rot, him_rot, dPhi]
      ring
    have habs := Complex.abs_im_le_norm (rot * (w - v))
    rw [him_diff, abs_neg, norm_mul, hrot_norm, one_mul] at habs
    linarith [(abs_le.mp habs).1]
  dsimp only [distPhi]
  rw [sub_le_iff_le_add]
  exact max_le (by linarith [le_max_left (-w.im) (dPhi w)])
    (by linarith [le_max_right (-w.im) (dPhi w)])

/-- `distPhi w ≤ ‖w‖` for every `w : ℂ`. -/
lemma distPhi_le_norm (w : ℂ) : distPhi w ≤ ‖w‖ := by
  have h1 : -w.im ≤ ‖w‖ := (neg_le_abs w.im).trans (Complex.abs_im_le_norm w)
  have h2 : dPhi w ≤ ‖w‖ := by
    let rot : ℂ := Complex.exp (-(phiRay : ℂ) * I)
    have hrot_norm : ‖rot‖ = 1 := by dsimp [rot]; rw [Complex.norm_exp]; simp
    have hre_rot : rot.re = Real.cos phiRay := by
      dsimp [rot]
      have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    have him_rot : rot.im = -Real.sin phiRay := by
      dsimp [rot]
      have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    have him : (rot * w).im = -dPhi w := by
      simp only [Complex.mul_im, hre_rot, him_rot, dPhi]; ring
    have habs := Complex.abs_im_le_norm (rot * w)
    rw [him, abs_neg, norm_mul, hrot_norm, one_mul] at habs
    exact (le_abs_self _).trans habs
  exact max_le h1 h2

/-- Cauchy derivative bound on `S_phi`: `‖deriv S_phi w‖ ≤ 4 / (distPhi w ^ 2 * cos phiRay ^ 2)` on `OmegaPhi`. -/
lemma norm_deriv_S_phi_le {w : ℂ} (hw : w ∈ OmegaPhi) :
    ‖deriv S_phi w‖ ≤ 4 / (distPhi w ^ 2 * Real.cos phiRay ^ 2) := by
  have hd : 0 < distPhi w := distPhi_pos hw
  have hr : 0 < distPhi w / 2 := half_pos hd
  have hcb_sub : Metric.closedBall w (distPhi w / 2) ⊆ OmegaPhi := by
    intro z hz
    have hdist : ‖z - w‖ ≤ distPhi w / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hdz : distPhi w / 2 ≤ distPhi z := by linarith [distPhi_sub_norm_le w z]
    have hdz_pos : 0 < distPhi z := lt_of_lt_of_le hr hdz
    rcases lt_max_iff.mp hdz_pos with him | hd'
    · exact Or.inl (by linarith)
    · exact Or.inr hd'
  have hf_diff : DifferentiableOn ℂ (fun z => S_phi z - 1) (Metric.closedBall w (distPhi w / 2)) :=
    (differentiableOn_S_phi.mono hcb_sub).sub (differentiableOn_const 1)
  have hf_dc : DiffContOnCl ℂ (fun z => S_phi z - 1) (Metric.ball w (distPhi w / 2)) :=
    ⟨hf_diff.mono Metric.ball_subset_closedBall, hf_diff.continuousOn.mono Metric.closure_ball_subset_closedBall⟩
  have hbound : ∀ z ∈ Metric.sphere w (distPhi w / 2),
      ‖S_phi z - 1‖ ≤ 2 / (distPhi w * Real.cos phiRay ^ 2) := by
    intro z hz
    have hcb : z ∈ Metric.closedBall w (distPhi w / 2) := Metric.sphere_subset_closedBall hz
    have hdist : ‖z - w‖ ≤ distPhi w / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hcb
    have hdz : distPhi w / 2 ≤ distPhi z := by linarith [distPhi_sub_norm_le w z]
    have hcos2 : 0 < Real.cos phiRay ^ 2 := pow_pos cos_phiRay_pos 2
    calc ‖S_phi z - 1‖ ≤ 1 / (distPhi z * Real.cos phiRay ^ 2) := norm_S_phi_sub_one_le (hcb_sub hcb)
      _ ≤ 1 / ((distPhi w / 2) * Real.cos phiRay ^ 2) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith)
      _ = 2 / (distPhi w * Real.cos phiRay ^ 2) := by ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (n := 1) (R := distPhi w / 2) (C := 2 / (distPhi w * Real.cos phiRay ^ 2)) hr hf_dc hbound
  have hderiv_eq : iteratedDeriv 1 (fun z => S_phi z - 1) w = deriv S_phi w := by
    rw [iteratedDeriv_one]
    exact ((differentiableOn_S_phi.differentiableAt (isOpen_OmegaPhi.mem_nhds hw)).hasDerivAt.sub_const 1).deriv
  rw [hderiv_eq, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at hcauchy
  calc ‖deriv S_phi w‖ ≤ (2 / (distPhi w * Real.cos phiRay ^ 2)) / (distPhi w / 2) := hcauchy
    _ = 4 / (distPhi w ^ 2 * Real.cos phiRay ^ 2) := by
        field_simp [hd.ne', cos_phiRay_pos.ne']; ring

/-- Elementary logarithm perturbation bound: for `‖u‖ ≤ 1/2`, `‖Complex.log (1 + u)‖ ≤ 2 * ‖u‖`. -/
lemma norm_clog_one_add_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u)‖ ≤ 2 * ‖u‖ := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun τ : ℝ => Complex.log (1 + (τ : ℂ) * u)) (u / (1 + (t : ℂ) * u)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hre : 0 < (1 + (t : ℂ) * u).re := by
      have habs : ‖(t : ℂ) * u‖ ≤ 1 / 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
        nlinarith [ht.2, norm_nonneg u]
      have hre_le := (abs_le.mp ((Complex.abs_re_le_norm _).trans habs)).1
      simp only [Complex.add_re, Complex.one_re]; linarith
    have hlin : HasDerivAt (fun τ : ℝ => 1 + (τ : ℂ) * u) u t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const u).const_add (1 : ℂ)
    have hlog := (Complex.hasDerivAt_log (Or.inl hre)).comp t hlin
    refine hlog.congr_deriv ?_; ring
  have hcont : ContinuousOn (fun t : ℝ => u / (1 + (t : ℂ) * u)) (Set.uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.div (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have habs : ‖(t : ℂ) * u‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      nlinarith [ht.2, norm_nonneg u]
    have hre : 1 / 2 ≤ (1 + (t : ℂ) * u).re := by
      have hre_le := (abs_le.mp ((Complex.abs_re_le_norm _).trans habs)).1
      simp only [Complex.add_re, Complex.one_re]; linarith
    intro h0; have := congr_arg Complex.re h0; simp only [Complex.zero_re] at this; linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero, Complex.log_one,
    sub_zero] at hftc
  rw [← hftc]
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖u / (1 + (t : ℂ) * u)‖ ≤ 2 * ‖u‖ := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have habs : ‖(t : ℂ) * u‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      nlinarith [ht.2, norm_nonneg u]
    have hden : 1 / 2 ≤ ‖1 + (t : ℂ) * u‖ := by
      have hre_le := (abs_le.mp ((Complex.abs_re_le_norm _).trans habs)).1
      have hre : 1 / 2 ≤ (1 + (t : ℂ) * u).re := by simp only [Complex.add_re, Complex.one_re]; linarith
      exact hre.trans (Complex.re_le_norm _)
    rw [norm_div]
    calc ‖u‖ / ‖1 + (t : ℂ) * u‖ ≤ ‖u‖ / (1 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg u) (by norm_num) hden
      _ = 2 * ‖u‖ := by ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- Complex log difference bound: if `z₁, z₂ ∈ OmegaPhi` (or just `‖z₂ - z₁‖ ≤ ‖z₁‖ / 2` and segment stays in `slitPlane`),
`‖Complex.log z₂ - Complex.log z₁‖ ≤ 2 * ‖z₂ - z₁‖ / ‖z₁‖`. -/
lemma norm_clog_sub_le_of_segment {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hdist : ‖z₂ - z₁‖ ≤ ‖z₁‖ / 2)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, z₁ + (t : ℂ) * (z₂ - z₁) ∈ Complex.slitPlane) :
    ‖Complex.log z₂ - Complex.log z₁‖ ≤ 2 * ‖z₂ - z₁‖ / ‖z₁‖ := by
  have hz₁_pos : 0 < ‖z₁‖ := norm_pos_iff.mpr hz₁
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun τ : ℝ => Complex.log (z₁ + (τ : ℂ) * (z₂ - z₁)))
        ((z₂ - z₁) / (z₁ + (t : ℂ) * (z₂ - z₁))) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hlin : HasDerivAt (fun τ : ℝ => z₁ + (τ : ℂ) * (z₂ - z₁)) (z₂ - z₁) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (z₂ - z₁)).const_add z₁
    have hlog := (Complex.hasDerivAt_log (hseg t ht)).comp t hlin
    refine hlog.congr_deriv ?_; ring
  have hcont : ContinuousOn (fun t : ℝ => (z₂ - z₁) / (z₁ + (t : ℂ) * (z₂ - z₁))) (Set.uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.div (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact Complex.slitPlane_ne_zero (hseg t ht)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [Complex.ofReal_one, one_mul, add_sub_cancel, Complex.ofReal_zero, zero_mul, add_zero] at hftc
  rw [← hftc]
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖(z₂ - z₁) / (z₁ + (t : ℂ) * (z₂ - z₁))‖ ≤ 2 * ‖z₂ - z₁‖ / ‖z₁‖ := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hden : ‖z₁‖ / 2 ≤ ‖z₁ + (t : ℂ) * (z₂ - z₁)‖ := by
      have htri : ‖z₁‖ ≤ ‖z₁ + (t : ℂ) * (z₂ - z₁)‖ + ‖(t : ℂ) * (z₂ - z₁)‖ := by
        have h := norm_add_le (z₁ + (t : ℂ) * (z₂ - z₁)) (-((t : ℂ) * (z₂ - z₁)))
        rw [norm_neg] at h
        simpa using h
      have hmul : ‖(t : ℂ) * (z₂ - z₁)‖ ≤ ‖z₁‖ / 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
        nlinarith [ht.2, norm_nonneg (z₂ - z₁)]
      linarith
    rw [norm_div]
    calc ‖z₂ - z₁‖ / ‖z₁ + (t : ℂ) * (z₂ - z₁)‖ ≤ ‖z₂ - z₁‖ / (‖z₁‖ / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (half_pos hz₁_pos) hden
      _ = 2 * ‖z₂ - z₁‖ / ‖z₁‖ := by ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- Angular margin `δ_v = π / 48` for the domain `V_dom` of `w_plus` and `F_plus`. -/
@[expose] def deltaV : ℝ := Real.pi / 48

lemma deltaV_pos : 0 < deltaV := by dsimp [deltaV]; linarith [Real.pi_pos]

lemma sin_deltaV_pos : 0 < Real.sin deltaV :=
  Real.sin_pos_of_pos_of_lt_pi deltaV_pos (by dsimp [deltaV]; linarith [Real.pi_pos])

/-- Explicit large depth `C_v` for the deep lower half-plane and contraction margin. -/
@[expose] def C_v : ℝ := 256 / Real.cos phiRay ^ 2

lemma C_v_mul_cos_sq : C_v * Real.cos phiRay ^ 2 = 256 := by
  dsimp only [C_v]
  exact div_mul_cancel₀ 256 (pow_pos cos_phiRay_pos 2).ne'

lemma sin_deltaV_ge : (1 / 20 : ℝ) ≤ Real.sin deltaV := by
  have h1 := Real.sin_gt_sub_cube deltaV_pos
  have hpi_lo : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_hi : Real.pi < 4 := Real.pi_lt_four
  have hcube : (Real.pi / 48) ^ 3 ≤ (4 / 48 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  dsimp only [deltaV] at h1 ⊢
  linarith

lemma log_262144_le : Real.log 262144 ≤ 20 := by
  have h4 : (262144 : ℝ) ≤ Real.exp 20 := by
    have hpow := Real.pow_div_factorial_le_exp (20 : ℝ) (by norm_num) 8
    norm_num [Nat.factorial] at hpow
    linarith
  calc Real.log 262144 ≤ Real.log (Real.exp 20) := Real.log_le_log (by norm_num) h4
    _ = 20 := Real.log_exp 20

lemma C_v_ge_256 : 256 ≤ C_v := by
  dsimp only [C_v]
  have hcos1 : Real.cos phiRay ^ 2 ≤ 1 := by
    have h1 := Real.cos_le_one phiRay
    nlinarith [cos_phiRay_pos]
  rw [le_div_iff₀ (pow_pos cos_phiRay_pos 2)]
  nlinarith

lemma C_v_pos : 0 < C_v := lt_of_lt_of_le (by norm_num) C_v_ge_256

/-- Explicit large radius `R_v` for the wide sector part of `V_dom`. -/
@[expose] def R_v : ℝ := 1024 * C_v / Real.sin deltaV

lemma R_v_ge_C_v : C_v ≤ R_v := by
  dsimp only [R_v]
  have hsin1 : Real.sin deltaV ≤ 1 := Real.sin_le_one deltaV
  rw [le_div_iff₀ sin_deltaV_pos]
  nlinarith [C_v_pos]

lemma R_v_pos : 0 < R_v := lt_of_lt_of_le C_v_pos R_v_ge_C_v

/-- Unified open domain `V_dom` for `w_plus` and `F_plus`, containing both `{Im v < -C_v}`
and the wide closed sector `{‖v‖ ≥ R_v, -π + δ_v ≤ arg v ≤ φ - δ_v}`! -/
@[expose] def V_dom : Set ℂ :=
  {v : ℂ | v.im < -C_v ∨ (R_v < ‖v‖ ∧ (Real.sin deltaV / 2) * ‖v‖ < dPhi v)}

lemma isOpen_V_dom : IsOpen V_dom := by
  have h1 : IsOpen {v : ℂ | v.im < -C_v} := isOpen_lt Complex.continuous_im continuous_const
  have h2 : IsOpen {v : ℂ | R_v < ‖v‖ ∧ (Real.sin deltaV / 2) * ‖v‖ < dPhi v} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt (continuous_const.mul continuous_norm)
        ((Complex.continuous_re.mul continuous_const).sub (Complex.continuous_im.mul continuous_const)))
  exact h1.union h2

/-- Clean elementary log bound for `x ≥ 256`: `Real.log x + Real.pi + 1 ≤ x / 16`. -/
lemma log_add_pi_add_one_le {x : ℝ} (hx : 256 ≤ x) :
    Real.log x + Real.pi + 1 ≤ x / 16 := by
  have hx0 : 0 < x := by linarith
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hlog256 : Real.log 256 ≤ 8 := by
    have h4 : (256 : ℝ) ≤ Real.exp 8 := by
      have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num) 6
      simp [Finset.sum_range_succ, Nat.factorial] at hsum
      norm_num at hsum
      linarith
    calc Real.log 256 ≤ Real.log (Real.exp 8) := Real.log_le_log (by norm_num) h4
      _ = 8 := Real.log_exp 8
  have h1 : Real.log (x / 256) ≤ x / 256 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log x = Real.log (x / 256) + Real.log 256 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; ring
  linarith

/-- On `V_dom`, every `v` satisfies `C_v ≤ ‖v‖` and `v ∈ OmegaPhi` (hence `v ∈ Complex.slitPlane`). -/
lemma V_dom_norm_ge {v : ℂ} (hv : v ∈ V_dom) : C_v ≤ ‖v‖ := by
  rcases hv with him | ⟨hr, _⟩
  · have h1 : -v.im ≤ ‖v‖ := (neg_le_abs v.im).trans (Complex.abs_im_le_norm v)
    linarith
  · exact R_v_ge_C_v.trans hr.le

lemma V_dom_subset_OmegaPhi : V_dom ⊆ OmegaPhi := by
  intro v hv
  rcases hv with him | ⟨hr, hd⟩
  · exact Or.inl (by linarith [C_v_pos])
  · exact Or.inr (lt_of_le_of_lt (mul_nonneg (half_pos sin_deltaV_pos).le (norm_nonneg v)) hd)

/-- Every `w ∈ closedBall (v + log v) 1` for `v ∈ V_dom` stays deep inside `OmegaPhi`
with `C_v / 2 ≤ distPhi w` and `(3/4) * ‖v‖ ≤ ‖w‖ ≤ (5/4) * ‖v‖`. -/
lemma closedBall_log_props {v : ℂ} (hv : v ∈ V_dom) {w : ℂ}
    (hw : w ∈ Metric.closedBall (v + Complex.log v) 1) :
    w ∈ OmegaPhi ∧ C_v / 2 ≤ distPhi w ∧ (3 / 4 : ℝ) * ‖v‖ ≤ ‖w‖ ∧ ‖w‖ ≤ (5 / 4 : ℝ) * ‖v‖ := by
  have hv_norm : C_v ≤ ‖v‖ := V_dom_norm_ge hv
  have hv256 : 256 ≤ ‖v‖ := C_v_ge_256.trans hv_norm
  have hv_pos : 0 < ‖v‖ := by linarith
  have hdist1 : ‖w - (v + Complex.log v)‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hlog_norm : ‖Complex.log v‖ ≤ Real.log ‖v‖ + Real.pi := by
    rw [Complex.log]
    have hln : 0 ≤ Real.log ‖v‖ := Real.log_nonneg (by linarith)
    calc ‖(Real.log ‖v‖ : ℂ) + (Complex.arg v : ℂ) * I‖
        ≤ ‖(Real.log ‖v‖ : ℂ)‖ + ‖(Complex.arg v : ℂ) * I‖ := norm_add_le _ _
      _ = Real.log ‖v‖ + |Complex.arg v| := by
          rw [Complex.norm_real, Real.norm_of_nonneg hln, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, Complex.norm_I, mul_one]
      _ ≤ Real.log ‖v‖ + Real.pi := add_le_add_right (Complex.abs_arg_le_pi v) _
  have hwv : ‖w - v‖ ≤ ‖v‖ / 16 := by
    have htri : ‖w - v‖ ≤ ‖w - (v + Complex.log v)‖ + ‖Complex.log v‖ := by
      have h := norm_add_le (w - (v + Complex.log v)) (Complex.log v)
      have heq : (w - (v + Complex.log v)) + Complex.log v = w - v := by ring
      rwa [heq] at h
    linarith [log_add_pi_add_one_le hv256]
  have hw_lo : (3 / 4 : ℝ) * ‖v‖ ≤ ‖w‖ := by
    have htri : ‖v‖ ≤ ‖w‖ + ‖w - v‖ := by
      have h := norm_add_le w (v - w); rw [norm_sub_rev] at h; simpa using h
    linarith
  have hw_hi : ‖w‖ ≤ (5 / 4 : ℝ) * ‖v‖ := by
    have htri : ‖w‖ ≤ ‖w - v‖ + ‖v‖ := by simpa using norm_add_le (w - v) v
    linarith
  have hdist_w : C_v / 2 ≤ distPhi w := by
    rcases hv with him | ⟨hr, hd⟩
    · -- On `{v.im < -C_v}`, `|(log v).im| ≤ π` and `|(w - (v + log v)).im| ≤ 1`, so `w.im ≤ -C_v + π + 1 ≤ -C_v/2`!
      have him_log : |(Complex.log v).im| ≤ Real.pi := by
        rw [Complex.log_im]; exact Complex.abs_arg_le_pi v
      have him_diff : |(w - (v + Complex.log v)).im| ≤ 1 :=
        (Complex.abs_im_le_norm _).trans hdist1
      have hw_im : w.im = v.im + (Complex.log v).im + (w - (v + Complex.log v)).im := by
        simp only [Complex.sub_im, Complex.add_im]; ring
      have hpi : Real.pi < 4 := Real.pi_lt_four
      have hCv : 256 ≤ C_v := C_v_ge_256
      have hneg : C_v / 2 ≤ -w.im := by
        linarith [(abs_le.mp him_log).2, (abs_le.mp him_diff).2]
      exact hneg.trans (le_max_left _ _)
    · -- On `{R_v < ‖v‖, (sin deltaV / 2) * ‖v‖ < dPhi v}`, `‖w - v‖ ≤ log ‖v‖ + π + 1 ≤ (sin deltaV / 4) * ‖v‖`!
      have hCv_pos : 0 < C_v := C_v_pos
      have hsin_pos : 0 < Real.sin deltaV := sin_deltaV_pos
      -- Show `log ‖v‖ + π + 1 ≤ (sin deltaV / 4) * ‖v‖` since `‖v‖ > R_v = 1024 * C_v / sin deltaV`!
      have hlog_small : Real.log ‖v‖ + Real.pi + 1 ≤ (Real.sin deltaV / 4) * ‖v‖ := by
        have hsin_ge : (1 / 20 : ℝ) ≤ Real.sin deltaV := sin_deltaV_ge
        have hnorm_big : 262144 ≤ ‖v‖ := by
          have h1 : 1024 * C_v ≤ R_v := by
            dsimp only [R_v]
            rw [le_div_iff₀ hsin_pos]
            nlinarith [Real.sin_le_one deltaV]
          linarith [C_v_ge_256]
        have hlog262 : Real.log 262144 ≤ 20 := log_262144_le
        have h1 : Real.log (‖v‖ / 262144) ≤ ‖v‖ / 262144 - 1 := Real.log_le_sub_one_of_pos (by positivity)
        have hsplit : Real.log ‖v‖ = Real.log (‖v‖ / 262144) + Real.log 262144 := by
          rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; ring
        have hpi : Real.pi < 4 := Real.pi_lt_four
        nlinarith
      have htri : ‖w - v‖ ≤ Real.log ‖v‖ + Real.pi + 1 := by
        have h := norm_add_le (w - (v + Complex.log v)) (Complex.log v)
        have heq : (w - (v + Complex.log v)) + Complex.log v = w - v := by ring
        rw [heq] at h; linarith
      have hd_w : (Real.sin deltaV / 4) * ‖v‖ ≤ dPhi w := by
        -- `|dPhi w - dPhi v| ≤ ‖w - v‖`
        have hdiff_d : dPhi v - ‖w - v‖ ≤ dPhi w := by
          let rot : ℂ := Complex.exp (-(phiRay : ℂ) * I)
          have hrot_norm : ‖rot‖ = 1 := by dsimp [rot]; rw [Complex.norm_exp]; simp
          have hre_rot : rot.re = Real.cos phiRay := by
            dsimp [rot]
            have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
            rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
          have him_rot : rot.im = -Real.sin phiRay := by
            dsimp [rot]
            have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
            rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
          have him_diff : (rot * (w - v)).im = -(dPhi w - dPhi v) := by
            simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, hre_rot, him_rot, dPhi]; ring
          have habs := Complex.abs_im_le_norm (rot * (w - v))
          rw [him_diff, abs_neg, norm_mul, hrot_norm, one_mul] at habs
          linarith [(abs_le.mp habs).1]
        linarith
      have hRv_val : (Real.sin deltaV / 4) * R_v = 256 * C_v := by
        dsimp only [R_v]; field_simp [hsin_pos.ne']; ring
      have hge : C_v / 2 ≤ (Real.sin deltaV / 4) * ‖v‖ := by nlinarith
      exact (hge.trans hd_w).trans (le_max_right _ _)
  have hw_mem : w ∈ OmegaPhi := by
    have hpos : 0 < distPhi w := lt_of_lt_of_le (half_pos C_v_pos) hdist_w
    rcases lt_max_iff.mp hpos with him | hd'
    · exact Or.inl (by linarith)
    · exact Or.inr hd'
  exact ⟨hw_mem, hdist_w, hw_lo, hw_hi⟩

/-- Contraction operator `T_op v w = v + Complex.log w - Complex.log (S_phi w)` for inverting `Ei(w) + iπ = e^v`. -/
@[expose] def T_op (v w : ℂ) : ℂ := v + Complex.log w - Complex.log (S_phi w)

/-- On `V_dom`, `T_op v` maps `closedBall (v + log v) 1` into `closedBall (v + log v) (1/2)`
and is a `1/2`-contraction on `closedBall (v + log v) 1`! -/
theorem T_op_contraction {v : ℂ} (hv : v ∈ V_dom) :
    (∀ w ∈ Metric.closedBall (v + Complex.log v) 1,
      ‖T_op v w - (v + Complex.log v)‖ ≤ 1 / 2) ∧
    (∀ w₁ ∈ Metric.closedBall (v + Complex.log v) 1,
     ∀ w₂ ∈ Metric.closedBall (v + Complex.log v) 1,
      ‖T_op v w₂ - T_op v w₁‖ ≤ (1 / 2 : ℝ) * ‖w₂ - w₁‖) := by
  have hv_norm : C_v ≤ ‖v‖ := V_dom_norm_ge hv
  have hv256 : 256 ≤ ‖v‖ := C_v_ge_256.trans hv_norm
  have hv_pos : 0 < ‖v‖ := by linarith
  have hcos2 : 0 < Real.cos phiRay ^ 2 := pow_pos cos_phiRay_pos 2
  -- Helper: on `closedBall (v + log v) 1`, `‖S_phi w - 1‖ ≤ 1/128` and `‖deriv S_phi w‖ ≤ 1/16`
  have hS_small : ∀ w ∈ Metric.closedBall (v + Complex.log v) 1,
      ‖S_phi w - 1‖ ≤ 1 / 128 ∧ ‖deriv S_phi w‖ ≤ 1 / 16 := by
    intro w hw
    obtain ⟨hw_mem, hdw, _, _⟩ := closedBall_log_props hv hw
    have hS1 : ‖S_phi w - 1‖ ≤ 1 / 128 := by
      have h1 := norm_S_phi_sub_one_le hw_mem
      have hden : 128 ≤ distPhi w * Real.cos phiRay ^ 2 := by
        nlinarith [C_v_mul_cos_sq]
      calc ‖S_phi w - 1‖ ≤ 1 / (distPhi w * Real.cos phiRay ^ 2) := h1
        _ ≤ 1 / 128 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hden
    have hS' : ‖deriv S_phi w‖ ≤ 1 / 16 := by
      have h1 := norm_deriv_S_phi_le hw_mem
      have hdw_ge : 128 ≤ distPhi w := by linarith [C_v_ge_256]
      have hden : 128 * 128 ≤ distPhi w ^ 2 * Real.cos phiRay ^ 2 := by
        have h1' : 128 ≤ distPhi w * Real.cos phiRay ^ 2 := by nlinarith [C_v_mul_cos_sq]
        have : distPhi w ^ 2 * Real.cos phiRay ^ 2 = distPhi w * (distPhi w * Real.cos phiRay ^ 2) := by ring
        rw [this]; nlinarith
      calc ‖deriv S_phi w‖ ≤ 4 / (distPhi w ^ 2 * Real.cos phiRay ^ 2) := h1
        _ ≤ 4 / (128 * 128) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
        _ ≤ 1 / 16 := by norm_num
    exact ⟨hS1, hS'⟩
  constructor
  · intro w hw
    obtain ⟨hw_mem, _, _, _⟩ := closedBall_log_props hv hw
    have hlog_diff : ‖Complex.log w - Complex.log v‖ ≤ 1 / 4 := by
      have hdist : ‖w - v‖ ≤ ‖v‖ / 16 := by
        have h1 : ‖w - (v + Complex.log v)‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
        have hlog_norm : ‖Complex.log v‖ ≤ Real.log ‖v‖ + Real.pi := by
          rw [Complex.log]
          have hln : 0 ≤ Real.log ‖v‖ := Real.log_nonneg (by linarith)
          calc ‖(Real.log ‖v‖ : ℂ) + (Complex.arg v : ℂ) * I‖
              ≤ ‖(Real.log ‖v‖ : ℂ)‖ + ‖(Complex.arg v : ℂ) * I‖ := norm_add_le _ _
            _ = Real.log ‖v‖ + |Complex.arg v| := by
                rw [Complex.norm_real, Real.norm_of_nonneg hln, norm_mul, Complex.norm_real,
                  Real.norm_eq_abs, Complex.norm_I, mul_one]
            _ ≤ Real.log ‖v‖ + Real.pi := add_le_add_right (Complex.abs_arg_le_pi v) _
        have htri : ‖w - v‖ ≤ ‖w - (v + Complex.log v)‖ + ‖Complex.log v‖ := by
          have h := norm_add_le (w - (v + Complex.log v)) (Complex.log v)
          have heq : (w - (v + Complex.log v)) + Complex.log v = w - v := by ring
          rwa [heq] at h
        linarith [log_add_pi_add_one_le hv256]
      have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, v + (t : ℂ) * (w - v) ∈ Complex.slitPlane := by
        intro t ht
        -- Check `distPhi (v + t(w - v)) > 0` by convexity of `OmegaPhi` pieces!
        have hmem_O : v + (t : ℂ) * (w - v) ∈ OmegaPhi := by
          rcases hv with him | ⟨hr, hd⟩
          · -- `v.im < -C_v` and `w.im ≤ -C_v / 2`!
            have hw_im : w.im ≤ -(C_v / 2) := by
              have h1 : ‖w - (v + Complex.log v)‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
              have him_log : |(Complex.log v).im| ≤ Real.pi := by rw [Complex.log_im]; exact Complex.abs_arg_le_pi v
              have him_diff : |(w - (v + Complex.log v)).im| ≤ 1 := (Complex.abs_im_le_norm _).trans h1
              have hpi : Real.pi < 4 := Real.pi_lt_four
              have : w.im = v.im + (Complex.log v).im + (w - (v + Complex.log v)).im := by
                simp only [Complex.sub_im, Complex.add_im]; ring
              linarith [(abs_le.mp him_log).2, (abs_le.mp him_diff).2, C_v_ge_256]
            have hlin_im : (v + (t : ℂ) * (w - v)).im = (1 - t) * v.im + t * w.im := by simp; ring
            exact Or.inl (by rw [hlin_im]; nlinarith [ht.1, ht.2, C_v_pos])
          · have hd_v : 0 < dPhi v := lt_of_le_of_lt (mul_nonneg (half_pos sin_deltaV_pos).le (norm_nonneg v)) hd
            have hd_w : 0 < dPhi w := by
              have h1 : ‖w - v‖ ≤ (Real.sin deltaV / 4) * ‖v‖ := by
                have hsin_ge : (1 / 20 : ℝ) ≤ Real.sin deltaV := sin_deltaV_ge
                have hnorm_big : 262144 ≤ ‖v‖ := by
                  have : 1024 * C_v ≤ R_v := by
                    dsimp only [R_v]; rw [le_div_iff₀ sin_deltaV_pos]; nlinarith [Real.sin_le_one deltaV, C_v_pos]
                  linarith [C_v_ge_256]
                have hlog262 : Real.log 262144 ≤ 20 := log_262144_le
                have h1' : Real.log (‖v‖ / 262144) ≤ ‖v‖ / 262144 - 1 := Real.log_le_sub_one_of_pos (by positivity)
                have hsplit : Real.log ‖v‖ = Real.log (‖v‖ / 262144) + Real.log 262144 := by
                  rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; ring
                have hpi : Real.pi < 4 := Real.pi_lt_four
                have htri : ‖w - v‖ ≤ Real.log ‖v‖ + Real.pi + 1 := by
                  have h1'' : ‖w - (v + Complex.log v)‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
                  have hlog_norm : ‖Complex.log v‖ ≤ Real.log ‖v‖ + Real.pi := by
                    rw [Complex.log]
                    have hln : 0 ≤ Real.log ‖v‖ := Real.log_nonneg (by linarith)
                    calc ‖(Real.log ‖v‖ : ℂ) + (Complex.arg v : ℂ) * I‖
                        ≤ ‖(Real.log ‖v‖ : ℂ)‖ + ‖(Complex.arg v : ℂ) * I‖ := norm_add_le _ _
                      _ = Real.log ‖v‖ + |Complex.arg v| := by
                          rw [Complex.norm_real, Real.norm_of_nonneg hln, norm_mul, Complex.norm_real,
                            Real.norm_eq_abs, Complex.norm_I, mul_one]
                      _ ≤ Real.log ‖v‖ + Real.pi := add_le_add_right (Complex.abs_arg_le_pi v) _
                  have h := norm_add_le (w - (v + Complex.log v)) (Complex.log v)
                  have heq : (w - (v + Complex.log v)) + Complex.log v = w - v := by ring
                  rw [heq] at h; linarith
                nlinarith
              let rot : ℂ := Complex.exp (-(phiRay : ℂ) * I)
              have hrot_norm : ‖rot‖ = 1 := by dsimp [rot]; rw [Complex.norm_exp]; simp
              have hre_rot : rot.re = Real.cos phiRay := by
                dsimp [rot]; have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
                rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
              have him_rot : rot.im = -Real.sin phiRay := by
                dsimp [rot]; have : -(phiRay : ℂ) * I = ((-phiRay : ℝ) : ℂ) * I := by push_cast; ring
                rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
              have him_diff : (rot * (w - v)).im = -(dPhi w - dPhi v) := by
                simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, hre_rot, him_rot, dPhi]; ring
              have habs := Complex.abs_im_le_norm (rot * (w - v))
              rw [him_diff, abs_neg, norm_mul, hrot_norm, one_mul] at habs
              linarith [(abs_le.mp habs).1, sin_deltaV_pos]
            have hlin_d : dPhi (v + (t : ℂ) * (w - v)) = (1 - t) * dPhi v + t * dPhi w := by
              dsimp [dPhi]; simp; ring
            exact Or.inr (by
              rw [hlin_d]
              by_cases ht0 : t = 0
              · subst ht0; linarith
              · have : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
                nlinarith [ht.2])
        exact OmegaPhi_subset_slitPlane hmem_O
      have hb := norm_clog_sub_le_of_segment (norm_pos_iff.mp hv_pos) (by linarith) hseg
      calc ‖Complex.log w - Complex.log v‖ ≤ 2 * ‖w - v‖ / ‖v‖ := hb
        _ ≤ 2 * (‖v‖ / 16) / ‖v‖ := div_le_div_of_nonneg_right (by linarith) hv_pos.le
        _ = 1 / 8 := by field_simp [hv_pos.ne']; ring
        _ ≤ 1 / 4 := by norm_num
    have hlogS : ‖Complex.log (S_phi w)‖ ≤ 1 / 4 := by
      have hS1 := (hS_small w hw).1
      have h1 := norm_clog_one_add_le (u := S_phi w - 1) (by linarith)
      rw [add_sub_cancel] at h1
      linarith
    have hrew : T_op v w - (v + Complex.log v) = (Complex.log w - Complex.log v) - Complex.log (S_phi w) := by
      dsimp only [T_op]; ring
    rw [hrew]
    calc ‖(Complex.log w - Complex.log v) - Complex.log (S_phi w)‖
        ≤ ‖Complex.log w - Complex.log v‖ + ‖Complex.log (S_phi w)‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hlog_diff hlogS
      _ = 1 / 2 := by norm_num
  · -- Contraction `‖T_op v w₂ - T_op v w₁‖ ≤ (1/2) * ‖w₂ - w₁‖` via FTC on the segment `[w₁, w₂] ⊆ closedBall (v + log v) 1`!
    intro w₁ hw₁ w₂ hw₂
    have hseg_cb : ∀ t ∈ Set.Icc (0 : ℝ) 1, w₁ + (t : ℂ) * (w₂ - w₁) ∈ Metric.closedBall (v + Complex.log v) 1 := by
      intro t ht
      have hconv := convex_closedBall (v + Complex.log v) (1 : ℝ) hw₁ hw₂
        (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (by ring)
      simpa [Complex.real_smul, sub_mul, one_mul] using
        (show (1 - t) • w₁ + t • w₂ = w₁ + (t : ℂ) * (w₂ - w₁) by simp [Complex.real_smul]; ring) ▸ hconv
    have hderiv_T : ∀ w ∈ Metric.closedBall (v + Complex.log v) 1,
        HasDerivAt (T_op v) (w⁻¹ - deriv S_phi w / S_phi w) w := by
      intro w hw
      obtain ⟨hw_mem, _, _, _⟩ := closedBall_log_props hv hw
      have hS_slit : S_phi w ∈ Complex.slitPlane := by
        left
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hS_small w hw).1)).1
        simp only [Complex.sub_re, Complex.one_re] at h1; linarith
      have hlog1 : HasDerivAt Complex.log w⁻¹ w :=
        Complex.hasDerivAt_log (OmegaPhi_subset_slitPlane hw_mem)
      have hS_d : HasDerivAt S_phi (deriv S_phi w) w :=
        (differentiableOn_S_phi.differentiableAt (isOpen_OmegaPhi.mem_nhds hw_mem)).hasDerivAt
      have hlogS : HasDerivAt (fun z => Complex.log (S_phi z)) ((S_phi w)⁻¹ * deriv S_phi w) w :=
        (Complex.hasDerivAt_log hS_slit).comp w hS_d
      have htot := (hlog1.const_add v).fun_sub hlogS
      refine htot.congr_deriv ?_; ring
    have hderiv_seg : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun τ : ℝ => T_op v (w₁ + (τ : ℂ) * (w₂ - w₁)))
          (((w₁ + (t : ℂ) * (w₂ - w₁))⁻¹ -
            deriv S_phi (w₁ + (t : ℂ) * (w₂ - w₁)) / S_phi (w₁ + (t : ℂ) * (w₂ - w₁))) * (w₂ - w₁)) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hlin : HasDerivAt (fun τ : ℝ => w₁ + (τ : ℂ) * (w₂ - w₁)) (w₂ - w₁) t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (w₂ - w₁)).const_add w₁
      exact (hderiv_T _ (hseg_cb t ht)).comp t hlin
    have hcont_seg : ContinuousOn (fun t : ℝ =>
        (((w₁ + (t : ℂ) * (w₂ - w₁))⁻¹ -
          deriv S_phi (w₁ + (t : ℂ) * (w₂ - w₁)) / S_phi (w₁ + (t : ℂ) * (w₂ - w₁))) * (w₂ - w₁)))
        (Set.uIcc (0 : ℝ) 1) := by
      have hlin_c : Continuous (fun t : ℝ => w₁ + (t : ℂ) * (w₂ - w₁)) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have hS_an : AnalyticOnNhd ℂ S_phi OmegaPhi := differentiableOn_S_phi.analyticOnNhd isOpen_OmegaPhi
      have hS'_cont : ContinuousOn (deriv S_phi) OmegaPhi := hS_an.deriv.continuousOn
      have hS_cont : ContinuousOn S_phi OmegaPhi := differentiableOn_S_phi.continuousOn
      have hmaps : Set.MapsTo (fun t : ℝ => w₁ + (t : ℂ) * (w₂ - w₁)) (Set.uIcc 0 1) OmegaPhi := by
        intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht
        exact (closedBall_log_props hv (hseg_cb t ht)).1
      refine ((hlin_c.continuousOn.inv₀ fun t ht => ?_).sub
        ((hS'_cont.comp hlin_c.continuousOn hmaps).div (hS_cont.comp hlin_c.continuousOn hmaps) fun t ht => ?_)).mul
        continuousOn_const
      · rw [Set.uIcc_of_le zero_le_one] at ht
        exact Complex.slitPlane_ne_zero (OmegaPhi_subset_slitPlane (closedBall_log_props hv (hseg_cb t ht)).1)
      · rw [Set.uIcc_of_le zero_le_one] at ht
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hS_small _ (hseg_cb t ht)).1)).1
        simp only [Complex.sub_re, Complex.one_re] at h1
        intro h0; have := congr_arg Complex.re h0; simp only [Function.comp_apply, Complex.zero_re] at this; linarith
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_seg hcont_seg.intervalIntegrable
    simp only [Complex.ofReal_one, one_mul, add_sub_cancel, Complex.ofReal_zero, zero_mul, add_zero] at hftc
    rw [← hftc]
    have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖(((w₁ + (t : ℂ) * (w₂ - w₁))⁻¹ -
          deriv S_phi (w₁ + (t : ℂ) * (w₂ - w₁)) / S_phi (w₁ + (t : ℂ) * (w₂ - w₁))) * (w₂ - w₁))‖ ≤
        (1 / 2 : ℝ) * ‖w₂ - w₁‖ := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      set wt := w₁ + (t : ℂ) * (w₂ - w₁)
      have hwt_cb : wt ∈ Metric.closedBall (v + Complex.log v) 1 := hseg_cb t ⟨ht.1.le, ht.2⟩
      obtain ⟨_, _, hwt_lo, _⟩ := closedBall_log_props hv hwt_cb
      obtain ⟨hS1, hS'⟩ := hS_small wt hwt_cb
      have hwt_ge : 1 / 4 ≤ 1 / 4 := le_rfl
      have hinv : ‖wt⁻¹‖ ≤ 1 / 4 := by
        rw [norm_inv]
        have : 4 ≤ ‖wt‖ := by linarith
        exact (inv_anti₀ (by norm_num) this).trans (by norm_num)
      have hS_lo : 1 / 2 ≤ ‖S_phi wt‖ := by
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hS1)).1
        simp only [Complex.sub_re, Complex.one_re] at h1
        exact (by linarith : 1 / 2 ≤ (S_phi wt).re).trans (Complex.re_le_norm _)
      have hdiv : ‖deriv S_phi wt / S_phi wt‖ ≤ 1 / 4 := by
        rw [norm_div]
        calc ‖deriv S_phi wt‖ / ‖S_phi wt‖ ≤ (1 / 16) / (1 / 2) :=
              div_le_div₀ (by norm_num) hS' (by norm_num) hS_lo
          _ = 1 / 8 := by norm_num
          _ ≤ 1 / 4 := by norm_num
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖wt⁻¹ - deriv S_phi wt / S_phi wt‖ ≤ ‖wt⁻¹‖ + ‖deriv S_phi wt / S_phi wt‖ := norm_sub_le _ _
        _ ≤ 1 / 4 + 1 / 4 := add_le_add hinv hdiv
        _ = 1 / 2 := by norm_num
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- Existence and uniqueness of the fixed point `w_plus v` on `V_dom` via Banach's fixed-point theorem! -/
theorem existsUnique_w_plus {v : ℂ} (hv : v ∈ V_dom) :
    ∃! w : ℂ, w ∈ Metric.closedBall (v + Complex.log v) 1 ∧ T_op v w = w := by
  obtain ⟨hself, hlip⟩ := T_op_contraction hv
  let B : Set ℂ := Metric.closedBall (v + Complex.log v) 1
  let f : B → B := fun x => ⟨T_op v x.1, by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact (hself x.1 x.2).trans (by norm_num)⟩
  have hcontr : ContractingWith (1 / 2 : NNReal) f := by
    refine ⟨by norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    push_cast
    dsimp only [f]
    exact hlip y.1 y.2 x.1 x.2
  have : CompleteSpace B := Metric.isClosed_closedBall.completeSpace_coe
  have : Nonempty B := ⟨⟨v + Complex.log v, Metric.mem_closedBall_self zero_le_one⟩⟩
  let wfix : B := hcontr.fixedPoint f
  refine ⟨wfix.1, ⟨wfix.2, congr_arg Subtype.val (hcontr.fixedPoint_isFixedPt)⟩, ?_⟩
  intro w ⟨hwB, hwEq⟩
  have hpt : Function.IsFixedPt f ⟨w, hwB⟩ := Subtype.ext hwEq
  exact congr_arg Subtype.val (hcontr.fixedPoint_unique hpt)

/-- The holomorphic lateral inverse `w_plus(v)` solving `Ei_complex (w_plus v) + iπ = exp v` on `V_dom`. -/
@[expose] def w_plus (v : ℂ) : ℂ :=
  open Classical in
  if hv : v ∈ V_dom then Classical.choose (existsUnique_w_plus hv) else 0

/-- The normalized inverse `F_plus(v) = w_plus(v) / S_phi(w_plus(v)) = exp(w_plus(v) - v)` on `V_dom`. -/
@[expose] def F_plus (v : ℂ) : ℂ := w_plus v / S_phi (w_plus v)

lemma w_plus_spec {v : ℂ} (hv : v ∈ V_dom) :
    w_plus v ∈ Metric.closedBall (v + Complex.log v) 1 ∧ T_op v (w_plus v) = w_plus v := by
  classical
  dsimp only [w_plus]
  split_ifs
  exact (Classical.choose_spec (existsUnique_w_plus hv)).1

lemma w_plus_eq_of_mem {v w : ℂ} (hv : v ∈ V_dom)
    (hw : w ∈ Metric.closedBall (v + Complex.log v) 1) (hfix : T_op v w = w) :
    w = w_plus v := by
  classical
  dsimp only [w_plus]
  split_ifs
  exact (Classical.choose_spec (existsUnique_w_plus hv)).2 w ⟨hw, hfix⟩

/-- **Exact Inversion Identity**: for every `v ∈ V_dom`, `Ei_complex (w_plus v) + iπ = exp v`! -/
theorem Ei_add_I_pi_w_plus {v : ℂ} (hv : v ∈ V_dom) :
    Ei_complex (w_plus v) + I * (Real.pi : ℂ) = Complex.exp v := by
  obtain ⟨hcb, hfix⟩ := w_plus_spec hv
  obtain ⟨hw_mem, hdw, _, _⟩ := closedBall_log_props hv hcb
  have hw0 : w_plus v ≠ 0 := Complex.slitPlane_ne_zero (OmegaPhi_subset_slitPlane hw_mem)
  have hS0 : S_phi (w_plus v) ≠ 0 := by
    have h1 := norm_S_phi_sub_one_le hw_mem
    have hden : 128 ≤ distPhi (w_plus v) * Real.cos phiRay ^ 2 := by
      nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
    have hS1 : ‖S_phi (w_plus v) - 1‖ ≤ 1 / 128 :=
      h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
    intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hS1; linarith
  have hv_eq : v = w_plus v - Complex.log (w_plus v) + Complex.log (S_phi (w_plus v)) := by
    dsimp only [T_op] at hfix; linear_combination hfix
  rw [← A_phi_eq_Ei_add_I_pi hw_mem]
  conv_rhs => rw [hv_eq]
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log hw0, Complex.exp_log hS0]
  dsimp only [A_phi, S_phi]
  field_simp [hw0]

/-- Exact formula `F_plus v = exp (w_plus v - v)` on `V_dom`. -/
lemma F_plus_eq_exp_sub {v : ℂ} (hv : v ∈ V_dom) :
    F_plus v = Complex.exp (w_plus v - v) := by
  obtain ⟨hcb, hfix⟩ := w_plus_spec hv
  obtain ⟨hw_mem, hdw, _, _⟩ := closedBall_log_props hv hcb
  have hw0 : w_plus v ≠ 0 := Complex.slitPlane_ne_zero (OmegaPhi_subset_slitPlane hw_mem)
  have hS0 : S_phi (w_plus v) ≠ 0 := by
    have h1 := norm_S_phi_sub_one_le hw_mem
    have hden : 128 ≤ distPhi (w_plus v) * Real.cos phiRay ^ 2 := by
      nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
    have hS1 : ‖S_phi (w_plus v) - 1‖ ≤ 1 / 128 :=
      h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
    intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hS1; linarith
  have hdiff : w_plus v - v = Complex.log (w_plus v) - Complex.log (S_phi (w_plus v)) := by
    dsimp only [T_op] at hfix; linear_combination -hfix
  dsimp only [F_plus]
  rw [hdiff, Complex.exp_sub, Complex.exp_log hw0, Complex.exp_log hS0]

/-- **Exact Complex Derivative of `w_plus`**: `HasDerivAt w_plus (S_phi (w_plus v)) v` on `V_dom`! -/
theorem hasDerivAt_w_plus {v₀ : ℂ} (hv₀ : v₀ ∈ V_dom) :
    HasDerivAt w_plus (S_phi (w_plus v₀)) v₀ := by
  -- Define `g(w) = w - log w + log (S_phi w)` and note `g'(w) = 1 / S_phi w`!
  let g : ℂ → ℂ := fun w => w - Complex.log w + Complex.log (S_phi w)
  obtain ⟨hcb₀, hfix₀⟩ := w_plus_spec hv₀
  obtain ⟨hw₀_mem, hdw₀, _, _⟩ := closedBall_log_props hv₀ hcb₀
  have hw₀_ne : w_plus v₀ ≠ 0 := Complex.slitPlane_ne_zero (OmegaPhi_subset_slitPlane hw₀_mem)
  have hS₀_small : ‖S_phi (w_plus v₀) - 1‖ ≤ 1 / 128 := by
    have h1 := norm_S_phi_sub_one_le hw₀_mem
    have hden : 128 ≤ distPhi (w_plus v₀) * Real.cos phiRay ^ 2 := by
      nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
    exact h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
  have hS₀_slit : S_phi (w_plus v₀) ∈ Complex.slitPlane := by
    left
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hS₀_small)).1
    simp only [Complex.sub_re, Complex.one_re] at h1; linarith
  have hS₀_ne : S_phi (w_plus v₀) ≠ 0 := Complex.slitPlane_ne_zero hS₀_slit
  -- Prove `HasDerivAt g (S_phi (w_plus v₀))⁻¹ (w_plus v₀)` via `A_phi(w) = exp(w) * S_phi(w) / w`!
  have hg_deriv : HasDerivAt g (S_phi (w_plus v₀))⁻¹ (w_plus v₀) := by
    have hS_d : HasDerivAt S_phi (deriv S_phi (w_plus v₀)) (w_plus v₀) :=
      (differentiableOn_S_phi.differentiableAt (isOpen_OmegaPhi.mem_nhds hw₀_mem)).hasDerivAt
    have hA_eq : A_phi =ᶠ[𝓝 (w_plus v₀)] fun w => Complex.exp w * S_phi w / w := by
      filter_upwards [isOpen_OmegaPhi.mem_nhds hw₀_mem] with w hw
      have hw_ne : w ≠ 0 := Complex.slitPlane_ne_zero (OmegaPhi_subset_slitPlane hw)
      dsimp only [A_phi, S_phi]; field_simp [hw_ne]
    have hA_d1 := (hasDerivAt_A_phi hw₀_mem).congr_of_eventuallyEq hA_eq.symm
    have hA_d2 := ((Complex.hasDerivAt_exp (w_plus v₀)).fun_mul hS_d).fun_div (hasDerivAt_id (w_plus v₀)) hw₀_ne
    have hderiv_eq := hA_d1.unique hA_d2
    have hexp_ne : Complex.exp (w_plus v₀) ≠ 0 := Complex.exp_ne_zero _
    have hS_ode : deriv S_phi (w_plus v₀) = 1 - S_phi (w_plus v₀) + S_phi (w_plus v₀) / w_plus v₀ := by
      simp only [id_eq] at hderiv_eq
      field_simp [hw₀_ne, hexp_ne] at hderiv_eq ⊢
      linear_combination -hderiv_eq
    have hlog_w : HasDerivAt Complex.log (w_plus v₀)⁻¹ (w_plus v₀) :=
      Complex.hasDerivAt_log (OmegaPhi_subset_slitPlane hw₀_mem)
    have hlog_S : HasDerivAt (fun w => Complex.log (S_phi w))
        ((S_phi (w_plus v₀))⁻¹ * deriv S_phi (w_plus v₀)) (w_plus v₀) :=
      (Complex.hasDerivAt_log hS₀_slit).comp (w_plus v₀) hS_d
    have htot := ((hasDerivAt_id (w_plus v₀)).fun_sub hlog_w).fun_add hlog_S
    refine htot.congr_deriv ?_
    rw [hS_ode]
    field_simp [hw₀_ne, hS₀_ne]
    ring
  -- Local 2-Lipschitz bound `‖w_plus v - w_plus v₀‖ ≤ 2 * ‖v - v₀‖` near `v₀`!
  have hcont_center : ContinuousAt (fun v : ℂ => v + Complex.log v) v₀ :=
    continuousAt_id.add (Complex.hasDerivAt_log (OmegaPhi_subset_slitPlane (V_dom_subset_OmegaPhi hv₀))).continuousAt
  have hnhds_ball : ∀ᶠ v in 𝓝 v₀,
      v ∈ V_dom ∧ w_plus v ∈ Metric.closedBall (v₀ + Complex.log v₀) 1 := by
    have hev1 : ∀ᶠ v in 𝓝 v₀, v ∈ V_dom := isOpen_V_dom.mem_nhds hv₀
    have hev2 : ∀ᶠ v in 𝓝 v₀, ‖(v + Complex.log v) - (v₀ + Complex.log v₀)‖ < 1 / 2 := by
      have h := hcont_center.eventually (Metric.ball_mem_nhds (v₀ + Complex.log v₀) (by norm_num : (0 : ℝ) < 1 / 2))
      refine h.mono fun v hv => by simpa [Metric.mem_ball, dist_eq_norm] using hv
    filter_upwards [hev1, hev2] with v hv hdv
    refine ⟨hv, ?_⟩
    obtain ⟨hcb, hfix⟩ := w_plus_spec hv
    have hhalf : ‖w_plus v - (v + Complex.log v)‖ ≤ 1 / 2 := by
      rw [← hfix]; exact (T_op_contraction hv).1 (w_plus v) hcb
    rw [Metric.mem_closedBall, dist_eq_norm]
    have htri : ‖w_plus v - (v₀ + Complex.log v₀)‖ ≤
        ‖w_plus v - (v + Complex.log v)‖ + ‖(v + Complex.log v) - (v₀ + Complex.log v₀)‖ := by
      have h := norm_add_le (w_plus v - (v + Complex.log v)) ((v + Complex.log v) - (v₀ + Complex.log v₀))
      have heq : (w_plus v - (v + Complex.log v)) + ((v + Complex.log v) - (v₀ + Complex.log v₀)) =
          w_plus v - (v₀ + Complex.log v₀) := by ring
      rwa [heq] at h
    linarith
  have hlip_loc : ∀ᶠ v in 𝓝 v₀, ‖w_plus v - w_plus v₀‖ ≤ 2 * ‖v - v₀‖ := by
    filter_upwards [hnhds_ball] with v ⟨hv, hw_cb₀⟩
    have hfix := (w_plus_spec hv).2
    have hTv : T_op v (w_plus v) - T_op v₀ (w_plus v) = v - v₀ := by dsimp [T_op]; ring
    have hcontr := (T_op_contraction hv₀).2 (w_plus v₀) hcb₀ (w_plus v) hw_cb₀
    have hdiff : w_plus v - w_plus v₀ = (v - v₀) + (T_op v₀ (w_plus v) - T_op v₀ (w_plus v₀)) := by
      linear_combination -hfix + hfix₀ + hTv
    have htri : ‖w_plus v - w_plus v₀‖ ≤ ‖v - v₀‖ + (1 / 2 : ℝ) * ‖w_plus v - w_plus v₀‖ := by
      calc ‖w_plus v - w_plus v₀‖
          = ‖(v - v₀) + (T_op v₀ (w_plus v) - T_op v₀ (w_plus v₀))‖ := by rw [hdiff]
        _ ≤ ‖v - v₀‖ + ‖T_op v₀ (w_plus v) - T_op v₀ (w_plus v₀)‖ := norm_add_le _ _
        _ ≤ ‖v - v₀‖ + (1 / 2 : ℝ) * ‖w_plus v - w_plus v₀‖ := add_le_add_right hcontr _
    linarith
  have hw_cont : Tendsto w_plus (𝓝 v₀) (𝓝 (w_plus v₀)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hball : ∀ᶠ v in 𝓝 v₀, ‖v - v₀‖ < ε / 2 := by
      filter_upwards [Metric.ball_mem_nhds v₀ (half_pos hε)] with v hv
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    filter_upwards [hlip_loc, hball] with v hlip hlt
    rw [dist_eq_norm]; linarith
  -- Now deduce `HasDerivAt w_plus (S_phi (w_plus v₀)) v₀` from `g (w_plus v) = v`!
  rw [hasDerivAt_iff_tendsto_slope_zero, ← tendsto_sub_nhds_zero_iff]
  have hg_lim := hasDerivAt_iff_tendsto.mp hg_deriv
  have hg_o : Tendsto (fun w : ℂ =>
      ‖w - w_plus v₀‖⁻¹ * ‖g w - g (w_plus v₀) - (S_phi (w_plus v₀))⁻¹ * (w - w_plus v₀)‖)
      (𝓝 (w_plus v₀)) (𝓝 0) := by
    refine hg_lim.congr fun w => ?_
    simp [smul_eq_mul, mul_comm]
  have hg_comp : Tendsto (fun t : ℂ =>
      ‖w_plus (v₀ + t) - w_plus v₀‖⁻¹ *
        ‖g (w_plus (v₀ + t)) - g (w_plus v₀) - (S_phi (w_plus v₀))⁻¹ * (w_plus (v₀ + t) - w_plus v₀)‖)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have hadd : Tendsto (fun t : ℂ => v₀ + t) (𝓝[≠] (0 : ℂ)) (𝓝 v₀) := by
      have h : ContinuousAt (fun t : ℂ => v₀ + t) 0 := continuousAt_const.add continuousAt_id
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    exact hg_o.comp (hw_cont.comp hadd)
  refine squeeze_zero_norm' (a := fun t : ℂ =>
      2 * ‖S_phi (w_plus v₀)‖ * (‖w_plus (v₀ + t) - w_plus v₀‖⁻¹ *
        ‖g (w_plus (v₀ + t)) - g (w_plus v₀) - (S_phi (w_plus v₀))⁻¹ * (w_plus (v₀ + t) - w_plus v₀)‖)) ?_ ?_
  · have hnhds_t : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ),
        v₀ + t ∈ V_dom ∧ ‖w_plus (v₀ + t) - w_plus v₀‖ ≤ 2 * ‖t‖ ∧ t ≠ 0 := by
      have hadd : Tendsto (fun t : ℂ => v₀ + t) (𝓝[≠] (0 : ℂ)) (𝓝 v₀) := by
        have h : ContinuousAt (fun t : ℂ => v₀ + t) 0 := continuousAt_const.add continuousAt_id
        simpa using h.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [hadd.eventually (isOpen_V_dom.mem_nhds hv₀),
        hadd.eventually hlip_loc, self_mem_nhdsWithin] with t htV htlip ht0
      exact ⟨htV, by simpa using htlip, ht0⟩
    filter_upwards [hnhds_t] with t ⟨htV, htlip, ht0⟩
    have hgt : g (w_plus (v₀ + t)) = v₀ + t := by
      have hfix := (w_plus_spec htV).2; dsimp only [g, T_op] at *; linear_combination -hfix
    have hg0 : g (w_plus v₀) = v₀ := by
      dsimp only [g, T_op] at *; linear_combination -hfix₀
    have hdw_ne : w_plus (v₀ + t) - w_plus v₀ ≠ 0 := by
      intro h0
      have hEq : w_plus (v₀ + t) = w_plus v₀ := sub_eq_zero.mp h0
      have : v₀ + t = v₀ := by rw [← hgt, hEq, hg0]
      exact ht0 (by linear_combination this)
    have hdw_pos : 0 < ‖w_plus (v₀ + t) - w_plus v₀‖ := norm_pos_iff.mpr hdw_ne
    have ht_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have hid : t⁻¹ • (w_plus (v₀ + t) - w_plus v₀) - S_phi (w_plus v₀) =
        -S_phi (w_plus v₀) * t⁻¹ *
          (g (w_plus (v₀ + t)) - g (w_plus v₀) - (S_phi (w_plus v₀))⁻¹ * (w_plus (v₀ + t) - w_plus v₀)) := by
      rw [hgt, hg0, smul_eq_mul]
      field_simp [ht0, hS₀_ne]
      ring
    rw [hid, norm_mul, norm_mul, norm_neg, norm_inv]
    have hratio : ‖t‖⁻¹ ≤ 2 * ‖w_plus (v₀ + t) - w_plus v₀‖⁻¹ := by
      rw [inv_le_comm₀ ht_pos (by positivity)]
      calc (2 * ‖w_plus (v₀ + t) - w_plus v₀‖⁻¹)⁻¹ = ‖w_plus (v₀ + t) - w_plus v₀‖ / 2 := by
            field_simp [hdw_pos.ne']
        _ ≤ ‖t‖ := by linarith
    calc ‖S_phi (w_plus v₀)‖ * ‖t‖⁻¹ *
          ‖g (w_plus (v₀ + t)) - g (w_plus v₀) - (S_phi (w_plus v₀))⁻¹ * (w_plus (v₀ + t) - w_plus v₀)‖
        ≤ ‖S_phi (w_plus v₀)‖ * (2 * ‖w_plus (v₀ + t) - w_plus v₀‖⁻¹) *
            ‖g (w_plus (v₀ + t)) - g (w_plus v₀) - (S_phi (w_plus v₀))⁻¹ * (w_plus (v₀ + t) - w_plus v₀)‖ := by
          gcongr
      _ = 2 * ‖S_phi (w_plus v₀)‖ * (‖w_plus (v₀ + t) - w_plus v₀‖⁻¹ *
            ‖g (w_plus (v₀ + t)) - g (w_plus v₀) - (S_phi (w_plus v₀))⁻¹ * (w_plus (v₀ + t) - w_plus v₀)‖) := by
          ring
  · simpa using hg_comp.const_mul (2 * ‖S_phi (w_plus v₀)‖)

theorem differentiableOn_w_plus : DifferentiableOn ℂ w_plus V_dom :=
  fun _ hv => (hasDerivAt_w_plus hv).differentiableAt.differentiableWithinAt

theorem differentiableOn_F_plus : DifferentiableOn ℂ F_plus V_dom := by
  intro v hv
  have hw := (hasDerivAt_w_plus hv).differentiableAt
  obtain ⟨hcb, _⟩ := w_plus_spec hv
  obtain ⟨hw_mem, hdw, _, _⟩ := closedBall_log_props hv hcb
  have hS : DifferentiableAt ℂ S_phi (w_plus v) :=
    differentiableOn_S_phi.differentiableAt (isOpen_OmegaPhi.mem_nhds hw_mem)
  have hS_ne : S_phi (w_plus v) ≠ 0 := by
    have h1 := norm_S_phi_sub_one_le hw_mem
    have hden : 128 ≤ distPhi (w_plus v) * Real.cos phiRay ^ 2 := by
      nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
    have hS1 : ‖S_phi (w_plus v) - 1‖ ≤ 1 / 128 :=
      h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
    intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hS1; linarith
  exact (hw.div (hS.comp v hw) hS_ne).differentiableWithinAt

lemma norm_F_plus_le {v : ℂ} (hv : v ∈ V_dom) : ‖F_plus v‖ ≤ 3 * ‖v‖ := by
  obtain ⟨hcb, _⟩ := w_plus_spec hv
  obtain ⟨hw_mem, hdw, _, hw_hi⟩ := closedBall_log_props hv hcb
  have hS1 : ‖S_phi (w_plus v) - 1‖ ≤ 1 / 128 := by
    have h1 := norm_S_phi_sub_one_le hw_mem
    have hden : 128 ≤ distPhi (w_plus v) * Real.cos phiRay ^ 2 := by
      nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
    exact h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
  have hS_lo : 1 / 2 ≤ ‖S_phi (w_plus v)‖ := by
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hS1)).1
    simp only [Complex.sub_re, Complex.one_re] at h1
    exact (by linarith : 1 / 2 ≤ (S_phi (w_plus v)).re).trans (Complex.re_le_norm _)
  dsimp only [F_plus]
  rw [norm_div]
  calc ‖w_plus v‖ / ‖S_phi (w_plus v)‖ ≤ ((5 / 4 : ℝ) * ‖v‖) / (1 / 2) :=
        div_le_div₀ (by positivity) hw_hi (by norm_num) hS_lo
    _ = (5 / 2 : ℝ) * ‖v‖ := by ring
    _ ≤ 3 * ‖v‖ := by linarith [norm_nonneg v]

/-! #### 3b. Formal `GevBound` Algebra, Recursion for `wCoeff`, and `HasGev1Exp` for `w_plus` and `F_plus / v` -/

/-- Weighted Gevrey-1 formal series bound: `‖a n k‖ ≤ M * ρ^n * n! / ((n+1)^2 * k!)` and `a n k = 0` for `k > n`. -/
@[expose] def GevBound (ρ M : ℝ) (a : LogCoeff) : Prop :=
  (∀ n k, n < k → a n k = 0) ∧
  (∀ n k, k ≤ n → ‖a n k‖ ≤ M * ρ ^ n * (n.factorial : ℝ) / (((n + 1 : ℝ) ^ 2) * (k.factorial : ℝ)))

lemma sum_inv_sq_le_two_sub (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (1 : ℝ) / ((j + 1 : ℝ) ^ 2)) ≤ 2 - 1 / (N + 1 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hstep : (1 : ℝ) / ((m + 1 + 1 : ℝ) ^ 2) ≤ 1 / (m + 1 : ℝ) - 1 / (m + 1 + 1 : ℝ) := by
      have hm1 : (0 : ℝ) < m + 1 := by positivity
      have hm2 : (0 : ℝ) < m + 1 + 1 := by positivity
      rw [div_sub_div _ _ hm1.ne' hm2.ne', div_le_div_iff₀ (pow_pos hm2 2) (mul_pos hm1 hm2)]
      nlinarith
    push_cast at ih ⊢
    linarith

lemma sum_inv_sq_le_two (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (1 : ℝ) / ((j + 1 : ℝ) ^ 2)) ≤ 2 := by
  have h := sum_inv_sq_le_two_sub N
  have : (0 : ℝ) < 1 / (N + 1 : ℝ) := by positivity
  linarith

lemma sum_conv_sq_le_16 (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      ((N + 1 : ℝ) ^ 2) / (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2))) ≤ 16 := by
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ((N + 1 : ℝ) ^ 2) / (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2)) ≤
        4 * (1 / ((n + 1 : ℝ) ^ 2)) + 4 * (1 / ((N - n + 1 : ℝ) ^ 2)) := by
    intro n hn
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hmn1 : (0 : ℝ) < (N - n : ℕ) + 1 := by positivity
    have hcast : (N - n : ℝ) + 1 = ((N - n : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hnN]
    rw [hcast]
    by_cases hhalf : (N + 1 : ℝ) ≤ 2 * (n + 1 : ℝ)
    · have hsq : (N + 1 : ℝ) ^ 2 ≤ 4 * (n + 1 : ℝ) ^ 2 := by nlinarith
      have h1 : ((N + 1 : ℝ) ^ 2) / (((n + 1 : ℝ) ^ 2) * (((N - n : ℕ) : ℝ) + 1) ^ 2) ≤
          4 * (1 / (((N - n : ℕ) : ℝ) + 1) ^ 2) := by
        rw [mul_one_div, div_le_div_iff₀ (mul_pos (pow_pos hn1 2) (pow_pos hmn1 2)) (pow_pos hmn1 2)]
        nlinarith [pow_pos hmn1 2]
      linarith [show (0 : ℝ) ≤ 4 * (1 / ((n + 1 : ℝ) ^ 2)) by positivity]
    · push Not at hhalf
      have hmn_ge : (N + 1 : ℝ) ≤ 2 * (((N - n : ℕ) : ℝ) + 1) := by
        rw [Nat.cast_sub hnN]; linarith
      have hsq : (N + 1 : ℝ) ^ 2 ≤ 4 * (((N - n : ℕ) : ℝ) + 1) ^ 2 := by nlinarith
      have h1 : ((N + 1 : ℝ) ^ 2) / (((n + 1 : ℝ) ^ 2) * (((N - n : ℕ) : ℝ) + 1) ^ 2) ≤
          4 * (1 / ((n + 1 : ℝ) ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ (mul_pos (pow_pos hn1 2) (pow_pos hmn1 2)) (pow_pos hn1 2)]
        nlinarith [pow_pos hn1 2]
      linarith [show (0 : ℝ) ≤ 4 * (1 / (((N - n : ℕ) : ℝ) + 1) ^ 2) by positivity]
  have hsum_rev : (∑ n ∈ Finset.range (N + 1), (1 : ℝ) / ((N - n + 1 : ℝ) ^ 2)) =
      ∑ j ∈ Finset.range (N + 1), (1 : ℝ) / ((j + 1 : ℝ) ^ 2) := by
    refine Finset.sum_bij (fun n _ => N - n) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_range] at hn ⊢; omega
    · intro a ha b hb hab; simp only [Finset.mem_range] at ha hb; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      exact ⟨N - j, Finset.mem_range.mpr (by omega), by omega⟩
    · intro n hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [Nat.cast_sub hnN]
  calc ∑ n ∈ Finset.range (N + 1),
        ((N + 1 : ℝ) ^ 2) / (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2))
      ≤ ∑ n ∈ Finset.range (N + 1),
          (4 * (1 / ((n + 1 : ℝ) ^ 2)) + 4 * (1 / ((N - n + 1 : ℝ) ^ 2))) := Finset.sum_le_sum hterm
    _ = 4 * (∑ n ∈ Finset.range (N + 1), (1 : ℝ) / ((n + 1 : ℝ) ^ 2)) +
          4 * (∑ n ∈ Finset.range (N + 1), (1 : ℝ) / ((N - n + 1 : ℝ) ^ 2)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 8 * (∑ j ∈ Finset.range (N + 1), (1 : ℝ) / ((j + 1 : ℝ) ^ 2)) := by rw [hsum_rev]; ring
    _ ≤ 8 * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le_two N) (by norm_num)
    _ = 16 := by norm_num

/-- **Banach Algebra Submultiplicativity of `GevBound`**:
`GevBound ρ M₁ a → GevBound ρ M₂ b → GevBound ρ (16 * M₁ * M₂) (mulCoeff a b)`. -/
theorem gevBound_mul {ρ M₁ M₂ : ℝ} (hρ : 0 ≤ ρ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    {a b : LogCoeff} (ha : GevBound ρ M₁ a) (hb : GevBound ρ M₂ b) :
    GevBound ρ (16 * M₁ * M₂) (mulCoeff a b) := by
  refine ⟨fun N K hNK => ?_, fun N K hKN => ?_⟩
  · dsimp only [mulCoeff]
    refine Finset.sum_eq_zero fun n hn => Finset.sum_eq_zero fun k hk => ?_
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hkn : n < k
    · rw [ha.1 n k hkn, zero_mul]
    · rw [hb.1 (N - n) (K - k) (by omega), mul_zero]
  · dsimp only [mulCoeff]
    have hstep : ‖∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (K + 1), a n k * b (N - n) (K - k)‖ ≤
        ∑ n ∈ Finset.range (N + 1),
          (M₁ * M₂ * ρ ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) /
            (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      let F := (Finset.range (K + 1)).filter (fun k => k ≤ n ∧ K - k ≤ N - n)
      have hfilt : (∑ k ∈ Finset.range (K + 1), a n k * b (N - n) (K - k)) =
          ∑ k ∈ F, a n k * b (N - n) (K - k) := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun k => k ≤ n ∧ K - k ≤ N - n) (Finset.range (K + 1)))]
        intro k hk hnot
        simp only [Finset.mem_filter, not_and, not_le] at hnot
        by_cases hkn : k ≤ n
        · rw [hb.1 (N - n) (K - k) (hnot hk hkn), mul_zero]
        · rw [ha.1 n k (by omega), zero_mul]
      rw [hfilt]
      have hcast_mn : ((N - n : ℕ) : ℝ) + 1 = (N - n + 1 : ℝ) := by rw [Nat.cast_sub hnN]
      calc ‖∑ k ∈ F, a n k * b (N - n) (K - k)‖
          ≤ ∑ k ∈ F, ‖a n k‖ * ‖b (N - n) (K - k)‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by rw [norm_mul])
        _ ≤ ∑ k ∈ F,
              (M₁ * ρ ^ n * (n.factorial : ℝ) / (((n + 1 : ℝ) ^ 2) * (k.factorial : ℝ))) *
                (M₂ * ρ ^ (N - n) * ((N - n).factorial : ℝ) /
                  ((((N - n : ℕ) : ℝ) + 1) ^ 2 * ((K - k).factorial : ℝ))) := by
            refine Finset.sum_le_sum fun k hk => ?_
            simp only [F, Finset.mem_filter, Finset.mem_range] at hk
            exact mul_le_mul (ha.2 n k hk.2.1) (hb.2 (N - n) (K - k) hk.2.2) (norm_nonneg _) (by positivity)
        _ = ((M₁ * M₂ * ρ ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) /
              (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2))) *
              ((∑ k ∈ F, (K.choose k : ℝ)) / (N.choose n : ℝ)) := by
            rw [Finset.sum_div, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k hk => ?_
            simp only [F, Finset.mem_filter, Finset.mem_range] at hk
            have hkK : k ≤ K := Nat.lt_succ_iff.mp hk.1
            have hpow : ρ ^ n * ρ ^ (N - n) = ρ ^ N := by rw [← pow_add, Nat.add_sub_of_le hnN]
            have hfd := fact_div_mul_fact_div hnN hkK
            rw [hcast_mn]
            have h1 : (M₁ * ρ ^ n * (n.factorial : ℝ) / (((n + 1 : ℝ) ^ 2) * (k.factorial : ℝ))) *
                (M₂ * ρ ^ (N - n) * ((N - n).factorial : ℝ) / ((N - n + 1 : ℝ) ^ 2 * ((K - k).factorial : ℝ))) =
                (M₁ * M₂ * (ρ ^ n * ρ ^ (N - n))) / (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2)) *
                  (((n.factorial : ℝ) / (k.factorial : ℝ)) * (((N - n).factorial : ℝ) / ((K - k).factorial : ℝ))) := by
              have hne1 : (n + 1 : ℝ) ^ 2 ≠ 0 := by positivity
              have hne2 : (N - n + 1 : ℝ) ^ 2 ≠ 0 := by rw [← hcast_mn]; positivity
              have hne3 : (k.factorial : ℝ) ≠ 0 := by positivity
              have hne4 : ((K - k).factorial : ℝ) ≠ 0 := by positivity
              field_simp [hne1, hne2, hne3, hne4]
            rw [h1, hpow, hfd]; ring
        _ ≤ ((M₁ * M₂ * ρ ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) /
              (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2))) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · rw [div_le_one (by exact_mod_cast Nat.choose_pos hnN)]
              exact_mod_cast sum_choose_le_choose hnN hKN
            · have : 0 ≤ (N - n + 1 : ℝ) ^ 2 := sq_nonneg _
              positivity
        _ = (M₁ * M₂ * ρ ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ))) /
              (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2)) := mul_one _
    have hN1_pos : (0 : ℝ) < (N + 1 : ℝ) ^ 2 := by positivity
    calc ‖∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (K + 1), a n k * b (N - n) (K - k)‖
        ≤ (M₁ * M₂ * ρ ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ)) / ((N + 1 : ℝ) ^ 2)) *
            ∑ n ∈ Finset.range (N + 1),
              ((N + 1 : ℝ) ^ 2) / (((n + 1 : ℝ) ^ 2) * ((N - n + 1 : ℝ) ^ 2)) := by
          refine hstep.trans (le_of_eq ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          field_simp [hN1_pos.ne']
      _ ≤ (M₁ * M₂ * ρ ^ N * ((N.factorial : ℝ) / (K.factorial : ℝ)) / ((N + 1 : ℝ) ^ 2)) * 16 :=
          mul_le_mul_of_nonneg_left (sum_conv_sq_le_16 N) (by positivity)
      _ = 16 * M₁ * M₂ * ρ ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) := by
          have hKf : (K.factorial : ℝ) ≠ 0 := by positivity
          field_simp [hN1_pos.ne', hKf]

/-- Formal powers `powCoeff a j` of a coefficient table `a`. -/
@[expose] def powCoeff (a : LogCoeff) : ℕ → LogCoeff
  | 0 => constCoeff 1
  | j + 1 => mulCoeff (powCoeff a j) a

lemma powCoeff_zero_lt {a : LogCoeff} (ha0 : ∀ k, a 0 k = 0) :
    ∀ j n k, n < j → powCoeff a j n k = 0 := by
  intro j
  induction j with
  | zero => intro n _ hn; omega
  | succ j ih =>
    intro n k hnj
    dsimp only [powCoeff, mulCoeff]
    refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun i _ => ?_
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    by_cases hmj : m < j
    · rw [ih m i hmj, zero_mul]
    · have hnm0 : n - m = 0 := by omega
      rw [hnm0, ha0 (k - i), mul_zero]

lemma gevBound_constCoeff_one {ρ : ℝ} (hρ : 0 ≤ ρ) : GevBound ρ 1 (constCoeff 1) := by
  refine ⟨fun n k hnk => by simp [constCoeff]; omega, fun n k _ => ?_⟩
  dsimp only [constCoeff]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩; simp
  · simp; positivity

lemma gevBound_powCoeff {ρ M : ℝ} (hρ : 0 ≤ ρ) (hM : 0 ≤ M) {a : LogCoeff}
    (ha : GevBound ρ M a) :
    ∀ j : ℕ, 1 ≤ j → GevBound ρ ((16 * M) ^ j / 16) (powCoeff a j) := by
  intro j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  induction m with
  | zero =>
    have hmul : powCoeff a 1 = mulCoeff (constCoeff 1) a := rfl
    have h1 : ∀ n k, mulCoeff (constCoeff 1) a n k = a n k := by
      intro n k
      dsimp only [mulCoeff, constCoeff]
      rw [Finset.sum_eq_single 0]
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro i _ hi; simp [hi]
        · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
      · intro r _ hr; refine Finset.sum_eq_zero fun i _ => by simp [hr]
      · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
    refine ⟨fun n k hnk => by rw [hmul, h1]; exact ha.1 n k hnk, fun n k hkn => ?_⟩
    rw [hmul, h1]
    have hM' : (16 * M) ^ 1 / 16 = M := by ring
    rw [hM']; exact ha.2 n k hkn
  | succ m ih =>
    have hprev := ih (Nat.succ_pos m)
    have hmul := gevBound_mul hρ (by positivity) hM hprev ha
    have hconst : 16 * ((16 * M) ^ (m + 1) / 16) * M = (16 * M) ^ (m + 2) / 16 := by
      rw [pow_succ]; ring
    rwa [hconst] at hmul

/-- Formal shift operator `shiftL a` representing `(log v + g(v)) / v`. -/
@[expose] def shiftL (a : LogCoeff) : LogCoeff
  | 0, _ => 0
  | n + 1, k => (if n = 0 ∧ k = 1 then 1 else 0) + a n k

/-- Formal `log (1 + u)` coefficient table (for `u 0 _ = 0`). -/
@[expose] def log1pCoeff (u : LogCoeff) : LogCoeff :=
  fun N K => ∑ j ∈ Finset.Ico 1 (N + 1), ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * powCoeff u j N K

/-- Formal `(1 + u)^{-m}` coefficient table (for `m ≥ 1`, `u 0 _ = 0`). -/
@[expose] def negPowCoeff (m : ℕ) (u : LogCoeff) : LogCoeff :=
  fun N K => ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * powCoeff u j N K

/-- Formal `y(v + L + g) = ∑_{m ≥ 1} m! v^{-m} (1 + u)^{-m}` coefficient table. -/
@[expose] def yCoeff (u : LogCoeff) : LogCoeff :=
  fun N K => ∑ m ∈ Finset.Ico 1 (N + 1), (m.factorial : ℂ) * negPowCoeff m u (N - m) K

/-- Formal fixed-point operator `phiOp a = log(1 + shiftL a) - log(1 + y(shiftL a))`. -/
@[expose] def phiOp (a : LogCoeff) : LogCoeff :=
  fun N K => log1pCoeff (shiftL a) N K - log1pCoeff (yCoeff (shiftL a)) N K

/-- Degree-cutoff congruence: `phiOp a N K` depends ONLY on `a m _` for `m < N`! -/
lemma powCoeff_congr_lt {a b : LogCoeff}
    {M : ℕ} (heq : ∀ n ≤ M, ∀ k, a n k = b n k) :
    ∀ j n k, n ≤ M → powCoeff a j n k = powCoeff b j n k := by
  intro j
  induction j with
  | zero => intro n k _; rfl
  | succ j ih =>
    intro n k hnM
    dsimp only [powCoeff, mulCoeff]
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun i _ => ?_
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [ih m i (hmle.trans hnM), heq (n - m) (by omega) (k - i)]

lemma shiftL_congr_le {a b : LogCoeff} {M : ℕ} (heq : ∀ n < M, ∀ k, a n k = b n k) :
    ∀ n ≤ M, ∀ k, shiftL a n k = shiftL b n k := by
  intro n hn k
  cases n with
  | zero => rfl
  | succ m =>
    dsimp only [shiftL]
    rw [heq m (by omega) k]

lemma phiOp_congr_lt {a b : LogCoeff} {N : ℕ} (heq : ∀ n < N, ∀ k, a n k = b n k) :
    ∀ K, phiOp a N K = phiOp b N K := by
  intro K
  have hsh := shiftL_congr_le heq
  have hpow := powCoeff_congr_lt hsh
  have hlog1 : log1pCoeff (shiftL a) N K = log1pCoeff (shiftL b) N K := by
    dsimp only [log1pCoeff]
    refine Finset.sum_congr rfl fun j _ => by rw [hpow j N K le_rfl]
  have hy_eq : ∀ n ≤ N, ∀ k, yCoeff (shiftL a) n k = yCoeff (shiftL b) n k := by
    intro n hn k
    dsimp only [yCoeff, negPowCoeff]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpow j (n - m) k (by omega)]
  have hpowy := powCoeff_congr_lt hy_eq
  have hlog2 : log1pCoeff (yCoeff (shiftL a)) N K = log1pCoeff (yCoeff (shiftL b)) N K := by
    dsimp only [log1pCoeff]
    refine Finset.sum_congr rfl fun j _ => by rw [hpowy j N K le_rfl]
  dsimp only [phiOp]
  rw [hlog1, hlog2]

/-- Plain structural recursion constructing the prefix of `wCoeff` through degree `N`. -/
@[expose] def wCoeffPrefix : ℕ → LogCoeff
  | 0 => fun _ _ => 0
  | N + 1 => fun n k =>
      if n ≤ N then wCoeffPrefix N n k
      else if n = N + 1 then phiOp (wCoeffPrefix N) (N + 1) k
      else 0

/-- The formal Gevrey-1 log-power coefficients `wCoeff` of `w_plus(v) - v - log v`. -/
@[expose] def wCoeff (n k : ℕ) : ℂ := wCoeffPrefix n n k

lemma wCoeffPrefix_stable : ∀ M N n k, n ≤ M → M ≤ N → wCoeffPrefix N n k = wCoeffPrefix M n k := by
  intro M N
  induction N with
  | zero =>
    intro n k _ hM0
    have h0 : M = 0 := by omega
    rw [h0]
  | succ N ih =>
    intro n k hnM hMN
    by_cases hEq : M = N + 1
    · subst hEq; rfl
    · have hMle : M ≤ N := by omega
      dsimp only [wCoeffPrefix]
      simp only [hnM.trans hMle, ↓reduceIte]
      exact ih n k hnM hMle

lemma wCoeffPrefix_eq_wCoeff {M n k : ℕ} (hn : n ≤ M) :
    wCoeffPrefix M n k = wCoeff n k :=
  wCoeffPrefix_stable n M n k le_rfl hn

lemma wCoeff_zero (k : ℕ) : wCoeff 0 k = 0 := rfl

/-- Exact fixed-point identity for `wCoeff`: `wCoeff N K = phiOp wCoeff N K` for all `N, K`! -/
theorem wCoeff_eq_phiOp (N K : ℕ) : wCoeff N K = phiOp wCoeff N K := by
  cases N with
  | zero =>
    simp [wCoeff, wCoeffPrefix, phiOp, log1pCoeff]
  | succ M =>
    change wCoeffPrefix (M + 1) (M + 1) K = phiOp wCoeff (M + 1) K
    dsimp only [wCoeffPrefix]
    have h1 : ¬ (M + 1 ≤ M) := by omega
    simp only [h1, ↓reduceIte]
    refine phiOp_congr_lt (fun n hn k => wCoeffPrefix_eq_wCoeff (by omega)) K

/-- Fundamental `GevBound 2000` propagation lemma through `phiOp`:
`GevBound 2000 1 a → (∀ k, a 0 k = 0) → GevBound 2000 1 (phiOp a)`! -/
theorem gevBound_phiOp {a : LogCoeff} (ha0 : ∀ k, a 0 k = 0) (ha : GevBound 2000 1 a) :
    GevBound 2000 (1 / 250) (shiftL a) ∧
    GevBound 2000 (1 / 100) (yCoeff (shiftL a)) ∧
    GevBound 2000 1 (phiOp a) := by
  have hrho : (0 : ℝ) ≤ 2000 := by norm_num
  -- 1. `GevBound 2000 (1/250) (shiftL a)`
  have hsh : GevBound 2000 (1 / 250) (shiftL a) := by
    refine ⟨fun n k hnk => ?_, fun n k hkn => ?_⟩
    · cases n with
      | zero => rfl
      | succ m =>
        dsimp only [shiftL]
        have hif : ¬ (m = 0 ∧ k = 1) := by omega
        simp only [hif, ↓reduceIte, zero_add]
        exact ha.1 m k (by omega)
    · cases n with
      | zero => simp [shiftL]; positivity
      | succ m =>
        dsimp only [shiftL]
        by_cases hm0 : m = 0
        · subst hm0
          rw [ha0 k, add_zero]
          split_ifs with h
          · rcases h with ⟨_, rfl⟩
            norm_num [Nat.factorial]
          · simp; positivity
        · simp only [hm0, false_and, ↓reduceIte, zero_add]
          by_cases hkm : k ≤ m
          · have hb := ha.2 m k hkm
            have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
            have hfac : ((m + 1).factorial : ℝ) = (m + 1 : ℝ) * (m.factorial : ℝ) := by
              exact_mod_cast Nat.factorial_succ m
            have hratio : ((m + 1 + 1 : ℝ) ^ 2) ≤ 8 * ((m + 1 : ℝ) ^ 2 * (m + 1 : ℝ)) := by
              have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
              nlinarith
            have hpow : (2000 : ℝ) ^ (m + 1) = 2000 * (2000 : ℝ) ^ m := by rw [pow_succ]; ring
            have hcast_m1 : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 1 + 1 := by push_cast; ring
            rw [hcast_m1]
            calc ‖a m k‖ ≤ 1 * 2000 ^ m * (m.factorial : ℝ) / (((m + 1 : ℝ) ^ 2) * (k.factorial : ℝ)) := hb
              _ ≤ (1 / 250) * 2000 ^ (m + 1) * ((m + 1).factorial : ℝ) /
                    (((m + 1 + 1 : ℝ) ^ 2) * (k.factorial : ℝ)) := by
                  rw [hpow, hfac]
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  have hnn : 0 ≤ (2000 : ℝ) ^ m * (m.factorial : ℝ) * (k.factorial : ℝ) := by positivity
                  have heq1 : 1 * (2000 : ℝ) ^ m * (m.factorial : ℝ) * (((m + 1 + 1 : ℝ) ^ 2) * (k.factorial : ℝ)) =
                      ((2000 : ℝ) ^ m * (m.factorial : ℝ) * (k.factorial : ℝ)) * ((m + 1 + 1 : ℝ) ^ 2) := by ring
                  have heq2 : (1 / 250 : ℝ) * (2000 * 2000 ^ m) * ((m + 1 : ℝ) * (m.factorial : ℝ)) *
                        (((m + 1 : ℝ) ^ 2) * (k.factorial : ℝ)) =
                      ((2000 : ℝ) ^ m * (m.factorial : ℝ) * (k.factorial : ℝ)) * (8 * ((m + 1 : ℝ) ^ 2 * (m + 1 : ℝ))) := by
                    ring
                  rw [heq1, heq2]
                  exact mul_le_mul_of_nonneg_left hratio hnn
          · rw [ha.1 m k (by omega), norm_zero]; positivity
  -- Helper: `GevBound 2000 M u → 16 * M ≤ 1 / 4 → GevBound 2000 (2 * M) (log1pCoeff u)`!
  have hlog_bound : ∀ (u : LogCoeff) (M : ℝ), 0 ≤ M → 16 * M ≤ 1 / 4 →
      GevBound 2000 M u → GevBound 2000 (2 * M) (log1pCoeff u) := by
    intro u M hM hM4 hu
    refine ⟨fun N K hNK => ?_, fun N K hKN => ?_⟩
    · dsimp only [log1pCoeff]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
      rw [(gevBound_powCoeff hrho hM hu j hj1).1 N K hNK, mul_zero]
    · dsimp only [log1pCoeff]
      have hgeom : (∑ j ∈ Finset.Ico 1 (N + 1), (16 * M) ^ j / 16) ≤ 2 * M := by
        have hle : ∀ j ∈ Finset.Ico 1 (N + 1), (16 * M) ^ j / 16 ≤ M * (1 / 4 : ℝ) ^ (j - 1) := by
          intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
          obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ']
          have hp : (16 * M) ^ p ≤ (1 / 4 : ℝ) ^ p := pow_le_pow_left₀ (by positivity) hM4 p
          have : 16 * M * (16 * M) ^ p / 16 = M * (16 * M) ^ p := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hp hM
        calc ∑ j ∈ Finset.Ico 1 (N + 1), (16 * M) ^ j / 16
            ≤ ∑ j ∈ Finset.Ico 1 (N + 1), M * (1 / 4 : ℝ) ^ (j - 1) := Finset.sum_le_sum hle
          _ = M * ∑ p ∈ Finset.range N, (1 / 4 : ℝ) ^ p := by
              rw [← Finset.mul_sum]
              congr 1
              refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
              · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
              · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
              · intro p hp; simp only [Finset.mem_range] at hp
                exact ⟨p + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel p 1⟩
              · intro _ _; rfl
          _ ≤ M * 2 := by
              refine mul_le_mul_of_nonneg_left ?_ hM
              rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
              have hnn : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ N := by positivity
              have hden : (1 / 4 : ℝ) - 1 = -(3 / 4) := by norm_num
              rw [hden]; linarith
          _ = 2 * M := by ring
      calc ‖∑ j ∈ Finset.Ico 1 (N + 1), ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * powCoeff u j N K‖
          ≤ ∑ j ∈ Finset.Ico 1 (N + 1), ‖((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * powCoeff u j N K‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.Ico 1 (N + 1),
              ((16 * M) ^ j / 16) * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
            rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
            have hinv : (1 : ℝ) / (j : ℝ) ≤ 1 := by
              rw [div_le_one (by positivity)]; exact_mod_cast hj1
            have hb := (gevBound_powCoeff hrho hM hu j hj1).2 N K hKN
            calc 1 / (j : ℝ) * ‖powCoeff u j N K‖ ≤ 1 * ‖powCoeff u j N K‖ :=
                  mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
              _ = ‖powCoeff u j N K‖ := one_mul _
              _ ≤ ((16 * M) ^ j / 16) * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
                  exact hb.trans (le_of_eq (by ring))
        _ = (∑ j ∈ Finset.Ico 1 (N + 1), (16 * M) ^ j / 16) *
              (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
            rw [← Finset.sum_mul]
        _ ≤ (2 * M) * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
            mul_le_mul_of_nonneg_right hgeom (by positivity)
        _ = (2 * M) * 2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) := by ring
  -- 2. `GevBound 2000 (2 * 2^m) (negPowCoeff m (shiftL a))` for `m ≥ 1`
  have hnegPow : ∀ m ≥ 1, GevBound 2000 (2 * (2 : ℝ) ^ m) (negPowCoeff m (shiftL a)) := by
    intro m hm
    refine ⟨fun N K hNK => ?_, fun N K hKN => ?_⟩
    · dsimp only [negPowCoeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      cases j with
      | zero => change _ * constCoeff 1 N K = 0; rw [(gevBound_constCoeff_one hrho).1 N K hNK, mul_zero]
      | succ p => rw [(gevBound_powCoeff hrho (by norm_num) hsh (p + 1) (Nat.succ_pos p)).1 N K hNK, mul_zero]
    · dsimp only [negPowCoeff]
      have hterm : ∀ j ∈ Finset.range (N + 1),
          ‖((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * powCoeff (shiftL a) j N K‖ ≤
            ((2 : ℝ) ^ m * (1 / 4 : ℝ) ^ j) *
              (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
        intro j _
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
        have hch : ((m + j - 1).choose j : ℝ) ≤ (2 : ℝ) ^ (m + j) := by
          let q : ℕ := m + j - 1
          have hq : q + 1 = m + j := by dsimp [q]; omega
          have h1 : q.choose j ≤ ∑ i ∈ Finset.range (q + 1), q.choose i := by
            by_cases hj : j ≤ q
            · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
            · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
          rw [Nat.sum_range_choose] at h1
          have h3 : 2 ^ q ≤ 2 ^ (m + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
          exact_mod_cast h1.trans h3
        cases j with
        | zero =>
          have hb := (gevBound_constCoeff_one hrho).2 N K hKN
          have h1 : ((m + 0 - 1).choose 0 : ℝ) = 1 := by simp
          rw [h1, one_mul, pow_zero, mul_one]
          have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
          calc ‖powCoeff (shiftL a) 0 N K‖
              ≤ 1 * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
                hb.trans (le_of_eq (by ring))
            _ ≤ (2 : ℝ) ^ m * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
                mul_le_mul_of_nonneg_right h2m (by positivity)
        | succ p =>
          have hb := (gevBound_powCoeff hrho (by norm_num) hsh (p + 1) (Nat.succ_pos p)).2 N K hKN
          have hcoef : ((m + (p + 1) - 1).choose (p + 1) : ℝ) * ((16 * (1 / 250 : ℝ)) ^ (p + 1) / 16) ≤
              (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ (p + 1) := by
            have h16 : (16 * (1 / 250 : ℝ)) ≤ 1 / 8 := by norm_num
            have hp1 : (16 * (1 / 250 : ℝ)) ^ (p + 1) ≤ (1 / 8 : ℝ) ^ (p + 1) :=
              pow_le_pow_left₀ (by norm_num) h16 (p + 1)
            calc ((m + (p + 1) - 1).choose (p + 1) : ℝ) * ((16 * (1 / 250 : ℝ)) ^ (p + 1) / 16)
                ≤ (2 : ℝ) ^ (m + (p + 1)) * ((1 / 8 : ℝ) ^ (p + 1) / 16) :=
                  mul_le_mul hch (by linarith) (by positivity) (by positivity)
              _ = (2 : ℝ) ^ m * ((2 * (1 / 8 : ℝ)) ^ (p + 1) / 16) := by
                  rw [pow_add, mul_pow]; ring
              _ = (2 : ℝ) ^ m * ((1 / 4 : ℝ) ^ (p + 1) / 16) := by norm_num
              _ ≤ (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ (p + 1) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (p + 1) := by positivity
                  linarith
          calc ((m + (p + 1) - 1).choose (p + 1) : ℝ) * ‖powCoeff (shiftL a) (p + 1) N K‖
              ≤ ((m + (p + 1) - 1).choose (p + 1) : ℝ) *
                  (((16 * (1 / 250 : ℝ)) ^ (p + 1) / 16) *
                    (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)))) :=
                mul_le_mul_of_nonneg_left (hb.trans (le_of_eq (by ring))) (by positivity)
            _ = (((m + (p + 1) - 1).choose (p + 1) : ℝ) * ((16 * (1 / 250 : ℝ)) ^ (p + 1) / 16)) *
                  (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by ring
            _ ≤ ((2 : ℝ) ^ m * (1 / 4 : ℝ) ^ (p + 1)) *
                  (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
                mul_le_mul_of_nonneg_right hcoef (by positivity)
      have hgeom : ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ j ≤ 2 * (2 : ℝ) ^ m := by
        rw [← Finset.mul_sum, mul_comm (2 : ℝ)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
        have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (N + 1) := by positivity
        have hden : (1 / 4 : ℝ) - 1 = -(3 / 4) := by norm_num
        rw [hden]; linarith
      calc ‖∑ j ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * powCoeff (shiftL a) j N K‖
          ≤ ∑ j ∈ Finset.range (N + 1),
              ‖((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * powCoeff (shiftL a) j N K‖ := norm_sum_le _ _
        _ ≤ (∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ j) *
              (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
            rw [Finset.sum_mul]; exact Finset.sum_le_sum hterm
        _ ≤ (2 * (2 : ℝ) ^ m) * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
            mul_le_mul_of_nonneg_right hgeom (by positivity)
        _ = 2 * (2 : ℝ) ^ m * 2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) := by ring
  -- 3. `GevBound 2000 (1/100) (yCoeff (shiftL a))`
  have hy : GevBound 2000 (1 / 100) (yCoeff (shiftL a)) := by
    refine ⟨fun N K hNK => ?_, fun N K hKN => ?_⟩
    · dsimp only [yCoeff]
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
      rw [(hnegPow m hm1).1 (N - m) K (by omega), mul_zero]
    · dsimp only [yCoeff]
      have hterm : ∀ m ∈ Finset.Ico 1 (N + 1),
          ‖(m.factorial : ℂ) * negPowCoeff m (shiftL a) (N - m) K‖ ≤
            (2 * (1 / 250 : ℝ) ^ m) *
              (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
        intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
        have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hm).2
        rw [norm_mul, Complex.norm_natCast]
        by_cases hKnm : K ≤ N - m
        · have hb := (hnegPow m hm1).2 (N - m) K hKnm
          have hfac_prod : (m.factorial : ℝ) * ((N - m).factorial : ℝ) ≤ (N.factorial : ℝ) := by
            have h1 := Nat.choose_mul_factorial_mul_factorial hmN
            have hpos : 1 ≤ N.choose m := Nat.choose_pos hmN
            exact_mod_cast (show m.factorial * (N - m).factorial ≤ N.factorial by nlinarith)
          have hsq_ratio : ((N + 1 : ℝ) ^ 2) ≤ (4 : ℝ) ^ m * (((N - m : ℕ) : ℝ) + 1) ^ 2 := by
            have hlin : (N + 1 : ℝ) ≤ (m + 1 : ℝ) * (((N - m : ℕ) : ℝ) + 1) := by
              rw [Nat.cast_sub hmN]
              have hm_nn : (0 : ℝ) ≤ m := by positivity
              have hNm_nn : (0 : ℝ) ≤ (N : ℝ) - m := sub_nonneg.mpr (by exact_mod_cast hmN)
              nlinarith
            have hm2 : (m + 1 : ℝ) ≤ (2 : ℝ) ^ m := nat_succ_le_two_pow m
            have hlin2 : (N + 1 : ℝ) ≤ (2 : ℝ) ^ m * (((N - m : ℕ) : ℝ) + 1) :=
              hlin.trans (mul_le_mul_of_nonneg_right hm2 (by positivity))
            have h4 : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num
            nlinarith [sq_nonneg ((N + 1 : ℝ)), mul_pow ((2 : ℝ) ^ m) (((N - m : ℕ) : ℝ) + 1) 2]
          have hpow2000 : (2000 : ℝ) ^ (N - m) * (2000 : ℝ) ^ m = (2000 : ℝ) ^ N := by
            rw [← pow_add, Nat.sub_add_cancel hmN]
          have h8 : (2 : ℝ) ^ m * (4 : ℝ) ^ m / (2000 : ℝ) ^ m = (1 / 250 : ℝ) ^ m := by
            rw [← mul_pow, ← div_pow]; norm_num
          calc (m.factorial : ℝ) * ‖negPowCoeff m (shiftL a) (N - m) K‖
              ≤ (m.factorial : ℝ) * (2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * ((N - m).factorial : ℝ) /
                  ((((N - m : ℕ) : ℝ) + 1) ^ 2 * (K.factorial : ℝ))) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = 2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * ((m.factorial : ℝ) * ((N - m).factorial : ℝ)) /
                  ((((N - m : ℕ) : ℝ) + 1) ^ 2 * (K.factorial : ℝ)) := by ring
            _ ≤ 2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * (N.factorial : ℝ) /
                  ((((N - m : ℕ) : ℝ) + 1) ^ 2 * (K.factorial : ℝ)) := by gcongr
            _ ≤ 2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * (N.factorial : ℝ) * ((4 : ℝ) ^ m / ((N + 1 : ℝ) ^ 2)) /
                  (K.factorial : ℝ) := by
                have hdiv : 1 / (((N - m : ℕ) : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ m / ((N + 1 : ℝ) ^ 2) := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
                have hrew1 : 2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * (N.factorial : ℝ) /
                      ((((N - m : ℕ) : ℝ) + 1) ^ 2 * (K.factorial : ℝ)) =
                    (2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * (N.factorial : ℝ) / (K.factorial : ℝ)) *
                      (1 / (((N - m : ℕ) : ℝ) + 1) ^ 2) := by
                  have hne1 : (((N - m : ℕ) : ℝ) + 1) ^ 2 ≠ 0 := by positivity
                  have hne2 : (K.factorial : ℝ) ≠ 0 := by positivity
                  field_simp [hne1, hne2]
                have hrew2 : 2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * (N.factorial : ℝ) *
                      ((4 : ℝ) ^ m / ((N + 1 : ℝ) ^ 2)) / (K.factorial : ℝ) =
                    (2 * (2 : ℝ) ^ m * 2000 ^ (N - m) * (N.factorial : ℝ) / (K.factorial : ℝ)) *
                      ((4 : ℝ) ^ m / ((N + 1 : ℝ) ^ 2)) := by ring
                rw [hrew1, hrew2]
                exact mul_le_mul_of_nonneg_left hdiv (by positivity)
            _ = (2 * (1 / 250 : ℝ) ^ m) *
                  (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
                rw [← h8, ← hpow2000]
                have h2000ne : (2000 : ℝ) ^ m ≠ 0 := by positivity
                field_simp [h2000ne]
        · rw [(hnegPow m hm1).1 (N - m) K (by omega), norm_zero, mul_zero]; positivity
      have hgeom : ∑ m ∈ Finset.Ico 1 (N + 1), 2 * (1 / 250 : ℝ) ^ m ≤ 1 / 100 := by
        have hsum : ∑ m ∈ Finset.Ico 1 (N + 1), 2 * (1 / 250 : ℝ) ^ m =
            (2 / 250) * ∑ p ∈ Finset.range N, (1 / 250 : ℝ) ^ p := by
          rw [← Finset.mul_sum]
          have hbij : ∑ m ∈ Finset.Ico 1 (N + 1), (1 / 250 : ℝ) ^ m =
              (1 / 250) * ∑ p ∈ Finset.range N, (1 / 250 : ℝ) ^ p := by
            rw [Finset.mul_sum]
            refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
            · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
            · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
            · intro p hp; simp only [Finset.mem_range] at hp
              exact ⟨p + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel p 1⟩
            · intro m hm
              have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
              obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
              rw [Nat.add_sub_cancel, pow_succ']
          rw [hbij]; ring
        rw [hsum, geom_sum_eq (by norm_num : (1 / 250 : ℝ) ≠ 1)]
        have : (0 : ℝ) ≤ (1 / 250 : ℝ) ^ N := by positivity
        have hden : (1 / 250 : ℝ) - 1 = -(249 / 250) := by norm_num
        rw [hden]; linarith
      calc ‖∑ m ∈ Finset.Ico 1 (N + 1), (m.factorial : ℂ) * negPowCoeff m (shiftL a) (N - m) K‖
          ≤ ∑ m ∈ Finset.Ico 1 (N + 1), ‖(m.factorial : ℂ) * negPowCoeff m (shiftL a) (N - m) K‖ :=
            norm_sum_le _ _
        _ ≤ (∑ m ∈ Finset.Ico 1 (N + 1), 2 * (1 / 250 : ℝ) ^ m) *
              (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
            rw [Finset.sum_mul]; exact Finset.sum_le_sum hterm
        _ ≤ (1 / 100) * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
            mul_le_mul_of_nonneg_right hgeom (by positivity)
        _ = (1 / 100) * 2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) := by ring
  -- 4. Combine `log1pCoeff (shiftL a)` and `log1pCoeff (yCoeff (shiftL a))`!
  have hlog1 := hlog_bound (shiftL a) (1 / 250) (by norm_num) (by norm_num) hsh
  have hlog2 := hlog_bound (yCoeff (shiftL a)) (1 / 100) (by norm_num) (by norm_num) hy
  refine ⟨hsh, hy, fun N K hNK => ?_, fun N K hKN => ?_⟩
  · dsimp only [phiOp]; rw [hlog1.1 N K hNK, hlog2.1 N K hNK, sub_zero]
  · dsimp only [phiOp]
    have hnn : 0 ≤ (2000 : ℝ) ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) := by
      positivity
    calc ‖log1pCoeff (shiftL a) N K - log1pCoeff (yCoeff (shiftL a)) N K‖
        ≤ ‖log1pCoeff (shiftL a) N K‖ + ‖log1pCoeff (yCoeff (shiftL a)) N K‖ := norm_sub_le _ _
      _ ≤ (2 * (1 / 250)) * 2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) +
            (2 * (1 / 100)) * 2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) :=
          add_le_add (hlog1.2 N K hKN) (hlog2.2 N K hKN)
      _ = (2 * (1 / 250) + 2 * (1 / 100)) *
            (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by ring
      _ ≤ 1 * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_right (by norm_num) hnn
      _ = 1 * 2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) := by ring

/-- Unconditional `GevBound 2000 1 wCoeff` by plain induction on `N`! -/
theorem wCoeff_gevBound : GevBound 2000 1 wCoeff := by
  have hpref : ∀ N : ℕ, (∀ k, wCoeffPrefix N 0 k = 0) ∧ GevBound 2000 1 (wCoeffPrefix N) := by
    intro N
    induction N with
    | zero =>
      refine ⟨fun _ => rfl, fun _ _ _ => rfl, fun n k _ => by simp [wCoeffPrefix]; positivity⟩
    | succ M ih =>
      have hphi := (gevBound_phiOp ih.1 ih.2).2.2
      refine ⟨fun k => ?_, fun n k hnk => ?_, fun n k hkn => ?_⟩
      · dsimp only [wCoeffPrefix]; simp only [Nat.zero_le, ↓reduceIte]; exact ih.1 k
      · dsimp only [wCoeffPrefix]
        split_ifs with h1 h2
        · exact ih.2.1 n k hnk
        · subst h2; exact hphi.1 (M + 1) k hnk
        · rfl
      · dsimp only [wCoeffPrefix]
        split_ifs with h1 h2
        · exact ih.2.2 n k hkn
        · subst h2; exact hphi.2 (M + 1) k hkn
        · simp; positivity
  exact ⟨fun n k hnk => (hpref n).2.1 n k hnk, fun n k hkn => (hpref n).2.2 n k hkn⟩

/-! #### 3c. Finite-Degree Residual Bounds & `HasGev1Exp V_sec (fun v => F_plus v / v)` -/

/-- Large radius for the Gevrey-1 sector `V_sec` of `w_plus` and `F_plus`. -/
@[expose] def R_sec : ℝ := max (R_v + 1) ((10 : ℝ) ^ 14)

lemma R_sec_ge_Rv : R_v + 1 ≤ R_sec := le_max_left _ _
lemma R_sec_ge_1e14 : (10 : ℝ) ^ 14 ≤ R_sec := le_max_right _ _
lemma R_sec_pos : 0 < R_sec := lt_of_lt_of_le (by positivity) R_sec_ge_1e14

/-- Closed wide sector `V_sec ⊆ V_dom` on which `w_plus` and `F_plus / v` have Gevrey-1 log-power expansions. -/
@[expose] def V_sec : Set ℂ :=
  {v : ℂ | R_sec ≤ ‖v‖ ∧ -Real.pi + 2 * deltaV ≤ Complex.arg v ∧ Complex.arg v ≤ phiRay - 2 * deltaV}

lemma V_sec_subset_V_dom : V_sec ⊆ V_dom := by
  intro v ⟨hR, hlo, hhi⟩
  have hv_pos : 0 < ‖v‖ := lt_of_lt_of_le R_sec_pos hR
  have hv0 : v ≠ 0 := norm_pos_iff.mp hv_pos
  have hv_gt_Rv : R_v < ‖v‖ := lt_of_lt_of_le (by linarith [R_sec_ge_Rv]) hR
  by_cases hhalf : Complex.arg v ≤ -Real.pi / 2
  · left
    have hsin_ge : Real.sin deltaV ≤ -Real.sin (Complex.arg v) := by
      have h1 : -Real.sin (Complex.arg v) = Real.sin (Complex.arg v + Real.pi) :=
        (Real.sin_add_pi (Complex.arg v)).symm
      rw [h1]
      exact Real.strictMonoOn_sin.monotoneOn
        ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
        ⟨by linarith [deltaV_pos, Real.pi_pos], by linarith⟩ (by linarith [deltaV_pos])
    have him : v.im = ‖v‖ * Real.sin (Complex.arg v) := (Complex.norm_mul_sin_arg v).symm
    have hRv : Real.sin deltaV * R_v = 1024 * C_v := by
      dsimp only [R_v]; field_simp [sin_deltaV_pos.ne']
    have h1 : Real.sin deltaV * ‖v‖ ≤ -v.im := by rw [him]; nlinarith
    nlinarith [C_v_pos, sin_deltaV_pos]
  · push Not at hhalf
    right
    refine ⟨hv_gt_Rv, ?_⟩
    have hre : v.re = ‖v‖ * Real.cos (Complex.arg v) := (Complex.norm_mul_cos_arg v).symm
    have him : v.im = ‖v‖ * Real.sin (Complex.arg v) := (Complex.norm_mul_sin_arg v).symm
    have hd_eq : dPhi v = ‖v‖ * Real.sin (phiRay - Complex.arg v) := by
      dsimp only [dPhi]; rw [hre, him, Real.sin_sub]; ring
    have hsin_ge : Real.sin deltaV ≤ Real.sin (phiRay - Complex.arg v) := by
      set θ : ℝ := phiRay - Complex.arg v
      have hθ_lo : deltaV ≤ θ := by dsimp [θ]; linarith [deltaV_pos]
      have hθ_hi : θ ≤ Real.pi - deltaV := by dsimp [θ, phiRay, deltaV]; linarith [Real.pi_pos]
      by_cases hθ2 : θ ≤ Real.pi / 2
      · exact Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
          ⟨by linarith [deltaV_pos, Real.pi_pos], hθ2⟩ hθ_lo
      · push Not at hθ2
        rw [← Real.sin_pi_sub θ]
        exact Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
          ⟨by linarith [deltaV_pos, Real.pi_pos], by linarith⟩ (by linarith)
    rw [hd_eq]; nlinarith [sin_deltaV_pos]

/-- Angular margin on `V_sec`: for `v ∈ V_sec` and `w ∈ closedBall (v + log v) 1`,
`(Real.sin deltaV / 2) * ‖v‖ ≤ distPhi w`! -/
lemma V_sec_distPhi_ge {v : ℂ} (hv : v ∈ V_sec) {w : ℂ}
    (hw : w ∈ Metric.closedBall (v + Complex.log v) 1) :
    (Real.sin deltaV / 2) * ‖v‖ ≤ distPhi w := by
  have hv_pos : 0 < ‖v‖ := lt_of_lt_of_le R_sec_pos hv.1
  have hv0 : v ≠ 0 := norm_pos_iff.mp hv_pos
  have hdv : Real.sin (2 * deltaV) * ‖v‖ ≤ distPhi v :=
    sin_mul_norm_le_distPhi (by linarith [deltaV_pos]) (by dsimp [deltaV]; linarith [Real.pi_pos])
      hv0 hv.2.1 hv.2.2
  have hsin2 : Real.sin deltaV ≤ Real.sin (2 * deltaV) :=
    Real.strictMonoOn_sin.monotoneOn
      ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
      ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
      (by linarith [deltaV_pos])
  have hdv1 : Real.sin deltaV * ‖v‖ ≤ distPhi v := (mul_le_mul_of_nonneg_right hsin2 hv_pos.le).trans hdv
  have hdist1 : ‖w - (v + Complex.log v)‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hv_dom := V_sec_subset_V_dom hv
  have hv256 : 256 ≤ ‖v‖ := C_v_ge_256.trans (V_dom_norm_ge hv_dom)
  have hlog_norm : ‖Complex.log v‖ ≤ Real.log ‖v‖ + Real.pi := by
    rw [Complex.log]
    have hln : 0 ≤ Real.log ‖v‖ := Real.log_nonneg (by linarith)
    calc ‖(Real.log ‖v‖ : ℂ) + (Complex.arg v : ℂ) * I‖
        ≤ ‖(Real.log ‖v‖ : ℂ)‖ + ‖(Complex.arg v : ℂ) * I‖ := norm_add_le _ _
      _ = Real.log ‖v‖ + |Complex.arg v| := by
          rw [Complex.norm_real, Real.norm_of_nonneg hln, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, Complex.norm_I, mul_one]
      _ ≤ Real.log ‖v‖ + Real.pi := add_le_add_right (Complex.abs_arg_le_pi v) _
  have hwv_tri : ‖w - v‖ ≤ Real.log ‖v‖ + Real.pi + 1 := by
    have h := norm_add_le (w - (v + Complex.log v)) (Complex.log v)
    have heq : (w - (v + Complex.log v)) + Complex.log v = w - v := by ring
    rw [heq] at h; linarith
  have hnorm_big : 262144 ≤ ‖v‖ := by linarith [R_sec_ge_1e14, hv.1]
  have hlog_small : Real.log ‖v‖ + Real.pi + 1 ≤ (Real.sin deltaV / 2) * ‖v‖ := by
    have hsin_ge : (1 / 20 : ℝ) ≤ Real.sin deltaV := sin_deltaV_ge
    have hlog262 : Real.log 262144 ≤ 20 := log_262144_le
    have h1 : Real.log (‖v‖ / 262144) ≤ ‖v‖ / 262144 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log ‖v‖ = Real.log (‖v‖ / 262144) + Real.log 262144 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; ring
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  linarith [distPhi_sub_norm_le v w]

/-- Elementary half-log exponential bound: `∑_{k=0}^n ‖log v‖^k / k! ≤ 2^n * exp(π/2) * √‖v‖` for `1 ≤ ‖v‖`. -/
lemma sum_log_div_fact_le_sqrt {v : ℂ} (hv : 1 ≤ ‖v‖) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ‖Complex.log v‖ ^ k / (k.factorial : ℝ)) ≤
      (2 : ℝ) ^ n * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖ := by
  have hv_pos : 0 < ‖v‖ := lt_of_lt_of_le zero_lt_one hv
  have hln : 0 ≤ Real.log ‖v‖ := Real.log_nonneg hv
  have hlog_le : ‖Complex.log v‖ ≤ Real.log ‖v‖ + Real.pi := by
    rw [Complex.log]
    calc ‖(Real.log ‖v‖ : ℂ) + (Complex.arg v : ℂ) * I‖
        ≤ ‖(Real.log ‖v‖ : ℂ)‖ + ‖(Complex.arg v : ℂ) * I‖ := norm_add_le _ _
      _ = Real.log ‖v‖ + |Complex.arg v| := by
          rw [Complex.norm_real, Real.norm_of_nonneg hln, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, Complex.norm_I, mul_one]
      _ ≤ Real.log ‖v‖ + Real.pi := add_le_add_right (Complex.abs_arg_le_pi v) _
  have hexp_half : Real.exp (‖Complex.log v‖ / 2) ≤ Real.exp (Real.pi / 2) * Real.sqrt ‖v‖ := by
    have hsqrt : Real.exp (Real.log ‖v‖ / 2) = Real.sqrt ‖v‖ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hv_pos, div_eq_mul_inv, one_div]
    calc Real.exp (‖Complex.log v‖ / 2)
        ≤ Real.exp ((Real.log ‖v‖ + Real.pi) / 2) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (Real.log ‖v‖ / 2) * Real.exp (Real.pi / 2) := by
          rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (Real.pi / 2) * Real.sqrt ‖v‖ := by rw [hsqrt, mul_comm]
  calc ∑ k ∈ Finset.range (n + 1), ‖Complex.log v‖ ^ k / (k.factorial : ℝ)
      ≤ ∑ k ∈ Finset.range (n + 1), (2 : ℝ) ^ n * ((‖Complex.log v‖ / 2) ^ k / (k.factorial : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h2k : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hkn
        have hrew : ‖Complex.log v‖ ^ k / (k.factorial : ℝ) =
            (2 : ℝ) ^ k * ((‖Complex.log v‖ / 2) ^ k / (k.factorial : ℝ)) := by
          rw [div_pow]; field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
        rw [hrew]
        exact mul_le_mul_of_nonneg_right h2k (by positivity)
    _ = (2 : ℝ) ^ n * ∑ k ∈ Finset.range (n + 1), (‖Complex.log v‖ / 2) ^ k / (k.factorial : ℝ) := by
        rw [← Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ n * Real.exp (‖Complex.log v‖ / 2) :=
        mul_le_mul_of_nonneg_left (sum_pow_div_factorial_le_exp (by positivity) _) (by positivity)
    _ ≤ (2 : ℝ) ^ n * (Real.exp (Real.pi / 2) * Real.sqrt ‖v‖) :=
        mul_le_mul_of_nonneg_left hexp_half (by positivity)
    _ = (2 : ℝ) ^ n * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖ := by ring

/-- Smallness of `evalTrunc a N v` when `a 0 _ = 0`, `GevBound 2000 M a`, `v ∈ V_sec`, and `32000 * N ≤ ‖v‖`:
`‖evalTrunc a N v‖ ≤ M / 16`! -/
lemma norm_evalTrunc_small {M : ℝ} (hM : 0 ≤ M) {a : LogCoeff} (ha0 : ∀ k, a 0 k = 0)
    (ha : GevBound 2000 M a) {N : ℕ} {v : ℂ} (hv : v ∈ V_sec) (hbig : 32000 * (N : ℝ) ≤ ‖v‖) :
    ‖evalTrunc a N v‖ ≤ M / 16 := by
  have hv1e14 : (10 : ℝ) ^ 14 ≤ ‖v‖ := R_sec_ge_1e14.trans hv.1
  have hv1 : 1 ≤ ‖v‖ := le_trans (by norm_num) hv1e14
  have hv_pos : 0 < ‖v‖ := lt_of_lt_of_le zero_lt_one hv1
  have hsqrt_ge : (10 : ℝ) ^ 7 ≤ Real.sqrt ‖v‖ := by
    rw [Real.le_sqrt (by norm_num) hv_pos.le]
    linarith [show ((10 : ℝ) ^ 7) ^ 2 = (10 : ℝ) ^ 14 by norm_num]
  have hexp_pi2 : Real.exp (Real.pi / 2) ≤ 8 := by
    have h1 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
    have h2 : Real.exp 2 ≤ 8 := by
      have h := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_pos 1]
    exact (Real.exp_le_exp.mpr h1).trans h2
  have hterm : ∀ n ∈ Finset.range N,
      ‖evalTerm a n v‖ ≤ M * Real.exp (Real.pi / 2) * (4000 / Real.sqrt ‖v‖) * (1 / 8 : ℝ) ^ (n - 1) := by
    intro n hn
    have hnN : n < N := Finset.mem_range.mp hn
    cases n with
    | zero =>
      have h0 : evalTerm a 0 v = 0 := by
        dsimp only [evalTerm]; rw [Finset.sum_eq_zero fun k _ => by rw [ha0 k, zero_mul], zero_div]
      rw [h0, norm_zero]; positivity
    | succ m =>
      have hterm_b : ‖evalTerm a (m + 1) v‖ ≤
          M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / ‖v‖ ^ (m + 1) *
            ((2 : ℝ) ^ (m + 1) * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖) := by
        dsimp only [evalTerm]
        rw [norm_div, norm_pow]
        have hsum : ‖∑ k ∈ Finset.range (m + 1 + 1), a (m + 1) k * Complex.log v ^ k‖ ≤
            M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) *
              ((2 : ℝ) ^ (m + 1) * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖) := by
          calc ‖∑ k ∈ Finset.range (m + 1 + 1), a (m + 1) k * Complex.log v ^ k‖
              ≤ ∑ k ∈ Finset.range (m + 1 + 1), ‖a (m + 1) k * Complex.log v ^ k‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.range (m + 1 + 1),
                  (M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                    (‖Complex.log v‖ ^ k / (k.factorial : ℝ)) := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hkm : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
                rw [norm_mul, norm_pow]
                have hb := ha.2 (m + 1) k hkm
                have hsq1 : (1 : ℝ) ≤ (((m + 1 : ℕ) : ℝ) + 1) ^ 2 := by
                  have h0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
                  nlinarith
                have hb' : ‖a (m + 1) k‖ ≤
                    M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ) := by
                  refine hb.trans ?_
                  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
                    (by nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity])
                calc ‖a (m + 1) k‖ * ‖Complex.log v‖ ^ k
                    ≤ (M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / (k.factorial : ℝ)) *
                        ‖Complex.log v‖ ^ k := mul_le_mul_of_nonneg_right hb' (by positivity)
                  _ = (M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                        (‖Complex.log v‖ ^ k / (k.factorial : ℝ)) := by ring
            _ = (M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                  ∑ k ∈ Finset.range (m + 1 + 1), ‖Complex.log v‖ ^ k / (k.factorial : ℝ) := by
                rw [← Finset.mul_sum]
            _ ≤ (M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                  ((2 : ℝ) ^ (m + 1) * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖) :=
                mul_le_mul_of_nonneg_left (sum_log_div_fact_le_sqrt hv1 (m + 1)) (by positivity)
        calc ‖∑ k ∈ Finset.range (m + 1 + 1), a (m + 1) k * Complex.log v ^ k‖ / ‖v‖ ^ (m + 1)
            ≤ (M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) *
                ((2 : ℝ) ^ (m + 1) * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖)) / ‖v‖ ^ (m + 1) :=
              div_le_div_of_nonneg_right hsum (by positivity)
          _ = M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / ‖v‖ ^ (m + 1) *
                ((2 : ℝ) ^ (m + 1) * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖) := by ring
      -- Bound `(4000)^{m+1} * (m+1)! / ‖v‖^{m+1} ≤ (4000 / ‖v‖) * (1/8)^m`
      have hfac_m : ((m + 1).factorial : ℝ) ≤ (N : ℝ) ^ m := by
        have hnat : ∀ q : ℕ, q + 1 < N → (q + 1).factorial ≤ N ^ q := by
          intro q
          induction q with
          | zero => intro _; simp
          | succ p ihp =>
            intro hlt
            rw [Nat.factorial_succ, pow_succ']
            exact Nat.mul_le_mul (by omega) (ihp (by omega))
        exact_mod_cast hnat m hnN
      have hratio : (4000 : ℝ) * (N : ℝ) / ‖v‖ ≤ 1 / 8 := by
        rw [div_le_iff₀ hv_pos]; linarith
      have hpow_b : (4000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / ‖v‖ ^ (m + 1) ≤
          (4000 / ‖v‖) * (1 / 8 : ℝ) ^ m := by
        calc (4000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / ‖v‖ ^ (m + 1)
            ≤ (4000 : ℝ) ^ (m + 1) * (N : ℝ) ^ m / ‖v‖ ^ (m + 1) := by gcongr
          _ = (4000 / ‖v‖) * ((4000 : ℝ) * (N : ℝ) / ‖v‖) ^ m := by
              rw [pow_succ' (4000 : ℝ), pow_succ' ‖v‖, div_pow, mul_pow]; ring
          _ ≤ (4000 / ‖v‖) * (1 / 8 : ℝ) ^ m :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio m) (by positivity)
      have hsqrt_div : Real.sqrt ‖v‖ / ‖v‖ = 1 / Real.sqrt ‖v‖ := by
        have hs_pos : 0 < Real.sqrt ‖v‖ := Real.sqrt_pos.mpr hv_pos
        rw [div_eq_div_iff hv_pos.ne' hs_pos.ne', one_mul, Real.mul_self_sqrt hv_pos.le]
      rw [Nat.add_sub_cancel]
      calc ‖evalTerm a (m + 1) v‖
          ≤ M * (2000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / ‖v‖ ^ (m + 1) *
              ((2 : ℝ) ^ (m + 1) * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖) := hterm_b
        _ = M * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖ *
              ((4000 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) / ‖v‖ ^ (m + 1)) := by
            rw [show (4000 : ℝ) = 2000 * 2 by norm_num, mul_pow]; ring
        _ ≤ M * Real.exp (Real.pi / 2) * Real.sqrt ‖v‖ * ((4000 / ‖v‖) * (1 / 8 : ℝ) ^ m) :=
            mul_le_mul_of_nonneg_left hpow_b (by positivity)
        _ = M * Real.exp (Real.pi / 2) * (4000 * (Real.sqrt ‖v‖ / ‖v‖)) * (1 / 8 : ℝ) ^ m := by ring
        _ = M * Real.exp (Real.pi / 2) * (4000 / Real.sqrt ‖v‖) * (1 / 8 : ℝ) ^ m := by
            rw [hsqrt_div]; ring
  have hgeom : ∑ n ∈ Finset.range N, (1 / 8 : ℝ) ^ (n - 1) ≤ 3 := by
    cases N with
    | zero => simp
    | succ M' =>
      rw [Finset.sum_range_succ']
      simp only [Nat.zero_sub, pow_zero, Nat.add_sub_cancel]
      rw [geom_sum_eq (by norm_num : (1 / 8 : ℝ) ≠ 1)]
      have hnn : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ M' := by positivity
      have hden : (1 / 8 : ℝ) - 1 = -(7 / 8) := by norm_num
      rw [hden]; linarith
  calc ‖evalTrunc a N v‖
      ≤ ∑ n ∈ Finset.range N, ‖evalTerm a n v‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
          M * Real.exp (Real.pi / 2) * (4000 / Real.sqrt ‖v‖) * (1 / 8 : ℝ) ^ (n - 1) :=
        Finset.sum_le_sum hterm
    _ = M * Real.exp (Real.pi / 2) * (4000 / Real.sqrt ‖v‖) *
          ∑ n ∈ Finset.range N, (1 / 8 : ℝ) ^ (n - 1) := by rw [← Finset.mul_sum]
    _ ≤ M * Real.exp (Real.pi / 2) * (4000 / Real.sqrt ‖v‖) * 3 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ M * 8 * (4000 / (10 : ℝ) ^ 7) * 3 := by
        have hdiv : 4000 / Real.sqrt ‖v‖ ≤ 4000 / (10 : ℝ) ^ 7 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt_ge
        gcongr
    _ ≤ M / 16 := by linarith

/-- **Finite-Degree Power Truncation Residual Lemma**:
If `u 0 _ = 0`, `GevBound 2000 M u` with `0 ≤ M` and `16 * M ≤ 1/6`, `v ∈ V_sec`, `32000 * N ≤ ‖v‖`,
then for EVERY `j : ℕ`,
`‖(evalTrunc u N v) ^ j - evalTrunc (powCoeff u j) N v‖ ≤ (1 / 4)^j * exp π * ‖v‖ * 2000^N * N! / ‖v‖^N`! -/
theorem norm_pow_sub_evalTrunc_powCoeff {M : ℝ} (hM : 0 ≤ M) (hM6 : 16 * M ≤ 1 / 6)
    {u : LogCoeff} (hu0 : ∀ k, u 0 k = 0) (hu : GevBound 2000 M u)
    {N : ℕ} (hN : 1 ≤ N) {v : ℂ} (hv : v ∈ V_sec) (hbig : 32000 * (N : ℝ) ≤ ‖v‖) :
    ∀ j : ℕ, ‖evalTrunc u N v ^ j - evalTrunc (powCoeff u j) N v‖ ≤
      (1 / 4 : ℝ) ^ j * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
  have hv1 : 1 ≤ ‖v‖ := le_trans (by norm_num) (R_sec_ge_1e14.trans hv.1)
  have hv_pos : 0 < ‖v‖ := lt_of_lt_of_le zero_lt_one hv1
  have hu_small : ‖evalTrunc u N v‖ ≤ 1 / 8 :=
    (norm_evalTrunc_small hM hu0 hu hv hbig).trans (by linarith)
  -- Helper for tail of `mulCoeff a b` over degrees `N ≤ n ≤ 2N - 2`!
  have hmul_tail : ∀ (a b : LogCoeff) (Ma Mb : ℝ), 0 ≤ Ma → 0 ≤ Mb →
      GevBound 2000 Ma a → GevBound 2000 Mb b →
      ‖evalTrunc a N v * evalTrunc b N v - evalTrunc (mulCoeff a b) N v‖ ≤
        2 * (16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
    intro a b Ma Mb hMa hMb ha hb
    let aT : LogCoeff := fun n k => if n < N then a n k else 0
    let bT : LogCoeff := fun n k => if n < N then b n k else 0
    have haT_gev : GevBound 2000 Ma aT := by
      refine ⟨fun n k hnk => ?_, fun n k hkn => ?_⟩
      · dsimp only [aT]; split_ifs; exact ha.1 n k hnk; rfl
      · dsimp only [aT]; split_ifs; exact ha.2 n k hkn; simp; positivity
    have hbT_gev : GevBound 2000 Mb bT := by
      refine ⟨fun n k hnk => ?_, fun n k hkn => ?_⟩
      · dsimp only [bT]; split_ifs; exact hb.1 n k hnk; rfl
      · dsimp only [bT]; split_ifs; exact hb.2 n k hkn; simp; positivity
    have hmul_gev := gevBound_mul (by norm_num : (0 : ℝ) ≤ 2000) hMa hMb haT_gev hbT_gev
    -- Exact identity: `evalTrunc a N v * evalTrunc b N v = evalTrunc (mulCoeff aT bT) (2 * N) v`!
    have hprod_eq : evalTrunc a N v * evalTrunc b N v = evalTrunc (mulCoeff aT bT) (2 * N) v := by
      have ha_eq : evalTrunc a N v = evalTrunc aT (2 * N) v := by
        dsimp only [evalTrunc]
        rw [← Finset.sum_subset (Finset.range_mono (by omega : N ≤ 2 * N))]
        · refine Finset.sum_congr rfl fun n hn => ?_
          dsimp only [evalTerm, aT]
          have hnN : n < N := Finset.mem_range.mp hn
          simp only [hnN, ↓reduceIte]
        · intro n _ hn
          have hnot : ¬ n < N := by simpa [Finset.mem_range] using hn
          dsimp only [evalTerm, aT]
          simp [hnot]
      have hb_eq : evalTrunc b N v = evalTrunc bT (2 * N) v := by
        dsimp only [evalTrunc]
        rw [← Finset.sum_subset (Finset.range_mono (by omega : N ≤ 2 * N))]
        · refine Finset.sum_congr rfl fun n hn => ?_
          dsimp only [evalTerm, bT]
          have hnN : n < N := Finset.mem_range.mp hn
          simp only [hnN, ↓reduceIte]
        · intro n _ hn
          have hnot : ¬ n < N := by simpa [Finset.mem_range] using hn
          dsimp only [evalTerm, bT]
          simp [hnot]
      dsimp only [evalTrunc]
      have h1 : ∑ p ∈ Finset.range (2 * N), evalTerm (mulCoeff aT bT) p v =
          ∑ p ∈ Finset.range (2 * N), ∑ n ∈ Finset.range (p + 1), evalTerm aT n v * evalTerm bT (p - n) v :=
        Finset.sum_congr rfl fun p _ => evalTerm_mulCoeff haT_gev.1 hbT_gev.1 p v
      rw [h1]
      -- Swap sums via `n < N` and `m < N` (for `n ≥ N` or `m ≥ N`, `evalTerm aT n v * evalTerm bT m v = 0`)!
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      have hbij : (∑ x ∈ (Finset.range (2 * N)).sigma (fun p => Finset.range (p + 1)),
          evalTerm aT x.2 v * evalTerm bT (x.1 - x.2) v) =
          ∑ x ∈ ((Finset.range (2 * N)).sigma (fun p => Finset.range (p + 1))).filter
            (fun x => x.2 < N ∧ x.1 - x.2 < N),
          evalTerm aT x.2 v * evalTerm bT (x.1 - x.2) v := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun x : Σ _ : ℕ, ℕ => x.2 < N ∧ x.1 - x.2 < N) _)]
        intro x hx hnot
        simp only [Finset.mem_filter, not_and, not_lt] at hnot
        by_cases h1' : x.2 < N
        · have h2' : N ≤ x.1 - x.2 := hnot hx h1'
          have h0 : evalTerm bT (x.1 - x.2) v = 0 := by
            dsimp only [evalTerm, bT]; simp [show ¬ (x.1 - x.2 < N) by omega]
          rw [h0, mul_zero]
        · have h0 : evalTerm aT x.2 v = 0 := by
            dsimp only [evalTerm, aT]; simp [h1']
          rw [h0, zero_mul]
      rw [hbij]
      refine (Finset.sum_bij (fun x _ => (⟨x.2, x.1 - x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_).symm
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hx ⊢
        exact hx.2
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hx₁ hx₂
        have h1' : x₁.2 = x₂.2 := congr_arg Sigma.fst heq
        have h2' : x₁.1 - x₁.2 = x₂.1 - x₂.2 := by simpa using congr_arg Sigma.snd heq
        exact Sigma.ext (by omega) (heq_of_eq h1')
      · intro y hy
        simp only [Finset.mem_sigma, Finset.mem_range] at hy
        refine ⟨⟨y.1 + y.2, y.1⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range]; omega
        · ext <;> simp
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hx
        have h1' : evalTerm aT x.2 v = evalTerm a x.2 v := by
          dsimp only [evalTerm]; congr 1
          refine Finset.sum_congr rfl fun k _ => by simp [aT, hx.2.1]
        have h2' : evalTerm bT (x.1 - x.2) v = evalTerm b (x.1 - x.2) v := by
          dsimp only [evalTerm]; congr 1
          refine Finset.sum_congr rfl fun k _ => by simp [bT, hx.2.2]
        rw [h1', h2']
    -- On degrees `< N`, `mulCoeff aT bT = mulCoeff a b`!
    have hlow_eq : evalTrunc (mulCoeff aT bT) N v = evalTrunc (mulCoeff a b) N v := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpN : p < N := Finset.mem_range.mp hp
      dsimp only [evalTerm, mulCoeff]
      congr 1
      refine Finset.sum_congr rfl fun K _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun k _ => ?_
      have hnp : n ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      dsimp only [aT, bT]
      simp only [show n < N by omega, show p - n < N by omega, ↓reduceIte]
    rw [hprod_eq, ← hlow_eq]
    have hsplit : evalTrunc (mulCoeff aT bT) (2 * N) v - evalTrunc (mulCoeff aT bT) N v =
        ∑ n ∈ Finset.Ico N (2 * N), evalTerm (mulCoeff aT bT) n v := by
      dsimp only [evalTrunc]
      have hU : Finset.range (2 * N) = Finset.range N ∪ Finset.Ico N (2 * N) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      rw [hU, Finset.sum_union (by simp [Finset.disjoint_left]; omega)]; ring
    rw [hsplit]
    -- Bound each term `n ∈ [N, 2N)` using `2000^n n! / ‖v‖^n ≤ (1/8)^{n-N} * 2000^N N! / ‖v‖^N`!
    have hterm_tail : ∀ n ∈ Finset.Ico N (2 * N),
        ‖evalTerm (mulCoeff aT bT) n v‖ ≤
          (16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N *
            (1 / 8 : ℝ) ^ (n - N) := by
      intro n hn
      have hn_lo : N ≤ n := (Finset.mem_Ico.mp hn).1
      have hn_hi : n < 2 * N := (Finset.mem_Ico.mp hn).2
      have hbase := norm_evalTerm_le (C := 16 * Ma * Mb) (A := 2000) (by positivity) (by norm_num)
        (fun k hkn => (hmul_gev.2 n k hkn).trans (div_le_div_of_nonneg_left (by positivity)
          (by positivity) (by
            have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            have hsq : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith
            nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))) hv1
      have hfac_ratio : (n.factorial : ℝ) ≤ (2 * (N : ℝ)) ^ (n - N) * (N.factorial : ℝ) := by
        have hnat : ∀ d : ℕ, N + d < 2 * N → (N + d).factorial ≤ (2 * N) ^ d * N.factorial := by
          intro d
          induction d with
          | zero => intro _; simp
          | succ d ihd =>
            intro hlt
            rw [← Nat.add_assoc, Nat.factorial_succ, pow_succ', mul_assoc]
            exact Nat.mul_le_mul (by omega) (ihd (by omega))
        have h := hnat (n - N) (by omega)
        rw [Nat.add_sub_of_le hn_lo] at h
        exact_mod_cast h
      have hpow_step : (2000 : ℝ) ^ n * (n.factorial : ℝ) / ‖v‖ ^ n ≤
          ((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) * (1 / 8 : ℝ) ^ (n - N) := by
        have h1 : (2000 : ℝ) ^ n = (2000 : ℝ) ^ N * (2000 : ℝ) ^ (n - N) := by
          rw [← pow_add, Nat.add_sub_of_le hn_lo]
        have h2 : ‖v‖ ^ n = ‖v‖ ^ N * ‖v‖ ^ (n - N) := by
          rw [← pow_add, Nat.add_sub_of_le hn_lo]
        have hr : (2000 : ℝ) * (2 * (N : ℝ)) / ‖v‖ ≤ 1 / 8 := by
          rw [div_le_iff₀ hv_pos]; linarith
        calc (2000 : ℝ) ^ n * (n.factorial : ℝ) / ‖v‖ ^ n
            ≤ (2000 : ℝ) ^ n * ((2 * (N : ℝ)) ^ (n - N) * (N.factorial : ℝ)) / ‖v‖ ^ n := by gcongr
          _ = ((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) *
                ((2000 : ℝ) * (2 * (N : ℝ)) / ‖v‖) ^ (n - N) := by
              rw [h1, h2, div_pow, mul_pow, mul_pow]; ring
          _ ≤ ((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) * (1 / 8 : ℝ) ^ (n - N) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr (n - N)) (by positivity)
      calc ‖evalTerm (mulCoeff aT bT) n v‖
          ≤ (16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ * ((2000 : ℝ) ^ n * (n.factorial : ℝ) / ‖v‖ ^ n) :=
            hbase.trans (le_of_eq (by ring))
        _ ≤ (16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ *
              (((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) * (1 / 8 : ℝ) ^ (n - N)) :=
            mul_le_mul_of_nonneg_left hpow_step (by positivity)
        _ = (16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N *
              (1 / 8 : ℝ) ^ (n - N) := by ring
    have hgeom : ∑ n ∈ Finset.Ico N (2 * N), (1 / 8 : ℝ) ^ (n - N) ≤ 2 := by
      have hbij : ∑ n ∈ Finset.Ico N (2 * N), (1 / 8 : ℝ) ^ (n - N) =
          ∑ d ∈ Finset.range N, (1 / 8 : ℝ) ^ d := by
        refine Finset.sum_bij (fun n _ => n - N) ?_ ?_ ?_ ?_
        · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
        · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
        · intro d hd; simp only [Finset.mem_range] at hd
          exact ⟨N + d, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel_left N d⟩
        · intro _ _; rfl
      rw [hbij, geom_sum_eq (by norm_num : (1 / 8 : ℝ) ≠ 1)]
      have hnn : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ N := by positivity
      have hden : (1 / 8 : ℝ) - 1 = -(7 / 8) := by norm_num
      rw [hden]; linarith
    calc ‖∑ n ∈ Finset.Ico N (2 * N), evalTerm (mulCoeff aT bT) n v‖
        ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖evalTerm (mulCoeff aT bT) n v‖ := norm_sum_le _ _
      _ ≤ ((16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) *
            ∑ n ∈ Finset.Ico N (2 * N), (1 / 8 : ℝ) ^ (n - N) := by
          rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm_tail
      _ ≤ ((16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) * 2 :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 2 * (16 * Ma * Mb) * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
  -- Now prove the claim by induction on `j`!
  intro j
  induction j with
  | zero =>
    have hev1 : evalTrunc (powCoeff u 0) N v = 1 := by
      dsimp only [evalTrunc, powCoeff]
      rw [Finset.sum_eq_single 0]
      · simp [evalTerm, constCoeff]
      · intro n _ hn0; simp [evalTerm, constCoeff, hn0]
      · intro h0; exact absurd (Finset.mem_range.mpr hN) h0
    rw [pow_zero, hev1, sub_self, norm_zero]
    positivity
  | succ j ih =>
    cases j with
    | zero =>
      have h1 : ∀ n k, powCoeff u 1 n k = u n k := by
        intro n k
        dsimp only [powCoeff, mulCoeff, constCoeff]
        rw [Finset.sum_eq_single 0]
        · rw [Finset.sum_eq_single 0]
          · simp
          · intro i _ hi; simp [hi]
          · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
        · intro r _ hr; refine Finset.sum_eq_zero fun i _ => by simp [hr]
        · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
      have hev_eq : evalTrunc (powCoeff u 1) N v = evalTrunc u N v := by
        dsimp only [evalTrunc, evalTerm]
        refine Finset.sum_congr rfl fun n _ => ?_
        congr 1; refine Finset.sum_congr rfl fun k _ => by rw [h1 n k]
      rw [pow_one, hev_eq, sub_self, norm_zero]; positivity
    | succ m =>
      have hsplit' : evalTrunc u N v ^ (m + 2) - evalTrunc (powCoeff u (m + 2)) N v =
          (evalTrunc u N v ^ (m + 1) - evalTrunc (powCoeff u (m + 1)) N v) * evalTrunc u N v +
          (evalTrunc (powCoeff u (m + 1)) N v * evalTrunc u N v -
            evalTrunc (mulCoeff (powCoeff u (m + 1)) u) N v) := by
        have : powCoeff u (m + 2) = mulCoeff (powCoeff u (m + 1)) u := rfl
        rw [this, pow_succ]; ring
      rw [hsplit']
      have htail := hmul_tail (powCoeff u (m + 1)) u ((16 * M) ^ (m + 1) / 16) M
        (by positivity) hM (gevBound_powCoeff (by norm_num) hM hu (m + 1) (Nat.succ_pos m)) hu
      have hcoef_tail : 2 * (16 * ((16 * M) ^ (m + 1) / 16) * M) ≤ (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2) := by
        have h1 : 2 * (16 * ((16 * M) ^ (m + 1) / 16) * M) = (1 / 8 : ℝ) * (16 * M) ^ (m + 2) := by
          rw [pow_succ]; ring
        rw [h1]
        have h2 : (16 * M) ^ (m + 2) ≤ (1 / 4 : ℝ) ^ (m + 2) :=
          pow_le_pow_left₀ (by positivity) (by linarith) (m + 2)
        have hnn : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (m + 2) := by positivity
        linarith
      let E : ℝ := Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N
      have hE_nn : 0 ≤ E := by positivity
      have hb1 : ‖(evalTrunc u N v ^ (m + 1) - evalTrunc (powCoeff u (m + 1)) N v) * evalTrunc u N v‖ ≤
          (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2) * E := by
        rw [norm_mul]
        calc ‖evalTrunc u N v ^ (m + 1) - evalTrunc (powCoeff u (m + 1)) N v‖ * ‖evalTrunc u N v‖
            ≤ ((1 / 4 : ℝ) ^ (m + 1) * E) * (1 / 8 : ℝ) :=
              mul_le_mul (ih.trans (le_of_eq (by dsimp [E]; ring))) hu_small (norm_nonneg _) (by positivity)
          _ = (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2) * E := by rw [pow_succ]; ring
      have hb2 : ‖evalTrunc (powCoeff u (m + 1)) N v * evalTrunc u N v -
            evalTrunc (mulCoeff (powCoeff u (m + 1)) u) N v‖ ≤
          (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2) * E := by
        calc _ ≤ 2 * (16 * ((16 * M) ^ (m + 1) / 16) * M) * E := htail.trans (le_of_eq (by dsimp [E]; ring))
          _ ≤ ((1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2)) * E := mul_le_mul_of_nonneg_right hcoef_tail hE_nn
          _ = (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2) * E := by ring
      calc ‖(evalTrunc u N v ^ (m + 1) - evalTrunc (powCoeff u (m + 1)) N v) * evalTrunc u N v +
            (evalTrunc (powCoeff u (m + 1)) N v * evalTrunc u N v -
              evalTrunc (mulCoeff (powCoeff u (m + 1)) u) N v)‖
          ≤ _ + _ := norm_add_le _ _
        _ ≤ (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2) * E + (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (m + 2) * E :=
            add_le_add hb1 hb2
        _ = (1 / 4 : ℝ) ^ (m + 2) * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
            dsimp only [E]; ring

/-- Finite Taylor remainder for `log (1 + u)` on `‖u‖ ≤ 1 / 4`. -/
lemma norm_clog_one_add_sub_sum_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) {N : ℕ} (hN : 1 ≤ N) :
    ‖Complex.log (1 + u) -
        ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * u ^ j‖ ≤ 2 * ‖u‖ ^ N := by
  let g : ℝ → ℂ := fun t => Complex.log (1 + (t : ℂ) * u) -
    ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * ((t : ℂ) * u) ^ j
  have h1tu_re : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ (1 + (t : ℂ) * u).re := by
    intro t ht
    have habs : ‖(t : ℂ) * u‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]; nlinarith [ht.2, norm_nonneg u]
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans habs)).1
    simp only [Complex.add_re, Complex.one_re]; linarith
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt g (u * (-((t : ℂ) * u)) ^ (N - 1) / (1 + (t : ℂ) * u)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hlin : HasDerivAt (fun τ : ℝ => 1 + (τ : ℂ) * u) u t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const u).const_add 1
    have hlog := (Complex.hasDerivAt_log (Or.inl (by linarith [h1tu_re t ht]))).comp t hlin
    have hsum : HasDerivAt
        (fun τ : ℝ => ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * ((τ : ℂ) * u) ^ j)
        (∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * ((j : ℂ) * ((t : ℂ) * u) ^ (j - 1) * u)) t := by
      refine HasDerivAt.fun_sum fun j hj => ?_
      have htu : HasDerivAt (fun τ : ℝ => (τ : ℂ) * u) u t := by
        simpa using (hasDerivAt_id t).ofReal_comp.mul_const u
      exact (htu.fun_pow j).const_mul _
    refine (hlog.fun_sub hsum).congr_deriv ?_
    have hsum_eq : ∑ j ∈ Finset.Ico 1 N,
        ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * ((j : ℂ) * ((t : ℂ) * u) ^ (j - 1) * u) =
        u * ∑ k ∈ Finset.range (N - 1), (-((t : ℂ) * u)) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
      · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        exact ⟨k + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel k 1⟩
      · intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
        have hjne : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hpow : (-((t : ℂ) * u)) ^ (j - 1) = (-1 : ℂ) ^ (j - 1) * ((t : ℂ) * u) ^ (j - 1) := by
          rw [← mul_pow]; congr 1; ring
        rw [hpow]; field_simp [hjne]
    rw [hsum_eq]
    have hgeom : (1 + (t : ℂ) * u) * ∑ k ∈ Finset.range (N - 1), (-((t : ℂ) * u)) ^ k =
        1 - (-((t : ℂ) * u)) ^ (N - 1) := by
      have h1 := mul_geom_sum (-((t : ℂ) * u)) (N - 1)
      have h2 : (-((t : ℂ) * u) - 1) = -(1 + (t : ℂ) * u) := by ring
      rw [h2] at h1
      linear_combination -h1
    have hden_ne : 1 + (t : ℂ) * u ≠ 0 := by
      intro h0; have := congr_arg Complex.re h0; simp only [Complex.zero_re] at this
      linarith [h1tu_re t ht]
    field_simp [hden_ne]
    linear_combination -u * hgeom
  have hcont : ContinuousOn (fun t : ℝ => u * (-((t : ℂ) * u)) ^ (N - 1) / (1 + (t : ℂ) * u))
      (Set.uIcc (0 : ℝ) 1) := by
    refine (continuous_const.mul ((Complex.continuous_ofReal.mul continuous_const).neg.pow (N - 1))).continuousOn.div
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    intro h0; have := congr_arg Complex.re h0; simp only [Complex.zero_re] at this
    linarith [h1tu_re t ht]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hg0 : g 0 = 0 := by
    dsimp only [g]
    simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.log_one, zero_sub]
    rw [neg_eq_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    rw [zero_pow (by omega), mul_zero]
  have hg1 : g 1 = Complex.log (1 + u) -
      ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * u ^ j := by
    dsimp only [g]; simp
  rw [hg1, hg0, sub_zero] at hftc
  rw [← hftc]
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖u * (-((t : ℂ) * u)) ^ (N - 1) / (1 + (t : ℂ) * u)‖ ≤ 2 * ‖u‖ ^ N := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hden : 1 / 2 ≤ ‖1 + (t : ℂ) * u‖ :=
      (h1tu_re t ⟨ht.1.le, ht.2⟩).trans (Complex.re_le_norm _)
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
    have htpow : (t * ‖u‖) ^ (N - 1) ≤ ‖u‖ ^ (N - 1) :=
      pow_le_pow_left₀ (mul_nonneg ht.1.le (norm_nonneg u)) (by nlinarith [ht.2, norm_nonneg u]) (N - 1)
    have hpowN : ‖u‖ * ‖u‖ ^ (N - 1) = ‖u‖ ^ N := by
      rw [← pow_succ', Nat.sub_add_cancel hN]
    calc ‖u‖ * (t * ‖u‖) ^ (N - 1) / ‖1 + (t : ℂ) * u‖
        ≤ ‖u‖ * ‖u‖ ^ (N - 1) / (1 / 2) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left htpow (norm_nonneg u)) (by norm_num) hden
      _ = 2 * ‖u‖ ^ N := by rw [hpowN]; ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- Exact finite Taylor remainder for `(1 + u)^{-m}` on `‖u‖ ≤ 1 / 4` by induction on `M`! -/
lemma norm_inv_one_add_pow_sub_sum_le : ∀ (M m : ℕ), 1 ≤ m → ∀ {u : ℂ}, ‖u‖ ≤ 1 / 4 →
    ‖((1 + u)⁻¹ : ℂ) ^ m -
        ∑ j ∈ Finset.range M, ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * u ^ j‖ ≤
      (((m + M - 1).choose M : ℕ) : ℝ) * (2 : ℝ) ^ (m + M) * ‖u‖ ^ M := by
  intro M
  induction M with
  | zero =>
    intro m hm u hu
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.add_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, pow_zero, mul_one]
    have hden : 1 / 2 ≤ ‖1 + u‖ := by
      have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hu)).1
      exact (show (1 / 2 : ℝ) ≤ (1 + u).re by simp only [Complex.add_re, Complex.one_re]; linarith).trans
        (Complex.re_le_norm _)
    rw [norm_pow, norm_inv]
    have hinv : ‖1 + u‖⁻¹ ≤ 2 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
      linarith
    exact pow_le_pow_left₀ (by positivity) hinv m
  | succ M ih =>
    intro m hm u hu
    let g : ℝ → ℂ := fun t => ((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ m -
      ∑ j ∈ Finset.range (M + 1), ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * ((t : ℂ) * u) ^ j
    have h1tu_re : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ (1 + (t : ℂ) * u).re := by
      intro t ht
      have habs : ‖(t : ℂ) * u‖ ≤ 1 / 4 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]; nlinarith [ht.2, norm_nonneg u]
      have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans habs)).1
      simp only [Complex.add_re, Complex.one_re]; linarith
    have h1tu_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 + (t : ℂ) * u ≠ 0 := by
      intro t ht h0; have := congr_arg Complex.re h0; simp only [Complex.zero_re] at this
      linarith [h1tu_re t ht]
    let gp : ℝ → ℂ := fun t => -(m : ℂ) * u *
      (((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ (m + 1) -
        ∑ k ∈ Finset.range M, ((-1 : ℂ) ^ k * ((((m + 1) + k - 1).choose k : ℕ) : ℂ)) * ((t : ℂ) * u) ^ k)
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (gp t) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hne := h1tu_ne t ht
      have hlin : HasDerivAt (fun τ : ℝ => 1 + (τ : ℂ) * u) u t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const u).const_add 1
      have hinv_d : HasDerivAt (fun τ : ℝ => (1 + (τ : ℂ) * u)⁻¹)
          (-u / (1 + (t : ℂ) * u) ^ 2) t := hlin.fun_inv hne
      have hpow_d : HasDerivAt (fun τ : ℝ => ((1 + (τ : ℂ) * u)⁻¹ : ℂ) ^ m)
          ((m : ℂ) * ((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ (m - 1) * (-u / (1 + (t : ℂ) * u) ^ 2)) t :=
        hinv_d.fun_pow m
      have hsum_d : HasDerivAt
          (fun τ : ℝ => ∑ j ∈ Finset.range (M + 1),
            ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * ((τ : ℂ) * u) ^ j)
          (∑ j ∈ Finset.range (M + 1),
            ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * ((j : ℂ) * ((t : ℂ) * u) ^ (j - 1) * u)) t := by
        refine HasDerivAt.fun_sum fun j _ => ?_
        have htu : HasDerivAt (fun τ : ℝ => (τ : ℂ) * u) u t := by
          simpa using (hasDerivAt_id t).ofReal_comp.mul_const u
        exact (htu.fun_pow j).const_mul _
      refine (hpow_d.fun_sub hsum_d).congr_deriv ?_
      have hterm1 : (m : ℂ) * ((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ (m - 1) * (-u / (1 + (t : ℂ) * u) ^ 2) =
          -(m : ℂ) * u * ((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ (m + 1) := by
        have hm2 : ((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ (m + 1) =
            ((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ (m - 1) * ((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ 2 := by
          rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
        rw [hm2, inv_pow]; field_simp [hne]
      have hterm2 : ∑ j ∈ Finset.range (M + 1),
            ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * ((j : ℂ) * ((t : ℂ) * u) ^ (j - 1) * u) =
          -(m : ℂ) * u * ∑ k ∈ Finset.range M,
            ((-1 : ℂ) ^ k * ((((m + 1) + k - 1).choose k : ℕ) : ℂ)) * ((t : ℂ) * u) ^ k := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hch : (m + k).choose (k + 1) * (k + 1) = (m + k).choose k * m := by
          have h := Nat.choose_succ_right_eq (m + k) k
          rwa [show m + k - k = m by omega] at h
        have hchC : (((m + k).choose (k + 1) : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) =
            (((m + k).choose k : ℕ) : ℂ) * (m : ℂ) := by exact_mod_cast hch
        simp only [Nat.add_sub_cancel, show m + (k + 1) - 1 = m + k by omega,
          show m + 1 + k - 1 = m + k by omega, pow_succ]
        linear_combination (-1 : ℂ) ^ k * u * ((t : ℂ) * u) ^ k * (-hchC)
      dsimp only [gp]
      rw [hterm1, hterm2]; ring
    have hcont : ContinuousOn gp (Set.uIcc (0 : ℝ) 1) := by
      dsimp only [gp]
      refine continuousOn_const.mul ?_
      refine ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn.inv₀ ?_).pow (m + 1)
        |>.sub ?_
      · intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht; exact h1tu_ne t ht
      · have hsum_cont : Continuous (fun t : ℝ => ∑ k ∈ Finset.range M,
            ((-1 : ℂ) ^ k * ((((m + 1) + k - 1).choose k : ℕ) : ℂ)) * ((t : ℂ) * u) ^ k) := by
          clear hderiv h1tu_re h1tu_ne g gp ih
          induction M with
          | zero => simpa using continuous_const
          | succ K ihK =>
            simp_rw [Finset.sum_range_succ]
            exact ihK.add (continuous_const.mul ((Complex.continuous_ofReal.mul continuous_const).pow K))
        exact hsum_cont.continuousOn
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    have hg0 : g 0 = 0 := by
      dsimp only [g]
      rw [Finset.sum_range_succ']
      simp only [Complex.ofReal_zero, zero_mul, add_zero, inv_one, one_pow, pow_zero, one_mul,
        Nat.choose_zero_right, Nat.cast_one]
      have hzero : ∑ k ∈ Finset.range M,
          ((-1 : ℂ) ^ (k + 1) * (((m + (k + 1) - 1).choose (k + 1) : ℕ) : ℂ)) * (0 : ℂ) ^ (k + 1) = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [zero_pow (Nat.succ_ne_zero k), mul_zero]
      rw [hzero, zero_add, sub_self]
    have hg1 : g 1 = ((1 + u)⁻¹ : ℂ) ^ m -
        ∑ j ∈ Finset.range (M + 1), ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * u ^ j := by
      dsimp only [g]; simp
    rw [hg1, hg0, sub_zero] at hftc
    rw [← hftc]
    let K : ℝ := (m : ℝ) * (((m + M).choose M : ℕ) : ℝ) * (2 : ℝ) ^ (m + M + 1) * ‖u‖ ^ (M + 1)
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖gp t‖ ≤ K * t ^ M := by
      intro t ht
      have htu : ‖(t : ℂ) * u‖ ≤ 1 / 4 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]; nlinarith [ht.2, norm_nonneg u]
      have hih := ih (m + 1) (by omega) htu
      simp only [show m + 1 + M = m + M + 1 by omega] at hih
      dsimp only [gp]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_natCast]
      have hpow_tu : ‖(t : ℂ) * u‖ ^ M = t ^ M * ‖u‖ ^ M := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1, mul_pow]
      rw [hpow_tu] at hih
      calc (m : ℝ) * ‖u‖ *
            ‖((1 + (t : ℂ) * u)⁻¹ : ℂ) ^ (m + 1) -
              ∑ k ∈ Finset.range M, ((-1 : ℂ) ^ k * (((m + 1 + k - 1).choose k : ℕ) : ℂ)) * ((t : ℂ) * u) ^ k‖
          ≤ (m : ℝ) * ‖u‖ * ((((m + M).choose M : ℕ) : ℝ) * (2 : ℝ) ^ (m + M + 1) * (t ^ M * ‖u‖ ^ M)) :=
            mul_le_mul_of_nonneg_left hih (by positivity)
        _ = K * t ^ M := by dsimp only [K]; rw [pow_succ']; ring
    have hint_t : IntervalIntegrable (fun t : ℝ => K * t ^ M) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_pow M)).intervalIntegrable 0 1
    have hle := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall fun t ht => hbd t ⟨ht.1.le, ht.2⟩) hint_t
    have hint_val : ∫ t in (0 : ℝ)..1, K * t ^ M = K / (M + 1 : ℝ) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp [div_eq_mul_inv]
    rw [hint_val] at hle
    have hch : (m + M).choose (M + 1) * (M + 1) = (m + M).choose M * m := by
      have h := Nat.choose_succ_right_eq (m + M) M
      rwa [show m + M - M = m by omega] at h
    have hchR : (((m + M).choose (M + 1) : ℕ) : ℝ) * (M + 1 : ℝ) =
        (((m + M).choose M : ℕ) : ℝ) * (m : ℝ) := by exact_mod_cast hch
    have hKeq : K / (M + 1 : ℝ) =
        (((m + (M + 1) - 1).choose (M + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (m + (M + 1)) * ‖u‖ ^ (M + 1) := by
      have hM1ne : (M + 1 : ℝ) ≠ 0 := by positivity
      dsimp only [K]
      rw [show m + (M + 1) - 1 = m + M by omega, show m + (M + 1) = m + M + 1 by omega]
      rw [div_eq_iff hM1ne]
      linear_combination -(2 : ℝ) ^ (m + M + 1) * ‖u‖ ^ (M + 1) * hchR
    rwa [hKeq] at hle

/-- Coarse bound `(4 : ℝ) ^ (m + M) * ‖u‖ ^ M` for the Taylor remainder of `(1 + u)^{-m}`. -/
lemma norm_inv_one_add_pow_sub_sum_le_four {M m : ℕ} (hm : 1 ≤ m) {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) :
    ‖((1 + u)⁻¹ : ℂ) ^ m -
        ∑ j ∈ Finset.range M, ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * u ^ j‖ ≤
      (4 : ℝ) ^ (m + M) * ‖u‖ ^ M := by
  have h1 := norm_inv_one_add_pow_sub_sum_le M m hm hu
  have hch : (((m + M - 1).choose M : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + M) := by
    have hnat : (m + M - 1).choose M ≤ 2 ^ (m + M) :=
      (Nat.choose_le_two_pow (m + M - 1) M).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast hnat
  have h4 : (2 : ℝ) ^ (m + M) * (2 : ℝ) ^ (m + M) = (4 : ℝ) ^ (m + M) := by
    rw [← mul_pow]; norm_num
  calc _ ≤ (((m + M - 1).choose M : ℕ) : ℝ) * (2 : ℝ) ^ (m + M) * ‖u‖ ^ M := h1
    _ ≤ ((2 : ℝ) ^ (m + M) * (2 : ℝ) ^ (m + M)) * ‖u‖ ^ M := by gcongr
    _ = (4 : ℝ) ^ (m + M) * ‖u‖ ^ M := by rw [h4]

/-- Uniform `O(‖log v‖ / ‖v‖)` bound on `evalTrunc a N v` when `a 0 = 0`, `GevBound 2000 M a`,
`M ≤ 1`, and `32000 * N ≤ ‖v‖` on `V_sec`. -/
lemma norm_evalTrunc_le_const_log_div {M : ℝ} (hM : 0 ≤ M) (hM1 : M ≤ 1) {a : LogCoeff}
    (ha0 : ∀ k, a 0 k = 0) (ha : GevBound 2000 M a) {N : ℕ} {v : ℂ} (hv : v ∈ V_sec)
    (hbig : 32000 * (N : ℝ) ≤ ‖v‖) :
    ‖evalTrunc a N v‖ ≤ (20000000 * Real.exp Real.pi) * ‖Complex.log v‖ / ‖v‖ := by
  have hv_ge : (10 : ℝ) ^ 14 ≤ ‖v‖ := R_sec_ge_1e14.trans hv.1
  have hv1 : 1 ≤ ‖v‖ := by linarith
  have hv_pos : 0 < ‖v‖ := by linarith
  have hlog_ge_one : 1 ≤ ‖Complex.log v‖ := by
    have h1 : Real.exp 1 ≤ ‖v‖ := by
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      linarith
    have h2 : 1 ≤ Real.log ‖v‖ := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ‖v‖ := Real.log_le_log (Real.exp_pos 1) h1
    have h3 : (Complex.log v).re = Real.log ‖v‖ := Complex.log_re v
    exact h2.trans (by rw [← h3]; exact Complex.re_le_norm _)
  have hterm0 : evalTerm a 0 v = 0 := by
    dsimp only [evalTerm]; simp [ha0]
  have hterm1 : ‖evalTerm a 1 v‖ ≤ 4000 * ‖Complex.log v‖ / ‖v‖ := by
    dsimp only [evalTerm]
    rw [norm_div, pow_one, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 := ha.2 1 0 (by omega)
    have h1 := ha.2 1 1 (by omega)
    norm_num [Nat.factorial] at h0 h1
    have htri : ‖a 1 0 * Complex.log v ^ 0 + a 1 1 * Complex.log v ^ 1‖ ≤
        500 * M + 500 * M * ‖Complex.log v‖ := by
      calc _ ≤ ‖a 1 0 * Complex.log v ^ 0‖ + ‖a 1 1 * Complex.log v ^ 1‖ := norm_add_le _ _
        _ = ‖a 1 0‖ + ‖a 1 1‖ * ‖Complex.log v‖ := by simp
        _ ≤ 500 * M + 500 * M * ‖Complex.log v‖ := by
            gcongr <;> linarith
    calc ‖a 1 0 * Complex.log v ^ 0 + a 1 1 * Complex.log v ^ 1‖ / ‖v‖
        ≤ (500 * M + 500 * M * ‖Complex.log v‖) / ‖v‖ :=
          div_le_div_of_nonneg_right htri hv_pos.le
      _ ≤ 4000 * ‖Complex.log v‖ / ‖v‖ := by
          refine div_le_div_of_nonneg_right ?_ hv_pos.le
          nlinarith
  have hterm_ge2 : ∀ n ∈ Finset.Ico 2 N,
      ‖evalTerm a n v‖ ≤ (8000000 * Real.exp Real.pi / ‖v‖) * (1 / 16 : ℝ) ^ (n - 2) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnN : n < N := (Finset.mem_Ico.mp hn).2
    have hbase := norm_evalTerm_le (C := M) (A := 2000) hM (by norm_num)
      (fun k hkn => (ha.2 n k hkn).trans (div_le_div_of_nonneg_left (by positivity)
        (by positivity) (by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hsq : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith
          nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))) hv1
    have hstep : ∀ d : ℕ, 2 + d < N →
        (2000 : ℝ) ^ (2 + d) * ((2 + d).factorial : ℝ) / ‖v‖ ^ (2 + d) ≤
          (8000000 / ‖v‖ ^ 2) * (1 / 16 : ℝ) ^ d := by
      intro d
      induction d with
      | zero => intro _; norm_num [Nat.factorial]
      | succ d ihd =>
        intro hlt
        have hr : (2000 : ℝ) * ((2 + d + 1 : ℕ) : ℝ) / ‖v‖ ≤ 1 / 16 := by
          rw [div_le_iff₀ hv_pos]
          have hcast : ((2 + d + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 + d + 1 ≤ N by omega)
          nlinarith
        have hrew : (2000 : ℝ) ^ (2 + (d + 1)) * ((2 + (d + 1)).factorial : ℝ) / ‖v‖ ^ (2 + (d + 1)) =
            ((2000 : ℝ) ^ (2 + d) * ((2 + d).factorial : ℝ) / ‖v‖ ^ (2 + d)) *
              ((2000 : ℝ) * ((2 + d + 1 : ℕ) : ℝ) / ‖v‖) := by
          rw [show 2 + (d + 1) = (2 + d) + 1 by omega, pow_succ, pow_succ, Nat.factorial_succ]
          push_cast
          have hne : ‖v‖ ^ (2 + d) ≠ 0 := by positivity
          field_simp [hne, hv_pos.ne']
        rw [hrew, pow_succ]
        calc _ ≤ ((8000000 / ‖v‖ ^ 2) * (1 / 16 : ℝ) ^ d) * (1 / 16 : ℝ) :=
              mul_le_mul (ihd (by omega)) hr (by positivity) (by positivity)
          _ = (8000000 / ‖v‖ ^ 2) * ((1 / 16 : ℝ) ^ d * (1 / 16 : ℝ)) := by ring
    have hpow := hstep (n - 2) (by omega)
    rw [Nat.add_sub_of_le hn2] at hpow
    calc ‖evalTerm a n v‖
        ≤ M * Real.exp Real.pi * ‖v‖ * ((2000 : ℝ) ^ n * (n.factorial : ℝ) / ‖v‖ ^ n) :=
          hbase.trans (le_of_eq (by ring))
      _ ≤ 1 * Real.exp Real.pi * ‖v‖ * ((8000000 / ‖v‖ ^ 2) * (1 / 16 : ℝ) ^ (n - 2)) := by
          have h1 : M * Real.exp Real.pi * ‖v‖ ≤ 1 * Real.exp Real.pi * ‖v‖ := by
            have : 0 ≤ Real.exp Real.pi * ‖v‖ := by positivity
            nlinarith
          exact mul_le_mul h1 hpow (by positivity) (by positivity)
      _ = (8000000 * Real.exp Real.pi / ‖v‖) * (1 / 16 : ℝ) ^ (n - 2) := by
          field_simp [hv_pos.ne']
  -- Split `Finset.range N` into `0`, `1`, and `Ico 2 N`.
  rcases N with _ | N'
  · simp [evalTrunc]; positivity
  · rcases N' with _ | N''
    · simp [evalTrunc, hterm0]; positivity
    · have hsplit : evalTrunc a (N'' + 2) v =
          evalTerm a 1 v + ∑ n ∈ Finset.Ico 2 (N'' + 2), evalTerm a n v := by
        dsimp only [evalTrunc]
        have hU : Finset.range (N'' + 2) = {0, 1} ∪ Finset.Ico 2 (N'' + 2) := by
          ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_Ico]; omega
        rw [hU, Finset.sum_union (by simp [Finset.disjoint_left]),
          Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), hterm0, zero_add]
      rw [hsplit]
      have hgeom : ∑ n ∈ Finset.Ico 2 (N'' + 2), (1 / 16 : ℝ) ^ (n - 2) ≤ 2 := by
        have hbij : ∑ n ∈ Finset.Ico 2 (N'' + 2), (1 / 16 : ℝ) ^ (n - 2) =
            ∑ d ∈ Finset.range N'', (1 / 16 : ℝ) ^ d := by
          refine Finset.sum_bij (fun n _ => n - 2) ?_ ?_ ?_ ?_
          · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
          · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
          · intro d hd; simp only [Finset.mem_range] at hd
            exact ⟨d + 2, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel d 2⟩
          · intro _ _; rfl
        rw [hbij, geom_sum_eq (by norm_num : (1 / 16 : ℝ) ≠ 1)]
        have : (0 : ℝ) ≤ (1 / 16 : ℝ) ^ N'' := by positivity
        have hden : (1 / 16 : ℝ) - 1 = -(15 / 16) := by norm_num
        rw [hden]; linarith
      have htail : ‖∑ n ∈ Finset.Ico 2 (N'' + 2), evalTerm a n v‖ ≤
          16000000 * Real.exp Real.pi / ‖v‖ := by
        calc ‖∑ n ∈ Finset.Ico 2 (N'' + 2), evalTerm a n v‖
            ≤ ∑ n ∈ Finset.Ico 2 (N'' + 2), ‖evalTerm a n v‖ := norm_sum_le _ _
          _ ≤ (8000000 * Real.exp Real.pi / ‖v‖) *
                ∑ n ∈ Finset.Ico 2 (N'' + 2), (1 / 16 : ℝ) ^ (n - 2) := by
              rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm_ge2
          _ ≤ (8000000 * Real.exp Real.pi / ‖v‖) * 2 :=
              mul_le_mul_of_nonneg_left hgeom (by positivity)
          _ = 16000000 * Real.exp Real.pi / ‖v‖ := by ring
      have hexp_ge1 : (1 : ℝ) ≤ Real.exp Real.pi := Real.one_le_exp Real.pi_pos.le
      calc ‖evalTerm a 1 v + ∑ n ∈ Finset.Ico 2 (N'' + 2), evalTerm a n v‖
          ≤ ‖evalTerm a 1 v‖ + ‖∑ n ∈ Finset.Ico 2 (N'' + 2), evalTerm a n v‖ := norm_add_le _ _
        _ ≤ 4000 * ‖Complex.log v‖ / ‖v‖ + 16000000 * Real.exp Real.pi / ‖v‖ :=
            add_le_add hterm1 htail
        _ ≤ (20000000 * Real.exp Real.pi) * ‖Complex.log v‖ / ‖v‖ := by
            rw [← add_div]
            refine div_le_div_of_nonneg_right ?_ hv_pos.le
            nlinarith

/-- Generic Gevrey-1 residual for `log (1 + evalTrunc u N v) - evalTrunc (log1pCoeff u) N v`! -/
lemma norm_clog_one_add_evalTrunc_sub_le {M : ℝ} (hM : 0 ≤ M) (hM6 : 16 * M ≤ 1 / 6)
    {u : LogCoeff} (hu0 : ∀ k, u 0 k = 0) (hu : GevBound 2000 M u)
    {N : ℕ} (hN : 1 ≤ N) {v : ℂ} (hv : v ∈ V_sec) (hbig : 32000 * (N : ℝ) ≤ ‖v‖) :
    ‖Complex.log (1 + evalTrunc u N v) - evalTrunc (log1pCoeff u) N v‖ ≤
      (3 * Real.exp Real.pi) * ‖v‖ * (20000000 * Real.exp Real.pi) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
  have hv_ge : (10 : ℝ) ^ 14 ≤ ‖v‖ := R_sec_ge_1e14.trans hv.1
  have hv1 : 1 ≤ ‖v‖ := by linarith
  have hv_pos : 0 < ‖v‖ := by linarith
  have hM1 : M ≤ 1 := by linarith
  have hu_sm : ‖evalTrunc u N v‖ ≤ 1 / 4 :=
    (norm_evalTrunc_small hM hu0 hu hv hbig).trans (by linarith)
  have hu_log : ‖evalTrunc u N v‖ ≤ (20000000 * Real.exp Real.pi) * ‖Complex.log v‖ / ‖v‖ :=
    norm_evalTrunc_le_const_log_div hM hM1 hu0 hu hv hbig
  -- Rewrite `evalTrunc (log1pCoeff u) N v` as `∑ j ∈ Ico 1 N, ((-1)^{j-1}/j) * evalTrunc (powCoeff u j) N v`!
  have hlog1p_eq : evalTrunc (log1pCoeff u) N v =
      ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * evalTrunc (powCoeff u j) N v := by
    dsimp only [evalTrunc, evalTerm, log1pCoeff]
    have hterm_eq : ∀ n ∈ Finset.range N,
        (∑ K ∈ Finset.range (n + 1),
          (∑ j ∈ Finset.Ico 1 (n + 1), ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * powCoeff u j n K) *
            Complex.log v ^ K) / v ^ n =
        ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) *
          ((∑ K ∈ Finset.range (n + 1), powCoeff u j n K * Complex.log v ^ K) / v ^ n) := by
      intro n hn
      have hnN : n < N := Finset.mem_range.mp hn
      have hsub : ∀ K,
          ∑ j ∈ Finset.Ico 1 (n + 1), ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * powCoeff u j n K =
          ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * powCoeff u j n K := by
        intro K
        refine Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega)) ?_
        intro j hj hnot
        simp only [Finset.mem_Ico] at hj hnot
        have hnj : n < j := by omega
        rw [powCoeff_zero_lt hu0 j n K hnj, mul_zero]
      simp_rw [hsub, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, mul_div_assoc]
    rw [Finset.sum_congr rfl hterm_eq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [hlog1p_eq]
  -- Split into Taylor remainder + power-truncation remainder!
  have hsplit : Complex.log (1 + evalTrunc u N v) -
      ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * evalTrunc (powCoeff u j) N v =
      (Complex.log (1 + evalTrunc u N v) -
        ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * (evalTrunc u N v) ^ j) +
      ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) *
        ((evalTrunc u N v) ^ j - evalTrunc (powCoeff u j) N v) := by
    have : ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) *
          ((evalTrunc u N v) ^ j - evalTrunc (powCoeff u j) N v) =
        ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * (evalTrunc u N v) ^ j -
        ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * evalTrunc (powCoeff u j) N v := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  rw [hsplit]
  let A : ℝ := 20000000 * Real.exp Real.pi
  have hA_ge : (2000 : ℝ) ≤ A := by
    have : (1 : ℝ) ≤ Real.exp Real.pi := Real.one_le_exp Real.pi_pos.le
    dsimp [A]; nlinarith
  have hpart1 : ‖Complex.log (1 + evalTrunc u N v) -
      ∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) * (evalTrunc u N v) ^ j‖ ≤
      2 * Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
    have h1 := norm_clog_one_add_sub_sum_le hu_sm hN
    have hlogN : ‖Complex.log v‖ ^ N / (N.factorial : ℝ) ≤ Real.exp Real.pi * ‖v‖ := by
      have h := Real.pow_div_factorial_le_exp ‖Complex.log v‖ (norm_nonneg _) N
      exact h.trans (exp_norm_log_le hv1)
    have hlogN' : ‖Complex.log v‖ ^ N ≤ Real.exp Real.pi * ‖v‖ * (N.factorial : ℝ) := by
      rwa [div_le_iff₀ (by positivity)] at hlogN
    calc _ ≤ 2 * ‖evalTrunc u N v‖ ^ N := h1
      _ ≤ 2 * (A * ‖Complex.log v‖ / ‖v‖) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu_log N) (by norm_num)
      _ = 2 * A ^ N * ‖Complex.log v‖ ^ N / ‖v‖ ^ N := by rw [div_pow, mul_pow]; ring
      _ ≤ 2 * A ^ N * (Real.exp Real.pi * ‖v‖ * (N.factorial : ℝ)) / ‖v‖ ^ N := by gcongr
      _ = 2 * Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
  have hpart2 : ‖∑ j ∈ Finset.Ico 1 N, ((-1 : ℂ) ^ (j - 1) / (j : ℂ)) *
        ((evalTrunc u N v) ^ j - evalTrunc (powCoeff u j) N v)‖ ≤
      Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
    have hterm : ∀ j ∈ Finset.Ico 1 N,
        ‖((-1 : ℂ) ^ (j - 1) / (j : ℂ)) *
          ((evalTrunc u N v) ^ j - evalTrunc (powCoeff u j) N v)‖ ≤
        (1 / 4 : ℝ) ^ j * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
      rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
      have hjinv : 1 / (j : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (show 0 < j by omega))]; exact_mod_cast hj1
      have hp := norm_pow_sub_evalTrunc_powCoeff hM hM6 hu0 hu hN hv hbig j
      calc (1 / (j : ℝ)) * ‖(evalTrunc u N v) ^ j - evalTrunc (powCoeff u j) N v‖
          ≤ 1 * ((1 / 4 : ℝ) ^ j * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
            mul_le_mul hjinv hp (norm_nonneg _) zero_le_one
        _ = (1 / 4 : ℝ) ^ j * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
    have hgeom : ∑ j ∈ Finset.Ico 1 N, (1 / 4 : ℝ) ^ j ≤ 1 := by
      have h1 : ∑ j ∈ Finset.Ico 1 N, (1 / 4 : ℝ) ^ j =
          (1 / 4 : ℝ) * ∑ k ∈ Finset.range (N - 1), (1 / 4 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
        · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨k + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel k 1⟩
        · intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
          obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ']
      rw [h1, geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
      have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (N - 1) := by positivity
      have hden : (1 / 4 : ℝ) - 1 = -(3 / 4) := by norm_num
      rw [hden]; linarith
    calc _ ≤ ∑ j ∈ Finset.Ico 1 N,
            ‖((-1 : ℂ) ^ (j - 1) / (j : ℂ)) *
              ((evalTrunc u N v) ^ j - evalTrunc (powCoeff u j) N v)‖ := norm_sum_le _ _
      _ ≤ (∑ j ∈ Finset.Ico 1 N, (1 / 4 : ℝ) ^ j) *
            (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
          rw [Finset.sum_mul]; exact Finset.sum_le_sum hterm
      _ ≤ 1 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
          mul_le_mul_of_nonneg_right hgeom (by positivity)
      _ ≤ Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
          rw [one_mul]; gcongr
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ 2 * Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N +
          Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := add_le_add hpart1 hpart2
    _ = (3 * Real.exp Real.pi) * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring

/-- Exact shift identity: `evalTrunc (shiftL wCoeff) (N + 1) v = (Complex.log v + evalTrunc wCoeff N v) / v`
for all `N ≥ 1` and `v ≠ 0`! -/
lemma evalTrunc_shiftL_succ {N : ℕ} (hN : 1 ≤ N) {v : ℂ} (_hv : v ≠ 0) :
    evalTrunc (shiftL wCoeff) (N + 1) v = (Complex.log v + evalTrunc wCoeff N v) / v := by
  dsimp only [evalTrunc]
  rw [Finset.sum_range_succ']
  have h0 : evalTerm (shiftL wCoeff) 0 v = 0 := by simp [evalTerm, shiftL]
  rw [h0, add_zero]
  have hterm : ∀ m ∈ Finset.range N,
      evalTerm (shiftL wCoeff) (m + 1) v =
        (if m = 0 then Complex.log v / v else 0) + evalTerm wCoeff m v / v := by
    intro m _
    dsimp only [evalTerm]
    rw [Finset.sum_range_succ]
    have htop : shiftL wCoeff (m + 1) (m + 1) = if m = 0 then 1 else 0 := by
      dsimp only [shiftL]
      have hw0 : wCoeff m (m + 1) = 0 := wCoeff_gevBound.1 m (m + 1) (by omega)
      rw [hw0, add_zero]
      by_cases hm0 : m = 0
      · subst hm0; simp
      · simp [hm0]
    have hlow : ∑ k ∈ Finset.range (m + 1), shiftL wCoeff (m + 1) k * Complex.log v ^ k =
        ∑ k ∈ Finset.range (m + 1), wCoeff m k * Complex.log v ^ k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      dsimp only [shiftL]
      have hnot : ¬ (m = 0 ∧ k = 1) := by omega
      simp only [hnot, ↓reduceIte, zero_add]
    rw [hlow, htop, add_div, div_div, ← pow_succ]
    by_cases hm0 : m = 0
    · subst hm0; simp [add_comm]
    · simp [hm0]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_div]
  have hsing : ∑ m ∈ Finset.range N, (if m = 0 then Complex.log v / v else 0) = Complex.log v / v := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h0'; exact absurd (Finset.mem_range.mpr hN) h0'
  rw [hsing, add_div]

/-- Small-`‖v‖` regime bound: when `‖v‖ < B * (N + 1)` and `1 ≤ ‖v‖`, both `1` and `‖evalTrunc a N v‖`
are bounded by Gevrey-1 terms! -/
lemma small_v_gev1_bounds {B : ℝ} (hB : 1 ≤ B) {N : ℕ} {v : ℂ} (hv1 : 1 ≤ ‖v‖)
    (hsmall : ‖v‖ < B * ((N : ℝ) + 1)) :
    let A : ℝ := 2 * max (2000 * Real.exp 1) (2 * B * Real.exp 1)
    1 ≤ A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N ∧
    ∀ {M : ℝ} (_ : 0 ≤ M) {a : LogCoeff} (_ : GevBound 2000 M a),
      ‖evalTrunc a N v‖ ≤ M * Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
  intro A
  have hA_pos : 0 < A := by
    have : 2000 * Real.exp 1 ≤ max (2000 * Real.exp 1) (2 * B * Real.exp 1) := le_max_left _ _
    have := Real.exp_pos 1
    dsimp [A]; linarith
  have hA_ge_2000e : 2000 * Real.exp 1 ≤ A / 2 := by
    dsimp [A]; linarith [le_max_left (2000 * Real.exp 1) (2 * B * Real.exp 1)]
  have hA_ge_2Be : 2 * B * Real.exp 1 ≤ A / 2 := by
    dsimp [A]; linarith [le_max_right (2000 * Real.exp 1) (2 * B * Real.exp 1)]
  have hv_pos : 0 < ‖v‖ := by linarith
  have hkey : ∀ n ≤ N, (2000 : ℝ) ^ n * (n.factorial : ℝ) / ‖v‖ ^ n ≤
      (A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
    intro n hn
    cases N with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0; simp
    | succ M' =>
      have hNpos : 1 ≤ M' + 1 := Nat.succ_pos M'
      have hv_le : ‖v‖ ≤ 2 * B * ((M' + 1 : ℕ) : ℝ) := by
        have h1 : ((M' + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((M' + 1 : ℕ) : ℝ) := by
          have : (1 : ℝ) ≤ ((M' + 1 : ℕ) : ℝ) := by exact_mod_cast hNpos
          linarith
        nlinarith [hsmall]
      have hfac_le_pow : (n.factorial : ℝ) ≤ ((M' + 1 : ℕ) : ℝ) ^ n := by
        have hnat : n.factorial ≤ (M' + 1) ^ n := by
          have h1 : ∀ k, k ≤ M' + 1 → k.factorial ≤ (M' + 1) ^ k := by
            intro k
            induction k with
            | zero => intro _; simp
            | succ k ihk =>
              intro hle
              rw [Nat.factorial_succ, pow_succ']
              exact Nat.mul_le_mul hle (ihk (by omega))
          exact h1 n hn
        exact_mod_cast hnat
      have hNpow_le : ((M' + 1 : ℕ) : ℝ) ^ (M' + 1) ≤ Real.exp 1 ^ (M' + 1) * ((M' + 1).factorial : ℝ) := by
        have h := Real.pow_div_factorial_le_exp ((M' + 1 : ℕ) : ℝ) (by positivity) (M' + 1)
        rw [div_le_iff₀ (by positivity)] at h
        have hexp : Real.exp ((M' + 1 : ℕ) : ℝ) = Real.exp 1 ^ (M' + 1) := by
          rw [← Real.exp_nat_mul]; simp
        rwa [hexp] at h
      have hpow_split : ‖v‖ ^ (M' + 1) = ‖v‖ ^ n * ‖v‖ ^ (M' + 1 - n) := by
        rw [← pow_add, Nat.add_sub_of_le hn]
      have hN_split : ((M' + 1 : ℕ) : ℝ) ^ n * ((M' + 1 : ℕ) : ℝ) ^ (M' + 1 - n) =
          ((M' + 1 : ℕ) : ℝ) ^ (M' + 1) := by
        rw [← pow_add, Nat.add_sub_of_le hn]
      have hA_split : (A / 2) ^ (M' + 1) = (A / 2) ^ n * (A / 2) ^ (M' + 1 - n) := by
        rw [← pow_add, Nat.add_sub_of_le hn]
      have hnum : (2000 : ℝ) ^ n * (n.factorial : ℝ) * ‖v‖ ^ (M' + 1 - n) ≤
          (A / 2) ^ (M' + 1) * ((M' + 1).factorial : ℝ) := by
        calc (2000 : ℝ) ^ n * (n.factorial : ℝ) * ‖v‖ ^ (M' + 1 - n)
            ≤ (2000 : ℝ) ^ n * ((M' + 1 : ℕ) : ℝ) ^ n * (2 * B * ((M' + 1 : ℕ) : ℝ)) ^ (M' + 1 - n) := by
              gcongr
          _ = (2000 : ℝ) ^ n * (2 * B) ^ (M' + 1 - n) *
                (((M' + 1 : ℕ) : ℝ) ^ n * ((M' + 1 : ℕ) : ℝ) ^ (M' + 1 - n)) := by
              rw [mul_pow]; ring
          _ = (2000 : ℝ) ^ n * (2 * B) ^ (M' + 1 - n) * ((M' + 1 : ℕ) : ℝ) ^ (M' + 1) := by rw [hN_split]
          _ ≤ (2000 : ℝ) ^ n * (2 * B) ^ (M' + 1 - n) *
                (Real.exp 1 ^ (M' + 1) * ((M' + 1).factorial : ℝ)) := by gcongr
          _ = (2000 : ℝ) ^ n * (Real.exp 1 ^ n) * ((2 * B * Real.exp 1) ^ (M' + 1 - n)) *
                ((M' + 1).factorial : ℝ) := by
              have hexp_s : Real.exp 1 ^ (M' + 1) = Real.exp 1 ^ n * Real.exp 1 ^ (M' + 1 - n) := by
                rw [← pow_add, Nat.add_sub_of_le hn]
              rw [hexp_s, mul_pow]; ring
          _ ≤ (A / 2) ^ n * (A / 2) ^ (M' + 1 - n) * ((M' + 1).factorial : ℝ) := by
              have h1 : (2000 : ℝ) ^ n * Real.exp 1 ^ n ≤ (A / 2) ^ n := by
                rw [← mul_pow]
                exact pow_le_pow_left₀ (by positivity) hA_ge_2000e n
              have h2 : (2 * B * Real.exp 1) ^ (M' + 1 - n) ≤ (A / 2) ^ (M' + 1 - n) :=
                pow_le_pow_left₀ (by positivity) hA_ge_2Be _
              have h12 := mul_le_mul h1 h2 (by positivity) (by positivity)
              exact mul_le_mul_of_nonneg_right h12 (by positivity)
          _ = (A / 2) ^ (M' + 1) * ((M' + 1).factorial : ℝ) := by rw [hA_split]
      rw [div_le_div_iff₀ (by positivity) (by positivity), hpow_split]
      have : (2000 : ℝ) ^ n * (n.factorial : ℝ) * (‖v‖ ^ n * ‖v‖ ^ (M' + 1 - n)) =
          ((2000 : ℝ) ^ n * (n.factorial : ℝ) * ‖v‖ ^ (M' + 1 - n)) * ‖v‖ ^ n := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hnum (by positivity)
  refine ⟨?_, ?_⟩
  · have h0 := hkey 0 (Nat.zero_le N)
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] at h0
    have hle : (A / 2) ^ N ≤ A ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
    calc (1 : ℝ) ≤ (A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := h0
      _ ≤ A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by gcongr
  · intro M hM a ha
    have hterm : ∀ n ∈ Finset.range N,
        ‖evalTerm a n v‖ ≤ M * Real.exp Real.pi * ‖v‖ * (A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
      intro n hn
      have hnN : n ≤ N := le_of_lt (Finset.mem_range.mp hn)
      have hbase := norm_evalTerm_le (C := M) (A := 2000) hM (by norm_num)
        (fun k hkn => (ha.2 n k hkn).trans (div_le_div_of_nonneg_left (by positivity)
          (by positivity) (by
            have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            have hsq : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith
            nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))) hv1
      calc ‖evalTerm a n v‖
          ≤ M * Real.exp Real.pi * ‖v‖ * ((2000 : ℝ) ^ n * (n.factorial : ℝ) / ‖v‖ ^ n) :=
            hbase.trans (le_of_eq (by ring))
        _ ≤ M * Real.exp Real.pi * ‖v‖ * ((A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
            mul_le_mul_of_nonneg_left (hkey n hnN) (by positivity)
        _ = M * Real.exp Real.pi * ‖v‖ * (A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
    have hNle : (N : ℝ) ≤ (2 : ℝ) ^ N := le_trans (by linarith) (nat_succ_le_two_pow N)
    have h2A : (2 : ℝ) ^ N * (A / 2) ^ N = A ^ N := by rw [← mul_pow]; ring
    calc ‖evalTrunc a N v‖ ≤ ∑ n ∈ Finset.range N, ‖evalTerm a n v‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N,
            (M * Real.exp Real.pi * ‖v‖ * (A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
          Finset.sum_le_sum hterm
      _ = (N : ℝ) * (M * Real.exp Real.pi * ‖v‖ * (A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ N * (M * Real.exp Real.pi * ‖v‖ * (A / 2) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
          mul_le_mul_of_nonneg_right hNle (by positivity)
      _ = M * Real.exp Real.pi * ‖v‖ * ((2 : ℝ) ^ N * (A / 2) ^ N) * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
      _ = M * Real.exp Real.pi * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by rw [h2A]

/-- Key Gevrey-1 residual for `S_phi w_N - 1` vs `evalTrunc (yCoeff (shiftL wCoeff)) (N + 1) v`! -/
lemma norm_S_phi_wN_sub_yN_le {N : ℕ} (hN : 1 ≤ N) {v : ℂ} (hv : v ∈ V_sec)
    (hbig : 32000 * ((N + 1 : ℕ) : ℝ) ≤ ‖v‖) :
    let wN : ℂ := v + Complex.log v + evalTrunc wCoeff N v
    let A_S : ℝ := max 2000 (2 / Real.cos phiRay)
    let C_S : ℝ := 4 / (Real.sin deltaV * Real.cos phiRay ^ 2) + 14 * Real.exp Real.pi
    ‖(S_phi wN - 1) - evalTrunc (yCoeff (shiftL wCoeff)) (N + 1) v‖ ≤
      C_S * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
  intro wN A_S C_S
  set M : ℕ := N + 1
  have hM1 : 1 ≤ M := by omega
  have hv_ge : (10 : ℝ) ^ 14 ≤ ‖v‖ := R_sec_ge_1e14.trans hv.1
  have hv1 : 1 ≤ ‖v‖ := by linarith
  have hv_pos : 0 < ‖v‖ := by linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp hv_pos
  have hv_dom : v ∈ V_dom := V_sec_subset_V_dom hv
  have hbigN : 32000 * (N : ℝ) ≤ ‖v‖ := by
    have : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show N ≤ M by omega)
    linarith
  have hw_small : ‖evalTrunc wCoeff N v‖ ≤ 1 / 16 := by
    have h := norm_evalTrunc_small (M := 1) zero_le_one wCoeff_zero wCoeff_gevBound hv hbigN
    linarith
  have hwN_cb : wN ∈ Metric.closedBall (v + Complex.log v) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : wN - (v + Complex.log v) = evalTrunc wCoeff N v := by dsimp [wN]; ring
    rw [heq]; linarith
  obtain ⟨hwN_mem, _, _, _⟩ := closedBall_log_props hv_dom hwN_cb
  have hsh_gev : GevBound 2000 (1 / 250) (shiftL wCoeff) :=
    (gevBound_phiOp wCoeff_zero wCoeff_gevBound).1
  have hsh0 : ∀ k, shiftL wCoeff 0 k = 0 := fun _ => rfl
  let uM : ℂ := evalTrunc (shiftL wCoeff) M v
  have huM_eq : uM = (Complex.log v + evalTrunc wCoeff N v) / v :=
    evalTrunc_shiftL_succ hN hv0
  have hwN_fac : wN = v * (1 + uM) := by
    dsimp only [wN]; rw [huM_eq]; field_simp [hv0]; ring
  have huM_sm : ‖uM‖ ≤ 1 / 4 := by
    have h := norm_evalTrunc_small (M := 1 / 250) (by norm_num) hsh0 hsh_gev hv hbig
    linarith
  have hlog_ge_one : 1 ≤ ‖Complex.log v‖ := by
    have h1 : Real.exp 1 ≤ ‖v‖ := by linarith [Real.exp_one_lt_d9]
    have h2 : 1 ≤ Real.log ‖v‖ := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ‖v‖ := Real.log_le_log (Real.exp_pos 1) h1
    exact h2.trans (by rw [← Complex.log_re v]; exact Complex.re_le_norm _)
  have huM_log : ‖uM‖ ≤ 2 * ‖Complex.log v‖ / ‖v‖ := by
    rw [huM_eq, norm_div]
    refine div_le_div_of_nonneg_right ?_ hv_pos.le
    calc ‖Complex.log v + evalTrunc wCoeff N v‖
        ≤ ‖Complex.log v‖ + ‖evalTrunc wCoeff N v‖ := norm_add_le _ _
      _ ≤ ‖Complex.log v‖ + 1 / 16 := add_le_add_right hw_small _
      _ ≤ 2 * ‖Complex.log v‖ := by linarith
  have hA_ge_2000 : (2000 : ℝ) ≤ A_S := le_max_left _ _
  have hA_ge_cos : 2 / Real.cos phiRay ≤ A_S := le_max_right _ _
  have hA_pos : 0 < A_S := lt_of_lt_of_le (by norm_num) hA_ge_2000
  have h1u_lo : 1 / 2 ≤ ‖1 + uM‖ := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans huM_sm)).1
    exact (show (1 / 2 : ℝ) ≤ (1 + uM).re by simp only [Complex.add_re, Complex.one_re]; linarith).trans
      (Complex.re_le_norm _)
  have h1u_hi : ‖1 + uM‖ ≤ 2 := by
    calc ‖1 + uM‖ ≤ ‖(1 : ℂ)‖ + ‖uM‖ := norm_add_le _ _
      _ ≤ 1 + 1 / 4 := by rw [norm_one]; linarith
      _ ≤ 2 := by norm_num
  have hwN_lo : ‖v‖ / 2 ≤ ‖wN‖ := by
    rw [hwN_fac, norm_mul]; nlinarith
  have hwN_hi : ‖wN‖ ≤ 2 * ‖v‖ := by
    rw [hwN_fac, norm_mul]; nlinarith
  have hwN_pos : 0 < ‖wN‖ := by linarith
  -- Part 1: Stieltjes asymptotic remainder `‖(S_phi wN - 1) - ∑ m ∈ Ico 1 M, m! / wN^m‖`.
  have hpart1 : ‖(S_phi wN - 1) - ∑ m ∈ Finset.Ico 1 M, (m.factorial : ℂ) / wN ^ m‖ ≤
      (4 / (Real.sin deltaV * Real.cos phiRay ^ 2)) * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
    have hsin_pos : 0 < Real.sin deltaV := sin_deltaV_pos
    have hcos_pos : 0 < Real.cos phiRay := cos_phiRay_pos
    have hsum_eq : (1 : ℂ) + ∑ m ∈ Finset.Ico 1 M, (m.factorial : ℂ) / wN ^ m =
        ∑ m ∈ Finset.range M, (m.factorial : ℂ) / wN ^ m := by
      have hU : Finset.range M = {0} ∪ Finset.Ico 1 M := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]; omega
      rw [hU, Finset.sum_union (by simp), Finset.sum_singleton]
      simp
    have hsub_eq : (S_phi wN - 1) - ∑ m ∈ Finset.Ico 1 M, (m.factorial : ℂ) / wN ^ m =
        S_phi wN - ∑ m ∈ Finset.range M, (m.factorial : ℂ) / wN ^ m := by
      rw [← hsum_eq]; ring
    rw [hsub_eq]
    have hst := norm_S_phi_sub_trunc_le M hwN_mem
    have hdw := V_sec_distPhi_ge hv hwN_cb
    have hdw_pos : 0 < distPhi wN := lt_of_lt_of_le (mul_pos (half_pos hsin_pos) hv_pos) hdw
    have hratio : ‖wN‖ / distPhi wN ≤ 4 / Real.sin deltaV := by
      rw [div_le_div_iff₀ hdw_pos hsin_pos]
      nlinarith
    have hM_div : (2 * (M : ℝ)) / ‖v‖ ≤ 1 := by
      rw [div_le_one hv_pos]; linarith
    have hpow_wN : (M.factorial : ℝ) / ‖wN‖ ^ M ≤ (2 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
      have hinv : (1 : ℝ) / ‖wN‖ ^ M ≤ (2 : ℝ) ^ M / ‖v‖ ^ M := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
        have : ‖v‖ ≤ 2 * ‖wN‖ := by linarith
        exact pow_le_pow_left₀ hv_pos.le this M
      calc (M.factorial : ℝ) / ‖wN‖ ^ M
          = (M.factorial : ℝ) * (1 / ‖wN‖ ^ M) := by ring
        _ ≤ (M.factorial : ℝ) * ((2 : ℝ) ^ M / ‖v‖ ^ M) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (2 * (M : ℝ) / ‖v‖) * ((2 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
            dsimp only [M]; rw [Nat.factorial_succ, pow_succ, pow_succ]; push_cast
            have hne : ‖v‖ ^ N ≠ 0 := by positivity
            field_simp [hne, hv_pos.ne']
        _ ≤ 1 * ((2 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
            mul_le_mul_of_nonneg_right hM_div (by positivity)
        _ = (2 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := one_mul _
    have hcos_split : Real.cos phiRay ^ (M + 1) = Real.cos phiRay ^ 2 * Real.cos phiRay ^ N := by
      dsimp only [M]; rw [← pow_add, show 2 + N = N + 1 + 1 by omega]
    calc ‖S_phi wN - ∑ m ∈ Finset.range M, (m.factorial : ℂ) / wN ^ m‖
        ≤ ‖wN‖ / (distPhi wN * Real.cos phiRay ^ (M + 1)) * (M.factorial : ℝ) / ‖wN‖ ^ M := hst
      _ = (‖wN‖ / distPhi wN) * (1 / Real.cos phiRay ^ (M + 1)) * ((M.factorial : ℝ) / ‖wN‖ ^ M) := by
          have h1 : distPhi wN ≠ 0 := hdw_pos.ne'
          have h2 : Real.cos phiRay ^ (M + 1) ≠ 0 := (pow_pos hcos_pos _).ne'
          have h3 : ‖wN‖ ^ M ≠ 0 := by positivity
          field_simp [h1, h2, h3]
      _ ≤ (4 / Real.sin deltaV) * (1 / Real.cos phiRay ^ (M + 1)) *
            ((2 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
      _ = (4 / (Real.sin deltaV * Real.cos phiRay ^ 2)) *
            ((2 / Real.cos phiRay) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
          rw [hcos_split, div_pow]
          have h1 : Real.sin deltaV ≠ 0 := hsin_pos.ne'
          have h2 : Real.cos phiRay ^ 2 ≠ 0 := (pow_pos hcos_pos 2).ne'
          have h3 : Real.cos phiRay ^ N ≠ 0 := (pow_pos hcos_pos N).ne'
          have h4 : ‖v‖ ^ N ≠ 0 := by positivity
          field_simp [h1, h2, h3, h4]
      _ ≤ (4 / (Real.sin deltaV * Real.cos phiRay ^ 2)) * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
          have h1 : (2 / Real.cos phiRay) ^ N ≤ A_S ^ N :=
            pow_le_pow_left₀ (by positivity) hA_ge_cos N
          have h2 : (4 / (Real.sin deltaV * Real.cos phiRay ^ 2)) ≤
              (4 / (Real.sin deltaV * Real.cos phiRay ^ 2)) * ‖v‖ := by
            have : (0 : ℝ) ≤ 4 / (Real.sin deltaV * Real.cos phiRay ^ 2) := by positivity
            nlinarith
          calc _ ≤ (4 / (Real.sin deltaV * Real.cos phiRay ^ 2)) * ‖v‖ *
                (A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
            _ = _ := by ring
  -- Part 2: Exact rewrite of `evalTrunc (yCoeff (shiftL wCoeff)) M v`!
  have hy_eq : evalTrunc (yCoeff (shiftL wCoeff)) M v =
      ∑ m ∈ Finset.Ico 1 M, ((m.factorial : ℂ) / v ^ m) *
        ∑ j ∈ Finset.range (M - m),
          ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) *
            evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v := by
    -- First expand `evalTrunc (yCoeff u) M v = ∑ m ∈ Ico 1 M, (m! / v^m) * evalTrunc (negPowCoeff m u) (M - m) v`
    have hstep1 : evalTrunc (yCoeff (shiftL wCoeff)) M v =
        ∑ m ∈ Finset.Ico 1 M, ((m.factorial : ℂ) / v ^ m) *
          evalTrunc (negPowCoeff m (shiftL wCoeff)) (M - m) v := by
      dsimp only [evalTrunc, evalTerm, yCoeff]
      have hterm_n : ∀ n ∈ Finset.range M,
          (∑ K ∈ Finset.range (n + 1),
            (∑ m ∈ Finset.Ico 1 (n + 1), (m.factorial : ℂ) * negPowCoeff m (shiftL wCoeff) (n - m) K) *
              Complex.log v ^ K) / v ^ n =
          ∑ m ∈ Finset.Ico 1 (n + 1),
            ((m.factorial : ℂ) / v ^ m) *
              ((∑ K ∈ Finset.range (n - m + 1), negPowCoeff m (shiftL wCoeff) (n - m) K * Complex.log v ^ K) /
                v ^ (n - m)) := by
        intro n _
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm, Finset.sum_div]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
        have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hm).2
        have hKsub : ∑ K ∈ Finset.range (n + 1),
              (m.factorial : ℂ) * negPowCoeff m (shiftL wCoeff) (n - m) K * Complex.log v ^ K =
            (m.factorial : ℂ) * ∑ K ∈ Finset.range (n - m + 1),
              negPowCoeff m (shiftL wCoeff) (n - m) K * Complex.log v ^ K := by
          rw [Finset.mul_sum]
          have hsub : Finset.range (n - m + 1) ⊆ Finset.range (n + 1) :=
            Finset.range_mono (by omega)
          rw [← Finset.sum_subset hsub]
          · refine Finset.sum_congr rfl fun K _ => by ring
          · intro K hK hnot
            simp only [Finset.mem_range] at hK hnot
            have hKgt : n - m < K := by omega
            have h0 : negPowCoeff m (shiftL wCoeff) (n - m) K = 0 := by
              dsimp only [negPowCoeff]
              refine Finset.sum_eq_zero fun j _ => ?_
              have hp0 : powCoeff (shiftL wCoeff) j (n - m) K = 0 := by
                cases j with
                | zero => simp [powCoeff, constCoeff]; intro h1; omega
                | succ j' => exact (gevBound_powCoeff (by norm_num) (by norm_num) hsh_gev (j' + 1)
                    (Nat.succ_pos j')).1 (n - m) K hKgt
              rw [hp0, mul_zero]
            rw [h0, mul_zero, zero_mul]
        rw [hKsub]
        have hpow_v : v ^ n = v ^ m * v ^ (n - m) := by rw [← pow_add, Nat.add_sub_of_le hmn]
        rw [hpow_v, mul_div_mul_comm]
      rw [Finset.sum_congr rfl hterm_n]
      -- Swap `∑ n ∈ range M, ∑ m ∈ Ico 1 (n + 1)` with `∑ m ∈ Ico 1 M, ∑ r ∈ range (M - m)`!
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ => (⟨x.2, x.1 - x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hx ⊢; omega
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hx₁ hx₂
        have h1' : x₁.2 = x₂.2 := congr_arg Sigma.fst heq
        have h2' : x₁.1 - x₁.2 = x₂.1 - x₂.2 := by simpa using congr_arg Sigma.snd heq
        exact Sigma.ext (by omega) (heq_of_eq h1')
      · intro y hy
        simp only [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hy
        refine ⟨⟨y.1 + y.2, y.1⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]; omega
        · ext <;> simp
      · intro _ _; rfl
    rw [hstep1]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    dsimp only [evalTrunc, evalTerm, negPowCoeff]
    have hterm_r : ∀ r ∈ Finset.range (M - m),
        (∑ K ∈ Finset.range (r + 1),
          (∑ j ∈ Finset.range (r + 1),
            ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * powCoeff (shiftL wCoeff) j r K) *
              Complex.log v ^ K) / v ^ r =
        ∑ j ∈ Finset.range (M - m),
          ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) *
            ((∑ K ∈ Finset.range (r + 1), powCoeff (shiftL wCoeff) j r K * Complex.log v ^ K) / v ^ r) := by
      intro r hr
      have hrM : r < M - m := Finset.mem_range.mp hr
      have hsub : ∀ K,
          ∑ j ∈ Finset.range (r + 1),
            ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * powCoeff (shiftL wCoeff) j r K =
          ∑ j ∈ Finset.range (M - m),
            ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) * powCoeff (shiftL wCoeff) j r K := by
        intro K
        refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
        intro j hj hnot
        simp only [Finset.mem_range] at hj hnot
        rw [powCoeff_zero_lt hsh0 j r K (by omega : r < j), mul_zero]
      simp_rw [hsub, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_assoc, mul_div_assoc]
    rw [Finset.sum_congr rfl hterm_r, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  -- Part 3: Bound `‖∑ m ∈ Ico 1 M, m! / wN^m - evalTrunc (yCoeff (shiftL wCoeff)) M v‖`!
  have hpart2 : ‖∑ m ∈ Finset.Ico 1 M, (m.factorial : ℂ) / wN ^ m -
        evalTrunc (yCoeff (shiftL wCoeff)) M v‖ ≤
      (14 * Real.exp Real.pi) * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
    rw [hy_eq, ← Finset.sum_sub_distrib]
    have h2000_step : (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M ≤
        (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
      have hratio : (2000 : ℝ) * (M : ℝ) / ‖v‖ ≤ 1 := by
        rw [div_le_one hv_pos]; linarith
      have hrew : (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M =
          ((2000 : ℝ) * (M : ℝ) / ‖v‖) * ((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        dsimp only [M]; rw [pow_succ, pow_succ, Nat.factorial_succ]; push_cast
        have hne : ‖v‖ ^ N ≠ 0 := by positivity
        field_simp [hne, hv_pos.ne']
      rw [hrew]
      calc _ ≤ 1 * ((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = _ := one_mul _
    -- Split each `m ∈ Ico 1 M` into 3 error terms!
    have hm_bound : ∀ m ∈ Finset.Ico 1 M,
        ‖(m.factorial : ℂ) / wN ^ m -
          ((m.factorial : ℂ) / v ^ m) *
            ∑ j ∈ Finset.range (M - m),
              ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) *
                evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v‖ ≤
        (8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N / (32000 : ℝ)) +
        ((1 / 16000 : ℝ) ^ m * 2 + (1 / 1000 : ℝ) ^ m * 4) *
          (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
      have hmM : m < M := (Finset.mem_Ico.mp hm).2
      have hrew : (m.factorial : ℂ) / wN ^ m = ((m.factorial : ℂ) / v ^ m) * ((1 + uM)⁻¹ : ℂ) ^ m := by
        rw [hwN_fac, mul_pow, inv_pow]; ring
      rw [hrew, ← mul_sub]
      -- Split `((1 + uM)⁻¹)^m - ∑ c_j * evalTrunc(u^j, M-m)` into 3 pieces:
      let c : ℕ → ℂ := fun j => (-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)
      have hc_bd : ∀ j, ‖c j‖ ≤ (2 : ℝ) ^ m * (2 : ℝ) ^ j := by
        intro j
        dsimp only [c]
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
        have hnat : (m + j - 1).choose j ≤ 2 ^ (m + j) :=
          (Nat.choose_le_two_pow (m + j - 1) j).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [← pow_add]; exact_mod_cast hnat
      have h3split : ((1 + uM)⁻¹ : ℂ) ^ m -
            ∑ j ∈ Finset.range (M - m), c j * evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v =
          (((1 + uM)⁻¹ : ℂ) ^ m - ∑ j ∈ Finset.range (M - m), c j * uM ^ j) +
          (∑ j ∈ Finset.range (M - m), c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v)) +
          (∑ j ∈ Finset.range (M - m), c j *
            (evalTrunc (powCoeff (shiftL wCoeff) j) M v - evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)) := by
        have h1 : ∑ j ∈ Finset.range (M - m), c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v) =
            ∑ j ∈ Finset.range (M - m), c j * uM ^ j -
            ∑ j ∈ Finset.range (M - m), c j * evalTrunc (powCoeff (shiftL wCoeff) j) M v := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
        have h2 : ∑ j ∈ Finset.range (M - m), c j *
              (evalTrunc (powCoeff (shiftL wCoeff) j) M v - evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v) =
            ∑ j ∈ Finset.range (M - m), c j * evalTrunc (powCoeff (shiftL wCoeff) j) M v -
            ∑ j ∈ Finset.range (M - m), c j * evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [h1, h2]; ring
      change ‖((m.factorial : ℂ) / v ^ m) *
          (((1 + uM)⁻¹ : ℂ) ^ m - ∑ j ∈ Finset.range (M - m), c j * evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)‖ ≤ _
      rw [h3split, mul_add, mul_add]
      -- Piece A: Taylor remainder of `(1 + uM)^{-m}`!
      have hA : ‖((m.factorial : ℂ) / v ^ m) *
            (((1 + uM)⁻¹ : ℂ) ^ m - ∑ j ∈ Finset.range (M - m), c j * uM ^ j)‖ ≤
          8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N / (32000 : ℝ) := by
        rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow]
        have htay := norm_inv_one_add_pow_sub_sum_le_four (M := M - m) hm1 huM_sm
        rw [show m + (M - m) = M by omega] at htay
        have hlogMm : ‖Complex.log v‖ ^ (M - m) ≤ Real.exp Real.pi * ‖v‖ * ((M - m).factorial : ℝ) := by
          have h := (Real.pow_div_factorial_le_exp ‖Complex.log v‖ (norm_nonneg _) (M - m)).trans
            (exp_norm_log_le hv1)
          rwa [div_le_iff₀ (by positivity)] at h
        have hfac_prod : (m.factorial : ℝ) * ((M - m).factorial : ℝ) ≤ (M.factorial : ℝ) := by
          have h1 := Nat.choose_mul_factorial_mul_factorial (le_of_lt hmM)
          have hpos : 1 ≤ M.choose m := Nat.choose_pos (le_of_lt hmM)
          exact_mod_cast (show m.factorial * (M - m).factorial ≤ M.factorial by nlinarith)
        have hpow_v : ‖v‖ ^ m * ‖v‖ ^ (M - m) = ‖v‖ ^ M := by
          rw [← pow_add, Nat.add_sub_of_le (le_of_lt hmM)]
        have h8M : (4 : ℝ) ^ M * (2 : ℝ) ^ (M - m) ≤ (8 : ℝ) ^ M := by
          have h2le : (2 : ℝ) ^ (M - m) ≤ (2 : ℝ) ^ M :=
            pow_le_pow_right₀ (by norm_num) (Nat.sub_le M m)
          have h42 : (4 : ℝ) ^ M * (2 : ℝ) ^ M = (8 : ℝ) ^ M := by rw [← mul_pow]; norm_num
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) M]
        have hM_div : (M : ℝ) / ‖v‖ ≤ 1 / 32000 := by
          rw [div_le_iff₀ hv_pos]; linarith
        calc (m.factorial : ℝ) / ‖v‖ ^ m *
              ‖((1 + uM)⁻¹ : ℂ) ^ m - ∑ j ∈ Finset.range (M - m), c j * uM ^ j‖
            ≤ (m.factorial : ℝ) / ‖v‖ ^ m * ((4 : ℝ) ^ M * ‖uM‖ ^ (M - m)) :=
              mul_le_mul_of_nonneg_left htay (by positivity)
          _ ≤ (m.factorial : ℝ) / ‖v‖ ^ m * ((4 : ℝ) ^ M * (2 * ‖Complex.log v‖ / ‖v‖) ^ (M - m)) := by
              gcongr
          _ = ((4 : ℝ) ^ M * (2 : ℝ) ^ (M - m)) * (m.factorial : ℝ) * ‖Complex.log v‖ ^ (M - m) /
                (‖v‖ ^ m * ‖v‖ ^ (M - m)) := by
              rw [div_pow, mul_pow]; ring
          _ ≤ (8 : ℝ) ^ M * (m.factorial : ℝ) * (Real.exp Real.pi * ‖v‖ * ((M - m).factorial : ℝ)) / ‖v‖ ^ M := by
              rw [hpow_v]; gcongr
          _ = (8 : ℝ) ^ M * Real.exp Real.pi * ‖v‖ * ((m.factorial : ℝ) * ((M - m).factorial : ℝ)) / ‖v‖ ^ M := by
              ring
          _ ≤ (8 : ℝ) ^ M * Real.exp Real.pi * ‖v‖ * (M.factorial : ℝ) / ‖v‖ ^ M := by gcongr
          _ = ((M : ℝ) / ‖v‖) * (8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              dsimp only [M]; rw [pow_succ, pow_succ, Nat.factorial_succ]; push_cast
              have hne : ‖v‖ ^ N ≠ 0 := by positivity
              field_simp [hne, hv_pos.ne']
          _ ≤ (1 / 32000 : ℝ) * (8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
              mul_le_mul_of_nonneg_right hM_div (by positivity)
          _ = 8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N / (32000 : ℝ) := by ring
      -- Piece B: power-truncation remainder at order `M`!
      have hB : ‖((m.factorial : ℂ) / v ^ m) *
            ∑ j ∈ Finset.range (M - m), c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v)‖ ≤
          (1 / 16000 : ℝ) ^ m * 2 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow]
        have hm_fac : (m.factorial : ℝ) / ‖v‖ ^ m ≤ (1 / 32000 : ℝ) ^ m := by
          have hnat : m.factorial ≤ M ^ m := by
            have h1 : ∀ k, k ≤ M → k.factorial ≤ M ^ k := by
              intro k; induction k with
              | zero => intro _; simp
              | succ k ihk => intro hle; rw [Nat.factorial_succ, pow_succ']; exact Nat.mul_le_mul hle (ihk (by omega))
            exact h1 m (le_of_lt hmM)
          have hcast : (m.factorial : ℝ) ≤ (M : ℝ) ^ m := by exact_mod_cast hnat
          have hratio : (M : ℝ) / ‖v‖ ≤ 1 / 32000 := by rw [div_le_iff₀ hv_pos]; linarith
          calc (m.factorial : ℝ) / ‖v‖ ^ m ≤ (M : ℝ) ^ m / ‖v‖ ^ m :=
                div_le_div_of_nonneg_right hcast (by positivity)
            _ = ((M : ℝ) / ‖v‖) ^ m := (div_pow _ _ _).symm
            _ ≤ (1 / 32000 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hratio m
        have hterm : ∀ j ∈ Finset.range (M - m),
            ‖c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v)‖ ≤
              (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ j *
                (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by
          intro j _
          rw [norm_mul]
          have hp := norm_pow_sub_evalTrunc_powCoeff (M := 1 / 250) (by norm_num) (by norm_num)
            hsh0 hsh_gev hM1 hv hbig j
          have h24 : (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j = (1 / 2 : ℝ) ^ j := by rw [← mul_pow]; norm_num
          calc ‖c j‖ * ‖uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v‖
              ≤ ((2 : ℝ) ^ m * (2 : ℝ) ^ j) *
                  ((1 / 4 : ℝ) ^ j * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) :=
                mul_le_mul (hc_bd j) hp (norm_nonneg _) (by positivity)
            _ = (2 : ℝ) ^ m * ((2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j) *
                  (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by ring
            _ = (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ j *
                  (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by rw [h24]
        have hgeom : ∑ j ∈ Finset.range (M - m), (1 / 2 : ℝ) ^ j ≤ 2 := by
          rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
          have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (M - m) := by positivity
          have hden : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
          rw [hden]; linarith
        have h16000 : (1 / 32000 : ℝ) ^ m * (2 : ℝ) ^ m = (1 / 16000 : ℝ) ^ m := by
          rw [← mul_pow]; norm_num
        have hsum_le : ‖∑ j ∈ Finset.range (M - m), c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v)‖ ≤
            (2 : ℝ) ^ m * 2 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by
          calc _ ≤ ∑ j ∈ Finset.range (M - m),
                ‖c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v)‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range (M - m),
                  (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ j *
                    (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) :=
                Finset.sum_le_sum hterm
            _ = (2 : ℝ) ^ m * (∑ j ∈ Finset.range (M - m), (1 / 2 : ℝ) ^ j) *
                  (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by
                rw [Finset.mul_sum, Finset.sum_mul]
            _ ≤ (2 : ℝ) ^ m * 2 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by
                gcongr
        calc (m.factorial : ℝ) / ‖v‖ ^ m *
              ‖∑ j ∈ Finset.range (M - m), c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v)‖
            ≤ (1 / 32000 : ℝ) ^ m *
                ((2 : ℝ) ^ m * 2 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M)) :=
              mul_le_mul hm_fac hsum_le (norm_nonneg _) (by positivity)
          _ = ((1 / 32000 : ℝ) ^ m * (2 : ℝ) ^ m) * 2 *
                (Real.exp Real.pi * ‖v‖ * ((2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M)) := by ring
          _ ≤ (1 / 16000 : ℝ) ^ m * 2 *
                (Real.exp Real.pi * ‖v‖ * ((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) := by
              rw [h16000]; gcongr
          _ = (1 / 16000 : ℝ) ^ m * 2 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              ring
      -- Piece C: tail degrees `n ∈ Ico (M - m) M`!
      have hC : ‖((m.factorial : ℂ) / v ^ m) *
            ∑ j ∈ Finset.range (M - m), c j *
              (evalTrunc (powCoeff (shiftL wCoeff) j) M v - evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)‖ ≤
          (1 / 1000 : ℝ) ^ m * 4 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow]
        have htail_j : ∀ j ∈ Finset.range (M - m),
            (m.factorial : ℝ) / ‖v‖ ^ m *
              ‖c j * (evalTrunc (powCoeff (shiftL wCoeff) j) M v -
                evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)‖ ≤
            (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ j * 2 *
              (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by
          intro j _
          have hdiff : evalTrunc (powCoeff (shiftL wCoeff) j) M v -
                evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v =
              ∑ n ∈ Finset.Ico (M - m) M, evalTerm (powCoeff (shiftL wCoeff) j) n v := by
            dsimp only [evalTrunc]
            have hU : Finset.range M = Finset.range (M - m) ∪ Finset.Ico (M - m) M := by
              ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
            rw [hU, Finset.sum_union (by simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]; intro a ha hb; omega)]
            ring
          rw [hdiff]
          cases j with
          | zero =>
            have h0 : ∑ n ∈ Finset.Ico (M - m) M, evalTerm (powCoeff (shiftL wCoeff) 0) n v = 0 := by
              refine Finset.sum_eq_zero fun n hn => ?_
              have hn1 : 1 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
              dsimp only [evalTerm, powCoeff, constCoeff]
              have : ∑ k ∈ Finset.range (n + 1), (if n = 0 ∧ k = 0 then (1 : ℂ) else 0) * Complex.log v ^ k = 0 :=
                Finset.sum_eq_zero fun k _ => by simp [show n ≠ 0 by omega]
              rw [this, zero_div]
            rw [h0, mul_zero, norm_zero, mul_zero]; positivity
          | succ j' =>
            have hpg := gevBound_powCoeff (by norm_num) (by norm_num) hsh_gev (j' + 1) (Nat.succ_pos j')
            have hterm_n : ∀ n ∈ Finset.Ico (M - m) M,
                (m.factorial : ℝ) / ‖v‖ ^ m * ‖c (j' + 1)‖ * ‖evalTerm (powCoeff (shiftL wCoeff) (j' + 1)) n v‖ ≤
                  (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ (j' + 1) * (1 / 8 : ℝ) ^ (m + n - M) *
                    (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by
              intro n hn
              have hn_lo : M - m ≤ n := (Finset.mem_Ico.mp hn).1
              have hn_hi : n < M := (Finset.mem_Ico.mp hn).2
              have hbase := norm_evalTerm_le (C := (16 * (1 / 250 : ℝ)) ^ (j' + 1) / 16) (A := 2000)
                (by positivity) (by norm_num)
                (fun k hkn => (hpg.2 n k hkn).trans (div_le_div_of_nonneg_left (by positivity)
                  (by positivity) (by
                    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                    have hsq : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith
                    nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))) hv1
              have hfac_prod : (m.factorial : ℝ) * (n.factorial : ℝ) ≤ ((m + n).factorial : ℝ) := by
                have h1 := Nat.choose_mul_factorial_mul_factorial (show m ≤ m + n by omega)
                rw [Nat.add_sub_cancel_left] at h1
                have hpos : 1 ≤ (m + n).choose m := Nat.choose_pos (by omega)
                exact_mod_cast (show m.factorial * n.factorial ≤ (m + n).factorial by nlinarith)
              have hfac_ratio : ((m + n).factorial : ℝ) ≤ (2 * (M : ℝ)) ^ (m + n - M) * (M.factorial : ℝ) := by
                have hnat : ∀ d : ℕ, M + d < 2 * M → (M + d).factorial ≤ (2 * M) ^ d * M.factorial := by
                  intro d; induction d with
                  | zero => intro _; simp
                  | succ d ihd =>
                    intro hlt; rw [← Nat.add_assoc, Nat.factorial_succ, pow_succ', mul_assoc]
                    exact Nat.mul_le_mul (by omega) (ihd (by omega))
                have h := hnat (m + n - M) (by omega)
                rw [Nat.add_sub_of_le (by omega : M ≤ m + n)] at h
                exact_mod_cast h
              have hpow_step : (2000 : ℝ) ^ (m + n) * ((m + n).factorial : ℝ) / ‖v‖ ^ (m + n) ≤
                  ((2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) * (1 / 8 : ℝ) ^ (m + n - M) := by
                have h1 : (2000 : ℝ) ^ (m + n) = (2000 : ℝ) ^ M * (2000 : ℝ) ^ (m + n - M) := by
                  rw [← pow_add, Nat.add_sub_of_le (by omega)]
                have h2 : ‖v‖ ^ (m + n) = ‖v‖ ^ M * ‖v‖ ^ (m + n - M) := by
                  rw [← pow_add, Nat.add_sub_of_le (by omega)]
                have hr : (2000 : ℝ) * (2 * (M : ℝ)) / ‖v‖ ≤ 1 / 8 := by
                  rw [div_le_iff₀ hv_pos]; linarith
                calc _ ≤ (2000 : ℝ) ^ (m + n) * ((2 * (M : ℝ)) ^ (m + n - M) * (M.factorial : ℝ)) / ‖v‖ ^ (m + n) := by
                      gcongr
                  _ = ((2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) *
                        ((2000 : ℝ) * (2 * (M : ℝ)) / ‖v‖) ^ (m + n - M) := by
                      rw [h1, h2, div_pow, mul_pow, mul_pow]; ring
                  _ ≤ ((2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) * (1 / 8 : ℝ) ^ (m + n - M) :=
                      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr _) (by positivity)
              have h2j : (2 : ℝ) ^ (j' + 1) * ((16 * (1 / 250 : ℝ)) ^ (j' + 1) / 16) ≤ (1 / 2 : ℝ) ^ (j' + 1) := by
                have h1 : (2 : ℝ) ^ (j' + 1) * (16 * (1 / 250 : ℝ)) ^ (j' + 1) = (32 / 250 : ℝ) ^ (j' + 1) := by
                  rw [← mul_pow]; norm_num
                have h2 : (32 / 250 : ℝ) ^ (j' + 1) ≤ (1 / 2 : ℝ) ^ (j' + 1) :=
                  pow_le_pow_left₀ (by norm_num) (by norm_num) _
                have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j' + 1) := by positivity
                linarith
              have h2m : (2 : ℝ) ^ m / (2000 : ℝ) ^ m = (1 / 1000 : ℝ) ^ m := by
                rw [← div_pow]; norm_num
              have h2000n : (2000 : ℝ) ^ n = (2000 : ℝ) ^ (m + n) / (2000 : ℝ) ^ m := by
                rw [pow_add]; field_simp [show (2000 : ℝ) ^ m ≠ 0 by positivity]
              have hvmn : ‖v‖ ^ m * ‖v‖ ^ n = ‖v‖ ^ (m + n) := (pow_add _ _ _).symm
              calc (m.factorial : ℝ) / ‖v‖ ^ m * ‖c (j' + 1)‖ *
                    ‖evalTerm (powCoeff (shiftL wCoeff) (j' + 1)) n v‖
                  ≤ (m.factorial : ℝ) / ‖v‖ ^ m * ((2 : ℝ) ^ m * (2 : ℝ) ^ (j' + 1)) *
                      ((16 * (1 / 250 : ℝ)) ^ (j' + 1) / 16 * Real.exp Real.pi * ‖v‖ *
                        (2000 : ℝ) ^ n * (n.factorial : ℝ) / ‖v‖ ^ n) := by
                    have h1 := mul_le_mul_of_nonneg_left (hc_bd (j' + 1)) (by positivity : 0 ≤ (m.factorial : ℝ) / ‖v‖ ^ m)
                    exact mul_le_mul h1 hbase (norm_nonneg _) (by positivity)
                _ = ((2 : ℝ) ^ m / (2000 : ℝ) ^ m) *
                      ((2 : ℝ) ^ (j' + 1) * ((16 * (1 / 250 : ℝ)) ^ (j' + 1) / 16)) *
                      Real.exp Real.pi * ‖v‖ *
                      ((2000 : ℝ) ^ (m + n) * ((m.factorial : ℝ) * (n.factorial : ℝ)) / ‖v‖ ^ (m + n)) := by
                    rw [h2000n, ← hvmn]
                    have hne1 : (2000 : ℝ) ^ m ≠ 0 := by positivity
                    have hne2 : ‖v‖ ^ m ≠ 0 := by positivity
                    have hne3 : ‖v‖ ^ n ≠ 0 := by positivity
                    field_simp [hne1, hne2, hne3]
                _ ≤ (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ (j' + 1) * Real.exp Real.pi * ‖v‖ *
                      ((2000 : ℝ) ^ (m + n) * ((m + n).factorial : ℝ) / ‖v‖ ^ (m + n)) := by
                    rw [h2m]; gcongr
                _ ≤ (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ (j' + 1) * Real.exp Real.pi * ‖v‖ *
                      (((2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) * (1 / 8 : ℝ) ^ (m + n - M)) := by
                    gcongr
                _ = (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ (j' + 1) * (1 / 8 : ℝ) ^ (m + n - M) *
                      (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by ring
            have hgeom_n : ∑ n ∈ Finset.Ico (M - m) M, (1 / 8 : ℝ) ^ (m + n - M) ≤ 2 := by
              have hbij : ∑ n ∈ Finset.Ico (M - m) M, (1 / 8 : ℝ) ^ (m + n - M) =
                  ∑ d ∈ Finset.range m, (1 / 8 : ℝ) ^ d := by
                refine Finset.sum_bij (fun n _ => m + n - M) ?_ ?_ ?_ ?_
                · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
                · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
                · intro d hd; simp only [Finset.mem_range] at hd
                  exact ⟨M - m + d, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
                · intro _ _; rfl
              rw [hbij, geom_sum_eq (by norm_num : (1 / 8 : ℝ) ≠ 1)]
              have : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ m := by positivity
              have hden : (1 / 8 : ℝ) - 1 = -(7 / 8) := by norm_num
              rw [hden]; linarith
            rw [norm_mul]
            calc (m.factorial : ℝ) / ‖v‖ ^ m * (‖c (j' + 1)‖ *
                  ‖∑ n ∈ Finset.Ico (M - m) M, evalTerm (powCoeff (shiftL wCoeff) (j' + 1)) n v‖)
                ≤ (m.factorial : ℝ) / ‖v‖ ^ m * ‖c (j' + 1)‖ *
                    ∑ n ∈ Finset.Ico (M - m) M, ‖evalTerm (powCoeff (shiftL wCoeff) (j' + 1)) n v‖ := by
                  rw [← mul_assoc]
                  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
              _ = ∑ n ∈ Finset.Ico (M - m) M,
                    (m.factorial : ℝ) / ‖v‖ ^ m * ‖c (j' + 1)‖ *
                      ‖evalTerm (powCoeff (shiftL wCoeff) (j' + 1)) n v‖ := Finset.mul_sum _ _ _
              _ ≤ ∑ n ∈ Finset.Ico (M - m) M,
                    (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ (j' + 1) * (1 / 8 : ℝ) ^ (m + n - M) *
                      (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) :=
                  Finset.sum_le_sum hterm_n
              _ = (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ (j' + 1) *
                    (∑ n ∈ Finset.Ico (M - m) M, (1 / 8 : ℝ) ^ (m + n - M)) *
                    (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by
                  rw [Finset.mul_sum, Finset.sum_mul]
              _ ≤ (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ (j' + 1) * 2 *
                    (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) := by gcongr
        have hgeom_j : ∑ j ∈ Finset.range (M - m), (1 / 2 : ℝ) ^ j ≤ 2 := by
          rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
          have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (M - m) := by positivity
          have hden : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
          rw [hden]; linarith
        calc (m.factorial : ℝ) / ‖v‖ ^ m *
              ‖∑ j ∈ Finset.range (M - m), c j *
                (evalTrunc (powCoeff (shiftL wCoeff) j) M v - evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)‖
            ≤ (m.factorial : ℝ) / ‖v‖ ^ m *
                ∑ j ∈ Finset.range (M - m),
                  ‖c j * (evalTrunc (powCoeff (shiftL wCoeff) j) M v -
                    evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)‖ :=
              mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
          _ = ∑ j ∈ Finset.range (M - m),
                (m.factorial : ℝ) / ‖v‖ ^ m *
                  ‖c j * (evalTrunc (powCoeff (shiftL wCoeff) j) M v -
                    evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)‖ := Finset.mul_sum _ _ _
          _ ≤ ∑ j ∈ Finset.range (M - m),
                (1 / 1000 : ℝ) ^ m * (1 / 2 : ℝ) ^ j * 2 *
                  (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M) :=
              Finset.sum_le_sum htail_j
          _ = (1 / 1000 : ℝ) ^ m * (∑ j ∈ Finset.range (M - m), (1 / 2 : ℝ) ^ j) * 2 *
                (Real.exp Real.pi * ‖v‖ * ((2000 : ℝ) ^ M * (M.factorial : ℝ) / ‖v‖ ^ M)) := by
              rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun _ _ => by ring
          _ ≤ (1 / 1000 : ℝ) ^ m * 2 * 2 *
                (Real.exp Real.pi * ‖v‖ * ((2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) := by gcongr
          _ = (1 / 1000 : ℝ) ^ m * 4 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              ring
      calc _ ≤ ‖((m.factorial : ℂ) / v ^ m) * (((1 + uM)⁻¹ : ℂ) ^ m - ∑ j ∈ Finset.range (M - m), c j * uM ^ j)‖ +
              ‖((m.factorial : ℂ) / v ^ m) *
                ∑ j ∈ Finset.range (M - m), c j * (uM ^ j - evalTrunc (powCoeff (shiftL wCoeff) j) M v)‖ +
              ‖((m.factorial : ℂ) / v ^ m) *
                ∑ j ∈ Finset.range (M - m), c j *
                  (evalTrunc (powCoeff (shiftL wCoeff) j) M v - evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ _ := by linarith [hA, hB, hC]
    -- Sum `hm_bound` over `m ∈ Finset.Ico 1 M`!
    have hcard : (Finset.Ico 1 M).card = N := by simp [M]
    have hgeom_16000 : ∑ m ∈ Finset.Ico 1 M, (1 / 16000 : ℝ) ^ m ≤ 1 := by
      have h1 : ∑ m ∈ Finset.Ico 1 M, (1 / 16000 : ℝ) ^ m =
          (1 / 16000 : ℝ) * ∑ k ∈ Finset.range N, (1 / 16000 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
        · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
        · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨k + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel k 1⟩
        · intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ']
      rw [h1, geom_sum_eq (by norm_num : (1 / 16000 : ℝ) ≠ 1)]
      have : (0 : ℝ) ≤ (1 / 16000 : ℝ) ^ N := by positivity
      have hden : (1 / 16000 : ℝ) - 1 = -(15999 / 16000) := by norm_num
      rw [hden]; linarith
    have hgeom_1000 : ∑ m ∈ Finset.Ico 1 M, (1 / 1000 : ℝ) ^ m ≤ 1 := by
      have h1 : ∑ m ∈ Finset.Ico 1 M, (1 / 1000 : ℝ) ^ m =
          (1 / 1000 : ℝ) * ∑ k ∈ Finset.range N, (1 / 1000 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
        · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
        · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨k + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel k 1⟩
        · intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ']
      rw [h1, geom_sum_eq (by norm_num : (1 / 1000 : ℝ) ≠ 1)]
      have : (0 : ℝ) ≤ (1 / 1000 : ℝ) ^ N := by positivity
      have hden : (1 / 1000 : ℝ) - 1 = -(999 / 1000) := by norm_num
      rw [hden]; linarith
    have hN_pow : (N : ℝ) * (8 : ℝ) ^ N / 32000 ≤ (2000 : ℝ) ^ N := by
      have hNle : (N : ℝ) ≤ (2 : ℝ) ^ N := le_trans (by linarith) (nat_succ_le_two_pow N)
      have h16 : (2 : ℝ) ^ N * (8 : ℝ) ^ N = (16 : ℝ) ^ N := by rw [← mul_pow]; norm_num
      have h16le : (16 : ℝ) ^ N ≤ (2000 : ℝ) ^ N := pow_le_pow_left₀ (by norm_num) (by norm_num) N
      have hnn : (0 : ℝ) ≤ (8 : ℝ) ^ N := by positivity
      nlinarith
    have hE2000_nn : 0 ≤ Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by positivity
    have h2000_A : (2000 : ℝ) ^ N ≤ A_S ^ N := pow_le_pow_left₀ (by norm_num) hA_ge_2000 N
    calc _ ≤ ∑ m ∈ Finset.Ico 1 M,
            ‖(m.factorial : ℂ) / wN ^ m -
              ((m.factorial : ℂ) / v ^ m) *
                ∑ j ∈ Finset.range (M - m),
                  ((-1 : ℂ) ^ j * (((m + j - 1).choose j : ℕ) : ℂ)) *
                    evalTrunc (powCoeff (shiftL wCoeff) j) (M - m) v‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Ico 1 M,
            ((8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N / (32000 : ℝ)) +
            ((1 / 16000 : ℝ) ^ m * 2 + (1 / 1000 : ℝ) ^ m * 4) *
              (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) :=
          Finset.sum_le_sum hm_bound
      _ = (N : ℝ) * (8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N / (32000 : ℝ)) +
            ((∑ m ∈ Finset.Ico 1 M, (1 / 16000 : ℝ) ^ m) * 2 +
              (∑ m ∈ Finset.Ico 1 M, (1 / 1000 : ℝ) ^ m) * 4) *
              (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.sum_mul,
            Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ (8 * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) +
            (1 * 2 + 1 * 4) * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
          have h1 : (N : ℝ) * (8 * Real.exp Real.pi * ‖v‖ * (8 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N / (32000 : ℝ)) =
              ((N : ℝ) * (8 : ℝ) ^ N / 32000) * (8 * Real.exp Real.pi * ‖v‖ * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          have h2 : (8 * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) =
              (2000 : ℝ) ^ N * (8 * Real.exp Real.pi * ‖v‖ * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          rw [h1, h2]
          exact add_le_add (mul_le_mul_of_nonneg_right hN_pow (by positivity))
            (mul_le_mul_of_nonneg_right (by linarith) hE2000_nn)
      _ = (14 * Real.exp Real.pi) * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
      _ ≤ (14 * Real.exp Real.pi) * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by gcongr
  -- Combine Part 1 + Part 2!
  have hcomb : (S_phi wN - 1) - evalTrunc (yCoeff (shiftL wCoeff)) M v =
      ((S_phi wN - 1) - ∑ m ∈ Finset.Ico 1 M, (m.factorial : ℂ) / wN ^ m) +
      (∑ m ∈ Finset.Ico 1 M, (m.factorial : ℂ) / wN ^ m - evalTrunc (yCoeff (shiftL wCoeff)) M v) := by ring
  rw [hcomb]
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ (4 / (Real.sin deltaV * Real.cos phiRay ^ 2)) * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N +
          (14 * Real.exp Real.pi) * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := add_le_add hpart1 hpart2
    _ = C_S * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by dsimp only [C_S]; ring

/-- **Main Gevrey-1 Expansion of `w_plus v - v - log v`** on the wide sector `V_sec`! -/
theorem w_plus_sub_hasGev1Exp :
    HasGev1Exp V_sec (fun v => w_plus v - v - Complex.log v) wCoeff := by
  let A_S : ℝ := max 2000 (2 / Real.cos phiRay)
  let A_log : ℝ := 20000000 * Real.exp Real.pi
  let A_sm : ℝ := 2 * max (2000 * Real.exp 1) (2 * 32000 * Real.exp 1)
  let A : ℝ := max (max A_S A_log) A_sm
  let C_S : ℝ := 4 / (Real.sin deltaV * Real.cos phiRay ^ 2) + 14 * Real.exp Real.pi
  let K_log : ℝ := A_log / 32000
  let C : ℝ := max 1 (2 * (6 * Real.exp Real.pi * K_log + 4 * C_S + Real.exp Real.pi) + Real.exp Real.pi + 1)
  have hA_ge_AS : A_S ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA_ge_Alog : A_log ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA_ge_Asm : A_sm ≤ A := le_max_right _ _
  have hA_ge_2000 : (2000 : ℝ) ≤ A := le_trans (le_max_left _ _) hA_ge_AS
  have hA_pos : 0 < A := lt_of_lt_of_le (by norm_num) hA_ge_2000
  have hC_ge1 : 1 ≤ C := le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge1
  have hCS_pos : 0 < C_S := by
    have := sin_deltaV_pos; have := cos_phiRay_pos; dsimp [C_S]; positivity
  have hKlog_pos : 0 < K_log := by dsimp [K_log, A_log]; positivity
  have hA_ge1 : (1 : ℝ) ≤ A := by linarith
  refine ⟨wCoeff_gevBound.1, C, hC_pos, A, hA_ge1, ?_, ?_⟩
  · -- Coefficient bound from `wCoeff_gevBound`
    intro n k hkn
    have h1 := wCoeff_gevBound.2 n k hkn
    have hsq : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
    have h1' : ‖wCoeff n k‖ ≤ 1 * (2000 : ℝ) ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) :=
      h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))
    calc ‖wCoeff n k‖ ≤ 1 * (2000 : ℝ) ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := h1'
      _ ≤ C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := by gcongr
  · -- Remainder bound for every `N : ℕ` and `v ∈ V_sec`!
    intro N v hv
    have hv_ge : (10 : ℝ) ^ 14 ≤ ‖v‖ := R_sec_ge_1e14.trans hv.1
    have hv1 : 1 ≤ ‖v‖ := by linarith
    have hv_pos : 0 < ‖v‖ := by linarith
    have hv0 : v ≠ 0 := norm_pos_iff.mp hv_pos
    have hv_dom : v ∈ V_dom := V_sec_subset_V_dom hv
    obtain ⟨hw_cb, hw_fix⟩ := w_plus_spec hv_dom
    have hw_bd1 : ‖w_plus v - v - Complex.log v‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw_cb
      have : w_plus v - v - Complex.log v = w_plus v - (v + Complex.log v) := by ring
      rw [this]; exact hw_cb
    -- Handle `N = 0` or small `‖v‖ < 32000 * (N + 1)` first!
    by_cases hcase : N = 0 ∨ ‖v‖ < 32000 * ((N : ℝ) + 1)
    · rcases hcase with rfl | hsmall
      · simp only [evalTrunc, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
          Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
        calc ‖w_plus v - v - Complex.log v‖ ≤ 1 := hw_bd1
          _ ≤ C * ‖v‖ := by nlinarith
      · obtain ⟨h1_sm, hev_sm⟩ := small_v_gev1_bounds (B := 32000) (by norm_num) hv1 hsmall
        have hev := hev_sm zero_le_one wCoeff_gevBound
        have hAsm_le : A_sm ^ N ≤ A ^ N := pow_le_pow_left₀ (by positivity) hA_ge_Asm N
        have h1_A : 1 ≤ A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N :=
          h1_sm.trans (by gcongr)
        have hC_ge : 1 + Real.exp Real.pi ≤ C := by
          have : 2 * (6 * Real.exp Real.pi * K_log + 4 * C_S + Real.exp Real.pi) + Real.exp Real.pi + 1 ≤ C :=
            le_max_right _ _
          have := Real.exp_pos Real.pi
          nlinarith
        calc ‖(w_plus v - v - Complex.log v) - evalTrunc wCoeff N v‖
            ≤ ‖w_plus v - v - Complex.log v‖ + ‖evalTrunc wCoeff N v‖ := norm_sub_le _ _
          _ ≤ 1 + 1 * Real.exp Real.pi * ‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N :=
              add_le_add hw_bd1 hev
          _ ≤ 1 * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) +
                Real.exp Real.pi * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              have h1v : (1 : ℝ) ≤ 1 * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
                nlinarith [h1_A]
              have h2v : 1 * Real.exp Real.pi * ‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N ≤
                  Real.exp Real.pi * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
                calc _ = Real.exp Real.pi * ‖v‖ * (A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
                  _ ≤ Real.exp Real.pi * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
              exact add_le_add h1v h2v
          _ = (1 + Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ C * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
              mul_le_mul_of_nonneg_right hC_ge (by positivity)
          _ = C * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
    · -- Main large-`‖v‖` regime: `N ≥ 1` and `32000 * (N + 1) ≤ ‖v‖`!
      push Not at hcase
      obtain ⟨hN0, hbig'⟩ := hcase
      have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
      have hbig : 32000 * ((N + 1 : ℕ) : ℝ) ≤ ‖v‖ := by push_cast; linarith
      have hbigN : 32000 * (N : ℝ) ≤ ‖v‖ := by linarith
      let wN : ℂ := v + Complex.log v + evalTrunc wCoeff N v
      have hwN_sm : ‖evalTrunc wCoeff N v‖ ≤ 1 / 16 := by
        have h := norm_evalTrunc_small (M := 1) zero_le_one wCoeff_zero wCoeff_gevBound hv hbigN
        linarith
      have hwN_cb : wN ∈ Metric.closedBall (v + Complex.log v) 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have : wN - (v + Complex.log v) = evalTrunc wCoeff N v := by dsimp [wN]; ring
        rw [this]; linarith
      obtain ⟨hwN_mem, _, _, _⟩ := closedBall_log_props hv_dom hwN_cb
      -- Contraction inequality: `‖w_plus v - wN‖ ≤ 2 * ‖T_op v wN - wN‖`!
      have hcontr : ‖w_plus v - wN‖ ≤ 2 * ‖T_op v wN - wN‖ := by
        have hlip := (T_op_contraction hv_dom).2 wN hwN_cb (w_plus v) hw_cb
        have htri : ‖w_plus v - wN‖ ≤ ‖T_op v (w_plus v) - T_op v wN‖ + ‖T_op v wN - wN‖ := by
          have heq : w_plus v - wN = (T_op v (w_plus v) - T_op v wN) + (T_op v wN - wN) := by
            rw [hw_fix]; ring
          rw [heq]; exact norm_add_le _ _
        linarith
      -- Compute `T_op v wN - wN` using `log(v * (1 + uM)) = log v + log(1 + uM)`!
      let uM : ℂ := evalTrunc (shiftL wCoeff) (N + 1) v
      let yM : ℂ := evalTrunc (yCoeff (shiftL wCoeff)) (N + 1) v
      have hsh_gev : GevBound 2000 (1 / 250) (shiftL wCoeff) :=
        (gevBound_phiOp wCoeff_zero wCoeff_gevBound).1
      have hy_gev : GevBound 2000 (1 / 100) (yCoeff (shiftL wCoeff)) :=
        (gevBound_phiOp wCoeff_zero wCoeff_gevBound).2.1
      have huM_eq : uM = (Complex.log v + evalTrunc wCoeff N v) / v := evalTrunc_shiftL_succ hN1 hv0
      have hwN_fac : wN = v * (1 + uM) := by dsimp [wN]; rw [huM_eq]; field_simp [hv0]; ring
      have huM_sm : ‖uM‖ ≤ 1 / 4000 := by
        have h := norm_evalTrunc_small (M := 1 / 250) (by norm_num) (fun _ => rfl) hsh_gev hv hbig
        linarith
      have h1u_ne : 1 + uM ≠ 0 := by
        intro h0
        have : ‖(1 : ℂ)‖ ≤ ‖1 + uM‖ + ‖-uM‖ := by simpa using norm_add_le (1 + uM) (-uM)
        rw [h0, norm_zero, zero_add, norm_neg, norm_one] at this; linarith
      have hlog_add : Complex.log wN = Complex.log v + Complex.log (1 + uM) := by
        rw [hwN_fac]
        have harg_1u : |Complex.arg (1 + uM)| < deltaV := by
          have hsin : |Real.sin (Complex.arg (1 + uM))| ≤ 1 / 2000 := by
            have h1 : ‖1 + uM‖ * |Real.sin (Complex.arg (1 + uM))| = |(1 + uM).im| := by
              rw [← Complex.norm_mul_sin_arg, abs_mul, abs_of_nonneg (norm_nonneg _)]
            have him : |(1 + uM).im| ≤ 1 / 4000 := by
              simpa [Complex.add_im] using (Complex.abs_im_le_norm uM).trans huM_sm
            have hnorm_lo : 1 / 2 ≤ ‖1 + uM‖ := by
              have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans huM_sm)).1
              exact (show (1 / 2 : ℝ) ≤ (1 + uM).re by simp [Complex.add_re]; linarith).trans
                (Complex.re_le_norm _)
            nlinarith [abs_nonneg (Real.sin (Complex.arg (1 + uM)))]
          have hre_pos : 0 < (1 + uM).re := by
            have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans huM_sm)).1
            simp only [Complex.add_re, Complex.one_re]; linarith
          have harg_half : |Complex.arg (1 + uM)| < Real.pi / 2 :=
            Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
          have hsin_abs : Real.sin |Complex.arg (1 + uM)| < Real.sin deltaV := by
            have heq : Real.sin |Complex.arg (1 + uM)| = |Real.sin (Complex.arg (1 + uM))| := by
              rcases le_total 0 (Complex.arg (1 + uM)) with h | h
              · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h
                  (Complex.arg_le_pi _))]
              · rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
                  (le_of_lt (Complex.neg_pi_lt_arg _)))]
            rw [heq]; linarith [sin_deltaV_ge]
          by_contra hge
          push Not at hge
          have hmono := Real.strictMonoOn_sin.monotoneOn
            ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
            ⟨by linarith [abs_nonneg (Complex.arg (1 + uM)), Real.pi_pos], harg_half.le⟩ hge
          linarith
        have hlo : -Real.pi < Complex.arg v + Complex.arg (1 + uM) := by
          have := (abs_lt.mp harg_1u).1; linarith [hv.2.1, deltaV_pos]
        have hhi : Complex.arg v + Complex.arg (1 + uM) ≤ Real.pi := by
          have := (abs_lt.mp harg_1u).2
          have hv2 := hv.2.2; dsimp only [phiRay, deltaV] at hv2 this; linarith [Real.pi_pos]
        exact Complex.log_mul hv0 h1u_ne ⟨hlo, hhi⟩
      -- Exact decomposition of `T_op v wN - wN`!
      have hphi_eq : evalTrunc (log1pCoeff (shiftL wCoeff)) (N + 1) v -
            evalTrunc (log1pCoeff (yCoeff (shiftL wCoeff))) (N + 1) v =
          evalTrunc wCoeff N v + evalTerm wCoeff N v := by
        have h1 : evalTrunc (log1pCoeff (shiftL wCoeff)) (N + 1) v -
              evalTrunc (log1pCoeff (yCoeff (shiftL wCoeff))) (N + 1) v =
            evalTrunc (phiOp wCoeff) (N + 1) v := by
          dsimp only [evalTrunc, evalTerm, phiOp]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← sub_div, ← Finset.sum_sub_distrib]
          congr 1; refine Finset.sum_congr rfl fun k _ => by ring
        have h2 : evalTrunc (phiOp wCoeff) (N + 1) v = evalTrunc wCoeff (N + 1) v := by
          dsimp only [evalTrunc, evalTerm]
          refine Finset.sum_congr rfl fun n _ => ?_
          congr 1; refine Finset.sum_congr rfl fun k _ => by rw [wCoeff_eq_phiOp n k]
        rw [h1, h2]; exact Finset.sum_range_succ _ N
      have hres_eq : T_op v wN - wN =
          (Complex.log (1 + uM) - evalTrunc (log1pCoeff (shiftL wCoeff)) (N + 1) v) -
          (Complex.log (S_phi wN) - Complex.log (1 + yM)) -
          (Complex.log (1 + yM) - evalTrunc (log1pCoeff (yCoeff (shiftL wCoeff))) (N + 1) v) +
          evalTerm wCoeff N v := by
        have hTop : T_op v wN - wN =
            Complex.log (1 + uM) - Complex.log (S_phi wN) - evalTrunc wCoeff N v := by
          dsimp only [T_op, wN]; rw [hlog_add]; ring
        rw [hTop]; linear_combination hphi_eq
      -- Bound each of the 4 terms on the RHS by `... * ‖v‖ * A^N * N! / ‖v‖^N`!
      have hAlog_step : A_log ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖v‖ ^ (N + 1) ≤
          K_log * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hratio : (N + 1 : ℝ) / ‖v‖ ≤ 1 / 32000 := by
          rw [div_le_iff₀ hv_pos]; push_cast at hbig; linarith
        have hrew : A_log ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖v‖ ^ (N + 1) =
            (A_log * ((N + 1 : ℝ) / ‖v‖)) * (A_log ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
          rw [pow_succ, pow_succ, Nat.factorial_succ]; push_cast
          have hne : ‖v‖ ^ N ≠ 0 := by positivity
          field_simp [hne, hv_pos.ne']
        rw [hrew]
        have h1 : A_log * ((N + 1 : ℝ) / ‖v‖) ≤ K_log := by
          dsimp only [K_log]; have hAl_nn : 0 ≤ A_log := by dsimp [A_log]; positivity
          calc A_log * ((N + 1 : ℝ) / ‖v‖) ≤ A_log * (1 / 32000) := mul_le_mul_of_nonneg_left hratio hAl_nn
            _ = A_log / 32000 := by ring
        have h2 : A_log ^ N * (N.factorial : ℝ) / ‖v‖ ^ N ≤ A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by
          have : A_log ^ N ≤ A ^ N := pow_le_pow_left₀ (by dsimp [A_log]; positivity) hA_ge_Alog N
          gcongr
        exact mul_le_mul h1 h2 (by positivity) hKlog_pos.le
      have hT1 : ‖Complex.log (1 + uM) - evalTrunc (log1pCoeff (shiftL wCoeff)) (N + 1) v‖ ≤
          (3 * Real.exp Real.pi * K_log) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have h := norm_clog_one_add_evalTrunc_sub_le (M := 1 / 250) (by norm_num) (by norm_num)
          (fun _ => rfl) hsh_gev (by omega) hv hbig
        calc _ ≤ (3 * Real.exp Real.pi) * ‖v‖ *
              (A_log ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖v‖ ^ (N + 1)) :=
            h.trans (le_of_eq (by dsimp [A_log]; ring))
          _ ≤ (3 * Real.exp Real.pi) * ‖v‖ * (K_log * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) :=
            mul_le_mul_of_nonneg_left hAlog_step (by positivity)
          _ = (3 * Real.exp Real.pi * K_log) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
      have hT3 : ‖Complex.log (1 + yM) - evalTrunc (log1pCoeff (yCoeff (shiftL wCoeff))) (N + 1) v‖ ≤
          (3 * Real.exp Real.pi * K_log) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hy0 : ∀ k, yCoeff (shiftL wCoeff) 0 k = 0 := fun k => by simp [yCoeff]
        have h := norm_clog_one_add_evalTrunc_sub_le (M := 1 / 100) (by norm_num) (by norm_num)
          hy0 hy_gev (by omega) hv hbig
        calc _ ≤ (3 * Real.exp Real.pi) * ‖v‖ *
              (A_log ^ (N + 1) * ((N + 1).factorial : ℝ) / ‖v‖ ^ (N + 1)) :=
            h.trans (le_of_eq (by dsimp [A_log]; ring))
          _ ≤ (3 * Real.exp Real.pi) * ‖v‖ * (K_log * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) :=
            mul_le_mul_of_nonneg_left hAlog_step (by positivity)
          _ = (3 * Real.exp Real.pi * K_log) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
      have hT2 : ‖Complex.log (S_phi wN) - Complex.log (1 + yM)‖ ≤
          (4 * C_S) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hyM_sm : ‖yM‖ ≤ 1 / 1600 := by
          have hy0 : ∀ k, yCoeff (shiftL wCoeff) 0 k = 0 := fun k => by simp [yCoeff]
          have h := norm_evalTrunc_small (M := 1 / 100) (by norm_num) hy0 hy_gev hv hbig
          linarith
        have hSwN_sm : ‖S_phi wN - 1‖ ≤ 1 / 128 := by
          have h1 := norm_S_phi_sub_one_le hwN_mem
          obtain ⟨_, hdw, _, _⟩ := closedBall_log_props hv_dom hwN_cb
          have hden : 128 ≤ distPhi wN * Real.cos phiRay ^ 2 := by
            nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
          exact h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
        have h1y_lo : 1 / 2 ≤ ‖1 + yM‖ := by
          have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hyM_sm)).1
          exact (show (1 / 2 : ℝ) ≤ (1 + yM).re by simp [Complex.add_re]; linarith).trans
            (Complex.re_le_norm _)
        have h1y_ne : 1 + yM ≠ 0 := norm_pos_iff.mp (by linarith)
        have hdiff_le : ‖S_phi wN - (1 + yM)‖ ≤ ‖1 + yM‖ / 2 := by
          have h1 : S_phi wN - (1 + yM) = (S_phi wN - 1) - yM := by ring
          rw [h1]
          have h2 : ‖(S_phi wN - 1) - yM‖ ≤ 1 / 128 + 1 / 1600 :=
            (norm_sub_le _ _).trans (add_le_add hSwN_sm hyM_sm)
          linarith
        have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 + yM) + (t : ℂ) * (S_phi wN - (1 + yM)) ∈ Complex.slitPlane := by
          intro t ht
          left
          have hrew : (1 + yM) + (t : ℂ) * (S_phi wN - (1 + yM)) =
              1 + ((1 - (t : ℂ)) * yM + (t : ℂ) * (S_phi wN - 1)) := by ring
          rw [hrew]
          have hnorm : ‖(1 - (t : ℂ)) * yM + (t : ℂ) * (S_phi wN - 1)‖ ≤ 1 / 4 := by
            have h1t : ‖1 - (t : ℂ)‖ = 1 - t := by
              rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.2])]
            calc _ ≤ ‖(1 - (t : ℂ)) * yM‖ + ‖(t : ℂ) * (S_phi wN - 1)‖ := norm_add_le _ _
              _ = (1 - t) * ‖yM‖ + t * ‖S_phi wN - 1‖ := by
                  rw [norm_mul, norm_mul, h1t, Complex.norm_real, Real.norm_of_nonneg ht.1]
              _ ≤ (1 - t) * (1 / 1600) + t * (1 / 128) := by nlinarith [ht.1, ht.2]
              _ ≤ 1 / 4 := by linarith [ht.1, ht.2]
          have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
          rw [Complex.add_re, Complex.one_re]; linarith
        have hlog_sub := norm_clog_sub_le_of_segment h1y_ne hdiff_le hseg
        have hSy := norm_S_phi_wN_sub_yN_le hN1 hv hbig
        have hSy_eq : S_phi wN - (1 + yM) = (S_phi wN - 1) - yM := by ring
        calc ‖Complex.log (S_phi wN) - Complex.log (1 + yM)‖
            ≤ 2 * ‖S_phi wN - (1 + yM)‖ / ‖1 + yM‖ := hlog_sub
          _ ≤ 2 * ‖S_phi wN - (1 + yM)‖ / (1 / 2) :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) h1y_lo
          _ = 4 * ‖(S_phi wN - 1) - yM‖ := by rw [hSy_eq]; ring
          _ ≤ 4 * (C_S * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
              mul_le_mul_of_nonneg_left hSy (by norm_num)
          _ ≤ 4 * (C_S * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              have : A_S ^ N ≤ A ^ N := pow_le_pow_left₀ (by dsimp [A_S]; positivity) hA_ge_AS N
              gcongr
          _ = (4 * C_S) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
      have hT4 : ‖evalTerm wCoeff N v‖ ≤
          Real.exp Real.pi * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hbase := norm_evalTerm_le (C := 1) (A := 2000) zero_le_one (by norm_num)
          (fun k hkn => (wCoeff_gevBound.2 N k hkn).trans (div_le_div_of_nonneg_left (by positivity)
            (by positivity) (by
              have hN0' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
              have hsq : (1 : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by nlinarith
              nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))) hv1
        have h2000 : (2000 : ℝ) ^ N ≤ A ^ N := pow_le_pow_left₀ (by norm_num) hA_ge_2000 N
        calc ‖evalTerm wCoeff N v‖
            ≤ 1 * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := hbase
          _ ≤ Real.exp Real.pi * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              rw [one_mul]; calc _ = Real.exp Real.pi * (‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
                _ ≤ _ := by gcongr
      have hres_bd : ‖T_op v wN - wN‖ ≤
          (6 * Real.exp Real.pi * K_log + 4 * C_S + Real.exp Real.pi) *
            (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        rw [hres_eq]
        have htri : ‖(Complex.log (1 + uM) - evalTrunc (log1pCoeff (shiftL wCoeff)) (N + 1) v) -
              (Complex.log (S_phi wN) - Complex.log (1 + yM)) -
              (Complex.log (1 + yM) - evalTrunc (log1pCoeff (yCoeff (shiftL wCoeff))) (N + 1) v) +
              evalTerm wCoeff N v‖ ≤
            ‖Complex.log (1 + uM) - evalTrunc (log1pCoeff (shiftL wCoeff)) (N + 1) v‖ +
            ‖Complex.log (S_phi wN) - Complex.log (1 + yM)‖ +
            ‖Complex.log (1 + yM) - evalTrunc (log1pCoeff (yCoeff (shiftL wCoeff))) (N + 1) v‖ +
            ‖evalTerm wCoeff N v‖ :=
          (norm_add_le _ _).trans (add_le_add
            ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
        linarith [htri, hT1, hT2, hT3, hT4]
      have hC_ge : 2 * (6 * Real.exp Real.pi * K_log + 4 * C_S + Real.exp Real.pi) ≤ C := by
        have : 2 * (6 * Real.exp Real.pi * K_log + 4 * C_S + Real.exp Real.pi) + Real.exp Real.pi + 1 ≤ C :=
          le_max_right _ _
        have := Real.exp_pos Real.pi
        linarith
      have hgoal_eq : (w_plus v - v - Complex.log v) - evalTrunc wCoeff N v = w_plus v - wN := by
        dsimp [wN]; ring
      rw [hgoal_eq]
      calc ‖w_plus v - wN‖ ≤ 2 * ‖T_op v wN - wN‖ := hcontr
        _ ≤ 2 * ((6 * Real.exp Real.pi * K_log + 4 * C_S + Real.exp Real.pi) *
              (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) :=
            mul_le_mul_of_nonneg_left hres_bd (by norm_num)
        _ = (2 * (6 * Real.exp Real.pi * K_log + 4 * C_S + Real.exp Real.pi)) *
              (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
        _ ≤ C * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
            mul_le_mul_of_nonneg_right hC_ge (by positivity)
        _ = C * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring

/-- Gevrey-1 expansion of `S_phi (w_plus v) - 1` on `V_sec`! -/
theorem S_phi_w_plus_sub_one_hasGev1Exp :
    HasGev1Exp V_sec (fun v => S_phi (w_plus v) - 1) (yCoeff (shiftL wCoeff)) := by
  obtain ⟨_, Cw, hCw, Aw, hAw, _, hw_rem⟩ := w_plus_sub_hasGev1Exp
  have hy_gev : GevBound 2000 (1 / 100) (yCoeff (shiftL wCoeff)) :=
    (gevBound_phiOp wCoeff_zero wCoeff_gevBound).2.1
  let A_S : ℝ := max 2000 (2 / Real.cos phiRay)
  let A_sm : ℝ := 2 * max (2000 * Real.exp 1) (2 * 32000 * Real.exp 1)
  let A : ℝ := max (max Aw A_S) A_sm
  let C_S : ℝ := 4 / (Real.sin deltaV * Real.cos phiRay ^ 2) + 14 * Real.exp Real.pi
  let C : ℝ := max 1 (Cw + C_S + Real.exp Real.pi + 1)
  have hA_ge_Aw : Aw ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA_ge_AS : A_S ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA_ge_Asm : A_sm ≤ A := le_max_right _ _
  have hA_ge_2000 : (2000 : ℝ) ≤ A := le_trans (le_max_left _ _) hA_ge_AS
  have hA_ge1 : (1 : ℝ) ≤ A := by linarith
  have hC_ge1 : 1 ≤ C := le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge1
  have hCS_pos : 0 < C_S := by
    have := sin_deltaV_pos; have := cos_phiRay_pos; dsimp [C_S]; positivity
  refine ⟨hy_gev.1, C, hC_pos, A, hA_ge1, ?_, ?_⟩
  · intro n k hkn
    have h1 := hy_gev.2 n k hkn
    have hsq : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
    have h1' : ‖yCoeff (shiftL wCoeff) n k‖ ≤ (1 / 100 : ℝ) * (2000 : ℝ) ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) :=
      h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))
    calc _ ≤ (1 / 100 : ℝ) * (2000 : ℝ) ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := h1'
      _ ≤ C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := by
          have : (1 / 100 : ℝ) ≤ C := by linarith
          gcongr
  · intro N v hv
    have hv_ge : (10 : ℝ) ^ 14 ≤ ‖v‖ := R_sec_ge_1e14.trans hv.1
    have hv1 : 1 ≤ ‖v‖ := by linarith
    have hv_pos : 0 < ‖v‖ := by linarith
    have hv_dom : v ∈ V_dom := V_sec_subset_V_dom hv
    obtain ⟨hw_cb, _⟩ := w_plus_spec hv_dom
    obtain ⟨hw_mem, hdw, _, _⟩ := closedBall_log_props hv_dom hw_cb
    have hSw_bd : ‖S_phi (w_plus v) - 1‖ ≤ 1 / 128 := by
      have h1 := norm_S_phi_sub_one_le hw_mem
      have hden : 128 ≤ distPhi (w_plus v) * Real.cos phiRay ^ 2 := by
        nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
      exact h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
    by_cases hcase : N = 0 ∨ ‖v‖ < 32000 * ((N : ℝ) + 1)
    · rcases hcase with rfl | hsmall
      · simp only [evalTrunc, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
          Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
        calc ‖S_phi (w_plus v) - 1‖ ≤ 1 / 128 := hSw_bd
          _ ≤ C * ‖v‖ := by nlinarith
      · obtain ⟨h1_sm, hev_sm⟩ := small_v_gev1_bounds (B := 32000) (by norm_num) hv1 hsmall
        have hev := hev_sm (by norm_num) hy_gev
        have hAsm_le : A_sm ^ N ≤ A ^ N := pow_le_pow_left₀ (by positivity) hA_ge_Asm N
        have h1_A : 1 ≤ A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := h1_sm.trans (by gcongr)
        have hC_ge : 1 + Real.exp Real.pi ≤ C := by
          have : Cw + C_S + Real.exp Real.pi + 1 ≤ C := le_max_right _ _
          linarith
        calc ‖(S_phi (w_plus v) - 1) - evalTrunc (yCoeff (shiftL wCoeff)) N v‖
            ≤ ‖S_phi (w_plus v) - 1‖ + ‖evalTrunc (yCoeff (shiftL wCoeff)) N v‖ := norm_sub_le _ _
          _ ≤ 1 + (1 / 100 : ℝ) * Real.exp Real.pi * ‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N :=
              add_le_add (hSw_bd.trans (by norm_num)) hev
          _ ≤ 1 * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) +
                Real.exp Real.pi * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              have h1v : (1 : ℝ) ≤ 1 * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
                have h2 : 1 * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) =
                    ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
                rw [h2]; nlinarith
              have h2v : (1 / 100 : ℝ) * Real.exp Real.pi * ‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N ≤
                  Real.exp Real.pi * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
                have h3 : (1 / 100 : ℝ) * Real.exp Real.pi * ‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N =
                    (1 / 100 : ℝ) * (Real.exp Real.pi * (‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) := by ring
                rw [h3]
                have hnn : 0 ≤ Real.exp Real.pi * (‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by positivity
                calc _ ≤ 1 * (Real.exp Real.pi * (‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N)) := by nlinarith
                  _ = Real.exp Real.pi * ‖v‖ * (A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
                  _ ≤ Real.exp Real.pi * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
                  _ = Real.exp Real.pi * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
              exact add_le_add h1v h2v
          _ = (1 + Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ C * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
              mul_le_mul_of_nonneg_right hC_ge (by positivity)
          _ = C * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
    · push Not at hcase
      obtain ⟨hN0, hbig'⟩ := hcase
      have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
      have hbig : 32000 * ((N + 1 : ℕ) : ℝ) ≤ ‖v‖ := by push_cast; linarith
      have hbigN : 32000 * (N : ℝ) ≤ ‖v‖ := by linarith
      let wN : ℂ := v + Complex.log v + evalTrunc wCoeff N v
      have hwN_sm : ‖evalTrunc wCoeff N v‖ ≤ 1 / 16 := by
        have h := norm_evalTrunc_small (M := 1) zero_le_one wCoeff_zero wCoeff_gevBound hv hbigN
        linarith
      have hwN_cb : wN ∈ Metric.closedBall (v + Complex.log v) 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have : wN - (v + Complex.log v) = evalTrunc wCoeff N v := by dsimp [wN]; ring
        rw [this]; linarith
      -- Lipschitz bound `‖S_phi (w_plus v) - S_phi wN‖ ≤ ‖w_plus v - wN‖` along the segment in `closedBall (v + log v) 1`!
      have hS_lip : ‖S_phi (w_plus v) - S_phi wN‖ ≤ ‖w_plus v - wN‖ := by
        let seg : ℝ → ℂ := fun t => wN + (t : ℂ) * (w_plus v - wN)
        have hseg_cb : ∀ t ∈ Set.Icc (0 : ℝ) 1, seg t ∈ Metric.closedBall (v + Complex.log v) 1 := by
          intro t ht
          have hconv := convex_closedBall (v + Complex.log v) (1 : ℝ)
          have hmem := hconv hwN_cb hw_cb (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
          have heq : (1 - t) • wN + t • w_plus v = seg t := by
            simp only [Complex.real_smul, seg]; push_cast; ring
          rwa [heq] at hmem
        have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
            HasDerivAt (fun τ : ℝ => S_phi (seg τ)) (deriv S_phi (seg t) * (w_plus v - wN)) t := by
          intro t ht
          rw [Set.uIcc_of_le zero_le_one] at ht
          have hmem := (closedBall_log_props hv_dom (hseg_cb t ht)).1
          have hlin : HasDerivAt seg (w_plus v - wN) t := by
            simpa [seg] using ((hasDerivAt_id t).ofReal_comp.mul_const (w_plus v - wN)).const_add wN
          have hSd := (differentiableOn_S_phi.differentiableAt (isOpen_OmegaPhi.mem_nhds hmem)).hasDerivAt
          exact hSd.comp t hlin
        have hcont : ContinuousOn (fun t : ℝ => deriv S_phi (seg t) * (w_plus v - wN)) (Set.uIcc (0 : ℝ) 1) := by
          have hdiff : DifferentiableOn ℂ (deriv S_phi) OmegaPhi :=
            (differentiableOn_S_phi.deriv isOpen_OmegaPhi)
          have hcont_S' : ContinuousOn (deriv S_phi) OmegaPhi := hdiff.continuousOn
          have hseg_cont : ContinuousOn seg (Set.uIcc (0 : ℝ) 1) :=
            (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
          have hmaps : Set.MapsTo seg (Set.uIcc (0 : ℝ) 1) OmegaPhi := by
            intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht
            exact (closedBall_log_props hv_dom (hseg_cb t ht)).1
          exact (hcont_S'.comp hseg_cont hmaps).mul continuousOn_const
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
        have hs0 : seg 0 = wN := by simp [seg]
        have hs1 : seg 1 = w_plus v := by simp [seg]
        rw [hs1, hs0] at hftc
        rw [← hftc]
        have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖deriv S_phi (seg t) * (w_plus v - wN)‖ ≤ ‖w_plus v - wN‖ := by
          intro t ht
          rw [Set.uIoc_of_le zero_le_one] at ht
          obtain ⟨hmem, hdw_t, _, _⟩ := closedBall_log_props hv_dom (hseg_cb t ⟨ht.1.le, ht.2⟩)
          have hS' := norm_deriv_S_phi_le hmem
          have hden : 16 ≤ distPhi (seg t) * Real.cos phiRay ^ 2 := by
            nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
          have hS'_le : ‖deriv S_phi (seg t)‖ ≤ 1 := by
            have h1 : 4 ≤ distPhi (seg t) ^ 2 * Real.cos phiRay ^ 2 := by
              have hd_ge : 1 ≤ distPhi (seg t) := by linarith [C_v_ge_256]
              nlinarith [pow_pos cos_phiRay_pos 2]
            exact hS'.trans ((div_le_one (by nlinarith [pow_pos cos_phiRay_pos 2])).mpr h1)
          rw [norm_mul]
          calc ‖deriv S_phi (seg t)‖ * ‖w_plus v - wN‖ ≤ 1 * ‖w_plus v - wN‖ :=
                mul_le_mul_of_nonneg_right hS'_le (norm_nonneg _)
            _ = ‖w_plus v - wN‖ := one_mul _
        simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd
      have hsplit : (S_phi (w_plus v) - 1) - evalTrunc (yCoeff (shiftL wCoeff)) N v =
          (S_phi (w_plus v) - S_phi wN) +
          ((S_phi wN - 1) - evalTrunc (yCoeff (shiftL wCoeff)) (N + 1) v) +
          evalTerm (yCoeff (shiftL wCoeff)) N v := by
        have hsucc : evalTrunc (yCoeff (shiftL wCoeff)) (N + 1) v =
            evalTrunc (yCoeff (shiftL wCoeff)) N v + evalTerm (yCoeff (shiftL wCoeff)) N v :=
          Finset.sum_range_succ _ N
        linear_combination hsucc
      rw [hsplit]
      have hb1 : ‖S_phi (w_plus v) - S_phi wN‖ ≤ Cw * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hwN_eq : w_plus v - wN = (w_plus v - v - Complex.log v) - evalTrunc wCoeff N v := by
          dsimp [wN]; ring
        have h1 := hw_rem N v hv
        rw [← hwN_eq] at h1
        have hAwA : Aw ^ N ≤ A ^ N := pow_le_pow_left₀ (by linarith) hA_ge_Aw N
        calc ‖S_phi (w_plus v) - S_phi wN‖ ≤ ‖w_plus v - wN‖ := hS_lip
          _ ≤ Cw * ‖v‖ * Aw ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := h1
          _ = Cw * (‖v‖ * Aw ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ Cw * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
      have hb2 : ‖(S_phi wN - 1) - evalTrunc (yCoeff (shiftL wCoeff)) (N + 1) v‖ ≤
          C_S * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have h := norm_S_phi_wN_sub_yN_le hN1 hv hbig
        have hASA : A_S ^ N ≤ A ^ N := pow_le_pow_left₀ (by dsimp [A_S]; positivity) hA_ge_AS N
        calc _ ≤ C_S * ‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := h
          _ = C_S * (‖v‖ * A_S ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ C_S * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
      have hb3 : ‖evalTerm (yCoeff (shiftL wCoeff)) N v‖ ≤
          Real.exp Real.pi * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hcoef_y : ∀ k ≤ N, ‖yCoeff (shiftL wCoeff) N k‖ ≤
            1 * (2000 : ℝ) ^ N * (N.factorial : ℝ) / (k.factorial : ℝ) := by
          intro k hkn
          have hsq : (1 : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith
          calc ‖yCoeff (shiftL wCoeff) N k‖
              ≤ (1 / 100 : ℝ) * (2000 : ℝ) ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (k.factorial : ℝ)) :=
                hy_gev.2 N k hkn
            _ ≤ (1 / 100 : ℝ) * (2000 : ℝ) ^ N * (N.factorial : ℝ) / (k.factorial : ℝ) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity)
                  (by nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity])
            _ ≤ 1 * (2000 : ℝ) ^ N * (N.factorial : ℝ) / (k.factorial : ℝ) := by
                have : (1 / 100 : ℝ) ≤ 1 := by norm_num
                gcongr
        have hbase := norm_evalTerm_le (C := 1) (A := 2000) zero_le_one (by norm_num) hcoef_y hv1
        have h2000A : (2000 : ℝ) ^ N ≤ A ^ N := pow_le_pow_left₀ (by norm_num) hA_ge_2000 N
        calc _ ≤ 1 * Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := hbase
          _ = Real.exp Real.pi * (‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ Real.exp Real.pi * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
      have hC_ge : Cw + C_S + Real.exp Real.pi ≤ C := by
        have : Cw + C_S + Real.exp Real.pi + 1 ≤ C := le_max_right _ _
        linarith
      calc _ ≤ ‖S_phi (w_plus v) - S_phi wN‖ +
            ‖(S_phi wN - 1) - evalTrunc (yCoeff (shiftL wCoeff)) (N + 1) v‖ +
            ‖evalTerm (yCoeff (shiftL wCoeff)) N v‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (Cw + C_S + Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
            linarith [hb1, hb2, hb3]
        _ ≤ C * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
            mul_le_mul_of_nonneg_right hC_ge (by positivity)
        _ = C * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring

/-- Gevrey-1 expansion of `(S_phi (w_plus v))⁻¹` on `V_sec`! -/
theorem inv_S_phi_w_plus_hasGev1Exp :
    HasGev1Exp V_sec (fun v => (S_phi (w_plus v))⁻¹) (negPowCoeff 1 (yCoeff (shiftL wCoeff))) := by
  let yC : LogCoeff := yCoeff (shiftL wCoeff)
  let bC : LogCoeff := negPowCoeff 1 yC
  have hy0 : ∀ k, yC 0 k = 0 := fun k => by simp [yC, yCoeff]
  have hy_gev : GevBound 2000 (1 / 100) yC := (gevBound_phiOp wCoeff_zero wCoeff_gevBound).2.1
  obtain ⟨_, Cy, hCy, Ay, hAy, _, hy_rem⟩ := S_phi_w_plus_sub_one_hasGev1Exp
  -- First prove `GevBound 2000 2 bC`!
  have hb_gev : GevBound 2000 2 bC := by
    refine ⟨fun N K hNK => ?_, fun N K hKN => ?_⟩
    · dsimp only [bC, negPowCoeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h0 : powCoeff yC j N K = 0 := by
        cases j with
        | zero => simp [powCoeff, constCoeff]; intro h1; omega
        | succ j' => exact (gevBound_powCoeff (by norm_num) (by norm_num) hy_gev (j' + 1)
            (Nat.succ_pos j')).1 N K hNK
      rw [h0, mul_zero]
    · dsimp only [bC, negPowCoeff]
      have hterm : ∀ j ∈ Finset.range (N + 1),
          ‖((-1 : ℂ) ^ j * (((1 + j - 1).choose j : ℕ) : ℂ)) * powCoeff yC j N K‖ ≤
            (1 / 2 : ℝ) ^ j * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
        intro j _
        rw [show 1 + j - 1 = j by omega, Nat.choose_self, Nat.cast_one, mul_one,
          norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        cases j with
        | zero =>
          have h0 := gevBound_constCoeff_one (by norm_num : (0 : ℝ) ≤ 2000)
          simpa [powCoeff] using h0.2 N K hKN
        | succ j' =>
          have hpg := (gevBound_powCoeff (by norm_num) (by norm_num) hy_gev (j' + 1)
            (Nat.succ_pos j')).2 N K hKN
          have hle : (16 * (1 / 100 : ℝ)) ^ (j' + 1) / 16 ≤ (1 / 2 : ℝ) ^ (j' + 1) := by
            have h1 : (16 * (1 / 100 : ℝ)) ^ (j' + 1) ≤ (1 / 2 : ℝ) ^ (j' + 1) :=
              pow_le_pow_left₀ (by norm_num) (by norm_num) _
            have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j' + 1) := by positivity
            linarith
          calc ‖powCoeff yC (j' + 1) N K‖
              ≤ ((16 * (1 / 100 : ℝ)) ^ (j' + 1) / 16) *
                  (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
                hpg.trans (le_of_eq (by ring))
            _ ≤ (1 / 2 : ℝ) ^ (j' + 1) *
                  (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
                mul_le_mul_of_nonneg_right hle (by positivity)
      have hgeom : ∑ j ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ j ≤ 2 := by
        rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
        have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (N + 1) := by positivity
        have hden : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
        rw [hden]; linarith
      calc ‖∑ j ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ j * (((1 + j - 1).choose j : ℕ) : ℂ)) * powCoeff yC j N K‖
          ≤ ∑ j ∈ Finset.range (N + 1),
              ‖((-1 : ℂ) ^ j * (((1 + j - 1).choose j : ℕ) : ℂ)) * powCoeff yC j N K‖ := norm_sum_le _ _
        _ ≤ (∑ j ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ j) *
              (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) := by
            rw [Finset.sum_mul]; exact Finset.sum_le_sum hterm
        _ ≤ 2 * (2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ))) :=
            mul_le_mul_of_nonneg_right hgeom (by positivity)
        _ = 2 * 2000 ^ N * (N.factorial : ℝ) / (((N + 1 : ℝ) ^ 2) * (K.factorial : ℝ)) := by ring
  let A_log4 : ℝ := 4 * (20000000 * Real.exp Real.pi)
  let A_sm : ℝ := 2 * max (2000 * Real.exp 1) (2 * 32000 * Real.exp 1)
  let A : ℝ := max (max Ay A_log4) A_sm
  let C : ℝ := max 2 (4 * Cy + 6 * Real.exp Real.pi + 2 * Real.exp Real.pi + 2)
  have hA_ge_Ay : Ay ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA_ge_Alog4 : A_log4 ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA_ge_Asm : A_sm ≤ A := le_max_right _ _
  have hA_ge_2000 : (2000 : ℝ) ≤ A := by
    have h1 : (2000 : ℝ) ≤ A_log4 := by
      have := Real.one_le_exp Real.pi_pos.le; dsimp [A_log4]; nlinarith
    exact h1.trans hA_ge_Alog4
  have hA_ge1 : (1 : ℝ) ≤ A := by linarith
  have hC_ge2 : 2 ≤ C := le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) hC_ge2
  refine ⟨hb_gev.1, C, hC_pos, A, hA_ge1, ?_, ?_⟩
  · intro n k hkn
    have h1 := hb_gev.2 n k hkn
    have hsq : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
    have h1' : ‖bC n k‖ ≤ 2 * (2000 : ℝ) ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) :=
      h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [show (0 : ℝ) < (k.factorial : ℝ) by positivity]))
    calc _ ≤ 2 * (2000 : ℝ) ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := h1'
      _ ≤ C * A ^ n * (n.factorial : ℝ) / (k.factorial : ℝ) := by gcongr
  · intro N v hv
    have hv_ge : (10 : ℝ) ^ 14 ≤ ‖v‖ := R_sec_ge_1e14.trans hv.1
    have hv1 : 1 ≤ ‖v‖ := by linarith
    have hv_pos : 0 < ‖v‖ := by linarith
    have hv_dom : v ∈ V_dom := V_sec_subset_V_dom hv
    obtain ⟨hw_cb, _⟩ := w_plus_spec hv_dom
    obtain ⟨hw_mem, hdw, _, _⟩ := closedBall_log_props hv_dom hw_cb
    have hSw_sm : ‖S_phi (w_plus v) - 1‖ ≤ 1 / 128 := by
      have h1 := norm_S_phi_sub_one_le hw_mem
      have hden : 128 ≤ distPhi (w_plus v) * Real.cos phiRay ^ 2 := by
        nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
      exact h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
    have hSw_lo : 1 / 2 ≤ ‖S_phi (w_plus v)‖ := by
      have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hSw_sm)).1
      exact (show (1 / 2 : ℝ) ≤ (S_phi (w_plus v)).re by simp [Complex.sub_re] at hre; linarith).trans
        (Complex.re_le_norm _)
    have hinv_bd : ‖(S_phi (w_plus v))⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hSw_lo
      linarith
    by_cases hcase : N = 0 ∨ ‖v‖ < 32000 * ((N : ℝ) + 1)
    · rcases hcase with rfl | hsmall
      · simp only [evalTrunc, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
          Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
        calc ‖(S_phi (w_plus v))⁻¹‖ ≤ 2 := hinv_bd
          _ ≤ C * ‖v‖ := by nlinarith
      · obtain ⟨h1_sm, hev_sm⟩ := small_v_gev1_bounds (B := 32000) (by norm_num) hv1 hsmall
        have hev := hev_sm (by norm_num) hb_gev
        have hAsm_le : A_sm ^ N ≤ A ^ N := pow_le_pow_left₀ (by positivity) hA_ge_Asm N
        have h1_A : 1 ≤ A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := h1_sm.trans (by gcongr)
        have hC_ge : 2 + 2 * Real.exp Real.pi ≤ C := by
          have : 4 * Cy + 6 * Real.exp Real.pi + 2 * Real.exp Real.pi + 2 ≤ C := le_max_right _ _
          have := Real.exp_pos Real.pi
          linarith
        calc ‖(S_phi (w_plus v))⁻¹ - evalTrunc bC N v‖
            ≤ ‖(S_phi (w_plus v))⁻¹‖ + ‖evalTrunc bC N v‖ := norm_sub_le _ _
          _ ≤ 2 + 2 * Real.exp Real.pi * ‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N :=
              add_le_add hinv_bd hev
          _ ≤ 2 * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) +
                (2 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              have h1v : (2 : ℝ) ≤ 2 * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
                have h2 : 2 * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) =
                    2 * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
                rw [h2]; nlinarith
              have h2v : 2 * Real.exp Real.pi * ‖v‖ * A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N ≤
                  (2 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
                calc _ = 2 * Real.exp Real.pi * ‖v‖ * (A_sm ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
                  _ ≤ 2 * Real.exp Real.pi * ‖v‖ * (A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
                  _ = _ := by ring
              exact add_le_add h1v h2v
          _ = (2 + 2 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ C * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
              mul_le_mul_of_nonneg_right hC_ge (by positivity)
          _ = C * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring
    · push Not at hcase
      obtain ⟨hN0, hbig'⟩ := hcase
      have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
      have hbigN : 32000 * (N : ℝ) ≤ ‖v‖ := by linarith
      let yN : ℂ := evalTrunc yC N v
      have hyN_sm : ‖yN‖ ≤ 1 / 4 := by
        have h := norm_evalTrunc_small (M := 1 / 100) (by norm_num) hy0 hy_gev hv hbigN
        linarith
      have hyN_log : ‖yN‖ ≤ (20000000 * Real.exp Real.pi) * ‖Complex.log v‖ / ‖v‖ :=
        norm_evalTrunc_le_const_log_div (by norm_num) (by norm_num) hy0 hy_gev hv hbigN
      have h1yN_lo : 1 / 2 ≤ ‖1 + yN‖ := by
        have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hyN_sm)).1
        exact (show (1 / 2 : ℝ) ≤ (1 + yN).re by simp [Complex.add_re]; linarith).trans
          (Complex.re_le_norm _)
      have h1yN_ne : 1 + yN ≠ 0 := norm_pos_iff.mp (by linarith)
      have hSw_ne : S_phi (w_plus v) ≠ 0 := norm_pos_iff.mp (by linarith)
      -- Rewrite `evalTrunc bC N v = ∑ j ∈ range N, (-1)^j * evalTrunc (powCoeff yC j) N v`!
      have hb_eq : evalTrunc bC N v =
          ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * evalTrunc (powCoeff yC j) N v := by
        dsimp only [evalTrunc, evalTerm, bC, negPowCoeff]
        have hterm_n : ∀ n ∈ Finset.range N,
            (∑ K ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (n + 1),
                ((-1 : ℂ) ^ j * (((1 + j - 1).choose j : ℕ) : ℂ)) * powCoeff yC j n K) *
                  Complex.log v ^ K) / v ^ n =
            ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j *
              ((∑ K ∈ Finset.range (n + 1), powCoeff yC j n K * Complex.log v ^ K) / v ^ n) := by
          intro n hn
          have hnN : n < N := Finset.mem_range.mp hn
          have hsub : ∀ K,
              ∑ j ∈ Finset.range (n + 1),
                ((-1 : ℂ) ^ j * (((1 + j - 1).choose j : ℕ) : ℂ)) * powCoeff yC j n K =
              ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * powCoeff yC j n K := by
            intro K
            have hsimp : ∑ j ∈ Finset.range (n + 1),
                ((-1 : ℂ) ^ j * (((1 + j - 1).choose j : ℕ) : ℂ)) * powCoeff yC j n K =
                ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * powCoeff yC j n K :=
              Finset.sum_congr rfl fun j _ => by
                rw [show 1 + j - 1 = j by omega, Nat.choose_self, Nat.cast_one, mul_one]
            rw [hsimp]
            refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
            intro j hj hnot
            simp only [Finset.mem_range] at hj hnot
            rw [powCoeff_zero_lt hy0 j n K (by omega : n < j), mul_zero]
          simp_rw [hsub, Finset.sum_mul]
          rw [Finset.sum_comm, Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => by
            simp_rw [mul_assoc]; rw [← Finset.mul_sum, mul_div_assoc]
        rw [Finset.sum_congr rfl hterm_n, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
      have hsplit : (S_phi (w_plus v))⁻¹ - evalTrunc bC N v =
          ((S_phi (w_plus v))⁻¹ - (1 + yN)⁻¹) +
          ((1 + yN)⁻¹ - ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * yN ^ j) +
          ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (yN ^ j - evalTrunc (powCoeff yC j) N v) := by
        rw [hb_eq]
        have h1 : ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (yN ^ j - evalTrunc (powCoeff yC j) N v) =
            ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * yN ^ j -
            ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * evalTrunc (powCoeff yC j) N v := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
        rw [h1]; ring
      rw [hsplit]
      -- Bound the 3 pieces!
      have hb1 : ‖(S_phi (w_plus v))⁻¹ - (1 + yN)⁻¹‖ ≤
          (4 * Cy) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hsub : (S_phi (w_plus v))⁻¹ - (1 + yN)⁻¹ =
            -((S_phi (w_plus v) - 1) - yN) / (S_phi (w_plus v) * (1 + yN)) := by
          field_simp [hSw_ne, h1yN_ne]; ring
        rw [hsub, norm_div, norm_neg, norm_mul]
        have hden : 1 / 4 ≤ ‖S_phi (w_plus v)‖ * ‖1 + yN‖ := by nlinarith
        have hyr := hy_rem N v hv
        have hAyA : Ay ^ N ≤ A ^ N := pow_le_pow_left₀ (by linarith) hA_ge_Ay N
        calc ‖(S_phi (w_plus v) - 1) - yN‖ / (‖S_phi (w_plus v)‖ * ‖1 + yN‖)
            ≤ ‖(S_phi (w_plus v) - 1) - yN‖ / (1 / 4) :=
              div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
          _ = 4 * ‖(S_phi (w_plus v) - 1) - yN‖ := by ring
          _ ≤ 4 * (Cy * ‖v‖ * Ay ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
              mul_le_mul_of_nonneg_left hyr (by norm_num)
          _ = (4 * Cy) * (‖v‖ * Ay ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ (4 * Cy) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
      have hb2 : ‖(1 + yN)⁻¹ - ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * yN ^ j‖ ≤
          (4 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have htay := norm_inv_one_add_pow_sub_sum_le_four (M := N) (m := 1) le_rfl hyN_sm
        simp only [pow_one] at htay
        have hsum_eq : ∑ j ∈ Finset.range N, ((-1 : ℂ) ^ j * (((1 + j - 1).choose j : ℕ) : ℂ)) * yN ^ j =
            ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * yN ^ j :=
          Finset.sum_congr rfl fun j _ => by
            rw [show 1 + j - 1 = j by omega, Nat.choose_self, Nat.cast_one, mul_one]
        rw [hsum_eq] at htay
        have hlogN : ‖Complex.log v‖ ^ N ≤ Real.exp Real.pi * ‖v‖ * (N.factorial : ℝ) := by
          have h := (Real.pow_div_factorial_le_exp ‖Complex.log v‖ (norm_nonneg _) N).trans
            (exp_norm_log_le hv1)
          rwa [div_le_iff₀ (by positivity)] at h
        have hAlog4A : A_log4 ^ N ≤ A ^ N :=
          pow_le_pow_left₀ (by dsimp [A_log4]; positivity) hA_ge_Alog4 N
        calc _ ≤ (4 : ℝ) ^ (1 + N) * ‖yN‖ ^ N := htay
          _ ≤ (4 : ℝ) ^ (1 + N) * ((20000000 * Real.exp Real.pi) * ‖Complex.log v‖ / ‖v‖) ^ N := by gcongr
          _ = 4 * A_log4 ^ N * ‖Complex.log v‖ ^ N / ‖v‖ ^ N := by
              dsimp only [A_log4]; rw [pow_add, pow_one, div_pow, mul_pow, mul_pow, mul_pow]; ring
          _ ≤ 4 * A_log4 ^ N * (Real.exp Real.pi * ‖v‖ * (N.factorial : ℝ)) / ‖v‖ ^ N := by gcongr
          _ = (4 * Real.exp Real.pi) * (‖v‖ * A_log4 ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ (4 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
      have hb3 : ‖∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (yN ^ j - evalTrunc (powCoeff yC j) N v)‖ ≤
          (2 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
        have hterm : ∀ j ∈ Finset.range N,
            ‖(-1 : ℂ) ^ j * (yN ^ j - evalTrunc (powCoeff yC j) N v)‖ ≤
              (1 / 4 : ℝ) ^ j * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
          intro j _
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact (norm_pow_sub_evalTrunc_powCoeff (M := 1 / 100) (by norm_num) (by norm_num)
            hy0 hy_gev hN1 hv hbigN j).trans (le_of_eq (by ring))
        have hgeom : ∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j ≤ 2 := by
          rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
          have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ N := by positivity
          have hden : (1 / 4 : ℝ) - 1 = -(3 / 4) := by norm_num
          rw [hden]; linarith
        have h2000A : (2000 : ℝ) ^ N ≤ A ^ N := pow_le_pow_left₀ (by norm_num) hA_ge_2000 N
        calc _ ≤ ∑ j ∈ Finset.range N, ‖(-1 : ℂ) ^ j * (yN ^ j - evalTrunc (powCoeff yC j) N v)‖ := norm_sum_le _ _
          _ ≤ (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j) *
                (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
              rw [Finset.sum_mul]; exact Finset.sum_le_sum hterm
          _ ≤ 2 * (Real.exp Real.pi * ‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
              mul_le_mul_of_nonneg_right hgeom (by positivity)
          _ = (2 * Real.exp Real.pi) * (‖v‖ * (2000 : ℝ) ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by ring
          _ ≤ (2 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by gcongr
      have hC_ge : 4 * Cy + 6 * Real.exp Real.pi ≤ C := by
        have : 4 * Cy + 6 * Real.exp Real.pi + 2 * Real.exp Real.pi + 2 ≤ C := le_max_right _ _
        have := Real.exp_pos Real.pi
        linarith
      calc _ ≤ ‖(S_phi (w_plus v))⁻¹ - (1 + yN)⁻¹‖ +
            ‖(1 + yN)⁻¹ - ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * yN ^ j‖ +
            ‖∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (yN ^ j - evalTrunc (powCoeff yC j) N v)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (4 * Cy + 6 * Real.exp Real.pi) * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) := by
            linarith [hb1, hb2, hb3]
        _ ≤ C * (‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N) :=
            mul_le_mul_of_nonneg_right hC_ge (by positivity)
        _ = C * ‖v‖ * A ^ N * (N.factorial : ℝ) / ‖v‖ ^ N := by ring

/-- **Main Section 3 Export**: `F_plus v / v` has a uniform Gevrey-1 log-power expansion on `V_sec`! -/
theorem F_plus_div_hasGev1Exp :
    ∃ a_F : LogCoeff, HasGev1Exp V_sec (fun v => F_plus v / v) a_F := by
  have hS1 : ∀ v ∈ V_sec, (1 : ℝ) ≤ ‖v‖ := fun v hv => by linarith [R_sec_ge_1e14.trans hv.1]
  -- 1. `HasGev1Exp V_sec (fun v => Complex.log v / v)`
  let logDivC : LogCoeff := fun n k => if n = 1 ∧ k = 1 then 1 else 0
  have hlogDiv : HasGev1Exp V_sec (fun v => Complex.log v / v) logDivC := by
    refine ⟨?_, Real.exp Real.pi, Real.exp_pos Real.pi, 1, le_rfl, ?_, ?_⟩
    · intro n k hnk; dsimp [logDivC]; split_ifs with h <;> [omega; rfl]
    · intro n k _
      dsimp only [logDivC]
      split_ifs with h
      · rcases h with ⟨rfl, rfl⟩; simp [Real.one_le_exp Real.pi_pos.le]
      · simp; positivity
    · intro N v hv
      have hv1 : 1 ≤ ‖v‖ := hS1 v hv
      have hv_pos : 0 < ‖v‖ := by linarith
      have hlog_le : ‖Complex.log v‖ ≤ Real.exp Real.pi * ‖v‖ := by
        have h := (Real.pow_div_factorial_le_exp ‖Complex.log v‖ (norm_nonneg _) 1).trans
          (exp_norm_log_le hv1)
        simpa using h
      cases N with
      | zero =>
        simp only [evalTrunc, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
          Nat.factorial_zero, Nat.cast_one, mul_one, div_one, norm_div]
        have h1 : ‖Complex.log v‖ / ‖v‖ ≤ Real.exp Real.pi := by
          rw [div_le_iff₀ hv_pos]; exact hlog_le
        have : Real.exp Real.pi ≤ Real.exp Real.pi * ‖v‖ := by
          have := Real.exp_pos Real.pi; nlinarith
        linarith
      | succ N' =>
        cases N' with
        | zero =>
          simp only [evalTrunc, evalTerm, logDivC, zero_add, Finset.range_one, Finset.sum_singleton,
            show ¬ (0 = 1 ∧ 0 = 1) by omega, ↓reduceIte, zero_mul, zero_div, sub_zero,
            pow_one, Nat.factorial_one, Nat.cast_one, mul_one, norm_div]
          exact div_le_div_of_nonneg_right hlog_le hv_pos.le
        | succ N'' =>
          have hev : evalTrunc logDivC (N'' + 2) v = Complex.log v / v := by
            dsimp only [evalTrunc]
            rw [Finset.sum_eq_single 1]
            · dsimp only [evalTerm, logDivC]
              rw [Finset.sum_range_succ, Finset.sum_range_one]
              simp
            · intro n _ hn1
              dsimp only [evalTerm, logDivC]
              have : ∑ k ∈ Finset.range (n + 1), (if n = 1 ∧ k = 1 then (1 : ℂ) else 0) * Complex.log v ^ k = 0 :=
                Finset.sum_eq_zero fun k _ => by simp [hn1]
              rw [this, zero_div]
            · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
          rw [hev, sub_self, norm_zero]; positivity
  -- 2. `w_plus v / v = 1 + log v / v + (w_plus v - v - log v) * v⁻¹`
  have h1 := hasGev1Exp_const hS1 (1 : ℂ)
  have hinv := hasGev1Exp_inv (S := V_sec) hS1
  have hrem := hasGev1Exp_mul hS1 w_plus_sub_hasGev1Exp hinv
  let aW : LogCoeff := addCoeff (addCoeff (constCoeff 1) logDivC) (mulCoeff wCoeff invCoeff)
  have hwdiv_raw : HasGev1Exp V_sec (fun z => 1 + Complex.log z / z + (w_plus z - z - Complex.log z) * z⁻¹) aW :=
    hasGev1Exp_add (hasGev1Exp_add h1 hlogDiv) hrem
  have hwdiv : HasGev1Exp V_sec (fun v => w_plus v / v) aW := by
    obtain ⟨h0, C, hC, A, hA, hc, hr⟩ := hwdiv_raw
    refine ⟨h0, C, hC, A, hA, hc, fun N v hv => ?_⟩
    have hv0 : v ≠ 0 := norm_pos_iff.mp (by linarith [hS1 v hv])
    have heq : w_plus v / v = 1 + Complex.log v / v + (w_plus v - v - Complex.log v) * v⁻¹ := by
      field_simp [hv0]; ring
    dsimp only; rw [heq]; exact hr N v hv
  -- 3. Multiply by `(S_phi (w_plus v))⁻¹`!
  have hprod := hasGev1Exp_mul hS1 hwdiv inv_S_phi_w_plus_hasGev1Exp
  refine ⟨mulCoeff aW (negPowCoeff 1 (yCoeff (shiftL wCoeff))), ?_⟩
  obtain ⟨h0, C, hC, A, hA, hc, hr⟩ := hprod
  refine ⟨h0, C, hC, A, hA, hc, fun N v hv => ?_⟩
  have heq : F_plus v / v = (w_plus v / v) * (S_phi (w_plus v))⁻¹ := by
    dsimp only [F_plus]; ring
  dsimp only; rw [heq]; exact hr N v hv

/-! ### 4. Entire Continuation `I_entire` and Sectorial Truncated Convolution on `Σ₀` -/

/-! #### 4a. Strip Integrals `J_strip`, Entire Continuation `I_entire`, and Agreement with `I_plus` -/

/-- The shifted valley integrand `exp (w - u - exp(-u) * (Ei_complex w + iπ))`. -/
@[expose] def valleyIntegrand (u w : ℂ) : ℂ :=
  Complex.exp (w - u - Complex.exp (-u) * (Ei_complex w + I * (Real.pi : ℂ)))

lemma hasDerivAt_valleyIntegrand_u (u w : ℂ) :
    HasDerivAt (fun z : ℂ => valleyIntegrand z w)
      ((-1 + Complex.exp (-u) * (Ei_complex w + I * (Real.pi : ℂ))) * valleyIntegrand u w) u := by
  dsimp only [valleyIntegrand]
  have h1 : HasDerivAt (fun z : ℂ => w - z) (-1) u := by
    simpa using (hasDerivAt_const u w).fun_sub (hasDerivAt_id u)
  have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-z) * (Ei_complex w + I * (Real.pi : ℂ)))
      ((-Complex.exp (-u)) * (Ei_complex w + I * (Real.pi : ℂ))) u := by
    have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-z)) (-Complex.exp (-u)) u := by
      simpa using (hasDerivAt_id u).neg.cexp
    exact hexp.mul_const _
  have h3 := (h1.fun_sub h2).cexp
  refine h3.congr_deriv ?_; ring

lemma hasDerivAt_valleyIntegrand_w {u w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt (valleyIntegrand u)
      ((1 - Complex.exp (-u) * (Complex.exp w / w)) * valleyIntegrand u w) w := by
  dsimp only [valleyIntegrand]
  have hEi := PakNthPrimeStokes.hasDerivAt_Ei_complex hw
  have h1 : HasDerivAt (fun z : ℂ => z - u) 1 w := by
    simpa using (hasDerivAt_id w).sub_const u
  have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-u) * (Ei_complex z + I * (Real.pi : ℂ)))
      (Complex.exp (-u) * (Complex.exp w / w)) w := by
    simpa using (hEi.add_const (I * (Real.pi : ℂ))).const_mul (Complex.exp (-u))
  have h3 := (h1.fun_sub h2).cexp
  refine h3.congr_deriv ?_; ring

lemma differentiableOn_valleyIntegrand_w (u : ℂ) :
    DifferentiableOn ℂ (valleyIntegrand u) Complex.slitPlane :=
  fun _ hw => (hasDerivAt_valleyIntegrand_w hw).differentiableAt.differentiableWithinAt

/-- Uniform constant bound on `‖Ei_complex (s - i/4) + iπ‖` for all `s ≤ 1`. -/
lemma norm_Ei_add_I_pi_left_le :
    ∃ K_L : ℝ, 0 < K_L ∧ ∀ s : ℝ, s ≤ 1 →
      ‖Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ)‖ ≤ K_L := by
  let K_L : ℝ := 4 + (|PakNthPrimeStokes.gammaE1| + |Real.log (1 / 4)| + Real.log 2 + Real.pi + Real.exp 2) + Real.pi
  have hK_pos : 0 < K_L := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have := Real.pi_pos
    dsimp [K_L]; positivity
  refine ⟨K_L, hK_pos, fun s hs1 => ?_⟩
  have hvp : (s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I = PakNthPrimeStokes.valleyPoint (-1) s (1 / 4) := by
    dsimp only [PakNthPrimeStokes.valleyPoint]; push_cast; ring
  by_cases hs0 : s ≤ 0
  · have him : ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I).im < 0 := by simp; norm_num
    rw [PakNthPrimeStokes.Ei_complex_eq_neg_E1_sub_I_pi him]
    have hsimp : -PakNthPrimeStokes.E1_complex (-((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) - I * (Real.pi : ℂ) +
        I * (Real.pi : ℂ) = -PakNthPrimeStokes.E1_complex (-((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) := by ring
    rw [hsimp, norm_neg]
    have him_ne : (-((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)).im ≠ 0 := by simp
    have hb := PakNthPrimeStokes.norm_E1_complex_le_exp_div_im him_ne
    have hre : -(-((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)).re = s := by simp
    have him_abs : |(-((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)).im| = 1 / 4 := by simp; norm_num
    rw [hre, him_abs] at hb
    have hexp1 : Real.exp s ≤ 1 := Real.exp_le_one_iff.mpr hs0
    have hle4 : Real.exp s / (1 / 4) ≤ 4 := by linarith
    have hrest : 0 ≤ (|PakNthPrimeStokes.gammaE1| + |Real.log (1 / 4)| + Real.log 2 + Real.pi + Real.exp 2) + Real.pi := by
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have := Real.pi_pos
      positivity
    exact (hb.trans hle4).trans (by dsimp [K_L]; linarith)
  · push Not at hs0
    rw [hvp]
    have hb := PakNthPrimeStokes.norm_Ei_complex_valleyPoint_le_small (σ := -1) (x := s) (ε := 1 / 4)
      (Or.inl rfl) hs0.le hs1 (by norm_num) (by norm_num)
    calc ‖PakNthPrimeStokes.Ei_complex (PakNthPrimeStokes.valleyPoint (-1) s (1 / 4)) + I * (Real.pi : ℂ)‖
        ≤ ‖PakNthPrimeStokes.Ei_complex (PakNthPrimeStokes.valleyPoint (-1) s (1 / 4))‖ + ‖I * (Real.pi : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ (|PakNthPrimeStokes.gammaE1| + |Real.log (1 / 4)| + Real.log 2 + Real.pi + Real.exp 2) + Real.pi := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
          linarith
      _ ≤ K_L := by dsimp [K_L]; linarith

/-- Explicit large-`s` asymptotic lower bound for `Re (exp (-u) * (Ei (s + i y) + iπ))` when `|y - u.im| ≤ π / 3`! -/
lemma re_exp_neg_mul_Ei_add_I_pi_ge {y : ℝ} {u : ℂ} (hstrip : |y - u.im| ≤ Real.pi / 3)
    {s : ℝ} (hs : max (max 16 (16 * |y|)) (32 / Real.cos phiRay ^ 2) ≤ s) :
    let w : ℂ := (s : ℂ) + (y : ℂ) * I
    w ∈ OmegaPhi ∧
    ‖Ei_complex w + I * (Real.pi : ℂ)‖ ≤ 2 * Real.exp s / s ∧
    (1 / 4 : ℝ) * (Real.exp (s - u.re) / s) ≤ (Complex.exp (-u) * (Ei_complex w + I * (Real.pi : ℂ))).re := by
  intro w
  have hs16 : 16 ≤ s := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hs
  have hsy : 16 * |y| ≤ s := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hs
  have hscos : 32 / Real.cos phiRay ^ 2 ≤ s := (le_max_right _ _).trans hs
  have hs_pos : 0 < s := by linarith
  have hsin_ge : (1 / 2 : ℝ) ≤ Real.sin phiRay := by
    have hcos_le : Real.cos (Real.pi / 24) ≥ 1 / 2 := by
      have h1 : Real.pi / 24 ≤ Real.pi / 3 := by linarith [Real.pi_pos]
      have h2 := Real.strictAntiOn_cos.antitoneOn
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ h1
      rwa [Real.cos_pi_div_three] at h2
    have hsin_eq : Real.sin phiRay = Real.cos (Real.pi / 24) := by
      have h : phiRay = Real.pi / 2 - Real.pi / 24 := by dsimp [phiRay]; ring
      rw [h, Real.sin_pi_div_two_sub]
    linarith
  have hd_ge : s / 4 ≤ dPhi w := by
    dsimp only [dPhi, w]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    have hcos1 : Real.cos phiRay ≤ 1 := Real.cos_le_one phiRay
    have hycos : y * Real.cos phiRay ≤ |y| := by
      calc y * Real.cos phiRay ≤ |y| * Real.cos phiRay :=
            mul_le_mul_of_nonneg_right (le_abs_self y) cos_phiRay_pos.le
        _ ≤ |y| * 1 := mul_le_mul_of_nonneg_left hcos1 (abs_nonneg y)
        _ = |y| := mul_one _
    nlinarith
  have hw_mem : w ∈ OmegaPhi := Or.inr (by linarith)
  have hdw_ge : s / 4 ≤ distPhi w := le_trans hd_ge (le_max_right _ _)
  have hw_re : w.re = s := by simp [w]
  have hw_norm_ge : s ≤ ‖w‖ := by
    have := Complex.re_le_norm w; rwa [hw_re] at this
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hA := A_phi_eq_Ei_add_I_pi hw_mem
  have hS1 := norm_S_phi_sub_one_le hw_mem
  have hS_bd : ‖S_phi w - 1‖ ≤ 1 / 8 := by
    have hden : 8 ≤ distPhi w * Real.cos phiRay ^ 2 := by
      have hcos2 : 0 < Real.cos phiRay ^ 2 := pow_pos cos_phiRay_pos 2
      have h1 : 32 ≤ s * Real.cos phiRay ^ 2 := (div_le_iff₀ hcos2).mp hscos
      nlinarith
    exact hS1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
  have hS_norm : ‖S_phi w‖ ≤ 2 := by
    have htri : ‖S_phi w‖ ≤ ‖S_phi w - 1‖ + ‖(1 : ℂ)‖ := by simpa using norm_add_le (S_phi w - 1) 1
    rw [norm_one] at htri; linarith
  have hEi_norm : ‖Ei_complex w + I * (Real.pi : ℂ)‖ ≤ 2 * Real.exp s / s := by
    rw [← hA]
    dsimp only [A_phi, S_phi]
    have hrew : Complex.exp w / w * S_phi w = A_phi w := by dsimp [A_phi, S_phi]; field_simp [hw0]
    rw [show Complex.exp w * S_phi_inner w = Complex.exp w / w * S_phi w by
      dsimp only [S_phi]; field_simp [hw0]]
    rw [norm_mul, norm_div, Complex.norm_exp, hw_re]
    calc Real.exp s / ‖w‖ * ‖S_phi w‖ ≤ Real.exp s / s * 2 :=
          mul_le_mul (div_le_div_of_nonneg_left (Real.exp_pos s).le hs_pos hw_norm_ge) hS_norm
            (norm_nonneg _) (by positivity)
      _ = 2 * Real.exp s / s := by ring
  -- Now compare `S_phi w / w` with `1 / s`: `‖S_phi w / w - 1 / s‖ ≤ (1 / 4) / s`!
  have hdiff_Sw : ‖S_phi w / w - (1 : ℂ) / (s : ℂ)‖ ≤ (1 / 4 : ℝ) / s := by
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
    have hdecomp : S_phi w / w - (1 : ℂ) / (s : ℂ) =
        (S_phi w - 1) / w - ((y : ℂ) * I) / ((s : ℂ) * w) := by
      have hw_def : w = (s : ℂ) + (y : ℂ) * I := rfl
      field_simp [hw0, hs0]
      rw [hw_def]; ring
    rw [hdecomp]
    have hb1 : ‖(S_phi w - 1) / w‖ ≤ (1 / 8 : ℝ) / s := by
      rw [norm_div]
      exact div_le_div₀ (by norm_num) hS_bd hs_pos hw_norm_ge
    have hb2 : ‖((y : ℂ) * I) / ((s : ℂ) * w)‖ ≤ (1 / 16 : ℝ) / s := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      have hden : s * s ≤ s * ‖w‖ := mul_le_mul_of_nonneg_left hw_norm_ge hs_pos.le
      calc |y| / (s * ‖w‖) ≤ |y| / (s * s) :=
            div_le_div_of_nonneg_left (abs_nonneg y) (mul_pos hs_pos hs_pos) hden
        _ ≤ (s / 16) / (s * s) := div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = (1 / 16 : ℝ) / s := by field_simp [hs_pos.ne']
    calc _ ≤ ‖(S_phi w - 1) / w‖ + ‖((y : ℂ) * I) / ((s : ℂ) * w)‖ := norm_sub_le _ _
      _ ≤ (1 / 8 : ℝ) / s + (1 / 16 : ℝ) / s := add_le_add hb1 hb2
      _ ≤ (1 / 4 : ℝ) / s := by rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hs_pos.le
  -- Compute real part of `exp (-u) * A_phi w = exp (w - u) * (S_phi w / w)`!
  have hprod_eq : Complex.exp (-u) * (Ei_complex w + I * (Real.pi : ℂ)) =
      Complex.exp (w - u) * ((1 : ℂ) / (s : ℂ)) +
      Complex.exp (w - u) * (S_phi w / w - (1 : ℂ) / (s : ℂ)) := by
    rw [← hA]
    have hA_eq : A_phi w = Complex.exp w * (S_phi w / w) := by dsimp [A_phi, S_phi]; field_simp [hw0]
    rw [hA_eq, ← mul_assoc, ← Complex.exp_add, show -u + w = w - u by ring]; ring
  have hcos_ge : (1 / 2 : ℝ) ≤ Real.cos (y - u.im) := by
    have h1 : |y - u.im| ≤ Real.pi / 3 := hstrip
    have h2 := Real.strictAntiOn_cos.antitoneOn
      ⟨abs_nonneg _, (h1.trans (by linarith [Real.pi_pos]))⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ h1
    rw [Real.cos_abs, Real.cos_pi_div_three] at h2
    exact h2
  have hwu_re : (w - u).re = s - u.re := by simp [w]
  have hwu_im : (w - u).im = y - u.im := by simp [w]
  have hmain_re : (1 / 2 : ℝ) * (Real.exp (s - u.re) / s) ≤
      (Complex.exp (w - u) * ((1 : ℂ) / (s : ℂ))).re := by
    have h1 : (Complex.exp (w - u) * ((1 : ℂ) / (s : ℂ))).re =
        (Real.exp (s - u.re) / s) * Real.cos (y - u.im) := by
      have hdiv : ((1 : ℂ) / (s : ℂ)) = ((1 / s : ℝ) : ℂ) := by push_cast; ring
      rw [hdiv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.exp_re, hwu_re, hwu_im]
      ring
    rw [h1]
    have : 0 ≤ Real.exp (s - u.re) / s := by positivity
    nlinarith
  have herr_norm : ‖Complex.exp (w - u) * (S_phi w / w - (1 : ℂ) / (s : ℂ))‖ ≤
      (1 / 4 : ℝ) * (Real.exp (s - u.re) / s) := by
    rw [norm_mul, Complex.norm_exp, hwu_re]
    calc Real.exp (s - u.re) * ‖S_phi w / w - (1 : ℂ) / (s : ℂ)‖
        ≤ Real.exp (s - u.re) * ((1 / 4 : ℝ) / s) :=
          mul_le_mul_of_nonneg_left hdiff_Sw (Real.exp_pos _).le
      _ = (1 / 4 : ℝ) * (Real.exp (s - u.re) / s) := by ring
  have herr_re := (abs_le.mp ((Complex.abs_re_le_norm _).trans herr_norm)).1
  refine ⟨hw_mem, hEi_norm, ?_⟩
  rw [hprod_eq, Complex.add_re]
  linarith

/-- Uniform super-exponential dominating bound on the right ray `s ≥ S₁` for `valleyIntegrand` and its `u`-derivative! -/
lemma norm_valleyIntegrand_right_dom (M_u M_y : ℝ) (_hMu : 0 ≤ M_u) (_hMy : 0 ≤ M_y) :
    let S₁ : ℝ := max (max 16 (16 * M_y)) (32 / Real.cos phiRay ^ 2)
    ∃ C > 0, ∀ (u : ℂ) (y : ℝ), |u.re| ≤ M_u → |y| ≤ M_y → |y - u.im| ≤ Real.pi / 3 →
      ∀ s ≥ S₁,
        ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ ≤ C * Real.exp (-s) ∧
        ‖(-1 + Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))) *
            valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ ≤ C * Real.exp (-s) := by
  intro S₁
  let a : ℝ := Real.exp (-M_u) / 4
  have ha_pos : 0 < a := by dsimp [a]; positivity
  let C₁ : ℝ := Real.exp M_u * Real.exp (6 / a)
  let C₂ : ℝ := Real.exp M_u * (16 / a ^ 2 * Real.exp (12 / a))
  let C : ℝ := max C₁ (C₁ + 2 * Real.exp M_u * C₂) + 1
  have hC_pos : 0 < C := by dsimp [C, C₁, C₂]; positivity
  refine ⟨C, hC_pos, fun u y hu hy hstrip s hs => ?_⟩
  have hs_y : max (max 16 (16 * |y|)) (32 / Real.cos phiRay ^ 2) ≤ s := by
    have h1 : max (max 16 (16 * |y|)) (32 / Real.cos phiRay ^ 2) ≤ S₁ :=
      max_le_max_right _ (max_le_max_left _ (by linarith))
    exact h1.trans hs
  have hs16 : 16 ≤ s := le_trans (le_max_left _ _) (le_max_left _ _) |>.trans hs
  have hs1 : 1 ≤ s := by linarith
  have hs_pos : 0 < s := by linarith
  obtain ⟨_, hEi_norm, hre_ge⟩ := re_exp_neg_mul_Ei_add_I_pi_ge hstrip hs_y
  have hneg_ure : -u.re ≤ M_u := by linarith [(abs_le.mp hu).1]
  have ha_le : a ≤ Real.exp (-u.re) / 4 := by
    dsimp only [a]; exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hu).2])) (by norm_num)
  have hexp_split : Real.exp (s - u.re) / s = Real.exp (-u.re) * (Real.exp s / s) := by
    rw [sub_eq_add_neg, Real.exp_add]; ring
  have hre_a : a * (Real.exp s / s) ≤ (Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))).re := by
    have h1 : a * (Real.exp s / s) ≤ (1 / 4 : ℝ) * (Real.exp (s - u.re) / s) := by
      rw [hexp_split]
      have : 0 ≤ Real.exp s / s := by positivity
      nlinarith
    exact h1.trans hre_ge
  have hbase_raw : ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp M_u * Real.exp (s - a * (Real.exp s / s)) := by
    dsimp only [valleyIntegrand]
    rw [Complex.norm_exp]
    have harg : (((s : ℂ) + (y : ℂ) * I) - u -
          Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))).re ≤
        M_u + (s - a * (Real.exp s / s)) := by
      rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im]
      linarith
    exact (Real.exp_le_exp.mpr harg).trans (le_of_eq (Real.exp_add _ _))
  have hb1 : ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ ≤ C₁ * Real.exp (-s) := by
    have htail := PakNthPrimeStokes.tail_exp_div_dominates ha_pos hs1
    calc _ ≤ Real.exp M_u * Real.exp (s - a * (Real.exp s / s)) := hbase_raw
      _ ≤ Real.exp M_u * Real.exp (-s + 6 / a) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htail) (Real.exp_pos _).le
      _ = C₁ * Real.exp (-s) := by dsimp [C₁]; rw [Real.exp_add]; ring
  have hb_exp : Real.exp s * ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ ≤ C₂ * Real.exp (-s) := by
    have habs := PakNthPrimeStokes.exp_mul_tail_absorb ha_pos hs1
    calc _ ≤ Real.exp s * (Real.exp M_u * Real.exp (s - a * (Real.exp s / s))) :=
          mul_le_mul_of_nonneg_left hbase_raw (Real.exp_pos _).le
      _ = Real.exp M_u * (Real.exp s * Real.exp (s - a * (Real.exp s / s))) := by ring
      _ ≤ Real.exp M_u * ((16 / a ^ 2 * Real.exp (12 / a)) * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
      _ = C₂ * Real.exp (-s) := by dsimp [C₂]; ring
  have hC1_le : C₁ ≤ C := by dsimp [C]; linarith [le_max_left C₁ (C₁ + 2 * Real.exp M_u * C₂)]
  have hC2_le : C₁ + 2 * Real.exp M_u * C₂ ≤ C := by
    dsimp [C]; linarith [le_max_right C₁ (C₁ + 2 * Real.exp M_u * C₂)]
  refine ⟨hb1.trans (mul_le_mul_of_nonneg_right hC1_le (Real.exp_pos _).le), ?_⟩
  have hfac : ‖-1 + Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
      1 + 2 * Real.exp M_u * Real.exp s := by
    have hexp_u : ‖Complex.exp (-u)‖ ≤ Real.exp M_u := by
      rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_exp.mpr hneg_ure
    have hdiv_le : 2 * Real.exp s / s ≤ 2 * Real.exp s := div_le_self (by positivity) hs1
    calc _ ≤ ‖(-1 : ℂ)‖ + ‖Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))‖ :=
          norm_add_le _ _
      _ = 1 + ‖Complex.exp (-u)‖ * ‖Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ)‖ := by
          rw [norm_neg, norm_one, norm_mul]
      _ ≤ 1 + Real.exp M_u * (2 * Real.exp s) := by
          gcongr; exact hEi_norm.trans hdiv_le
      _ = 1 + 2 * Real.exp M_u * Real.exp s := by ring
  rw [norm_mul]
  calc _ ≤ (1 + 2 * Real.exp M_u * Real.exp s) * ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
    _ = ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ +
          2 * Real.exp M_u * (Real.exp s * ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖) := by ring
    _ ≤ C₁ * Real.exp (-s) + 2 * Real.exp M_u * (C₂ * Real.exp (-s)) :=
        add_le_add hb1 (mul_le_mul_of_nonneg_left hb_exp (by positivity))
    _ = (C₁ + 2 * Real.exp M_u * C₂) * Real.exp (-s) := by ring
    _ ≤ C * Real.exp (-s) := mul_le_mul_of_nonneg_right hC2_le (Real.exp_pos _).le

/-- Piecewise rectangular horizontal-strip contour integral `J_strip y₀ u` defining the
entire continuation of `I_plus` on `{u : ℂ | |u.im - y₀| < π / 3}`! -/
@[expose] def J_strip (y₀ : ℝ) (u : ℂ) : ℂ :=
  (∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) +
  (I * ∫ y in (-1 / 4 : ℝ)..y₀, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) +
  (∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (y₀ : ℂ) * I))

lemma integrableOn_exp_Iic (c : ℝ) : IntegrableOn (fun s : ℝ => Real.exp s) (Set.Iic c) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi (-c)) :=
    (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) (-c)).congr_fun
      (fun x _ => by simp) measurableSet_Ioi
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ici (-c)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
  rw [← integrable_indicator_iff measurableSet_Iic]
  rw [← integrable_indicator_iff measurableSet_Ici] at h2
  have hcomp := h2.comp_neg
  refine hcomp.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Set.indicator, Set.mem_Iic, Set.mem_Ici, neg_neg, neg_le_neg_iff]

lemma integrableOn_exp_neg_Ici (c : ℝ) : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Set.Ici c) :=
  (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    ((integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) c).congr_fun
      (fun x _ => by simp) measurableSet_Ioi)

/-- Integrability of `valleyIntegrand u (s + i y)` on `Set.Ici 1` whenever `|y - u.im| ≤ π / 3`. -/
lemma integrableOn_valleyIntegrand_right {u : ℂ} {y : ℝ} (hstrip : |y - u.im| ≤ Real.pi / 3) :
    IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)) (Set.Ici 1) := by
  obtain ⟨C, _, hdom⟩ := norm_valleyIntegrand_right_dom |u.re| |y| (abs_nonneg _) (abs_nonneg _)
  set S₁ : ℝ := max (max 16 (16 * |y|)) (32 / Real.cos phiRay ^ 2)
  have hS1_ge : 1 ≤ S₁ := by
    have : (16 : ℝ) ≤ S₁ := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hcont : ContinuousOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)) (Set.Ici 1) := by
    refine (differentiableOn_valleyIntegrand_w u).continuousOn.comp (g := valleyIntegrand u)
      (Complex.continuous_ofReal.add continuous_const).continuousOn ?_
    intro s hs
    left
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    linarith [Set.mem_Ici.mp hs]
  have hleft : IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)) (Set.Icc 1 S₁) :=
    (hcont.mono (fun s (hs : s ∈ Set.Icc 1 S₁) => hs.1)).integrableOn_Icc
  have hright : IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)) (Set.Ici S₁) := by
    refine ((integrableOn_exp_neg_Ici S₁).const_mul C).mono'
      ((hcont.mono (fun s (hs : s ∈ Set.Ici S₁) => hS1_ge.trans hs)).aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact (hdom u y le_rfl le_rfl hstrip s hs).1
  have hU : Set.Ici (1 : ℝ) = Set.Icc 1 S₁ ∪ Set.Ici S₁ := by
    ext s; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Icc]
    exact ⟨fun h => by rcases le_total s S₁ with h1 | h2 <;> [exact Or.inl ⟨h, h1⟩; exact Or.inr h2],
      fun h => by rcases h with ⟨h1, _⟩ | h2 <;> linarith⟩
  rw [hU]; exact hleft.union hright

/-- Holomorphicity of `J_strip y₀` on the open horizontal strip `{u : ℂ | |u.im - y₀| < π / 3}`! -/
theorem differentiableOn_J_strip (y₀ : ℝ) :
    DifferentiableOn ℂ (J_strip y₀) {u : ℂ | |u.im - y₀| < Real.pi / 3} := by
  intro u₀ hu₀
  have hstrip₀ : |u₀.im - y₀| < Real.pi / 3 := hu₀
  set δ : ℝ := min 1 ((Real.pi / 3 - |u₀.im - y₀|) / 2)
  have hδ_pos : 0 < δ := lt_min zero_lt_one (by linarith)
  have hball_nhds : Metric.ball u₀ δ ∈ 𝓝 u₀ := Metric.ball_mem_nhds u₀ hδ_pos
  have hball_re : ∀ u ∈ Metric.ball u₀ δ, |u.re| ≤ |u₀.re| + 1 := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : |u.re - u₀.re| ≤ 1 := ((Complex.abs_re_le_norm (u - u₀)).trans hu.le).trans (min_le_left _ _)
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [le_abs_self u₀.re, neg_le_abs u₀.re]
  have hball_strip : ∀ u ∈ Metric.ball u₀ δ, |y₀ - u.im| ≤ Real.pi / 3 := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : |u.im - u₀.im| ≤ (Real.pi / 3 - |u₀.im - y₀|) / 2 :=
      ((Complex.abs_im_le_norm (u - u₀)).trans hu.le).trans (min_le_right _ _)
    have htri : |y₀ - u.im| ≤ |u₀.im - y₀| + |u.im - u₀.im| := by
      have h := abs_add_le (y₀ - u₀.im) (u₀.im - u.im)
      rw [show (y₀ - u₀.im) + (u₀.im - u.im) = y₀ - u.im by ring, abs_sub_comm y₀ u₀.im,
        abs_sub_comm u₀.im u.im] at h
      exact h
    linarith
  let M_u : ℝ := |u₀.re| + 1
  -- Piece 1: left ray `Set.Iic 1`
  have hdiff1 : DifferentiableAt ℂ (fun u : ℂ =>
      ∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) u₀ := by
    obtain ⟨K_L, hKL, hEi_L⟩ := norm_Ei_add_I_pi_left_le
    let F : ℂ → ℝ → ℂ := fun u s => valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)
    let F' : ℂ → ℝ → ℂ := fun u s =>
      (-1 + Complex.exp (-u) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))) *
        valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)
    let B : ℝ := (1 + Real.exp M_u * K_L) * Real.exp (M_u + Real.exp M_u * K_L)
    have hcont_w : Continuous (fun s : ℝ => (s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) :=
      Complex.continuous_ofReal.add continuous_const
    have hcont_F : ∀ u : ℂ, Continuous (F u) := fun u => by
      refine (differentiableOn_valleyIntegrand_w u).continuousOn.comp_continuous hcont_w fun s => ?_
      right; simp
    have hcont_Ei : Continuous (fun s : ℝ => Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) := by
      refine continuous_iff_continuousAt.mpr fun s => ?_
      have hslit : ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) ∈ Complex.slitPlane := Or.inr (by simp)
      exact ContinuousAt.comp (g := Ei_complex) (PakNthPrimeStokes.hasDerivAt_Ei_complex hslit).continuousAt hcont_w.continuousAt
    have hcont_F' : Continuous (F' u₀) :=
      (continuous_const.add (continuous_const.mul (hcont_Ei.add continuous_const))).mul (hcont_F u₀)
    have hbd_F : ∀ u ∈ Metric.ball u₀ δ, ∀ s ≤ (1 : ℝ),
        ‖F u s‖ ≤ Real.exp (M_u + Real.exp M_u * K_L) * Real.exp s ∧ ‖F' u s‖ ≤ B * Real.exp s := by
      intro u hu s hs
      have hre : -u.re ≤ M_u := by linarith [(abs_le.mp (hball_re u hu)).1]
      have hexp_u : ‖Complex.exp (-u)‖ ≤ Real.exp M_u := by
        rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_exp.mpr hre
      have hprod : ‖Complex.exp (-u) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
          Real.exp M_u * K_L := by
        rw [norm_mul]; exact mul_le_mul hexp_u (hEi_L s hs) (norm_nonneg _) (Real.exp_pos _).le
      have hbase : ‖F u s‖ ≤ Real.exp (M_u + Real.exp M_u * K_L) * Real.exp s := by
        dsimp only [F, valleyIntegrand]
        rw [Complex.norm_exp]
        have harg : (((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) - u -
              Complex.exp (-u) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))).re ≤
            (M_u + Real.exp M_u * K_L) + s := by
          have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
          rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im]
          linarith
        exact (Real.exp_le_exp.mpr harg).trans (le_of_eq (Real.exp_add _ _))
      refine ⟨hbase, ?_⟩
      dsimp only [F', B]
      rw [norm_mul]
      have hfac : ‖-1 + Complex.exp (-u) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
          1 + Real.exp M_u * K_L := by
        calc _ ≤ ‖(-1 : ℂ)‖ + _ := norm_add_le _ _
          _ ≤ 1 + Real.exp M_u * K_L := by rw [norm_neg, norm_one]; linarith
      calc _ ≤ (1 + Real.exp M_u * K_L) * (Real.exp (M_u + Real.exp M_u * K_L) * Real.exp s) :=
            mul_le_mul hfac hbase (norm_nonneg _) (by positivity)
        _ = (1 + Real.exp M_u * K_L) * Real.exp (M_u + Real.exp M_u * K_L) * Real.exp s := by ring
    have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Iic (1 : ℝ)))
      (F := F) (F' := F') (bound := fun s => B * Real.exp s)
      hball_nhds
      (Filter.Eventually.of_forall fun u => (hcont_F u).aestronglyMeasurable)
      (((integrableOn_exp_Iic 1).const_mul (Real.exp (M_u + Real.exp M_u * K_L))).mono'
        (hcont_F u₀).aestronglyMeasurable
        (by filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
            exact (hbd_F u₀ (Metric.mem_ball_self hδ_pos) s hs).1))
      hcont_F'.aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs u hu
          exact (hbd_F u hu s hs).2)
      ((integrableOn_exp_Iic 1).const_mul B)
      (Filter.Eventually.of_forall fun s u _ => hasDerivAt_valleyIntegrand_u u _)
    exact hres.2.differentiableAt
  -- Piece 2: compact vertical segment `(-1/4)..y₀`
  have hdiff2 : DifferentiableAt ℂ (fun u : ℂ =>
      I * ∫ y in (-1 / 4 : ℝ)..y₀, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) u₀ := by
    let F : ℂ → ℝ → ℂ := fun u y => valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)
    let F' : ℂ → ℝ → ℂ := fun u y =>
      (-1 + Complex.exp (-u) * (Ei_complex ((1 : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))) *
        valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)
    have hcont_w : Continuous (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcont_Ei : Continuous (fun y : ℝ => Ei_complex ((1 : ℂ) + (y : ℂ) * I)) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have hslit : ((1 : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := Or.inl (by simp)
      exact ContinuousAt.comp (g := Ei_complex) (PakNthPrimeStokes.hasDerivAt_Ei_complex hslit).continuousAt hcont_w.continuousAt
    have hcont_F : ∀ u : ℂ, Continuous (F u) := fun u =>
      (differentiableOn_valleyIntegrand_w u).continuousOn.comp_continuous hcont_w fun y => Or.inl (by simp)
    have hcont_F' : Continuous (F' u₀) :=
      (continuous_const.add (continuous_const.mul (hcont_Ei.add continuous_const))).mul (hcont_F u₀)
    obtain ⟨K_E, hKE⟩ := (isCompact_uIcc (a := (-1 / 4 : ℝ)) (b := y₀)).exists_bound_of_continuousOn
      (hcont_Ei.add continuous_const).continuousOn
    let K_E' : ℝ := max 0 K_E
    let B : ℝ := (1 + Real.exp M_u * K_E') * Real.exp (1 + M_u + Real.exp M_u * K_E')
    have hbd_F' : ∀ y ∈ Set.uIcc (-1 / 4 : ℝ) y₀, ∀ u ∈ Metric.ball u₀ δ, ‖F' u y‖ ≤ B := by
      intro y hy u hu
      have hEi : ‖Ei_complex ((1 : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ)‖ ≤ K_E' :=
        (hKE y hy).trans (le_max_right _ _)
      have hre : -u.re ≤ M_u := by linarith [(abs_le.mp (hball_re u hu)).1]
      have hexp_u : ‖Complex.exp (-u)‖ ≤ Real.exp M_u := by
        rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_exp.mpr hre
      have hprod : ‖Complex.exp (-u) * (Ei_complex ((1 : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
          Real.exp M_u * K_E' := by
        rw [norm_mul]; exact mul_le_mul hexp_u hEi (norm_nonneg _) (Real.exp_pos _).le
      have hbase : ‖F u y‖ ≤ Real.exp (1 + M_u + Real.exp M_u * K_E') := by
        dsimp only [F, valleyIntegrand]
        rw [Complex.norm_exp]
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
        refine Real.exp_le_exp.mpr ?_
        rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
        linarith
      dsimp only [F', B]
      rw [norm_mul]
      have hfac : ‖-1 + Complex.exp (-u) * (Ei_complex ((1 : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
          1 + Real.exp M_u * K_E' := by
        calc _ ≤ ‖(-1 : ℂ)‖ + _ := norm_add_le _ _
          _ ≤ 1 + Real.exp M_u * K_E' := by rw [norm_neg, norm_one]; linarith
      exact mul_le_mul hfac hbase (norm_nonneg _) (by positivity)
    have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := fun _ => B)
      hball_nhds
      (Filter.Eventually.of_forall fun u => (hcont_F u).aestronglyMeasurable)
      ((hcont_F u₀).intervalIntegrable _ _)
      hcont_F'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y hy u hu => hbd_F' y (Set.uIoc_subset_uIcc hy) u hu)
      (intervalIntegrable_const (μ := volume))
      (Filter.Eventually.of_forall fun y _ u _ => hasDerivAt_valleyIntegrand_u u _)
    exact (hres.2.const_mul I).differentiableAt
  -- Piece 3: right ray `Set.Ici 1`
  have hdiff3 : DifferentiableAt ℂ (fun u : ℂ =>
      ∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (y₀ : ℂ) * I)) u₀ := by
    let F : ℂ → ℝ → ℂ := fun u s => valleyIntegrand u ((s : ℂ) + (y₀ : ℂ) * I)
    let F' : ℂ → ℝ → ℂ := fun u s =>
      (-1 + Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y₀ : ℂ) * I) + I * (Real.pi : ℂ))) *
        valleyIntegrand u ((s : ℂ) + (y₀ : ℂ) * I)
    obtain ⟨C_r, hCr_pos, hdom_r⟩ := norm_valleyIntegrand_right_dom M_u |y₀| (by dsimp [M_u]; positivity) (abs_nonneg _)
    set S₁ : ℝ := max (max 16 (16 * |y₀|)) (32 / Real.cos phiRay ^ 2)
    have hS1_ge : 1 ≤ S₁ := by
      have : (16 : ℝ) ≤ S₁ := le_trans (le_max_left _ _) (le_max_left _ _)
      linarith
    have hcont_w : Continuous (fun s : ℝ => (s : ℂ) + (y₀ : ℂ) * I) :=
      Complex.continuous_ofReal.add continuous_const
    have hcont_Ei : ContinuousOn (fun s : ℝ => Ei_complex ((s : ℂ) + (y₀ : ℂ) * I)) (Set.Ici 1) := by
      intro s hs
      have hslit : ((s : ℂ) + (y₀ : ℂ) * I) ∈ Complex.slitPlane := Or.inl (by simp; linarith [Set.mem_Ici.mp hs])
      exact (ContinuousAt.comp (g := Ei_complex) (f := fun t : ℝ => (t : ℂ) + (y₀ : ℂ) * I)
        (PakNthPrimeStokes.hasDerivAt_Ei_complex hslit).continuousAt hcont_w.continuousAt).continuousWithinAt
    have hcont_F : ∀ u : ℂ, ContinuousOn (F u) (Set.Ici 1) := fun u =>
      (differentiableOn_valleyIntegrand_w u).continuousOn.comp (g := valleyIntegrand u) hcont_w.continuousOn
        (fun s hs => Or.inl (by simp; linarith [Set.mem_Ici.mp hs]))
    have hcont_F' : ContinuousOn (F' u₀) (Set.Ici 1) :=
      (continuousOn_const.add (continuousOn_const.mul (hcont_Ei.add continuousOn_const))).mul (hcont_F u₀)
    obtain ⟨K_c, hKc⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := S₁)).exists_bound_of_continuousOn
      ((hcont_Ei.add continuousOn_const).mono (fun s (hs : s ∈ Set.Icc 1 S₁) => hs.1))
    let K_c' : ℝ := max 0 K_c
    let B_c : ℝ := (1 + Real.exp M_u * K_c') * Real.exp (S₁ + M_u + Real.exp M_u * K_c') * Real.exp S₁
    let B_tot : ℝ := max C_r B_c
    have hbd_F' : ∀ s ∈ Set.Ici (1 : ℝ), ∀ u ∈ Metric.ball u₀ δ, ‖F' u s‖ ≤ B_tot * Real.exp (-s) := by
      intro s hs u hu
      by_cases hsS : S₁ ≤ s
      · have h1 := (hdom_r u y₀ (hball_re u hu) le_rfl (hball_strip u hu) s hsS).2
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      · push Not at hsS
        have hsIcc : s ∈ Set.Icc (1 : ℝ) S₁ := ⟨hs, hsS.le⟩
        have hEi : ‖Ei_complex ((s : ℂ) + (y₀ : ℂ) * I) + I * (Real.pi : ℂ)‖ ≤ K_c' :=
          (hKc s hsIcc).trans (le_max_right _ _)
        have hre : -u.re ≤ M_u := by linarith [(abs_le.mp (hball_re u hu)).1]
        have hexp_u : ‖Complex.exp (-u)‖ ≤ Real.exp M_u := by
          rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_exp.mpr hre
        have hprod : ‖Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y₀ : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
            Real.exp M_u * K_c' := by
          rw [norm_mul]; exact mul_le_mul hexp_u hEi (norm_nonneg _) (Real.exp_pos _).le
        have hbase : ‖F u s‖ ≤ Real.exp (S₁ + M_u + Real.exp M_u * K_c') := by
          dsimp only [F, valleyIntegrand]
          rw [Complex.norm_exp]
          have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
          refine Real.exp_le_exp.mpr ?_
          rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im]
          linarith
        have hfac : ‖-1 + Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y₀ : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
            1 + Real.exp M_u * K_c' := by
          calc _ ≤ ‖(-1 : ℂ)‖ + _ := norm_add_le _ _
            _ ≤ 1 + Real.exp M_u * K_c' := by rw [norm_neg, norm_one]; linarith
        have h1exp : 1 ≤ Real.exp S₁ * Real.exp (-s) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
        have hmul : ‖F' u s‖ ≤ (1 + Real.exp M_u * K_c') * Real.exp (S₁ + M_u + Real.exp M_u * K_c') := by
          dsimp only [F']; rw [norm_mul]; exact mul_le_mul hfac hbase (norm_nonneg _) (by positivity)
        calc ‖F' u s‖ ≤ ((1 + Real.exp M_u * K_c') * Real.exp (S₁ + M_u + Real.exp M_u * K_c')) * 1 := by linarith
          _ ≤ ((1 + Real.exp M_u * K_c') * Real.exp (S₁ + M_u + Real.exp M_u * K_c')) *
                (Real.exp S₁ * Real.exp (-s)) :=
              mul_le_mul_of_nonneg_left h1exp (by positivity)
          _ = B_c * Real.exp (-s) := by dsimp [B_c]; ring
          _ ≤ B_tot * Real.exp (-s) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ici (1 : ℝ)))
      (F := F) (F' := F') (bound := fun s => B_tot * Real.exp (-s))
      hball_nhds
      (Filter.Eventually.of_forall fun u => (hcont_F u).aestronglyMeasurable measurableSet_Ici)
      (integrableOn_valleyIntegrand_right (hball_strip u₀ (Metric.mem_ball_self hδ_pos)))
      (hcont_F'.aestronglyMeasurable measurableSet_Ici)
      (by filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs u hu
          exact hbd_F' s hs u hu)
      ((integrableOn_exp_neg_Ici 1).const_mul B_tot)
      (Filter.Eventually.of_forall fun s u _ => hasDerivAt_valleyIntegrand_u u _)
    exact hres.2.differentiableAt
  exact ((hdiff1.add hdiff2).add hdiff3).differentiableWithinAt

/-- **Overlap Invariance**: `J_strip y₁ u = J_strip y₂ u` whenever both `|u.im - y₁| < π/3` and `|u.im - y₂| < π/3`! -/
theorem J_strip_eq_of_overlap {y₁ y₂ : ℝ} {u : ℂ}
    (h1 : |u.im - y₁| < Real.pi / 3) (h2 : |u.im - y₂| < Real.pi / 3) :
    J_strip y₁ u = J_strip y₂ u := by
  let M_y : ℝ := max |y₁| |y₂|
  obtain ⟨C, _, hdom⟩ := norm_valleyIntegrand_right_dom |u.re| M_y (abs_nonneg _) (le_trans (abs_nonneg y₁) (le_max_left _ _))
  set S₁ : ℝ := max (max 16 (16 * M_y)) (32 / Real.cos phiRay ^ 2)
  have hstrip_mid : ∀ y ∈ Set.uIcc y₁ y₂, |y - u.im| ≤ Real.pi / 3 ∧ |y| ≤ M_y := by
    intro y hy
    have h1' : |y₁ - u.im| ≤ Real.pi / 3 := by rw [abs_sub_comm]; exact h1.le
    have h2' : |y₂ - u.im| ≤ Real.pi / 3 := by rw [abs_sub_comm]; exact h2.le
    rw [abs_le] at h1' h2'
    rcases Set.mem_uIcc.mp hy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨?_, ?_⟩⟩
      · have : -M_y ≤ y₁ := by linarith [neg_abs_le y₁, le_max_left |y₁| |y₂|]
        linarith
      · have : y₂ ≤ M_y := le_trans (le_abs_self y₂) (le_max_right |y₁| |y₂|)
        linarith
    · refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨?_, ?_⟩⟩
      · have : -M_y ≤ y₂ := by linarith [neg_abs_le y₂, le_max_right |y₁| |y₂|]
        linarith
      · have : y₁ ≤ M_y := le_trans (le_abs_self y₁) (le_max_left |y₁| |y₂|)
        linarith
  -- For every `M ≥ max 2 S₁`, Cauchy's rectangle theorem on `[1, M] × [y₁, y₂]` relates the two truncated rays!
  have hrect : ∀ M : ℝ, max 2 S₁ ≤ M →
      (∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₁ : ℂ) * I)) -
      (∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₂ : ℂ) * I)) -
      I * (∫ y in y₁..y₂, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) =
      -(I * ∫ y in y₁..y₂, valleyIntegrand u ((M : ℂ) + (y : ℂ) * I)) := by
    intro M hM
    let z : ℂ := (1 : ℂ) + (y₁ : ℂ) * I
    let w : ℂ := (M : ℂ) + (y₂ : ℂ) * I
    have hzre : z.re = 1 := by simp [z]
    have hzim : z.im = y₁ := by simp [z]
    have hwre : w.re = M := by simp [w]
    have hwim : w.im = y₂ := by simp [w]
    have hsub : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Complex.slitPlane := by
      intro p hp
      left
      have hpre := hp.1
      rw [hzre, hwre, Set.uIcc_of_le (by linarith [le_max_left (2 : ℝ) S₁])] at hpre
      linarith [hpre.1]
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (valleyIntegrand u) z w ((differentiableOn_valleyIntegrand_w u).mono hsub)
    rw [hzre, hzim, hwre, hwim] at hcauchy
    simp only [smul_eq_mul] at hcauchy
    linear_combination hcauchy
  -- Let `M → +∞`!
  have hlim1 : Tendsto (fun M : ℝ => ∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₁ : ℂ) * I))
      atTop (𝓝 (∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (y₁ : ℂ) * I))) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact intervalIntegral_tendsto_integral_Ioi 1
      ((integrableOn_Ici_iff_integrableOn_Ioi).mp (integrableOn_valleyIntegrand_right (by rw [abs_sub_comm]; exact h1.le)))
      tendsto_id
  have hlim2 : Tendsto (fun M : ℝ => ∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₂ : ℂ) * I))
      atTop (𝓝 (∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (y₂ : ℂ) * I))) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact intervalIntegral_tendsto_integral_Ioi 1
      ((integrableOn_Ici_iff_integrableOn_Ioi).mp (integrableOn_valleyIntegrand_right (by rw [abs_sub_comm]; exact h2.le)))
      tendsto_id
  have hlim_rhs : Tendsto (fun M : ℝ => -(I * ∫ y in y₁..y₂, valleyIntegrand u ((M : ℂ) + (y : ℂ) * I)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun M : ℝ => (C * |y₂ - y₁|) * Real.exp (-M)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (max 2 S₁)] with M hM
      have hMS : S₁ ≤ M := le_trans (le_max_right _ _) hM
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
      have hbd : ∀ y ∈ Set.uIoc y₁ y₂, ‖valleyIntegrand u ((M : ℂ) + (y : ℂ) * I)‖ ≤ C * Real.exp (-M) := by
        intro y hy
        obtain ⟨hs, hmy⟩ := hstrip_mid y (Set.uIoc_subset_uIcc hy)
        exact (hdom u y le_rfl hmy hs M hMS).1
      calc _ ≤ (C * Real.exp (-M)) * |y₂ - y₁| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
        _ = (C * |y₂ - y₁|) * Real.exp (-M) := by ring
    · have h0 : Tendsto (fun M : ℝ => Real.exp (-M)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simpa using h0.const_mul (C * |y₂ - y₁|)
  have hlim_lhs : Tendsto (fun M : ℝ =>
      (∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₁ : ℂ) * I)) -
      (∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₂ : ℂ) * I)) -
      I * (∫ y in y₁..y₂, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)))
      atTop (𝓝 ((∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (y₁ : ℂ) * I)) -
        (∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (y₂ : ℂ) * I)) -
        I * (∫ y in y₁..y₂, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)))) :=
    (hlim1.sub hlim2).sub tendsto_const_nhds
  have hlim_eq : Tendsto (fun M : ℝ =>
      (∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₁ : ℂ) * I)) -
      (∫ s in (1 : ℝ)..M, valleyIntegrand u ((s : ℂ) + (y₂ : ℂ) * I)) -
      I * (∫ y in y₁..y₂, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)))
      atTop (𝓝 0) :=
    hlim_rhs.congr' (by filter_upwards [Filter.eventually_ge_atTop (max 2 S₁)] with M hM; exact (hrect M hM).symm)
  have hzero := tendsto_nhds_unique hlim_lhs hlim_eq
  -- Combine with vertical-segment additivity `(-1/4)..y₁ + y₁..y₂ = (-1/4)..y₂`!
  have hcont_v : Continuous (fun y : ℝ => valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) :=
    (differentiableOn_valleyIntegrand_w u).continuousOn.comp_continuous
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun y => Or.inl (by simp)
  have hv_add : (∫ y in (-1 / 4 : ℝ)..y₁, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) +
      (∫ y in y₁..y₂, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) =
      ∫ y in (-1 / 4 : ℝ)..y₂, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont_v.intervalIntegrable _ _) (hcont_v.intervalIntegrable _ _)
  dsimp only [J_strip]
  linear_combination hzero + I * hv_add

/-- The global entire continuation `I_entire : ℂ → ℂ` of `I_plus`! -/
@[expose] def I_entire (u : ℂ) : ℂ := J_strip u.im u

/-- **Global Holomorphicity**: `I_entire` is entire on `ℂ`! -/
theorem differentiable_I_entire : Differentiable ℂ I_entire := by
  intro u₀
  have hopen : IsOpen {u : ℂ | |u.im - u₀.im| < Real.pi / 3} :=
    isOpen_lt ((continuous_abs.comp (Complex.continuous_im.sub continuous_const))) continuous_const
  have hmem : u₀ ∈ {u : ℂ | |u.im - u₀.im| < Real.pi / 3} := by
    simp only [Set.mem_ofPred_eq, sub_self, abs_zero]; linarith [Real.pi_pos]
  have hdiff : DifferentiableAt ℂ (J_strip u₀.im) u₀ :=
    (differentiableOn_J_strip u₀.im).differentiableAt (hopen.mem_nhds hmem)
  have heq : I_entire =ᶠ[𝓝 u₀] J_strip u₀.im := by
    filter_upwards [hopen.mem_nhds hmem] with u hu
    exact J_strip_eq_of_overlap (by simp; linarith [Real.pi_pos]) hu
  exact hdiff.congr_of_eventuallyEq heq

/-- **Exact Agreement with `I_plus` on all of `ℝ`**: `I_entire (u : ℂ) = I_plus u`! -/
theorem I_entire_ofReal (u : ℝ) : I_entire (u : ℂ) = I_plus u := by
  have h1 : |((u : ℂ)).im - 0| < Real.pi / 3 := by simp; linarith [Real.pi_pos]
  have h2 : |((u : ℂ)).im - (-1 / 4 : ℝ)| < Real.pi / 3 := by
    simp only [Complex.ofReal_im, zero_sub, abs_neg]
    rw [abs_of_neg (by norm_num : (-1 / 4 : ℝ) < 0)]
    linarith [Real.pi_gt_three]
  have hstrip : I_entire (u : ℂ) = J_strip (-1 / 4) (u : ℂ) := by
    dsimp only [I_entire]; simp only [Complex.ofReal_im]
    exact J_strip_eq_of_overlap h1 h2
  rw [hstrip]
  dsimp only [J_strip]
  rw [intervalIntegral.integral_same, mul_zero, add_zero]
  -- Glue `Set.Iic 1` and `Set.Ici 1` to `∫ s : ℝ, valleyIntegrand u (s - i/4)`!
  have hvp : ∀ s : ℝ, (s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I = PakNthPrimeStokes.valleyPoint (-1) s (1 / 4) := by
    intro s; dsimp only [PakNthPrimeStokes.valleyPoint]; push_cast; ring
  have hint_left : IntegrableOn (fun s : ℝ => valleyIntegrand (u : ℂ) ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I))
      (Set.Iic 1) := by
    obtain ⟨K_L, _, hEi_L⟩ := norm_Ei_add_I_pi_left_le
    have hcont : Continuous (fun s : ℝ => valleyIntegrand (u : ℂ) ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) :=
      (differentiableOn_valleyIntegrand_w (u : ℂ)).continuousOn.comp_continuous
        (Complex.continuous_ofReal.add continuous_const) fun s => Or.inr (by simp)
    refine ((integrableOn_exp_Iic 1).const_mul (Real.exp (-u + Real.exp (-u) * K_L))).mono'
      hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
    dsimp only [valleyIntegrand]
    rw [Complex.norm_exp]
    have hprod : ‖Complex.exp (-(u : ℂ)) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
        Real.exp (-u) * K_L := by
      rw [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
      exact mul_le_mul_of_nonneg_left (hEi_L s hs) (Real.exp_pos _).le
    have h1' := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
    have harg : (((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) - (u : ℂ) -
          Complex.exp (-(u : ℂ)) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))).re ≤
        (-u + Real.exp (-u) * K_L) + s := by
      rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
      linarith
    exact (Real.exp_le_exp.mpr harg).trans (le_of_eq (Real.exp_add _ _))
  have hint_right : IntegrableOn (fun s : ℝ => valleyIntegrand (u : ℂ) ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I))
      (Set.Ici 1) :=
    integrableOn_valleyIntegrand_right (by rw [abs_sub_comm]; exact h2.le)
  have hint_ioi : IntegrableOn (fun s : ℝ => valleyIntegrand (u : ℂ) ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I))
      (Set.Ioi 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mp hint_right
  have hglue : (∫ s in Set.Iic (1 : ℝ), valleyIntegrand (u : ℂ) ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) +
      (∫ s in Set.Ici (1 : ℝ), valleyIntegrand (u : ℂ) ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) =
      ∫ s : ℝ, valleyIntegrand (u : ℂ) ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hdisj : Disjoint (Set.Iic (1 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      Set.disjoint_left.mpr fun _ h1' h2' => not_lt_of_ge h1' h2'
    have hunion : Set.Iic (1 : ℝ) ∪ Set.Ioi (1 : ℝ) = Set.univ := Set.Iic_union_Ioi
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_left hint_ioi, hunion,
      MeasureTheory.setIntegral_univ]
  rw [hglue]
  -- Match with `PakNthPrimeStokes.I_contour_eq_J_valley`!
  change _ = PakNthPrimeStokes.I_contour (-1) u (1 / 4)
  rw [PakNthPrimeStokes.I_contour_eq_J_valley (σ := -1) (Or.inl rfl) u (by norm_num) (by norm_num)]
  dsimp only [PakNthPrimeStokes.J_valley]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  rw [hvp s]
  dsimp only [valleyIntegrand]
  have hexpu : ((Real.exp (-u) : ℝ) : ℂ) = Complex.exp (-(u : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  rw [hexpu, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- **Convex Half-Plane Holomorphic Primitive**: if `f` is holomorphic on an open `Ω ⊆ ℂ`
containing all closed axis-aligned rectangles between any two points of `Ω` (such as `{Im w < 0}`
or `{0 < Re w}`), then the L-shaped integral
`F(z) = ∫_{z₀.re}^{z.re} f(s + i z₀.im) ds + i ∫_{z₀.im}^{z.im} f(z.re + i t) dt`
satisfies `HasDerivAt F (f z) z` for every `z ∈ Ω`! -/
theorem hasDerivAt_halfplanePrimitive {Ω : Set ℂ} (hΩ : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hrect : ∀ a ∈ Ω, ∀ b ∈ Ω, Set.uIcc a.re b.re ×ℂ Set.uIcc a.im b.im ⊆ Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) :
    let F : ℂ → ℂ := fun z =>
      (∫ s in z₀.re..z.re, f ((s : ℂ) + (z₀.im : ℂ) * I)) +
      I * (∫ t in z₀.im..z.im, f ((z.re : ℂ) + (t : ℂ) * I))
    ∀ z ∈ Ω, HasDerivAt F (f z) z := by
  intro F z hz
  have hdiff_eq : ∀ w ∈ Ω,
      F w - F z =
        (∫ s in z.re..w.re, f ((s : ℂ) + (z.im : ℂ) * I)) +
        I * (∫ t in z.im..w.im, f ((w.re : ℂ) + (t : ℂ) * I)) := by
    intro w hw
    let z₁ : ℂ := (z.re : ℂ) + (z₀.im : ℂ) * I
    let w₁ : ℂ := (w.re : ℂ) + (z.im : ℂ) * I
    have hz₁ : z₁ ∈ Ω := hrect z₀ hz₀ z hz ⟨by simp [z₁], by simp [z₁]⟩
    have hw₁ : w₁ ∈ Ω := hrect z hz w hw ⟨by simp [w₁], by simp [w₁]⟩
    have hsub := hrect z₁ hz₁ w₁ hw₁
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z₁ w₁ (hf.mono hsub)
    have hz₁_re : z₁.re = z.re := by simp [z₁]
    have hz₁_im : z₁.im = z₀.im := by simp [z₁]
    have hw₁_re : w₁.re = w.re := by simp [w₁]
    have hw₁_im : w₁.im = z.im := by simp [w₁]
    rw [hz₁_re, hz₁_im, hw₁_re, hw₁_im] at hcauchy
    simp only [smul_eq_mul] at hcauchy
    have hcont_h : ∀ (a b : ℂ), a ∈ Ω → b ∈ Ω →
        ContinuousOn (fun s : ℝ => f ((s : ℂ) + (a.im : ℂ) * I)) (Set.uIcc a.re b.re) := by
      intro a b ha hb
      refine hf.continuousOn.comp (Complex.continuous_ofReal.add continuous_const).continuousOn ?_
      intro s hs
      exact hrect a ha b hb ⟨by simpa using hs, by simp⟩
    have hcont_v : ∀ (a b : ℂ), a ∈ Ω → b ∈ Ω →
        ContinuousOn (fun t : ℝ => f ((b.re : ℂ) + (t : ℂ) * I)) (Set.uIcc a.im b.im) := by
      intro a b ha hb
      refine hf.continuousOn.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
      intro t ht
      exact hrect a ha b hb ⟨by simp, by simpa using ht⟩
    have hcont_h2 : ContinuousOn (fun s : ℝ => f ((s : ℂ) + (z₀.im : ℂ) * I)) (Set.uIcc z.re w.re) := by
      simpa [hz₁_re, hz₁_im, hw₁_re] using hcont_h z₁ w₁ hz₁ hw₁
    have hcont_v1 : ContinuousOn (fun t : ℝ => f ((w.re : ℂ) + (t : ℂ) * I)) (Set.uIcc z₀.im z.im) := by
      simpa [hz₁_im, hw₁_re, hw₁_im] using hcont_v z₁ w₁ hz₁ hw₁
    have h1 : (∫ s in z₀.re..z.re, f ((s : ℂ) + (z₀.im : ℂ) * I)) +
        (∫ s in z.re..w.re, f ((s : ℂ) + (z₀.im : ℂ) * I)) =
        ∫ s in z₀.re..w.re, f ((s : ℂ) + (z₀.im : ℂ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont_h z₀ z hz₀ hz).intervalIntegrable hcont_h2.intervalIntegrable
    have h2 : (∫ t in z₀.im..z.im, f ((w.re : ℂ) + (t : ℂ) * I)) +
        (∫ t in z.im..w.im, f ((w.re : ℂ) + (t : ℂ) * I)) =
        ∫ t in z₀.im..w.im, f ((w.re : ℂ) + (t : ℂ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        hcont_v1.intervalIntegrable (hcont_v z w hz hw).intervalIntegrable
    dsimp only [F]
    linear_combination -h1 - I * h2 + hcauchy
  -- Prove `HasDerivAt F (f z) z` via `hasDerivAt_iff_isLittleO`!
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hcont_z : ContinuousAt f z := (hf.differentiableAt (hΩ.mem_nhds hz)).continuousAt
  have hnhds_f : ∀ᶠ p in 𝓝 z, ‖f p - f z‖ ≤ c / 2 := by
    have h := hcont_z.eventually (Metric.ball_mem_nhds (f z) (half_pos hc))
    exact h.mono fun p hp => le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hp)
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.eventually_nhds_iff.mp (hnhds_f.and (hΩ.mem_nhds hz))
  refine Metric.eventually_nhds_iff.mpr ⟨δ / 2, half_pos hδ_pos, fun w hw => ?_⟩
  have hw_lt : ‖w - z‖ < δ / 2 := by simpa [dist_eq_norm] using hw
  have hwΩ : w ∈ Ω := (hδ_sub (by rw [dist_eq_norm]; linarith)).2
  rw [hdiff_eq w hwΩ]
  have hlin_h : ∫ _s in z.re..w.re, f z = ((w.re - z.re : ℝ) : ℂ) * f z := by
    rw [intervalIntegral.integral_const, Complex.real_smul]
  have hlin_v : ∫ _t in z.im..w.im, f z = ((w.im - z.im : ℝ) : ℂ) * f z := by
    rw [intervalIntegral.integral_const, Complex.real_smul]
  have hfz_split : f z * (w - z) =
      (∫ _s in z.re..w.re, f z) + I * (∫ _t in z.im..w.im, f z) := by
    rw [hlin_h, hlin_v]
    have hwz : w - z = ((w.re - z.re : ℝ) : ℂ) + I * ((w.im - z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hwz]; ring
  have hcont_h : ContinuousOn (fun s : ℝ => f ((s : ℂ) + (z.im : ℂ) * I)) (Set.uIcc z.re w.re) := by
    refine hf.continuousOn.comp (Complex.continuous_ofReal.add continuous_const).continuousOn ?_
    intro s hs; exact hrect z hz w hwΩ ⟨by simpa using hs, by simp⟩
  have hcont_v : ContinuousOn (fun t : ℝ => f ((w.re : ℂ) + (t : ℂ) * I)) (Set.uIcc z.im w.im) := by
    refine hf.continuousOn.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
    intro t ht; exact hrect z hz w hwΩ ⟨by simp, by simpa using ht⟩
  have hsub_eq : ((∫ s in z.re..w.re, f ((s : ℂ) + (z.im : ℂ) * I)) +
        I * (∫ t in z.im..w.im, f ((w.re : ℂ) + (t : ℂ) * I))) - f z * (w - z) =
      (∫ s in z.re..w.re, (f ((s : ℂ) + (z.im : ℂ) * I) - f z)) +
      I * (∫ t in z.im..w.im, (f ((w.re : ℂ) + (t : ℂ) * I) - f z)) := by
    rw [hfz_split, intervalIntegral.integral_sub hcont_h.intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_sub hcont_v.intervalIntegrable intervalIntegrable_const]
    ring
  rw [smul_eq_mul, mul_comm (w - z), hsub_eq]
  have hbd_h : ‖∫ s in z.re..w.re, (f ((s : ℂ) + (z.im : ℂ) * I) - f z)‖ ≤ (c / 2) * |w.re - z.re| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hs_mem := Set.uIoc_subset_uIcc hs
    have hdist : ‖((s : ℂ) + (z.im : ℂ) * I) - z‖ < δ := by
      have heq : ((s : ℂ) + (z.im : ℂ) * I) - z = ((s - z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      have habs : |s - z.re| ≤ |w.re - z.re| := by
        rcases Set.mem_uIcc.mp hs_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by simpa using Complex.abs_re_le_norm (w - z)
      linarith
    exact (hδ_sub (by rwa [dist_eq_norm])).1
  have hbd_v : ‖∫ t in z.im..w.im, (f ((w.re : ℂ) + (t : ℂ) * I) - f z)‖ ≤ (c / 2) * |w.im - z.im| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    have ht_mem := Set.uIoc_subset_uIcc ht
    have hdist : ‖((w.re : ℂ) + (t : ℂ) * I) - z‖ < δ := by
      have hre : |w.re - z.re| ≤ ‖w - z‖ := by simpa using Complex.abs_re_le_norm (w - z)
      have him : |t - z.im| ≤ |w.im - z.im| := by
        rcases Set.mem_uIcc.mp ht_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have him_le : |w.im - z.im| ≤ ‖w - z‖ := by simpa using Complex.abs_im_le_norm (w - z)
      have htri : ‖((w.re : ℂ) + (t : ℂ) * I) - z‖ ≤ |w.re - z.re| + |t - z.im| := by
        have heq : ((w.re : ℂ) + (t : ℂ) * I) - z = ((w.re - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I := by
          apply Complex.ext <;> simp
        rw [heq]
        calc _ ≤ ‖((w.re - z.re : ℝ) : ℂ)‖ + ‖((t - z.im : ℝ) : ℂ) * I‖ := norm_add_le _ _
          _ = |w.re - z.re| + |t - z.im| := by
              rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
                Real.norm_eq_abs, Real.norm_eq_abs]
      linarith
    exact (hδ_sub (by rwa [dist_eq_norm])).1
  have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by simpa using Complex.abs_re_le_norm (w - z)
  have him_le : |w.im - z.im| ≤ ‖w - z‖ := by simpa using Complex.abs_im_le_norm (w - z)
  calc _ ≤ ‖∫ s in z.re..w.re, (f ((s : ℂ) + (z.im : ℂ) * I) - f z)‖ +
        ‖I * ∫ t in z.im..w.im, (f ((w.re : ℂ) + (t : ℂ) * I) - f z)‖ := norm_add_le _ _
    _ = ‖∫ s in z.re..w.re, (f ((s : ℂ) + (z.im : ℂ) * I) - f z)‖ +
          ‖∫ t in z.im..w.im, (f ((w.re : ℂ) + (t : ℂ) * I) - f z)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (c / 2) * |w.re - z.re| + (c / 2) * |w.im - z.im| := add_le_add hbd_h hbd_v
    _ ≤ (c / 2) * ‖w - z‖ + (c / 2) * ‖w - z‖ := by nlinarith
    _ = c * ‖w - z‖ := by ring

/-! #### 4b. Contour Deformation to `w_plus` and Unified Truncated Convolution on `Σ₀` -/

/-- Corollary of `hasDerivAt_halfplanePrimitive`: on any open set `Ω` closed under axis-aligned
rectangles, the line integral of a holomorphic `f` along any `C¹` curve `γ : [a, b] → Ω` equals
the L-shaped integral from `γ a` to `γ b`! -/
theorem integral_curve_eq_L_path {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hrect : ∀ p ∈ Ω, ∀ q ∈ Ω, Set.uIcc p.re q.re ×ℂ Set.uIcc p.im q.im ⊆ Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    {a b : ℝ} {γ γ' : ℝ → ℂ}
    (hγ_mem : ∀ x ∈ Set.uIcc a b, γ x ∈ Ω)
    (hγ_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt γ (γ' x) x)
    (hγ'_cont : ContinuousOn γ' (Set.uIcc a b)) :
    ∫ x in a..b, f (γ x) * γ' x =
      (∫ s in (γ a).re..(γ b).re, f ((s : ℂ) + ((γ a).im : ℂ) * I)) +
      I * (∫ t in (γ a).im..(γ b).im, f (((γ b).re : ℂ) + (t : ℂ) * I)) := by
  have ha_mem : γ a ∈ Ω := hγ_mem a Set.left_mem_uIcc
  let F : ℂ → ℂ := fun z =>
    (∫ s in (γ a).re..z.re, f ((s : ℂ) + ((γ a).im : ℂ) * I)) +
    I * (∫ t in (γ a).im..z.im, f ((z.re : ℂ) + (t : ℂ) * I))
  have hF_deriv : ∀ z ∈ Ω, HasDerivAt F (f z) z :=
    hasDerivAt_halfplanePrimitive hΩ ha_mem hrect hf
  have hcomp_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun τ => F (γ τ)) (f (γ x) * γ' x) x :=
    fun x hx => (hF_deriv (γ x) (hγ_mem x hx)).comp x (hγ_deriv x hx)
  have hγ_cont : ContinuousOn γ (Set.uIcc a b) :=
    fun x hx => (hγ_deriv x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun x => f (γ x) * γ' x) (Set.uIcc a b) :=
    (hf.continuousOn.comp hγ_cont hγ_mem).mul hγ'_cont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hcomp_deriv hcont.intervalIntegrable
  have hFa : F (γ a) = 0 := by simp [F]
  rw [hFa, sub_zero] at hftc
  exact hftc

/-- Exact FTC / integration-by-parts identity along `x ↦ w_plus (u + x)` on `V_dom`:
`∫_a^b valleyIntegrand u (w_plus (u + x)) * S_phi (w_plus (u + x)) dx`
`= (valleyIntegrand u (w_plus (u + b)) - valleyIntegrand u (w_plus (u + a)))`
`  + ∫_a^b exp(2x - exp x) * F_plus (u + x) dx`! -/
theorem integral_valleyIntegrand_w_plus_eq {u : ℂ} {a b : ℝ}
    (hdom : ∀ x ∈ Set.uIcc a b, u + (x : ℂ) ∈ V_dom) :
    ∫ x in a..b, valleyIntegrand u (w_plus (u + (x : ℂ))) * S_phi (w_plus (u + (x : ℂ))) =
      (valleyIntegrand u (w_plus (u + (b : ℂ))) - valleyIntegrand u (w_plus (u + (a : ℂ)))) +
      ∫ x in a..b, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)) := by
  let g : ℝ → ℂ := fun x => valleyIntegrand u (w_plus (u + (x : ℂ)))
  let g' : ℝ → ℂ := fun x =>
    valleyIntegrand u (w_plus (u + (x : ℂ))) * S_phi (w_plus (u + (x : ℂ))) -
    ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x := by
    intro x hx
    have hv : u + (x : ℂ) ∈ V_dom := hdom x hx
    obtain ⟨hcb, _⟩ := w_plus_spec hv
    obtain ⟨hw_mem, hdw, _, _⟩ := closedBall_log_props hv hcb
    have hw_slit : w_plus (u + (x : ℂ)) ∈ Complex.slitPlane := OmegaPhi_subset_slitPlane hw_mem
    have hw0 : w_plus (u + (x : ℂ)) ≠ 0 := Complex.slitPlane_ne_zero hw_slit
    have hS0 : S_phi (w_plus (u + (x : ℂ))) ≠ 0 := by
      have h1 := norm_S_phi_sub_one_le hw_mem
      have hden : 128 ≤ distPhi (w_plus (u + (x : ℂ))) * Real.cos phiRay ^ 2 := by
        nlinarith [C_v_mul_cos_sq, pow_pos cos_phiRay_pos 2]
      have hS1 := h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hden)
      intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hS1; linarith
    have hlin : HasDerivAt (fun τ : ℝ => u + (τ : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_add u
    have hw_d : HasDerivAt (fun τ : ℝ => w_plus (u + (τ : ℂ))) (S_phi (w_plus (u + (x : ℂ)))) x := by
      exact ((hasDerivAt_w_plus hv).comp x hlin).congr_deriv (mul_one _)
    have hg_d := (hasDerivAt_valleyIntegrand_w (u := u) hw_slit).comp x hw_d
    refine hg_d.congr_deriv ?_
    -- Show `(exp(-u) * (exp w / w)) * g x * S_phi w = exp(2x - exp x) * F_plus (u + x)`!
    have hEi := Ei_add_I_pi_w_plus hv
    have hF := F_plus_eq_exp_sub hv
    have hg_val : valleyIntegrand u (w_plus (u + (x : ℂ))) =
        F_plus (u + (x : ℂ)) * Complex.exp ((x : ℂ) - Complex.exp (x : ℂ)) := by
      dsimp only [valleyIntegrand]
      rw [hEi, hF]
      have hexp_x : Complex.exp (-u) * Complex.exp (u + (x : ℂ)) = Complex.exp (x : ℂ) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [hexp_x, ← Complex.exp_add]; congr 1; ring
    have hexp_w : Complex.exp (-u) * Complex.exp (w_plus (u + (x : ℂ))) =
        Complex.exp (x : ℂ) * F_plus (u + (x : ℂ)) := by
      rw [hF, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have hF_def : F_plus (u + (x : ℂ)) = w_plus (u + (x : ℂ)) / S_phi (w_plus (u + (x : ℂ))) := rfl
    have hreal_exp : ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) =
        Complex.exp ((x : ℂ) - Complex.exp (x : ℂ)) * Complex.exp (x : ℂ) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]; push_cast; congr 1; ring
    dsimp only [g']
    have hkey : Complex.exp (-u) * (Complex.exp (w_plus (u + (x : ℂ))) / w_plus (u + (x : ℂ))) *
          valleyIntegrand u (w_plus (u + (x : ℂ))) * S_phi (w_plus (u + (x : ℂ))) =
        ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)) := by
      have h1 : Complex.exp (-u) * (Complex.exp (w_plus (u + (x : ℂ))) / w_plus (u + (x : ℂ))) =
          (Complex.exp (x : ℂ) * F_plus (u + (x : ℂ))) / w_plus (u + (x : ℂ)) := by
        rw [← mul_div_assoc, hexp_w]
      rw [h1, hg_val, hreal_exp]
      have hcancel : F_plus (u + (x : ℂ)) * S_phi (w_plus (u + (x : ℂ))) = w_plus (u + (x : ℂ)) := by
        rw [hF_def]; exact div_mul_cancel₀ _ hS0
      calc Complex.exp (x : ℂ) * F_plus (u + (x : ℂ)) / w_plus (u + (x : ℂ)) *
            (F_plus (u + (x : ℂ)) * Complex.exp ((x : ℂ) - Complex.exp (x : ℂ))) *
            S_phi (w_plus (u + (x : ℂ)))
          = (Complex.exp ((x : ℂ) - Complex.exp (x : ℂ)) * Complex.exp (x : ℂ)) * F_plus (u + (x : ℂ)) *
              ((F_plus (u + (x : ℂ)) * S_phi (w_plus (u + (x : ℂ)))) / w_plus (u + (x : ℂ))) := by ring
        _ = (Complex.exp ((x : ℂ) - Complex.exp (x : ℂ)) * Complex.exp (x : ℂ)) * F_plus (u + (x : ℂ)) := by
            rw [hcancel, div_self hw0, mul_one]
    linear_combination -hkey
  have hcont_v : ContinuousOn (fun x : ℝ => u + (x : ℂ)) (Set.uIcc a b) :=
    (continuous_const.add Complex.continuous_ofReal).continuousOn
  have hcont_w : ContinuousOn (fun x : ℝ => w_plus (u + (x : ℂ))) (Set.uIcc a b) :=
    differentiableOn_w_plus.continuousOn.comp hcont_v hdom
  have hw_maps : Set.MapsTo (fun x : ℝ => w_plus (u + (x : ℂ))) (Set.uIcc a b) OmegaPhi :=
    fun x hx => (closedBall_log_props (hdom x hx) (w_plus_spec (hdom x hx)).1).1
  have hcont1 : ContinuousOn (fun x : ℝ => valleyIntegrand u (w_plus (u + (x : ℂ))) * S_phi (w_plus (u + (x : ℂ))))
      (Set.uIcc a b) :=
    ((differentiableOn_valleyIntegrand_w u).continuousOn.comp hcont_w
      (fun x hx => OmegaPhi_subset_slitPlane (hw_maps hx))).mul
      (differentiableOn_S_phi.continuousOn.comp hcont_w hw_maps)
  have hcont2 : ContinuousOn (fun x : ℝ => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))
      (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub Real.continuous_exp))).continuousOn.mul
      (differentiableOn_F_plus.continuousOn.comp hcont_v hdom)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont1.sub hcont2).intervalIntegrable
  rw [intervalIntegral.integral_sub hcont1.intervalIntegrable hcont2.intervalIntegrable] at hftc
  dsimp only [g] at hftc
  linear_combination hftc

/-- Asymptotic behavior of `w_plus (u + x)` as `x → +∞`: `u + x ∈ V_sec`, `(w_plus (u + x)).re → +∞`,
and `(w_plus (u + x)).im → u.im`! -/
lemma tendsto_w_plus_add_real (u : ℂ) :
    (∀ᶠ x : ℝ in atTop, u + (x : ℂ) ∈ V_sec) ∧
    Tendsto (fun x : ℝ => (w_plus (u + (x : ℂ))).re) atTop atTop ∧
    Tendsto (fun x : ℝ => (w_plus (u + (x : ℂ))).im) atTop (𝓝 u.im) := by
  have hv_mem : ∀ᶠ x : ℝ in atTop, u + (x : ℂ) ∈ V_sec := by
    filter_upwards [Filter.eventually_ge_atTop (max (R_sec + |u.re| + 1) (2 * |u.im| / Real.sin deltaV + |u.re| + 1))]
      with x hx
    have hre : R_sec + 1 ≤ (u + (x : ℂ)).re := by
      have h1 : R_sec + |u.re| + 1 ≤ x := le_trans (le_max_left _ _) hx
      simp only [Complex.add_re, Complex.ofReal_re]; linarith [neg_abs_le u.re]
    have hre_pos : 0 < (u + (x : ℂ)).re := by linarith [R_sec_pos]
    have hnorm : R_sec ≤ ‖u + (x : ℂ)‖ := (by linarith : R_sec ≤ (u + (x : ℂ)).re).trans (Complex.re_le_norm _)
    have harg_half : |Complex.arg (u + (x : ℂ))| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
    have harg_le : |Complex.arg (u + (x : ℂ))| ≤ deltaV := by
      have h2 : 2 * |u.im| / Real.sin deltaV + |u.re| + 1 ≤ x := le_trans (le_max_right _ _) hx
      have hre2 : 2 * |u.im| / Real.sin deltaV ≤ (u + (x : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re]; linarith [neg_abs_le u.re]
      have hsin_le : Real.sin |Complex.arg (u + (x : ℂ))| ≤ Real.sin deltaV := by
        have heq : Real.sin |Complex.arg (u + (x : ℂ))| = |Real.sin (Complex.arg (u + (x : ℂ)))| := by
          rcases le_total 0 (Complex.arg (u + (x : ℂ))) with h | h
          · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (Complex.arg_le_pi _))]
          · rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
              (le_of_lt (Complex.neg_pi_lt_arg _)))]
        rw [heq]
        have him : |(u + (x : ℂ)).im| = ‖u + (x : ℂ)‖ * |Real.sin (Complex.arg (u + (x : ℂ)))| := by
          rw [← Complex.norm_mul_sin_arg, abs_mul, abs_of_nonneg (norm_nonneg _)]
        have him_eq : |(u + (x : ℂ)).im| = |u.im| := by simp
        have hnorm_ge : 2 * |u.im| / Real.sin deltaV ≤ ‖u + (x : ℂ)‖ := hre2.trans (Complex.re_le_norm _)
        have hmul : 2 * |u.im| ≤ ‖u + (x : ℂ)‖ * Real.sin deltaV := by
          rwa [div_le_iff₀ sin_deltaV_pos] at hnorm_ge
        have hnorm_pos : 0 < ‖u + (x : ℂ)‖ := lt_of_lt_of_le R_sec_pos hnorm
        nlinarith [abs_nonneg u.im, sin_deltaV_pos]
      by_contra hgt
      push Not at hgt
      have hstrict := Real.strictMonoOn_sin
        ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
        ⟨by linarith [abs_nonneg (Complex.arg (u + (x : ℂ))), Real.pi_pos], harg_half.le⟩ hgt
      linarith
    have hlo : -Real.pi + 2 * deltaV ≤ Complex.arg (u + (x : ℂ)) := by
      have := (abs_le.mp harg_le).1; dsimp [deltaV] at this ⊢; linarith [Real.pi_pos]
    have hhi : Complex.arg (u + (x : ℂ)) ≤ phiRay - 2 * deltaV := by
      have := (abs_le.mp harg_le).2; dsimp [phiRay, deltaV] at this ⊢; linarith [Real.pi_pos]
    exact ⟨hnorm, hlo, hhi⟩
  -- `(w_plus (u + x)).re → +∞`
  have hre_top : Tendsto (fun x : ℝ => (w_plus (u + (x : ℂ))).re) atTop atTop := by
    refine tendsto_atTop_mono' atTop (f₁ := fun x : ℝ => u.re + x - 1) ?_ ?_
    · filter_upwards [hv_mem] with x hx
      have hv_dom := V_sec_subset_V_dom hx
      have hcb := (w_plus_spec hv_dom).1
      rw [Metric.mem_closedBall, dist_eq_norm] at hcb
      have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm _).trans hcb)).1
      have hlog_nn : 0 ≤ (Complex.log (u + (x : ℂ))).re := by
        rw [Complex.log_re]; exact Real.log_nonneg (by linarith [R_sec_ge_1e14.trans hx.1])
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hre_diff
      linarith
    · have h : (fun x : ℝ => u.re + x - 1) = fun x => x + (u.re - 1) := funext fun x => by ring
      rw [h]; exact tendsto_id.atTop_add tendsto_const_nhds
  -- `(w_plus (u + x)).im → u.im` using `w_plus_sub_hasGev1Exp` at `N = 2`!
  have him_lim : Tendsto (fun x : ℝ => (w_plus (u + (x : ℂ))).im) atTop (𝓝 u.im) := by
    obtain ⟨_, Cw, hCw, Aw, hAw, _, hw_rem⟩ := w_plus_sub_hasGev1Exp
    have hnorm_top : Tendsto (fun x : ℝ => ‖u + (x : ℂ)‖) atTop atTop := by
      refine tendsto_atTop_mono' atTop (f₁ := fun x : ℝ => x + u.re) ?_
        (tendsto_id.atTop_add tendsto_const_nhds)
      filter_upwards with x
      have : x + u.re = (u + (x : ℂ)).re := by simp; ring
      rw [this]; exact Complex.re_le_norm _
    -- 1. `Complex.arg (u + x) → 0`
    have harg0 : Tendsto (fun x : ℝ => Complex.arg (u + (x : ℂ))) atTop (𝓝 0) := by
      have hev : (fun x : ℝ => Complex.arg (u + (x : ℂ))) =ᶠ[atTop]
          fun x : ℝ => Real.arcsin (u.im / ‖u + (x : ℂ)‖) := by
        filter_upwards [Filter.eventually_ge_atTop (|u.re| + 1)] with x hx
        have hre : 0 ≤ (u + (x : ℂ)).re := by
          simp only [Complex.add_re, Complex.ofReal_re]; linarith [neg_abs_le u.re]
        unfold Complex.arg
        simp only [hre, ↓reduceIte, Complex.add_im, Complex.ofReal_im, add_zero]
      refine Tendsto.congr' hev.symm ?_
      have hdiv0 : Tendsto (fun x : ℝ => u.im / ‖u + (x : ℂ)‖) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hnorm_top
      have hcomp := (Real.continuous_arcsin.tendsto 0).comp hdiv0
      simpa [Function.comp_def, Real.arcsin_zero] using hcomp
    -- 2. `‖w_plus (u + x) - (u + x) - Complex.log (u + x)‖ → 0` via `w_plus_sub_hasGev1Exp` at `N = 2`!
    have hrem0 : Tendsto (fun x : ℝ => ‖w_plus (u + (x : ℂ)) - (u + (x : ℂ)) - Complex.log (u + (x : ℂ))‖)
        atTop (𝓝 0) := by
      have hsqrt_top : Tendsto (fun x : ℝ => Real.sqrt ‖u + (x : ℂ)‖) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp hnorm_top
      let K : ℝ := 2 * Cw * Aw ^ 2 + 4000 * (2 + Real.pi)
      refine squeeze_zero' (g := fun x : ℝ => K / Real.sqrt ‖u + (x : ℂ)‖)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      · filter_upwards [hv_mem] with x hx
        set v : ℂ := u + (x : ℂ)
        have hv1 : 1 ≤ ‖v‖ := by linarith [R_sec_ge_1e14.trans hx.1]
        have hv_pos : 0 < ‖v‖ := by linarith
        have hsq_pos : 0 < Real.sqrt ‖v‖ := Real.sqrt_pos.mpr hv_pos
        have hsq_ge1 : 1 ≤ Real.sqrt ‖v‖ := Real.one_le_sqrt.mpr hv1
        have hsq_le : Real.sqrt ‖v‖ ≤ ‖v‖ := by
          have : Real.sqrt ‖v‖ * Real.sqrt ‖v‖ = ‖v‖ := Real.mul_self_sqrt hv_pos.le
          nlinarith
        have hrem2 := hw_rem 2 v hx
        have hrem2' : ‖(w_plus v - v - Complex.log v) - evalTrunc wCoeff 2 v‖ ≤
            (2 * Cw * Aw ^ 2) / Real.sqrt ‖v‖ := by
          have h1 : Cw * ‖v‖ * Aw ^ 2 * ((2 : ℕ).factorial : ℝ) / ‖v‖ ^ 2 = (2 * Cw * Aw ^ 2) / ‖v‖ := by
            norm_num [Nat.factorial]; field_simp [hv_pos.ne']
          rw [h1] at hrem2
          exact hrem2.trans (div_le_div_of_nonneg_left (by positivity) hsq_pos hsq_le)
        have hev2 : ‖evalTrunc wCoeff 2 v‖ ≤ (4000 * (2 + Real.pi)) / Real.sqrt ‖v‖ := by
          have hbig : 32000 * (2 : ℝ) ≤ ‖v‖ := by linarith [R_sec_ge_1e14.trans hx.1]
          -- Directly bound `evalTrunc wCoeff 2 v = evalTerm wCoeff 1 v`!
          have heq2 : evalTrunc wCoeff 2 v = evalTerm wCoeff 1 v := by
            simp [evalTrunc, Finset.sum_range_succ, evalTerm, wCoeff_zero]
          rw [heq2]
          dsimp only [evalTerm]
          rw [norm_div, pow_one, Finset.sum_range_succ, Finset.sum_range_one]
          have h0 := wCoeff_gevBound.2 1 0 (by omega)
          have h1 := wCoeff_gevBound.2 1 1 (by omega)
          norm_num [Nat.factorial] at h0 h1
          have hlog_v : ‖Complex.log v‖ ≤ 2 * Real.sqrt ‖v‖ + Real.pi := by
            have hlog_sq : Real.log ‖v‖ ≤ 2 * Real.sqrt ‖v‖ := by
              have h := Real.log_le_sub_one_of_pos hsq_pos
              have hsq : Real.log ‖v‖ = 2 * Real.log (Real.sqrt ‖v‖) := by
                rw [Real.log_sqrt hv_pos.le]; ring
              linarith
            rw [Complex.log]
            calc ‖(Real.log ‖v‖ : ℂ) + (Complex.arg v : ℂ) * I‖
                ≤ ‖(Real.log ‖v‖ : ℂ)‖ + ‖(Complex.arg v : ℂ) * I‖ := norm_add_le _ _
              _ = Real.log ‖v‖ + |Complex.arg v| := by
                  rw [Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hv1),
                    norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
              _ ≤ 2 * Real.sqrt ‖v‖ + Real.pi := add_le_add hlog_sq (Complex.abs_arg_le_pi v)
          have hnum : ‖wCoeff 1 0 * Complex.log v ^ 0 + wCoeff 1 1 * Complex.log v ^ 1‖ ≤
              4000 * (2 + Real.pi) * Real.sqrt ‖v‖ := by
            calc _ ≤ ‖wCoeff 1 0 * Complex.log v ^ 0‖ + ‖wCoeff 1 1 * Complex.log v ^ 1‖ := norm_add_le _ _
              _ = ‖wCoeff 1 0‖ + ‖wCoeff 1 1‖ * ‖Complex.log v‖ := by simp
              _ ≤ 500 + 500 * (2 * Real.sqrt ‖v‖ + Real.pi) := by gcongr
              _ ≤ 4000 * (2 + Real.pi) * Real.sqrt ‖v‖ := by nlinarith [Real.pi_pos]
          calc _ ≤ (4000 * (2 + Real.pi) * Real.sqrt ‖v‖) / ‖v‖ :=
                div_le_div_of_nonneg_right hnum hv_pos.le
            _ = (4000 * (2 + Real.pi)) / Real.sqrt ‖v‖ := by
                have hdiv : Real.sqrt ‖v‖ / ‖v‖ = 1 / Real.sqrt ‖v‖ := by
                  rw [div_eq_div_iff hv_pos.ne' hsq_pos.ne', one_mul]
                  exact Real.mul_self_sqrt hv_pos.le
                rw [mul_div_assoc, hdiv, mul_one_div]
        have htri : ‖w_plus v - v - Complex.log v‖ ≤
            ‖(w_plus v - v - Complex.log v) - evalTrunc wCoeff 2 v‖ + ‖evalTrunc wCoeff 2 v‖ := by
          simpa using norm_add_le ((w_plus v - v - Complex.log v) - evalTrunc wCoeff 2 v) (evalTrunc wCoeff 2 v)
        dsimp only [K]; rw [add_div]; linarith
      · exact tendsto_const_nhds.div_atTop hsqrt_top
    have him_diff : Tendsto (fun x : ℝ => (w_plus (u + (x : ℂ))).im - u.im) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun x : ℝ =>
          |Complex.arg (u + (x : ℂ))| + ‖w_plus (u + (x : ℂ)) - (u + (x : ℂ)) - Complex.log (u + (x : ℂ))‖)
        (fun x => ?_) ?_
      · have hsplit : (w_plus (u + (x : ℂ))).im - u.im =
            Complex.arg (u + (x : ℂ)) + (w_plus (u + (x : ℂ)) - (u + (x : ℂ)) - Complex.log (u + (x : ℂ))).im := by
          simp [Complex.log_im]
        rw [Real.norm_eq_abs, hsplit]
        exact (abs_add_le _ _).trans (add_le_add le_rfl (Complex.abs_im_le_norm _))
      · simpa using harg0.abs.add hrem0
    simpa using him_diff.add_const u.im
  exact ⟨hv_mem, hre_top, him_lim⟩

/-- Simple global bound on `Ei_complex (x + i y) + iπ` for `x ≥ 1` via 2-segment FTC! -/
lemma norm_Ei_complex_add_I_pi_le_exp {x y : ℝ} (hx : 1 ≤ x) :
    ‖Ei_complex ((x : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ)‖ ≤
      ‖Ei_complex (1 : ℂ)‖ + Real.pi + Real.exp 1 * |y| + Real.exp x := by
  -- Segment 1: vertical from `1` to `1 + i y`
  have h1 : ‖Ei_complex ((1 : ℂ) + (y : ℂ) * I) - Ei_complex (1 : ℂ)‖ ≤ Real.exp 1 * |y| := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) y,
        HasDerivAt (fun τ : ℝ => Ei_complex ((1 : ℂ) + (τ : ℂ) * I))
          (Complex.exp ((1 : ℂ) + (t : ℂ) * I) / ((1 : ℂ) + (t : ℂ) * I) * I) t := by
      intro t _
      have hslit : ((1 : ℂ) + (t : ℂ) * I) ∈ Complex.slitPlane := Or.inl (by simp)
      have hlin : HasDerivAt (fun τ : ℝ => (1 : ℂ) + (τ : ℂ) * I) I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add 1
      exact (PakNthPrimeStokes.hasDerivAt_Ei_complex hslit).comp t hlin
    have hcont : ContinuousOn (fun t : ℝ => Complex.exp ((1 : ℂ) + (t : ℂ) * I) / ((1 : ℂ) + (t : ℂ) * I) * I)
        (Set.uIcc (0 : ℝ) y) := by
      have hlin : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      refine ((Complex.continuous_exp.comp hlin).continuousOn.div hlin.continuousOn ?_).mul continuousOn_const
      intro t _; exact Complex.slitPlane_ne_zero (Or.inl (by simp))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hftc
    rw [← hftc]
    have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) y,
        ‖Complex.exp ((1 : ℂ) + (t : ℂ) * I) / ((1 : ℂ) + (t : ℂ) * I) * I‖ ≤ Real.exp 1 := by
      intro t _
      rw [norm_mul, Complex.norm_I, mul_one, norm_div, Complex.norm_exp]
      have hre : ((1 : ℂ) + (t : ℂ) * I).re = 1 := by simp
      have hnorm : 1 ≤ ‖(1 : ℂ) + (t : ℂ) * I‖ := by
        have := Complex.re_le_norm ((1 : ℂ) + (t : ℂ) * I); rwa [hre] at this
      rw [hre]; exact div_le_self (Real.exp_pos 1).le hnorm
    simpa [sub_zero, mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const hbd
  -- Segment 2: horizontal from `1 + i y` to `x + i y`
  have h2 : ‖Ei_complex ((x : ℂ) + (y : ℂ) * I) - Ei_complex ((1 : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp x := by
    have hderiv : ∀ s ∈ Set.uIcc (1 : ℝ) x,
        HasDerivAt (fun τ : ℝ => Ei_complex ((τ : ℂ) + (y : ℂ) * I))
          (Complex.exp ((s : ℂ) + (y : ℂ) * I) / ((s : ℂ) + (y : ℂ) * I)) s := by
      intro s hs
      rw [Set.uIcc_of_le hx] at hs
      have hslit : ((s : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := Or.inl (by simp; linarith [hs.1])
      have hlin : HasDerivAt (fun τ : ℝ => (τ : ℂ) + (y : ℂ) * I) 1 s := by
        simpa using (hasDerivAt_id s).ofReal_comp.add_const ((y : ℂ) * I)
      exact ((PakNthPrimeStokes.hasDerivAt_Ei_complex hslit).comp s hlin).congr_deriv (mul_one _)
    have hcont : ContinuousOn (fun s : ℝ => Complex.exp ((s : ℂ) + (y : ℂ) * I) / ((s : ℂ) + (y : ℂ) * I))
        (Set.uIcc (1 : ℝ) x) := by
      have hlin : Continuous (fun s : ℝ => (s : ℂ) + (y : ℂ) * I) :=
        Complex.continuous_ofReal.add continuous_const
      refine (Complex.continuous_exp.comp hlin).continuousOn.div hlin.continuousOn ?_
      intro s hs; rw [Set.uIcc_of_le hx] at hs
      exact Complex.slitPlane_ne_zero (Or.inl (by simp; linarith [hs.1]))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    simp only [Complex.ofReal_one] at hftc
    rw [← hftc]
    have hle := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun s : ℝ => Complex.exp ((s : ℂ) + (y : ℂ) * I) / ((s : ℂ) + (y : ℂ) * I)) hx
      (Filter.Eventually.of_forall fun s hs => by
        rw [norm_div, Complex.norm_exp]
        have hre : ((s : ℂ) + (y : ℂ) * I).re = s := by simp
        have hnorm : 1 ≤ ‖(s : ℂ) + (y : ℂ) * I‖ := by
          have := Complex.re_le_norm ((s : ℂ) + (y : ℂ) * I); rw [hre] at this; linarith [hs.1]
        rw [hre]; exact div_le_self (Real.exp_pos s).le hnorm)
      (Real.continuous_exp.intervalIntegrable (μ := volume) 1 x)
    rw [integral_exp] at hle
    linarith [Real.exp_pos 1]
  have hsplit : Ei_complex ((x : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ) =
      (Ei_complex ((x : ℂ) + (y : ℂ) * I) - Ei_complex ((1 : ℂ) + (y : ℂ) * I)) +
      (Ei_complex ((1 : ℂ) + (y : ℂ) * I) - Ei_complex (1 : ℂ)) +
      Ei_complex (1 : ℂ) + I * (Real.pi : ℂ) := by ring
  rw [hsplit]
  have hpi : ‖I * (Real.pi : ℂ)‖ = Real.pi := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have htri : ‖(Ei_complex ((x : ℂ) + (y : ℂ) * I) - Ei_complex ((1 : ℂ) + (y : ℂ) * I)) +
        (Ei_complex ((1 : ℂ) + (y : ℂ) * I) - Ei_complex (1 : ℂ)) +
        Ei_complex (1 : ℂ) + I * (Real.pi : ℂ)‖ ≤
      ‖Ei_complex ((x : ℂ) + (y : ℂ) * I) - Ei_complex ((1 : ℂ) + (y : ℂ) * I)‖ +
      ‖Ei_complex ((1 : ℂ) + (y : ℂ) * I) - Ei_complex (1 : ℂ)‖ +
      ‖Ei_complex (1 : ℂ)‖ + ‖I * (Real.pi : ℂ)‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  linarith [htri, h1, h2, hpi]

/-- Universal pointwise domination of the Gamma-log kernel `exp (2 x - exp x) * (M + |x|)`:
for all `x : ℝ` and `M ≥ 0`, `exp (2 x - exp x) * (M + |x|) ≤ exp 4 * (M + 2) * exp (-3 * |x| / 2)`! -/
lemma gamma_kernel_mul_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    Real.exp (2 * x - Real.exp x) * (M + |x|) ≤ Real.exp 4 * (M + 2) * Real.exp (-(3 / 2) * |x|) := by
  have habs_exp : |x| ≤ 2 * Real.exp (|x| / 2) := by
    have h1 := Real.add_one_le_exp (|x| / 2)
    linarith
  have hbase : 2 * x - Real.exp x ≤ 4 - 2 * |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      have h2 := Real.sum_le_exp_of_nonneg hx 3
      norm_num [Finset.sum_range_succ, Nat.factorial] at h2
      nlinarith [sq_nonneg (x - 3)]
    · rw [abs_of_nonpos hx]
      have := Real.exp_pos x
      linarith
  have h1 : Real.exp (2 * x - Real.exp x) ≤ Real.exp 4 * Real.exp (-2 * |x|) := by
    calc Real.exp (2 * x - Real.exp x) ≤ Real.exp (4 + (-2 * |x|)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 4 * Real.exp (-2 * |x|) := Real.exp_add _ _
  have h2 : M + |x| ≤ (M + 2) * Real.exp (|x| / 2) := by
    have hge1 : 1 ≤ Real.exp (|x| / 2) := Real.one_le_exp (by positivity)
    nlinarith
  calc Real.exp (2 * x - Real.exp x) * (M + |x|)
      ≤ (Real.exp 4 * Real.exp (-2 * |x|)) * ((M + 2) * Real.exp (|x| / 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp 4 * (M + 2) * (Real.exp (-2 * |x|) * Real.exp (|x| / 2)) := by ring
    _ = Real.exp 4 * (M + 2) * Real.exp (-(3 / 2) * |x|) := by
        rw [← Real.exp_add]; congr 2; ring

lemma integrableOn_exp_neg_three_halves_abs :
    Integrable (fun x : ℝ => Real.exp (-(3 / 2) * |x|)) volume := by
  refine PakNthPrimeStokes.integrable_exp_neg_abs.mono'
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by linarith [abs_nonneg x])

/-- Tail integral bound for `exp (-(3/2) * |x|)` on `Iic (-L)` and `Ici L` (`L ≥ 0`). -/
lemma integral_exp_neg_three_halves_tails {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in Set.Iic (-L), Real.exp (-(3 / 2) * |x|)) ≤ Real.exp (-(3 / 2) * L) ∧
    (∫ x in Set.Ici L, Real.exp (-(3 / 2) * |x|)) ≤ Real.exp (-(3 / 2) * L) := by
  have hint_pos : ∀ c : ℝ, IntegrableOn (fun x : ℝ => Real.exp (-(3 / 2) * x)) (Set.Ici c) := fun c =>
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (show (-(3 / 2) : ℝ) < 0 by norm_num) c)
  have hval_pos : ∫ x in Set.Ici L, Real.exp (-(3 / 2) * x) = (2 / 3) * Real.exp (-(3 / 2) * L) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hderiv : ∀ x ∈ Set.Ici L, HasDerivAt (fun t : ℝ => -(2 / 3) * Real.exp (-(3 / 2) * t))
        (Real.exp (-(3 / 2) * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => -(3 / 2) * t) (-(3 / 2)) x := by
        simpa using (hasDerivAt_id x).const_mul (-(3 / 2 : ℝ))
      have h2 := (h1.exp).const_mul (-(2 / 3 : ℝ))
      refine h2.congr_deriv ?_; ring
    have htend : Tendsto (fun t : ℝ => -(2 / 3) * Real.exp (-(3 / 2) * t)) atTop (𝓝 0) := by
      have hlin : Tendsto (fun t : ℝ => -(3 / 2 : ℝ) * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_id
      simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul (-(2 / 3 : ℝ))
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      ((integrableOn_Ici_iff_integrableOn_Ioi).mp (hint_pos L)) htend
    rw [hftc]; ring
  have hright : ∫ x in Set.Ici L, Real.exp (-(3 / 2) * |x|) ≤ Real.exp (-(3 / 2) * L) := by
    have heq : ∫ x in Set.Ici L, Real.exp (-(3 / 2) * |x|) = ∫ x in Set.Ici L, Real.exp (-(3 / 2) * x) :=
      setIntegral_congr_fun measurableSet_Ici fun x hx => by
        rw [abs_of_nonneg (hL.trans hx)]
    rw [heq, hval_pos]; linarith [Real.exp_pos (-(3 / 2) * L)]
  have hleft : ∫ x in Set.Iic (-L), Real.exp (-(3 / 2) * |x|) ≤ Real.exp (-(3 / 2) * L) := by
    have hsub : ∫ x in Set.Iic (-L), Real.exp (-(3 / 2) * |x|) =
        ∫ x in Set.Ici L, Real.exp (-(3 / 2) * |x|) := by
      rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ici]
      rw [← MeasureTheory.integral_neg_eq_self (fun x => Set.indicator (Set.Ici L) (fun t => Real.exp (-(3 / 2) * |t|)) x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Set.indicator, Set.mem_Iic, Set.mem_Ici, abs_neg]
      split_ifs with h1 h2
      · rfl
      · exact absurd (by linarith : L ≤ -x) h2
      · exact absurd (by linarith : x ≤ -L) h1
      · rfl
    rw [hsub]; exact hright
  exact ⟨hleft, hright⟩

/-- **Region I (Deep Lower Half-Plane)**: for every `u : ℂ` with `u.im < -C_v - 1`,
`I_entire u = ∫ x : ℝ, exp (2 x - exp x) * F_plus (u + x)`! -/
theorem I_entire_eq_conv_lower {u : ℂ} (hu : u.im < -C_v - 1) :
    I_entire u = ∫ x : ℝ, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)) := by
  have hu_neg : u.im < -1 / 4 := by linarith [C_v_ge_256]
  have hdom_all : ∀ x : ℝ, u + (x : ℂ) ∈ V_dom := by
    intro x; left; simp; linarith
  have hw_im_neg : ∀ x : ℝ, (w_plus (u + (x : ℂ))).im < 0 := by
    intro x
    have hv := hdom_all x
    have hcb := (w_plus_spec hv).1
    rw [Metric.mem_closedBall, dist_eq_norm] at hcb
    have him_diff := (abs_le.mp ((Complex.abs_im_le_norm _).trans hcb)).2
    have harg_neg : Complex.arg (u + (x : ℂ)) < 0 := by
      have him : (u + (x : ℂ)).im < 0 := by simp; linarith [C_v_ge_256]
      exact Complex.arg_neg_iff.mpr him
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero, Complex.log_im] at him_diff
    linarith [C_v_ge_256]
  -- Step 1: `I_entire u = ∫ s : ℝ, valleyIntegrand u (s + i u.im)` by shifting `Iic 1` from `-1/4` to `u.im`!
  have hleft_eq : (∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) +
      I * (∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) =
      ∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I) := by
    have hbound_strip : ∃ K > 0, ∀ y ∈ Set.Icc u.im (-1 / 4 : ℝ), ∀ s ≤ (1 : ℝ),
        ‖valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)‖ ≤ K * Real.exp s := by
      -- For `s ≤ 0`: `Ei(s + i y) + iπ = -E1(-(s + i y))` with `|y| ≥ 1/4` so `‖E1‖ ≤ 4`!
      -- For `0 ≤ s ≤ 1`: compact rectangle `[0, 1] × [u.im, -1/4] ⊆ {Im w < 0} ⊆ slitPlane`!
      have hcont_Ei : ContinuousOn (fun p : ℝ × ℝ => Ei_complex ((p.1 : ℂ) + (p.2 : ℂ) * I) + I * (Real.pi : ℂ))
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc u.im (-1 / 4 : ℝ)) := by
        intro p hp
        have him : ((p.1 : ℂ) + (p.2 : ℂ) * I).im < 0 := by simp; linarith [hp.2.2]
        have hlin : Continuous (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * I) :=
          (Complex.continuous_ofReal.comp continuous_fst).add
            ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
        exact ((ContinuousAt.comp (g := Ei_complex) (f := fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * I)
          (PakNthPrimeStokes.hasDerivAt_Ei_complex (Or.inr him.ne)).continuousAt hlin.continuousAt).add
          continuousAt_const).continuousWithinAt
      obtain ⟨K_c, hKc⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont_Ei
      let K_E : ℝ := max 4 K_c
      let K : ℝ := Real.exp (-u.re + Real.exp (-u.re) * K_E)
      refine ⟨K, Real.exp_pos _, fun y hy s hs1 => ?_⟩
      have hEi_bd : ‖Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ)‖ ≤ K_E := by
        by_cases hs0 : s ≤ 0
        · have him : ((s : ℂ) + (y : ℂ) * I).im < 0 := by simp; linarith [hy.2]
          rw [PakNthPrimeStokes.Ei_complex_eq_neg_E1_sub_I_pi him]
          have hsimp : -PakNthPrimeStokes.E1_complex (-((s : ℂ) + (y : ℂ) * I)) - I * (Real.pi : ℂ) +
              I * (Real.pi : ℂ) = -PakNthPrimeStokes.E1_complex (-((s : ℂ) + (y : ℂ) * I)) := by ring
          rw [hsimp, norm_neg]
          have him_ne : (-((s : ℂ) + (y : ℂ) * I)).im ≠ 0 := by simp; linarith [hy.2]
          have hb := PakNthPrimeStokes.norm_E1_complex_le_exp_div_im him_ne
          have hre : -(-((s : ℂ) + (y : ℂ) * I)).re = s := by simp
          have him_ge : 1 / 4 ≤ |(-((s : ℂ) + (y : ℂ) * I)).im| := by
            simp only [Complex.neg_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
              abs_neg]
            rw [abs_of_neg (by linarith [hy.2])]; linarith [hy.2]
          rw [hre] at hb
          have hle4 : Real.exp s / |(-((s : ℂ) + (y : ℂ) * I)).im| ≤ 4 := by
            calc _ ≤ 1 / (1 / 4) := div_le_div₀ zero_le_one (Real.exp_le_one_iff.mpr hs0) (by norm_num) him_ge
              _ = 4 := by norm_num
          exact (hb.trans hle4).trans (le_max_left _ _)
        · push Not at hs0
          exact (hKc (s, y) ⟨⟨hs0.le, hs1⟩, hy⟩).trans (le_max_right _ _)
      dsimp only [valleyIntegrand, K]
      rw [Complex.norm_exp]
      have hprod : ‖Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤
          Real.exp (-u.re) * K_E := by
        rw [norm_mul, Complex.norm_exp, Complex.neg_re]
        exact mul_le_mul_of_nonneg_left hEi_bd (Real.exp_pos _).le
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
      have harg : (((s : ℂ) + (y : ℂ) * I) - u -
            Complex.exp (-u) * (Ei_complex ((s : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))).re ≤
          (-u.re + Real.exp (-u.re) * K_E) + s := by
        rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
        linarith
      exact (Real.exp_le_exp.mpr harg).trans (le_of_eq (Real.exp_add _ _))
    obtain ⟨K, hK_pos, hK_bd⟩ := hbound_strip
    have hint_y : ∀ y ∈ Set.Icc u.im (-1 / 4 : ℝ),
        IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)) (Set.Iic 1) := by
      intro y hy
      have hcont : Continuous (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (y : ℂ) * I)) :=
        (differentiableOn_valleyIntegrand_w u).continuousOn.comp_continuous
          (Complex.continuous_ofReal.add continuous_const) fun s => Or.inr (by simp; linarith [hy.2])
      refine ((integrableOn_exp_Iic 1).const_mul K).mono' hcont.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
      exact hK_bd y hy s hs
    have hrect : ∀ M : ℝ, M ≤ 0 →
        (∫ s in M..(1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) -
        (∫ s in M..(1 : ℝ), valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
        I * (∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) =
        I * (∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((M : ℂ) + (y : ℂ) * I)) := by
      intro M _
      let z : ℂ := (M : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I
      let w : ℂ := (1 : ℂ) + (u.im : ℂ) * I
      have hsub : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Complex.slitPlane := by
        intro p hp
        right
        have hpim := hp.2
        have hzim : z.im = -1 / 4 := by simp [z]
        have hwim : w.im = u.im := by simp [w]
        rw [hzim, hwim, Set.uIcc_comm, Set.uIcc_of_le hu_neg.le] at hpim
        linarith [hpim.2]
      have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (valleyIntegrand u) z w ((differentiableOn_valleyIntegrand_w u).mono hsub)
      have hzre : z.re = M := by simp [z]
      have hzim : z.im = -1 / 4 := by simp [z]
      have hwre : w.re = 1 := by simp [w]
      have hwim : w.im = u.im := by simp [w]
      rw [hzre, hzim, hwre, hwim] at hc
      simp only [smul_eq_mul] at hc
      linear_combination hc
    have hlim1 : Tendsto (fun M : ℝ => ∫ s in M..(1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I))
        atBot (𝓝 (∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I))) :=
      intervalIntegral_tendsto_integral_Iic 1 (hint_y (-1 / 4) ⟨hu_neg.le, le_rfl⟩) tendsto_id
    have hlim2 : Tendsto (fun M : ℝ => ∫ s in M..(1 : ℝ), valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I))
        atBot (𝓝 (∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I))) :=
      intervalIntegral_tendsto_integral_Iic 1 (hint_y u.im ⟨le_rfl, hu_neg.le⟩) tendsto_id
    have hlim_rhs : Tendsto (fun M : ℝ => I * ∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((M : ℂ) + (y : ℂ) * I))
        atBot (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun M : ℝ => (K * |u.im - (-1 / 4)|) * Real.exp M) ?_ ?_
      · filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with M hM
        rw [norm_mul, Complex.norm_I, one_mul]
        have hbd : ∀ y ∈ Set.uIoc (-1 / 4 : ℝ) u.im, ‖valleyIntegrand u ((M : ℂ) + (y : ℂ) * I)‖ ≤ K * Real.exp M := by
          intro y hy
          have hy' : y ∈ Set.Icc u.im (-1 / 4 : ℝ) := by
            have := Set.uIoc_subset_uIcc hy
            rwa [Set.uIcc_comm, Set.uIcc_of_le hu_neg.le] at this
          exact hK_bd y hy' M (by linarith)
        calc _ ≤ (K * Real.exp M) * |u.im - (-1 / 4)| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
          _ = (K * |u.im - (-1 / 4)|) * Real.exp M := by ring
      · simpa using Real.tendsto_exp_atBot.const_mul (K * |u.im - (-1 / 4)|)
    have hlim_lhs := (hlim1.sub hlim2).add (tendsto_const_nhds (x := I * ∫ y in (-1 / 4 : ℝ)..u.im,
      valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)))
    have hlim_eq : Tendsto (fun M : ℝ =>
        (∫ s in M..(1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) -
        (∫ s in M..(1 : ℝ), valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
        I * (∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I))) atBot (𝓝 0) :=
      hlim_rhs.congr' (by filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with M hM; exact (hrect M hM).symm)
    linear_combination tendsto_nhds_unique hlim_lhs hlim_eq
  -- Combine `Iic 1` and `Ici 1` to get `I_entire u = ∫ s : ℝ, valleyIntegrand u (s + i u.im)`!
  have hline_int : Integrable (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) volume := by
    have hright := integrableOn_valleyIntegrand_right (u := u) (y := u.im) (by simp; positivity)
    have hleft : IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) (Set.Iic 1) := by
      have hcont : Continuous (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) :=
        (differentiableOn_valleyIntegrand_w u).continuousOn.comp_continuous
          (Complex.continuous_ofReal.add continuous_const) fun s => Or.inr (by simp; linarith)
      have hcompact : IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) (Set.Icc 0 1) :=
        hcont.continuousOn.integrableOn_Icc
      have hneg : IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) (Set.Iic 0) := by
        refine ((integrableOn_exp_Iic 0).const_mul (Real.exp (-u.re + Real.exp (-u.re) * 4))).mono'
          hcont.aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
        have him : ((s : ℂ) + (u.im : ℂ) * I).im < 0 := by simp; linarith
        rw [valleyIntegrand, PakNthPrimeStokes.Ei_complex_eq_neg_E1_sub_I_pi him, Complex.norm_exp]
        have hsimp : -PakNthPrimeStokes.E1_complex (-((s : ℂ) + (u.im : ℂ) * I)) - I * (Real.pi : ℂ) +
            I * (Real.pi : ℂ) = -PakNthPrimeStokes.E1_complex (-((s : ℂ) + (u.im : ℂ) * I)) := by ring
        rw [hsimp]
        have hb := PakNthPrimeStokes.norm_E1_complex_le_exp_div_im (z := -((s : ℂ) + (u.im : ℂ) * I))
          (by simp; linarith)
        have hre : -(-((s : ℂ) + (u.im : ℂ) * I)).re = s := by simp
        have him_ge : 1 / 4 ≤ |(-((s : ℂ) + (u.im : ℂ) * I)).im| := by
          simp only [Complex.neg_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
            abs_neg]
          rw [abs_of_neg (by linarith)]; linarith
        rw [hre] at hb
        have hE1 : ‖-PakNthPrimeStokes.E1_complex (-((s : ℂ) + (u.im : ℂ) * I))‖ ≤ 4 := by
          rw [norm_neg]
          calc _ ≤ Real.exp s / |(-((s : ℂ) + (u.im : ℂ) * I)).im| := hb
            _ ≤ 1 / (1 / 4) := div_le_div₀ zero_le_one (Real.exp_le_one_iff.mpr hs) (by norm_num) him_ge
            _ = 4 := by norm_num
        have hprod : ‖Complex.exp (-u) * (-PakNthPrimeStokes.E1_complex (-((s : ℂ) + (u.im : ℂ) * I)))‖ ≤
            Real.exp (-u.re) * 4 := by
          rw [norm_mul, Complex.norm_exp, Complex.neg_re]; exact mul_le_mul_of_nonneg_left hE1 (Real.exp_pos _).le
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
        have harg : (((s : ℂ) + (u.im : ℂ) * I) - u -
              Complex.exp (-u) * (-PakNthPrimeStokes.E1_complex (-((s : ℂ) + (u.im : ℂ) * I)))).re ≤
            (-u.re + Real.exp (-u.re) * 4) + s := by
          rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im]
          linarith
        exact (Real.exp_le_exp.mpr harg).trans (le_of_eq (Real.exp_add _ _))
      have hU : Set.Iic (1 : ℝ) = Set.Iic 0 ∪ Set.Icc 0 1 := by
        ext s; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
        exact ⟨fun h => by rcases le_total s 0 with h1 | h2 <;> [exact Or.inl h1; exact Or.inr ⟨h2, h⟩],
          fun h => by rcases h with h1 | ⟨_, h2⟩ <;> linarith⟩
      rw [hU]; exact hneg.union hcompact
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (1 : ℝ))]
    exact hleft.union ((integrableOn_Ici_iff_integrableOn_Ioi).mp hright)
  have hI_line : I_entire u = ∫ s : ℝ, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I) := by
    dsimp only [I_entire, J_strip]
    rw [hleft_eq, MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hdisj : Disjoint (Set.Iic (1 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hline_int.integrableOn hline_int.integrableOn,
      Set.Iic_union_Ioi, MeasureTheory.setIntegral_univ]
  -- Step 2: Deform `∫ s : ℝ, valleyIntegrand u (s + i u.im)` to `∫ x : ℝ, exp (2x - exp x) * F_plus (u + x)`
  -- inside `{Im w < 0}` via `integral_curve_eq_L_path` + `integral_valleyIntegrand_w_plus_eq`!
  have hF_int : Integrable (fun x : ℝ => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) volume := by
    have hcont : Continuous (fun x : ℝ => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).sub Real.continuous_exp))).mul
        (differentiableOn_F_plus.continuousOn.comp_continuous (continuous_const.add Complex.continuous_ofReal) hdom_all)
    refine (integrableOn_exp_neg_three_halves_abs.const_mul (3 * Real.exp 4 * (‖u‖ + 2))).mono'
      hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hF_le : ‖F_plus (u + (x : ℂ))‖ ≤ 3 * (‖u‖ + |x|) := by
      have h1 := norm_F_plus_le (hdom_all x)
      have h2 : ‖u + (x : ℂ)‖ ≤ ‖u‖ + |x| := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using norm_add_le u (x : ℂ)
      linarith
    have hk := gamma_kernel_mul_le (norm_nonneg u) x
    calc Real.exp (2 * x - Real.exp x) * ‖F_plus (u + (x : ℂ))‖
        ≤ Real.exp (2 * x - Real.exp x) * (3 * (‖u‖ + |x|)) :=
          mul_le_mul_of_nonneg_left hF_le (Real.exp_pos _).le
      _ = 3 * (Real.exp (2 * x - Real.exp x) * (‖u‖ + |x|)) := by ring
      _ ≤ 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * |x|)) :=
          mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = 3 * Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * |x|) := by ring
  -- For any `R ≥ 1`, connect `[-R, R]` on the `x`-axis to `[(w_plus(u - R)).re, (w_plus(u + R)).re]` on `Im w = u.im`!
  let Ω_neg : Set ℂ := {w : ℂ | w.im < 0}
  have hΩ_open : IsOpen Ω_neg := isOpen_lt Complex.continuous_im continuous_const
  have hΩ_rect : ∀ p ∈ Ω_neg, ∀ q ∈ Ω_neg, Set.uIcc p.re q.re ×ℂ Set.uIcc p.im q.im ⊆ Ω_neg := by
    intro p hp q hq z hz
    have hzim := hz.2
    rcases Set.mem_uIcc.mp hzim with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact lt_of_le_of_lt h2 hq
    · exact lt_of_le_of_lt h2 hp
  have hf_diff : DifferentiableOn ℂ (valleyIntegrand u) Ω_neg :=
    (differentiableOn_valleyIntegrand_w u).mono fun w hw => Or.inr hw.ne
  -- Identity for any `A, B : ℝ`:
  have hAB_eq : ∀ A B : ℝ,
      (∫ x in A..B, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) -
      (∫ s in (w_plus (u + (A : ℂ))).re..(w_plus (u + (B : ℂ))).re,
        valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) =
      (valleyIntegrand u (w_plus (u + (A : ℂ))) - valleyIntegrand u (w_plus (u + (B : ℂ)))) +
      I * (∫ t in u.im..(w_plus (u + (B : ℂ))).im,
        valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in u.im..(w_plus (u + (A : ℂ))).im,
        valleyIntegrand u (((w_plus (u + (A : ℂ))).re : ℂ) + (t : ℂ) * I)) := by
    intro A B
    have hL := integral_curve_eq_L_path hΩ_open hΩ_rect hf_diff (a := A) (b := B)
      (γ := fun x : ℝ => w_plus (u + (x : ℂ)))
      (γ' := fun x : ℝ => S_phi (w_plus (u + (x : ℂ))))
      (fun x _ => hw_im_neg x)
      (fun x _ => by
        have hlin : HasDerivAt (fun τ : ℝ => u + (τ : ℂ)) 1 x := by
          simpa using (hasDerivAt_id x).ofReal_comp.const_add u
        exact ((hasDerivAt_w_plus (hdom_all x)).comp x hlin).congr_deriv (mul_one _))
      (differentiableOn_S_phi.continuousOn.comp
        (differentiableOn_w_plus.continuousOn.comp (continuous_const.add Complex.continuous_ofReal).continuousOn
          (fun x _ => hdom_all x))
        (fun x _ => (closedBall_log_props (hdom_all x) (w_plus_spec (hdom_all x)).1).1))
    have hIBP := integral_valleyIntegrand_w_plus_eq (u := u) (a := A) (b := B) (fun x _ => hdom_all x)
    -- Shift horizontal edge from `(w_plus(u+A)).im` to `u.im` using Cauchy rectangle on
    -- `[(w_plus(u+A)).re, (w_plus(u+B)).re] × [u.im, (w_plus(u+A)).im]` inside `Ω_neg`!
    let p : ℂ := ((w_plus (u + (A : ℂ))).re : ℂ) + (u.im : ℂ) * I
    let q : ℂ := ((w_plus (u + (B : ℂ))).re : ℂ) + ((w_plus (u + (A : ℂ))).im : ℂ) * I
    have hp : p ∈ Ω_neg := by change p.im < 0; simp [p]; linarith
    have hq : q ∈ Ω_neg := by change q.im < 0; simp [q]; exact hw_im_neg A
    have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (valleyIntegrand u) p q (hf_diff.mono (hΩ_rect p hp q hq))
    have hpre : p.re = (w_plus (u + (A : ℂ))).re := by simp [p]
    have hpim : p.im = u.im := by simp [p]
    have hqre : q.re = (w_plus (u + (B : ℂ))).re := by simp [q]
    have hqim : q.im = (w_plus (u + (A : ℂ))).im := by simp [q]
    rw [hpre, hpim, hqre, hqim] at hc
    simp only [smul_eq_mul] at hc
    have hcont_v : ∀ (r y₁ y₂ : ℝ), y₁ < 0 → y₂ < 0 →
        ContinuousOn (fun t : ℝ => valleyIntegrand u ((r : ℂ) + (t : ℂ) * I)) (Set.uIcc y₁ y₂) := by
      intro r y₁ y₂ hy₁ hy₂
      refine hf_diff.continuousOn.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
      intro t ht
      change ((r : ℂ) + (t : ℂ) * I).im < 0
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      rcases Set.mem_uIcc.mp ht with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact lt_of_le_of_lt h2 hy₂
      · exact lt_of_le_of_lt h2 hy₁
    have hv_add : (∫ t in u.im..(w_plus (u + (A : ℂ))).im,
          valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)) +
        (∫ t in (w_plus (u + (A : ℂ))).im..(w_plus (u + (B : ℂ))).im,
          valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)) =
        ∫ t in u.im..(w_plus (u + (B : ℂ))).im,
          valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont_v _ _ _ (by linarith) (hw_im_neg A)).intervalIntegrable
        (hcont_v _ _ _ (hw_im_neg A) (hw_im_neg B)).intervalIntegrable
    linear_combination -hIBP + hL - hc + I * hv_add
  -- Take `A = -R`, `B = R` and let `R → +∞`!
  obtain ⟨_, hre_top, him_lim⟩ := tendsto_w_plus_add_real u
  have hre_bot : Tendsto (fun R : ℝ => (w_plus (u + ((-R : ℝ) : ℂ))).re) atTop atBot := by
    have hlin : Tendsto (fun R : ℝ => u.re + ‖u‖ / 2 + 1 - R / 2) atTop atBot := by
      have h1 : Tendsto (fun R : ℝ => (-(1 / 2 : ℝ)) * R) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_id
      have h2 := tendsto_atBot_add_const_left atTop (u.re + ‖u‖ / 2 + 1) h1
      refine h2.congr fun R => by ring
    refine tendsto_atBot_mono' atTop ?_ hlin
    filter_upwards [Filter.eventually_ge_atTop (‖u‖ + 4)] with R hR
    have hv := hdom_all (-R)
    have hcb := (w_plus_spec hv).1
    rw [Metric.mem_closedBall, dist_eq_norm] at hcb
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm _).trans hcb)).2
    have hnorm_le : ‖u + ((-R : ℝ) : ℂ)‖ ≤ ‖u‖ + R := by
      calc _ ≤ ‖u‖ + ‖((-R : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖u‖ + |-R| := by simp [Complex.norm_real]
        _ = ‖u‖ + R := by rw [abs_neg, abs_of_nonneg (by linarith [norm_nonneg u])]
    have hnorm_pos : 0 < ‖u + ((-R : ℝ) : ℂ)‖ := by
      have him : (u + ((-R : ℝ) : ℂ)).im < 0 := by simp; linarith [C_v_ge_256]
      exact norm_pos_iff.mpr (fun h0 => by have := congr_arg Complex.im h0; simp at this; linarith)
    have hlog_le : Real.log ‖u + ((-R : ℝ) : ℂ)‖ ≤ (‖u‖ + R) / 2 := by
      have h1 : Real.log ‖u + ((-R : ℝ) : ℂ)‖ ≤ Real.log (‖u‖ + R) :=
        Real.log_le_log hnorm_pos hnorm_le
      have h2 : Real.log (‖u‖ + R) ≤ (‖u‖ + R) / 2 := by
        have hsq_pos : 0 < Real.sqrt (‖u‖ + R) := Real.sqrt_pos.mpr (by linarith [norm_nonneg u])
        have hlog2 := Real.log_le_sub_one_of_pos (show 0 < (‖u‖ + R) / 2 by linarith [norm_nonneg u])
        -- Even simpler: `log t = log 2 + log (t/2) ≤ 1 + (t/2 - 1) = t/2`!
        have hlog_two : Real.log 2 ≤ 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) (by linarith)
            _ = 1 := Real.log_exp 1
        have hmul : Real.log (‖u‖ + R) = Real.log 2 + Real.log ((‖u‖ + R) / 2) := by
          rw [← Real.log_mul (by norm_num) (by linarith [norm_nonneg u])]; congr 1; ring
        linarith
      exact h1.trans h2
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.log_re] at hre_diff
    linarith
  have hlim_F : Tendsto (fun R : ℝ => ∫ x in (-R)..R,
      ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))
      atTop (𝓝 (∫ x : ℝ, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))) :=
    intervalIntegral_tendsto_integral hF_int tendsto_neg_atTop_atBot tendsto_id
  have hlim_line : Tendsto (fun R : ℝ =>
      ∫ s in (w_plus (u + ((-R : ℝ) : ℂ))).re..(w_plus (u + (R : ℂ))).re,
        valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I))
      atTop (𝓝 (∫ s : ℝ, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hline_int hre_bot hre_top
  -- Show each of the 4 RHS terms in `hAB_eq (-R) R` tends to `0` as `R → +∞`!
  have hlim_bA : Tendsto (fun R : ℝ => valleyIntegrand u (w_plus (u + ((-R : ℝ) : ℂ)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun R : ℝ => (3 * (‖u‖ + 2)) * Real.exp (-R / 2)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
      have hv := hdom_all (-R)
      have hval : valleyIntegrand u (w_plus (u + ((-R : ℝ) : ℂ))) =
          F_plus (u + ((-R : ℝ) : ℂ)) * Complex.exp (((-R : ℝ) : ℂ) - Complex.exp ((-R : ℝ) : ℂ)) := by
        dsimp only [valleyIntegrand]
        rw [Ei_add_I_pi_w_plus hv, F_plus_eq_exp_sub hv]
        have : Complex.exp (-u) * Complex.exp (u + ((-R : ℝ) : ℂ)) = Complex.exp ((-R : ℝ) : ℂ) := by
          rw [← Complex.exp_add]; congr 1; ring
        rw [this, ← Complex.exp_add]; congr 1; ring
      rw [hval, norm_mul, Complex.norm_exp]
      have hre : (((-R : ℝ) : ℂ) - Complex.exp ((-R : ℝ) : ℂ)).re = -R - Real.exp (-R) := by
        rw [Complex.sub_re, Complex.ofReal_re, ← Complex.ofReal_exp, Complex.ofReal_re]
      rw [hre]
      have hF_le : ‖F_plus (u + ((-R : ℝ) : ℂ))‖ ≤ 3 * (‖u‖ + R) := by
        have h1 := norm_F_plus_le hv
        have h2 : ‖u + ((-R : ℝ) : ℂ)‖ ≤ ‖u‖ + R := by
          calc _ ≤ ‖u‖ + ‖((-R : ℝ) : ℂ)‖ := norm_add_le _ _
            _ = ‖u‖ + R := by simp [Complex.norm_real, abs_of_nonneg hR]
        linarith
      have hR_exp : R ≤ 2 * Real.exp (R / 2) := by linarith [Real.add_one_le_exp (R / 2)]
      have h1 : Real.exp (-R - Real.exp (-R)) ≤ Real.exp (-R) :=
        Real.exp_le_exp.mpr (by linarith [Real.exp_pos (-R)])
      have h2 : ‖u‖ + R ≤ (‖u‖ + 2) * Real.exp (R / 2) := by
        nlinarith [Real.one_le_exp (show 0 ≤ R / 2 by linarith), norm_nonneg u]
      calc ‖F_plus (u + ((-R : ℝ) : ℂ))‖ * Real.exp (-R - Real.exp (-R))
          ≤ (3 * (‖u‖ + R)) * Real.exp (-R) := mul_le_mul hF_le h1 (Real.exp_pos _).le (by positivity)
        _ ≤ (3 * ((‖u‖ + 2) * Real.exp (R / 2))) * Real.exp (-R) := by gcongr
        _ = (3 * (‖u‖ + 2)) * (Real.exp (R / 2) * Real.exp (-R)) := by ring
        _ = (3 * (‖u‖ + 2)) * Real.exp (-R / 2) := by rw [← Real.exp_add]; congr 2; ring
    · have h1 : Tendsto (fun R : ℝ => (-R) / 2) atTop atBot := by
        have := Tendsto.const_mul_atTop_of_neg (show (-(1 / 2) : ℝ) < 0 by norm_num) tendsto_id
        exact this.congr fun R => by dsimp [id]; ring
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (3 * (‖u‖ + 2))
  have hlim_bB : Tendsto (fun R : ℝ => valleyIntegrand u (w_plus (u + (R : ℂ)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun R : ℝ => (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-R / 2)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
      have hv := hdom_all R
      have hval : valleyIntegrand u (w_plus (u + (R : ℂ))) =
          F_plus (u + (R : ℂ)) * Complex.exp ((R : ℂ) - Complex.exp (R : ℂ)) := by
        dsimp only [valleyIntegrand]
        rw [Ei_add_I_pi_w_plus hv, F_plus_eq_exp_sub hv]
        have : Complex.exp (-u) * Complex.exp (u + (R : ℂ)) = Complex.exp (R : ℂ) := by
          rw [← Complex.exp_add]; congr 1; ring
        rw [this, ← Complex.exp_add]; congr 1; ring
      rw [hval, norm_mul, Complex.norm_exp]
      have hre : ((R : ℂ) - Complex.exp (R : ℂ)).re = R - Real.exp R := by
        rw [Complex.sub_re, Complex.ofReal_re, ← Complex.ofReal_exp, Complex.ofReal_re]
      rw [hre]
      have hF_le : ‖F_plus (u + (R : ℂ))‖ ≤ 3 * (‖u‖ + R) := by
        have h1 := norm_F_plus_le hv
        have h2 : ‖u + (R : ℂ)‖ ≤ ‖u‖ + R := by
          calc _ ≤ ‖u‖ + ‖(R : ℂ)‖ := norm_add_le _ _
            _ = ‖u‖ + R := by simp [Complex.norm_real, abs_of_nonneg hR]
        linarith
      have h1 : Real.exp (R - Real.exp R) ≤ Real.exp (2 * R - Real.exp R) := Real.exp_le_exp.mpr (by linarith)
      have hk := gamma_kernel_mul_le (norm_nonneg u) R
      rw [abs_of_nonneg hR] at hk
      calc ‖F_plus (u + (R : ℂ))‖ * Real.exp (R - Real.exp R)
          ≤ (3 * (‖u‖ + R)) * Real.exp (2 * R - Real.exp R) :=
            mul_le_mul hF_le h1 (Real.exp_pos _).le (by positivity)
        _ = 3 * (Real.exp (2 * R - Real.exp R) * (‖u‖ + R)) := by ring
        _ ≤ 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * R)) :=
            mul_le_mul_of_nonneg_left hk (by norm_num)
        _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-R / 2) := by
            have : Real.exp (-(3 / 2) * R) ≤ Real.exp (-R / 2) := Real.exp_le_exp.mpr (by linarith)
            calc 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * R))
                = (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * R) := by ring
              _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-R / 2) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
    · have h1 : Tendsto (fun R : ℝ => (-R) / 2) atTop atBot := by
        have := Tendsto.const_mul_atTop_of_neg (show (-(1 / 2) : ℝ) < 0 by norm_num) tendsto_id
        exact this.congr fun R => by dsimp [id]; ring
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (3 * Real.exp 4 * (‖u‖ + 2))
  have hlim_vB : Tendsto (fun R : ℝ => I * ∫ t in u.im..(w_plus (u + (R : ℂ))).im,
      valleyIntegrand u (((w_plus (u + (R : ℂ))).re : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    let M_y : ℝ := |u.im| + Real.pi / 3
    obtain ⟨C, _, hdom⟩ := norm_valleyIntegrand_right_dom |u.re| M_y (abs_nonneg _) (by dsimp [M_y]; positivity)
    set S₁ : ℝ := max (max 16 (16 * M_y)) (32 / Real.cos phiRay ^ 2)
    have hev_im : ∀ᶠ R : ℝ in atTop, |(w_plus (u + (R : ℂ))).im - u.im| ≤ Real.pi / 3 := by
      have h := him_lim.eventually (Metric.ball_mem_nhds u.im (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 3))
      exact h.mono fun R hR => le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hR)
    have hev_re : ∀ᶠ R : ℝ in atTop, S₁ ≤ (w_plus (u + (R : ℂ))).re :=
      hre_top.eventually (Filter.eventually_ge_atTop S₁)
    refine squeeze_zero_norm' (a := fun R : ℝ => (C * (Real.pi / 3)) * Real.exp (-(w_plus (u + (R : ℂ))).re)) ?_ ?_
    · filter_upwards [hev_im, hev_re] with R himR hreR
      rw [norm_mul, Complex.norm_I, one_mul]
      have hbd : ∀ t ∈ Set.uIoc u.im (w_plus (u + (R : ℂ))).im,
          ‖valleyIntegrand u (((w_plus (u + (R : ℂ))).re : ℂ) + (t : ℂ) * I)‖ ≤
            C * Real.exp (-(w_plus (u + (R : ℂ))).re) := by
        intro t ht
        have ht_mem := Set.uIoc_subset_uIcc ht
        have ht_strip : |t - u.im| ≤ Real.pi / 3 := by
          rw [abs_le] at himR ⊢
          rcases Set.mem_uIcc.mp ht_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [Real.pi_pos]
        have ht_My : |t| ≤ M_y := by
          have := abs_add_le (t - u.im) u.im
          rw [sub_add_cancel] at this; dsimp [M_y]; linarith
        exact (hdom u t le_rfl ht_My ht_strip _ hreR).1
      calc _ ≤ (C * Real.exp (-(w_plus (u + (R : ℂ))).re)) * |(w_plus (u + (R : ℂ))).im - u.im| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hbd
        _ ≤ (C * Real.exp (-(w_plus (u + (R : ℂ))).re)) * (Real.pi / 3) :=
            mul_le_mul_of_nonneg_left himR (by positivity)
        _ = (C * (Real.pi / 3)) * Real.exp (-(w_plus (u + (R : ℂ))).re) := by ring
    · have h0 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hre_top)
      simpa using h0.const_mul (C * (Real.pi / 3))
  have hlim_vA : Tendsto (fun R : ℝ => I * ∫ t in u.im..(w_plus (u + ((-R : ℝ) : ℂ))).im,
      valleyIntegrand u (((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    let K : ℝ := Real.exp (-u.re + Real.exp (-u.re) * 4) * (Real.pi + 1)
    refine squeeze_zero_norm' (a := fun R : ℝ => K * Real.exp ((w_plus (u + ((-R : ℝ) : ℂ))).re)) ?_ ?_
    · filter_upwards [hre_bot.eventually (Filter.eventually_le_atBot (0 : ℝ))] with R hre0
      rw [norm_mul, Complex.norm_I, one_mul]
      have hv := hdom_all (-R)
      have hcb := (w_plus_spec hv).1
      rw [Metric.mem_closedBall, dist_eq_norm] at hcb
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm _).trans hcb)
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero, Complex.log_im] at him_diff
      have harg_le := abs_le.mp (Complex.abs_arg_le_pi (u + ((-R : ℝ) : ℂ)))
      have hlen : |(w_plus (u + ((-R : ℝ) : ℂ))).im - u.im| ≤ Real.pi + 1 := by
        rw [abs_le]; constructor <;> linarith
      have him_hi : (w_plus (u + ((-R : ℝ) : ℂ))).im ≤ -1 / 4 := by
        have harg_neg : Complex.arg (u + ((-R : ℝ) : ℂ)) < 0 :=
          Complex.arg_neg_iff.mpr (by simp; linarith [C_v_ge_256])
        linarith [C_v_ge_256]
      have hbd : ∀ t ∈ Set.uIoc u.im (w_plus (u + ((-R : ℝ) : ℂ))).im,
          ‖valleyIntegrand u (((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)‖ ≤
            Real.exp (-u.re + Real.exp (-u.re) * 4) * Real.exp ((w_plus (u + ((-R : ℝ) : ℂ))).re) := by
        intro t ht
        have ht_mem := Set.uIoc_subset_uIcc ht
        have ht_hi : t ≤ -1 / 4 := by
          rcases Set.mem_uIcc.mp ht_mem with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
        have him : (((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I).im < 0 := by simp; linarith
        rw [valleyIntegrand, PakNthPrimeStokes.Ei_complex_eq_neg_E1_sub_I_pi him, Complex.norm_exp]
        have hsimp : -PakNthPrimeStokes.E1_complex (-(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)) -
            I * (Real.pi : ℂ) + I * (Real.pi : ℂ) =
            -PakNthPrimeStokes.E1_complex (-(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)) := by ring
        rw [hsimp]
        have hb := PakNthPrimeStokes.norm_E1_complex_le_exp_div_im
          (z := -(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)) (by simp; linarith)
        have hre' : -(-(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)).re = (w_plus (u + ((-R : ℝ) : ℂ))).re := by simp
        have him_ge : 1 / 4 ≤ |(-(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)).im| := by
          simp only [Complex.neg_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
            abs_neg]
          rw [abs_of_neg (by linarith)]; linarith
        rw [hre'] at hb
        have hE1 : ‖-PakNthPrimeStokes.E1_complex (-(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I))‖ ≤ 4 := by
          rw [norm_neg]
          calc _ ≤ Real.exp ((w_plus (u + ((-R : ℝ) : ℂ))).re) / _ := hb
            _ ≤ 1 / (1 / 4) := div_le_div₀ zero_le_one (Real.exp_le_one_iff.mpr hre0) (by norm_num) him_ge
            _ = 4 := by norm_num
        have hprod : ‖Complex.exp (-u) * (-PakNthPrimeStokes.E1_complex (-(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)))‖ ≤
            Real.exp (-u.re) * 4 := by
          rw [norm_mul, Complex.norm_exp, Complex.neg_re]; exact mul_le_mul_of_nonneg_left hE1 (Real.exp_pos _).le
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
        have harg : ((((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I) - u -
              Complex.exp (-u) * (-PakNthPrimeStokes.E1_complex (-(((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I)))).re ≤
            (-u.re + Real.exp (-u.re) * 4) + (w_plus (u + ((-R : ℝ) : ℂ))).re := by
          rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im]
          linarith
        exact (Real.exp_le_exp.mpr harg).trans (le_of_eq (Real.exp_add _ _))
      calc _ ≤ (Real.exp (-u.re + Real.exp (-u.re) * 4) * Real.exp ((w_plus (u + ((-R : ℝ) : ℂ))).re)) *
              |(w_plus (u + ((-R : ℝ) : ℂ))).im - u.im| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
        _ ≤ (Real.exp (-u.re + Real.exp (-u.re) * 4) * Real.exp ((w_plus (u + ((-R : ℝ) : ℂ))).re)) * (Real.pi + 1) :=
            mul_le_mul_of_nonneg_left hlen (by positivity)
        _ = K * Real.exp ((w_plus (u + ((-R : ℝ) : ℂ))).re) := by dsimp [K]; ring
    · simpa using (Real.tendsto_exp_atBot.comp hre_bot).const_mul K
  have hlim_rhs : Tendsto (fun R : ℝ =>
      (valleyIntegrand u (w_plus (u + ((-R : ℝ) : ℂ))) - valleyIntegrand u (w_plus (u + (R : ℂ)))) +
      I * (∫ t in u.im..(w_plus (u + (R : ℂ))).im,
        valleyIntegrand u (((w_plus (u + (R : ℂ))).re : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in u.im..(w_plus (u + ((-R : ℝ) : ℂ))).im,
        valleyIntegrand u (((w_plus (u + ((-R : ℝ) : ℂ))).re : ℂ) + (t : ℂ) * I))) atTop (𝓝 0) := by
    simpa using ((hlim_bA.sub hlim_bB).add hlim_vB).sub hlim_vA
  have hlim_lhs := hlim_F.sub hlim_line
  have hlim_zero := hlim_rhs.congr (fun R => (hAB_eq (-R) R).symm)
  have hdiff0 := tendsto_nhds_unique hlim_lhs hlim_zero
  rw [hI_line]
  exact (sub_eq_zero.mp hdiff0).symm

/-- Explicit radius `R_conv` for the unified sectorial truncated convolution on `Σ₀ = rotatedClosedSector theta1' theta2' R_conv`. -/
@[expose] def R_conv : ℝ := max (6 * R_sec) (max (32 * (C_v + 1)) (10 ^ 6))

lemma R_conv_ge_6Rsec : 6 * R_sec ≤ R_conv := le_max_left _ _
lemma R_conv_ge_2Rsec : 2 * R_sec ≤ R_conv := by linarith [R_conv_ge_6Rsec, R_sec_pos]
lemma R_conv_ge_32Cv : 32 * (C_v + 1) ≤ R_conv := le_trans (le_max_left _ _) (le_max_right _ _)
lemma R_conv_ge_1e6 : (10 : ℝ) ^ 6 ≤ R_conv := le_trans (le_max_right _ _) (le_max_right _ _)
lemma R_conv_pos : 0 < R_conv := lt_of_lt_of_le (by positivity) R_conv_ge_1e6

/-- Geometry lemma: for every `u ∈ rotatedClosedSector theta1' theta2' R_conv` and `|x| ≤ ‖u‖ / 24`,
the shifted point `u + (x : ℂ)` lies inside `V_sec`! -/
lemma shift_mem_V_sec {u : ℂ} (hu : u ∈ rotatedClosedSector theta1' theta2' R_conv)
    {x : ℝ} (hx : |x| ≤ ‖u‖ / 24) :
    u + (x : ℂ) ∈ V_sec := by
  have hu_ge : R_conv ≤ ‖u‖ := hu.1
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le R_conv_pos hu_ge
  have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hnorm_lo : (23 / 24 : ℝ) * ‖u‖ ≤ ‖u + (x : ℂ)‖ := by
    have htri : ‖u‖ ≤ ‖u + (x : ℂ)‖ + ‖-((x : ℂ))‖ := by simpa using norm_add_le (u + (x : ℂ)) (-(x : ℂ))
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at htri
    linarith
  have hR : R_sec ≤ ‖u + (x : ℂ)‖ := by linarith [R_conv_ge_2Rsec, R_sec_pos]
  -- Bound `|Complex.arg (1 + (x : ℂ) / u)| < deltaV`!
  have hdiv : ‖(x : ℂ) / u‖ ≤ 1 / 24 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hu_pos]; linarith
  have h1u_lo : 1 / 2 ≤ ‖1 + (x : ℂ) / u‖ := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hdiv)).1
    exact (show (1 / 2 : ℝ) ≤ (1 + (x : ℂ) / u).re by simp [Complex.add_re]; linarith).trans (Complex.re_le_norm _)
  have h1u_ne : 1 + (x : ℂ) / u ≠ 0 := norm_pos_iff.mp (by linarith)
  have harg_1u : |Complex.arg (1 + (x : ℂ) / u)| < deltaV := by
    have hsin : |Real.sin (Complex.arg (1 + (x : ℂ) / u))| ≤ (1 / 24 : ℝ) / (23 / 24) := by
      have h1 : ‖1 + (x : ℂ) / u‖ * |Real.sin (Complex.arg (1 + (x : ℂ) / u))| = |(1 + (x : ℂ) / u).im| := by
        rw [← Complex.norm_mul_sin_arg, abs_mul, abs_of_nonneg (norm_nonneg _)]
      have him : |(1 + (x : ℂ) / u).im| ≤ 1 / 24 := by
        simpa [Complex.add_im] using (Complex.abs_im_le_norm ((x : ℂ) / u)).trans hdiv
      have hnorm23 : 23 / 24 ≤ ‖1 + (x : ℂ) / u‖ := by
        have htri : ‖(1 : ℂ)‖ ≤ ‖1 + (x : ℂ) / u‖ + ‖-((x : ℂ) / u)‖ := by
          simpa using norm_add_le (1 + (x : ℂ) / u) (-((x : ℂ) / u))
        rw [norm_one, norm_neg] at htri; linarith
      have hnn := abs_nonneg (Real.sin (Complex.arg (1 + (x : ℂ) / u)))
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 23 / 24)]
      nlinarith
    have hre_pos : 0 < (1 + (x : ℂ) / u).re := by
      have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hdiv)).1
      simp only [Complex.add_re, Complex.one_re]; linarith
    have harg_half : |Complex.arg (1 + (x : ℂ) / u)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
    have hsin_abs : Real.sin |Complex.arg (1 + (x : ℂ) / u)| < Real.sin deltaV := by
      have heq : Real.sin |Complex.arg (1 + (x : ℂ) / u)| = |Real.sin (Complex.arg (1 + (x : ℂ) / u))| := by
        rcases le_total 0 (Complex.arg (1 + (x : ℂ) / u)) with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (Complex.arg_le_pi _))]
        · rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
            (le_of_lt (Complex.neg_pi_lt_arg _)))]
      rw [heq]; linarith [sin_deltaV_ge]
    by_contra hge
    push Not at hge
    have hmono := Real.strictMonoOn_sin.monotoneOn
      ⟨by linarith [deltaV_pos, Real.pi_pos], by dsimp [deltaV]; linarith [Real.pi_pos]⟩
      ⟨by linarith [abs_nonneg (Complex.arg (1 + (x : ℂ) / u)), Real.pi_pos], harg_half.le⟩ hge
    linarith
  have harg_u : theta1' ≤ Complex.arg u ∧ Complex.arg u ≤ theta2' := by
    have hcen : (theta1' + theta2') / 2 = -5 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
    have hhw : (theta2' - theta1') / 2 = 14 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
    have hrot := hu.2
    rw [hcen, hhw] at hrot
    have hu_exp : u = Complex.exp ((Real.log ‖u‖ : ℂ) + (Complex.arg u : ℂ) * I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hu_pos]
      exact (Complex.norm_mul_exp_arg_mul_I u).symm
    have hprod : Complex.exp (-(((-5 * Real.pi / 24 : ℝ) : ℂ)) * I) * u =
        Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)) := by
      conv_lhs => rw [hu_exp]
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hprod] at hrot
    by_cases hwrap : Complex.arg u + 5 * Real.pi / 24 ≤ Real.pi
    · have him : ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)).im =
          Complex.arg u + 5 * Real.pi / 24 := by simp
      have harg_eq : Complex.arg (Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I))) =
          Complex.arg u + 5 * Real.pi / 24 := by
        rw [arg_cexp_eq_im (by rw [him]; linarith [Complex.neg_pi_lt_arg u, Real.pi_pos]) (by rw [him]; exact hwrap), him]
      rw [harg_eq, abs_le] at hrot
      dsimp only [theta1', theta2']; constructor <;> linarith
    · push Not at hwrap
      have hshift : Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)) =
          Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I)) := by
        have h2pi : ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)) =
            ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I)) +
            (2 * Real.pi * I) := by push_cast; ring
        rw [h2pi, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      rw [hshift] at hrot
      have him : ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I)).im =
          Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi := by simp
      have harg_eq : Complex.arg (Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I))) =
          Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi := by
        rw [arg_cexp_eq_im (by rw [him]; linarith [Real.pi_pos])
          (by rw [him]; linarith [Complex.arg_le_pi u, Real.pi_pos]), him]
      rw [harg_eq, abs_le] at hrot
      linarith [Complex.arg_le_pi u, Real.pi_pos]
  -- Now compute `Complex.arg (u + x) = Complex.arg u + Complex.arg (1 + x / u)`!
  have hfac : u + (x : ℂ) = u * (1 + (x : ℂ) / u) := by field_simp [hu0]
  have hlo : -Real.pi < Complex.arg u + Complex.arg (1 + (x : ℂ) / u) := by
    have := (abs_lt.mp harg_1u).1; dsimp only [theta1', deltaV] at harg_u this; linarith [Real.pi_pos]
  have hhi : Complex.arg u + Complex.arg (1 + (x : ℂ) / u) ≤ Real.pi := by
    have := (abs_lt.mp harg_1u).2; dsimp only [theta2', deltaV] at harg_u this; linarith [Real.pi_pos]
  have harg_add : Complex.arg (u + (x : ℂ)) = Complex.arg u + Complex.arg (1 + (x : ℂ) / u) := by
    rw [hfac, Complex.arg_mul hu0 h1u_ne ⟨hlo, hhi⟩]
  refine ⟨hR, ?_, ?_⟩
  · have := (abs_lt.mp harg_1u).1
    rw [harg_add]; dsimp only [theta1', deltaV] at harg_u this ⊢; linarith [Real.pi_pos]
  · have := (abs_lt.mp harg_1u).2
    rw [harg_add]; dsimp only [theta2', phiRay, deltaV] at harg_u this ⊢; linarith [Real.pi_pos]

/-- Helper: `rotatedClosedSector theta1' theta2' R_conv` extracts `theta1' ≤ arg u ≤ theta2'`. -/
lemma rotatedClosedSector_enlarged_arg_mem {u : ℂ} (hu : u ∈ rotatedClosedSector theta1' theta2' R_conv) :
    theta1' ≤ Complex.arg u ∧ Complex.arg u ≤ theta2' := by
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le R_conv_pos hu.1
  have hcen : (theta1' + theta2') / 2 = -5 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
  have hhw : (theta2' - theta1') / 2 = 14 * Real.pi / 24 := by dsimp [theta1', theta2']; ring
  have hrot := hu.2
  rw [hcen, hhw] at hrot
  have hu_exp : u = Complex.exp ((Real.log ‖u‖ : ℂ) + (Complex.arg u : ℂ) * I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hu_pos]
    exact (Complex.norm_mul_exp_arg_mul_I u).symm
  have hprod : Complex.exp (-(((-5 * Real.pi / 24 : ℝ) : ℂ)) * I) * u =
      Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)) := by
    conv_lhs => rw [hu_exp]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hprod] at hrot
  by_cases hwrap : Complex.arg u + 5 * Real.pi / 24 ≤ Real.pi
  · have him : ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)).im =
        Complex.arg u + 5 * Real.pi / 24 := by simp
    have harg_eq : Complex.arg (Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I))) =
        Complex.arg u + 5 * Real.pi / 24 := by
      rw [arg_cexp_eq_im (by rw [him]; linarith [Complex.neg_pi_lt_arg u, Real.pi_pos]) (by rw [him]; exact hwrap), him]
    rw [harg_eq, abs_le] at hrot
    dsimp only [theta1', theta2']; constructor <;> linarith
  · push Not at hwrap
    have hshift : Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)) =
        Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I)) := by
      have h2pi : ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 : ℝ) : ℂ) * I)) =
          ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I)) +
          (2 * Real.pi * I) := by push_cast; ring
      rw [h2pi, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hshift] at hrot
    have him : ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I)).im =
        Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi := by simp
    have harg_eq : Complex.arg (Complex.exp ((Real.log ‖u‖ : ℂ) + (((Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi : ℝ) : ℂ) * I))) =
        Complex.arg u + 5 * Real.pi / 24 - 2 * Real.pi := by
      rw [arg_cexp_eq_im (by rw [him]; linarith [Real.pi_pos])
        (by rw [him]; linarith [Complex.arg_le_pi u, Real.pi_pos]), him]
    rw [harg_eq, abs_le] at hrot
    linarith [Complex.arg_le_pi u, Real.pi_pos]

/-- **Region II (Right Half-Plane of `Σ₀`)**: for `u ∈ rotatedClosedSector theta1' theta2' R_conv`
with `-C_v - 1 ≤ u.im`, we have `u.re ≥ ‖u‖ / 4` and the truncated convolution error is `O(exp(-‖u‖ / 96))`! -/
theorem I_entire_conv_bound_right :
    ∃ C_R > 0, ∀ u ∈ rotatedClosedSector theta1' theta2' R_conv, -C_v - 1 ≤ u.im →
      ‖I_entire u - ∫ x in Set.Icc (-(‖u‖ / 24)) (‖u‖ / 24),
          ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))‖ ≤
        C_R * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
  obtain ⟨K_L, hKL_pos, hEi_L⟩ := norm_Ei_add_I_pi_left_le
  let K_Ei : ℝ := ‖Ei_complex (1 : ℂ)‖ + Real.pi + 4 * Real.exp 1 + 1
  let C_R : ℝ := 100 * (Real.exp (1 + K_L) + Real.exp (1 + K_Ei) + Real.exp (K_Ei + Real.pi + 1) +
    Real.exp 4 + 1)
  have hCR_pos : 0 < C_R := by dsimp [C_R, K_Ei]; positivity
  refine ⟨C_R, hCR_pos, fun u hu hu_im => ?_⟩
  have hu_ge : R_conv ≤ ‖u‖ := hu.1
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le R_conv_pos hu_ge
  have hu_1e6 : (1000000 : ℝ) ≤ ‖u‖ := by
    have h := R_conv_ge_1e6.trans hu_ge; norm_num at h; exact h
  obtain ⟨harg_lo, harg_hi⟩ := rotatedClosedSector_enlarged_arg_mem hu
  -- 1. Show `-π / 4 ≤ Complex.arg u`, hence `u.re ≥ ‖u‖ / 3 ≥ ‖u‖ / 4`!
  have hsin_pi8 : (1 / 3 : ℝ) ≤ Real.sin (Real.pi / 8) := by
    have h1 := Real.sin_gt_sub_cube (show (0 : ℝ) < Real.pi / 8 by linarith [Real.pi_pos])
    have hpi_lo := Real.pi_gt_three
    have hpi_hi := Real.pi_lt_four
    have hcube : (Real.pi / 8) ^ 3 ≤ (4 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    linarith
  have harg_ge_m4 : -Real.pi / 4 ≤ Complex.arg u := by
    by_contra hlt
    push Not at hlt
    have hsin_le : Real.sin (Complex.arg u) ≤ -(1 / 3 : ℝ) := by
      have h1 : Real.sin (Complex.arg u) = -Real.sin (Complex.arg u + Real.pi) := by
        rw [Real.sin_add_pi, neg_neg]
      rw [h1]
      have hge : Real.sin (Real.pi / 8) ≤ Real.sin (Complex.arg u + Real.pi) := by
        set α : ℝ := Complex.arg u + Real.pi
        have hα_lo : 5 * Real.pi / 24 ≤ α := by dsimp [α, theta1'] at harg_lo ⊢; linarith
        have hα_hi : α ≤ 3 * Real.pi / 4 := by dsimp [α]; linarith
        by_cases hα2 : α ≤ Real.pi / 2
        · exact Real.strictMonoOn_sin.monotoneOn
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
            ⟨by linarith [Real.pi_pos], hα2⟩ (by linarith [Real.pi_pos])
        · push Not at hα2
          rw [← Real.sin_pi_sub α]
          exact Real.strictMonoOn_sin.monotoneOn
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])
      linarith
    have him_eq : u.im = ‖u‖ * Real.sin (Complex.arg u) := (Complex.norm_mul_sin_arg u).symm
    have h1 : u.im ≤ -(1 / 3 : ℝ) * ‖u‖ := by rw [him_eq]; nlinarith
    have h2 : 32 * (C_v + 1) ≤ ‖u‖ := R_conv_ge_32Cv.trans hu_ge
    linarith [C_v_pos]
  have hcos_ge : (1 / 3 : ℝ) ≤ Real.cos (Complex.arg u) := by
    have habs_arg : |Complex.arg u| ≤ 3 * Real.pi / 8 := by
      rw [abs_le]; dsimp only [theta2'] at harg_hi; constructor <;> linarith [Real.pi_pos]
    have h1 := Real.strictAntiOn_cos.antitoneOn
      ⟨abs_nonneg _, habs_arg.trans (by linarith [Real.pi_pos])⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ habs_arg
    rw [Real.cos_abs] at h1
    have h2 : Real.cos (3 * Real.pi / 8) = Real.sin (Real.pi / 8) := by
      have : 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 := by ring
      rw [this, Real.cos_pi_div_two_sub]
    linarith
  have hure_ge : ‖u‖ / 3 ≤ u.re := by
    have hre_eq : u.re = ‖u‖ * Real.cos (Complex.arg u) := (Complex.norm_mul_cos_arg u).symm
    rw [hre_eq]; nlinarith
  have hure_ge4 : ‖u‖ / 4 ≤ u.re := by linarith
  have hure_pos : 0 < u.re := by linarith
  -- 2. Define cutoff `x_a := -(u.re / 6)` and check `u + x ∈ V_dom`, `1 ≤ (w_plus (u + x)).re` for all `x ≥ x_a`!
  set x_a : ℝ := -(u.re / 6)
  have hdom_ge : ∀ x : ℝ, x_a ≤ x → u + (x : ℂ) ∈ V_dom := by
    intro x hx
    right
    have hre_x : (5 / 6 : ℝ) * u.re ≤ (u + (x : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; dsimp only [x_a] at hx; linarith
    have hnorm_x : R_v < ‖u + (x : ℂ)‖ := by
      have h1 : (5 / 6 : ℝ) * u.re ≤ ‖u + (x : ℂ)‖ := hre_x.trans (Complex.re_le_norm _)
      have h2 : 6 * R_sec ≤ ‖u‖ := R_conv_ge_6Rsec.trans hu_ge
      have h3 : R_v + 1 ≤ R_sec := R_sec_ge_Rv
      linarith [R_v_pos]
    refine ⟨hnorm_x, ?_⟩
    -- Prove `Real.sin deltaV / 2 * ‖u + x‖ < dPhi (u + x)` using `sin φ ≥ 9/10`, `cos φ ≤ 1/6`, `sin δ < 1/12`!
    have hsin_phi : (9 / 10 : ℝ) ≤ Real.sin phiRay := by
      have h1 : phiRay = Real.pi / 2 - Real.pi / 24 := by dsimp [phiRay]; ring
      rw [h1, Real.sin_pi_div_two_sub]
      have h2 := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 24)
      have hsq : (Real.pi / 24) ^ 2 ≤ (4 / 24 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.pi_pos]) (by linarith [Real.pi_lt_four]) 2
      linarith
    have hcos_phi : Real.cos phiRay ≤ 1 / 6 := by
      have h1 : phiRay = Real.pi / 2 - Real.pi / 24 := by dsimp [phiRay]; ring
      rw [h1, Real.cos_pi_div_two_sub]
      have h2 := Real.sin_le (show (0 : ℝ) ≤ Real.pi / 24 by linarith [Real.pi_pos])
      linarith [Real.pi_lt_four]
    have hsin_d_lt : Real.sin deltaV / 2 < 1 / 24 := by
      have h1 := Real.sin_le deltaV_pos.le
      dsimp only [deltaV] at h1 ⊢; linarith [Real.pi_lt_four]
    have hd_ge : ‖u‖ / 12 + (9 / 10 : ℝ) * (x - x_a) ≤ dPhi (u + (x : ℂ)) := by
      dsimp only [dPhi]
      have hre_split : (u + (x : ℂ)).re = (5 / 6 : ℝ) * u.re + (x - x_a) := by
        simp only [Complex.add_re, Complex.ofReal_re]; dsimp only [x_a]; ring
      have him_x : (u + (x : ℂ)).im = u.im := by simp
      rw [hre_split, him_x]
      have h2 : u.im * Real.cos phiRay ≤ ‖u‖ * (1 / 6) := by
        have him_le : u.im ≤ ‖u‖ := Complex.im_le_norm u
        calc u.im * Real.cos phiRay ≤ ‖u‖ * Real.cos phiRay :=
              mul_le_mul_of_nonneg_right him_le cos_phiRay_pos.le
          _ ≤ ‖u‖ * (1 / 6) := mul_le_mul_of_nonneg_left hcos_phi hu_pos.le
      nlinarith
    have hnorm_le : ‖u + (x : ℂ)‖ ≤ 2 * ‖u‖ + (x - x_a) := by
      have hsplit : u + (x : ℂ) = (u + (x_a : ℂ)) + ((x - x_a : ℝ) : ℂ) := by push_cast; ring
      have hna : ‖u + (x_a : ℂ)‖ ≤ 2 * ‖u‖ := by
        calc ‖u + (x_a : ℂ)‖ ≤ ‖u‖ + |x_a| := by simpa [Complex.norm_real] using norm_add_le u (x_a : ℂ)
          _ = ‖u‖ + u.re / 6 := by dsimp [x_a]; rw [abs_neg, abs_of_pos (by linarith)]
          _ ≤ 2 * ‖u‖ := by linarith [Complex.re_le_norm u]
      rw [hsplit]
      calc _ ≤ ‖u + (x_a : ℂ)‖ + ‖((x - x_a : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖u + (x_a : ℂ)‖ + (x - x_a) := by
            rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hx)]
        _ ≤ 2 * ‖u‖ + (x - x_a) := by linarith
    have hnorm_pos : 0 < ‖u + (x : ℂ)‖ := lt_of_lt_of_le R_v_pos hnorm_x.le
    nlinarith
  have hw_re_pos : ∀ x : ℝ, x_a ≤ x → 1 ≤ (w_plus (u + (x : ℂ))).re := by
    intro x hx
    have hv := hdom_ge x hx
    have hcb := (w_plus_spec hv).1
    rw [Metric.mem_closedBall, dist_eq_norm] at hcb
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm _).trans hcb)).1
    have hre_x : (5 / 6 : ℝ) * u.re ≤ u.re + x := by dsimp only [x_a] at hx; linarith
    have hlog_nn : 0 ≤ (Complex.log (u + (x : ℂ))).re := by
      rw [Complex.log_re]
      have : (5 / 6 : ℝ) * u.re ≤ ‖u + (x : ℂ)‖ :=
        (by simp; linarith : (5 / 6 : ℝ) * u.re ≤ (u + (x : ℂ)).re).trans (Complex.re_le_norm _)
      exact Real.log_nonneg (by linarith)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hre_diff
    linarith
  set w_a : ℂ := w_plus (u + (x_a : ℂ))
  have hwa_re_ge1 : 1 ≤ w_a.re := hw_re_pos x_a le_rfl
  have hwa_re_le : w_a.re ≤ (11 / 12 : ℝ) * u.re := by
    have hv := hdom_ge x_a le_rfl
    have hcb := (w_plus_spec hv).1
    rw [Metric.mem_closedBall, dist_eq_norm] at hcb
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm _).trans hcb)).2
    have hnorm_a : ‖u + (x_a : ℂ)‖ ≤ 4 * u.re := by
      calc ‖u + (x_a : ℂ)‖ ≤ ‖u‖ + ‖(x_a : ℂ)‖ := norm_add_le _ _
        _ = ‖u‖ + |x_a| := by simp [Complex.norm_real]
        _ = ‖u‖ + u.re / 6 := by
            dsimp only [x_a]; rw [abs_neg, abs_of_pos (by linarith)]
        _ ≤ 4 * u.re := by linarith
    have hnorm_a_pos : 0 < ‖u + (x_a : ℂ)‖ := by
      have : (5 / 6 : ℝ) * u.re ≤ ‖u + (x_a : ℂ)‖ :=
        (by simp [x_a]; linarith : (5 / 6 : ℝ) * u.re ≤ (u + (x_a : ℂ)).re).trans (Complex.re_le_norm _)
      linarith
    have hlog_le : Real.log ‖u + (x_a : ℂ)‖ ≤ (1 / 12 : ℝ) * u.re - 1 := by
      have h1 : Real.log ‖u + (x_a : ℂ)‖ ≤ Real.log (4 * u.re) := Real.log_le_log hnorm_a_pos hnorm_a
      have h2 : Real.log (4 * u.re) = Real.log 192 + Real.log (u.re / 48) := by
        rw [← Real.log_mul (by norm_num) (by linarith)]; congr 1; ring
      have h3 : Real.log (u.re / 48) ≤ u.re / 48 - 1 := Real.log_le_sub_one_of_pos (by linarith)
      have h4 : Real.log 192 ≤ 10 := by
        have he : (192 : ℝ) ≤ Real.exp 10 := by
          have hp := Real.pow_div_factorial_le_exp (10 : ℝ) (by norm_num) 4
          norm_num [Nat.factorial] at hp; linarith
        calc Real.log 192 ≤ Real.log (Real.exp 10) := Real.log_le_log (by norm_num) he
          _ = 10 := Real.log_exp 10
      linarith [h1, h2, h3, h4, hure_ge4, hu_1e6]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.log_re] at hre_diff
    dsimp only [w_a, x_a] at hre_diff ⊢
    linarith
  have hwa_im_diff : |w_a.im - u.im| ≤ Real.pi + 1 := by
    have hv := hdom_ge x_a le_rfl
    have hcb := (w_plus_spec hv).1
    rw [Metric.mem_closedBall, dist_eq_norm] at hcb
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm _).trans hcb)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero, Complex.log_im] at him_diff
    have harg := abs_le.mp (Complex.abs_arg_le_pi (u + (x_a : ℂ)))
    rw [abs_le]; constructor <;> linarith
  -- 3. Deform the right ray `∫_{Ici 1} valleyIntegrand u (s + i u.im)` to `∫_{Ici x_a} exp(2x - exp x) * F_plus (u + x)`
  -- inside `Ω_pos := {w : ℂ | 0 < w.re}`!
  let Ω_pos : Set ℂ := {w : ℂ | 0 < w.re}
  have hΩ_open : IsOpen Ω_pos := isOpen_lt continuous_const Complex.continuous_re
  have hΩ_rect : ∀ p ∈ Ω_pos, ∀ q ∈ Ω_pos, Set.uIcc p.re q.re ×ℂ Set.uIcc p.im q.im ⊆ Ω_pos := by
    intro p hp q hq z hz
    rcases Set.mem_uIcc.mp hz.1 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_lt_of_le hp h1
    · exact lt_of_lt_of_le hq h1
  have hf_diff : DifferentiableOn ℂ (valleyIntegrand u) Ω_pos :=
    (differentiableOn_valleyIntegrand_w u).mono fun w hw => Or.inl hw
  have hF_int_xa : IntegrableOn (fun x : ℝ => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))
      (Set.Ici x_a) := by
    have hcont : ContinuousOn (fun x : ℝ => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))
        (Set.Ici x_a) :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).sub Real.continuous_exp))).continuousOn.mul
        (differentiableOn_F_plus.continuousOn.comp (continuous_const.add Complex.continuous_ofReal).continuousOn
          fun x hx => hdom_ge x hx)
    refine ((integrableOn_exp_neg_three_halves_abs.integrableOn).const_mul (3 * Real.exp 4 * (‖u‖ + 2))).mono'
      (hcont.aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hF_le : ‖F_plus (u + (x : ℂ))‖ ≤ 3 * (‖u‖ + |x|) := by
      have h1 := norm_F_plus_le (hdom_ge x hx)
      have h2 : ‖u + (x : ℂ)‖ ≤ ‖u‖ + |x| := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using norm_add_le u (x : ℂ)
      linarith
    have hk := gamma_kernel_mul_le (norm_nonneg u) x
    calc Real.exp (2 * x - Real.exp x) * ‖F_plus (u + (x : ℂ))‖
        ≤ Real.exp (2 * x - Real.exp x) * (3 * (‖u‖ + |x|)) :=
          mul_le_mul_of_nonneg_left hF_le (Real.exp_pos _).le
      _ = 3 * (Real.exp (2 * x - Real.exp x) * (‖u‖ + |x|)) := by ring
      _ ≤ 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * |x|)) :=
          mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = 3 * Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * |x|) := by ring
  -- Finite-`B` identity for `x_a ≤ B`:
  have hB_eq : ∀ B : ℝ, x_a ≤ B →
      (∫ s in (1 : ℝ)..(w_plus (u + (B : ℂ))).re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) -
      (∫ x in x_a..B, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) =
      (∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
      I * (∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)) +
      (valleyIntegrand u (w_plus (u + (B : ℂ))) - valleyIntegrand u w_a) -
      I * (∫ t in u.im..(w_plus (u + (B : ℂ))).im,
        valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)) := by
    intro B hB
    have hdom_uIcc : ∀ x ∈ Set.uIcc x_a B, u + (x : ℂ) ∈ V_dom := by
      intro x hx; rw [Set.uIcc_of_le hB] at hx; exact hdom_ge x hx.1
    have hL := integral_curve_eq_L_path hΩ_open hΩ_rect hf_diff (a := x_a) (b := B)
      (γ := fun x : ℝ => w_plus (u + (x : ℂ)))
      (γ' := fun x : ℝ => S_phi (w_plus (u + (x : ℂ))))
      (fun x hx => by rw [Set.uIcc_of_le hB] at hx; exact lt_of_lt_of_le zero_lt_one (hw_re_pos x hx.1))
      (fun x hx => by
        have hlin : HasDerivAt (fun τ : ℝ => u + (τ : ℂ)) 1 x := by
          simpa using (hasDerivAt_id x).ofReal_comp.const_add u
        exact ((hasDerivAt_w_plus (hdom_uIcc x hx)).comp x hlin).congr_deriv (mul_one _))
      (differentiableOn_S_phi.continuousOn.comp
        (differentiableOn_w_plus.continuousOn.comp (continuous_const.add Complex.continuous_ofReal).continuousOn hdom_uIcc)
        (fun x hx => (closedBall_log_props (hdom_uIcc x hx) (w_plus_spec (hdom_uIcc x hx)).1).1))
    have hIBP := integral_valleyIntegrand_w_plus_eq (u := u) (a := x_a) (b := B) hdom_uIcc
    -- Cauchy rectangle on `[w_a.re, (w_plus (u + B)).re] × [u.im, w_a.im]` inside `Ω_pos`!
    let p : ℂ := (w_a.re : ℂ) + (u.im : ℂ) * I
    let q : ℂ := ((w_plus (u + (B : ℂ))).re : ℂ) + (w_a.im : ℂ) * I
    have hp : p ∈ Ω_pos := by dsimp [Ω_pos, p]; simp; linarith
    have hq : q ∈ Ω_pos := by dsimp [Ω_pos, q]; simp; linarith [hw_re_pos B hB]
    have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (valleyIntegrand u) p q (hf_diff.mono (hΩ_rect p hp q hq))
    have hpre : p.re = w_a.re := by simp [p]
    have hpim : p.im = u.im := by simp [p]
    have hqre : q.re = (w_plus (u + (B : ℂ))).re := by simp [q]
    have hqim : q.im = w_a.im := by simp [q]
    rw [hpre, hpim, hqre, hqim] at hc
    simp only [smul_eq_mul] at hc
    have hcont_h : ∀ (r₁ r₂ : ℝ), 0 < r₁ → 0 < r₂ →
        ContinuousOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) (Set.uIcc r₁ r₂) := by
      intro r₁ r₂ hr₁ hr₂
      refine hf_diff.continuousOn.comp (Complex.continuous_ofReal.add continuous_const).continuousOn ?_
      intro s hs; dsimp [Ω_pos]; simp
      rcases Set.mem_uIcc.mp hs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have hcont_v : ∀ (r y₁ y₂ : ℝ), 0 < r →
        ContinuousOn (fun t : ℝ => valleyIntegrand u ((r : ℂ) + (t : ℂ) * I)) (Set.uIcc y₁ y₂) := by
      intro r y₁ y₂ hr
      refine hf_diff.continuousOn.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
      intro t _; dsimp [Ω_pos]; simp; exact hr
    have hh_add : (∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
        (∫ s in w_a.re..(w_plus (u + (B : ℂ))).re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) =
        ∫ s in (1 : ℝ)..(w_plus (u + (B : ℂ))).re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont_h 1 w_a.re zero_lt_one (by linarith)).intervalIntegrable
        (hcont_h w_a.re (w_plus (u + (B : ℂ))).re (by linarith) (by linarith [hw_re_pos B hB])).intervalIntegrable
    have hv_add : (∫ t in u.im..w_a.im, valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)) +
        (∫ t in w_a.im..(w_plus (u + (B : ℂ))).im, valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)) =
        ∫ t in u.im..(w_plus (u + (B : ℂ))).im, valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont_v _ _ _ (by linarith [hw_re_pos B hB])).intervalIntegrable
        (hcont_v _ _ _ (by linarith [hw_re_pos B hB])).intervalIntegrable
    linear_combination -hh_add + hIBP - hL + hc - I * hv_add
  -- Let `B → +∞` to obtain the exact contour split for `∫_{Ici 1} valleyIntegrand u (s + i u.im)`!
  obtain ⟨_, hre_top, him_lim⟩ := tendsto_w_plus_add_real u
  have hlim_ray : Tendsto (fun B : ℝ => ∫ s in (1 : ℝ)..(w_plus (u + (B : ℂ))).re,
      valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I))
      atTop (𝓝 (∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I))) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact intervalIntegral_tendsto_integral_Ioi 1
      ((integrableOn_Ici_iff_integrableOn_Ioi).mp (integrableOn_valleyIntegrand_right (by simp; positivity)))
      hre_top
  have hlim_F : Tendsto (fun B : ℝ => ∫ x in x_a..B,
      ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))
      atTop (𝓝 (∫ x in Set.Ici x_a, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact intervalIntegral_tendsto_integral_Ioi x_a
      ((integrableOn_Ici_iff_integrableOn_Ioi).mp hF_int_xa) tendsto_id
  have hlim_bB : Tendsto (fun B : ℝ => valleyIntegrand u (w_plus (u + (B : ℂ)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun B : ℝ => (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-B / 2)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (max 0 x_a)] with B hB
      have hB0 : 0 ≤ B := le_trans (le_max_left _ _) hB
      have hv := hdom_ge B (le_trans (le_max_right _ _) hB)
      have hval : valleyIntegrand u (w_plus (u + (B : ℂ))) =
          F_plus (u + (B : ℂ)) * Complex.exp ((B : ℂ) - Complex.exp (B : ℂ)) := by
        dsimp only [valleyIntegrand]
        rw [Ei_add_I_pi_w_plus hv, F_plus_eq_exp_sub hv]
        have : Complex.exp (-u) * Complex.exp (u + (B : ℂ)) = Complex.exp (B : ℂ) := by
          rw [← Complex.exp_add]; congr 1; ring
        rw [this, ← Complex.exp_add]; congr 1; ring
      rw [hval, norm_mul, Complex.norm_exp]
      have hre : ((B : ℂ) - Complex.exp (B : ℂ)).re = B - Real.exp B := by
        rw [Complex.sub_re, Complex.ofReal_re, ← Complex.ofReal_exp, Complex.ofReal_re]
      rw [hre]
      have hF_le : ‖F_plus (u + (B : ℂ))‖ ≤ 3 * (‖u‖ + B) := by
        have h1 := norm_F_plus_le hv
        have h2 : ‖u + (B : ℂ)‖ ≤ ‖u‖ + B := by
          calc _ ≤ ‖u‖ + ‖(B : ℂ)‖ := norm_add_le _ _
            _ = ‖u‖ + B := by simp [Complex.norm_real, abs_of_nonneg hB0]
        linarith
      have h1 : Real.exp (B - Real.exp B) ≤ Real.exp (2 * B - Real.exp B) := Real.exp_le_exp.mpr (by linarith)
      have hk := gamma_kernel_mul_le (norm_nonneg u) B
      rw [abs_of_nonneg hB0] at hk
      calc ‖F_plus (u + (B : ℂ))‖ * Real.exp (B - Real.exp B)
          ≤ (3 * (‖u‖ + B)) * Real.exp (2 * B - Real.exp B) :=
            mul_le_mul hF_le h1 (Real.exp_pos _).le (by positivity)
        _ = 3 * (Real.exp (2 * B - Real.exp B) * (‖u‖ + B)) := by ring
        _ ≤ 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * B)) :=
            mul_le_mul_of_nonneg_left hk (by norm_num)
        _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-B / 2) := by
            have : Real.exp (-(3 / 2) * B) ≤ Real.exp (-B / 2) := Real.exp_le_exp.mpr (by linarith)
            calc 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * B))
                = (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * B) := by ring
              _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-B / 2) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
    · have h1 : Tendsto (fun B : ℝ => (-B) / 2) atTop atBot := by
        have := Tendsto.const_mul_atTop_of_neg (show (-(1 / 2) : ℝ) < 0 by norm_num) tendsto_id
        exact this.congr fun B => by dsimp [id]; ring
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (3 * Real.exp 4 * (‖u‖ + 2))
  have hlim_vB : Tendsto (fun B : ℝ => I * ∫ t in u.im..(w_plus (u + (B : ℂ))).im,
      valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    let M_y : ℝ := |u.im| + Real.pi / 3
    obtain ⟨C, _, hdom⟩ := norm_valleyIntegrand_right_dom |u.re| M_y (abs_nonneg _) (by dsimp [M_y]; positivity)
    set S₁ : ℝ := max (max 16 (16 * M_y)) (32 / Real.cos phiRay ^ 2)
    have hev_im : ∀ᶠ B : ℝ in atTop, |(w_plus (u + (B : ℂ))).im - u.im| ≤ Real.pi / 3 := by
      have h := him_lim.eventually (Metric.ball_mem_nhds u.im (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 3))
      exact h.mono fun B hB => le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hB)
    have hev_re : ∀ᶠ B : ℝ in atTop, S₁ ≤ (w_plus (u + (B : ℂ))).re :=
      hre_top.eventually (Filter.eventually_ge_atTop S₁)
    refine squeeze_zero_norm' (a := fun B : ℝ => (C * (Real.pi / 3)) * Real.exp (-(w_plus (u + (B : ℂ))).re)) ?_ ?_
    · filter_upwards [hev_im, hev_re] with B himB hreB
      rw [norm_mul, Complex.norm_I, one_mul]
      have hbd : ∀ t ∈ Set.uIoc u.im (w_plus (u + (B : ℂ))).im,
          ‖valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)‖ ≤
            C * Real.exp (-(w_plus (u + (B : ℂ))).re) := by
        intro t ht
        have ht_mem := Set.uIoc_subset_uIcc ht
        have ht_strip : |t - u.im| ≤ Real.pi / 3 := by
          rw [abs_le] at himB ⊢
          rcases Set.mem_uIcc.mp ht_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [Real.pi_pos]
        have ht_My : |t| ≤ M_y := by
          have := abs_add_le (t - u.im) u.im
          rw [sub_add_cancel] at this; dsimp [M_y]; linarith
        exact (hdom u t le_rfl ht_My ht_strip _ hreB).1
      calc _ ≤ (C * Real.exp (-(w_plus (u + (B : ℂ))).re)) * |(w_plus (u + (B : ℂ))).im - u.im| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hbd
        _ ≤ (C * Real.exp (-(w_plus (u + (B : ℂ))).re)) * (Real.pi / 3) :=
            mul_le_mul_of_nonneg_left himB (by positivity)
        _ = (C * (Real.pi / 3)) * Real.exp (-(w_plus (u + (B : ℂ))).re) := by ring
    · have h0 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hre_top)
      simpa using h0.const_mul (C * (Real.pi / 3))
  have hsplit_ray : (∫ s in Set.Ici (1 : ℝ), valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) -
      (∫ x in Set.Ici x_a, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) =
      (∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
      I * (∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)) -
      valleyIntegrand u w_a := by
    have hlim_rhs : Tendsto (fun B : ℝ =>
        (∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
        I * (∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)) +
        (valleyIntegrand u (w_plus (u + (B : ℂ))) - valleyIntegrand u w_a) -
        I * (∫ t in u.im..(w_plus (u + (B : ℂ))).im,
          valleyIntegrand u (((w_plus (u + (B : ℂ))).re : ℂ) + (t : ℂ) * I)))
        atTop (𝓝 ((∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
          I * (∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)) -
          valleyIntegrand u w_a)) := by
      have h1 := ((tendsto_const_nhds (x := ∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)).add
        (tendsto_const_nhds (x := I * ∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)))).add
        (hlim_bB.sub (tendsto_const_nhds (x := valleyIntegrand u w_a)))).sub hlim_vB
      simpa [sub_eq_add_neg, add_assoc] using h1
    have hlim_lhs := hlim_ray.sub hlim_F
    have hlim_eq := hlim_rhs.congr' (by filter_upwards [Filter.eventually_ge_atTop x_a] with B hB; exact (hB_eq B hB).symm)
    exact tendsto_nhds_unique hlim_lhs hlim_eq
  -- 4. Bound EVERY ONE of the 6 error terms by `... * Real.exp (-(1 / 96) * ‖u‖)`!
  -- Useful elementary inequality: `(‖u‖ + 2) * exp (-u.re / 24) ≤ 200` (actually `≤ 100` for `u.re ≥ 10^5`!)
  have hu_exp_absorb : ∀ c : ℝ, (1 / 48 : ℝ) ≤ c → (‖u‖ + 2) * Real.exp (-c * u.re) ≤ 1 := by
    intro c hc
    have h1 : (c * u.re) ^ 2 / 2 ≤ Real.exp (c * u.re) := by
      simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (c * u.re) (by nlinarith) 2
    have hcu : ‖u‖ / 144 ≤ c * u.re := by nlinarith
    have h2 : ‖u‖ + 2 ≤ (c * u.re) ^ 2 / 2 := by nlinarith
    have hrew : Real.exp (-c * u.re) = (Real.exp (c * u.re))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
    rw [hrew, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h2.trans h1
  -- Term 1: Left ray `∫_{Iic 1} valleyIntegrand u (s - i/4)`!
  have hT1 : ‖∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)‖ ≤
      Real.exp (1 + K_L) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
    have hbd_pt : ∀ s ≤ (1 : ℝ),
        ‖valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)‖ ≤
          (Real.exp (K_L - u.re)) * Real.exp s := by
      intro s hs
      dsimp only [valleyIntegrand]
      rw [Complex.norm_exp]
      have hexpu1 : Real.exp (-u.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hprod : ‖Complex.exp (-u) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤ K_L := by
        rw [norm_mul, Complex.norm_exp, Complex.neg_re]
        calc Real.exp (-u.re) * ‖Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ)‖
            ≤ 1 * K_L := mul_le_mul hexpu1 (hEi_L s hs) (norm_nonneg _) zero_le_one
          _ = K_L := one_mul _
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
      have harg : (((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) - u -
            Complex.exp (-u) * (Ei_complex ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I) + I * (Real.pi : ℂ))).re ≤
          (K_L - u.re) + s := by
        rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
        linarith
      exact (Real.exp_le_exp.mpr harg).trans (le_of_eq (Real.exp_add _ _))
    have hint1 : IntegrableOn (fun s : ℝ => valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) (Set.Iic 1) := by
      have hcont : Continuous (fun s : ℝ => valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) :=
        (differentiableOn_valleyIntegrand_w u).continuousOn.comp_continuous
          (Complex.continuous_ofReal.add continuous_const) fun s => Or.inr (by simp)
      refine ((integrableOn_exp_Iic 1).const_mul (Real.exp (K_L - u.re))).mono' hcont.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs; exact hbd_pt s hs
    have hint_exp1 : ∫ s in Set.Iic (1 : ℝ), Real.exp s = Real.exp 1 := by
      have hsub : ∫ s in Set.Iic (1 : ℝ), Real.exp s = ∫ x in Set.Ici (-1 : ℝ), Real.exp (-x) := by
        rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ici]
        rw [← MeasureTheory.integral_neg_eq_self (fun x => Set.indicator (Set.Ici (-1 : ℝ)) (fun t => Real.exp (-t)) x)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only [Set.indicator, Set.mem_Iic, Set.mem_Ici, neg_neg]
        split_ifs with h1 h2
        · rfl
        · exact absurd (by linarith : -1 ≤ -s) h2
        · exact absurd (by linarith : s ≤ 1) h1
        · rfl
      rw [hsub, MeasureTheory.integral_Ici_eq_integral_Ioi]
      have hderiv : ∀ x ∈ Set.Ici (-1 : ℝ), HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-x)) x := by
        intro x _; simpa using ((hasDerivAt_id x).neg.exp).fun_neg
      have htend : Tendsto (fun t : ℝ => -Real.exp (-t)) atTop (𝓝 0) := by
        simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg
      have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
        ((integrableOn_Ici_iff_integrableOn_Ioi).mp (integrableOn_exp_neg_Ici (-1))) htend
      rw [hftc]; simp
    calc _ ≤ ∫ s in Set.Iic (1 : ℝ), ‖valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ s in Set.Iic (1 : ℝ), Real.exp (K_L - u.re) * Real.exp s :=
          setIntegral_mono_on hint1.norm ((integrableOn_exp_Iic 1).const_mul _) measurableSet_Iic hbd_pt
      _ = Real.exp (K_L - u.re) * Real.exp 1 := by rw [integral_const_mul, hint_exp1]
      _ = Real.exp (1 + K_L) * Real.exp (-u.re) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (1 + K_L) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
  -- Helper bound on `valleyIntegrand u (x + i y)` for `1 ≤ x ≤ (11/12) u.re` and `|y| ≤ ‖u‖ + π + 2`!
  have hrect_pt_bd : ∀ (x y : ℝ), 1 ≤ x → x ≤ (11 / 12 : ℝ) * u.re → |y| ≤ ‖u‖ + Real.pi + 2 →
      ‖valleyIntegrand u ((x : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp (K_Ei + x - u.re) := by
    intro x y hx1 hxu hy
    dsimp only [valleyIntegrand]
    rw [Complex.norm_exp]
    have hEi := norm_Ei_complex_add_I_pi_le_exp (y := y) hx1
    have hprod : ‖Complex.exp (-u) * (Ei_complex ((x : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ))‖ ≤ K_Ei := by
      rw [norm_mul, Complex.norm_exp, Complex.neg_re]
      have hexp1 : Real.exp (-u.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hy_abs : Real.exp (-u.re) * |y| ≤ 4 := by
        have hy_le : |y| ≤ 4 * (‖u‖ + 2) := by linarith [Real.pi_lt_four]
        have h := hu_exp_absorb 1 (by norm_num)
        rw [show (-1 : ℝ) * u.re = -u.re by ring] at h
        calc Real.exp (-u.re) * |y| ≤ Real.exp (-u.re) * (4 * (‖u‖ + 2)) :=
              mul_le_mul_of_nonneg_left hy_le (Real.exp_pos _).le
          _ = 4 * ((‖u‖ + 2) * Real.exp (-u.re)) := by ring
          _ ≤ 4 * 1 := by linarith
          _ = 4 := mul_one _
      have hexp_x : Real.exp (-u.re) * Real.exp x ≤ 1 := by
        rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
      calc Real.exp (-u.re) * ‖Ei_complex ((x : ℂ) + (y : ℂ) * I) + I * (Real.pi : ℂ)‖
          ≤ Real.exp (-u.re) * (‖Ei_complex (1 : ℂ)‖ + Real.pi + Real.exp 1 * |y| + Real.exp x) :=
            mul_le_mul_of_nonneg_left hEi (Real.exp_pos _).le
        _ = Real.exp (-u.re) * (‖Ei_complex (1 : ℂ)‖ + Real.pi) +
              Real.exp 1 * (Real.exp (-u.re) * |y|) + Real.exp (-u.re) * Real.exp x := by ring
        _ ≤ 1 * (‖Ei_complex (1 : ℂ)‖ + Real.pi) + Real.exp 1 * 4 + 1 := by
            have : 0 ≤ ‖Ei_complex (1 : ℂ)‖ + Real.pi := by positivity
            nlinarith [Real.exp_pos (1 : ℝ)]
        _ = K_Ei := by dsimp [K_Ei]; ring
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hprod)).1
    refine Real.exp_le_exp.mpr ?_
    rw [Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    linarith
  -- Term 2: Vertical segment `I * ∫ y in (-1/4)..u.im, valleyIntegrand u (1 + i y)`!
  have hT2 : ‖I * ∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp (1 + K_Ei) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
    rw [norm_mul, Complex.norm_I, one_mul]
    have hbd : ∀ y ∈ Set.uIoc (-1 / 4 : ℝ) u.im,
        ‖valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp (K_Ei + 1 - u.re) := by
      intro y hy
      have hy_mem := Set.uIoc_subset_uIcc hy
      have hy_abs : |y| ≤ ‖u‖ + Real.pi + 2 := by
        have him : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
        rw [abs_le] at him ⊢
        rcases Set.mem_uIcc.mp hy_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [Real.pi_pos]
      exact hrect_pt_bd 1 y le_rfl (by linarith) hy_abs
    have hlen : |u.im - (-1 / 4 : ℝ)| ≤ ‖u‖ + 2 := by
      have him : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
      rw [abs_le] at him ⊢; constructor <;> linarith
    have habs := hu_exp_absorb (1 / 2) (by norm_num)
    calc _ ≤ Real.exp (K_Ei + 1 - u.re) * |u.im - (-1 / 4 : ℝ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ ≤ Real.exp (K_Ei + 1 - u.re) * (‖u‖ + 2) := mul_le_mul_of_nonneg_left hlen (Real.exp_pos _).le
      _ = Real.exp (1 + K_Ei) * ((‖u‖ + 2) * Real.exp (-(1 / 2 : ℝ) * u.re)) * Real.exp (-(1 / 2 : ℝ) * u.re) := by
          have : Real.exp (K_Ei + 1 - u.re) =
              Real.exp (1 + K_Ei) * Real.exp (-(1 / 2 : ℝ) * u.re) * Real.exp (-(1 / 2 : ℝ) * u.re) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          rw [this]; ring
      _ ≤ Real.exp (1 + K_Ei) * 1 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
          have h1 : Real.exp (-(1 / 2 : ℝ) * u.re) ≤ Real.exp (-(1 / 96 : ℝ) * ‖u‖) :=
            Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul (mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le) h1 (Real.exp_pos _).le (by positivity)
      _ = Real.exp (1 + K_Ei) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by ring
  -- Term 3: Horizontal segment `∫ s in 1..w_a.re, valleyIntegrand u (s + i u.im)`!
  have hT3 : ‖∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)‖ ≤
      Real.exp (1 + K_Ei) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
    have hbd : ∀ s ∈ Set.uIoc (1 : ℝ) w_a.re,
        ‖valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)‖ ≤ Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) := by
      intro s hs
      rw [Set.uIoc_of_le hwa_re_ge1] at hs
      have hy_abs : |u.im| ≤ ‖u‖ + Real.pi + 2 := by linarith [Complex.abs_im_le_norm u, Real.pi_pos]
      have h1 := hrect_pt_bd s u.im hs.1.le (hs.2.trans hwa_re_le) hy_abs
      exact h1.trans (Real.exp_le_exp.mpr (by linarith [hs.2]))
    have hlen : |w_a.re - 1| ≤ ‖u‖ + 2 := by
      rw [abs_of_nonneg (by linarith)]; linarith [Complex.re_le_norm u]
    have habs := hu_exp_absorb (1 / 24) (by norm_num)
    calc _ ≤ Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) * |w_a.re - 1| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ ≤ Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) * (‖u‖ + 2) := mul_le_mul_of_nonneg_left hlen (Real.exp_pos _).le
      _ = Real.exp K_Ei * ((‖u‖ + 2) * Real.exp (-(1 / 24 : ℝ) * u.re)) * Real.exp (-(1 / 24 : ℝ) * u.re) := by
          have : Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) =
              Real.exp K_Ei * Real.exp (-(1 / 24 : ℝ) * u.re) * Real.exp (-(1 / 24 : ℝ) * u.re) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          rw [this]; ring
      _ ≤ Real.exp (1 + K_Ei) * 1 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
          have h1 : Real.exp K_Ei ≤ Real.exp (1 + K_Ei) := Real.exp_le_exp.mpr (by linarith)
          have h2 : Real.exp (-(1 / 24 : ℝ) * u.re) ≤ Real.exp (-(1 / 96 : ℝ) * ‖u‖) :=
            Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul (mul_le_mul h1 habs (by positivity) (Real.exp_pos _).le) h2 (Real.exp_pos _).le (by positivity)
      _ = Real.exp (1 + K_Ei) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by ring
  -- Term 4: Vertical segment `I * ∫ t in u.im..w_a.im, valleyIntegrand u (w_a.re + i t)`!
  have hT4 : ‖I * ∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)‖ ≤
      (Real.pi + 1) * Real.exp (K_Ei + Real.pi + 1) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
    rw [norm_mul, Complex.norm_I, one_mul]
    have hbd : ∀ t ∈ Set.uIoc u.im w_a.im,
        ‖valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)‖ ≤ Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) := by
      intro t ht
      have ht_mem := Set.uIoc_subset_uIcc ht
      have ht_abs : |t| ≤ ‖u‖ + Real.pi + 2 := by
        have him : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
        have hwa_im : |w_a.im| ≤ ‖u‖ + Real.pi + 1 := by
          have := abs_add_le (w_a.im - u.im) u.im; rw [sub_add_cancel] at this; linarith
        rw [abs_le] at him hwa_im ⊢
        rcases Set.mem_uIcc.mp ht_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [Real.pi_pos]
      exact (hrect_pt_bd w_a.re t hwa_re_ge1 hwa_re_le ht_abs).trans (Real.exp_le_exp.mpr (by linarith))
    calc _ ≤ Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) * |w_a.im - u.im| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ ≤ Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) * (Real.pi + 1) :=
          mul_le_mul_of_nonneg_left hwa_im_diff (Real.exp_pos _).le
      _ = (Real.pi + 1) * Real.exp K_Ei * Real.exp (-(1 / 12 : ℝ) * u.re) := by
          have : Real.exp (K_Ei - (1 / 12 : ℝ) * u.re) = Real.exp K_Ei * Real.exp (-(1 / 12 : ℝ) * u.re) := by
            rw [sub_eq_add_neg, Real.exp_add]; ring
          rw [this]; ring
      _ ≤ (Real.pi + 1) * Real.exp (K_Ei + Real.pi + 1) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
          have h1 : Real.exp K_Ei ≤ Real.exp (K_Ei + Real.pi + 1) := Real.exp_le_exp.mpr (by linarith [Real.pi_pos])
          have h2 : Real.exp (-(1 / 12 : ℝ) * u.re) ≤ Real.exp (-(1 / 96 : ℝ) * ‖u‖) :=
            Real.exp_le_exp.mpr (by linarith)
          gcongr
  -- Term 5: IBP boundary term `valleyIntegrand u w_a`!
  have hT5 : ‖valleyIntegrand u w_a‖ ≤ 6 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
    have hv := hdom_ge x_a le_rfl
    have hval : valleyIntegrand u w_a =
        F_plus (u + (x_a : ℂ)) * Complex.exp ((x_a : ℂ) - Complex.exp (x_a : ℂ)) := by
      dsimp only [valleyIntegrand, w_a]
      rw [Ei_add_I_pi_w_plus hv, F_plus_eq_exp_sub hv]
      have hce : Complex.exp (-u) * Complex.exp (u + (x_a : ℂ)) = Complex.exp (x_a : ℂ) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [hce, ← Complex.exp_add]
      congr 1; ring
    rw [hval, norm_mul, Complex.norm_exp]
    have hre : ((x_a : ℂ) - Complex.exp (x_a : ℂ)).re = x_a - Real.exp x_a := by
      rw [Complex.sub_re, Complex.ofReal_re, ← Complex.ofReal_exp, Complex.ofReal_re]
    rw [hre]
    have hF_le : ‖F_plus (u + (x_a : ℂ))‖ ≤ 6 * (‖u‖ + 2) := by
      have h1 := norm_F_plus_le hv
      have h2 : ‖u + (x_a : ℂ)‖ ≤ 2 * ‖u‖ := by
        calc _ ≤ ‖u‖ + |x_a| := by simpa [Complex.norm_real] using norm_add_le u (x_a : ℂ)
          _ = ‖u‖ + u.re / 6 := by dsimp [x_a]; rw [abs_neg, abs_of_pos (by linarith)]
          _ ≤ 2 * ‖u‖ := by linarith [Complex.re_le_norm u]
      linarith
    have h1 : Real.exp (x_a - Real.exp x_a) ≤ Real.exp (-(1 / 6 : ℝ) * u.re) :=
      Real.exp_le_exp.mpr (by dsimp [x_a]; linarith [Real.exp_pos x_a])
    have habs := hu_exp_absorb (1 / 12) (by norm_num)
    calc ‖F_plus (u + (x_a : ℂ))‖ * Real.exp (x_a - Real.exp x_a)
        ≤ (6 * (‖u‖ + 2)) * Real.exp (-(1 / 6 : ℝ) * u.re) :=
          mul_le_mul hF_le h1 (Real.exp_pos _).le (by positivity)
      _ = 6 * ((‖u‖ + 2) * Real.exp (-(1 / 12 : ℝ) * u.re)) * Real.exp (-(1 / 12 : ℝ) * u.re) := by
          have : Real.exp (-(1 / 6 : ℝ) * u.re) = Real.exp (-(1 / 12 : ℝ) * u.re) * Real.exp (-(1 / 12 : ℝ) * u.re) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]; ring
      _ ≤ 6 * 1 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
          have h2 : Real.exp (-(1 / 12 : ℝ) * u.re) ≤ Real.exp (-(1 / 96 : ℝ) * ‖u‖) :=
            Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul (by linarith) h2 (Real.exp_pos _).le (by norm_num)
      _ = 6 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by ring
  -- Term 6: Tail of `∫_{Ici x_a}` outside `Icc (-(‖u‖ / 24)) (‖u‖ / 24)`!
  have hxa_le : x_a ≤ -(‖u‖ / 24) := by dsimp [x_a]; linarith
  have hT6 : ‖(∫ x in Set.Ici x_a, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) -
        (∫ x in Set.Icc (-(‖u‖ / 24)) (‖u‖ / 24), ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))‖ ≤
      6 * Real.exp 4 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
    let f : ℝ → ℂ := fun x => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))
    let L : ℝ := ‖u‖ / 24
    have hL_pos : 0 < L := by dsimp [L]; linarith
    have hxa_L : x_a ≤ -L := hxa_le
    have hsplit_set : Set.Ici x_a = (Set.Ico x_a (-L) ∪ Set.Icc (-L) L) ∪ Set.Ioi L := by
      ext x; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ico, Set.mem_Icc, Set.mem_Ioi]
      constructor
      · intro hx
        by_cases h1 : x < -L
        · exact Or.inl (Or.inl ⟨hx, h1⟩)
        · push Not at h1
          by_cases h2 : x ≤ L
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · push Not at h2; exact Or.inr h2
      · intro hx
        rcases hx with (⟨h1, _⟩ | ⟨h1, _⟩) | h1 <;> linarith
    have hdisj1 : Disjoint (Set.Ico x_a (-L)) (Set.Icc (-L) L) :=
      Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h2.1 h1.2
    have hdisj2 : Disjoint (Set.Ico x_a (-L) ∪ Set.Icc (-L) L) (Set.Ioi L) :=
      Set.disjoint_left.mpr fun _ h1 h2 => by
        have h2' : L < _ := Set.mem_Ioi.mp h2
        rcases h1 with h1' | h1'
        · exact not_lt_of_ge (by linarith [h1'.2, hL_pos] : _ ≤ L) h2'
        · exact not_lt_of_ge h1'.2 h2'
    have hint_1 : IntegrableOn f (Set.Ico x_a (-L)) := hF_int_xa.mono_set (fun x hx => hx.1)
    have hint_2 : IntegrableOn f (Set.Icc (-L) L) :=
      hF_int_xa.mono_set (fun x hx => Set.mem_Ici.mpr (by linarith [(Set.mem_Icc.mp hx).1, hxa_L]))
    have hint_3 : IntegrableOn f (Set.Ioi L) :=
      hF_int_xa.mono_set (fun x hx => Set.mem_Ici.mpr (by linarith [Set.mem_Ioi.mp hx, hxa_L, hL_pos]))
    have hdiff_eq : (∫ x in Set.Ici x_a, f x) - (∫ x in Set.Icc (-L) L, f x) =
        (∫ x in Set.Ico x_a (-L), f x) + (∫ x in Set.Ioi L, f x) := by
      rw [hsplit_set, MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioi (hint_1.union hint_2) hint_3,
        MeasureTheory.setIntegral_union hdisj1 measurableSet_Icc hint_1 hint_2]
      ring
    rw [hdiff_eq]
    have hdom_f : ∀ x ≥ x_a, ‖f x‖ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) := by
      intro x hx
      dsimp only [f]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hF_le : ‖F_plus (u + (x : ℂ))‖ ≤ 3 * (‖u‖ + |x|) := by
        have h1 := norm_F_plus_le (hdom_ge x hx)
        have h2 : ‖u + (x : ℂ)‖ ≤ ‖u‖ + |x| := by simpa [Complex.norm_real] using norm_add_le u (x : ℂ)
        linarith
      have hk := gamma_kernel_mul_le (norm_nonneg u) x
      calc _ ≤ Real.exp (2 * x - Real.exp x) * (3 * (‖u‖ + |x|)) :=
            mul_le_mul_of_nonneg_left hF_le (Real.exp_pos _).le
        _ = 3 * (Real.exp (2 * x - Real.exp x) * (‖u‖ + |x|)) := by ring
        _ ≤ 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * |x|)) := mul_le_mul_of_nonneg_left hk (by norm_num)
        _ = (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) := by ring
    obtain ⟨htail_L, htail_R⟩ := integral_exp_neg_three_halves_tails hL_pos.le
    have hb_left : ‖∫ x in Set.Ico x_a (-L), f x‖ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) := by
      calc _ ≤ ∫ x in Set.Ico x_a (-L), ‖f x‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x in Set.Ico x_a (-L), (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) :=
            setIntegral_mono_on hint_1.norm (integrableOn_exp_neg_three_halves_abs.integrableOn.const_mul _)
              measurableSet_Ico fun x hx => hdom_f x hx.1
        _ = (3 * Real.exp 4 * (‖u‖ + 2)) * ∫ x in Set.Ico x_a (-L), Real.exp (-(3 / 2) * |x|) :=
            integral_const_mul _ _
        _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * ∫ x in Set.Iic (-L), Real.exp (-(3 / 2) * |x|) :=
            mul_le_mul_of_nonneg_left (setIntegral_mono_set integrableOn_exp_neg_three_halves_abs.integrableOn
              (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
              (Filter.Eventually.of_forall fun x hx => le_of_lt hx.2)) (by positivity)
        _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) :=
            mul_le_mul_of_nonneg_left htail_L (by positivity)
    have hb_right : ‖∫ x in Set.Ioi L, f x‖ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) := by
      calc _ ≤ ∫ x in Set.Ioi L, ‖f x‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x in Set.Ioi L, (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) :=
            setIntegral_mono_on hint_3.norm (integrableOn_exp_neg_three_halves_abs.integrableOn.const_mul _)
              measurableSet_Ioi fun x hx => hdom_f x (by linarith [Set.mem_Ioi.mp hx, hxa_L, hL_pos])
        _ = (3 * Real.exp 4 * (‖u‖ + 2)) * ∫ x in Set.Ioi L, Real.exp (-(3 / 2) * |x|) :=
            integral_const_mul _ _
        _ = (3 * Real.exp 4 * (‖u‖ + 2)) * ∫ x in Set.Ici L, Real.exp (-(3 / 2) * |x|) := by
            rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
        _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) :=
            mul_le_mul_of_nonneg_left htail_R (by positivity)
    have habs_L : (‖u‖ + 2) * Real.exp (-(1 / 32 : ℝ) * ‖u‖) ≤ 1 := by
      have h1 := hu_exp_absorb (1 / 32) (by norm_num)
      have h2 : Real.exp (-(1 / 32 : ℝ) * ‖u‖) ≤ Real.exp (-(1 / 32 : ℝ) * u.re) :=
        Real.exp_le_exp.mpr (by linarith [Complex.re_le_norm u])
      calc (‖u‖ + 2) * Real.exp (-(1 / 32 : ℝ) * ‖u‖)
          ≤ (‖u‖ + 2) * Real.exp (-(1 / 32 : ℝ) * u.re) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 1 := h1
    have hexp_L : Real.exp (-(3 / 2) * L) = Real.exp (-(1 / 32 : ℝ) * ‖u‖) * Real.exp (-(1 / 32 : ℝ) * ‖u‖) := by
      rw [← Real.exp_add]; dsimp [L]; congr 1; ring
    calc _ ≤ ‖∫ x in Set.Ico x_a (-L), f x‖ + ‖∫ x in Set.Ioi L, f x‖ := norm_add_le _ _
      _ ≤ (6 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) := by linarith [hb_left, hb_right]
      _ = 6 * Real.exp 4 * ((‖u‖ + 2) * Real.exp (-(1 / 32 : ℝ) * ‖u‖)) * Real.exp (-(1 / 32 : ℝ) * ‖u‖) := by
          rw [hexp_L]; ring
      _ ≤ 6 * Real.exp 4 * 1 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
          have h2 : Real.exp (-(1 / 32 : ℝ) * ‖u‖) ≤ Real.exp (-(1 / 96 : ℝ) * ‖u‖) :=
            Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul (mul_le_mul_of_nonneg_left habs_L (by positivity)) h2 (Real.exp_pos _).le (by positivity)
      _ = 6 * Real.exp 4 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by ring
  -- Combine all 6 error terms!
  have htot_eq : I_entire u - ∫ x in Set.Icc (-(‖u‖ / 24)) (‖u‖ / 24),
        ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)) =
      (∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) +
      (I * ∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) +
      (∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
      (I * ∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)) -
      valleyIntegrand u w_a +
      ((∫ x in Set.Ici x_a, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) -
        (∫ x in Set.Icc (-(‖u‖ / 24)) (‖u‖ / 24), ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))) := by
    dsimp only [I_entire, J_strip]; linear_combination hsplit_ray
  rw [htot_eq]
  have htri : ‖(∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)) +
        (I * ∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)) +
        (∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)) +
        (I * ∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)) -
        valleyIntegrand u w_a +
        ((∫ x in Set.Ici x_a, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) -
          (∫ x in Set.Icc (-(‖u‖ / 24)) (‖u‖ / 24), ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))))‖ ≤
      ‖∫ s in Set.Iic (1 : ℝ), valleyIntegrand u ((s : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I)‖ +
      ‖I * ∫ y in (-1 / 4 : ℝ)..u.im, valleyIntegrand u ((1 : ℂ) + (y : ℂ) * I)‖ +
      ‖∫ s in (1 : ℝ)..w_a.re, valleyIntegrand u ((s : ℂ) + (u.im : ℂ) * I)‖ +
      ‖I * ∫ t in u.im..w_a.im, valleyIntegrand u ((w_a.re : ℂ) + (t : ℂ) * I)‖ +
      ‖valleyIntegrand u w_a‖ +
      ‖(∫ x in Set.Ici x_a, ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))) -
        (∫ x in Set.Icc (-(‖u‖ / 24)) (‖u‖ / 24), ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ)))‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl))
      le_rfl)) le_rfl)
  have hpi5 : Real.pi + 1 ≤ 100 := by linarith [Real.pi_lt_four]
  have hsum_le : Real.exp (1 + K_L) + Real.exp (1 + K_Ei) + Real.exp (1 + K_Ei) +
      (Real.pi + 1) * Real.exp (K_Ei + Real.pi + 1) + 6 + 6 * Real.exp 4 ≤ C_R := by
    dsimp only [C_R]; nlinarith [Real.exp_pos (1 + K_L), Real.exp_pos (1 + K_Ei),
      Real.exp_pos (K_Ei + Real.pi + 1), Real.exp_pos (4 : ℝ)]
  have hexp_pos := Real.exp_pos (-(1 / 96 : ℝ) * ‖u‖)
  nlinarith [htri, hT1, hT2, hT3, hT4, hT5, hT6]

/-- **Main Section 4 Export**: Unified truncated convolution representation of `I_entire` across
the ENTIRE enlarged closed sector `rotatedClosedSector theta1' theta2' R_conv` (width `7π/6 > π`)! -/
theorem I_entire_truncated_conv_bound :
    ∃ C_conv > 0, ∃ c_conv > 0, ∀ u ∈ rotatedClosedSector theta1' theta2' R_conv,
      ‖I_entire u - ∫ x in Set.Icc (-(‖u‖ / 24)) (‖u‖ / 24),
          ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))‖ ≤
        C_conv * Real.exp (-c_conv * ‖u‖) := by
  obtain ⟨C_R, hCR, hright⟩ := I_entire_conv_bound_right
  refine ⟨max C_R (6 * Real.exp 4), lt_of_lt_of_le hCR (le_max_left _ _), 1 / 96, by norm_num, fun u hu => ?_⟩
  by_cases him : u.im < -C_v - 1
  · -- Region I: `I_entire u = ∫_ℝ exp(2x - exp x) * F_plus (u + x)` + tail bound!
    rw [I_entire_eq_conv_lower him]
    have hu_ge : R_conv ≤ ‖u‖ := hu.1
    have hu_1e6 : (1000000 : ℝ) ≤ ‖u‖ := by
      have h := R_conv_ge_1e6.trans hu_ge; norm_num at h; exact h
    have hu_pos : 0 < ‖u‖ := by linarith
    have hdom_all : ∀ x : ℝ, u + (x : ℂ) ∈ V_dom := fun x => Or.inl (by simp; linarith)
    let f : ℝ → ℂ := fun x => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ) * F_plus (u + (x : ℂ))
    let L : ℝ := ‖u‖ / 24
    have hL_pos : 0 < L := by dsimp [L]; linarith
    have hdom_f : ∀ x : ℝ, ‖f x‖ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) := by
      intro x; dsimp only [f]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hF_le : ‖F_plus (u + (x : ℂ))‖ ≤ 3 * (‖u‖ + |x|) := by
        have h1 := norm_F_plus_le (hdom_all x)
        have h2 : ‖u + (x : ℂ)‖ ≤ ‖u‖ + |x| := by simpa [Complex.norm_real] using norm_add_le u (x : ℂ)
        linarith
      have hk := gamma_kernel_mul_le (norm_nonneg u) x
      calc _ ≤ Real.exp (2 * x - Real.exp x) * (3 * (‖u‖ + |x|)) :=
            mul_le_mul_of_nonneg_left hF_le (Real.exp_pos _).le
        _ = 3 * (Real.exp (2 * x - Real.exp x) * (‖u‖ + |x|)) := by ring
        _ ≤ 3 * (Real.exp 4 * (‖u‖ + 2) * Real.exp (-(3 / 2) * |x|)) := mul_le_mul_of_nonneg_left hk (by norm_num)
        _ = (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) := by ring
    have hf_int : Integrable f volume := by
      have hcont : Continuous f :=
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          ((continuous_const.mul continuous_id).sub Real.continuous_exp))).mul
          (differentiableOn_F_plus.continuousOn.comp_continuous (continuous_const.add Complex.continuous_ofReal) hdom_all)
      exact (integrableOn_exp_neg_three_halves_abs.const_mul _).mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall hdom_f)
    have hsplit : (Set.univ : Set ℝ) = (Set.Iio (-L) ∪ Set.Icc (-L) L) ∪ Set.Ioi L := by
      ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, true_iff]
      by_cases h1 : x < -L
      · exact Or.inl (Or.inl h1)
      · push Not at h1
        by_cases h2 : x ≤ L
        · exact Or.inl (Or.inr ⟨h1, h2⟩)
        · push Not at h2; exact Or.inr h2
    have hdisj1 : Disjoint (Set.Iio (-L)) (Set.Icc (-L) L) :=
      Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h2.1 h1
    have hdisj2 : Disjoint (Set.Iio (-L) ∪ Set.Icc (-L) L) (Set.Ioi L) :=
      Set.disjoint_left.mpr fun _ h1 h2 => by
        have h2' : L < _ := Set.mem_Ioi.mp h2
        rcases h1 with h1' | h1'
        · have h1'' : _ < -L := Set.mem_Iio.mp h1'
          exact not_lt_of_ge (by linarith [h1'', hL_pos] : _ ≤ L) h2'
        · exact not_lt_of_ge h1'.2 h2'
    have hdiff_eq : (∫ x : ℝ, f x) - (∫ x in Set.Icc (-L) L, f x) =
        (∫ x in Set.Iio (-L), f x) + (∫ x in Set.Ioi L, f x) := by
      rw [← MeasureTheory.setIntegral_univ, hsplit,
        MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioi
          (hf_int.integrableOn.union hf_int.integrableOn) hf_int.integrableOn,
        MeasureTheory.setIntegral_union hdisj1 measurableSet_Icc hf_int.integrableOn hf_int.integrableOn]
      ring
    rw [hdiff_eq]
    obtain ⟨htail_L, htail_R⟩ := integral_exp_neg_three_halves_tails hL_pos.le
    have hb_left : ‖∫ x in Set.Iio (-L), f x‖ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) := by
      calc _ ≤ ∫ x in Set.Iio (-L), ‖f x‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x in Set.Iio (-L), (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) :=
            setIntegral_mono_on hf_int.integrableOn.norm
              (integrableOn_exp_neg_three_halves_abs.integrableOn.const_mul _) measurableSet_Iio fun x _ => hdom_f x
        _ = (3 * Real.exp 4 * (‖u‖ + 2)) * ∫ x in Set.Iic (-L), Real.exp (-(3 / 2) * |x|) := by
            rw [integral_const_mul, MeasureTheory.integral_Iic_eq_integral_Iio]
        _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) :=
            mul_le_mul_of_nonneg_left htail_L (by positivity)
    have hb_right : ‖∫ x in Set.Ioi L, f x‖ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) := by
      calc _ ≤ ∫ x in Set.Ioi L, ‖f x‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x in Set.Ioi L, (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * |x|) :=
            setIntegral_mono_on hf_int.integrableOn.norm
              (integrableOn_exp_neg_three_halves_abs.integrableOn.const_mul _) measurableSet_Ioi fun x _ => hdom_f x
        _ = (3 * Real.exp 4 * (‖u‖ + 2)) * ∫ x in Set.Ici L, Real.exp (-(3 / 2) * |x|) := by
            rw [integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi]
        _ ≤ (3 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) :=
            mul_le_mul_of_nonneg_left htail_R (by positivity)
    have habs_L : (‖u‖ + 2) * Real.exp (-(1 / 32 : ℝ) * ‖u‖) ≤ 1 := by
      have h1 : ((1 / 32 : ℝ) * ‖u‖) ^ 2 / 2 ≤ Real.exp ((1 / 32 : ℝ) * ‖u‖) := by
        simpa [Nat.factorial] using Real.pow_div_factorial_le_exp ((1 / 32 : ℝ) * ‖u‖) (by positivity) 2
      have h2 : ‖u‖ + 2 ≤ ((1 / 32 : ℝ) * ‖u‖) ^ 2 / 2 := by nlinarith
      have hrew : Real.exp (-(1 / 32 : ℝ) * ‖u‖) = (Real.exp ((1 / 32 : ℝ) * ‖u‖))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [hrew, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      exact h2.trans h1
    have hexp_L : Real.exp (-(3 / 2) * L) = Real.exp (-(1 / 32 : ℝ) * ‖u‖) * Real.exp (-(1 / 32 : ℝ) * ‖u‖) := by
      rw [← Real.exp_add]; dsimp [L]; congr 1; ring
    calc _ ≤ ‖∫ x in Set.Iio (-L), f x‖ + ‖∫ x in Set.Ioi L, f x‖ := norm_add_le _ _
      _ ≤ (6 * Real.exp 4 * (‖u‖ + 2)) * Real.exp (-(3 / 2) * L) := by linarith [hb_left, hb_right]
      _ = 6 * Real.exp 4 * ((‖u‖ + 2) * Real.exp (-(1 / 32 : ℝ) * ‖u‖)) * Real.exp (-(1 / 32 : ℝ) * ‖u‖) := by
          rw [hexp_L]; ring
      _ ≤ 6 * Real.exp 4 * 1 * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
          have h2 : Real.exp (-(1 / 32 : ℝ) * ‖u‖) ≤ Real.exp (-(1 / 96 : ℝ) * ‖u‖) :=
            Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul (mul_le_mul_of_nonneg_left habs_L (by positivity)) h2 (Real.exp_pos _).le (by positivity)
      _ ≤ max C_R (6 * Real.exp 4) * Real.exp (-(1 / 96 : ℝ) * ‖u‖) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · push Not at him
    exact (hright u hu him).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-! ### 5. Shift-Integration Gevrey-1 Asymptotic Expansion of `I_entire u / u` on `Σ₀` -/

/-- Elementary factorial product inequality `n! * m! ≤ (n + m)!`. -/
lemma factorial_mul_factorial_le (n m : ℕ) :
    (n.factorial : ℝ) * (m.factorial : ℝ) ≤ ((n + m).factorial : ℝ) := by
  have h1 : ((n + m).choose n * n.factorial * m.factorial : ℕ) = (n + m).factorial := by
    simpa [Nat.add_sub_cancel_left] using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n m)
  have hpos : 1 ≤ (n + m).choose n := Nat.choose_pos (Nat.le_add_right n m)
  have hnat : n.factorial * m.factorial ≤ (n + m).factorial := by
    calc n.factorial * m.factorial = 1 * n.factorial * m.factorial := by ring
      _ ≤ (n + m).choose n * n.factorial * m.factorial := by gcongr
      _ = (n + m).factorial := h1
  exact_mod_cast hnat

/-- Elementary exponential-to-Gevrey bound: `exp (-c * r) ≤ (1 / c) ^ k * k! / r ^ k` for `c, r > 0`. -/
lemma exp_neg_mul_le_factorial {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (k : ℕ) :
    Real.exp (-c * r) ≤ (1 / c) ^ k * (k.factorial : ℝ) / r ^ k := by
  have h1 : (c * r) ^ k / (k.factorial : ℝ) ≤ Real.exp (c * r) :=
    Real.pow_div_factorial_le_exp (c * r) (by positivity) k
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have h2 : Real.exp (-c * r) = (Real.exp (c * r))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h2]
  have hinv : (Real.exp (c * r))⁻¹ ≤ ((c * r) ^ k / (k.factorial : ℝ))⁻¹ :=
    inv_anti₀ (by positivity) h1
  calc (Real.exp (c * r))⁻¹
      ≤ ((c * r) ^ k / (k.factorial : ℝ))⁻¹ := hinv
    _ = (1 / c) ^ k * (k.factorial : ℝ) / r ^ k := by
        rw [inv_div, mul_pow, one_div, inv_pow]
        field_simp [hc.ne', hr.ne']

lemma nat_add_one_sq_le_four_pow (d : ℕ) : ((d : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ d := by
  induction d with
  | zero => norm_num
  | succ n ih =>
    push_cast
    have h4 : (4 : ℝ) ^ (n + 1) = 4 * (4 : ℝ) ^ n := by rw [pow_succ]; ring
    rw [h4]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

lemma nat_add_one_cube_le_eight_pow (N : ℕ) : ((N : ℝ) + 1) ^ 3 ≤ (8 : ℝ) ^ N := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    push_cast
    have h8 : (8 : ℝ) ^ (n + 1) = 8 * (8 : ℝ) ^ n := by rw [pow_succ]; ring
    rw [h8]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hcube : ((n : ℝ) + 1 + 1) ^ 3 ≤ 8 * ((n : ℝ) + 1) ^ 3 := by
      have hlin : (n : ℝ) + 1 + 1 ≤ 2 * ((n : ℝ) + 1) := by linarith
      calc ((n : ℝ) + 1 + 1) ^ 3 ≤ (2 * ((n : ℝ) + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) hlin 3
        _ = 8 * ((n : ℝ) + 1) ^ 3 := by ring
    linarith

/-- Uniform Cauchy Taylor coefficient of a function `g : ℂ → ℂ` on `Metric.closedBall 0 (1 / 2)`. -/
@[expose] def taylorCoeffHalf (g : ℂ → ℂ) (m : ℕ) : ℂ :=
  (cauchyPowerSeries g 0 (1 / 2 : ℝ)).coeff m

/-- Coefficient bound `‖taylorCoeffHalf g m‖ ≤ M * 2 ^ m` for `g` bounded by `M` on `closedBall 0 (1 / 2)`. -/
lemma norm_taylorCoeffHalf_le {g : ℂ → ℂ} {M : ℝ} (_hM : 0 ≤ M)
    (hg : DifferentiableOn ℂ g (Metric.closedBall 0 (1 / 2 : ℝ)))
    (hbd : ∀ z ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ), ‖g z‖ ≤ M) (m : ℕ) :
    ‖taylorCoeffHalf g m‖ ≤ M * (2 : ℝ) ^ m := by
  have hcoeff_norm : ‖taylorCoeffHalf g m‖ ≤ ‖cauchyPowerSeries g 0 (1 / 2 : ℝ) m‖ := by
    have happ := FormalMultilinearSeries.apply_eq_pow_smul_coeff
      (p := cauchyPowerSeries g 0 (1 / 2 : ℝ)) (n := m) (z := (1 : ℂ))
    simp only [one_pow, one_smul] at happ
    dsimp only [taylorCoeffHalf]
    rw [← happ]
    calc ‖(cauchyPowerSeries g 0 (1 / 2 : ℝ) m) (fun _ => (1 : ℂ))‖
        ≤ ‖cauchyPowerSeries g 0 (1 / 2 : ℝ) m‖ * ∏ _i : Fin m, ‖(1 : ℂ)‖ :=
          (cauchyPowerSeries g 0 (1 / 2 : ℝ) m).le_opNorm _
      _ = ‖cauchyPowerSeries g 0 (1 / 2 : ℝ) m‖ := by simp
  have hcauchy := norm_cauchyPowerSeries_le g 0 (1 / 2 : ℝ) m
  have hcircle_mem : ∀ θ : ℝ, circleMap (0 : ℂ) (1 / 2 : ℝ) θ ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) := by
    intro θ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, circleMap, zero_add, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (by norm_num), Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcont_norm : Continuous (fun θ : ℝ => ‖g (circleMap (0 : ℂ) (1 / 2 : ℝ) θ)‖) :=
    (hg.continuousOn.comp_continuous (continuous_circleMap 0 (1 / 2 : ℝ)) hcircle_mem).norm
  have hint_le : ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖g (circleMap (0 : ℂ) (1 / 2 : ℝ) θ)‖ ≤ (2 * Real.pi) * M := by
    calc ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖g (circleMap (0 : ℂ) (1 / 2 : ℝ) θ)‖
        ≤ ∫ _θ in (0 : ℝ)..(2 * Real.pi), M :=
          intervalIntegral.integral_mono_on (by positivity)
            (hcont_norm.intervalIntegrable (μ := volume) _ _)
            (intervalIntegrable_const (μ := volume)) (fun θ _ => hbd _ (hcircle_mem θ))
      _ = (2 * Real.pi) * M := by simp
  have havg_le : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖g (circleMap (0 : ℂ) (1 / 2 : ℝ) θ)‖ ≤ M := by
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖g (circleMap (0 : ℂ) (1 / 2 : ℝ) θ)‖
        ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi) * M) :=
          mul_le_mul_of_nonneg_left hint_le (by positivity)
      _ = M := by field_simp [Real.pi_pos.ne']
  have habs2 : (|(1 / 2 : ℝ)|)⁻¹ = 2 := by norm_num
  calc ‖taylorCoeffHalf g m‖
      ≤ ‖cauchyPowerSeries g 0 (1 / 2 : ℝ) m‖ := hcoeff_norm
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖g (circleMap (0 : ℂ) (1 / 2 : ℝ) θ)‖) *
          (|(1 / 2 : ℝ)|)⁻¹ ^ m := hcauchy
    _ ≤ M * (2 : ℝ) ^ m := by
        rw [habs2]; exact mul_le_mul_of_nonneg_right havg_le (by positivity)

/-- Uniform Cauchy Taylor remainder bound on `‖t‖ ≤ 1 / 4` for `g` bounded by `M` on `closedBall 0 (1 / 2)`. -/
lemma norm_taylorCoeffHalf_sub_sum_le {g : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hg : DifferentiableOn ℂ g (Metric.closedBall 0 (1 / 2 : ℝ)))
    (hbd : ∀ z ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ), ‖g z‖ ≤ M)
    (K : ℕ) {t : ℂ} (ht : ‖t‖ ≤ 1 / 4) :
    ‖g t - ∑ m ∈ Finset.range K, taylorCoeffHalf g m * t ^ m‖ ≤ 2 * M * (2 * ‖t‖) ^ K := by
  let Rnn : NNReal := ⟨1 / 2, by norm_num⟩
  have hRnn_pos : (0 : NNReal) < Rnn := by change (0 : ℝ) < 1 / 2; norm_num
  have hfps := hg.hasFPowerSeriesOnBall (R := Rnn) hRnn_pos
  have ht_eball : t ∈ Metric.eball (0 : ℂ) (Rnn : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm]
    exact ENNReal.coe_lt_coe.mpr (show ‖t‖₊ < Rnn from by
      change ‖t‖ < (1 / 2 : ℝ); linarith)
  have hsum0 := hfps.hasSum ht_eball
  simp only [zero_add] at hsum0
  have hsum : HasSum (fun m : ℕ => taylorCoeffHalf g m * t ^ m) (g t) := by
    refine hsum0.congr_fun fun m => ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
    rfl
  have htail : HasSum (fun m : ℕ => taylorCoeffHalf g (m + K) * t ^ (m + K))
      (g t - ∑ m ∈ Finset.range K, taylorCoeffHalf g m * t ^ m) :=
    (hasSum_nat_add_iff' K).mpr hsum
  have hdom_pt : ∀ m : ℕ, ‖taylorCoeffHalf g (m + K) * t ^ (m + K)‖ ≤ (M * (2 * ‖t‖) ^ K) * (2 * ‖t‖) ^ m := by
    intro m
    rw [norm_mul, norm_pow]
    have hc := norm_taylorCoeffHalf_le hM hg hbd (m + K)
    calc ‖taylorCoeffHalf g (m + K)‖ * ‖t‖ ^ (m + K)
        ≤ (M * (2 : ℝ) ^ (m + K)) * ‖t‖ ^ (m + K) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = M * ((2 * ‖t‖) ^ (m + K)) := by rw [mul_pow]; ring
      _ = (M * (2 * ‖t‖) ^ K) * (2 * ‖t‖) ^ m := by rw [pow_add]; ring
  have hr_lt : 2 * ‖t‖ < 1 := by linarith
  have hgeom_sum : Summable (fun m : ℕ => (M * (2 * ‖t‖) ^ K) * (2 * ‖t‖) ^ m) :=
    (summable_geometric_of_lt_one (by positivity) hr_lt).mul_left _
  have hnorm_sum : Summable (fun m : ℕ => ‖taylorCoeffHalf g (m + K) * t ^ (m + K)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom_pt hgeom_sum
  rw [← htail.tsum_eq]
  calc ‖∑' m : ℕ, taylorCoeffHalf g (m + K) * t ^ (m + K)‖
      ≤ ∑' m : ℕ, ‖taylorCoeffHalf g (m + K) * t ^ (m + K)‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' m : ℕ, (M * (2 * ‖t‖) ^ K) * (2 * ‖t‖) ^ m := hnorm_sum.tsum_le_tsum hdom_pt hgeom_sum
    _ = (M * (2 * ‖t‖) ^ K) * (1 - 2 * ‖t‖)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr_lt]
    _ ≤ (M * (2 * ‖t‖) ^ K) * 2 := by
        have hinv : (1 - 2 * ‖t‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * M * (2 * ‖t‖) ^ K := by ring

/-- Unified holomorphic shift basis `(1 + ζ) * (1 + ζ)⁻¹ ^ n * (log (1 + ζ)) ^ j` on `closedBall 0 (1 / 2)`. -/
@[expose] def shiftBasis (n j : ℕ) (ζ : ℂ) : ℂ :=
  (1 + ζ) * (1 + ζ)⁻¹ ^ n * Complex.log (1 + ζ) ^ j

/-- Taylor coefficients of `shiftBasis n j` at `0`. -/
@[expose] def shiftC (n j m : ℕ) : ℂ :=
  taylorCoeffHalf (shiftBasis n j) m

lemma differentiableOn_shiftBasis (n j : ℕ) :
    DifferentiableOn ℂ (shiftBasis n j) (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
  have hslit : ∀ ζ ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ), 1 + ζ ∈ Complex.slitPlane := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hζ
    have hre := (abs_le.mp ((Complex.abs_re_le_norm ζ).trans hζ)).1
    exact Or.inl (by simp; linarith)
  have h1 : DifferentiableOn ℂ (fun ζ : ℂ => 1 + ζ) (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
    (differentiable_const (1 : ℂ)).add differentiable_id |>.differentiableOn
  have h2 : DifferentiableOn ℂ (fun ζ : ℂ => (1 + ζ)⁻¹ ^ n) (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
    (h1.inv fun ζ hζ => Complex.slitPlane_ne_zero (hslit ζ hζ)).pow n
  have h3 : DifferentiableOn ℂ (fun ζ : ℂ => Complex.log (1 + ζ) ^ j) (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
    refine DifferentiableOn.pow ?_ j
    intro ζ hζ
    have hd : HasDerivAt (fun w : ℂ => Complex.log (1 + w)) ((1 + ζ)⁻¹) ζ := by
      have hlin : HasDerivAt (fun w : ℂ => 1 + w) 1 ζ := by simpa using (hasDerivAt_id ζ).const_add (1 : ℂ)
      exact ((Complex.hasDerivAt_log (hslit ζ hζ)).comp ζ hlin).congr_deriv (mul_one _)
    exact hd.differentiableAt.differentiableWithinAt
  exact (h1.mul h2).mul h3

lemma norm_shiftBasis_le (n j : ℕ) {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) :
    ‖shiftBasis n j ζ‖ ≤ (2 : ℝ) ^ (n + 1) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hζ
  dsimp only [shiftBasis]
  rw [norm_mul, norm_mul, norm_pow, norm_inv, norm_pow]
  have h1_le : ‖(1 : ℂ) + ζ‖ ≤ 2 := by
    calc ‖(1 : ℂ) + ζ‖ ≤ ‖(1 : ℂ)‖ + ‖ζ‖ := norm_add_le _ _
      _ ≤ 1 + 1 / 2 := by rw [norm_one]; linarith
      _ ≤ 2 := by norm_num
  have h1_ge : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) + ζ‖ := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm ζ).trans hζ)).1
    have := Complex.re_le_norm ((1 : ℂ) + ζ)
    simp only [Complex.add_re, Complex.one_re] at this; linarith
  have hinv_le : ‖(1 : ℂ) + ζ‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hlog_le : ‖Complex.log (1 + ζ)‖ ≤ 1 := by
    calc ‖Complex.log (1 + ζ)‖ ≤ 2 * ‖ζ‖ := norm_clog_one_add_le hζ
      _ ≤ 1 := by linarith
  have hpow1 : ‖(1 : ℂ) + ζ‖⁻¹ ^ n ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hinv_le n
  have hpow2 : ‖Complex.log (1 + ζ)‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hlog_le
  calc ‖(1 : ℂ) + ζ‖ * ‖(1 : ℂ) + ζ‖⁻¹ ^ n * ‖Complex.log (1 + ζ)‖ ^ j
      ≤ (2 * (2 : ℝ) ^ n) * 1 :=
        mul_le_mul (mul_le_mul h1_le hpow1 (by positivity) (by norm_num)) hpow2 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

lemma norm_shiftC_le (n j m : ℕ) : ‖shiftC n j m‖ ≤ (2 : ℝ) ^ (n + 1 + m) := by
  calc ‖shiftC n j m‖ ≤ (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ m :=
        norm_taylorCoeffHalf_le (by positivity) (differentiableOn_shiftBasis n j)
          (fun _ hζ => norm_shiftBasis_le n j hζ) m
    _ = (2 : ℝ) ^ (n + 1 + m) := (pow_add _ _ _).symm

lemma norm_shiftBasis_sub_sum_le (n j K : ℕ) {t : ℂ} (ht : ‖t‖ ≤ 1 / 4) :
    ‖shiftBasis n j t - ∑ m ∈ Finset.range K, shiftC n j m * t ^ m‖ ≤
      (2 : ℝ) ^ (n + 2) * (2 * ‖t‖) ^ K := by
  calc ‖shiftBasis n j t - ∑ m ∈ Finset.range K, shiftC n j m * t ^ m‖
      ≤ 2 * (2 : ℝ) ^ (n + 1) * (2 * ‖t‖) ^ K :=
        norm_taylorCoeffHalf_sub_sum_le (by positivity) (differentiableOn_shiftBasis n j)
          (fun _ hζ => norm_shiftBasis_le n j hζ) K ht
    _ = (2 : ℝ) ^ (n + 2) * (2 * ‖t‖) ^ K := by rw [pow_succ (2 : ℝ) (n + 1)]; ring

/-- Sharp uniform envelope for the Gamma-log kernel: `exp (2x - exp x) ≤ exp 4 * exp (-2 |x|)` for all `x : ℝ`. -/
lemma exp_two_sub_exp_le_exp4_mul (x : ℝ) :
    Real.exp (2 * x - Real.exp x) ≤ Real.exp 4 * Real.exp (-2 * |x|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    have hexp : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
      have h := Real.sum_le_exp_of_nonneg hx 3
      simp [Finset.sum_range_succ, Nat.factorial] at h; linarith
    nlinarith [sq_nonneg (x - 3)]
  · push Not at hx
    rw [abs_of_neg hx]
    linarith [Real.exp_pos x]

/-- Two-sided symmetric Gamma integral `∫_ℝ |x|^m * exp (-|x|) dx = 2 * m!`. -/
lemma integral_abs_pow_mul_exp_neg_abs (m : ℕ) :
    Integrable (fun x : ℝ => |x| ^ m * Real.exp (-|x|)) volume ∧
    (∫ x : ℝ, |x| ^ m * Real.exp (-|x|)) = 2 * (m.factorial : ℝ) := by
  have hint_pos : IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-x)) (Set.Ioi 0) := by
    have h1 := integrableOn_exp_mul_Ioi (show (-(1 / 2 : ℝ)) < 0 by norm_num) 0
    have hdom : IntegrableOn (fun r : ℝ => ((m.factorial : ℝ) / (1 / 2 : ℝ) ^ m) * Real.exp (-(1 / 2 : ℝ) * r))
        (Set.Ioi 0) := h1.const_mul _
    refine hdom.mono' ((continuous_pow m |>.mul (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    rw [Real.norm_of_nonneg (by positivity)]
    have hpow : ((1 / 2 : ℝ) * r) ^ m / (m.factorial : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * r) :=
      Real.pow_div_factorial_le_exp ((1 / 2 : ℝ) * r) (by positivity) m
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hmul : r ^ m ≤ ((m.factorial : ℝ) / (1 / 2 : ℝ) ^ m) * Real.exp ((1 / 2 : ℝ) * r) := by
      rw [mul_pow] at hpow
      rw [div_le_iff₀ hfac] at hpow
      have h2 : (1 / 2 : ℝ) ^ m * r ^ m ≤ Real.exp ((1 / 2 : ℝ) * r) * (m.factorial : ℝ) := hpow
      calc r ^ m = ((1 / 2 : ℝ) ^ m * r ^ m) / (1 / 2 : ℝ) ^ m := by field_simp
        _ ≤ (Real.exp ((1 / 2 : ℝ) * r) * (m.factorial : ℝ)) / (1 / 2 : ℝ) ^ m :=
            div_le_div_of_nonneg_right h2 (by positivity)
        _ = ((m.factorial : ℝ) / (1 / 2 : ℝ) ^ m) * Real.exp ((1 / 2 : ℝ) * r) := by ring
    calc r ^ m * Real.exp (-r)
        ≤ (((m.factorial : ℝ) / (1 / 2 : ℝ) ^ m) * Real.exp ((1 / 2 : ℝ) * r)) * Real.exp (-r) :=
          mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / (1 / 2 : ℝ) ^ m) * (Real.exp ((1 / 2 : ℝ) * r) * Real.exp (-r)) := by ring
      _ = ((m.factorial : ℝ) / (1 / 2 : ℝ) ^ m) * Real.exp (-(1 / 2 : ℝ) * r) := by
          rw [← Real.exp_add]; congr 2; ring
  have hint_ioi : IntegrableOn (fun x : ℝ => |x| ^ m * Real.exp (-|x|)) (Set.Ioi 0) :=
    hint_pos.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have hint_iio : IntegrableOn (fun x : ℝ => |x| ^ m * Real.exp (-|x|)) (Set.Iio 0) := by
    have hind_ioi : Integrable (Set.indicator (Set.Ioi (0 : ℝ)) (fun x : ℝ => |x| ^ m * Real.exp (-|x|))) volume :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr hint_ioi
    have hcomp : Integrable (fun x : ℝ =>
        Set.indicator (Set.Ioi (0 : ℝ)) (fun t : ℝ => |t| ^ m * Real.exp (-|t|)) (-x)) volume :=
      (MeasureTheory.Measure.measurePreserving_neg volume).integrable_comp_of_integrable hind_ioi
    have heq : (fun x : ℝ => Set.indicator (Set.Ioi (0 : ℝ)) (fun t : ℝ => |t| ^ m * Real.exp (-|t|)) (-x)) =
        Set.indicator (Set.Iio (0 : ℝ)) (fun x : ℝ => |x| ^ m * Real.exp (-|x|)) := by
      ext x; simp only [Set.indicator, Set.mem_Ioi, Set.mem_Iio, abs_neg]
      split_ifs with h1 h2
      · rfl
      · exact absurd (by linarith) h2
      · exact absurd (by linarith) h1
      · rfl
    rw [heq] at hcomp
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Iio).mp hcomp
  have hint_iic : IntegrableOn (fun x : ℝ => |x| ^ m * Real.exp (-|x|)) (Set.Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hint_iio
  have hint_all : Integrable (fun x : ℝ => |x| ^ m * Real.exp (-|x|)) volume := by
    rw [← integrableOn_univ, show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 by
      ext x; simp]
    exact hint_iic.union hint_ioi
  refine ⟨hint_all, ?_⟩
  have hsplit : (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 := by ext x; simp
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi 0) := Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
  rw [← MeasureTheory.setIntegral_univ, hsplit,
    MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_iic hint_ioi,
    MeasureTheory.integral_Iic_eq_integral_Iio]
  have hleft : (∫ x in Set.Iio (0 : ℝ), |x| ^ m * Real.exp (-|x|)) =
      ∫ x in Set.Ioi (0 : ℝ), |x| ^ m * Real.exp (-|x|) := by
    rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_neg_eq_self (Set.indicator (Set.Ioi (0 : ℝ)) (fun t : ℝ => |t| ^ m * Real.exp (-|t|)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Set.indicator, Set.mem_Iio, Set.mem_Ioi, abs_neg]
    split_ifs with h1 h2
    · rfl
    · exact absurd (by linarith) h2
    · exact absurd (by linarith) h1
    · rfl
  have hright : (∫ x in Set.Ioi (0 : ℝ), |x| ^ m * Real.exp (-|x|)) = (m.factorial : ℝ) := by
    have h1 := integral_Ioi_pow_mul_exp_neg zero_lt_one m
    simp only [neg_mul, one_mul, one_pow, div_one] at h1
    rw [← h1]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
  rw [hleft, hright]; ring

/-- Full Gamma-log moments `γ_m := ∫_ℝ exp(2x - exp x) * x^m dx`. -/
@[expose] def gammaMom (m : ℕ) : ℝ :=
  ∫ x : ℝ, Real.exp (2 * x - Real.exp x) * x ^ m

/-- Integrability, full moment bound, truncated absolute moment bound, and tail bound for `gammaMom`. -/
lemma gammaMom_bounds (m : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Integrable (fun x : ℝ => Real.exp (2 * x - Real.exp x) * x ^ m) volume ∧
    |gammaMom m| ≤ 2 * Real.exp 4 * (m.factorial : ℝ) ∧
    (∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * |x| ^ m) ≤ 2 * Real.exp 4 * (m.factorial : ℝ) ∧
    |gammaMom m - ∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m| ≤
      2 * Real.exp 4 * Real.exp (-L) * (m.factorial : ℝ) := by
  obtain ⟨hint_abs, heq_abs⟩ := integral_abs_pow_mul_exp_neg_abs m
  have hdom_all : ∀ x : ℝ, ‖Real.exp (2 * x - Real.exp x) * x ^ m‖ ≤
      Real.exp 4 * (|x| ^ m * Real.exp (-|x|)) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    have h1 := exp_two_sub_exp_le_exp4_mul x
    have h2 : Real.exp (-2 * |x|) ≤ Real.exp (-|x|) := Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
    calc Real.exp (2 * x - Real.exp x) * |x| ^ m
        ≤ (Real.exp 4 * Real.exp (-2 * |x|)) * |x| ^ m := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Real.exp 4 * Real.exp (-|x|)) * |x| ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (by positivity)
      _ = Real.exp 4 * (|x| ^ m * Real.exp (-|x|)) := by ring
  have hcont : Continuous (fun x : ℝ => Real.exp (2 * x - Real.exp x) * x ^ m) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub Real.continuous_exp)).mul (continuous_pow m)
  have hint_m : Integrable (fun x : ℝ => Real.exp (2 * x - Real.exp x) * x ^ m) volume :=
    (hint_abs.const_mul (Real.exp 4)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hdom_all)
  have hmom_le : |gammaMom m| ≤ 2 * Real.exp 4 * (m.factorial : ℝ) := by
    dsimp only [gammaMom]
    calc |∫ x : ℝ, Real.exp (2 * x - Real.exp x) * x ^ m|
        = ‖∫ x : ℝ, Real.exp (2 * x - Real.exp x) * x ^ m‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x : ℝ, ‖Real.exp (2 * x - Real.exp x) * x ^ m‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, Real.exp 4 * (|x| ^ m * Real.exp (-|x|)) :=
          integral_mono hint_m.norm (hint_abs.const_mul (Real.exp 4)) hdom_all
      _ = Real.exp 4 * (2 * (m.factorial : ℝ)) := by rw [integral_const_mul, heq_abs]
      _ = 2 * Real.exp 4 * (m.factorial : ℝ) := by ring
  have htrunc_abs_le : (∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * |x| ^ m) ≤
      2 * Real.exp 4 * (m.factorial : ℝ) := by
    have hcont_abs : Continuous (fun x : ℝ => Real.exp (2 * x - Real.exp x) * |x| ^ m) :=
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub Real.continuous_exp)).mul
        (continuous_abs.pow m)
    have hint_t : IntegrableOn (fun x : ℝ => Real.exp (2 * x - Real.exp x) * |x| ^ m) (Set.Icc (-L) L) :=
      hcont_abs.continuousOn.integrableOn_compact isCompact_Icc
    calc ∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * |x| ^ m
        ≤ ∫ x in Set.Icc (-L) L, Real.exp 4 * (|x| ^ m * Real.exp (-|x|)) :=
          setIntegral_mono_on hint_t (hint_abs.const_mul (Real.exp 4)).integrableOn measurableSet_Icc fun x _ => by
            have := hdom_all x
            rwa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow] at this
      _ ≤ ∫ x : ℝ, Real.exp 4 * (|x| ^ m * Real.exp (-|x|)) :=
          setIntegral_le_integral (hint_abs.const_mul (Real.exp 4))
            (Filter.Eventually.of_forall fun _ => by positivity)
      _ = 2 * Real.exp 4 * (m.factorial : ℝ) := by rw [integral_const_mul, heq_abs]; ring
  have htail_le : |gammaMom m - ∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m| ≤
      2 * Real.exp 4 * Real.exp (-L) * (m.factorial : ℝ) := by
    let f : ℝ → ℝ := fun x => Real.exp (2 * x - Real.exp x) * x ^ m
    have hcompl : (Set.Icc (-L) L)ᶜ ∪ Set.Icc (-L) L = Set.univ := Set.compl_union_self _
    have hdisj : Disjoint (Set.Icc (-L) L)ᶜ (Set.Icc (-L) L) := disjoint_compl_left
    have hdiff : gammaMom m - ∫ x in Set.Icc (-L) L, f x = ∫ x in (Set.Icc (-L) L)ᶜ, f x := by
      dsimp only [gammaMom, f]
      have hu : (∫ x in (Set.Icc (-L) L)ᶜ, f x) + (∫ x in Set.Icc (-L) L, f x) = ∫ x : ℝ, f x := by
        rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Icc hint_m.integrableOn hint_m.integrableOn,
          hcompl, MeasureTheory.setIntegral_univ]
      linarith
    rw [hdiff]
    have hdom_tail : ∀ x ∈ (Set.Icc (-L) L)ᶜ, ‖f x‖ ≤ (Real.exp 4 * Real.exp (-L)) * (|x| ^ m * Real.exp (-|x|)) := by
      intro x hx
      have hge : L ≤ |x| := by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      dsimp only [f]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
      have h1 := exp_two_sub_exp_le_exp4_mul x
      have h2 : Real.exp (-2 * |x|) ≤ Real.exp (-L) * Real.exp (-|x|) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      calc Real.exp (2 * x - Real.exp x) * |x| ^ m
          ≤ (Real.exp 4 * Real.exp (-2 * |x|)) * |x| ^ m := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (Real.exp 4 * (Real.exp (-L) * Real.exp (-|x|))) * |x| ^ m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (by positivity)
        _ = (Real.exp 4 * Real.exp (-L)) * (|x| ^ m * Real.exp (-|x|)) := by ring
    calc |∫ x in (Set.Icc (-L) L)ᶜ, f x|
        = ‖∫ x in (Set.Icc (-L) L)ᶜ, f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in (Set.Icc (-L) L)ᶜ, ‖f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in (Set.Icc (-L) L)ᶜ, (Real.exp 4 * Real.exp (-L)) * (|x| ^ m * Real.exp (-|x|)) :=
          setIntegral_mono_on hint_m.integrableOn.norm (hint_abs.const_mul _).integrableOn
            measurableSet_Icc.compl hdom_tail
      _ ≤ ∫ x : ℝ, (Real.exp 4 * Real.exp (-L)) * (|x| ^ m * Real.exp (-|x|)) :=
          setIntegral_le_integral (hint_abs.const_mul _) (Filter.Eventually.of_forall fun _ => by positivity)
      _ = 2 * Real.exp 4 * Real.exp (-L) * (m.factorial : ℝ) := by rw [integral_const_mul, heq_abs]; ring
  exact ⟨hint_m, hmom_le, htrunc_abs_le, htail_le⟩

/-- Formal Gevrey-1 log-power coefficients for `I_entire u / u` induced by shifting `a_F` under
the Gamma-log kernel `exp (2x - exp x) dx`. -/
@[expose] def convCoeff (a_F : LogCoeff) (d l : ℕ) : ℂ :=
  if d < l then 0 else
  ∑ n ∈ Finset.range (d + 1),
    ∑ k ∈ Finset.range (n + 1),
      if l ≤ k then
        a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) * ((gammaMom (d - n) : ℝ) : ℂ)
      else 0

/-- Algebraic reindexing of `evalTrunc (convCoeff a_F) N u` into the `(n, m, k, l)` quadruple sum. -/
lemma evalTrunc_convCoeff_eq (a_F : LogCoeff) (N : ℕ) (u : ℂ) :
    evalTrunc (convCoeff a_F) N u =
      ∑ n ∈ Finset.range N,
        ∑ m ∈ Finset.range (N - n),
          ∑ k ∈ Finset.range (n + 1),
            ∑ l ∈ Finset.range (k + 1),
              a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                ((gammaMom m : ℝ) : ℂ) * (Complex.log u ^ l / u ^ (n + m)) := by
  -- First rewrite each degree-`d` term `evalTerm (convCoeff a_F) d u` as a sum over `n ≤ d`.
  have hterm : ∀ d : ℕ, evalTerm (convCoeff a_F) d u =
      ∑ n ∈ Finset.range (d + 1),
        ∑ k ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (k + 1),
            a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
              ((gammaMom (d - n) : ℝ) : ℂ) * (Complex.log u ^ l / u ^ d) := by
    intro d
    dsimp only [evalTerm]
    rw [Finset.sum_div]
    have h1 : ∑ l ∈ Finset.range (d + 1), convCoeff a_F d l * Complex.log u ^ l / u ^ d =
        ∑ l ∈ Finset.range (d + 1),
          ∑ n ∈ Finset.range (d + 1),
            ∑ k ∈ Finset.range (n + 1),
              (if l ≤ k then
                a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
                  ((gammaMom (d - n) : ℝ) : ℂ) * (Complex.log u ^ l / u ^ d)
              else 0) := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hdl : ¬ d < l := by simp only [Finset.mem_range] at hl; omega
      dsimp only [convCoeff]; simp only [hdl, ↓reduceIte]
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd : k ≤ d := by simp only [Finset.mem_range] at hn hk; omega
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range (d + 1)).filter (fun l => l ≤ k) = Finset.range (k + 1) := by
      ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt]
  dsimp only [evalTrunc]
  simp_rw [hterm]
  -- Reindex `∑ d < N, ∑ n ≤ d, F n (d - n) = ∑ n < N, ∑ m < N - n, F n m`!
  let F : ℕ → ℕ → ℂ := fun n m =>
    ∑ k ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (k + 1),
        a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
          ((gammaMom m : ℝ) : ℂ) * (Complex.log u ^ l / u ^ (n + m))
  have hL : (∑ d ∈ Finset.range N, ∑ n ∈ Finset.range (d + 1),
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
        a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
          ((gammaMom (d - n) : ℝ) : ℂ) * (Complex.log u ^ l / u ^ d)) =
      ∑ p ∈ (Finset.range N).sigma (fun d => Finset.range (d + 1)), F p.2 (p.1 - p.2) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    dsimp only [F]
    have hadd : p.2 + (p.1 - p.2) = p.1 := Nat.add_sub_of_le (by omega)
    rw [hadd]
  have hR : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (N - n), F n m) =
      ∑ q ∈ (Finset.range N).sigma (fun n => Finset.range (N - n)), F q.1 q.2 :=
    Finset.sum_sigma' _ _ _
  rw [hL, hR]
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 - p.2⟩) (fun q => ⟨q.1 + q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp; simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢; omega
  · intro q hq; simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢; omega
  · intro p hp; simp only [Finset.mem_sigma, Finset.mem_range] at hp
    exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
  · intro q hq; simp only [Finset.mem_sigma, Finset.mem_range] at hq
    exact Sigma.ext rfl (heq_of_eq (by dsimp; omega))
  · intro p _; rfl

/-- Complex logarithm splitting `log (u + x) = log u + log (1 + x / u)` on `Σ₀` for `|x| ≤ ‖u‖ / 24`. -/
lemma clog_add_ofReal_eq {u : ℂ} (hu : u ∈ rotatedClosedSector theta1' theta2' R_conv)
    {x : ℝ} (hx : |x| ≤ ‖u‖ / 24) :
    Complex.log (u + (x : ℂ)) = Complex.log u + Complex.log (1 + (x : ℂ) / u) := by
  have hu_ge : R_conv ≤ ‖u‖ := hu.1
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le R_conv_pos hu_ge
  have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
  let t : ℂ := (x : ℂ) / u
  have ht_norm : ‖t‖ ≤ 1 / 24 := by
    dsimp only [t]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hu_pos]; linarith
  have h1t_re : (23 / 24 : ℝ) ≤ (1 + t).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm t).trans ht_norm)).1
    simp only [Complex.add_re, Complex.one_re]; linarith
  have h1t_norm : (23 / 24 : ℝ) ≤ ‖1 + t‖ := h1t_re.trans (Complex.re_le_norm _)
  have h1t0 : 1 + t ≠ 0 := norm_pos_iff.mp (by linarith)
  have harg_1t : |Complex.arg (1 + t)| ≤ Real.pi / 24 := by
    have hlt_pi2 : |Complex.arg (1 + t)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
    have hsin_ge : 2 / Real.pi * |Complex.arg (1 + t)| ≤ Real.sin |Complex.arg (1 + t)| :=
      Real.mul_le_sin (abs_nonneg _) hlt_pi2.le
    have hsin_eq : Real.sin |Complex.arg (1 + t)| = |(1 + t).im| / ‖1 + t‖ := by
      have hpi2 := abs_lt.mp hlt_pi2
      have h1 : Real.sin |Complex.arg (1 + t)| = |Real.sin (Complex.arg (1 + t))| := by
        rcases le_or_gt 0 (Complex.arg (1 + t)) with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]))]
        · rw [abs_of_neg h, Real.sin_neg,
            abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith [Real.pi_pos]))]
      rw [h1, Complex.sin_arg, abs_div, abs_of_pos (by linarith : 0 < ‖1 + t‖)]
    have him_le : |(1 + t).im| ≤ 1 / 24 := by
      have : (1 + t).im = t.im := by simp
      rw [this]; exact (Complex.abs_im_le_norm t).trans ht_norm
    have hsin_le : Real.sin |Complex.arg (1 + t)| ≤ 1 / 23 := by
      rw [hsin_eq]
      calc |(1 + t).im| / ‖1 + t‖ ≤ (1 / 24 : ℝ) / (23 / 24) :=
            div_le_div₀ (by norm_num) him_le (by norm_num) h1t_norm
        _ = 1 / 23 := by norm_num
    have hmul : 2 / Real.pi * |Complex.arg (1 + t)| ≤ 1 / 23 := hsin_ge.trans hsin_le
    have hpi := Real.pi_pos
    have hle : |Complex.arg (1 + t)| ≤ Real.pi / 46 := by
      have := mul_le_mul_of_nonneg_left hmul (show 0 ≤ Real.pi / 2 by positivity)
      have hL : Real.pi / 2 * (2 / Real.pi * |Complex.arg (1 + t)|) = |Complex.arg (1 + t)| := by
        field_simp [hpi.ne']
      rw [hL] at this; linarith
    linarith
  obtain ⟨harg_lo, harg_hi⟩ := rotatedClosedSector_enlarged_arg_mem hu
  have h1t_abs := abs_le.mp harg_1t
  have hprod : u + (x : ℂ) = u * (1 + t) := by dsimp only [t]; field_simp [hu0]
  rw [hprod]
  exact Complex.log_mul hu0 h1t0
    ⟨by dsimp only [theta1'] at harg_lo; linarith [Real.pi_pos],
     by dsimp only [theta2'] at harg_hi; linarith [Real.pi_pos]⟩

/-- **MAIN SECTION 5 EXPORT (`I_entire_div_hasGev1Exp`)**:
`u ↦ I_entire u / u` admits a uniform Gevrey-1 log-power asymptotic expansion on the ENTIRE
enlarged closed sector `rotatedClosedSector theta1' theta2' R_conv` (opening `7π/6 > π`)! -/
theorem I_entire_div_hasGev1Exp :
    ∃ a_I : LogCoeff, HasGev1Exp (rotatedClosedSector theta1' theta2' R_conv)
      (fun u => I_entire u / u) a_I := by
  obtain ⟨a_F, h0_F, C_F, hCF, A_F, hAF, hcoeff_F, hrem_F⟩ := F_plus_div_hasGev1Exp
  obtain ⟨C_conv, hCconv, c_conv, hcconv, htrunc_conv⟩ := I_entire_truncated_conv_bound
  refine ⟨convCoeff a_F, ?_, ?_⟩
  · intro d l hdl; dsimp only [convCoeff]; simp only [hdl, ↓reduceIte]
  let C_I : ℝ := C_conv + 24 * Real.exp (Real.pi + 5) * C_F
  let A_I : ℝ := max (192 * A_F) (max 1 (1 / c_conv))
  have hCI_pos : 0 < C_I := by dsimp [C_I]; positivity
  have hAI_ge1 : 1 ≤ A_I := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAI_ge_192AF : 192 * A_F ≤ A_I := le_max_left _ _
  have hAI_ge_inv_c : 1 / c_conv ≤ A_I := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C_I, hCI_pos, A_I, hAI_ge1, ?_, ?_⟩
  · -- Part 1: Gevrey-1 coefficient bound for `convCoeff a_F`!
    intro d l hld
    dsimp only [convCoeff]
    simp only [not_lt.mpr hld, ↓reduceIte]
    have hinner : ∀ n ∈ Finset.range (d + 1), ∀ k ∈ Finset.range (n + 1),
        ‖if l ≤ k then a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
          ((gammaMom (d - n) : ℝ) : ℂ) else 0‖ ≤
          (4 * Real.exp 4 * C_F) * (2 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by
      intro n hn k hk
      simp only [Finset.mem_range] at hn hk
      split_ifs with hlk
      · rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
        have h1 := hcoeff_F n k (by omega)
        have h2 := norm_shiftC_le n (k - l) (d - n)
        have h3 := (gammaMom_bounds (d - n) le_rfl).2.1
        have hch_eq : ((k.choose l : ℕ) : ℝ) =
            (k.factorial : ℝ) / ((l.factorial : ℝ) * ((k - l).factorial : ℝ)) := by
          have h := Nat.choose_mul_factorial_mul_factorial hlk
          have hcast : ((k.choose l : ℕ) : ℝ) * (l.factorial : ℝ) * ((k - l).factorial : ℝ) = (k.factorial : ℝ) := by
            exact_mod_cast h
          have hlpos : (0 : ℝ) < (l.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos l)
          have hklpos : (0 : ℝ) < ((k - l).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos (k - l))
          rw [eq_div_iff (by positivity)]; linarith
        have h2pow : (2 : ℝ) ^ (n + 1 + (d - n)) = 2 * (2 : ℝ) ^ d := by
          have : n + 1 + (d - n) = d + 1 := by omega
          rw [this, pow_succ]; ring
        have hAF_le : A_F ^ n ≤ A_F ^ d := pow_le_pow_right₀ hAF (by omega)
        have hfac_prod : (n.factorial : ℝ) * ((d - n).factorial : ℝ) ≤ (d.factorial : ℝ) := by
          have := factorial_mul_factorial_le n (d - n)
          rwa [Nat.add_sub_of_le (by omega)] at this
        have hkl_ge1 : (1 : ℝ) ≤ ((k - l).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - l)
        have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
        have hl_pos : (0 : ℝ) < (l.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos l)
        calc ‖a_F n k‖ * (k.choose l : ℝ) * ‖shiftC n (k - l) (d - n)‖ * |gammaMom (d - n)|
            ≤ (C_F * A_F ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) * (k.choose l : ℝ) *
                ((2 : ℝ) ^ (n + 1 + (d - n))) * (2 * Real.exp 4 * ((d - n).factorial : ℝ)) := by
              gcongr
          _ = 4 * Real.exp 4 * C_F * A_F ^ n * (2 : ℝ) ^ d *
                ((n.factorial : ℝ) * ((d - n).factorial : ℝ) / ((l.factorial : ℝ) * ((k - l).factorial : ℝ))) := by
              rw [hch_eq, h2pow]; field_simp [hk_pos.ne', hl_pos.ne']; ring
          _ ≤ 4 * Real.exp 4 * C_F * A_F ^ d * (2 : ℝ) ^ d *
                ((d.factorial : ℝ) / ((l.factorial : ℝ) * 1)) := by
              have hdiv : (n.factorial : ℝ) * ((d - n).factorial : ℝ) /
                    ((l.factorial : ℝ) * ((k - l).factorial : ℝ)) ≤
                  (d.factorial : ℝ) / ((l.factorial : ℝ) * 1) :=
                div_le_div₀ (by positivity) hfac_prod (by positivity)
                  (mul_le_mul_of_nonneg_left hkl_ge1 hl_pos.le)
              gcongr
          _ = (4 * Real.exp 4 * C_F) * (2 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by
              rw [mul_one, mul_pow]; ring
      · rw [norm_zero]; positivity
    have hsum_le : ‖∑ n ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (n + 1),
          if l ≤ k then a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
            ((gammaMom (d - n) : ℝ) : ℂ) else 0‖ ≤
        ((d : ℝ) + 1) ^ 2 * ((4 * Real.exp 4 * C_F) * (2 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) := by
      calc _ ≤ ∑ n ∈ Finset.range (d + 1), ‖∑ k ∈ Finset.range (n + 1),
              if l ≤ k then a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
                ((gammaMom (d - n) : ℝ) : ℂ) else 0‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (n + 1),
              ‖if l ≤ k then a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) (d - n) *
                ((gammaMom (d - n) : ℝ) : ℂ) else 0‖ :=
            Finset.sum_le_sum fun n _ => norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range (d + 1), ∑ _k ∈ Finset.range (n + 1),
              ((4 * Real.exp 4 * C_F) * (2 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) :=
            Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hinner n hn k hk
        _ ≤ ∑ _n ∈ Finset.range (d + 1), ((d : ℝ) + 1) *
              ((4 * Real.exp 4 * C_F) * (2 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hnd : ((n + 1 : ℕ) : ℝ) ≤ (d : ℝ) + 1 := by
              simp only [Finset.mem_range] at hn; exact_mod_cast (show n + 1 ≤ d + 1 by omega)
            exact mul_le_mul_of_nonneg_right hnd (by positivity)
        _ = ((d : ℝ) + 1) ^ 2 * ((4 * Real.exp 4 * C_F) * (2 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have h4exp : 4 * Real.exp 4 * C_F ≤ C_I := by
      dsimp only [C_I]
      have : Real.exp 4 ≤ Real.exp (Real.pi + 5) := Real.exp_le_exp.mpr (by linarith [Real.pi_pos])
      nlinarith [Real.exp_pos (4 : ℝ), Real.exp_pos (Real.pi + 5)]
    have h8AF : 8 * A_F ≤ A_I := by linarith
    calc _ ≤ (4 : ℝ) ^ d * ((4 * Real.exp 4 * C_F) * (2 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ)) :=
          hsum_le.trans (mul_le_mul_of_nonneg_right (nat_add_one_sq_le_four_pow d) (by positivity))
      _ = (4 * Real.exp 4 * C_F) * (8 * A_F) ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by
          have : (4 : ℝ) ^ d * (2 * A_F) ^ d = (8 * A_F) ^ d := by rw [← mul_pow]; congr 1; ring
          calc _ = (4 * Real.exp 4 * C_F) * ((4 : ℝ) ^ d * (2 * A_F) ^ d) * (d.factorial : ℝ) / (l.factorial : ℝ) := by ring
            _ = _ := by rw [this]
      _ ≤ C_I * A_I ^ d * (d.factorial : ℝ) / (l.factorial : ℝ) := by gcongr
  · -- Part 2: Uniform Gevrey-1 remainder bound across ALL `N : ℕ` and ALL `u ∈ Σ₀`!
    intro N u hu
    have hu_ge : R_conv ≤ ‖u‖ := hu.1
    have hu_1e6 : (1000000 : ℝ) ≤ ‖u‖ := by
      have h := R_conv_ge_1e6.trans hu_ge; norm_num at h; exact h
    have hu_ge1 : (1 : ℝ) ≤ ‖u‖ := by linarith
    have hu_pos : 0 < ‖u‖ := by linarith
    have hu0 : u ≠ 0 := norm_pos_iff.mp hu_pos
    let L : ℝ := ‖u‖ / 24
    have hL_pos : 0 < L := by dsimp [L]; linarith
    let K_I : ℝ → ℂ := fun x => ((Real.exp (2 * x - Real.exp x) : ℝ) : ℂ)
    -- Pointwise properties for `x ∈ Set.Icc (-L) L`
    have hx_abs : ∀ x ∈ Set.Icc (-L) L, |x| ≤ L := fun x hx => abs_le.mpr hx
    have hx_Vsec : ∀ x ∈ Set.Icc (-L) L, u + (x : ℂ) ∈ V_sec :=
      fun x hx => shift_mem_V_sec hu (hx_abs x hx)
    have hx_norm_lo : ∀ x ∈ Set.Icc (-L) L, (23 / 24 : ℝ) * ‖u‖ ≤ ‖u + (x : ℂ)‖ := by
      intro x hx
      have h1 := hx_abs x hx
      have h2 := norm_sub_norm_le u (-(x : ℂ))
      rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h2
      dsimp only [L] at h1; linarith
    have hx_norm_hi : ∀ x ∈ Set.Icc (-L) L, ‖u + (x : ℂ)‖ ≤ 2 * ‖u‖ := by
      intro x hx
      have h1 := hx_abs x hx
      have h2 : ‖u + (x : ℂ)‖ ≤ ‖u‖ + |x| := by simpa [Complex.norm_real] using norm_add_le u (x : ℂ)
      dsimp only [L] at h1; linarith
    have hx_ne : ∀ x ∈ Set.Icc (-L) L, u + (x : ℂ) ≠ 0 := fun x hx =>
      norm_pos_iff.mp (by linarith [hx_norm_lo x hx])
    have ht_le : ∀ x ∈ Set.Icc (-L) L, ‖(x : ℂ) / u‖ ≤ 1 / 4 := by
      intro x hx
      have h1 := hx_abs x hx
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hu_pos]
      dsimp only [L] at h1; linarith
    -- Key exponential-log bound: `(1 + ‖log u‖)^k / k! ≤ exp (π + 1) * ‖u‖` for ALL `k : ℕ`!
    have hlog_pow_le : ∀ k : ℕ, (1 + ‖Complex.log u‖) ^ k / (k.factorial : ℝ) ≤
        Real.exp (Real.pi + 1) * ‖u‖ := by
      intro k
      calc (1 + ‖Complex.log u‖) ^ k / (k.factorial : ℝ)
          ≤ Real.exp (1 + ‖Complex.log u‖) := Real.pow_div_factorial_le_exp _ (by positivity) k
        _ = Real.exp 1 * Real.exp ‖Complex.log u‖ := Real.exp_add 1 _
        _ ≤ Real.exp 1 * (Real.exp Real.pi * ‖u‖) :=
            mul_le_mul_of_nonneg_left (exp_norm_log_le hu_ge1) (Real.exp_pos 1).le
        _ = Real.exp (Real.pi + 1) * ‖u‖ := by rw [Real.exp_add]; ring
    -- Define the truncated Taylor-expanded polynomial in `x`:
    let P_trunc : ℝ → ℂ := fun x =>
      ∑ n ∈ Finset.range N,
        ∑ m ∈ Finset.range (N - n),
          ∑ k ∈ Finset.range (n + 1),
            ∑ l ∈ Finset.range (k + 1),
              a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                ((x : ℂ) ^ m * (Complex.log u ^ l / u ^ (n + m)))
    -- Integrability of all pieces on compact `Set.Icc (-L) L`
    have hcont_K : Continuous K_I :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).sub Real.continuous_exp))
    have hcont_F : ContinuousOn (fun x : ℝ => F_plus (u + (x : ℂ))) (Set.Icc (-L) L) :=
      differentiableOn_F_plus.continuousOn.comp (continuous_const.add Complex.continuous_ofReal).continuousOn
        fun x hx => V_sec_subset_V_dom (hx_Vsec x hx)
    have hcont_evalT : ContinuousOn (fun x : ℝ => (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)))
        (Set.Icc (-L) L) := by
      have hcont_log : ContinuousOn (fun x : ℝ => Complex.log (u + (x : ℂ))) (Set.Icc (-L) L) := by
        refine ContinuousOn.congr (f := fun x : ℝ => Complex.log u + Complex.log (1 + (x : ℂ) / u)) ?_
          (fun x hx => clog_add_ofReal_eq hu (hx_abs x hx))
        refine continuousOn_const.add ?_
        intro x hx
        have hslit : 1 + (x : ℂ) / u ∈ Complex.slitPlane := by
          have ht := ht_le x hx
          have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans ht)).1
          exact Or.inl (by simp; linarith)
        have hlin : ContinuousAt (fun τ : ℝ => 1 + (τ : ℂ) / u) x :=
          (continuous_const.add (Complex.continuous_ofReal.div_const u)).continuousAt
        exact (ContinuousAt.comp (g := Complex.log) (f := fun τ : ℝ => 1 + (τ : ℂ) / u)
          (Complex.hasDerivAt_log hslit).continuousAt hlin).continuousWithinAt
      have hcont_sum : ∀ (s : Finset ℕ) (g : ℕ → ℝ → ℂ),
          (∀ i ∈ s, ContinuousOn (g i) (Set.Icc (-L) L)) →
          ContinuousOn (fun x : ℝ => ∑ i ∈ s, g i x) (Set.Icc (-L) L) := by
        intro s g hg
        classical
        induction s using Finset.induction_on with
        | empty => simpa using continuousOn_const
        | insert a t ha ih =>
          have h1 : (fun x : ℝ => ∑ i ∈ insert a t, g i x) = fun x => g a x + ∑ i ∈ t, g i x := by
            ext x; exact Finset.sum_insert ha
          rw [h1]
          exact (hg a (Finset.mem_insert_self _ _)).add
            (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
      refine (continuous_const.add (Complex.continuous_ofReal.div_const u)).continuousOn.mul ?_
      refine hcont_sum (Finset.range N) (fun n x => evalTerm a_F n (u + (x : ℂ))) fun n _ => ?_
      dsimp only [evalTerm]
      refine (hcont_sum (Finset.range (n + 1)) (fun k x => a_F n k * Complex.log (u + (x : ℂ)) ^ k)
        fun k _ => continuousOn_const.mul (hcont_log.pow k)).div
        ((continuous_const.add Complex.continuous_ofReal).continuousOn.pow n)
        (fun x hx => pow_ne_zero n (hx_ne x hx))
    have hcont_P : Continuous P_trunc := by
      dsimp only [P_trunc]; fun_prop
    have hint_Fdiv : IntegrableOn (fun x : ℝ => K_I x * (F_plus (u + (x : ℂ)) / u)) (Set.Icc (-L) L) :=
      (hcont_K.continuousOn.mul (hcont_F.div_const u)).integrableOn_compact isCompact_Icc
    have hint_ev : IntegrableOn (fun x : ℝ => K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ))))
        (Set.Icc (-L) L) :=
      (hcont_K.continuousOn.mul hcont_evalT).integrableOn_compact isCompact_Icc
    have hint_P : IntegrableOn (fun x : ℝ => K_I x * P_trunc x) (Set.Icc (-L) L) :=
      (hcont_K.mul hcont_P).continuousOn.integrableOn_compact isCompact_Icc
    -- Split `I_entire u / u - evalTrunc (convCoeff a_F) N u = T₁ + T₂ + T₃ + T₄`!
    let T₁ : ℂ := I_entire u / u - ∫ x in Set.Icc (-L) L, K_I x * (F_plus (u + (x : ℂ)) / u)
    let T₂ : ℂ := ∫ x in Set.Icc (-L) L, K_I x *
        (F_plus (u + (x : ℂ)) / u - (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)))
    let T₃ : ℂ := ∫ x in Set.Icc (-L) L, K_I x *
        ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) - P_trunc x)
    let T₄ : ℂ := (∫ x in Set.Icc (-L) L, K_I x * P_trunc x) - evalTrunc (convCoeff a_F) N u
    have hsplit : I_entire u / u - evalTrunc (convCoeff a_F) N u = T₁ + T₂ + T₃ + T₄ := by
      have hsub1 : T₂ = (∫ x in Set.Icc (-L) L, K_I x * (F_plus (u + (x : ℂ)) / u)) -
          (∫ x in Set.Icc (-L) L, K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)))) := by
        dsimp only [T₂]
        rw [show (fun x => K_I x * (F_plus (u + (x : ℂ)) / u -
              (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)))) =
            fun x => K_I x * (F_plus (u + (x : ℂ)) / u) -
              K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ))) by ext x; ring]
        exact MeasureTheory.integral_sub hint_Fdiv hint_ev
      have hsub2 : T₃ = (∫ x in Set.Icc (-L) L, K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)))) -
          (∫ x in Set.Icc (-L) L, K_I x * P_trunc x) := by
        dsimp only [T₃]
        rw [show (fun x => K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) - P_trunc x)) =
            fun x => K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ))) - K_I x * P_trunc x by
              ext x; ring]
        exact MeasureTheory.integral_sub hint_ev hint_P
      dsimp only [T₁, T₄]; linear_combination -hsub1 - hsub2
    -- Bound 1: `‖T₁‖ ≤ C_conv * ‖u‖ * A_I ^ N * N! / ‖u‖ ^ N`
    have hT1 : ‖T₁‖ ≤ C_conv * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
      have hdiv_int : ∫ x in Set.Icc (-L) L, K_I x * (F_plus (u + (x : ℂ)) / u) =
          (∫ x in Set.Icc (-L) L, K_I x * F_plus (u + (x : ℂ))) / u := by
        simp_rw [← mul_div_assoc]; exact MeasureTheory.integral_div u _
      have hT1_eq : T₁ = (I_entire u - ∫ x in Set.Icc (-L) L, K_I x * F_plus (u + (x : ℂ))) / u := by
        dsimp only [T₁]; rw [hdiv_int, sub_div]
      rw [hT1_eq, norm_div]
      have hconv := htrunc_conv u hu
      have hexp := exp_neg_mul_le_factorial hcconv hu_pos N
      calc ‖I_entire u - ∫ x in Set.Icc (-L) L, K_I x * F_plus (u + (x : ℂ))‖ / ‖u‖
          ≤ (C_conv * Real.exp (-c_conv * ‖u‖)) / ‖u‖ := div_le_div_of_nonneg_right hconv hu_pos.le
        _ ≤ C_conv * Real.exp (-c_conv * ‖u‖) := div_le_self (by positivity) hu_ge1
        _ ≤ C_conv * ((1 / c_conv) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N) :=
            mul_le_mul_of_nonneg_left hexp hCconv.le
        _ ≤ C_conv * (1 * (A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N)) := by
            rw [one_mul]; gcongr
        _ ≤ C_conv * (‖u‖ * (A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N)) := by gcongr
        _ = C_conv * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by ring
    -- Bound 2: `‖T₂‖ ≤ (8 * Real.exp 4 * C_F) * ‖u‖ * A_I ^ N * N! / ‖u‖ ^ N`
    have hT2 : ‖T₂‖ ≤ (8 * Real.exp 4 * C_F) * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
      let B2 : ℝ := 4 * C_F * ‖u‖ * (2 * A_F) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N
      have hB2_nn : 0 ≤ B2 := by dsimp [B2]; positivity
      have hpt : ∀ x ∈ Set.Icc (-L) L,
          ‖K_I x * (F_plus (u + (x : ℂ)) / u - (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)))‖ ≤
            Real.exp (2 * x - Real.exp x) * B2 := by
        intro x hx
        have hfac : F_plus (u + (x : ℂ)) / u - (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) =
            (1 + (x : ℂ) / u) * (F_plus (u + (x : ℂ)) / (u + (x : ℂ)) - evalTrunc a_F N (u + (x : ℂ))) := by
          have h1 : (1 + (x : ℂ) / u) * (F_plus (u + (x : ℂ)) / (u + (x : ℂ))) = F_plus (u + (x : ℂ)) / u := by
            have hux : 1 + (x : ℂ) / u = (u + (x : ℂ)) / u := by field_simp [hu0]
            rw [hux]; field_simp [hu0, hx_ne x hx]
          rw [mul_sub, h1]
        rw [hfac, norm_mul, norm_mul]
        have hK_norm : ‖K_I x‖ = Real.exp (2 * x - Real.exp x) := by
          dsimp only [K_I]; rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        rw [hK_norm]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have h1t_le : ‖(1 : ℂ) + (x : ℂ) / u‖ ≤ 2 := by
          calc ‖(1 : ℂ) + (x : ℂ) / u‖ ≤ ‖(1 : ℂ)‖ + ‖(x : ℂ) / u‖ := norm_add_le _ _
            _ ≤ 1 + 1 / 4 := by rw [norm_one]; linarith [ht_le x hx]
            _ ≤ 2 := by norm_num
        have hrem := hrem_F N (u + (x : ℂ)) (hx_Vsec x hx)
        have hlo := hx_norm_lo x hx
        have hhi := hx_norm_hi x hx
        have hpow_lo : ((1 / 2 : ℝ) * ‖u‖) ^ N ≤ ‖u + (x : ℂ)‖ ^ N :=
          pow_le_pow_left₀ (by positivity) (by linarith) N
        calc ‖(1 : ℂ) + (x : ℂ) / u‖ * ‖F_plus (u + (x : ℂ)) / (u + (x : ℂ)) - evalTrunc a_F N (u + (x : ℂ))‖
            ≤ 2 * (C_F * ‖u + (x : ℂ)‖ * A_F ^ N * (N.factorial : ℝ) / ‖u + (x : ℂ)‖ ^ N) :=
              mul_le_mul h1t_le hrem (norm_nonneg _) (by norm_num)
          _ ≤ 2 * (C_F * (2 * ‖u‖) * A_F ^ N * (N.factorial : ℝ) / ((1 / 2 : ℝ) * ‖u‖) ^ N) := by
              gcongr
          _ = B2 := by
              dsimp only [B2]; rw [mul_pow, mul_pow]
              have hhalf : (1 / 2 : ℝ) ^ N * (2 : ℝ) ^ N = 1 := by rw [← mul_pow]; norm_num
              have hhalf_ne : (1 / 2 : ℝ) ^ N ≠ 0 := by positivity
              field_simp [hu_pos.ne', hhalf_ne]
              calc (2 : ℝ) ^ 2 = 4 * 1 := by norm_num
                _ = 4 * ((1 / 2 : ℝ) ^ N * (2 : ℝ) ^ N) := by rw [hhalf]
                _ = (1 / 2 : ℝ) ^ N * 4 * (2 : ℝ) ^ N := by ring
      have hint_T2 : IntegrableOn (fun x : ℝ => K_I x *
            (F_plus (u + (x : ℂ)) / u - (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ))))
          (Set.Icc (-L) L) :=
        (hint_Fdiv.sub hint_ev).congr_fun (fun x _ => by simp [mul_sub]) measurableSet_Icc
      have hint_exp : IntegrableOn (fun x : ℝ => Real.exp (2 * x - Real.exp x) * B2) (Set.Icc (-L) L) :=
        ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub Real.continuous_exp)).mul
          continuous_const).continuousOn.integrableOn_compact isCompact_Icc
      have hmom0 : (∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x)) ≤ 2 * Real.exp 4 := by
        have h := (gammaMom_bounds 0 hL_pos.le).2.2.1
        simpa [Nat.factorial] using h
      calc ‖T₂‖ ≤ ∫ x in Set.Icc (-L) L,
              ‖K_I x * (F_plus (u + (x : ℂ)) / u - (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * B2 :=
            setIntegral_mono_on hint_T2.norm hint_exp measurableSet_Icc hpt
        _ = (∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x)) * B2 := integral_mul_const _ _
        _ ≤ (2 * Real.exp 4) * B2 := mul_le_mul_of_nonneg_right hmom0 hB2_nn
        _ = (8 * Real.exp 4 * C_F) * ‖u‖ * (2 * A_F) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by dsimp [B2]; ring
        _ ≤ (8 * Real.exp 4 * C_F) * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
            have : 2 * A_F ≤ A_I := by linarith
            gcongr
    -- Bound 3: `‖T₃‖ ≤ (8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * A_I ^ N * N! / ‖u‖ ^ N`
    have hT3 : ‖T₃‖ ≤ (8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
      -- Pointwise exact rewrite of `(1 + x/u) * evalTrunc a_F N (u + x) - P_trunc x`!
      have hpt_eq : ∀ x ∈ Set.Icc (-L) L,
          (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) - P_trunc x =
            ∑ n ∈ Finset.range N,
              ∑ k ∈ Finset.range (n + 1),
                ∑ l ∈ Finset.range (k + 1),
                  a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                    (shiftBasis n (k - l) ((x : ℂ) / u) -
                      ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m) := by
        intro x hx
        have hlog := clog_add_ofReal_eq hu (hx_abs x hx)
        have hux : u + (x : ℂ) = u * (1 + (x : ℂ) / u) := by field_simp [hu0]
        have h1 : (1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) =
            ∑ n ∈ Finset.range N,
              ∑ k ∈ Finset.range (n + 1),
                ∑ l ∈ Finset.range (k + 1),
                  a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                    shiftBasis n (k - l) ((x : ℂ) / u) := by
          dsimp only [evalTrunc, evalTerm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hlog, add_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp only [shiftBasis]
          rw [hux, mul_pow, div_eq_mul_inv, mul_inv, ← inv_pow]
          ring
        have h2 : P_trunc x =
            ∑ n ∈ Finset.range N,
              ∑ k ∈ Finset.range (n + 1),
                ∑ l ∈ Finset.range (k + 1),
                  a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                    (∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m) := by
          dsimp only [P_trunc]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [div_pow, pow_add]; ring
        rw [h1, h2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => by ring
      have hpt_bd : ∀ x ∈ Set.Icc (-L) L,
          ‖K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) - P_trunc x)‖ ≤
            ∑ n ∈ Finset.range N,
              ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (Real.exp (2 * x - Real.exp x) * |x| ^ (N - n)) := by
        intro x hx
        rw [hpt_eq x hx, norm_mul]
        have hK_norm : ‖K_I x‖ = Real.exp (2 * x - Real.exp x) := by
          dsimp only [K_I]; rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        rw [hK_norm]
        calc Real.exp (2 * x - Real.exp x) * ‖∑ n ∈ Finset.range N, _‖
            ≤ Real.exp (2 * x - Real.exp x) * ∑ n ∈ Finset.range N,
                ‖∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
                  a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                    (shiftBasis n (k - l) ((x : ℂ) / u) -
                      ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m)‖ :=
              mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
          _ = ∑ n ∈ Finset.range N, Real.exp (2 * x - Real.exp x) *
                ‖∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
                  a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                    (shiftBasis n (k - l) ((x : ℂ) / u) -
                      ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m)‖ :=
              Finset.mul_sum _ _ _
          _ ≤ _ := by
              refine Finset.sum_le_sum fun n hn => ?_
              simp only [Finset.mem_range] at hn
              have hinner_k : ∀ k ∈ Finset.range (n + 1),
                  ‖∑ l ∈ Finset.range (k + 1),
                    a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                      (shiftBasis n (k - l) ((x : ℂ) / u) -
                        ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m)‖ ≤
                  (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                    (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * |x| ^ (N - n) := by
                intro k hk
                simp only [Finset.mem_range] at hk
                have hrem_x : ∀ l : ℕ, ‖shiftBasis n (k - l) ((x : ℂ) / u) -
                      ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m‖ ≤
                    (2 : ℝ) ^ (n + 2) * (2 * (|x| / ‖u‖)) ^ (N - n) := by
                  intro l
                  have h := norm_shiftBasis_sub_sum_le n (k - l) (N - n) (ht_le x hx)
                  rwa [norm_div, Complex.norm_real, Real.norm_eq_abs] at h
                have hsum_l : ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖Complex.log u‖ ^ l =
                    (1 + ‖Complex.log u‖) ^ k := by
                  have h := add_pow ‖Complex.log u‖ (1 : ℝ) k
                  rw [add_comm] at h
                  simpa [one_pow, mul_comm] using h.symm
                have hfac_n : (2 : ℝ) ^ (n + 2) * (2 * (|x| / ‖u‖)) ^ (N - n) / ‖u‖ ^ n =
                    (4 * (2 : ℝ) ^ N / ‖u‖ ^ N) * |x| ^ (N - n) := by
                  rw [mul_pow, div_pow]
                  have hadd : n + (N - n) = N := Nat.add_sub_of_le (by omega)
                  have h2 : (2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (N - n) = 4 * (2 : ℝ) ^ N := by
                    calc (2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (N - n)
                        = 4 * ((2 : ℝ) ^ n * (2 : ℝ) ^ (N - n)) := by rw [pow_add]; ring
                      _ = 4 * (2 : ℝ) ^ N := by rw [← pow_add, hadd]
                  have hu_pow : ‖u‖ ^ (N - n) * ‖u‖ ^ n = ‖u‖ ^ N := by rw [← pow_add, add_comm, hadd]
                  calc (2 : ℝ) ^ (n + 2) * ((2 : ℝ) ^ (N - n) * (|x| ^ (N - n) / ‖u‖ ^ (N - n))) / ‖u‖ ^ n
                      = ((2 : ℝ) ^ (n + 2) * (2 : ℝ) ^ (N - n)) * |x| ^ (N - n) / (‖u‖ ^ (N - n) * ‖u‖ ^ n) := by
                        field_simp [hu_pos.ne']
                    _ = (4 * (2 : ℝ) ^ N / ‖u‖ ^ N) * |x| ^ (N - n) := by rw [h2, hu_pow]; ring
                calc ‖∑ l ∈ Finset.range (k + 1), _‖
                    ≤ ∑ l ∈ Finset.range (k + 1), ‖a_F n k * ((k.choose l : ℕ) : ℂ) *
                        (Complex.log u ^ l / u ^ n) *
                        (shiftBasis n (k - l) ((x : ℂ) / u) -
                          ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m)‖ :=
                      norm_sum_le _ _
                  _ ≤ ∑ l ∈ Finset.range (k + 1), ‖a_F n k‖ * (k.choose l : ℝ) *
                        (‖Complex.log u‖ ^ l / ‖u‖ ^ n) *
                        ((2 : ℝ) ^ (n + 2) * (2 * (|x| / ‖u‖)) ^ (N - n)) := by
                      refine Finset.sum_le_sum fun l _ => ?_
                      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_div, norm_pow, norm_pow]
                      exact mul_le_mul_of_nonneg_left (hrem_x l) (by positivity)
                  _ = ‖a_F n k‖ * (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖Complex.log u‖ ^ l) *
                        ((2 : ℝ) ^ (n + 2) * (2 * (|x| / ‖u‖)) ^ (N - n) / ‖u‖ ^ n) := by
                      rw [Finset.mul_sum, Finset.sum_mul]
                      refine Finset.sum_congr rfl fun l _ => by ring
                  _ = ‖a_F n k‖ * (1 + ‖Complex.log u‖) ^ k * ((4 * (2 : ℝ) ^ N / ‖u‖ ^ N) * |x| ^ (N - n)) := by
                      rw [hsum_l, hfac_n]
                  _ ≤ (C_F * A_F ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) * (1 + ‖Complex.log u‖) ^ k *
                        ((4 * (2 : ℝ) ^ N / ‖u‖ ^ N) * |x| ^ (N - n)) := by
                      exact mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_right (hcoeff_F n k (by omega)) (by positivity)) (by positivity)
                  _ = (C_F * A_F ^ n * (n.factorial : ℝ)) * ((1 + ‖Complex.log u‖) ^ k / (k.factorial : ℝ)) *
                        ((4 * (2 : ℝ) ^ N / ‖u‖ ^ N) * |x| ^ (N - n)) := by ring
                  _ ≤ (C_F * A_F ^ n * (n.factorial : ℝ)) * (Real.exp (Real.pi + 1) * ‖u‖) *
                        ((4 * (2 : ℝ) ^ N / ‖u‖ ^ N) * |x| ^ (N - n)) := by
                      exact mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left (hlog_pow_le k) (by positivity)) (by positivity)
                  _ = (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                        (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * |x| ^ (N - n) := by ring
              have hsum_k : ‖∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
                    a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                      (shiftBasis n (k - l) ((x : ℂ) / u) -
                        ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m)‖ ≤
                  ((n : ℝ) + 1) * ((C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                    (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * |x| ^ (N - n)) := by
                calc _ ≤ ∑ k ∈ Finset.range (n + 1), ‖∑ l ∈ Finset.range (k + 1),
                        a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                          (shiftBasis n (k - l) ((x : ℂ) / u) -
                            ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m)‖ := norm_sum_le _ _
                  _ ≤ ∑ _k ∈ Finset.range (n + 1),
                        ((C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                          (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * |x| ^ (N - n)) := Finset.sum_le_sum hinner_k
                  _ = ((n : ℝ) + 1) * ((C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                        (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * |x| ^ (N - n)) := by
                      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
              calc Real.exp (2 * x - Real.exp x) * ‖∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1),
                      a_F n k * ((k.choose l : ℕ) : ℂ) * (Complex.log u ^ l / u ^ n) *
                        (shiftBasis n (k - l) ((x : ℂ) / u) -
                          ∑ m ∈ Finset.range (N - n), shiftC n (k - l) m * ((x : ℂ) / u) ^ m)‖
                  ≤ Real.exp (2 * x - Real.exp x) * (((n : ℝ) + 1) *
                      ((C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                        (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * |x| ^ (N - n))) :=
                    mul_le_mul_of_nonneg_left hsum_k (Real.exp_pos _).le
                _ = ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                      (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (Real.exp (2 * x - Real.exp x) * |x| ^ (N - n)) := by ring
      have hint_T3 : IntegrableOn (fun x : ℝ => K_I x *
            ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) - P_trunc x))
          (Set.Icc (-L) L) :=
        (hint_ev.sub hint_P).congr_fun (fun x _ => by simp [mul_sub]) measurableSet_Icc
      have hint_rhs : ∀ n ∈ Finset.range N, IntegrableOn (fun x : ℝ =>
            ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
              (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (Real.exp (2 * x - Real.exp x) * |x| ^ (N - n)))
          (Set.Icc (-L) L) := fun n _ =>
        (continuous_const.mul ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub Real.continuous_exp)).mul
          (continuous_abs.pow (N - n)))).continuousOn.integrableOn_compact isCompact_Icc
      have hint_finset_real : ∀ (s : Finset ℕ) (g : ℕ → ℝ → ℝ),
          (∀ n ∈ s, IntegrableOn (g n) (Set.Icc (-L) L)) →
          IntegrableOn (fun x => ∑ n ∈ s, g n x) (Set.Icc (-L) L) ∧
          (∫ x in Set.Icc (-L) L, ∑ n ∈ s, g n x) = ∑ n ∈ s, ∫ x in Set.Icc (-L) L, g n x := by
        intro s g hg
        classical
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          exact ⟨integrableOn_zero, by simp⟩
        | insert a t ha ih =>
          have hga := hg a (Finset.mem_insert_self _ _)
          have ⟨hgt_int, hgt_eq⟩ := ih fun n hn => hg n (Finset.mem_insert_of_mem hn)
          have heq : (fun x => ∑ n ∈ insert a t, g n x) = fun x => g a x + ∑ n ∈ t, g n x := by
            ext x; exact Finset.sum_insert ha
          rw [heq]
          refine ⟨hga.add hgt_int, ?_⟩
          rw [MeasureTheory.integral_add hga hgt_int, hgt_eq, Finset.sum_insert ha]
      have ⟨hint_rhs_sum, hint_rhs_eq⟩ := hint_finset_real (Finset.range N)
        (fun n x => ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
          (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (Real.exp (2 * x - Real.exp x) * |x| ^ (N - n))) hint_rhs
      calc ‖T₃‖ ≤ ∫ x in Set.Icc (-L) L,
              ‖K_I x * ((1 + (x : ℂ) / u) * evalTrunc a_F N (u + (x : ℂ)) - P_trunc x)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in Set.Icc (-L) L, ∑ n ∈ Finset.range N,
              ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (Real.exp (2 * x - Real.exp x) * |x| ^ (N - n)) :=
            setIntegral_mono_on hint_T3.norm hint_rhs_sum measurableSet_Icc hpt_bd
        _ = ∑ n ∈ Finset.range N, ∫ x in Set.Icc (-L) L,
              ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (Real.exp (2 * x - Real.exp x) * |x| ^ (N - n)) :=
            hint_rhs_eq
        _ ≤ ∑ n ∈ Finset.range N,
              ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (2 * Real.exp 4 * ((N - n).factorial : ℝ)) := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left (gammaMom_bounds (N - n) hL_pos.le).2.2.1 (by positivity)
        _ ≤ ∑ _n ∈ Finset.range N,
              ((N : ℝ) + 1) * ((8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (2 * A_F) ^ N *
                (N.factorial : ℝ) / ‖u‖ ^ N) := by
            refine Finset.sum_le_sum fun n hn => ?_
            simp only [Finset.mem_range] at hn
            have hn_le : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast (show n + 1 ≤ N + 1 by omega)
            have hAF_le : A_F ^ n ≤ A_F ^ N := pow_le_pow_right₀ hAF (by omega)
            have hfac : (n.factorial : ℝ) * ((N - n).factorial : ℝ) ≤ (N.factorial : ℝ) := by
              have := factorial_mul_factorial_le n (N - n)
              rwa [Nat.add_sub_of_le (by omega)] at this
            have hexp_add : Real.exp (Real.pi + 1) * Real.exp 4 = Real.exp (Real.pi + 5) := by
              rw [← Real.exp_add]; congr 1; ring
            calc ((n : ℝ) + 1) * (C_F * Real.exp (Real.pi + 1) * ‖u‖ * A_F ^ n * (n.factorial : ℝ) *
                    (4 * (2 : ℝ) ^ N / ‖u‖ ^ N)) * (2 * Real.exp 4 * ((N - n).factorial : ℝ))
                = ((n : ℝ) + 1) * (8 * (Real.exp (Real.pi + 1) * Real.exp 4) * C_F * ‖u‖ *
                    (A_F ^ n * (2 : ℝ) ^ N) * ((n.factorial : ℝ) * ((N - n).factorial : ℝ)) / ‖u‖ ^ N) := by ring
              _ ≤ ((N : ℝ) + 1) * (8 * Real.exp (Real.pi + 5) * C_F * ‖u‖ *
                    (A_F ^ N * (2 : ℝ) ^ N) * (N.factorial : ℝ) / ‖u‖ ^ N) := by
                  rw [hexp_add]; gcongr
              _ = ((N : ℝ) + 1) * ((8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (2 * A_F) ^ N *
                    (N.factorial : ℝ) / ‖u‖ ^ N) := by rw [mul_pow]; ring
        _ = (N : ℝ) * ((N : ℝ) + 1) * ((8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (2 * A_F) ^ N *
              (N.factorial : ℝ) / ‖u‖ ^ N) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        _ ≤ (4 : ℝ) ^ N * ((8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (2 * A_F) ^ N *
              (N.factorial : ℝ) / ‖u‖ ^ N) := by
            have hN2 : (N : ℝ) * ((N : ℝ) + 1) ≤ (4 : ℝ) ^ N := by
              have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
              exact (by nlinarith : (N : ℝ) * ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 2).trans
                (nat_add_one_sq_le_four_pow N)
            exact mul_le_mul_of_nonneg_right hN2 (by positivity)
        _ = (8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (8 * A_F) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
            have : (4 : ℝ) ^ N * (2 * A_F) ^ N = (8 * A_F) ^ N := by rw [← mul_pow]; congr 1; ring
            calc _ = (8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * ((4 : ℝ) ^ N * (2 * A_F) ^ N) *
                  (N.factorial : ℝ) / ‖u‖ ^ N := by ring
              _ = _ := by rw [this]
        _ ≤ (8 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
            have : 8 * A_F ≤ A_I := by linarith
            gcongr
    -- Bound 4: `‖T₄‖ ≤ (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * A_I ^ N * N! / ‖u‖ ^ N`
    have hT4 : ‖T₄‖ ≤ (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
      -- Pull the finite sum outside `∫_{Icc (-L) L} K_I x * P_trunc x`!
      have hint_P_eq : ∫ x in Set.Icc (-L) L, K_I x * P_trunc x =
          ∑ n ∈ Finset.range N,
            ∑ m ∈ Finset.range (N - n),
              ∑ k ∈ Finset.range (n + 1),
                ∑ l ∈ Finset.range (k + 1),
                  a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                    (((∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) : ℝ) : ℂ) *
                    (Complex.log u ^ l / u ^ (n + m)) := by
        have hstep : ∀ (n m k l : ℕ),
            ∫ x in Set.Icc (-L) L, K_I x *
              (a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                ((x : ℂ) ^ m * (Complex.log u ^ l / u ^ (n + m)))) =
            a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
              (((∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) : ℝ) : ℂ) *
              (Complex.log u ^ l / u ^ (n + m)) := by
          intro n m k l
          have hrew : (fun x : ℝ => K_I x *
                (a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                  ((x : ℂ) ^ m * (Complex.log u ^ l / u ^ (n + m))))) =
              fun x : ℝ => (a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                (Complex.log u ^ l / u ^ (n + m))) *
                (((Real.exp (2 * x - Real.exp x) * x ^ m : ℝ) : ℂ)) := by
            ext x; dsimp only [K_I]; push_cast; ring
          have hint_real : IntegrableOn (fun x : ℝ => Real.exp (2 * x - Real.exp x) * x ^ m) (Set.Icc (-L) L) :=
            ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub Real.continuous_exp)).mul
              (continuous_pow m)).continuousOn.integrableOn_compact isCompact_Icc
          have hofR : (∫ x in Set.Icc (-L) L, ((Real.exp (2 * x - Real.exp x) * x ^ m : ℝ) : ℂ)) =
              (((∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) : ℝ) : ℂ) :=
            Complex.ofRealCLM.integral_comp_comm hint_real
          rw [hrew, integral_const_mul, hofR]; ring
        have hci : ∀ (f : ℝ → ℂ), Continuous f → IntegrableOn f (Set.Icc (-L) L) :=
          fun f hf => hf.continuousOn.integrableOn_compact isCompact_Icc
        have hint_finset_c : ∀ (s : Finset ℕ) (g : ℕ → ℝ → ℂ),
            (∀ i ∈ s, IntegrableOn (g i) (Set.Icc (-L) L)) →
            IntegrableOn (fun x => ∑ i ∈ s, g i x) (Set.Icc (-L) L) ∧
            (∫ x in Set.Icc (-L) L, ∑ i ∈ s, g i x) = ∑ i ∈ s, ∫ x in Set.Icc (-L) L, g i x := by
          intro s g hg
          classical
          induction s using Finset.induction_on with
          | empty =>
            simp only [Finset.sum_empty]
            exact ⟨integrableOn_zero, by simp⟩
          | insert a t ha ih =>
            have hga := hg a (Finset.mem_insert_self _ _)
            have ⟨hgt_int, hgt_eq⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
            have heq : (fun x => ∑ i ∈ insert a t, g i x) = fun x => g a x + ∑ i ∈ t, g i x := by
              ext x; exact Finset.sum_insert ha
            rw [heq]
            refine ⟨hga.add hgt_int, ?_⟩
            rw [MeasureTheory.integral_add hga hgt_int, hgt_eq, Finset.sum_insert ha]
        dsimp only [P_trunc]
        simp_rw [Finset.mul_sum]
        rw [(hint_finset_c _ _ fun n _ => hci _ (by fun_prop)).2]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [(hint_finset_c _ _ fun m _ => hci _ (by fun_prop)).2]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [(hint_finset_c _ _ fun k _ => hci _ (by fun_prop)).2]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [(hint_finset_c _ _ fun l _ => hci _ (by fun_prop)).2]
        refine Finset.sum_congr rfl fun l _ => hstep n m k l
      have hT4_eq : T₄ =
          ∑ n ∈ Finset.range N,
            ∑ m ∈ Finset.range (N - n),
              ∑ k ∈ Finset.range (n + 1),
                ∑ l ∈ Finset.range (k + 1),
                  a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                    ((((∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) - gammaMom m : ℝ) : ℂ)) *
                    (Complex.log u ^ l / u ^ (n + m)) := by
        dsimp only [T₄]
        rw [hint_P_eq, evalTrunc_convCoeff_eq, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => by push_cast; ring
      rw [hT4_eq]
      have hterm_nmk : ∀ n ∈ Finset.range N, ∀ m ∈ Finset.range (N - n), ∀ k ∈ Finset.range (n + 1),
          ‖∑ l ∈ Finset.range (k + 1),
            a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
              ((((∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) - gammaMom m : ℝ) : ℂ)) *
              (Complex.log u ^ l / u ^ (n + m))‖ ≤
            (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (24 * A_F) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
        intro n hn m hm k hk
        simp only [Finset.mem_range] at hn hm hk
        have htail_m : |(∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) - gammaMom m| ≤
            2 * Real.exp 4 * Real.exp (-L) * (m.factorial : ℝ) := by
          rw [abs_sub_comm]; exact (gammaMom_bounds m hL_pos.le).2.2.2
        have hsum_l : ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖Complex.log u‖ ^ l =
            (1 + ‖Complex.log u‖) ^ k := by
          have h := add_pow ‖Complex.log u‖ (1 : ℝ) k
          rw [add_comm] at h; simpa [one_pow, mul_comm] using h.symm
        have hexp_L : Real.exp (-L) ≤ (24 : ℝ) ^ (N - (n + m)) * ((N - (n + m)).factorial : ℝ) / ‖u‖ ^ (N - (n + m)) := by
          have h := exp_neg_mul_le_factorial (show (0 : ℝ) < 1 / 24 by norm_num) hu_pos (N - (n + m))
          have hL_eq : -L = -(1 / 24 : ℝ) * ‖u‖ := by dsimp [L]; ring
          have h24 : (1 : ℝ) / (1 / 24 : ℝ) = 24 := by norm_num
          rw [hL_eq]; rwa [h24] at h
        have hfac3 : (n.factorial : ℝ) * (m.factorial : ℝ) * ((N - (n + m)).factorial : ℝ) ≤ (N.factorial : ℝ) := by
          have h1 := factorial_mul_factorial_le n m
          have h2 := factorial_mul_factorial_le (n + m) (N - (n + m))
          rw [Nat.add_sub_of_le (by omega)] at h2
          exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2
        have hpow_geom : A_F ^ n * (2 : ℝ) ^ (n + 1 + m) * (24 : ℝ) ^ (N - (n + m)) ≤ 2 * (24 * A_F) ^ N := by
          have h1 : A_F ^ n ≤ A_F ^ N := pow_le_pow_right₀ hAF (by omega)
          have h2 : (2 : ℝ) ^ (n + 1 + m) = 2 * (2 : ℝ) ^ (n + m) := by
            have : n + 1 + m = (n + m) + 1 := by omega
            rw [this, pow_succ]; ring
          have h3 : (2 : ℝ) ^ (n + m) ≤ (24 : ℝ) ^ (n + m) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
          have h4 : (24 : ℝ) ^ (n + m) * (24 : ℝ) ^ (N - (n + m)) = (24 : ℝ) ^ N := by
            rw [← pow_add, Nat.add_sub_of_le (by omega)]
          calc A_F ^ n * (2 : ℝ) ^ (n + 1 + m) * (24 : ℝ) ^ (N - (n + m))
              = 2 * A_F ^ n * ((2 : ℝ) ^ (n + m) * (24 : ℝ) ^ (N - (n + m))) := by rw [h2]; ring
            _ ≤ 2 * A_F ^ N * ((24 : ℝ) ^ (n + m) * (24 : ℝ) ^ (N - (n + m))) := by gcongr
            _ = 2 * (24 * A_F) ^ N := by rw [h4, mul_pow]; ring
        have hu_pow : ‖u‖ ^ (n + m) * ‖u‖ ^ (N - (n + m)) = ‖u‖ ^ N := by
          rw [← pow_add, Nat.add_sub_of_le (by omega)]
        have hexp_add : Real.exp (Real.pi + 1) * Real.exp 4 = Real.exp (Real.pi + 5) := by
          rw [← Real.exp_add]; congr 1; ring
        calc ‖∑ l ∈ Finset.range (k + 1), _‖
            ≤ ∑ l ∈ Finset.range (k + 1), ‖a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                ((((∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) - gammaMom m : ℝ) : ℂ)) *
                (Complex.log u ^ l / u ^ (n + m))‖ := norm_sum_le _ _
          _ ≤ ∑ l ∈ Finset.range (k + 1), ‖a_F n k‖ * (k.choose l : ℝ) * (2 : ℝ) ^ (n + 1 + m) *
                (2 * Real.exp 4 * Real.exp (-L) * (m.factorial : ℝ)) * (‖Complex.log u‖ ^ l / ‖u‖ ^ (n + m)) := by
              refine Finset.sum_le_sum fun l _ => ?_
              rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
                Real.norm_eq_abs, norm_div, norm_pow, norm_pow]
              have hsc := norm_shiftC_le n (k - l) m
              gcongr
          _ = ‖a_F n k‖ * (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖Complex.log u‖ ^ l) *
                ((2 : ℝ) ^ (n + 1 + m) * (2 * Real.exp 4 * Real.exp (-L) * (m.factorial : ℝ)) / ‖u‖ ^ (n + m)) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun l _ => by ring
          _ ≤ (C_F * A_F ^ n * (n.factorial : ℝ) / (k.factorial : ℝ)) * (1 + ‖Complex.log u‖) ^ k *
                ((2 : ℝ) ^ (n + 1 + m) * (2 * Real.exp 4 *
                  ((24 : ℝ) ^ (N - (n + m)) * ((N - (n + m)).factorial : ℝ) / ‖u‖ ^ (N - (n + m))) *
                  (m.factorial : ℝ)) / ‖u‖ ^ (n + m)) := by
              rw [hsum_l]; have := hcoeff_F n k (by omega); gcongr
          _ = 2 * C_F * Real.exp 4 * ((1 + ‖Complex.log u‖) ^ k / (k.factorial : ℝ)) *
                (A_F ^ n * (2 : ℝ) ^ (n + 1 + m) * (24 : ℝ) ^ (N - (n + m))) *
                ((n.factorial : ℝ) * (m.factorial : ℝ) * ((N - (n + m)).factorial : ℝ)) /
                (‖u‖ ^ (n + m) * ‖u‖ ^ (N - (n + m))) := by
              field_simp [hu_pos.ne']
          _ ≤ 2 * C_F * Real.exp 4 * (Real.exp (Real.pi + 1) * ‖u‖) *
                (2 * (24 * A_F) ^ N) * (N.factorial : ℝ) / ‖u‖ ^ N := by
              rw [hu_pow]; have := hlog_pow_le k; gcongr
          _ = (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (24 * A_F) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
              rw [← hexp_add]; ring
      let B4 : ℝ := (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (24 * A_F) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N
      have hB4_nn : 0 ≤ B4 := by dsimp [B4]; positivity
      have htriple : ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (N - n), ∑ k ∈ Finset.range (n + 1),
            ∑ l ∈ Finset.range (k + 1),
              a_F n k * ((k.choose l : ℕ) : ℂ) * shiftC n (k - l) m *
                ((((∫ x in Set.Icc (-L) L, Real.exp (2 * x - Real.exp x) * x ^ m) - gammaMom m : ℝ) : ℂ)) *
                (Complex.log u ^ l / u ^ (n + m))‖ ≤ ((N : ℝ) + 1) ^ 3 * B4 := by
        calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (N - n), ∑ k ∈ Finset.range (n + 1),
                ‖∑ l ∈ Finset.range (k + 1), _‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ =>
                (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_sum_le _ _))
          _ ≤ ∑ n ∈ Finset.range N, ∑ _m ∈ Finset.range (N - n), ∑ _k ∈ Finset.range (n + 1), B4 :=
              Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun k hk =>
                hterm_nmk n hn m hm k hk
          _ ≤ ∑ _n ∈ Finset.range N, ((N : ℝ) + 1) * (((N : ℝ) + 1) * B4) := by
              refine Finset.sum_le_sum fun n hn => ?_
              simp only [Finset.mem_range] at hn
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              have h1 : ((N - n : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (show N - n ≤ N + 1 by omega)
              have h2 : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (show n + 1 ≤ N + 1 by omega)
              exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hB4_nn) (by positivity) (by positivity)
          _ = (N : ℝ) * (((N : ℝ) + 1) * (((N : ℝ) + 1) * B4)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ ((N : ℝ) + 1) ^ 3 * B4 := by
              have hN : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
              calc (N : ℝ) * (((N : ℝ) + 1) * (((N : ℝ) + 1) * B4))
                  = ((N : ℝ) * ((N : ℝ) + 1) ^ 2) * B4 := by ring
                _ ≤ ((N : ℝ) + 1) ^ 3 * B4 := by nlinarith [sq_nonneg ((N : ℝ) + 1), hB4_nn]
      calc _ ≤ (8 : ℝ) ^ N * B4 := htriple.trans (mul_le_mul_of_nonneg_right (nat_add_one_cube_le_eight_pow N) hB4_nn)
        _ = (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * (192 * A_F) ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by
            dsimp only [B4]
            have : (8 : ℝ) ^ N * (24 * A_F) ^ N = (192 * A_F) ^ N := by rw [← mul_pow]; congr 1; ring
            calc _ = (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * ((8 : ℝ) ^ N * (24 * A_F) ^ N) *
                  (N.factorial : ℝ) / ‖u‖ ^ N := by ring
              _ = _ := by rw [this]
        _ ≤ (4 * Real.exp (Real.pi + 5) * C_F) * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by gcongr
    -- Combine `T₁ + T₂ + T₃ + T₄`!
    rw [hsplit]
    have htri : ‖T₁ + T₂ + T₃ + T₄‖ ≤ ‖T₁‖ + ‖T₂‖ + ‖T₃‖ + ‖T₄‖ :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    have h4le : Real.exp 4 ≤ Real.exp (Real.pi + 5) := Real.exp_le_exp.mpr (by linarith [Real.pi_pos])
    have hC_sum : C_conv + 8 * Real.exp 4 * C_F + 8 * Real.exp (Real.pi + 5) * C_F +
        4 * Real.exp (Real.pi + 5) * C_F ≤ C_I := by
      dsimp only [C_I]; nlinarith [Real.exp_pos (Real.pi + 5)]
    have hfac_nn : 0 ≤ ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by positivity
    calc ‖T₁ + T₂ + T₃ + T₄‖
        ≤ ‖T₁‖ + ‖T₂‖ + ‖T₃‖ + ‖T₄‖ := htri
      _ ≤ (C_conv + 8 * Real.exp 4 * C_F + 8 * Real.exp (Real.pi + 5) * C_F +
            4 * Real.exp (Real.pi + 5) * C_F) * (‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N) := by
          have : C_conv * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N +
              8 * Real.exp 4 * C_F * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N +
              8 * Real.exp (Real.pi + 5) * C_F * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N +
              4 * Real.exp (Real.pi + 5) * C_F * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N =
            (C_conv + 8 * Real.exp 4 * C_F + 8 * Real.exp (Real.pi + 5) * C_F +
              4 * Real.exp (Real.pi + 5) * C_F) * (‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N) := by ring
          linarith [hT1, hT2, hT3, hT4]
      _ ≤ C_I * (‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N) := mul_le_mul_of_nonneg_right hC_sum hfac_nn
      _ = C_I * ‖u‖ * A_I ^ N * (N.factorial : ℝ) / ‖u‖ ^ N := by ring

/-! ### 6. Unconditional Proof of Pak's Conjecture 2.5a from `Main.PNTAllOrders` -/

/-- **PAK'S CONJECTURE 2.5a (`pak_2_5a_of_pnt`, Tier 1 Unconditional from `Main.PNTAllOrders`)**:
The ordinary generating function `∑_{n ≥ 1} p_n q^n` of the `n`-th prime is differentially
transcendental over `ℂ(q)`, proved unconditionally from `Main.PNTAllOrders` (with zero
additional analytic or sectorial hypotheses). -/
theorem pak_2_5a_of_pnt (hpnt : Main.PNTAllOrders) :
    AlgebraicIndependent ℂ (PrimeNome.seriesCoordinates NthPrime.series) := by
  obtain ⟨a_I, ha_I⟩ := I_entire_div_hasGev1Exp
  exact pak_2_5a_of_pnt_and_sectorial_gevrey1_bridge hpnt
    (hsector_of_Y_gev1 (R₀ := R_conv) (by have h := R_conv_ge_1e6; norm_num at h; linarith)
      isOpen_univ (Set.subset_univ _) differentiable_I_entire.differentiableOn
      (fun u _ => I_entire_ofReal u) ha_I)

end
end PakPrimes.PakNthPrimeUnconditional
